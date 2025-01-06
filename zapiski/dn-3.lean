set_option autoImplicit false

/------------------------------------------------------------------------------
 ## Naravna števila

 Definirajte funkcijo, ki _rekurzivno_ (torej naivno in ne direktno s formulo,
 ki jo boste morali dokazati) sešteje prvih `n` naravnih števil, ter
 dokažite, da zanjo velja znana enakost (najprej v obliki, ki ne zahteva
 deljenja, nato pa še v običajni obliki).
------------------------------------------------------------------------------/

def vsota_prvih : Nat → Nat :=
  fun n =>
    let rec sestej (m : Nat) (vs : Nat) : Nat :=
      match m with
      | 0 => vs
      | m' + 1 => sestej m' (vs + m)
    sestej n 0

theorem vsota_vsote (m n : Nat) : vsota_prvih (m + n) = m * n + vsota_prvih m + vsota_prvih n :=
  sorry

theorem gauss : (n : Nat) → 2 * vsota_prvih n = n * (n + 1) :=
  by
    intro n
    induction n with
    | zero =>
      simp [vsota_prvih]
      rfl
    | succ n' ih =>
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      rw (config := { occs := .pos [2]}) [Nat.add_assoc]
      rw [← Nat.two_mul, Nat.mul_one]
      rw [vsota_vsote, Nat.mul_one]
      rw [Nat.mul_add, Nat.mul_add]
      rw [ih]
      simp [vsota_prvih, vsota_prvih.sestej]
      rw [Nat.mul_add,Nat.mul_one, ← Nat.pow_two]
      rw [← Nat.add_assoc]
      rw (config := { occs := .pos [4]}) [Nat.add_assoc]
      rw [← Nat.two_mul]
      rw (config := { occs := .pos [3]}) [Nat.add_comm]
      rw [Nat.add_assoc]


theorem cisto_pravi_gauss : (n : Nat) → vsota_prvih n = (n * (n + 1)) / 2 :=
  by
    intro n
    rw [← gauss n] -- Use the proven gauss theorem
    simp [Nat.mul_div_cancel] -- Simplify the result using division by 2
/------------------------------------------------------------------------------
 ## Vektorji

 Definirajmo vektorje podobno kot na predavanjih, le da namesto svojih naravnih
 števil uporabimo vgrajena. Da se tipi ujamejo, funkcijo stikanja napišemo s
 pomočjo taktik.

 Napišite funkcijo `obrni`, ki vrne na glavo obrnjen vektor, ter funkciji
 `glava` in `rep`, ki varno vrneta glavo in rep _nepraznega_ seznama.
------------------------------------------------------------------------------/

inductive Vektor : Type → Nat → Type where
  | prazen : {A : Type} → Vektor A 0
  | sestavljen : {A : Type} → {n : Nat} → A → Vektor A n → Vektor A (n + 1)
deriving Repr

def stakni : {A : Type} → {m n : Nat} → Vektor A m → Vektor A n → Vektor A (m + n) :=
  fun xs ys => match xs with
  | .prazen => by rw [Nat.add_comm]; exact ys
  | .sestavljen x xs' => by rw [Nat.add_right_comm]; exact Vektor.sestavljen x (stakni xs' ys)

def obrni : {A : Type} → {n : Nat} → Vektor A n → Vektor A n :=
  fun xs =>
    match xs with
    | .prazen => .prazen
    | .sestavljen x xs' => stakni (obrni xs') (.sestavljen x .prazen)

def glava : {A : Type} → {n : Nat} → Vektor A (n + 1) -> A :=
  fun {A} {n} xs =>
    match xs with
    | .sestavljen x xs' => x

def rep : {A : Type} → {n : Nat} → Vektor A (n + 1) → Vektor A n :=
  fun {A} {n} xs =>
    match xs with
    | .sestavljen _ xs' => xs'

/------------------------------------------------------------------------------
 ## Predikatni račun

 Dokažite spodnje tri trditve. Zadnja je _paradoks pivca_, ki pravi:
   "V vsaki neprazni gostilni obstaja gost, za katerega velja,
   da če pije on, pijejo vsi v gostilni."
 Za dokaz potrebujete klasično logiko, torej nekaj iz modula `Classical`.
------------------------------------------------------------------------------/

theorem forall_implies : {A : Type} → {P Q : A → Prop} →
  (∀ x, (P x → Q x)) → (∀ x, P x) → (∀ x, Q x) := by
  intros A P Q h1 h2 x
  apply h1
  apply h2

theorem forall_implies' : {A : Type} → {P : Prop} → {Q : A → Prop} →
  (∀ x, (P → Q x)) ↔ (P → ∀ x, Q x) := by
    intros A P Q
    apply Iff.intro
    -- Dokaz leve strani
    intro h
    intro p
    intro x
    exact h x p
    -- Dokaz desne strani
    intro h1
    intro x
    intro h2
    apply h1
    apply h2

theorem paradoks_pivca :
  {G : Type} → {P : G → Prop} →
  (g : G) →  -- (g : G) pove, da je v gostilni vsaj en gost
  ∃ (p : G), (P p → ∀ (x : G), P x) :=
  by
    intros G P g
    by_cases hp : ∃ x, P x
    case pos =>
      cases hp with
      | intro p h =>
        exists p
        intro h'
        intro x
        exact h'
    case neg =>
      exists g
      intro h'
      exfalso
      exact hp ⟨g, h'⟩

/------------------------------------------------------------------------------
 ## Dvojiška drevesa

 Podan naj bo tip dvojiških dreves skupaj s funkcijama za zrcaljenje in izračun
 višine ter dvema funkcijama, ki obe od leve proti desni naštejeta elemente
 drevesa. Pri tem prva deluje naivno in ima časovno zahtevnost O(n log n), druga
 pa je malo bolj zapletena in deluje v času O(n). Dokažite spodnje enakosti, pri
 čemer lahko do pomožne funkcije `aux` dostopate kot `elementi'.aux`
-------------------------------------------------------------------------------/

inductive Drevo : Type → Type where
  | prazno : {A : Type} → Drevo A
  | sestavljeno : {A : Type} → Drevo A → A → Drevo A → Drevo A

def zrcali : {A : Type} → Drevo A → Drevo A :=
  fun t => match t with
  | .prazno => .prazno
  | .sestavljeno l x d => .sestavljeno (zrcali d) x (zrcali l)

def visina : {A : Type} → Drevo A → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno l _ d => 1 + max (visina l) (visina d)

def elementi : {A : Type} → Drevo A → List A :=
  fun t => match t with
  | .prazno => []
  | .sestavljeno l x d => elementi l ++ x :: elementi d

def elementi' : {A : Type} → Drevo A → List A :=
  let rec aux : {A : Type} → Drevo A → List A → List A :=
    fun t acc => match t with
    | .prazno => acc
    | .sestavljeno l x d => aux l (x :: aux d acc)
  fun t => aux t []

theorem zrcali_zrcali :
  {A : Type} → (t : Drevo A) →
  zrcali (zrcali t) = t := by
  intro A
  intro t
  induction t with
  | prazno =>
    simp [zrcali]
  | sestavljeno x l r ihl ihr =>
    simp [zrcali]
    rw [ihl, ihr]
    simp [zrcali]

theorem max_comm {a b : Nat} : max a b = max b a :=
  sorry

theorem visina_zrcali :
  {A : Type} → (t : Drevo A) →
  visina (zrcali t) = visina t := by
  intro A
  intro t
  induction t with
  | prazno =>
    simp [zrcali, visina]
  | sestavljeno l x r ihl ihr =>
    simp [zrcali, visina]
    rw [ihl, ihr]
    rw [max_comm]

theorem elementi_elementi' :
  {A : Type} → (t : Drevo A) →
  elementi t = elementi' t := by
  intros A t
  induction t with
  | prazno =>
    simp [elementi, elementi']
    rfl
  | sestavljeno l x r ihl ihr =>
    simp [elementi, elementi']
    rw [ihl, ihr]
    rw [elementi'.aux]
