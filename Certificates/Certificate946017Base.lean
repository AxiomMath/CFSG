
module

public import Certificates.Data.ParrottPSp43L1

@[expose] public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups
open CFSG.Sporadic.Schreier (tab)

local notation "P45" => Equiv.Perm (Fin 45)

def prodSpan : List P45 → List P45
  | [] => [1]
  | g :: gs => prodSpan gs ++ (prodSpan gs).map (g * ·)

def tabList (l : List P45) : List P45 := l.map tab

def mulClosedB (L : List P45) : Bool :=
  L.all fun x => L.all fun y => decide (x * y ∈ L)

def invClosedB (L : List P45) : Bool := L.all fun x => decide (x⁻¹ ∈ L)

def subsetB (l L : List P45) : Bool := l.all fun x => decide (x ∈ L)

def inAB (L : List P45) : Bool := L.all fun x => QA45.sift x 0

structure ListGroupFacts (L «gens» : List P45) : Prop where
  nodup : L.Nodup
  one_mem : (1 : P45) ∈ L
  mul_closed : mulClosedB L = true
  inv_closed : invClosedB L = true
  gens_mem : subsetB «gens» L = true
  in_A : inAB L = true

def T0gens : List P45 := [u, v, alpha1, beta1, alpha2, beta2]

def T0list (_ : Unit := ()) : List P45 :=
  tabList (prodSpan (tabList [u, v, t, alpha1, beta1, alpha2, beta2]))

def Sgens : List P45 := [u, alpha1 * alpha2, beta1 * beta2, t]

def Slist (_ : Unit := ()) : List P45 := tabList (prodSpan (tabList Sgens))

def E3gens : List P45 := [u * v, alpha1 * alpha2, alpha1 * beta1 * beta2, t]

def E1gens : List P45 := [v, u, t, alpha1 * alpha2]

def E2gens : List P45 := [v * alpha1, u * beta1 * beta2, t, alpha1 * alpha2]

def E3list (_ : Unit := ()) : List P45 := tabList (prodSpan (tabList E3gens))

def E1list (_ : Unit := ()) : List P45 := tabList (prodSpan (tabList E1gens))

def E2list (_ : Unit := ()) : List P45 := tabList (prodSpan (tabList E2gens))

def involutionsOf (L : List P45) : List P45 := L.filter fun x => x * x = 1 ∧ x ≠ 1

def pairwiseCommB : List P45 → Bool
  | [] => true
  | a :: l => l.all (fun b => decide (a * b = b * a)) && pairwiseCommB l

def e16Check (_ : Unit := ()) : Bool :=
  let S := Slist ()
  let E3 := E3list ()
  let E1 := E1list ()
  let E2 := E2list ()
  ((involutionsOf (T0list ())).sublistsLen 4).all fun l =>
    !(pairwiseCommB l) ||
      (let sp := tabList (prodSpan l)
       !(decide sp.Nodup) || subsetB sp S || subsetB sp E3 || subsetB sp E1 || subsetB sp E2)

def invCentralizerB (T gs L : List P45) : Bool :=
  T.all fun c => !(decide (c * c = 1) && (gs.all fun x => decide (c * x = x * c))) || decide (c ∈ L)

def e16CentralizerCheck (_ : Unit := ()) : Bool :=
  let T := T0list ()
  invCentralizerB T (tabList Sgens) (Slist ()) && invCentralizerB T (tabList E3gens) (E3list ()) &&
    invCentralizerB T (tabList E1gens) (E1list ()) && invCentralizerB T (tabList E2gens) (E2list ())

def meetUtB (A S X : List P45) : Bool :=
  let z₀ := tab (u * t)
  X.any fun z => decide (z ≠ 1) && decide (z ∈ S) && (A.any fun c => decide (c * z * c⁻¹ = z₀))

def e16MeetCheck (_ : Unit := ()) : Bool :=
  let A := elemsT QA45
  let S := Slist ()
  meetUtB A S S && meetUtB A S (E3list ()) && meetUtB A S (E1list ()) && meetUtB A S (E2list ())

def commCount (a : P45) : ℕ :=
  let a := tab a
  ((elemsT QA45).filter fun g => g * a = a * g).length

def involutionCount (_ : Unit := ()) : ℕ :=
  ((elemsT QA45).filter fun g => g * g = 1 ∧ g ≠ 1).length

def orderThreeCount (_ : Unit := ()) : ℕ :=
  ((elemsT QA45).filter fun g => g * g * g = 1 ∧ g ≠ 1).length

def t0NormalizerCheck (_ : Unit := ()) : Bool :=
  let L := T0list ()
  let gs := tabList T0gens
  (elemsT QA45).all fun c => !(gs.all fun x => decide (c * x * c⁻¹ ∈ L)) || decide (c ∈ L)

def b5NormalizerCount (_ : Unit := ()) : ℕ :=
  let b := tab b5
  let pows := tabList [1, b, b * b, b * b * b, b * b * b * b]
  ((elemsT QA45).filter fun c => decide (c * b * c⁻¹ ∈ pows)).length

def NSlist (_ : Unit := ()) : List P45 :=
  let S := Slist ()
  let gs := tabList Sgens
  (elemsT QA45).filter fun c => gs.all fun x => decide (c * x * c⁻¹ ∈ S)

def centralizerSCheck (_ : Unit := ()) : Bool :=
  let S := Slist ()
  let gs := tabList Sgens
  (elemsT QA45).all fun c => !(gs.all fun x => decide (c * x = x * c)) || decide (c ∈ S)

def conjOrbit (N : List P45) (g : P45) : List P45 :=
  let g := tab g
  (N.map fun c => tab (c * g * c⁻¹)).dedup

def sOrbitCheck (N : List P45) : Bool :=
  let S := Slist ()
  let ot := conjOrbit N t
  let ou := conjOrbit N (u * t)
  decide (ot.length = 5) &&
    (elemsT QA45).all (fun g => !(ot.all fun o => decide (g * o = o * g)) || decide (g ∈ S)) &&
    (S.filter fun s => decide (s ≠ 1)).all (fun s => decide (s ∈ ot) || decide (s ∈ ou)) &&
    decide (tab (u * t) ∉ ot)

def Q8gens : List P45 := [alpha2, beta2]

def Q8list (_ : Unit := ()) : List P45 :=
  let a := tab alpha2
  let b := tab beta2
  tabList [1, a, a * a, a * a * a, b, b * a, b * (a * a), b * (a * a * a)]

def D8gens : List P45 := [t, u, v * beta]

def D8list (_ : Unit := ()) : List P45 :=
  let r := tab (t * (v * beta))
  let s := tab t
  tabList [1, r, r * r, r * r * r, s, s * r, s * (r * r), s * (r * r * r)]

def d8CenterCheck (_ : Unit := ()) : Bool :=
  let L := D8list ()
  let gs := tabList D8gens
  let z := tab (u * t)
  L.all fun x => !(gs.all fun g => decide (x * g = g * x)) || decide (x = 1) || decide (x = z)

end CFSG.RankThree.GF2n.Parrott

set_option maxRecDepth 400000

