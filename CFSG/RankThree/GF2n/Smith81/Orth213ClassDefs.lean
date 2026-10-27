module

public import CFSG.RankThree.GF2n.Smith81.OrthModel

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthClass

open QuadraticMap

variable {K : Type} [Field K] {ι : Type}

@[expose] noncomputable def nSing (qU : QuadraticForm K (ι → K)) (P : (ι → K) → Prop) : ℕ :=
  Nat.card {s : ι → K // P s ∧ qU s = 0}

@[expose] noncomputable def tCount (qU : QuadraticForm K (ι → K))
    (I : Set ((ι → K) × (ι → K))) : ℕ :=
  Nat.card {p : (ι → K) × (ι → K) // p ∈ I ∧ PairTypeA qU p}

@[expose] def Ish (qU : QuadraticForm K (ι → K)) (u w : ι → K) (β : K) :
    Set ((ι → K) × (ι → K)) :=
  {p | polar qU p.1 u = 0 ∧ ∃ t : K, p.2 = t • u ∧ polar qU p.1 w = β * t}

end CFSG.RankThree.GF2n.Smith81.OrthClass
