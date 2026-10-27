module

public import CFSG.Quasithin.Background.HSporLatInputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Inputs
public import CFSG.Sporadic.Schreier.M23Gens

public section

namespace CFSG.Quasithin.H.MathieuLat

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Sporadic.Schreier (m23GenA m23GenB)

@[expose] noncomputable def m23Sg : List ↥CFSG.Blueprint.NativeSporadic.M23 :=
  m23Qp.map fun p => (slpElts m23GenA m23GenB m23Prog).getD p.1 1

@[expose] noncomputable def m23SylTwo : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23 :=
  Subgroup.closure {x | x ∈ m23Sg}

@[expose] noncomputable def m23Member (j : ℕ) : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23 :=
  Subgroup.closure
    {x | x ∈ m23Sg ++ (CFSG.Quasithin.A312M23.m23MwLit[j]!).map (wordElt m23GenA m23GenB)}

end CFSG.Quasithin.H.MathieuLat

end
