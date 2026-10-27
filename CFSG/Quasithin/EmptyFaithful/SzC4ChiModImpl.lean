module

public import CFSG.Quasithin.EmptyFaithful.SzC4ChiApi
public import CFSG.Quasithin.EmptyFaithful.SzC4ChiModDef
public import CFSG.Quasithin.EmptyFaithful.SzC4ChiModExact
public import CFSG.Quasithin.EmptyFaithful.SzC4ChiModVec
public import CFSG.Quasithin.EmptyFaithful.SzC4ChiModFin
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.SzC4

@[expose] noncomputable def deltaImpl : DeltaAPI where
  delta A _ _ φ := ChiMod.delta A φ
  delta_congr _ e φ φ' h := ChiMod.delta_congr e φ φ' h
  delta_one A _ _ _ := ChiMod.delta_one A
  delta_exact hM ι π hι hπ hex φA φM φB h7 h1 h2 :=
    ChiMod.delta_exact hM ι π hι hπ hex φA φM φB h7 h1 h2

theorem delta_vecAut {F : Type} [Field F] [Fintype F] (_hF : Fintype.card F = 2) (k : ℕ)
    (B : Matrix (Fin 3) (Fin 3) F) (hB : B ^ 7 = 1) :
    deltaImpl.delta (Multiplicative (Fin k → Fin 3 → F)) (vecAut k B hB) = k * chiMat B :=
  ChiMod.delta_vecAut_aux k B hB

end CFSG.Quasithin.SzC4
