module

public import CFSG.Quasithin.Background.D2Decomp

public section

namespace CFSG.Quasithin

open CFSG.Open

structure Setting151c {V : Type*} [CommGroup V] [Finite V] (X Tb Xc : Subgroup (MulAut V)) :
    Prop where
  sq : ∀ v : V, v ^ 2 = 1
  solv : Group.IsSolvable ↥X
  o2 : pCoreOf 2 X = ⊥
  sqtk : IsQuotientOfSQTKTC ↥X
  qhat : qhatOf X ≤ 2
  syl : Tb ∈ sylow2Of X
  gen : ∀ W : Subgroup V, (∀ g ∈ X, ∀ z ∈ fixV Tb, g z ∈ W) → W = ⊤
  xc_le : Xc ≤ X
  tb_le : Tb ≤ Xc
  xc_ne : ¬ X ≤ Xc
  hU : ∀ Z₁ : Subgroup V, Z₁ ≤ fixV Tb → Z₁ ≠ ⊥ → X ⊓ centSub Z₁ ≤ Xc
  star : ∀ W : Subgroup V, W ≠ ⊥ → (∀ g ∈ X, ∀ w ∈ W, g w ∈ W) →
    W ≤ Subgroup.closure {x | ∃ g ∈ Xc, ∃ z ∈ fixV Tb ⊓ W, g z = x} → False
  central : ∀ c ∈ fixV (fittingOf (Jhat X)), ∀ j ∈ Jhat X, j c = c

end CFSG.Quasithin
