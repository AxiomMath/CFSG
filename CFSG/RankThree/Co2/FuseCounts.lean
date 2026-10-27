module

public import CFSG.RankThree.Co2.CrConj

public section

namespace CFSG.RankThree.Co2

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

@[expose] def InCls (S : Finset ℕ) (x : M22) : Prop := ∃ c ∈ S, CrConj (repMat c) x

@[expose] noncomputable def fuseN (S₁ S₂ S₃ : Finset ℕ) : ℕ :=
  Nat.card {x : M22 // x ∈ matGrp pWords3 ∧ InCls S₁ x ∧ InCls S₂ (x * repMat 0) ∧
    InCls S₃ (x * repMat 2)}

end CFSG.RankThree.Co2

end
