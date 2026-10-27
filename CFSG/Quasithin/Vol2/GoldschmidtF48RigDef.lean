module

public import CFSG.Quasithin.Recognition.F4Setting

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w

namespace LieSetting

@[expose] def CartanFPF (S : LieSetting.{u, w}) : Prop :=
  ∃ b u₁ u₂ : S.ι.Γ, S.ι.graph.dist S.ι.xv b = S.m ∧ S.ι.graph.Adj S.ι.xv u₁ ∧
    S.ι.graph.Adj S.ι.xv u₂ ∧ u₁ ≠ u₂ ∧
    ∃ h : S.ι.G0, h • S.ι.xv = S.ι.xv ∧ h • b = b ∧ h • u₁ = u₁ ∧ h • u₂ = u₂ ∧
      ∀ q ∈ S.Qbar S.ι.xv, h * q * h⁻¹ = q → q = 1

@[expose] def FaithfulOnType (S : LieSetting.{u, w}) (s : Bool) : Prop :=
  ∀ k : S.ι.G0, (∀ v : S.ι.Γ, CosetGeom.vtype v = s → k • v = v) → k = 1

end LieSetting

end CFSG.Quasithin
