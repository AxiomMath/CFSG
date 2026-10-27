module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoD4
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6SU6Y
public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenInput
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6SU6Unitary
public import CFSG.RankThree.PartOne.CTP.SeitzFineU5
public import CFSG.RankThree.PartOne.KF.SU5Model

public noncomputable section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups
open CFSG.LieType.SeitzGeneration.ExcHigh


variable (K : Type) [Field K] [Finite K]

@[expose] def PhiJoin (σ : K ≃+* K) (a : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
    Subgroup (twistedE6RootGroup K σ) :=
  ⨆ γ : {γ : Fin TwistTag.E6.tag.rank → ℤ // IsRoot TwistTag.E6.tag γ},
    phiTwoCompIn (twistedE6RootGroup K σ) a γ.1

@[expose] def SU6AmbientCut (σ : K ≃+* K) (a : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K) : Prop :=
  (E6GraphLevi.unitarySL σ.toRingHom).map Ψ ≤
    (PhiJoin K σ a).map (twistedE6RootGroup K σ).subtype

@[expose] def CenterCut (σ : K ≃+* K) (a : ModGL TwistTag.E6.tag (AlgebraicClosure K)) : Prop :=
  (centerHom σ.toRingHom).range ≤ PhiJoin K σ a

variable {K}

theorem phiJoin_eq_top_of_su6_center (σ : K ≃+* K)
    (a : ModGL TwistTag.E6.tag (AlgebraicClosure K)) (ε : K)
    (Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K) (hΨ : TwSU6.IsPsiTw σ.toRingHom ε Ψ)
    (hσσ : ∀ c, σ (σ c) = c) (hε0 : ε ≠ 0) (hε : σ ε = -ε)
    (hA : SU6AmbientCut K σ a Ψ) (hC : CenterCut K σ a) :
    PhiJoin K σ a = ⊤ := by
  apply eq_top_of_orbitRankOneGroup_le
  intro i
  fin_cases i
  · exact (TwSU6.orbitRankOneGroup_le_map hΨ hσσ hε0 hε _ (by decide)).trans hA
  · exact (TwSU6.orbitRankOneGroup_le_map hΨ hσσ hε0 hε _ (by decide)).trans hA
  · exact (TwSU6.orbitRankOneGroup_le_map hΨ hσσ hε0 hε _ (by decide)).trans hA
  · intro y hy
    obtain ⟨A, hA⟩ := orbitRankOneGroup_le_range_rankOneFix σ.toRingHom orbCenter orbCenter_card hy
    exact ⟨centerHom σ.toRingHom A, hC ⟨A, rfl⟩, hA⟩

@[expose] def frameLangSL2 [CharP K 2] (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) : SL(2, K) :=
  ⟨!![ζ, ζ ^ 2; 1, 1], by
    rw [Matrix.det_fin_two_of]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (-1 : K) * hζ + ζ * h2⟩

@[expose] def frameLang [CharP K 2] (ζ : K) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    ModGL TwistTag.E6.tag K :=
  rootSL2 TwistTag.E6.tag K (frameRoot 0) (frameLangSL2 ζ hζ) *
    rootSL2 TwistTag.E6.tag K (frameRoot 1) (frameLangSL2 ζ hζ) *
    rootSL2 TwistTag.E6.tag K (frameRoot 2) (frameLangSL2 ζ hζ) *
    rootSL2 TwistTag.E6.tag K (frameRoot 3) (frameLangSL2 ζ hζ)

end CFSG.StandardType.PhiTwoRootGen

end
