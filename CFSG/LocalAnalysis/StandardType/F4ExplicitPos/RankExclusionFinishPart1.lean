module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ComponentAttachPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankExclusionPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CTNative
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.LowRankModelsPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterProofFastPart2

@[expose] public section

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.Open

open CFSG.StandardType.LieCore

open CFSG.StandardType.F4ExplicitPos.RankExclusion

open CFSG.StandardType.F4ExplicitPos.LowRankModels

open CFSG.StandardType.F4ExplicitPos.ComponentAttach

open CFSG.StandardType.F4ExplicitPos.CyclicFinish

open CFSG.StandardType.F4ExplicitPos.InnerDirect

open CFSG.StandardType.F4ExplicitPos.CenterProofFast

open CFSG.StandardType.F4ExplicitPos.CubicLiteral

open CFSG.StandardType.F4ExplicitPos.CubicAction

open CFSG.StandardType.F4ExplicitPos.AmbientAction

open CFSG.StandardType.F4ExplicitPos.Quasisimple

open CFSG.StandardType.F4ExplicitPos.CTNative

open scoped Pointwise

namespace CFSG.StandardType.F4ExplicitPos.RankExclusionFinish

theorem frobeniusFixed_component_models_of_coord
    {Ω : Type} [Field Ω] [CharP Ω 2] [IsSepClosed Ω] [IsAlgClosed Ω]
    (a : Fin Tag.F4.rank → Ωˣ)
    (i : KernelComponent (rootCharHom a))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : ∀ j, a j ^ p = 1) :
    compRank (componentRoots (rootCharHom a) i) ≤ 2 →
      ∀ (k : ℕ) (_hk : k ≠ 0)
        (_hk4 : 4 ≤ Nat.card (TauCeti.frobeniusFixedSubfield Ω 2 k)),
      let E := TauCeti.frobeniusFixedSubfield Ω 2 k
      let H0 := CFSG.StandardType.F4ExplicitPos.FiniteAction.rootSpanOver Ω E
        (componentRoots (rootCharHom a) i)
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) E ≃* H0) ∨
      Nonempty (Matrix.SpecialLinearGroup (Fin 3) E ≃* H0) ∨
      Nonempty (StatedSp 2 E ≃* H0) := by
  have ha' : a ^ p = 1 := funext ha
  have hm : rootDiagUnit Tag.F4 a ^ p = rootDiagUnit Tag.F4 (a ^ p) :=
    rootDiagUnit_pow a p
  rw [ha', rootDiagUnit_one] at hm
  exact CFSG.StandardType.F4ExplicitPos.LowRankModels.frobeniusFixed_component_models a i hp hp2 hm

theorem center_adjointGroup_f4_charTwo_eq_bot
    {k : Type} [Field k] [CharP k 2] :
    Subgroup.center (adjointGroup .F4 k) = ⊥ :=
  CFSG.StandardType.F4ExplicitPos.CenterProofFast.center_adjointGroup_F4_charTwo_eq_bot

theorem rank_exclusion_actual_theta_models
    {Ω : Type} [Field Ω] [CharP Ω 2] [IsSepClosed Ω] [IsAlgClosed Ω]
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω)
    {X : Type} [Group X] [Finite X] {G₀ B₁ K : Subgroup X}
    (a : Fin Tag.F4.rank → Ωˣ) (i : KernelComponent (rootCharHom a))
    (Θ : B₁ →* ModGL Tag.F4 Ω)
    (η : G₀ →* ModGL Tag.F4 Ω)
    (hBG : B₁ ≤ Subgroup.normalizer (G₀ : Set X))
    (hKG : K ≤ G₀)
    (hBK : B₁ ≤ Subgroup.normalizer (K : Set X))
    (hηinj : Function.Injective η)
    (hηact : ∀ (b : B₁) (y : G₀),
      η ((G₀.normalizerMonoidHom ⟨b, hBG b.2⟩) y) = Θ b * η y * (Θ b)⁻¹)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (D : LangDatum Tag.F4 Ω) (hρ : FrobRootMap D ρ)
    (hKorbit : (η.comp (Subgroup.inclusion hKG)).range ≤
      rootSpan Tag.F4 Ω (ratOrbit (fun u => ρ u) (componentRoots (rootCharHom a) i)))
    (hfix : ∀ b : B₁, D.step (Θ b) = Θ b)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : ∀ j, a j ^ p = 1)
    (hadj : ∀ b : B₁, Θ b ∈ adjointGroup Tag.F4 Ω)
    (hcomm : ∀ b : B₁,
      rootDiagUnit Tag.F4 a * Θ b * (rootDiagUnit Tag.F4 a)⁻¹ = Θ b)
    (hBel : IsElemAbelian p B₁)
    (hcubic : p ^ 3 ≤ Nat.card (conjAction hBK).range) :
    3 ≤ compRank (componentRoots (rootCharHom a) i) :=
  CFSG.StandardType.F4ExplicitPos.RankExclusion.rank_exclusion_actual_theta
    (Ω := Ω) halg a i Θ η hBG hKG hBK hηinj hηact ρ D hρ hKorbit hfix
    hp hp2 ha hadj hcomm hBel hcubic
    (frobeniusFixed_component_models_of_coord a i hp hp2 ha)

end CFSG.StandardType.F4ExplicitPos.RankExclusionFinish
end

end
