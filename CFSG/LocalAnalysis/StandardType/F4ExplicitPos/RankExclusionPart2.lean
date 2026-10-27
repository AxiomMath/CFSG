module

public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart12
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CyclicFinish
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RankExclusionPart1

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.RankExclusion
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
      CFSG.LieType.AlgebraicGroups
  CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.StandardType.S2MathFi1035Pos
  CFSG.Open
open CFSG.StandardType.F4ExplicitPos.CyclicImplementers
open CFSG.StandardType.F4ExplicitPos.OrbitKernel
open CFSG.StandardType.F4ExplicitPos.CubicAction
open scoped Pointwise

section RankExclusion

theorem rank_exclusion_of_models
    {Ω : Type} [Field Ω] [CharP Ω 2] [IsSepClosed Ω] [IsAlgClosed Ω]
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω)
    {X : Type} [Group X] [Finite X] {G₀ B₁ K : Subgroup X}
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ)
    (Θ : B₁ →* ModGL Tag.F4 Ω)
    (hΘZ : ∀ b : B₁, Θ b ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ))
    (η : G₀ →* ModGL Tag.F4 Ω)
    (hBG : B₁ ≤ Subgroup.normalizer (G₀ : Set X))
    (hKG : K ≤ G₀)
    (hBK : B₁ ≤ Subgroup.normalizer (K : Set X))
    (hηinj : Function.Injective η)
    (hηact : ∀ (b : B₁) (y : G₀),
      η ((G₀.normalizerMonoidHom ⟨b, hBG b.2⟩) y) = Θ b * η y * (Θ b)⁻¹)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (D : LangDatum Tag.F4 Ω) (hρ : FrobRootMap D ρ)
    (hKorbit : (η.comp (Subgroup.inclusion hKG)).range ≤
      rootSpan Tag.F4 Ω (ratOrbit (fun u => ρ u) (componentRoots χ i)))
    (hfix : ∀ b : B₁, D.step (Θ b) = Θ b)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hBel : IsElemAbelian p B₁)
    (hcubic : p ^ 3 ≤ Nat.card (conjAction hBK).range)
    (hmodels : compRank (componentRoots χ i) ≤ 2 →
      ∀ (k : ℕ) (_hk : k ≠ 0)
        (_hk4 : 4 ≤ Nat.card (TauCeti.frobeniusFixedSubfield Ω 2 k)),
      let E := TauCeti.frobeniusFixedSubfield Ω 2 k
      let H0 := CFSG.StandardType.F4ExplicitPos.FiniteAction.rootSpanOver Ω E (componentRoots χ i)
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) E ≃* H0) ∨
      Nonempty (Matrix.SpecialLinearGroup (Fin 3) E ≃* H0) ∨
      Nonempty (StatedSp 2 E ≃* H0)) :
    3 ≤ compRank (componentRoots χ i) := by
  by_contra h3
  have h2 : compRank (componentRoots χ i) ≤ 2 := by omega
  have : Finite B₁ := Subtype.finite
  obtain ⟨k, hk, hk4, β, hβker⟩ := exists_betaOfGamma i Θ hΘZ halg
  have hγδ : (gammaOfTheta i Θ hΘZ).ker ≤ (conjAction hBK).ker :=
    gamma_ker_le_conjAction_ker i Θ hΘZ η hBG hKG hBK hηinj hηact ρ D hρ hKorbit hfix
  rcases hmodels h2 k hk hk4 with h2m | h3m | h4m
  · obtain ⟨e2⟩ := h2m
    let E := TauCeti.frobeniusFixedSubfield Ω 2 k
    let H0 := CFSG.StandardType.F4ExplicitPos.FiniteAction.rootSpanOver Ω E (componentRoots χ i)
    let qE : H0 ⧸ Subgroup.center H0 ≃*
        Matrix.SpecialLinearGroup (Fin 2) E ⧸
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E) :=
      quotientCenterCongr e2.symm
    let j : H0 ⧸ Subgroup.center H0 →*
        (GL (Fin 2) Ω ⧸ CFSG.Open.StatedScalars (Fin 2) Ω) :=
      (pslToProj (n := Fin 2) E.subtype).comp qE.toMonoidHom
    have hj : Function.Injective j :=
      (pslToProj_injective (n := Fin 2) E.subtype E.subtype_injective).comp qE.injective
    let lam : B₁ →* (GL (Fin 2) Ω ⧸ CFSG.Open.StatedScalars (Fin 2) Ω) := j.comp β
    have : Finite lam.range :=
      Finite.of_surjective lam.rangeRestrict (MonoidHom.rangeRestrict_surjective lam)
    have hlamker : lam.ker = (gammaOfTheta i Θ hΘZ).ker := by
      change (j.comp β).ker = (gammaOfTheta i Θ hΘZ).ker
      rw [MonoidHom.ker_comp_of_injective β j hj, hβker]
    have hlamδ : lam.ker ≤ (conjAction hBK).ker := by rw [hlamker]; exact hγδ
    have hcompare : Nat.card (conjAction hBK).range ≤ Nat.card lam.range :=
      card_range_le_of_ker_le lam (conjAction hBK) hlamδ
    have hEl : IsElemAbelian p lam.range :=
      CFSG.StandardType.isElemAbelian_range_of_isElemAbelian hBel lam
    let := ZMod.algebra Ω 2
    have : Algebra.IsAlgebraic (ZMod 2) Ω := halg
    have hbound : Nat.card lam.range ≤ p :=
      CFSG.StandardType.F4ExplicitPos.ProjectiveRank.card_le_p_of_isElemAbelian_statedProj_two
        (F := ZMod 2) (Ω := Ω) hp hp2 lam.range hEl
    have hle : p ^ 3 ≤ p := hcubic.trans (hcompare.trans hbound)
    have hlt : p < p ^ 3 := by
      have := pow_lt_pow_right₀ hp.one_lt (by norm_num : (1 : ℕ) < 3)
      simpa using this
    omega
  · obtain ⟨e3⟩ := h3m
    let E := TauCeti.frobeniusFixedSubfield Ω 2 k
    let H0 := CFSG.StandardType.F4ExplicitPos.FiniteAction.rootSpanOver Ω E (componentRoots χ i)
    let qE : H0 ⧸ Subgroup.center H0 ≃*
        Matrix.SpecialLinearGroup (Fin 3) E ⧸
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) E) :=
      quotientCenterCongr e3.symm
    let j : H0 ⧸ Subgroup.center H0 →*
        (GL (Fin 3) Ω ⧸ CFSG.Open.StatedScalars (Fin 3) Ω) :=
      (pslToProj (n := Fin 3) E.subtype).comp qE.toMonoidHom
    have hj : Function.Injective j :=
      (pslToProj_injective (n := Fin 3) E.subtype E.subtype_injective).comp qE.injective
    let lam : B₁ →* (GL (Fin 3) Ω ⧸ CFSG.Open.StatedScalars (Fin 3) Ω) := j.comp β
    have : Finite lam.range :=
      Finite.of_surjective lam.rangeRestrict (MonoidHom.rangeRestrict_surjective lam)
    have hlamker : lam.ker = (gammaOfTheta i Θ hΘZ).ker := by
      change (j.comp β).ker = (gammaOfTheta i Θ hΘZ).ker
      rw [MonoidHom.ker_comp_of_injective β j hj, hβker]
    have hlamδ : lam.ker ≤ (conjAction hBK).ker := by rw [hlamker]; exact hγδ
    have hcompare : Nat.card (conjAction hBK).range ≤ Nat.card lam.range :=
      card_range_le_of_ker_le lam (conjAction hBK) hlamδ
    have hEl : IsElemAbelian p lam.range :=
      CFSG.StandardType.isElemAbelian_range_of_isElemAbelian hBel lam
    let := ZMod.algebra Ω 2
    have : Algebra.IsAlgebraic (ZMod 2) Ω := halg
    have hbound : Nat.card lam.range ≤ p ^ 2 :=
      CFSG.StandardType.F4ExplicitPos.ProjectiveRank.card_le_sq_of_isElemAbelian_statedProj_three
        (F := ZMod 2) (Ω := Ω) hp hp2 lam.range hEl
    have hle : p ^ 3 ≤ p ^ 2 := hcubic.trans (hcompare.trans hbound)
    have hlt : p ^ 2 < p ^ 3 := by
      have := pow_lt_pow_right₀ hp.one_lt (by norm_num : (2 : ℕ) < 3)
      simpa using this
    omega
  · obtain ⟨e4⟩ := h4m
    let E := TauCeti.frobeniusFixedSubfield Ω 2 k
    let H0 := CFSG.StandardType.F4ExplicitPos.FiniteAction.rootSpanOver Ω E (componentRoots χ i)
    let qE : H0 ⧸ Subgroup.center H0 ≃*
        StatedSp 2 E ⧸ Subgroup.center (StatedSp 2 E) :=
      quotientCenterCongr e4.symm
    have hZ : Subgroup.center (StatedSp 2 E) = ⊥ :=
      center_statedSp_eq_bot (n := 2) (E := E)
    let qSp : StatedSp 2 E ⧸ Subgroup.center (StatedSp 2 E) ≃* StatedSp 2 E :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    let j : H0 ⧸ Subgroup.center H0 →* StatedSp 2 Ω :=
      (CFSG.StandardType.F4ExplicitPos.GeometricRank.spMapHom (n := 2) E.subtype).comp
        (qSp.toMonoidHom.comp qE.toMonoidHom)
    have hj : Function.Injective j :=
      (CFSG.StandardType.F4ExplicitPos.GeometricRank.spMapHom_injective (n := 2)
        E.subtype_injective).comp (qSp.injective.comp qE.injective)
    let lam : B₁ →* StatedSp 2 Ω := j.comp β
    have : Finite lam.range :=
      Finite.of_surjective lam.rangeRestrict (MonoidHom.rangeRestrict_surjective lam)
    have hlamker : lam.ker = (gammaOfTheta i Θ hΘZ).ker := by
      change (j.comp β).ker = (gammaOfTheta i Θ hΘZ).ker
      rw [MonoidHom.ker_comp_of_injective β j hj, hβker]
    have hlamδ : lam.ker ≤ (conjAction hBK).ker := by rw [hlamker]; exact hγδ
    have hcompare : Nat.card (conjAction hBK).range ≤ Nat.card lam.range :=
      card_range_le_of_ker_le lam (conjAction hBK) hlamδ
    have hEl : IsElemAbelian p lam.range :=
      CFSG.StandardType.isElemAbelian_range_of_isElemAbelian hBel lam
    let := ZMod.algebra Ω 2
    have : Algebra.IsAlgebraic (ZMod 2) Ω := halg
    have hbound : Nat.card lam.range ≤ p ^ 2 :=
      CFSG.StandardType.F4ExplicitPos.GeometricRank.card_le_sq_of_isElemAbelian_statedSp_two
        (F := ZMod 2) (Ω := Ω) hp hp2 lam.range hEl
    have hle : p ^ 3 ≤ p ^ 2 := hcubic.trans (hcompare.trans hbound)
    have hlt : p ^ 2 < p ^ 3 := by
      have := pow_lt_pow_right₀ hp.one_lt (by norm_num : (2 : ℕ) < 3)
      simpa using this
    omega

end RankExclusion

section ActualTheta

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] {p : ℕ}

variable {X : Type} [Group X] [Finite X] {B₁ : Subgroup X}

variable (Θ : B₁ →* ModGL Tag.F4 Ω) (a : Fin Tag.F4.rank → Ωˣ)

theorem hThetaZ_of_actual
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : ∀ i, a i ^ p = 1)
    (hadj : ∀ b : B₁, Θ b ∈ adjointGroup Tag.F4 Ω)
    (hcomm : ∀ b : B₁,
      rootDiagUnit Tag.F4 a * Θ b * (rootDiagUnit Tag.F4 a)⁻¹ = Θ b) :
    ∀ b : B₁, Θ b ∈
      torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots (rootCharHom a)) := by
  intro b
  exact CFSG.StandardType.F4ExplicitPos.CyclicFinish.f4_hgen (K := Ω) hp hp2 a ha
    ((mem_toralCentralizer (τ := Tag.F4) (K := Ω) (a := a) (g := Θ b)).2
      ⟨hadj b, hcomm b⟩)

end ActualTheta

section ActualRankExclusion

theorem rank_exclusion_actual_theta
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
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : ∀ i, a i ^ p = 1)
    (hadj : ∀ b : B₁, Θ b ∈ adjointGroup Tag.F4 Ω)
    (hcomm : ∀ b : B₁,
      rootDiagUnit Tag.F4 a * Θ b * (rootDiagUnit Tag.F4 a)⁻¹ = Θ b)
    (hBel : IsElemAbelian p B₁)
    (hcubic : p ^ 3 ≤ Nat.card (conjAction hBK).range)
    (hmodels : compRank (componentRoots (rootCharHom a) i) ≤ 2 →
      ∀ (k : ℕ) (_hk : k ≠ 0)
        (_hk4 : 4 ≤ Nat.card (TauCeti.frobeniusFixedSubfield Ω 2 k)),
      let E := TauCeti.frobeniusFixedSubfield Ω 2 k
      let H0 := CFSG.StandardType.F4ExplicitPos.FiniteAction.rootSpanOver Ω E
        (componentRoots (rootCharHom a) i)
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) E ≃* H0) ∨
      Nonempty (Matrix.SpecialLinearGroup (Fin 3) E ≃* H0) ∨
      Nonempty (StatedSp 2 E ≃* H0)) :
    3 ≤ compRank (componentRoots (rootCharHom a) i) :=
  rank_exclusion_of_models (χ := rootCharHom a) halg i Θ
    (hThetaZ_of_actual Θ a hp hp2 ha hadj hcomm)
    η hBG hKG hBK hηinj hηact ρ D hρ hKorbit hfix hp hp2 hBel hcubic hmodels

end ActualRankExclusion

end CFSG.StandardType.F4ExplicitPos.RankExclusion
end

end
