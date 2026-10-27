module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankJReflection
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Arith
import CFSG.LocalAnalysis.StandardType.GGF4NbrAutReflKGReduce
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.ChevIndep
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.GenPeriodic
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OuterTwist

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggMaxRank_model
    {G : Type} [Group G] [Finite G] (hRig : GGLabelRigidInput)
    {Bs X : Subgroup G} {n : ℕ} (hΛ : LargeEvenInLambda2 ⟨.E8, 0, n⟩)
    (hinn : GGInnerDiagOn Bs X) (hlab : GGHasLabel ⟨.E8, 0, n⟩ (↥X ⧸ Subgroup.center ↥X)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ _ : ↥X ≃* adjointGroup .E8 K, Subgroup.center ↥X = ⊥ ∧
        Bs ≤ Subgroup.normalizer (X : Set G) ∧
        ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹ := by
  classical
  obtain ⟨hperf, lab', _hlab', hraw'⟩ := ggInnerDiagOn_relabel hRig hinn hΛ hlab
  obtain ⟨R₀, _instR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨_, _, hrest₀⟩ := hQ₀
  obtain ⟨_, hP₀⟩ := hrest₀
  obtain ⟨hlabeq, _, _⟩ := hP₀
  subst hlabeq
  have hInnAll : LargeEvenLabelAll ⟨.E8, 0, n⟩
      (LargeEvenSimpleGuard fun R _ I _ => I ⊆ LargeEvenInnSet R) :=
    largeEvenLabelAll_subset_inn hΛ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  obtain ⟨R, _instR, I, F, hQR, hguard⟩ := largeEvenRawDatum_exists (hInnAll _ hraw')
  obtain ⟨hsR, hnaR, hrest⟩ := hQR
  obtain ⟨θ, hP'⟩ := hrest
  obtain ⟨_, hBsN, hind⟩ := hP'
  have hI : I ⊆ LargeEvenInnSet R := hguard hsR hnaR
  have hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹ :=
    F4AutRefl.exists_conj_of_inn hperf θ hI hBsN hind
  obtain ⟨K, _instK, _finK, hKcard, hQK⟩ := hraw'
  obtain ⟨_, _, hrestK⟩ := hQK
  obtain ⟨θ_K, _hPK⟩ := hrestK
  obtain ⟨eQ⟩ := centerQuot_chevGroup_equiv K .E8
  let eAd : ↥X ⧸ Subgroup.center ↥X ≃* Blueprint.AdjointQuotient .E8 K := θ_K.trans eQ
  have hRq : IsQuasisimple R := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnaR).1
  have hf : Function.Surjective ((θ.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center ↥X))) :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ((θ.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center ↥X))).ker ≤
      Subgroup.center ↥X := by
    rw [MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
  have hperfX : Group.IsPerfect ↥X := Group.isPerfect_def.mpr hperf
  have hXq : IsQuasisimple ↥X :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperfX _ hf hker).mpr hRq
  have hZ : Subgroup.center ↥X = ⊥ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.center_eq_bot_of_E8 hXq hΛ.1 hKcard eAd
  let eX : ↥X ⧸ Subgroup.center ↥X ≃* ↥X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let eA : Blueprint.AdjointQuotient .E8 K ≃* adjointGroup .E8 K :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := .E8) (K := K))).trans
      QuotientGroup.quotientBot
  exact ⟨K, _instK, _finK, charP_two_of_card hKcard, hKcard, eX.symm.trans (eAd.trans eA),
    hZ, hBsN, hinner⟩

end CFSG.StandardType

end
