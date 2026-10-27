module

public import CFSG.RankThree.PartTwo.Sec4.Item426A6Outer
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec4.LThreePiKind

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)
open Matrix

theorem isQuasisimple_SL_three (K : Type*) [Field K] [Finite K] :
    IsQuasisimple (SpecialLinearGroup (Fin 3) K) ∧
      aschbacherSolvableCore 3 (SpecialLinearGroup (Fin 3) K) = ⊥ := by
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  have hs : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 3) K) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 3 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  have hnc : ∃ a b : SpecialLinearGroup (Fin 3) K ⧸ Subgroup.center (SpecialLinearGroup (Fin 3) K),
      a * b ≠ b * a := by
    by_contra h
    have hab : ∀ a b : ProjectiveSpecialLinearGroup (Fin 3) K, a * b = b * a := fun a b => by
      by_contra hab
      exact h ⟨a, b, hab⟩
    have hP : Group.IsPerfect (ProjectiveSpecialLinearGroup (Fin 3) K) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have htop := hP.commutator_eq_top
    have hbot : commutator (ProjectiveSpecialLinearGroup (Fin 3) K) = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact hab b a
    have : Nontrivial (ProjectiveSpecialLinearGroup (Fin 3) K) := hs.toNontrivial
    exact bot_ne_top (hbot.symm.trans htop)
  have hq : IsQuasisimple (SpecialLinearGroup (Fin 3) K) :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient _ le_rfl hperf hs hnc
  refine ⟨hq, Sec13.aschbacherSolvableCore_eq_bot_of_isQuasisimple hq ?_⟩
  intro z
  refine ⟨1, ?_⟩
  have hz3 : (z : SpecialLinearGroup (Fin 3) K) ^ 3 = 1 := by
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp z.2
    rw [Fintype.card_fin] at hr
    have hm : ((z : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
      rw [← hrz, ← map_pow, hr, map_one]
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    have h1 := congrFun (congrFun hm i) j
    simpa using h1
  rw [pow_one]
  exact Subtype.ext hz3

theorem card_SL_three_ne (K : Type) [Field K] [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 3) K) ≠ 1080 := by
  rw [← Nat.card_congr (statedSLEquiv 3 K).toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three]
  set q := Nat.card K
  have hq : 2 ≤ q := Finite.one_lt_card
  rcases Nat.lt_or_ge q 3 with h2 | h3
  · have hq2 : q = 2 := by omega
    rw [hq2]
    norm_num
  · have h1 : 27 ≤ q ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left h3 3
    have h2 : 8 ≤ q ^ 2 - 1 := by
      have : 9 ≤ q ^ 2 := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left h3 2
      omega
    have h4 : 26 ≤ q ^ 3 - 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h4
    omega

section Fixed

variable {K : Type} [Field K]

abbrev fixedField (σ : K ≃+* K) : Subfield K :=
  σ.toRingHom.eqLocusField (RingHom.id K)

theorem nonempty_fixSub_slFieldAut_equiv (σ : K ≃+* K) :
    Nonempty (SpecialLinearGroup (Fin 3) (fixedField σ) ≃*
      fixSub (slFieldAut (Fin 3) K σ)) := by
  set K₀ := fixedField σ with hK₀
  set σs := slFieldAut (Fin 3) K σ with hσs
  let ι : SpecialLinearGroup (Fin 3) K₀ →* SpecialLinearGroup (Fin 3) K :=
    SpecialLinearGroup.map K₀.subtype
  have hι : Function.Injective ι := fun g g' h => by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => Subtype.ext ?_
    have := congrArg (fun A : SpecialLinearGroup (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) i j) h
    simpa [ι] using this
  have hσsapp : ∀ (A : SpecialLinearGroup (Fin 3) K) (i j : Fin 3),
      (σs A : Matrix (Fin 3) (Fin 3) K) i j = σ ((A : Matrix (Fin 3) (Fin 3) K) i j) :=
    fun _ _ _ => rfl
  have hrange : ι.range = fixSub σs := by
    ext A
    constructor
    · rintro ⟨g, rfl⟩
      rw [mem_fixSub]
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      rw [hσsapp]
      have hg : ((ι g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
          ((g : Matrix (Fin 3) (Fin 3) K₀) i j : K) := rfl
      rw [hg]
      exact RingHom.mem_eqLocusField.mp ((g : Matrix (Fin 3) (Fin 3) K₀) i j).2
    · intro hA
      rw [mem_fixSub] at hA
      have hmem : ∀ i j, (A : Matrix (Fin 3) (Fin 3) K) i j ∈ K₀ := fun i j => by
        rw [RingHom.mem_eqLocusField]
        have := congrArg (fun B : SpecialLinearGroup (Fin 3) K =>
          (B : Matrix (Fin 3) (Fin 3) K) i j) hA
        simpa [hσsapp] using this
      set M : Matrix (Fin 3) (Fin 3) K₀ := Matrix.of fun i j => ⟨_, hmem i j⟩ with hM
      have hMmap : M.map K₀.subtype = (A : Matrix (Fin 3) (Fin 3) K) := by
        ext i j
        rfl
      have hdet : M.det = 1 := by
        apply K₀.subtype_injective
        rw [RingHom.map_det, RingHom.mapMatrix_apply, hMmap, A.2, map_one]
      refine ⟨⟨M, hdet⟩, Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
      rfl
  exact ⟨(MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hrange)⟩

end Fixed

theorem slThreeFieldComponent : K426.SLThreeFieldComponent := by
  intro K _ _ _ α hα3 hF P hP htc
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  obtain ⟨φ, ⟨σ, rfl⟩, -, d, hd, hτ⟩ := hF
  have hcl : linearAutGroup 3 K = (conjAut 3 K).range := by
    rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
  have hd' : d ∈ (conjAut 3 K).range := by
    have : d ∈ linearAutGroup 3 K := hd
    rwa [hcl] at this
  obtain ⟨D, rfl⟩ := hd'
  set γ := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K D with hγ
  set σs := slFieldAut (Fin 3) K σ with hσs
  have hα : γ * σs * γ⁻¹ = α := by
    apply mulAut_eq_of_forall_inv_mul_mem_center hperf
    intro g
    rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one,
      ← descendAut_proj, ← descendAut_proj]
    have h1 : descendAut 3 K (γ * σs * γ⁻¹) = descendAut 3 K α := by
      rw [map_mul, map_mul, map_inv, hτ]
      rfl
    rw [h1]
  have hcongr : MulAut.congr γ σs = γ * σs * γ⁻¹ := by
    ext x
    rfl
  have hfix : MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id _) =
      (fixSub σs).map γ.toMonoidHom := by
    rw [← hα, ← hcongr, map_fixSub_eq]
  rw [hfix] at hP
  have hP₁ := map_mem_thetaComponentsIn γ.symm hP
  have hmm : ((fixSub σs).map γ.toMonoidHom).map γ.symm.toMonoidHom = fixSub σs := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id (fixSub σs)
    ext x
    simp
  rw [hmm] at hP₁
  obtain ⟨P₁', hP₁', hP₁eq⟩ := hP₁
  obtain ⟨e₀⟩ := nonempty_fixSub_slFieldAut_equiv σ
  set Q := SpecialLinearGroup (Fin 3) (fixedField σ)
  have hP₂ := map_mulEquiv_mem_thetaComponents Nat.prime_three e₀.symm hP₁'
  set P₂ := P₁'.map e₀.symm.toMonoidHom with hP₂def
  let eP : P ≃* P₂ :=
    ((P.equivMapOfInjective γ.symm.toMonoidHom γ.symm.injective).trans
      ((MulEquiv.subgroupCongr hP₁eq.symm).trans
        (P₁'.equivMapOfInjective (fixSub σs).subtype (fixSub σs).subtype_injective).symm)).trans
      (P₁'.equivMapOfInjective e₀.symm.toMonoidHom e₀.symm.injective)
  have htc₂ : IsTripleCover (P₂ ⧸ aschbacherSolvableCore 3 P₂) (alternatingGroup (Fin 6)) :=
    isTripleCover_of_mulEquiv (quotThetaEquiv eP) htc
  obtain ⟨hQq, hQθ⟩ := isQuasisimple_SL_three (fixedField σ)
  have hcard₂ : Nat.card (P₂ ⧸ aschbacherSolvableCore 3 P₂) = 1080 :=
    KFacts.KS14.card_eq_of_isExtOf_alternating_six htc₂.isExtOf
  have hP₂1 : P₂ ≠ ⊥ := by
    intro hbot
    have : Subsingleton P₂ := by rw [hbot]; infer_instance
    have h1 : Nat.card (P₂ ⧸ aschbacherSolvableCore 3 P₂) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨inferInstance, inferInstance⟩
    omega
  have hP₂top : P₂ = ⊤ := eq_top_of_isPerfect_of_isSubnormal hQq hP₂.1 hP₂.2.1 hP₂1
  have e₁ : P₂ ⧸ aschbacherSolvableCore 3 P₂ ≃* Q :=
    (quotThetaEquiv ((MulEquiv.subgroupCongr hP₂top).trans Subgroup.topEquiv)).trans
      ((QuotientGroup.quotientMulEquivOfEq hQθ).trans QuotientGroup.quotientBot)
  apply card_SL_three_ne (fixedField σ)
  rw [← hcard₂]
  exact (Nat.card_congr e₁.toEquiv).symm

end CFSG.RankThree.PartTwo.Sec4.Item426
