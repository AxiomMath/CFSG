module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCross

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.RankThree.PartTwo.Sec21.Item223CensusResProof
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)

namespace Res424Six


theorem cross_of_diagonal {G : Type} [Group G] [Finite G] (X : Subgroup G) (y : G)
    (hy3 : y ^ 3 = 1) (hdiag : KFacts.InducesStdKind X y .diagonal) :
    (∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K - 1 →
      ∀ (e : X ⧸ aschbacherSolvableCore 3 X ≃* projectiveSL 3 K)
        (hy : y ∈ Subgroup.normalizer (X : Set G)),
        inducedAutHom X e ⟨y, hy⟩ ∈ linearAutGroup 3 K) ∧
    (∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K - 1 →
      ∀ (e : X ⧸ aschbacherSolvableCore 3 X ≃* Matrix.SpecialLinearGroup (Fin 3) K)
        (hy : y ∈ Subgroup.normalizer (X : Set G)),
        descendAut 3 K (inducedAutHom X e ⟨y, hy⟩) ∈ linearAutGroup 3 K) ∧
    (∀ (p f : ℕ) (K : Type) [Field K] (hK : UnitaryFieldData p f K), 3 ∣ p ^ f + 1 →
      ∀ (e : X ⧸ aschbacherSolvableCore 3 X ≃* unitaryPSU hK 3)
        (hy : y ∈ Subgroup.normalizer (X : Set G)),
        inducedAutHom X e ⟨y, hy⟩ ∈ (psuConj hK).range) ∧
    ∀ (p f : ℕ) (K : Type) [Field K] (hK : UnitaryFieldData p f K) (hq : 2 < p ^ f),
      3 ∣ p ^ f + 1 →
      ∀ (e : X ⧸ aschbacherSolvableCore 3 X ≃* unitarySU p f K 3)
        (hy : y ∈ Subgroup.normalizer (X : Set G)),
        MulAut.congr (suCenterEquiv hK hq)
          (centerDescend _ (inducedAutHom X e ⟨y, hy⟩)) ∈ (psuConj hK).range := by
  cases hdiag with
  | psl2 K h => exact (Sec21.Item223CensusProof.not_inducesKindPSL2_diagonal hy3 h).elim
  | psp r K hr h =>
    exact (Sec21.Item223CensusProof.not_inducesKindPSp_diagonal
      (by rcases hr with hr | ⟨rfl, -⟩ <;> omega) hy3 h).elim
  | psp4even F h => exact (Sec21.Item223CensusProof.not_inducesKindPSp4Even_diagonal h).elim
  | g2 K hK3 hK4 h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    exact (hni hτ).elim
  | sz a K ha hK h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    exact (hni hτ).elim
  | triality f hf K hK σ hσ h =>
    obtain ⟨e, hx, h⟩ := h
    exact h.elim
  | largeRee a ha K hK h =>
    obtain ⟨e, hx, hτ, hni⟩ := h
    exact (hni hτ).elim
  | psl n K' hn h =>
    obtain ⟨e', hx, hτ, hni⟩ := h
    have h3 : 3 ∣ n ∧ 3 ∣ Nat.card K' - 1 := by
      by_contra h3
      exact hni (Sec21.Item223CensusProof.isInnerAut_of_mem_linearAutGroup_of_pow_three hn h3
        hτ (inducedAutHom_pow_eq_one X e' hx hy3))
    rcases (show n = 3 ∨ 6 ≤ n by obtain ⟨k, hk⟩ := h3.1; omega) with rfl | hn6
    · refine ⟨fun K _ _ hK e hy => ?_, fun K _ _ hK e hy => ?_,
        fun p f K _ hK h3' e hy => ?_, fun p f K _ hK hq h3' e hy => ?_⟩
      · rw [inducedAutHom_eq_congr X e' e]
        exact congr_mem_linearAutGroup hK h3.2 _ hτ
      · exact (false_of_center (e'.symm.trans e) (center_projectiveSL_three K')
          (center_SL_three_ne_bot hK)).elim
      · exact ((isEmpty_projectiveSL_three_equiv_unitaryPSU h3.2 hK h3').false
          (e'.symm.trans e)).elim
      · exact (false_of_center (e'.symm.trans e) (center_projectiveSL_three K')
          (center_unitarySU_three_ne_bot hK h3')).elim
    · have hH : Sec21.HighInv (X ⧸ aschbacherSolvableCore 3 X) :=
        (highInv_projectiveSL hn6 h3.2).of_mulEquiv e'
      exact ⟨fun K _ _ hK e _ => (not_highInv_projectiveSL_three hK e hH).elim,
        fun K _ _ hK e _ => (not_highInv_SL_three hK e hH).elim,
        fun p f K _ hK h3' e _ => (not_highInv_unitaryPSU_three hK h3' e hH).elim,
        fun p f K _ hK _ h3' e _ => (not_highInv_unitarySU_three hK h3' e hH).elim⟩
  | sl n K' hn h =>
    obtain ⟨e', hx, hτ, hni⟩ := h
    have h3 : 3 ∣ n ∧ 3 ∣ Nat.card K' - 1 := by
      by_contra h3
      exact hni (Sec21.Item223CensusProof.isInnerAut_of_mem_linearAutGroup_of_pow_three hn h3
        hτ (by rw [← map_pow, inducedAutHom_pow_eq_one X e' hx hy3, map_one]))
    rcases (show n = 3 ∨ 6 ≤ n by obtain ⟨k, hk⟩ := h3.1; omega) with rfl | hn6
    · refine ⟨fun K _ _ hK e hy => ?_, fun K _ _ hK e hy => ?_,
        fun p f K _ hK h3' e hy => ?_, fun p f K _ hK _ _ e hy => ?_⟩
      · exact (false_of_center (e.symm.trans e') (center_projectiveSL_three K)
          (center_SL_three_ne_bot h3.2)).elim
      · rw [inducedAutHom_eq_congr X e' e]
        exact descendAut_congr_mem_linearAutGroup hK h3.2 _ hτ
      · by_cases hq : 2 < p ^ f
        · exact (false_of_center (e.symm.trans e') (center_unitaryPSU_three hK hq)
            (center_SL_three_ne_bot h3.2)).elim
        · have hq2 : p ^ f = 2 := by
            have := two_le_pow_of_unitaryFieldData hK
            omega
          have h1 := Nat.card_congr (e.symm.trans e').toEquiv
          rw [card_unitaryPSU_three_two hK hq2, card_SL_three] at h1
          have h2 := sl3Poly_lt (q := 2) le_rfl
            (show 2 < Nat.card K' by have := four_le_card h3.2; omega)
          norm_num at h2
          omega
      · exact ((isEmpty_SL_three_equiv_unitarySU (K := K') hK).false (e'.symm.trans e)).elim
    · have hH : Sec21.HighInv (X ⧸ aschbacherSolvableCore 3 X) :=
        (highInv_SL hn6 h3.2).of_mulEquiv e'
      exact ⟨fun K _ _ hK e _ => (not_highInv_projectiveSL_three hK e hH).elim,
        fun K _ _ hK e _ => (not_highInv_SL_three hK e hH).elim,
        fun p f K _ hK h3' e _ => (not_highInv_unitaryPSU_three hK h3' e hH).elim,
        fun p f K _ hK _ h3' e _ => (not_highInv_unitarySU_three hK h3' e hH).elim⟩
  | @psu3 p' f' K' _ hK' hq' h =>
    obtain ⟨e', hx, hτ, hni⟩ := h
    have h3 : 3 ∣ p' ^ f' + 1 := by
      by_contra h3
      obtain ⟨B, hB⟩ := hτ
      rw [← hB] at hni
      exact hni (Sec21.Item223CensusProof.isInnerAut_psuConj_of_not_dvd h3 B)
    refine ⟨fun K _ _ hK e hy => ?_, fun K _ _ hK e hy => ?_,
      fun p f K _ hK h3' e hy => ?_, fun p f K _ hK hq h3' e hy => ?_⟩
    · exact ((isEmpty_projectiveSL_three_equiv_unitaryPSU hK hK' h3).false (e.symm.trans e')).elim
    · exact (false_of_center (e'.symm.trans e) (center_unitaryPSU_three hK' hq')
        (center_SL_three_ne_bot hK)).elim
    · rw [inducedAutHom_eq_congr X e' e]
      exact congr_mem_psuConj_range hK hK' h3' h3 hq' _ hτ
    · exact (false_of_center (e'.symm.trans e) (center_unitaryPSU_three hK' hq')
        (center_unitarySU_three_ne_bot hK h3')).elim
  | @su3 p' f' K' _ hK' hq' h =>
    obtain ⟨e', hx, hτ, hni⟩ := h
    have h3 : 3 ∣ p' ^ f' + 1 := by
      by_contra h3
      obtain ⟨B, hB⟩ := hτ
      rw [← hB] at hni
      exact hni (Sec21.Item223CensusProof.isInnerAut_psuConj_of_not_dvd h3 B)
    refine ⟨fun K _ _ hK e hy => ?_, fun K _ _ _ e hy => ?_,
      fun p f K _ hK h3' e hy => ?_, fun p f K _ hK hq h3' e hy => ?_⟩
    · exact (false_of_center (e.symm.trans e') (center_projectiveSL_three K)
        (center_unitarySU_three_ne_bot hK' h3)).elim
    · exact ((isEmpty_SL_three_equiv_unitarySU (K := K) hK').false (e.symm.trans e')).elim
    · by_cases hq : 2 < p ^ f
      · exact (false_of_center (e.symm.trans e') (center_unitaryPSU_three hK hq)
          (center_unitarySU_three_ne_bot hK' h3)).elim
      · have hq2 : p ^ f = 2 := by
          have := two_le_pow_of_unitaryFieldData hK
          omega
        have h1 := Nat.card_congr (e.symm.trans e').toEquiv
        rw [card_unitaryPSU_three_two hK hq2, card_unitarySU_three' hK'] at h1
        have h2 := su3Poly_lt (q := 2) le_rfl hq'
        norm_num at h2
        omega
    · rw [inducedAutHom_eq_congr X e' e]
      exact centerDescend_congr_mem_psuConj_range hK hK' hq hq' _ hτ

section Proj

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal] {K : Type} [Field K]
  {p f : ℕ} {π : Bool}

open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

theorem exists_isPGLAtP_of_diagonal (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hθ : aschbacherSolvableCore 3 L = ⊥) (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {x : G}
    (hx3 : x ^ 3 = 1) (hdiag : KFacts.InducesStdKind L x .diagonal) : ∃ y, IsPGLAtP e x y := by
  obtain ⟨hlin, -, hpsu, -⟩ := cross_of_diagonal L x hx3 hdiag
  have := hK.finite
  set xN : Subgroup.normalizer (L : Set G) := ⟨x, mem_normalizer_of_normal x⟩ with hxN
  cases π
  ·
    have h := hK.unitary
    set ψ := psuEquivUnitary h with hψ
    set e' := (thetaBotEquiv hθ).trans (e.trans ψ) with he'
    have hind := inducedAutHom_thetaBot hθ e ψ xN
    set α := MulAut.congr ψ (slAct e xN) with hα
    have h3 : 3 ∣ p ^ f + 1 := by
      change p ^ f % 3 = 2 at hq
      omega
    have hD : α ∈ (psuConj h).range := by
      rw [← hind]
      exact hpsu p f K h h3 e' xN.2
    have hcoe : ∀ s : unitarySU p f K 3,
        slAct e xN (suToPsu p f K s) = ψ.symm (α (unitaryProj h 3 s)) := by
      intro s
      rw [hα, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, ← psuEquivUnitary_suToPsu h, MulEquiv.symm_apply_apply]
    have hproj : ∀ t : unitarySU p f K 3, ψ.symm (unitaryProj h 3 t) = suToPsu p f K t := by
      intro t
      rw [MulEquiv.symm_apply_eq, psuEquivUnitary_suToPsu]
    obtain ⟨A, hA⟩ := hD
    refine ⟨A, (mem_glPi_false h).mpr A.2, fun m => ?_⟩
    obtain ⟨s, rfl⟩ := suToPsu_surjective (p := p) (f := f) (K := K) m
    rw [hcoe, ← hA, psuConj_unitaryProj, hproj, coe_suToPsu, coe_suToPsu, coe_suConj, map_mul,
      map_mul, Subgroup.coe_inv, map_inv]
  ·
    set ψ := pslEquivProjective (p ^ f) K with hψ
    set e' := (thetaBotEquiv hθ).trans (e.trans ψ) with he'
    have hind := inducedAutHom_thetaBot hθ e ψ xN
    set α := MulAut.congr ψ (slAct e xN) with hα
    have h3 : 3 ∣ Nat.card K - 1 := by
      have hc : Nat.card K = p ^ f := hK.card
      change p ^ f % 3 = 1 at hq
      rw [hc]
      omega
    have hD : α ∈ linearAutGroup 3 K := by
      rw [← hind]
      exact hlin K h3 e' xN.2
    have hcoe : ∀ s : SpecialLinearGroup (Fin 3) K,
        slAct e xN (slToPsl (p ^ f) K s) = ψ.symm (α (proj 3 K s)) := by
      intro s
      rw [hα, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, ← pslEquivProjective_slToPsl (q := p ^ f),
        MulEquiv.symm_apply_apply]
    have hproj : ∀ t : SpecialLinearGroup (Fin 3) K,
        ψ.symm (proj 3 K t) = slToPsl (p ^ f) K t := by
      intro t
      rw [MulEquiv.symm_apply_eq, pslEquivProjective_slToPsl]
    obtain ⟨A, hA⟩ := (mem_linearAutGroup_iff (n := 3) (K := K)).mp hD
    refine ⟨A, mem_glPi_true _ _, fun m => ?_⟩
    obtain ⟨s, rfl⟩ := slToPsl_surjective (K := K) (p ^ f) m
    rw [hcoe, ← hA, conjAut_proj, hproj, coe_slToPsl, coe_slToPsl, toGL_slConjugation, map_mul,
      map_mul, map_inv]

end Proj

section SL

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal] {K : Type} [Field K]
  {p f : ℕ} {π : Bool}

open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

theorem exists_isPGLAt_of_diagonal (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) [Group.IsPerfect L] (hθ : aschbacherSolvableCore 3 L = ⊥)
    (e : L ≃* slPi π 3 (p ^ f) K) {x : G} (hx3 : x ^ 3 = 1)
    (hdiag : KFacts.InducesStdKind L x .diagonal) : ∃ y, IsPGLAt e x y := by
  obtain ⟨-, hsl, -, hsu⟩ := cross_of_diagonal L x hx3 hdiag
  have := hK.finite
  set xN : Subgroup.normalizer (L : Set G) := ⟨x, mem_normalizer_of_normal x⟩ with hxN
  cases π
  ·
    have h := hK.unitary
    set ψ := slPiFalseEquiv p f K with hψ
    set e' := (thetaBotEquiv hθ).trans (e.trans ψ) with he'
    have hind := inducedAutHom_thetaBot hθ e ψ xN
    set β := MulAut.congr ψ (slAct e xN) with hβ
    have : Group.IsPerfect (unitarySU p f K 3) :=
      Group.IsPerfect.ofSurjective (f := (e.trans ψ).toMonoidHom) (e.trans ψ).surjective
    set α := MulAut.congr (suCenterEquiv h hq2) (centerDescend _ β) with hα
    have h3 : 3 ∣ p ^ f + 1 := by
      change p ^ f % 3 = 2 at hq
      omega
    have hD : α ∈ (psuConj h).range := by
      rw [hα, ← hind]
      exact hsu p f K h hq2 h3 e' xN.2
    have hlift : ∀ γ : MulAut (unitarySU p f K 3),
        MulAut.congr (suCenterEquiv h hq2) (centerDescend _ γ) = α → β = γ := by
      intro γ hγ
      have hγ' : centerDescend _ γ = centerDescend _ β := (MulAut.congr _).injective hγ
      apply mulAut_eq_of_inv_mul_mem_center
      intro g
      have h1 := congrArg (fun τ : MulAut (unitarySU p f K 3 ⧸ Subgroup.center _) =>
        τ (g : unitarySU p f K 3 ⧸ Subgroup.center _)) hγ'
      simp only [centerDescend_mk] at h1
      exact QuotientGroup.eq.mp h1
    have hcoe : ∀ s : slPi false 3 (p ^ f) K, ((slAct e xN s : slPi false 3 (p ^ f) K) :
        GL (Fin 3) K) = ((β (ψ s) : unitarySU p f K 3) : GL (Fin 3) K) := by
      intro s
      have h1 : β (ψ s) = ψ (slAct e xN s) := by
        rw [hβ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply]
      rw [h1, hψ, coe_slPiFalseEquiv]
    obtain ⟨A, hA⟩ := hD
    have hβA := hlift (suConj h A) (by rw [congr_centerDescend_suConj, hA])
    refine ⟨A, (mem_glPi_false h).mpr A.2, fun s => ?_⟩
    rw [hcoe, hβA, coe_suConj, hψ, coe_slPiFalseEquiv]
    rfl
  ·
    set ψ : slPi true 3 (p ^ f) K ≃* SpecialLinearGroup (Fin 3) K := slPiTrueEquiv (p ^ f) K
      with hψ
    set e' := (thetaBotEquiv hθ).trans (e.trans ψ) with he'
    have hind := inducedAutHom_thetaBot hθ e ψ xN
    set β := MulAut.congr ψ (slAct e xN) with hβ
    have : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
      Group.IsPerfect.ofSurjective (f := (e.trans ψ).toMonoidHom) (e.trans ψ).surjective
    set α := descendAut 3 K β with hα
    have h3 : 3 ∣ Nat.card K - 1 := by
      have hc : Nat.card K = p ^ f := hK.card
      change p ^ f % 3 = 1 at hq
      rw [hc]
      omega
    have hD : α ∈ linearAutGroup 3 K := by
      rw [hα, ← hind]
      exact hsl K h3 e' xN.2
    have hlift : ∀ γ : MulAut (SpecialLinearGroup (Fin 3) K), descendAut 3 K γ = α → β = γ := by
      intro γ hγ
      apply mulAut_eq_of_inv_mul_mem_center
      intro g
      rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one,
        ← descendAut_proj, ← descendAut_proj, hγ]
    have hcoe : ∀ s : slPi true 3 (p ^ f) K, ((slAct e xN s : slPi true 3 (p ^ f) K) :
        GL (Fin 3) K) = Matrix.SpecialLinearGroup.toGL (β (ψ s)) := by
      intro s
      have h1 : β (ψ s) = ψ (slAct e xN s) := by
        rw [hβ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply]
      rw [h1, hψ, toGL_slPiTrueEquiv]
    rw [linearAutGroup_eq_range] at hD
    obtain ⟨A, hA⟩ := hD
    have hβA := hlift (slConjugation 3 K A) hA
    refine ⟨A, mem_glPi_true _ _, fun s => ?_⟩
    rw [hcoe, hβA, toGL_slConjugation, hψ, toGL_slPiTrueEquiv]

end SL

end Res424Six

end CFSG.RankThree.PartTwo.Sec4
