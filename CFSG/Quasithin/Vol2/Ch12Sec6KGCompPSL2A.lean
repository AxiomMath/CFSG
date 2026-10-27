module

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerInvolutionFusion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.RankThree.PartTwo.KFacts

variable {F : Type} [Field F] [Finite F]

theorem pglAction_injective (hF : IsOddPrimePower (Nat.card F)) (h3 : 3 < Nat.card F) :
    Function.Injective (pglAction F) := by
  rw [pglAction_eq_native F hF h3]
  exact pgl2InnerAutPSL2_injective F hF h3

theorem exists_pglAction_inv_of_reflection (hF : IsOddPrimePower (Nat.card F))
    (h3 : 3 < Nat.card F) {U : Subgroup (PGL2 F)} {w : PGL2 F} (hUc : IsCyclic U)
    (hU2 : 2 ∣ Nat.card U) (hwU : w ∉ U) (hww : w * w = 1)
    (hinv : ∀ t ∈ U, w * t * w⁻¹ = t⁻¹)
    (hUJ : ¬ U ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    {g : PGL2 F} (hg : BenderSuzuki.PFAppendixIII.IsInvolution g) :
    ∃ x : PSL2 F, orderOf x = Nat.card U / 2 ∧ pglAction F g x = x⁻¹ := by
  classical
  set J := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range with hJ
  have hJ2 : J.index = 2 := pgl2_psl2Range_index_eq_two F hF
  have hJn : J.Normal := Subgroup.normal_of_index_eq_two hJ2
  have hcomm : commutator (PGL2 F) = J := pgl2_commutator_eq_psl2_range_of_card_gt_three F hF h3
  obtain ⟨u, hu⟩ := hUc.exists_generator
  have huo : orderOf (u : PGL2 F) = Nat.card U := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hu
  have huJ : (u : PGL2 F) ∉ J := by
    intro h
    apply hUJ
    intro t ht
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hu ⟨t, ht⟩)
    have : t = (u : PGL2 F) ^ k := by
      rw [← Subgroup.coe_zpow, hk]
    rw [this]
    exact J.zpow_mem h k
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have key : ∀ w₁ : PGL2 F, BenderSuzuki.PFAppendixIII.IsInvolution w₁ →
      w₁ * u * w₁⁻¹ = (u : PGL2 F)⁻¹ → (w₁ ∈ J ↔ g ∈ J) →
      ∃ x : PSL2 F, orderOf x = Nat.card U / 2 ∧ pglAction F g x = x⁻¹ := by
    intro w₁ hw₁ hw₁u hcl
    obtain ⟨h, hh⟩ : ∃ h : PGL2 F, h * w₁ * h⁻¹ = g := by
      by_cases hgJ : g ∈ J
      · have hw₁J := hcl.mpr hgJ
        rw [← hcomm] at hgJ hw₁J
        obtain ⟨h, -, hh⟩ := pgl2_inner_involutions_conjugate hF h3 hw₁J hw₁ hgJ hg
        exact ⟨h, hh⟩
      · have hw₁J : w₁ ∉ J := fun h => hgJ (hcl.mp h)
        rw [← hcomm] at hgJ hw₁J
        exact isConj_iff.mp (pgl2_outer_involutions_conjugate F hF h3 hw₁ hg hw₁J hgJ)
    set y : PGL2 F := h * (u : PGL2 F) ^ 2 * h⁻¹ with hy
    have hyJ : y ∈ J := hJn.conj_mem _ (Subgroup.sq_mem_of_index_two hJ2 _) h
    obtain ⟨x, hx⟩ := hyJ
    refine ⟨x, ?_, ?_⟩
    · rw [← orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective x, hx, hy,
        ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_pow' _ two_ne_zero, huo,
        Nat.gcd_eq_right hU2]
    · apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      rw [toPGL_pglAction, map_inv, hx, ← hh, hy]
      have h2 : w₁ * (u : PGL2 F) ^ 2 * w₁⁻¹ = ((u : PGL2 F) ^ 2)⁻¹ := by
        rw [pow_two, mul_inv_rev,
          show w₁ * (↑u * ↑u) * w₁⁻¹ = (w₁ * ↑u * w₁⁻¹) * (w₁ * ↑u * w₁⁻¹) by group, hw₁u]
      calc h * w₁ * h⁻¹ * (h * ↑u ^ 2 * h⁻¹) * (h * w₁ * h⁻¹)⁻¹ =
          h * (w₁ * ↑u ^ 2 * w₁⁻¹) * h⁻¹ := by group
        _ = (h * ↑u ^ 2 * h⁻¹)⁻¹ := by rw [h2]; group
  have hwI : BenderSuzuki.PFAppendixIII.IsInvolution w := by
    refine ⟨fun h1 => hwU (h1 ▸ U.one_mem), by rw [pow_two, hww]⟩
  have hwu : w * u * w⁻¹ = (u : PGL2 F)⁻¹ := hinv u u.2
  by_cases hcl : w ∈ J ↔ g ∈ J
  · exact key w hwI hwu hcl
  · refine key (w * u) ⟨fun h1 => hwU ?_, ?_⟩ ?_ ?_
    · have : w = (u : PGL2 F)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact U.inv_mem u.2
    · rw [pow_two]
      calc w * ↑u * (w * ↑u) = (w * ↑u * w⁻¹) * ↑u := by rw [hwinv]; group
        _ = 1 := by rw [hwu]; group
    · calc w * ↑u * ↑u * (w * ↑u)⁻¹ = w * ↑u * w⁻¹ := by group
        _ = (u : PGL2 F)⁻¹ := hwu
    · rw [Subgroup.mul_mem_iff_of_index_two hJ2]
      tauto

theorem exists_pglAction_inv_split (hF : IsOddPrimePower (Nat.card F)) (h3 : 3 < Nat.card F)
    {g : PGL2 F} (hg : BenderSuzuki.PFAppendixIII.IsInvolution g) :
    ∃ x : PSL2 F, orderOf x = (Nat.card F - 1) / 2 ∧ pglAction F g x = x⁻¹ := by
  obtain ⟨U, w, hUc, hUcard, hwU, hww, hinv, hUJ⟩ := pgl2_split_torus_reflection_data F
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, n, -, hp, -, hq⟩ := hF
    rw [hq]
    exact hp.pow
  have hU2 : 2 ∣ Nat.card U := by
    rw [hUcard]
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  rw [← hUcard]
  exact exists_pglAction_inv_of_reflection hF h3 hUc hU2 hwU hww hinv (hUJ hodd) hg

theorem exists_pglAction_inv_nonsplit (hF : IsOddPrimePower (Nat.card F)) (h3 : 3 < Nat.card F)
    {g : PGL2 F} (hg : BenderSuzuki.PFAppendixIII.IsInvolution g) :
    ∃ x : PSL2 F, orderOf x = (Nat.card F + 1) / 2 ∧ pglAction F g x = x⁻¹ := by
  obtain ⟨p, n, hp, hpo, -, hq⟩ := id hF
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, w, hUc, hUcard, hwU, hww, hinv, hUJ⟩ := pgl2_nonsplit_torus_reflection_data hq
  have hodd : Odd (Nat.card F) := by
    rw [hq]
    exact hpo.pow
  have hU2 : 2 ∣ Nat.card U := by
    rw [hUcard]
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  rw [← hUcard]
  exact exists_pglAction_inv_of_reflection hF h3 hUc hU2 hwU hww hinv (hUJ hodd) hg

theorem ringAut_sq_eq_one {p f : ℕ} (hp : p.Prime) (hFc : Nat.card F = p ^ f)
    (hf : f = 1 ∨ f = 2) (σ : F ≃+* F) : σ ^ 2 = 1 := by
  obtain ⟨hcard, -⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F hFc
  have : Finite (RingAut F) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have h1 : σ ^ Nat.card (RingAut F) = 1 := pow_card_eq_one'
  rcases hf with rfl | rfl
  · rw [hcard, pow_one] at h1
    rw [h1, one_pow]
  · rwa [hcard] at h1

theorem ringAut_eq_one {p : ℕ} (hp : p.Prime) (hFc : Nat.card F = p) (σ : F ≃+* F) : σ = 1 := by
  obtain ⟨hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F (by rw [hFc, pow_one])
  have : Finite (RingAut F) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have h1 : σ ^ Nat.card (RingAut F) = 1 := pow_card_eq_one'
  rwa [hcard, pow_one] at h1

theorem pow_four_mem_range_conj (hF : IsOddPrimePower (Nat.card F)) {p f : ℕ} (hp : p.Prime)
    (hFc : Nat.card F = p ^ f) (hf : f = 1 ∨ f = 2) (α : MulAut (PSL2 F)) :
    α ^ 4 ∈ (MulAut.conj : PSL2 F →* MulAut (PSL2 F)).range := by
  obtain ⟨g, σ, rfl⟩ := exists_pglAction_mul_psl2FieldAut α
  have hs2 : psl2FieldAut F σ * psl2FieldAut F σ = 1 := by
    rw [← map_mul, ← pow_two, ringAut_sq_eq_one hp hFc hf σ, map_one]
  have hsinv : (psl2FieldAut F σ)⁻¹ = psl2FieldAut F σ := inv_eq_of_mul_eq_one_right hs2
  have h2 : (pglAction F g * psl2FieldAut F σ) ^ 2 = pglAction F (g * pgl2FieldAut F σ g) := by
    rw [pow_two, map_mul, ← psl2FieldAut_mul_pglAction_mul_inv σ g, hsinv]
    simp only [mul_assoc]
  obtain ⟨y, hy⟩ :=
    Subgroup.sq_mem_of_index_two (pgl2_psl2Range_index_eq_two F hF) (g * pgl2FieldAut F σ g)
  refine ⟨y, ?_⟩
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, ← map_pow, ← hy, pglAction_toPGL]

theorem mem_range_conj_of_pow_three_eq_one (hF : IsOddPrimePower (Nat.card F)) {p f : ℕ}
    (hp : p.Prime) (hFc : Nat.card F = p ^ f) (hf : f = 1 ∨ f = 2) {α : MulAut (PSL2 F)}
    (hα : α ^ 3 = 1) : α ∈ (MulAut.conj : PSL2 F →* MulAut (PSL2 F)).range := by
  have h := pow_four_mem_range_conj hF hp hFc hf α
  rwa [show α ^ 4 = α by rw [pow_succ, hα, one_mul]] at h

omit [Finite F] in
@[expose] noncomputable def sl2Transv (t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t

omit [Finite F] in
theorem transvection_pow {i j : Fin 2} (hij : i ≠ j) (t : F) (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection hij t ^ n =
      Matrix.SpecialLinearGroup.transvection hij ((n : F) * t) := by
  induction n with
  | zero => simp [Matrix.SpecialLinearGroup.transvection_coeff_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← Matrix.SpecialLinearGroup.transvection_add]
    congr 1
    push_cast
    ring

omit [Finite F] in
theorem orderOf_mk_transvection {i j : Fin 2} (hij : i ≠ j) {p : ℕ} [hp : Fact p.Prime]
    [CharP F p] {t : F} (ht : t ≠ 0) :
    orderOf (QuotientGroup.mk (Matrix.SpecialLinearGroup.transvection hij t) : PSL2 F) = p := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← QuotientGroup.mk_pow, transvection_pow, CharP.cast_eq_zero, zero_mul,
      Matrix.SpecialLinearGroup.transvection_coeff_zero, QuotientGroup.mk_one]
  · intro h1
    rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.transvection_mem_center_iff] at h1
    exact ht h1

omit [Finite F] in
theorem psl2FieldAut_sl2Transv (σ : F ≃+* F) (t : F) :
    psl2FieldAut F σ (QuotientGroup.mk (sl2Transv t) : PSL2 F) =
      QuotientGroup.mk (sl2Transv (σ t)) := by
  show psl2RingEquiv σ (QuotientGroup.mk' _ (sl2Transv t)) = QuotientGroup.mk' _ (sl2Transv (σ t))
  rw [psl2RingEquiv_mk]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Transv, Matrix.SpecialLinearGroup.transvection_coe]

omit [Finite F] in
theorem sl2Transv_inv (t : F) : (sl2Transv t)⁻¹ = sl2Transv (-t) :=
  Matrix.SpecialLinearGroup.transvection_inv _ t

end CFSG.Quasithin.H13.S126C
