module

public import CFSG.Quasithin.Background.F7TwoInvSporModel
public import CFSG.Quasithin.Background.F7TwoInvL2Model
public import CFSG.RankThree.PartOne.KS.HeKit
public import CFSG.Sporadic.HeldB.InnerClass
public import Certificates.Certificate7417

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.Blueprint

theorem rep_heComm {y yi x xi : Array ℕ} {gy gx : Equiv.Perm (Fin 8330)} (hy : Rep 8330 y gy)
    (hyi : Rep 8330 yi gy⁻¹) (hx : Rep 8330 x gx) (hxi : Rep 8330 xi gx⁻¹) :
    Rep 8330 (heComm y yi x xi) (gy * gx * gy⁻¹ * gx⁻¹) := by
  have := rep_compA (rep_compA hy hx) (rep_compA hyi hxi)
  rwa [← mul_assoc] at this

theorem heNonTwo_spec {c : Array ℕ} {y : Equiv.Perm (Fin 8330)} (hc : Rep 8330 c y) {s m : ℕ}
    (hm : Odd m) (h : heNonTwo c s m = true) : ∀ n : ℕ, y ^ 2 ^ n ≠ 1 := by
  simp only [heNonTwo, Bool.and_eq_true, Bool.not_eq_true'] at h
  have h1 : y ^ (2 ^ s * m) = 1 := eq_of_eqA (rep_hePowA hc _) rep_idA h.1
  have h2 : y ^ 2 ^ s ≠ 1 := fun e => by
    rw [(eqA_iff (rep_hePowA hc _) rep_idA).2 e] at h
    exact absurd h.2 (by decide)
  exact pow_two_pow_ne_one_of_pow hm h1 h2

section Check


theorem heInvChk_spec :
    (∀ n : ℕ, (heGenPerm 0 * (heGenPerm 1 * heGenPerm 0) * (heGenPerm 0)⁻¹ *
      (heGenPerm 1 * heGenPerm 0)⁻¹) ^ 2 ^ n ≠ 1) ∧
    (∀ n : ℕ, (heT1P * heGenPerm 0 * heT1P⁻¹ * (heGenPerm 0)⁻¹) ^ 2 ^ n ≠ 1) ∧
    (∀ n : ℕ, (heT1P * (heGenPerm 1 * heGenPerm 0) * heT1P⁻¹ *
      (heGenPerm 1 * heGenPerm 0)⁻¹) ^ 2 ^ n ≠ 1) ∧
    heAutU * heGenPerm 0 = heGenPerm 0 * heAutU ∧
    (∀ n : ℕ, (heAutU * (heGenPerm 1 * heGenPerm 0) * heAutU⁻¹ *
      (heGenPerm 1 * heGenPerm 0)⁻¹) ^ 2 ^ n ≠ 1) := by
  have h := Certificates.certificate7417
  simp only [heInvChk, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have rA : Rep 8330 (heGen 0) (heGenPerm 0) := rep_heGen (by norm_num)
  have rB : Rep 8330 (heGen 1) (heGenPerm 1) := rep_heGen (by norm_num)
  have rAi : Rep 8330 (invCand 8330 (heGen 0)) (heGenPerm 0)⁻¹ := rep_heGen_inv (by norm_num)
  have rBi : Rep 8330 (invCand 8330 (heGen 1)) (heGenPerm 1)⁻¹ := rep_heGen_inv (by norm_num)
  have rBA : Rep 8330 (compA 8330 (heGen 1) (heGen 0)) (heGenPerm 1 * heGenPerm 0) :=
    rep_compA rB rA
  have rBAi : Rep 8330 (compA 8330 (invCand 8330 (heGen 0)) (invCand 8330 (heGen 1)))
      (heGenPerm 1 * heGenPerm 0)⁻¹ := by
    rw [mul_inv_rev]
    exact rep_compA rAi rBi
  have rT : Rep 8330 heT1Arr heT1P := rep_heT1
  have rTi : Rep 8330 (invCand 8330 heT1Arr) heT1P⁻¹ := rep_heT1_inv
  have rU : Rep 8330 heUArr heAutU := rep_heU
  have rUi : Rep 8330 heUArr heAutU⁻¹ := by rw [heAutU_inv]; exact rU
  exact ⟨heNonTwo_spec (rep_heComm rA rAi rBA rBAi) (by decide) h1,
    heNonTwo_spec (rep_heComm rT rTi rA rAi) (by decide) h2,
    heNonTwo_spec (rep_heComm rT rTi rBA rBAi) (by decide) h3,
    (eqA_iff (rep_compA rU rA) (rep_compA rA rU)).1 h4,
    heNonTwo_spec (rep_heComm rU rUi rBA rBAi) (by decide) h5⟩

end Check

section Classes


theorem invAutGen_heP :
    ∀ φ : MulAut heP, φ * φ = 1 → φ ≠ 1 → InvAutGen heP φ := by
  have hM := CFSG.RankThree.PartOne.heAutModel
  obtain ⟨h1, h2, h3, h4, h5⟩ := heInvChk_spec
  have hga : heGenPerm 0 ∈ heP := heGenPerm_mem (by norm_num)
  have hgb : heGenPerm 1 ∈ heP := heGenPerm_mem (by norm_num)
  have hgen0 : Subgroup.closure ({⟨heGenPerm 0, hga⟩, ⟨heGenPerm 1, hgb⟩} : Set heP) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top (by rw [heP]) hga hgb
  have hgen : Subgroup.closure
      ({⟨heGenPerm 0, hga⟩, ⟨heGenPerm 1 * heGenPerm 0, heP.mul_mem hgb hga⟩} : Set heP) = ⊤ := by
    rw [eq_top_iff, ← hgen0, Subgroup.closure_le]
    have hA : (⟨heGenPerm 0, hga⟩ : heP) ∈ Subgroup.closure
        ({⟨heGenPerm 0, hga⟩, ⟨heGenPerm 1 * heGenPerm 0, heP.mul_mem hgb hga⟩} : Set heP) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hBA : (⟨heGenPerm 1 * heGenPerm 0, heP.mul_mem hgb hga⟩ : heP) ∈ Subgroup.closure
        ({⟨heGenPerm 0, hga⟩, ⟨heGenPerm 1 * heGenPerm 0, heP.mul_mem hgb hga⟩} : Set heP) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    rintro x (rfl | rfl)
    · exact hA
    · have e : (⟨heGenPerm 1, hgb⟩ : heP) =
          ⟨heGenPerm 1 * heGenPerm 0, heP.mul_mem hgb hga⟩ * (⟨heGenPerm 0, hga⟩ : heP)⁻¹ :=
        Subtype.ext (by simp)
      rw [e]
      exact Subgroup.mul_mem _ hBA (Subgroup.inv_mem _ hA)
  refine invAutGen_of_model hM.le hM.conj_mem hM.surj hM.inj hgen
    [heGenPerm 0, heT1P, heAutU] ?_ ?_
  · intro x hxR hx2 hx1
    have hord : orderOf x = 2 := orderOf_eq_prime (by rwa [pow_two]) hx1
    by_cases hxP : x ∈ heP
    · rcases involution_conj_cases hxP hord with ⟨c, hc, hxc⟩ | ⟨c, hc, hxc⟩
      · exact ⟨heGenPerm 0, by simp, c, hc, hxc⟩
      · exact ⟨heT1P, by simp, c, hc, hxc⟩
    · obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU hxR hxP hord
      exact ⟨heAutU, by simp, g, hg, hxg⟩
  · intro ρ hρ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl
    · refine ⟨heP_le_heAutGroup hga, 1, one_mem _, ?_⟩
      simp only [one_mul, inv_one, mul_one]
      exact seedOK_pair (Or.inr rfl) (Or.inl h1) (Or.inr h1)
    · refine ⟨heP_le_heAutGroup heT1P_mem, 1, one_mem _, ?_⟩
      simp only [one_mul, inv_one, mul_one]
      exact seedOK_pair (Or.inl h2) (Or.inl h3) (Or.inl h2)
    · refine ⟨heAutU_mem_heAutGroup, 1, one_mem _, ?_⟩
      simp only [one_mul, inv_one, mul_one]
      exact seedOK_pair (Or.inr h4) (Or.inl h5) (Or.inr h5)

theorem invAutGen_carrier_He :
    ∀ φ : MulAut (NativeSporadic.Carrier .He), φ * φ = 1 → φ ≠ 1 →
      InvAutGen (NativeSporadic.Carrier .He) φ :=
  invAutGen_of_mulEquiv_forall heEquivP invAutGen_heP

end Classes

end CFSG.Quasithin.F7Two
