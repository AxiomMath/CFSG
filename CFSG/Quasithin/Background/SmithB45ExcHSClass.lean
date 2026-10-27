module

public import Certificates.Certificate260390
public import CFSG.Quasithin.Background.SmithB45ExcHSRuLift
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSPerm
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.B45Exc.HS

open CFSG.Quasithin.B45Exc.Tab CFSG.Quasithin.B45Exc.HSRu CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.HSExcl CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Blueprint
open scoped commutatorElement

theorem hs_class_checks :
    hsClassCheck0 = true ∧ hsClassCheck1 = true ∧ hsClassCheck3 = true ∧ hsFixCheck = true :=
  Certificates.certificate260390

noncomputable abbrev hsT (k : ℕ) : Equiv.Perm (Fin 3850) := tp 3850 (hsCentTbl k)

section Reps


theorem hsT_sq {k : ℕ} (hk : k ∈ [5, 12, 21, 34]) : hsT k * hsT k = 1 := by
  have H := rows_sq
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at H
  obtain ⟨h0, h1, h2, h3⟩ := H
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem pRep_hsT {k : ℕ} (hk : k ∈ [5, 12, 21, 34]) : PRep 3850 (hsTP k) (hsT k) :=
  pRep_hsTP (hs_perm_check.2.2 k (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
    rcases hk with rfl | rfl | rfl | rfl <;> simp)) (hsT_sq hk)

theorem hsT_mem_P : hsT 5 ∈ hsP ∧ hsT 12 ∈ hsP := by
  have H := fun r hr => (hs_involution_centralizers.2.2.2.1 r hr).2.2.1
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at H
  obtain ⟨h0, h1, -, -⟩ := H
  exact ⟨by simpa using h0, by simpa using h1⟩

theorem hsT_not_mem_P : hsT 21 ∉ hsP ∧ hsT 34 ∉ hsP := by
  have H := fun r hr => (hs_involution_centralizers.2.2.2.1 r hr).2.2.1
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at H
  obtain ⟨-, -, h2, h3⟩ := H
  exact ⟨by simpa using h2, by simpa using h3⟩

theorem hs_inv_conj {x : Equiv.Perm (Fin 3850)} (hx : x ∈ hsR) (h2 : x * x = 1) (h1 : x ≠ 1) :
    ∃ g ∈ hsP, ∃ k ∈ [5, 12, 21, 34], x = g * hsT k * g⁻¹ := by
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  obtain ⟨r, hr, g, hg, hxg⟩ := hs_involution_centralizers.2.2.2.2.1 x hx hord
  refine ⟨g, hg, ?_⟩
  rcases rows_cases r hr with ⟨hrep, -⟩ | ⟨hrep, -⟩ | ⟨hrep, -⟩ | ⟨hrep, -⟩
  · exact ⟨5, by simp, by rw [hxg, hrep]⟩
  · exact ⟨12, by simp, by rw [hxg, hrep]⟩
  · exact ⟨21, by simp, by rw [hxg, hrep]⟩
  · exact ⟨34, by simp, by rw [hxg, hrep]⟩

end Reps

section Fix


theorem hs_fix : (fixFinset (hsT 5)).card = 170 ∧ (fixFinset (hsT 12)).card = 30 ∧
    (fixFinset (hsT 21)).card = 350 ∧ (fixFinset (hsT 34)).card = 46 := by
  have h := hs_class_checks.2.2.2
  simp only [hsFixCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h5, h12⟩, h21⟩, h34⟩ := h
  have r : ∀ k ∈ [5, 12, 21, 34], (fixFinset (hsT k)).card = fixCountA 3850 (hsTA k) :=
    fun k hk => (fixCountA_eq (pRep_hsT hk).1).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [r 5 (by simp), h5]
  · rw [r 12 (by simp), h12]
  · rw [r 21 (by simp), h21]
  · rw [r 34 (by simp), h34]

theorem hs_inv_of_fix {x : Equiv.Perm (Fin 3850)} (hx : x ∈ hsR) (h2 : x * x = 1) (h1 : x ≠ 1) :
    ((fixFinset x).card = 170 → ∃ g ∈ hsP, x = g * hsT 5 * g⁻¹) ∧
      ((fixFinset x).card = 30 → ∃ g ∈ hsP, x = g * hsT 12 * g⁻¹) ∧
      ((fixFinset x).card = 46 → ∃ g ∈ hsP, x = g * hsT 34 * g⁻¹) ∧
      ((fixFinset x).card = 170 ∨ (fixFinset x).card = 30 ∨ (fixFinset x).card = 350 ∨
        (fixFinset x).card = 46) := by
  obtain ⟨g, hg, k, hk, rfl⟩ := hs_inv_conj hx h2 h1
  rw [card_fix_conj]
  obtain ⟨f5, f12, f21, f34⟩ := hs_fix
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · rw [f5]; exact ⟨fun _ => ⟨g, hg, rfl⟩, by omega, by omega, by omega⟩
  · rw [f12]; exact ⟨by omega, fun _ => ⟨g, hg, rfl⟩, by omega, by omega⟩
  · rw [f21]; exact ⟨by omega, by omega, by omega, by omega⟩
  · rw [f34]; exact ⟨by omega, by omega, fun _ => ⟨g, hg, rfl⟩, by omega⟩

end Fix

section Wit


theorem hs_order5 : ∃ g ∈ hsP, (hsT 5 * (g * hsT 5 * g⁻¹)) ^ 5 = 1 ∧
    hsT 5 * (g * hsT 5 * g⁻¹) ≠ 1 := by
  obtain ⟨g, hg, hgr⟩ := regIn_hsP.word hsW0
  have ht := pRep_hsT (k := 5) (by simp)
  have hy : PRep 3850 (hsInvProd (hsTP 5) hsW0) (hsT 5 * (g * hsT 5 * g⁻¹)) :=
    ht.mul ((hgr.mul ht).mul hgr.inv)
  exact ⟨g, hg, orderCheck_spec hy hs_class_checks.1⟩

theorem hs_cfg_of_check {k : ℕ} (hk : k ∈ [5, 12, 21, 34]) {wg wx wy : List ℤ}
    (h : cfgCheck 3850 5 (hsInvProd (hsTP k) wg) (pWord 3850 hsGens wx)
      (pWord 3850 hsGens wy) = true) :
    ∃ g ∈ hsP, ∃ x ∈ hsP, ∃ y ∈ hsP, hsT k * (g * hsT k * g⁻¹) = ⁅x, y⁆ ∧ x ^ 5 = 1 ∧
      Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧ ⁅x, y⁆ ≠ 1 := by
  obtain ⟨g, hg, hgr⟩ := regIn_hsP.word wg
  obtain ⟨x, hx, hxr⟩ := regIn_hsP.word wx
  obtain ⟨y, hy, hyr⟩ := regIn_hsP.word wy
  have ht := pRep_hsT hk
  have hz : PRep 3850 (hsInvProd (hsTP k) wg) (hsT k * (g * hsT k * g⁻¹)) :=
    ht.mul ((hgr.mul ht).mul hgr.inv)
  exact ⟨g, hg, x, hx, y, hy, cfgCheck_spec hz hxr hyr h⟩

theorem hs_cfg1 : ∃ g ∈ hsP, ∃ x ∈ hsP, ∃ y ∈ hsP, hsT 12 * (g * hsT 12 * g⁻¹) = ⁅x, y⁆ ∧
    x ^ 5 = 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧ ⁅x, y⁆ ≠ 1 :=
  hs_cfg_of_check (by simp) hs_class_checks.2.1

theorem hs_cfg3 : ∃ g ∈ hsP, ∃ x ∈ hsP, ∃ y ∈ hsP, hsT 34 * (g * hsT 34 * g⁻¹) = ⁅x, y⁆ ∧
    x ^ 5 = 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧ ⁅x, y⁆ ≠ 1 :=
  hs_cfg_of_check (by simp) hs_class_checks.2.2.1

end Wit

end CFSG.Quasithin.B45Exc.HS
