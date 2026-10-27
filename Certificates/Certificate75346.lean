module

public import CFSG.Sporadic.HN.LocalK
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporZTwo
import Certificates.Kernel.HNLocal.ZFacts
public import CFSG.Certificates.Kernel.HNLocalSound
public import CFSG.Sporadic.Th.F2Spec

public section

open CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK CFSG.LocalAnalysis.WeakClosure81

public section

namespace Certificates

open CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK CFSG.LocalAnalysis.WeakClosure81
  CFSG.LocalAnalysis.WeakClosure81.SporHN CertificateChecks.KernelHNLocalZ Subgroup

open CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK CFSG.LocalAnalysis.WeakClosure81 in
theorem certificate75346 : ∃ (T : Subgroup (J dHN)) (hc : ∀ p ∈ T, wG 13 * p = p * wG 13)
    (hs : wG 13 * wG 13 = 1), Nat.card T = 2 ^ 14 ∧ wG 13 ∈ T ∧ wG 13 ≠ 1 ∧
      (∀ x ∈ T, (∀ p ∈ T, x * p = p * x) → x = 1 ∨ x = wG 13) ∧
      Nat.card (zTwoOf T (wG 13) hc hs) = 4 ∧
      Subgroup.centralizer {wG 13} ⊔
        Subgroup.normalizer (zTwoOf T (wG 13) hc hs : Set (J dHN)) = ⊤ := by
  obtain ⟨T, w, hc, hs, hT, htT, ht1, hZ, hw1, hwt, hV, -, -, hg, ha, hb, hl⟩ := hn75346_facts
  refine ⟨T, hc, hs, hT, htT, ht1, fun x hx h => (hZ x).1 ⟨hx, h⟩, ?_, ?_⟩
  · have hinv : (wG 13)⁻¹ = wG 13 := inv_eq_of_mul_eq_one_right hs
    have d1 : wG 13 * w ≠ 1 := fun h => hwt (by rw [← hinv]; exact eq_inv_of_mul_eq_one_right h)
    have d2 : wG 13 * w ≠ wG 13 := fun h => hw1 (mul_left_cancel (h.trans (mul_one _).symm))
    have d3 : wG 13 * w ≠ w := fun h => ht1 (mul_right_cancel (h.trans (one_mul _).symm))
    have hS : (zTwoOf T (wG 13) hc hs : Set (J dHN)) = {1, wG 13, w, wG 13 * w} := by
      ext y
      rw [SetLike.mem_coe, hV]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have h4 : ({1, wG 13, w, wG 13 * w} : Set (J dHN)).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem (by simp [Ne.symm ht1, Ne.symm hw1, Ne.symm d1]),
        Set.ncard_insert_of_notMem (by simp [Ne.symm hwt, Ne.symm d2]),
        Set.ncard_pair (Ne.symm d3)]
    rw [← h4, ← hS]
    exact Nat.card_coe_set_eq _
  · have hmem : ∀ z ∈ hnAWord ++ hnBWord, topZ z ∈ centralizer {wG 13} ⊔
        normalizer (zTwoOf T (wG 13) hc hs : Set (J dHN)) := by
      intro z hz
      obtain ⟨hz0, h⟩ := hl z hz
      unfold topZ
      rcases h with h | ⟨h, hcm⟩
      · rw [if_neg (by omega)]
        split_ifs
        · exact (le_sup_right : normalizer _ ≤ centralizer {wG 13} ⊔ _) hg
        · exact (le_sup_right : normalizer _ ≤ centralizer {wG 13} ⊔ _) (inv_mem hg)
      · rw [if_pos h]
        have hcen : wG (z.natAbs - 1) ∈ centralizer {wG 13} := mem_centralizer_singleton_iff.2 hcm
        refine (le_sup_left : centralizer {wG 13} ≤ _ ⊔ _) ?_
        unfold progZ
        split_ifs
        · exact hcen
        · exact inv_mem hcen
    rw [eq_top_iff, ← closure_ab dHN, closure_le]
    rintro _ (rfl | rfl)
    · rw [ha]
      exact list_prod_mem fun y hy => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
        exact hmem z (List.mem_append_left _ hz)
    · rw [hb]
      exact list_prod_mem fun y hy => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
        exact hmem z (List.mem_append_right _ hz)

end Certificates

end

end
