module

public import Certificates.Kernel.Co2Census.CCRep
public import Certificates.Kernel.Co2Census.CCK8

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

set_option maxRecDepth 100000

section CC


theorem cc_card_inv : Nat.card {y : Cz // y * y = 1} = 178688 := by
  have e : ∀ y : Cz, y * y = 1 ↔ ccPred 1 1 false y := by
    intro y
    simp [ccPred]
  rw [Nat.card_congr (Equiv.subtypeEquivRight e)]
  let w : ℕ → Cz := fun l => ⟨sElt (l + 1), S0_le_Cz (sElt_mem_S0 _)⟩
  have hs : ConjSteps repK stL 2 fun l => piC (w l) := by
    refine conjSteps_of (fun l hl => ?_) (fun l hl => ?_)
    · rw [piC_S0 (sElt_mem_S0 _)]
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · rw [← F1_misc_spec.2.1]
        exact repK_sElt 1
      · rw [← F1_misc_spec.2.2.1]
        exact repK_sElt 2
    · obtain ⟨-, -, h2, h3, -⟩ := L_misc_spec
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · exact ⟨h2, ABIt_lt (by norm_num)⟩
      · exact ⟨h3, ABIt_lt (by norm_num)⟩
  have hw : ∀ l < 2, ∀ y, ccPred 1 1 false (w l * y * (w l)⁻¹) ↔ ccPred 1 1 false y := by
    intro l _ y
    exact hpPred_conj (by rw [mul_one, one_mul]) (by rw [mul_one, one_mul]) false y
  have hL := F1_misc_spec.2.2.2.1
  have hdist : ∀ j < 5, ∀ j' < 5, Lrt j = Lrt j' → j = j' := by
    intro j hj j' hj' e
    have h1 : Lrt j = [0, 1, 64, 379, 1324].getD j 0 := by
      rw [← hL, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
    have h2 : Lrt j' = [0, 1, 64, 379, 1324].getD j' 0 := by
      rw [← hL, List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
        List.getElem_range]
    rw [h1, h2] at e
    interval_cases j <;> interval_cases j' <;> simp_all
  have hrk : ∀ j < 5, Lrt j < 5104 ∧ rtOf LXt (Lrt j) = Lrt j ∧
      repK (sElt (f1c j)) (LPt (Lrt j)) := fun j hj =>
    ⟨(L_misc_spec.2.2.2.2.2.2.1 j hj).1, (L_misc_spec.2.2.2.2.2.2.1 j hj).2.1, f1n_rep hj⟩
  have hsupp : ∀ y, ccPred 1 1 false y → ∃ i < 5104, repK (piC y) (LPt i) := by
    intro y hy
    have h2 := congrArg piC hy.2
    rw [map_mul, map_one] at h2
    exact s0_inv_iff.1 ⟨piC_mem y, h2⟩
  rw [card_query piC _ (hi := 80) hs hw L_tree (fun i hi => L_roots_spec hi) hdist hrk hsupp
      (by norm_num),
    ← F1C_total, ← sum_range_list]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  congr 1
  have hn : f1c j < 1451520 := by interval_cases j <;> decide
  exact fib_cc_eq QK_eq repK_one' piC_one' repK_one' piC_one' false hn

end CC

end CertificateChecks.KernelCo2Census

end
