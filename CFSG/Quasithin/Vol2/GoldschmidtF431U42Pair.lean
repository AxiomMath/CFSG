module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Tau

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

theorem chkMisc_spec : chkMisc = true :=
  Certificates.certificate4161.2.2.2.2.2.2.2.1

theorem misc_spec :
    comp (comp (comp (tpTab.getD 31 []) (tpTab.getD 5 [])) (tpTab.getD 36 [])) (tpTab.getD 44 []) =
      yL ∧
    (∃ k < 5, Tl.contains (comp (comp (DL 1) (gTL k)) (evalW (invW (DW.getD 1 [])))) = false) ∧
    (∃ k < 5, Tl.contains (comp (comp (DL 2) (gTL k)) (evalW (invW (DW.getD 2 [])))) = false) ∧
    (∀ p ∈ L0, Tl.contains (tpTab.getD p []) = true) := by
  have h := chkMisc_spec
  simp only [chkMisc, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.all_eq_true,
    List.mem_range, Bool.not_eq_true', and_assoc] at h
  exact h

theorem y45_eq_s :
    y45 = sT 31 * sT 5 * sT 36 * sT 44 := by
  refine eq_of_repL (l := yL) repL_y ?_
  have h := misc_spec.1
  rw [← h]
  have e : ∀ (i : ℕ) (hi : i < 45), RepL (tpTab.getD i []) (sT ⟨i, hi⟩) := by
    intro i hi
    rw [tpTab_getD _ hi]
    exact repL_sT ⟨i, hi⟩
  have h31 := e 31 (by norm_num)
  have h5 := e 5 (by norm_num)
  have h36 := e 36 (by norm_num)
  have h44 := e 44 (by norm_num)
  exact repL_mul (repL_mul (repL_mul h31 h5) h36) h44

end CFSG.Quasithin.H13.F431.U42
