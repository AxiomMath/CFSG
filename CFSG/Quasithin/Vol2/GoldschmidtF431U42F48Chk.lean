module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Dat
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Recognition.CertPermList
public import Certificates.Data.U42F431Check

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431

@[expose] def f48Cj (w : List ℕ) : List ℕ := f48N1 ++ w ++ invW f48N1

@[expose] def f48T (k : ℕ) : List ℕ :=
  (List.range 45).map fun m => if f48Near.contains m then m else applyW (f48Bz.getD m []) k

theorem f48_n1_fix : applyW f48N1 0 = 0 := by decide +kernel

theorem f48_bz_spec : ∀ m < 45, f48Near.contains m = false →
    inB (evalW (f48Bz.getD m [])) = true ∧ inB (evalW (f48Cj (f48Bz.getD m []))) = true ∧
      applyW (f48Bz.getD m []) f48F0 = m := by decide +kernel

theorem f48_stab_spec : ∀ s ∈ f48Stab, inB (evalW s) = true ∧ inB (evalW (f48Cj s)) = true ∧
    applyW s f48F0 = f48F0 := by decide +kernel

theorem f48_keyCheck : ∀ k < 45, (f48T k).Nodup → (∀ s ∈ f48Stab, applyW s k = k) →
    f48T k = idL ∨ f48T k = f48T 2 := by decide +kernel

theorem f48_rel_spec : inB (evalW f48Rel) = true ∧ inB (evalW f48B2) = true ∧
    evalW (f48N1 ++ f48Rel ++ f48N1 ++ f48Rel ++ f48N1 ++ f48Rel) = idL := by decide +kernel

theorem f48_relCheck : compL (compL (compL (evalW f48N1) (f48T 2)) (evalW f48Rel))
    (compL (compL (compL (evalW f48N1) (f48T 2)) (evalW f48Rel))
      (compL (compL (evalW f48N1) (f48T 2)) (evalW f48Rel))) ≠ idL := by decide +kernel

theorem f48_linesCheck : ∀ k < 27,
    (lnTab.getD k []).contains 0 = true →
    sameSet (lnTab.getD k []) L0 = true ∨
    sameSet (lnTab.getD k []) (imgSet (evalW f48N1) L0) = true ∨
    sameSet (lnTab.getD k []) (imgSet (evalW (f48B2 ++ f48N1)) L0) = true := by
  decide +kernel

theorem f48_near_coll : ∀ m < 45, f48Near.contains m = true →
    ∃ k < 27, (lnTab.getD k []).contains 0 = true ∧ (lnTab.getD k []).contains m = true := by
  decide +kernel

end CFSG.Quasithin.H13.F431.U42
