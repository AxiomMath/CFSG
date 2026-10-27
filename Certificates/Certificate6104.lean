module

public import CFSG.Sporadic.Recognition.JankoWongPresInputs
import Certificates.Kernel.CosPresTab.F6104
import Certificates.Kernel.CosPresTab.JWGlue
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.JankoWong

namespace Certificates

open CFSG.CosetTable CFSG.Sporadic.Recognition.JankoWong in
theorem certificate6104 : ∀ neg : Bool,
    (Finite (PG 6 (jwRels neg)) ∧ Nat.card (PG 6 (jwRels neg)) ≤ 898128000) ∧
    (Finite (PG (subsetOf 6 [0, 1, 2, 3, 4]).length (jwRels5 neg)) ∧
      Nat.card (PG (subsetOf 6 [0, 1, 2, 3, 4]).length (jwRels5 neg)) ≤ 3265920) ∧
    (Finite (PG (subsetOf (subsetOf 6 [0, 1, 2, 3, 4]).length [0, 1, 2, 3]).length (jwRels4 neg)) ∧
      Nat.card (PG (subsetOf (subsetOf 6 [0, 1, 2, 3, 4]).length [0, 1, 2, 3]).length
        (jwRels4 neg)) ≤ 1152) ∧
    jwTabCheck neg = true := by
  refine fun neg => ?_
  have key : ∀ (h6 : CFSG.Certificates.KB.TableFact 6 ((jwRels neg).map encW)
        ((subsetOf 6 [0, 1, 2, 3, 4]).map fun x => [(x.val, true)]) 275)
      (h5 : CFSG.Certificates.KB.TableFact (subsetOf 6 [0, 1, 2, 3, 4]).length
        ((jwRels5 neg).map encW)
        ((subsetOf (subsetOf 6 [0, 1, 2, 3, 4]).length [0, 1, 2, 3]).map
          fun x => [(x.val, true)]) 2835)
      (h4 : CFSG.Certificates.KB.TableFact
        (subsetOf (subsetOf 6 [0, 1, 2, 3, 4]).length [0, 1, 2, 3]).length
        ((jwRels4 neg).map encW) [] 1152),
      (Finite (PG 6 (jwRels neg)) ∧ Nat.card (PG 6 (jwRels neg)) ≤ 898128000) ∧
      (Finite (PG (subsetOf 6 [0, 1, 2, 3, 4]).length (jwRels5 neg)) ∧
        Nat.card (PG (subsetOf 6 [0, 1, 2, 3, 4]).length (jwRels5 neg)) ≤ 3265920) ∧
      (Finite (PG (subsetOf (subsetOf 6 [0, 1, 2, 3, 4]).length [0, 1, 2, 3]).length
          (jwRels4 neg)) ∧
        Nat.card (PG (subsetOf (subsetOf 6 [0, 1, 2, 3, 4]).length [0, 1, 2, 3]).length
          (jwRels4 neg)) ≤ 1152) := by
    intro h6 h5 h4
    have c4 := TableFact.card (jwRels4 neg) (by decide) h4
    have c5 := card_le_of_index_restrict (jwRels5 neg) _
      (TableFact.genSub_index (jwRels5 neg) (by decide) _ h5) c4
    have c6 := card_le_of_index_restrict (jwRels neg) _
      (TableFact.genSub_index (jwRels neg) (by decide) _ h6) c5
    exact ⟨c6, c5, c4⟩
  have ht := CFSG.KC.TabWord.JW.jwTabCheck_eq_true neg
  cases neg
  · obtain ⟨c6, c5, c4⟩ := key CFSG.KBFact.F6104a0 CFSG.KBFact.F6104b0 CFSG.KBFact.F6104c0
    exact ⟨c6, c5, c4, ht⟩
  · obtain ⟨c6, c5, c4⟩ := key CFSG.KBFact.F6104a1 CFSG.KBFact.F6104b1 CFSG.KBFact.F6104c1
    exact ⟨c6, c5, c4, ht⟩

end Certificates
