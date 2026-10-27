module

public import CFSG.Sporadic.J4.QT2LocZCentNative
public import CFSG.Sporadic.J4.QT2LocX0MainBase
public import CFSG.Sporadic.J4.QTRankProof

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

theorem zcGenWords_letters : ∀ w ∈ zcGenWords, ∀ l ∈ w, l ∈ letters := by decide

theorem zcGenTabs_getD {k : ℕ} (hk : k < 3) :
    zcGenTabs.getD k [] = wordT (zcGenWords.getD k []) := by
  interval_cases k <;> rfl

theorem zcGenWords_mem {k : ℕ} (hk : k < 3) : zcGenWords.getD k [] ∈ zcGenWords := by
  interval_cases k <;> simp [zcGenWords]

theorem zcGen_acts
    (hM : MatFacts) {k : ℕ} (hk : k < 3) :
    Acts (el5 (zcGenWords.getD k [])) (zcGenTabs.getD k []) := by
  have hl := zcGenWords_letters _ (zcGenWords_mem hk)
  rw [zcGenTabs_getD hk, el5, wordProd_gen5_xJ _ hl]
  exact Acts_wordProd hM _ hl

theorem el5_append (w w' : List ℤ) : el5 (w ++ w') = el5 w * el5 w' := by
  unfold el5
  exact wordProd_append _ _ _

theorem wf_getD_append {A B : Array (Array V2)} (hA : A.size = 3) (hAw : A.all wfRows = true)
    {k : ℕ} (hk : k < 3) : wfRows ((A ++ B)[k]?.getD idRows) = true := by
  have hk' : k < A.size := by omega
  rw [Array.getElem?_append_left hk', Array.getElem?_eq_getElem hk', Option.getD_some]
  exact (Array.all_eq_true_iff_forall_mem.1 hAw) _ (Array.getElem_mem hk')

end CFSG.Sporadic.J4.QT2
