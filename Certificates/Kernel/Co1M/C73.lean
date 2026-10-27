
module

public import Certificates.Kernel.Co1M.W73
public import Certificates.Kernel.Co1M.K73F0
public import Certificates.Kernel.Co1M.K73F1
public import Certificates.Kernel.Co1M.C10071
public import CFSG.Certificates.Kernel.Co1M.FixSlice73Sound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.Odd73 CFSG.KC.Co1Fix CFSG.KC.Co1M
  CFSG.KD.Co1M CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative CFSG.KC.VecK
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Odd

theorem c73_rr : rr = fun i => (cmRP71.map (unpackR 24)).toArray[i]?.getD (idRows 24) := by
  funext i
  rw [rr, c71_regs]

theorem c73_inPts (w : Nat) :
    inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w =
      orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 w :=
  cm_orb_inPts w

theorem c73_validRows (M : Nat) : validRows (unpackR 24 M) = true := by
  simp only [validRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [unpackR], fun i hi => ?_⟩
  simp only [unpackR, Array.getElem_ofFn]
  exact (Nat.mod_lt _ (by norm_num)).trans_eq (by norm_num)

theorem c73_valid : validOK = true := by
  have h94 : ((List.range 94).all fun i => validRows (rr i)) = true := by
    rw [List.all_eq_true]
    intro i hi
    rw [c71_rr (by rw [c71_len]; exact List.mem_range.1 hi)]
    exact c73_validRows _
  have hid : validRows (idRows 24) = true := by
    rw [← CFSG.KC.VecK.unpackR_idF]
    exact c73_validRows _
  unfold validOK isT4 type4N
  rw [h94, hid, c73_inPts, c73_rr]
  quickRfl

theorem c73_fix : fixOK = true := by
  unfold fixOK Mt
  rw [c73_rr]
  quickRfl

theorem c73_partner : partnerOK = true := by
  unfold partnerOK
  rw [c73_rr]
  quickRfl

theorem c73_conj : conjOK = true := by
  unfold conjOK
  rw [c73_rr]
  quickRfl

theorem c73_QT : transposeRows 24 qRows = unpackR 24 QT73 := eq_of_beq (by quickRfl)

theorem c73_beq (a b : Nat) : (a == b) = Nat.beq a b := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Nat.beq_eq]

theorem c73_isFixed (T x : Nat) : isFixedN (unpackR 24 T) x = Nat.beq (vmF 24 T x) x := by
  rw [isFixedN, CFSG.KC.F2W.vecMulN_unpackR, c73_beq]

theorem c73_t4 (x : Nat) : type4N (transposeRows 24 qRows) (orbitOf 2 98280).pts
    (posTable 24 (orbitOf 2 98280).pts) 98280 x = t4K73 x := by
  have hd : ∀ a b, dotN a b = dotK 24 a b := fun a b => (dotK_dotN a b).symm
  unfold type4N t4K73 q0N
  rw [c73_inPts, c73_QT, CFSG.KC.F2W.vecMulN_unpackR, hd]
  cases h1 : Nat.beq x 0 <;> cases dotK 24 x (vmF 24 QT73 x) <;>
    cases orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 x <;>
    simp_all [andB, notB, bne, c73_beq]

theorem c73_Mt {i : Nat} (hi : i < 94) : Mt i = unpackR 24 (trK 24 (getL 0 cmRP71 i)) := by
  rw [Mt, c71_rr (by rw [c71_len]; exact hi), CFSG.KC.F2W.transposeRows_unpackR]

theorem c73_spanK_len : ∀ (F : List Nat) (acc : Nat), (spanK F acc).length = 2 ^ F.length
  | [], _ => rfl
  | f :: F, acc => by
    rw [spanK, List.length_append, c73_spanK_len F, c73_spanK_len F, List.length_cons, pow_succ]
    ring

theorem c73_fixK : fixK 24 (trK 24 (getL 0 cmRP71 27)) 0 FR3 YR3 16 65536 0 = true := w71_fix

theorem c73_slice {j : Nat} (hj : j < 64) :
    cnt7K t4K73 (trK 24 (getL 0 R73 70)) (trK 24 (getL 0 R73 73)) (trK 24 (getL 0 R73 76))
      (List.drop 6 FR3) (offK FR3 6 j) = pack7 (List.getD FC73 j List.nil) := by
  apply Nat.eq_of_beq_eq_true
  by_cases h : j < 32
  · exact FX73x0.all j (w73_lt (b := 32) h rfl)
  · have := FX73x1.all (j - 32) (w73_lt (b := 32) (by omega) rfl)
    unfold fx73G at this
    have e : Nat.add 32 (j - 32) = j := by
      change 32 + (j - 32) = j
      omega
    rwa [e] at this

theorem c73_FCbnd : ∀ j < 64, (FC73.getD j []).length = 7 ∧
    ∀ k < 7, (FC73.getD j []).getD k 0 < 4096 := by decide

theorem c73_counts {j : Nat} (hj : j < 64) {k : Nat} (hk : k < 7) :
    ((spanK (List.drop 6 FR3) (offK FR3 6 j)).filter (test7 t4K73 (trK 24 (getL 0 R73 70))
      (trK 24 (getL 0 R73 73)) (trK 24 (getL 0 R73 76)) k)).length = (FC73.getD j []).getD k 0 := by
  have hl : (List.drop 6 FR3).length = 10 := rfl
  refine cnt7_fields (c := fun k => ((spanK (List.drop 6 FR3) (offK FR3 6 j)).filter
    (test7 t4K73 (trK 24 (getL 0 R73 70)) (trK 24 (getL 0 R73 73)) (trK 24 (getL 0 R73 76))
      k)).length) (c73_FCbnd j hj).1 (fun k _ => ?_) (c73_FCbnd j hj).2 ?_ k hk
  · have := List.length_filter_le (test7 t4K73 (trK 24 (getL 0 R73 70)) (trK 24 (getL 0 R73 73))
      (trK 24 (getL 0 R73 76)) k) (spanK (List.drop 6 FR3) (offK FR3 6 j))
    rw [c73_spanK_len, hl] at this
    omega
  · rw [← cnt7K_eq]
    exact c73_slice hj

theorem c73_sum {k : Nat} (hk : k < 7) :
    ∑ j ∈ Finset.range 64, ((spanK (List.drop 6 FR3) (offK FR3 6 j)).filter
      (test7 t4K73 (trK 24 (getL 0 R73 70)) (trK 24 (getL 0 R73 73)) (trK 24 (getL 0 R73 76))
        k)).length = ∑ j ∈ Finset.range 64, (FC73.getD j []).getD k 0 :=
  Finset.sum_congr rfl fun _ hj => c73_counts (Finset.mem_range.1 hj) hk

theorem c73_totals : (List.range 7).map (fun k => ∑ j ∈ Finset.range 64, (FC73.getD j []).getD k 0) =
    [32535, 1024, 405, 256, 135, 256, 75] := by decide

theorem c73_total {k : Nat} (hk : k < 7) :
    ∑ j ∈ Finset.range 64, (FC73.getD j []).getD k 0 =
      [32535, 1024, 405, 256, 135, 256, 75].getD k 0 := by
  have h : ((List.range 7).map (fun k => ∑ j ∈ Finset.range 64, (FC73.getD j []).getD k 0)).getD
      k 0 = [32535, 1024, 405, 256, 135, 256, 75].getD k 0 := by rw [c73_totals]
  rw [← h, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]

theorem c73_count {k : Nat} (hk : k < 7) :
    countBelow (fun x => Nat.beq (vmF 24 (trK 24 (getL 0 cmRP71 27)) x) x &&
      test7 t4K73 (trK 24 (getL 0 R73 70)) (trK 24 (getL 0 R73 73)) (trK 24 (getL 0 R73 76)) k x)
      16777216 0 = [32535, 1024, 405, 256, 135, 256, 75].getD k 0 := by
  rw [slices_count c73_fixK, c73_sum hk, c73_total hk]

theorem c73_fix2 : fixOK₂ = true := by
  have h1 : fixCount [Mt 27] = 65536 := by
    unfold fixCount
    rw [c73_Mt (by norm_num)]
    have e : (fun x => [unpackR 24 (trK 24 (getL 0 cmRP71 27))].all fun Mt => isFixedN Mt x) =
        fun x => Nat.beq (vmF 24 (trK 24 (getL 0 cmRP71 27)) x) x && (fun _ => true) x := by
      funext x
      simp only [List.all_cons, List.all_nil, Bool.and_true, c73_isFixed]
    rw [e, slices_count c73_fixK]
    simp only [List.filter_true, c73_spanK_len]
    rfl
  have h2 : fixCount4 [Mt 27] (transposeRows 24 qRows) (orbitOf 2 98280).pts
      (posTable 24 (orbitOf 2 98280).pts) 98280 = 32535 := by
    unfold fixCount4
    rw [c73_Mt (by norm_num)]
    have e : (fun x => ([unpackR 24 (trK 24 (getL 0 cmRP71 27))].all fun Mt => isFixedN Mt x) &&
        type4N (transposeRows 24 qRows) (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts)
          98280 x) = fun x => Nat.beq (vmF 24 (trK 24 (getL 0 cmRP71 27)) x) x &&
        test7 t4K73 (trK 24 (getL 0 R73 70)) (trK 24 (getL 0 R73 73)) (trK 24 (getL 0 R73 76))
          0 x := by
      funext x
      simp only [List.all_cons, List.all_nil, Bool.and_true, c73_isFixed, c73_t4, test7]
    rw [e, c73_count (by norm_num)]
    rfl
  unfold fixOK₂
  rw [h1, h2]
  rfl

theorem c73_pair {k s : Nat} (hk : k < 3) (hs : sIdx[k]! = s) (hT : getL 0 R73 (getL 0 J73 k) =
    getL 0 cmRP71 s) :
    fixCount [Mt 27, Mt (sIdx[k]!)] = [32535, 1024, 405, 256, 135, 256, 75].getD (1 + 2 * k) 0 ∧
    fixCount4 [Mt 27, Mt (sIdx[k]!)] (transposeRows 24 qRows) (orbitOf 2 98280).pts
      (posTable 24 (orbitOf 2 98280).pts) 98280 =
        [32535, 1024, 405, 256, 135, 256, 75].getD (2 + 2 * k) 0 := by
  have hs94 : s < 94 := by
    interval_cases k <;> (rw [← hs]; decide)
  have hTs : ∀ x, isFixedN (Mt (sIdx[k]!)) x = Nat.beq (vmF 24 (trK 24 (getL 0 cmRP71 s)) x) x := by
    intro x
    rw [hs, c73_Mt hs94, c73_isFixed]
  have hT1 : ∀ x, test7 t4K73 (trK 24 (getL 0 R73 70)) (trK 24 (getL 0 R73 73))
      (trK 24 (getL 0 R73 76)) (1 + 2 * k) x = Nat.beq (vmF 24 (trK 24 (getL 0 cmRP71 s)) x) x := by
    intro x
    rw [← hT]
    interval_cases k <;> rfl
  have hT2 : ∀ x, test7 t4K73 (trK 24 (getL 0 R73 70)) (trK 24 (getL 0 R73 73))
      (trK 24 (getL 0 R73 76)) (2 + 2 * k) x =
        (Nat.beq (vmF 24 (trK 24 (getL 0 cmRP71 s)) x) x && t4K73 x) := by
    intro x
    rw [← hT]
    interval_cases k <;> rfl
  constructor
  · unfold fixCount
    rw [← c73_count (k := 1 + 2 * k) (by omega)]
    congr 1
    funext x
    simp only [List.all_cons, List.all_nil, Bool.and_true, hTs, hT1]
    rw [c73_Mt (by norm_num), c73_isFixed]
  · unfold fixCount4
    rw [← c73_count (k := 2 + 2 * k) (by omega)]
    congr 1
    funext x
    simp only [List.all_cons, List.all_nil, Bool.and_true, hTs, hT2, c73_t4]
    rw [c73_Mt (by norm_num), c73_isFixed, Bool.and_assoc]

theorem c73_pair0 : pairFixOK 0 1024 405 = true := by
  obtain ⟨h1, h2⟩ := c73_pair (k := 0) (s := 70) (by norm_num) rfl (by rw [w73_R]; rfl)
  unfold pairFixOK
  rw [h1, h2]
  rfl

theorem c73_pair1 : pairFixOK 1 256 135 = true := by
  obtain ⟨h1, h2⟩ := c73_pair (k := 1) (s := 73) (by norm_num) rfl (by rw [w73_R]; rfl)
  unfold pairFixOK
  rw [h1, h2]
  rfl

theorem c73_pair2 : pairFixOK 2 256 75 = true := by
  obtain ⟨h1, h2⟩ := c73_pair (k := 2) (s := 76) (by norm_num) rfl (by rw [w73_R]; rfl)
  unfold pairFixOK
  rw [h1, h2]
  rfl

theorem c73_gram1 : gramOK (transposeRows 24 f0Rows) (Wk 1) = true := by
  have e : Wk 1 = W1L := c71_W1
  rw [e]
  quickRfl

theorem c73_gram2 : gramOK (transposeRows 24 f0Rows) (Wk 2) = true := by
  have e : Wk 2 = W2L := c71_W2
  rw [e]
  quickRfl

end CertificateChecks.KernelCo1M

end
