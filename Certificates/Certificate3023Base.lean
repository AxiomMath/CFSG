
module

public import CFSG.Monster.B.TwoA.Census.CosetEnumCheckInputs
import Certificates.Kernel.MonsterB.Coset3023Checks
import Certificates.Kernel.MonsterB.Coset3023Class
import CFSG.Monster.B.TwoA.Census.CosetEnumCheckBase
import all CFSG.Monster.B.TwoA.Census.CosetEnumCheckInputs
import Certificates.Kernel.MonsterB.Coset3023Count

namespace CertificateChecks.Batch3023

open CFSG.KC.KDense CFSG.KLie.CT CFSG.Monster.B CFSG.KC.SortTree CFSG.KC.Bfs
  CFSG.Monster.B.TwoA.Census CertificateChecks.Coset3023

theorem tab_spec {c : ℕ} {TT : ℕ → ℕ} {e : ℕ} {pe' : Bool} {BT : ℕ} (he : cosetA c = e)
    (hpe : Model.pN e = pe') (hP : ∀ i < 24, pe (PP c) i = (cosetArr c)[i]!)
    (hBT : betaTabT (PP c) = BT) (ha : tabA TT e pe' (PP c) BT = true)
    (hd : tabD TT e pe' (PP c) BT = true) : TabSpec TT (tT c) (tD c) := by
  refine ⟨fun A hA => ?_, fun D hD => ?_⟩
  · rw [tT_get c hA, alphaN, he, ← alphaW_eq th_ok hP, hpe, hBT]
    exact of_decide_eq_true ((allN_iff' _ _).1 ha A hA)
  · rw [tD_get c hD, alphaN, he, ← alphaW_eq th_ok hP, hpe, hBT]
    exact of_decide_eq_true ((allN_iff' _ _).1 hd D hD)

theorem spec_1 : TabSpec T1 (tT 1) (tD 1) :=
  tab_spec e_ok.1 pe_ok.1 pp_1 bt_1 ta_1 td_1

theorem spec_2 : TabSpec T2 (tT 2) (tD 2) :=
  tab_spec e_ok.2.1 pe_ok.2.1 pp_2 bt_2 ta_2 td_2

theorem spec_6 : TabSpec T6 (tT 6) (tD 6) :=
  tab_spec e_ok.2.2 pe_ok.2.2 pp_6 bt_6 ta_6 td_6

theorem blocks_all {TT : ℕ → ℕ} {w : Model.Pauli} {J : ℕ → ℕ}
    (h0 : blocksOK TT w J 0 2048 = true) (h1 : blocksOK TT w J 2048 2048 = true) :
    ∀ a < 4096, blockOK TT w J a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 2048 with h | h
  · have := (allN_iff' _ _).1 h0 a h
    change blockOK TT w J (0 + a) = true at this
    rwa [Nat.zero_add] at this
  · have := (allN_iff' _ _).1 h1 (a - 2048) (by omega)
    change blockOK TT w J (2048 + (a - 2048)) = true at this
    rwa [show 2048 + (a - 2048) = a by omega] at this

theorem count_1 : Rep4371.Native.CosetEnum.countSq (tT 1) (tD 1) (wP 1) = 69632 := by
  rw [countSq_eq_keys spec_1, w_ok.1,
    keys_sum_eq (v := fun k => [20480, 0, 16384, 0, 16384, 0, 16384, 0].getD k 0) sort_1
      (blocks_all blk_1_0 blk_1_1) fun k hk => by
        interval_cases k
        exacts [part_1_0, part_1_1, part_1_2, part_1_3, part_1_4, part_1_5, part_1_6, part_1_7]]
  simp [Finset.sum_range_succ]

theorem count_2 : Rep4371.Native.CosetEnum.countSq (tT 2) (tD 2) (wP 2) = 8192 := by
  rw [countSq_eq_keys spec_2, w_ok.2.1,
    keys_sum_eq (v := fun k => [4096, 4096, 0, 0, 0, 0, 0, 0].getD k 0) sort_2
      (blocks_all blk_2_0 blk_2_1) fun k hk => by
        interval_cases k
        exacts [part_2_0, part_2_1, part_2_2, part_2_3, part_2_4, part_2_5, part_2_6, part_2_7]]
  simp [Finset.sum_range_succ]

theorem count_6 : Rep4371.Native.CosetEnum.countSq (tT 6) (tD 6) (wP 6) = 0 := by
  rw [countSq_eq_keys spec_6, w_ok.2.2,
    keys_sum_eq (v := fun _ => 0) sort_6 (blocks_all blk_6_0 blk_6_1) fun k hk => by
        interval_cases k
        exacts [part_6_0, part_6_1, part_6_2, part_6_3, part_6_4, part_6_5, part_6_6, part_6_7]]
  simp

theorem tree1_all : ∀ k < 137, tree1 k = true := by
  have h : ∀ q < 8, trees1 (18 * q) (if q = 7 then 11 else 18) = true := by
    intro q hq
    interval_cases q
    exacts [tr_0, tr_1, tr_2, tr_3, tr_4, tr_5, tr_6, tr_7]
  intro k hk
  have := (allN_iff' _ _).1 (h (k / 18) (by omega)) (k % 18) (by split <;> omega)
  change tree1 (18 * (k / 18) + k % 18) = true at this
  rwa [Nat.div_add_mod] at this

theorem class_spec {k : ℕ} (hk : k < 137) :
    ∃ S, ClassSpec (Rep4371.Native.CosetEnum.act imgs1L) (classEnc k) (classSize k) (rec1 k) S := by
  have ht := tree1_all k hk
  unfold tree1 at ht
  rw [andB_iff, Nat.beq_eq] at ht
  obtain ⟨h0, hT⟩ := ht
  have hs := classSize_eq k hk
  by_cases h04 : k = 0 ∨ k = 4
  · rw [if_pos h04] at hs
    rw [hs] at hT ⊢
    rcases h04 with rfl | rfl
    · exact class_small hT h0 edges_0 (by norm_num)
    · exact class_small hT h0 edges_1 (by norm_num)
  · rw [if_neg h04] at hs
    rw [hs] at hT ⊢
    exact class_big hT h0 span_1 (by norm_num)

theorem classCheck_ok : classCheck = true := by
  unfold classCheck
  dsimp only
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  obtain ⟨S, hS⟩ := class_spec hk
  have hle : classSize k ≤ 9000 := by rw [classSize_eq k hk]; split <;> norm_num
  obtain ⟨c1, c2, c3, -⟩ := natBfs_class hS hle
  unfold classCert
  rw [imgs_1]
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨⟨c1, c2⟩, c3⟩, ?_⟩
  rw [sqTest_eq_sqW spec_1, w_ok.1]
  exact (allN_iff' _ _).1 sq_1 k hk

theorem class17Check_ok : class17Check = true := by
  obtain ⟨S, hS⟩ := class_spec (k := 17) (by norm_num)
  have hle : classSize 17 ≤ 9000 := by rw [classSize_eq 17 (by norm_num)]; norm_num
  obtain ⟨-, -, -, c4⟩ := natBfs_class hS hle
  have hs : classSize 17 = 512 := by rw [classSize_eq 17 (by norm_num)]; norm_num
  have hm := c4 10 (by rw [hs]; norm_num)
  rw [Nat.eq_of_beq_eq_true mem_17] at hm
  unfold class17Check
  unfold classCert
  rw [imgs_1]
  obtain ⟨j, hj, e⟩ := Array.mem_iff_getElem.1 hm
  rw [List.any_eq_true]
  exact ⟨j, List.mem_range.2 hj, by rw [getElem!_pos _ j hj, e]; rfl⟩

theorem class2Check_ok : class2Check = true := by
  have ht := tree_2
  unfold Coset3023.tree2 at ht
  rw [andB_iff, Nat.beq_eq] at ht
  obtain ⟨h0, hT⟩ := ht
  obtain ⟨S, hS⟩ := class_big hT h0 span_2 (by norm_num)
  obtain ⟨c1, c2, -, -⟩ := natBfs_class hS (by norm_num)
  unfold class2Check
  unfold classCert
  rw [imgs_2]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨c1, c2⟩, ?_⟩
  rw [sqTest_eq_sqW spec_2, w_ok.2.1]
  exact sq_2

end CertificateChecks.Batch3023

@[expose] public section

namespace Certificates

open CertificateChecks

end Certificates
