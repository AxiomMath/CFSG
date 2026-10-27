module

public import CFSG.Monster.B.TwoA.Census.MonoCertInputs
public import Certificates.Kernel.MonsterB.Mono3016K
public import CFSG.Certificates.Kernel.SortTreeP
public import CFSG.Certificates.Kernel.MonsterB.PermISound
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SortTreeMul

public section

open CFSG.Monster.B.TwoA.Census CFSG.Monster.Code CFSG.KC.SortTree CFSG.KLie.CT CFSG.KC.Bfs
  CertificateChecks.Mono3016

namespace CertificateChecks.Batch3016

open CFSG.Monster.B.TwoA.Census CFSG.Monster.Code CFSG.KC.SortTree CFSG.KLie.CT CFSG.KC.Bfs
  CertificateChecks.Mono3016

set_option maxRecDepth 100000

theorem kPerm : (∀ j < 3, PermArr (seedA j) = true) ∧
    ∀ j < 3, ∀ a ∈ centGenArrs j, PermArr a = true := by decide +kernel

theorem kX : ∀ j < 3, ∀ k < 12,
    fget XJ (12 * j + k) 24 = Bmask k ^^^ permI (seedA j) (Bmask k) := by
  decide +kernel

theorem kP : ∀ j < 3, ∀ t < (centGenArrs j).length,
    fget PJ (5 * j + t) 120 = CFSG.KC.U6Orb.packL 5 ((centGenArrs j).getD t #[]).toList := by
  decide +kernel

theorem kNg : ngenJ 0 = 14 ∧ ngenJ 1 = 17 ∧ ngenJ 2 = 17 := by decide +kernel

theorem permR_succ (P n m : ℕ) :
    permR P n (m + 1) = if n.testBit m then permR P n m + 2 ^ fget P m 5 else permR P n m := by
  change nIf(bit n m, Nat.add (permR P n m) (pw2 (fget P m 5)), permR P n m) = _
  rw [CFSG.KC.U6Orb.bit_eq, CFSG.KC.U6Orb.pw2_eq]
  cases n.testBit m <;> rfl

theorem permR_eq {p : Array ℕ} (hp : PermArr p = true) (n : ℕ) :
    permR (CFSG.KC.U6Orb.packL 5 p.toList) n 24 = permI p n := by
  have key : ∀ m ≤ 24, permR (CFSG.KC.U6Orb.packL 5 p.toList) n m =
      (List.range m).foldl (fun acc j => if n.testBit j then acc + 2 ^ p[j]! else acc) 0 := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [permR_succ, ih (by omega), List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil, CFSG.KC.U6Orb.fget_packA (i := m) (lt32_of_perm hp)
          (by rw [PermArr_size hp]; omega)]
  exact key 24 le_rfl

theorem ble_false {a b : ℕ} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases e : Nat.ble a b
  · rfl
  · exact absurd (ble_iff.1 e) h

theorem blt_false {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · exact absurd (blt_iff.1 e) h

theorem canIK_eq (n : ℕ) : canIK n = canI n := by
  change nIf(Nat.ble n (n ^^^ 16777215), n, n ^^^ 16777215) = min n (n ^^^ OM)
  have hOM : OM = 16777215 := by decide
  rw [hOM, Nat.min_def]
  by_cases hle : n ≤ n ^^^ 16777215
  · rw [ble_iff.2 hle, ite_eq_left hle]
  · rw [ble_false hle, ite_eq_right hle]

theorem actJR_eq {j : ℕ} (hj : j < 3) {k : ℕ} (hk : k < ngenJ j) (n : ℕ) :
    actJ j k n = actJR j k n := by
  rw [actJ, actJR]
  by_cases h : k < 12
  · rw [ite_eq_left h]
    change _ = nIf(Nat.blt k 12, _, _)
    rw [blt_iff.2 h]
    change _ = canIK (Nat.xor n (fget XJ (12 * j + k) 24))
    rw [canIK_eq, kX j hj k h, Nat.xor_assoc]
    rfl
  · rw [ite_eq_right h]
    change _ = nIf(Nat.blt k 12, _, _)
    rw [blt_false h]
    change _ = canIK (permR (fget PJ (5 * j + (k - 12)) 120) n 24)
    have ht : k - 12 < (centGenArrs j).length := by rw [ngenJ] at hk; omega
    have hmem : (centGenArrs j).getD (k - 12) #[] ∈ centGenArrs j := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
      exact List.getElem_mem ht
    rw [canIK_eq, kP j hj _ ht, permR_eq (kPerm.2 j hj _ hmem)]

theorem reach_iff {j ng r x : ℕ} (hj : j < 3) (hng : ngenJ j = ng) :
    Reach (actJR j) ng r x ↔ Reach (actJ j) (ngenJ j) r x := by
  subst hng
  constructor
  · intro h
    induction h with
    | root => exact Reach.root
    | step k hk _ ih =>
      rw [← actJR_eq hj hk]
      exact Reach.step k hk ih
  · intro h
    induction h with
    | root => exact Reach.root
    | step k hk _ ih =>
      rw [actJR_eq hj hk]
      exact Reach.step k hk ih

theorem valid_of {j o n : ℕ} (h : validRec j o n = true) {t : ℕ} (ht : t < n) :
    validB j (valF 24 (recI o t)) = true := by
  rw [validRec, List.all_eq_true] at h
  have := h t (List.mem_range.2 ht)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  obtain ⟨⟨⟨hv, hw⟩, hc⟩, he⟩ := this
  rw [validB, Bool.and_eq_true]
  refine ⟨?_, he⟩
  rw [List.contains_iff_mem, validList, List.mem_filter]
  exact ⟨List.mem_map.2 ⟨_, List.mem_range.2 hw, hc⟩, by simpa using hv⟩

theorem orb {j ng d o n C : ℕ} (hj : j < 3) (hng : ngenJ j = ng) (hn : 0 < n) (hf : n ≤ 3000)
    (hT : treeOK (actJR j) ng (fun _ => true) d (recI o) n 24 5 11 64 C = true)
    (hE : closeOK (actJR j) ng (recI o) (edgeI o) n 24 64 C = true)
    (hV : validRec j o n = true) :
    natCertOK (actJ j) (ngenJ j) (validB j) d (natBfs (actJ j) (ngenJ j) d 3000) = true ∧
      (natBfs (actJ j) (ngenJ j) d 3000).pts.size = n ∧
      (∀ x, x ∈ (natBfs (actJ j) (ngenJ j) d 3000).pts ↔ ∃ t < n, valF 24 (recI o t) = x) ∧
      (natBfs (actJ j) (ngenJ j) d 3000).pts.toList.Nodup := by
  obtain ⟨S, hS, hcard, -, -, hmem⟩ := orbit_sound hn hT hE
  have hv : ∀ x ∈ S, validB j x = true := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (hmem x).1 hx
    exact valid_of hV ht
  obtain ⟨h1, h2, h3, h4⟩ := natBfs_spec (act := actJ j) (fuel := 3000) S
    (fun x => (reach_iff hj hng).symm.trans (hS x)) hv (by rw [hcard]; exact hf)
  exact ⟨h1, h3.trans hcard, fun x => (h2 x).trans (hmem x), h4⟩

@[expose] def sizes : List ℕ := [1, 759, 1288, 16, 112, 32, 32]

@[expose] def offs : List ℕ := [0, 1, 760, 2048, 2064, 2176, 2208]

theorem facts (i : ℕ) (hi : i < 7) :
    natCertOK (actJ (monoSeed.getD i 0)) (ngenJ (monoSeed.getD i 0)) (validB (monoSeed.getD i 0))
      (monoSign.getD i 0) (monoCert i) = true ∧
    (monoCert i).pts.size = sizes.getD i 0 ∧
    (∀ x, x ∈ (monoCert i).pts ↔ ∃ t < sizes.getD i 0, valF 24 (recI (offs.getD i 0) t) = x) ∧
    (monoCert i).pts.toList.Nodup := by
  interval_cases i
  · exact orb (j := 0) (by norm_num) kNg.1 (by decide) (by decide) t0 e0 v0
  · exact orb (j := 0) (by norm_num) kNg.1 (by decide) (by decide) t1 e1 v1
  · exact orb (j := 0) (by norm_num) kNg.1 (by decide) (by decide) t2 e2 v2
  · exact orb (j := 1) (by norm_num) kNg.2.1 (by decide) (by decide) t3 e3 v3
  · exact orb (j := 1) (by norm_num) kNg.2.1 (by decide) (by decide) t4 e4 v4
  · exact orb (j := 2) (by norm_num) kNg.2.2 (by decide) (by decide) t5 e5 v5
  · exact orb (j := 2) (by norm_num) kNg.2.2 (by decide) (by decide) t6 e6 v6

theorem kLen : ∀ j < 3, (eligList j).length = [2048, 128, 64].getD j 0 := by decide +kernel

theorem combI_inj {a b : ℕ} (ha : a < 4096) (hb : b < 4096) (h : combI a = combI b) : a = b := by
  have h' := kDec
  rw [List.all_eq_true] at h'
  have e1 := h' a (List.mem_range.2 ha)
  have e2 := h' b (List.mem_range.2 hb)
  rw [beq_iff_eq] at e1 e2
  rw [← e1, ← e2, h]

theorem validList_nodup : validList.Nodup :=
  ((List.nodup_range).map_on fun _ ha _ hb e =>
    combI_inj (List.mem_range.1 ha) (List.mem_range.1 hb) e).filter _

theorem mem_elig {j t : ℕ} {o n : ℕ} (hV : validRec j o n = true) (ht : t < n) :
    valF 24 (recI o t) ∈ eligList j := by
  have h := valid_of hV ht
  rw [validB, Bool.and_eq_true, List.contains_iff_mem] at h
  exact List.mem_filter.2 h

theorem disj_sound {o n o' n' : ℕ} (h : disjI o n o' n' = true) {a b : ℕ} (ha : a < n)
    (hb : b < n') : valF 24 (recI o a) ≠ valF 24 (recI o' b) := by
  have h1 := (CFSG.KC.SortTree.allN_iff _ _).1 h a ha
  have h2 := (CFSG.KC.SortTree.allN_iff _ _).1 h1 b hb
  intro e
  rw [e] at h2
  simp [notB, Nat.beq_refl] at h2

theorem disjoint_pts {i i' o n o' n' : ℕ} (hi : i < 7) (hi' : i' < 7) (ho : offs.getD i 0 = o)
    (hn : sizes.getD i 0 = n) (ho' : offs.getD i' 0 = o') (hn' : sizes.getD i' 0 = n')
    (h : disjI o n o' n' = true) :
    ∀ x ∈ (monoCert i).pts.toList, ∀ y ∈ (monoCert i').pts.toList, x ≠ y := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := ((facts i hi).2.2.1 x).1 (Array.mem_toList_iff.1 hx)
  obtain ⟨b, hb, e⟩ := ((facts i' hi').2.2.1 _).1 (Array.mem_toList_iff.1 hy)
  subst ho hn ho' hn'
  exact disj_sound h ha hb (hxy.trans e.symm)

theorem sub_elig {i j o n : ℕ} (hi : i < 7) (ho : offs.getD i 0 = o) (hn : sizes.getD i 0 = n)
    (hV : validRec j o n = true) :
    ∀ x ∈ (monoCert i).pts.toList, x ∈ eligList j := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := ((facts i hi).2.2.1 x).1 (Array.mem_toList_iff.1 hx)
  subst ho hn
  exact mem_elig hV ht

theorem len_pts {i : ℕ} (hi : i < 7) : (monoCert i).pts.toList.length = sizes.getD i 0 := by
  rw [Array.length_toList]
  exact (facts i hi).2.1

theorem perm_of {L : List ℕ} {j : ℕ} (hnd : L.Nodup) (hsub : ∀ x ∈ L, x ∈ eligList j)
    (hlen : (eligList j).length ≤ L.length) :
    (L.mergeSort fun a b => decide (a ≤ b)) = (eligList j).mergeSort fun a b => decide (a ≤ b) := by
  have hp := (List.subperm_of_subset hnd hsub).perm_of_length_le hlen
  have hs : ∀ l : List ℕ, (l.mergeSort fun a b => decide (a ≤ b)).Pairwise (· ≤ ·) := fun l =>
    (List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l).imp
      fun h => by simpa using h
  exact List.Perm.eq_of_pairwise' (hs _) (hs _)
    ((List.mergeSort_perm _ _).trans (hp.trans (List.mergeSort_perm _ _).symm))

theorem partition : ∀ j < 3,
    (((List.range 7).filter (fun i => monoSeed.getD i 0 == j)).flatMap
      (fun i => (monoCert i).pts.toList)).mergeSort (fun a b => decide (a ≤ b)) =
      (eligList j).mergeSort (fun a b => decide (a ≤ b)) := by
  intro j hj
  have hl := kLen j hj
  interval_cases j
  · have hf : (List.range 7).filter (fun i => monoSeed.getD i 0 == 0) = [0, 1, 2] := by decide
    rw [hf]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine perm_of ?_ ?_ ?_
    · rw [List.nodup_append, List.nodup_append]
      refine ⟨(facts 0 (by norm_num)).2.2.2, ⟨(facts 1 (by norm_num)).2.2.2,
        (facts 2 (by norm_num)).2.2.2, disjoint_pts (i := 1) (i' := 2) (o := 1) (n := 759)
          (o' := 760) (n' := 1288) (by norm_num) (by norm_num) rfl rfl rfl rfl d12⟩, ?_⟩
      intro x hx y hy
      rcases List.mem_append.1 hy with h | h
      · exact disjoint_pts (i := 0) (i' := 1) (o := 0) (n := 1) (o' := 1) (n' := 759)
          (by norm_num) (by norm_num) rfl rfl rfl rfl d01 x hx y h
      · exact disjoint_pts (i := 0) (i' := 2) (o := 0) (n := 1) (o' := 760) (n' := 1288)
          (by norm_num) (by norm_num) rfl rfl rfl rfl d02 x hx y h
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact sub_elig (i := 0) (o := 0) (n := 1) (by norm_num) rfl rfl v0 x h
      · rcases List.mem_append.1 h with h | h
        · exact sub_elig (i := 1) (o := 1) (n := 759) (by norm_num) rfl rfl v1 x h
        · exact sub_elig (i := 2) (o := 760) (n := 1288) (by norm_num) rfl rfl v2 x h
    · rw [hl, List.length_append, List.length_append, len_pts (i := 0) (by norm_num),
        len_pts (i := 1) (by norm_num), len_pts (i := 2) (by norm_num)]
      decide
  · have hf : (List.range 7).filter (fun i => monoSeed.getD i 0 == 1) = [3, 4] := by decide
    rw [hf]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine perm_of ?_ ?_ ?_
    · rw [List.nodup_append]
      exact ⟨(facts 3 (by norm_num)).2.2.2, (facts 4 (by norm_num)).2.2.2,
        disjoint_pts (i := 3) (i' := 4) (o := 2048) (n := 16) (o' := 2064) (n' := 112)
          (by norm_num) (by norm_num) rfl rfl rfl rfl d34⟩
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact sub_elig (i := 3) (o := 2048) (n := 16) (by norm_num) rfl rfl v3 x h
      · exact sub_elig (i := 4) (o := 2064) (n := 112) (by norm_num) rfl rfl v4 x h
    · rw [hl, List.length_append, len_pts (i := 3) (by norm_num), len_pts (i := 4) (by norm_num)]
      decide
  · have hf : (List.range 7).filter (fun i => monoSeed.getD i 0 == 2) = [5, 6] := by decide
    rw [hf]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine perm_of ?_ ?_ ?_
    · rw [List.nodup_append]
      exact ⟨(facts 5 (by norm_num)).2.2.2, (facts 6 (by norm_num)).2.2.2,
        disjoint_pts (i := 5) (i' := 6) (o := 2176) (n := 32) (o' := 2208) (n' := 32)
          (by norm_num) (by norm_num) rfl rfl rfl rfl d56⟩
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact sub_elig (i := 5) (o := 2176) (n := 32) (by norm_num) rfl rfl v5 x h
      · exact sub_elig (i := 6) (o := 2208) (n := 32) (by norm_num) rfl rfl v6 x h
    · rw [hl, List.length_append, len_pts (i := 5) (by norm_num), len_pts (i := 6) (by norm_num)]
      decide

end CertificateChecks.Batch3016

namespace Certificates

open CertificateChecks.Batch3016 in
open CFSG.Monster.B.TwoA.Census CFSG.Monster.Code in
theorem certificate3016 : (∀ i < 7, natCertOK (actJ (monoSeed.getD i 0)) (ngenJ (monoSeed.getD i 0))
       (validB (monoSeed.getD i 0)) (monoSign.getD i 0) (monoCert i) = true)
    ∧ (∀ i < 7, (monoCert i).pts.size = [1, 759, 1288, 16, 112, 32, 32].getD i 0)
    ∧ (∀ j < 3, (eligList j).length = [2048, 128, 64].getD j 0)
    ∧ (∀ j < 3,
       (((List.range 7).filter (fun i => monoSeed.getD i 0 == j)).flatMap
         (fun i => (monoCert i).pts.toList)).mergeSort (fun a b => decide (a ≤ b)) =
       (eligList j).mergeSort (fun a b => decide (a ≤ b)))
    ∧ (∀ j < 3, ∀ n ∈ validList,
       bvec 24 (permI (seedA j) n) = bvec 24 n ∘ arrFun (ainv (seedA j)))
    ∧ (∀ j < 3, ∀ k < 12,
       bvec 24 (permI (seedA j) (Bmask k)) = bvec 24 (Bmask k) ∘ arrFun (ainv (seedA j)))
    ∧ (∀ j < 3, ∀ a ∈ centGenArrs j, ∀ n ∈ validList,
       bvec 24 (permI a n) = bvec 24 n ∘ arrFun (ainv a))
    ∧ (∀ j < 3, ∀ n ∈ validList, permI (seedA j) n < 2 ^ 24) :=
  ⟨fun i hi => (facts i hi).1, fun i hi => (facts i hi).2.1, kLen, partition,
    fun j hj n _ => bvec_permI (kPerm.1 j hj) n, fun j hj _ _ => bvec_permI (kPerm.1 j hj) _,
    fun j hj a ha n _ => bvec_permI (kPerm.2 j hj a ha) n,
    fun j hj n _ => permI_lt (kPerm.1 j hj) n⟩

end Certificates
