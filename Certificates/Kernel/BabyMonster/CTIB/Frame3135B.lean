module

public import CFSG.Monster.B.GSide.HInnerFusionI3CertInputs
public import Certificates.Kernel.BabyMonster.CTIB.InnerTab
public import Certificates.Kernel.BabyMonster.CTIB.Cls3135Data
public import Certificates.Kernel.BabyMonster.CTIB.Orb3135Data
public import Certificates.Kernel.BabyMonster.CTIB.Outer3122
public import Certificates.Kernel.BabyMonster.CTIB.CosetQBind
public import Certificates.Kernel.BabyMonster.CTIB.QK
public import CFSG.Certificates.Kernel.BabyMonster.OrbTreeWSound
import Certificates.Certificate3110
import Certificates.Kernel.BabyMonster.CTIB.CosetQCount
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Tree
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos0
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos1
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos2
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos3
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos4
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos5
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos6
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos7
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos8
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos9
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos10
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos11
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos12
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos13
import Certificates.Kernel.BabyMonster.CTIB.Orb3135.Clos14
import Certificates.Kernel.BabyMonster.CTIB.Cls3135.Tree
import Certificates.Kernel.BabyMonster.CTIB.Cls3135.Cnt0
import Certificates.Kernel.BabyMonster.CTIB.Cls3135.Cnt1
import Certificates.Kernel.BabyMonster.CTIB.Cls3135.Cnt2
import Certificates.Kernel.BabyMonster.CTIB.Cls3135.Misc
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Monster.B.TwoA.Sp8.QuadCosetC

public section

namespace CertificateChecks.KernelBM.CTIB.Frame3135

open CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.Monster.B.GSide CFSG.KC.BM
  CFSG.KC.BM.CosetQ CFSG.KC.BM.OrbT CFSG.KC.BM.OrbW CertificateChecks.KernelBM.CTIB
  CertificateChecks.KernelBM.CTIB.CosetQ CertificateChecks.KernelBM.CTIB.Inner

set_option maxRecDepth 400000

theorem rankOff6 (j : ℕ) : rankOff 6 + j = j := by simp [rankOff]

theorem gA6_eq {j : ℕ} (hj : j < 15) :
    wordAut (genInvImgs ()) (centWordN 6 j) = arrOf (nthN Gs j) := by
  have h := words_of Certificates.certificate3110.1 (k := 6) (j := j) (by rw [rankOff6]; omega)
  rw [rankOff6] at h
  rw [h, word_imgs symFacts ct_eq _ (steps_of (by omega)), (wOK_eq (by omega)).1]

theorem ga_get {j : ℕ} (hj : j < 15) : (gA6 ()).getD j #[] = arrOf (nthN Gs j) := by
  rw [gA6, getD_range_map _ _ hj, gA6_eq hj]

theorem ds_get {j : ℕ} (hj : j < 15) : ds6.getD j 0 = nthN Ds j := by
  rw [ds6, getD_range_map _ _ hj, deltaN, rankOff6, ds_eq j (by omega)]

theorem ec_get : ∀ j < 15, eCodes.getD j 0 = nthN CFSG.KD.Orb3135.EC j := by decide +kernel

theorem qinv_eq (x : ℕ) : qinv x = qinvK LOq x := by
  rw [qinv, qinvK, QK.mulQ_eq, QK.mulQ_eq]

theorem prods : qinv 10541 = 4204845 ∧ qmul gArr 10541 854 = 10875 ∧ qmul gArr 4204845 10875 = 854 := by
  have h := Cls3135.prods
  simp only [andB_true] at h
  refine ⟨?_, ?_, ?_⟩
  · rw [qinv_eq]
    exact beq_iff.1 h.1
  · rw [← QK.mulQ_eq]
    exact beq_iff.1 h.2.1
  · rw [← QK.mulQ_eq]
    exact beq_iff.1 h.2.2

theorem fAct_eq {j : ℕ} (hj : j < 15) (n : ℕ) : fAct (gA6 ()) j n = Orb3135.act j n := by
  rw [fAct, ga_get hj, ec_get j hj, qinv_eq, beq_iff.1 (Cls3135.ec_inv j hj)]
  simp only [Orb3135.act, cjAutK, QK.mulQ_eq, QK.autQ_eq]

theorem fuse_act {k : ℕ} (hk : k < 37) (x : ℕ) :
    fuseAct (liftImgsN 6).toArray (gA6 ()) ds6 k x = fuseK LOq AH6 Gs Ds k x := by
  by_cases h : k < 22
  · have hb : Nat.blt k 22 = true := blt_iff.2 h
    have e : fuseK LOq AH6 Gs Ds k x = mulQ LOq (fld32 AH6 k) (mulQ LOq x (2 ^ k)) := by
      unfold fuseK
      rw [hb]
      rfl
    rw [e, fuseAct, if_pos h, qconj, lift6, arrOf_getD AH6 h, QK.mulQ_eq, QK.mulQ_eq]
  · obtain ⟨t, rfl⟩ : ∃ t, k = 22 + t := ⟨k - 22, by omega⟩
    have ht : t < 15 := by omega
    have hb : Nat.blt (22 + t) 22 = false := Bool.eq_false_iff.2 fun e => h (blt_iff.1 e)
    have e : fuseK LOq AH6 Gs Ds (22 + t) x = mulQ LOq (nthN Ds t) (autQ LOq (nthN Gs t) x) := by
      unfold fuseK
      rw [hb]
      change mulQ LOq (nthN Ds (22 + t - 22)) (autQ LOq (nthN Gs (22 + t - 22)) x) = _
      rw [Nat.add_sub_cancel_left]
    rw [e, fuseAct, if_neg h, Nat.add_sub_cancel_left, ga_get ht, ds_get ht, fuse, QK.autQ_eq,
      QK.mulQ_eq]

theorem act_eq : fuseAct (liftImgsN 6).toArray (gA6 ()) ds6 =
    fuseAct (arrOf AH6) ((List.range 15).map fun j => arrOf (nthN Gs (0 + j))).toArray
      ((List.range 15).map fun j => nthN Ds (0 + j)).toArray := by
  have hgL : ((List.range 15).map fun j => wordAut (genInvImgs ()) (centWordN 6 j)) =
      (List.range 15).map fun j => arrOf (nthN Gs (0 + j)) :=
    List.map_congr_left fun j hj => by rw [gA6_eq (List.mem_range.1 hj), Nat.zero_add]
  have hdL : ((List.range 15).map fun j => deltaN 6 j) =
      (List.range 15).map fun j => nthN Ds (0 + j) :=
    List.map_congr_left fun j hj => by
      rw [deltaN, rankOff6, ds_eq _ (by have := List.mem_range.1 hj; omega), Nat.zero_add]
  rw [lift6, gA6, ds6, hgL, hdL]

theorem ptB_inj {B n bound : ℕ} {SB : List ℕ} (h : ∀ i < n, incB B n bound SB i = true)
    {i j : ℕ} (hi : i < n) (hj : j < n) (e : ptB B SB i = ptB B SB j) : i = j := by
  rcases Nat.lt_trichotomy i j with hl | hl | hl
  · exact absurd e (Nat.ne_of_lt (incB_mono h j hj i hl))
  · exact hl
  · exact absurd e.symm (Nat.ne_of_lt (incB_mono h i hi j hl))

theorem card_filter_ptsB {B n bound : ℕ} {SB : List ℕ} (h : ∀ i < n, incB B n bound SB i = true)
    (P : ℕ → Prop) [DecidablePred P] :
    ((ptsB B n SB).filter P).card = Nat.count (fun i => P (ptB B SB i)) n := by
  have e : ptsB B n SB = (Finset.range n).image (ptB B SB) := by
    ext x
    simp [mem_ptsB]
  have hinj : Set.InjOn (ptB B SB) ↑((Finset.range n).filter fun i => P (ptB B SB i)) :=
    fun i hi j hj hij => ptB_inj h
      (Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1) hij
  rw [e, Finset.filter_image, Finset.card_image_of_injOn hinj, Nat.count_eq_card_filter_range]

theorem arr_filter {A : Array ℕ} {S : Finset ℕ} (hm : ∀ x, x ∈ A ↔ x ∈ S) (hs : A.size = S.card)
    (p : ℕ → Bool) : (A.toList.filter p).length = (S.filter fun x => p x = true).card := by
  have hset : A.toList.toFinset = S := by
    ext x
    rw [List.mem_toFinset, Array.mem_toList_iff, hm]
  have hnd : A.toList.Nodup := by
    have hc : (A.toList : Multiset ℕ).toFinset.card = Multiset.card (A.toList : Multiset ℕ) := by
      rw [Multiset.coe_card]
      change A.toList.toFinset.card = _
      rw [hset, Array.length_toList, hs]
    exact Multiset.coe_nodup.1 (Multiset.toFinset_card_eq_card_iff_nodup.1 hc)
  rw [← List.toFinset_card_of_nodup (hnd.filter _), List.toFinset_filter, hset]

theorem cntB_eq (f : ℕ → ℕ) (lo : ℕ) :
    ∀ len, cntB f lo len = Nat.count (fun j => f (lo + j) = 2) len
  | 0 => by rw [Nat.count_zero]; rfl
  | len + 1 => by
    change Nat.add (cntB f lo len) (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (f (Nat.add lo len)) 2)) = _
    rw [cntB_eq f lo len, Nat.count_succ]
    by_cases h : f (lo + len) = 2
    · have hb : Nat.beq (f (Nat.add lo len)) 2 = true := beq_iff.2 h
      rw [hb, if_pos h]
      rfl
    · have hb : Nat.beq (f (Nat.add lo len)) 2 = false := Bool.eq_false_iff.2 fun e => h (beq_iff.1 e)
      rw [hb, if_neg h]
      rfl

theorem count_blocks (p : ℕ → Prop) [DecidablePred p] (B : ℕ) : ∀ m,
    Nat.count p (B * m) = ∑ b ∈ Finset.range m, Nat.count (fun j => p (B * b + j)) B
  | 0 => by simp
  | m + 1 => by rw [Nat.mul_succ, Nat.count_add, count_blocks p B m, Finset.sum_range_succ]

theorem walkE_eq (e : ℕ) : walkE pR1 pR2 e = walkOK e := by
  unfold walkE walkOK
  change andB (Nat.blt (eRec e) 5) _ = _
  cases Nat.blt (eRec e) 5 <;> rfl

theorem beq_nat (a b : ℕ) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff]

theorem P_eq : Cls3135.P1 = pR1 ∧ Cls3135.P2 = pR2 :=
  ⟨beq_iff.1 (by quickRfl), beq_iff.1 (by quickRfl)⟩

theorem frChk_spec (hC : CensusLists) {a e : ℕ}
    (h : frChk LOq AH6 4204845 10541 Cls3135.P1 Cls3135.P2 a e ≠ 0) :
    commR6 innerTab (qmul gArr (qinv 10541) a) =
      Nat.beq (frChk LOq AH6 4204845 10541 Cls3135.P1 Cls3135.P2 a e) 2 := by
  obtain ⟨p1, p2⟩ := P_eq
  rw [p1, p2] at h ⊢
  rw [prods.1, ← QK.mulQ_eq]
  unfold frChk at h ⊢
  beta_reduce at h ⊢
  generalize mulQ LOq 4204845 a = n at h ⊢
  have hc : (qmul gArr (autApply gArr (liftImgsN 6).toArray n) 10541 == qmul gArr 10541 n) =
      Nat.beq (mulQ LOq (autQ LOq AH6 n) 10541) (mulQ LOq 10541 n) := by
    rw [lift6, ← QK.autQ_eq, ← QK.mulQ_eq, ← QK.mulQ_eq, beq_nat]
  unfold commR6
  rw [hc]
  rw [land_mod n] at h ⊢
  cases hcm : Nat.beq (mulQ LOq (autQ LOq AH6 n) 10541) (mulQ LOq 10541 n)
  · simp only [Bool.and_false]
    rfl
  · rw [hcm] at h
    dsimp only at h ⊢
    by_cases hv : n % 2 ^ 22 = 0
    · have hb : Nat.beq (n % 2 ^ 22) 0 = true := beq_iff.2 hv
      rw [hb]
      have hty : innerTy innerTab n ≠ 3 := by
        unfold innerTy
        rw [if_pos hv]
        split_ifs <;> omega
      simp only [Bool.and_true, beq_eq_false_iff_ne.2 hty]
      rfl
    · have hb : Nat.beq (n % 2 ^ 22) 0 = false := Bool.eq_false_iff.2 fun e => hv (beq_iff.1 e)
      rw [hb] at h ⊢
      dsimp only at h ⊢
      cases hw : andB (walkE pR1 pR2 e) (Nat.beq (Nat.land e 4194303) (n % 2 ^ 22))
      · rw [hw] at h
        exact (h rfl).elim
      · rw [andB_true, walkE_eq, beq_iff] at hw
        have hty := innerTy_walk hC hw.1 hw.2.symm (fun e0 => hv (hw.2.symm.trans e0))
        rw [hty]
        dsimp only
        change ((eRec e + 1 == 3) && true) = Nat.beq (Bool.rec (motive := fun _ => ℕ) 1 2 (Nat.beq (eRec e) 2)) 2
        cases hr : Nat.beq (eRec e) 2
        · have hne : eRec e + 1 ≠ 3 := fun h3 => by
            have := beq_iff.2 (by omega : eRec e = 2)
            rw [hr] at this
            exact absurd this (by decide)
          simp only [Bool.and_true, beq_eq_false_iff_ne.2 hne]
          rfl
        · have h3 : eRec e + 1 = 3 := by rw [beq_iff.1 hr]
          simp only [Bool.and_true, h3, beq_self_eq_true]
          rfl

theorem clos_all : ∀ i < 30240,
    closB Orb3135.act 15 1008 30240 CFSG.KD.Orb3135.SB CFSG.KD.Orb3135.EB i = true := by
  intro i hi
  obtain ⟨m, t, ht, rfl⟩ : ∃ m t, t < 2016 ∧ i = 2016 * m + t :=
    ⟨i / 2016, i % 2016, Nat.mod_lt _ (by decide), (Nat.div_add_mod i 2016).symm⟩
  have hm : m < 15 := by omega
  interval_cases m
  · exact Orb3135.clos0 t ht
  · exact Orb3135.clos1 t ht
  · exact Orb3135.clos2 t ht
  · exact Orb3135.clos3 t ht
  · exact Orb3135.clos4 t ht
  · exact Orb3135.clos5 t ht
  · exact Orb3135.clos6 t ht
  · exact Orb3135.clos7 t ht
  · exact Orb3135.clos8 t ht
  · exact Orb3135.clos9 t ht
  · exact Orb3135.clos10 t ht
  · exact Orb3135.clos11 t ht
  · exact Orb3135.clos12 t ht
  · exact Orb3135.clos13 t ht
  · exact Orb3135.clos14 t ht

theorem bfs854 :
    natCertOK (fAct (gA6 ())) 15 (fun p => decide (p < 2 ^ 23)) 854
        (natBfs (fAct (gA6 ())) 15 854 30241).1 (natBfs (fAct (gA6 ())) 15 854 30241).2.1
        (natBfs (fAct (gA6 ())) 15 854 30241).2.2.1 (natBfs (fAct (gA6 ())) 15 854 30241).2.2.2 = true ∧
      (natBfs (fAct (gA6 ())) 15 854 30241).1.size = 30240 := by
  obtain ⟨hS, hcard, hb⟩ := orbB_reach (fun k hk x => fAct_eq hk x) Orb3135.inc clos_all Orb3135.tree
    (by decide) (beq_iff.1 Orb3135.root)
  obtain ⟨hc, -, hsz⟩ := natBfs_native (valid := fun p => decide (p < 2 ^ 23)) (fuel := 30241) _
    (fun x => reach_bfs.trans (hS x)) (fun x hx => decide_eq_true (Nat.lt_of_lt_of_eq (hb x hx) rfl))
    ((Nat.le_of_eq hcard).trans (by decide))
  exact ⟨hc, hsz.trans hcard⟩

theorem rec43 : repOf PT6 (fld32 RT6 0) = 43 ∧
    ((Finset.range 529).filter (fun q => labOf PT6 q = labOf PT6 (fld32 RT6 0))).sum
      (sizeOf 6 PT6) = 34560 := by
  have h := congrArg (fun l : List (ℕ × ℕ × ℕ) => (l.getD 0 (0, 0, 0)).2.1) fr6
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by decide : 0 < 5),
    Option.map_some, Option.getD_some] at h
  rw [(root6 0 (by decide)).2.2, ← h]
  exact ⟨by decide +kernel, by decide +kernel⟩

theorem cls_reach : ∀ x, Reach (fuseAct (liftImgsN 6).toArray (gA6 ()) ds6) 37 43 x ↔
    x ∈ ptsB 960 34560 CFSG.KD.Cls3135.DB := by
  obtain ⟨act, hact⟩ : ∃ f, f = fuseAct (arrOf AH6)
      ((List.range 15).map fun j => arrOf (nthN Gs (0 + j))).toArray
      ((List.range 15).map fun j => nthN Ds (0 + j)).toArray := ⟨_, rfl⟩
  have hact1 : ∀ i < 22, ∀ n, act i n = qconj (gArr ()) (arrOf AH6) i n := fun i hi n => by
    rw [hact, fuseAct, ite_eq_left hi]
  have hact2 : ∀ t < 15, ∀ n,
      act (22 + t) n = fuse (gArr ()) (arrOf (nthN Gs (0 + t))) (nthN Ds (0 + t)) n :=
    fun t ht n => by
      rw [hact, fuseAct, ite_eq_right (by omega), (by omega : 22 + t - 22 = t),
        getD_range_map _ _ ht, getD_range_map _ _ ht]
  obtain ⟨hp, h0, -⟩ := root6 0 (by decide)
  obtain ⟨S, hSm, hScard, -, -⟩ :=
    forb_facts rank6 act hact1 hact2 hp ((trOK_spec (rank6.tr _ hp)).1 h0)
  obtain ⟨h43, hsz⟩ := rec43
  rw [h43] at hSm
  rw [hsz] at hScard
  have hM : fuseAct (liftImgsN 6).toArray (gA6 ()) ds6 = act := act_eq.trans hact.symm
  have hT := treeB_reach (act := fuseAct (liftImgsN 6).toArray (gA6 ()) ds6) (act' := Cls3135.fact)
    (fun k hk x => fuse_act hk x) Cls3135.tree (beq_iff.1 Cls3135.root)
  rw [hM] at hT
  have hsub : ptsB 960 34560 CFSG.KD.Cls3135.DB ⊆ S := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_ptsB.1 hx
    exact (hSm _).2 (reach_bfs.2 (hT i hi))
  have heq : ptsB 960 34560 CFSG.KD.Cls3135.DB = S :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hScard, (ptsB_card Cls3135.inc).1])
  rw [hM]
  intro x
  rw [heq]
  exact (hSm x).symm

theorem bfs43 : (∀ x, x ∈ (natBfs (fuseAct (liftImgsN 6).toArray (gA6 ()) ds6) 37 43 34561).1 ↔
      x ∈ ptsB 960 34560 CFSG.KD.Cls3135.DB) ∧
    (natBfs (fuseAct (liftImgsN 6).toArray (gA6 ()) ds6) 37 43 34561).1.size =
      (ptsB 960 34560 CFSG.KD.Cls3135.DB).card := by
  obtain ⟨-, hmem, hsz⟩ := natBfs_native (valid := fun _ => true) (fuel := 34561) _ cls_reach
    (fun _ _ => rfl) (by rw [(ptsB_card Cls3135.inc).1]; decide)
  exact ⟨hmem, hsz⟩

theorem blocks : ∀ b < 36, okB Cls3135.chk (960 * b) 960 = true ∧
    cntB Cls3135.chk (960 * b) 960 = nthN CFSG.KD.Cls3135.CK b := by
  intro b hb
  have get : ∀ {x y : Bool}, andB x y = true → x = true ∧ y = true := fun h => andB_true.1 h
  rcases (by omega : b < 12 ∨ (12 ≤ b ∧ b < 24) ∨ 24 ≤ b) with h | h | h
  · have := get (Cls3135.cnt0 b h)
    rw [Nat.zero_add] at this
    exact ⟨this.1, beq_iff.1 this.2⟩
  · obtain ⟨t, rfl⟩ : ∃ t, b = 12 + t := ⟨b - 12, by omega⟩
    have := get (Cls3135.cnt1 t (by omega))
    exact ⟨this.1, beq_iff.1 this.2⟩
  · obtain ⟨t, rfl⟩ : ∃ t, b = 24 + t := ⟨b - 24, by omega⟩
    have := get (Cls3135.cnt2 t (by omega))
    exact ⟨this.1, beq_iff.1 this.2⟩

theorem chk_ne : ∀ i < 34560, Cls3135.chk i ≠ 0 := by
  intro i hi
  have hb := (blocks (i / 960) (by omega)).1
  unfold okB at hb
  have h := allLt_eq_true.1 hb (i % 960) (Nat.mod_lt _ (by decide))
  have e : Nat.add (960 * (i / 960)) (i % 960) = i := by
    rw [Nat.add_eq]
    omega
  rw [notB_true, e] at h
  intro e0
  rw [e0] at h
  exact absurd h (by decide)

theorem ck_sum : ∑ b ∈ Finset.range 36, nthN CFSG.KD.Cls3135.CK b = 30240 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  decide +kernel

theorem filt (hC : CensusLists) :
    ((natBfs (fuseAct (liftImgsN 6).toArray (gA6 ()) ds6) 37 43 34561).1.toList.filter
      fun a => commR6 innerTab (qmul gArr (qinv 10541) a)).length = 30240 := by
  obtain ⟨hm, hs⟩ := bfs43
  rw [arr_filter hm hs, card_filter_ptsB Cls3135.inc,
    count_congr' (q := fun i => Cls3135.chk i = 2) fun i hi => by
      rw [frChk_spec hC (a := ptB 960 CFSG.KD.Cls3135.DB i)
        (e := fldB 96 960 CFSG.KD.Cls3135.WB i) (chk_ne i hi)]
      exact beq_iff,
    (by norm_num : (34560 : ℕ) = 960 * 36), count_blocks]
  rw [← ck_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [← (blocks b (Finset.mem_range.1 hb)).2, cntB_eq]

theorem all8 (hC : CensusLists) : (natBfs (fuseAct (liftImgsN 6).toArray (gA6 ()) ds6) 37 46090 65).1.all
    (fun a => !commR6 innerTab (qmul gArr (qinv 10541) a)) = true := by
  obtain ⟨hS, hcard, -⟩ := orbT_reach (act' := Outer3122.act) (fun k hk x => fuse_act hk x)
    Outer3122.inc Outer3122.clos Outer3122.tree (by decide) (beq_iff.1 Outer3122.root)
  obtain ⟨-, hmem, -⟩ := natBfs_native (valid := fun _ => true) (fuel := 65) _
    (fun x => reach_bfs.trans (hS x)) (fun _ _ => rfl) ((Nat.le_of_eq hcard).trans (by decide))
  rw [Array.all_eq_true']
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_ptsF.1 ((hmem x).1 hx)
  have h := beq_iff.1 (Cls3135.chk8 i hi)
  rw [frChk_spec hC (a := fld32 CFSG.KD.Outer3122.S i) (e := fldB 96 64 [CFSG.KD.Cls3135.V8] i)
    (by rw [h]; decide), h]
  rfl

theorem comm854 (hC : CensusLists) : commR6 innerTab 854 = true := by
  have h := frChk_spec hC (a := 10875) (e := CFSG.KD.Cls3135.W854)
    (by rw [beq_iff.1 Cls3135.chk854]; decide)
  rw [prods.1, prods.2.2, beq_iff.1 Cls3135.chk854] at h
  exact h

theorem mem43 : (natBfs (fuseAct (liftImgsN 6).toArray (gA6 ()) ds6) 37 43 34561).1.contains
    (qmul gArr 10541 854) = true := by
  rw [prods.2.1, Array.contains_iff_mem, bfs43.1, mem_ptsB]
  exact ⟨61, by decide, beq_iff.1 Cls3135.target⟩

theorem fix_all :(List.range 15).all (fixR6 (gA6 ())) = true := by
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.1 hj
  have h := beq_iff.1 (Cls3135.fix j hj')
  have e : qmul gArr (qinv (autApply gArr (liftImgsN 6).toArray (eCodes.getD j 0)))
      (qmul gArr (fuse gArr ((gA6 ()).getD j #[]) (ds6.getD j 0) 10541) (eCodes.getD j 0)) =
      Cls3135.fixK j := by
    have hd : ds6.getD j 0 = nthN Ds j := ds_get hj'
    rw [hd, ga_get hj', ec_get j hj', lift6, fuse, qinv_eq, ← QK.autQ_eq, ← QK.autQ_eq,
      ← QK.mulQ_eq, ← QK.mulQ_eq, ← QK.mulQ_eq]
    rfl
  rw [fixR6, e, h]
  rfl

end CertificateChecks.KernelBM.CTIB.Frame3135

end
