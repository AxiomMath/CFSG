module

public import Certificates.Kernel.Census.Co2R.Z
public import Certificates.Kernel.Census.Co2R.ZI0
public import Certificates.Kernel.Census.Co2R.ZI1
public import Certificates.Kernel.Census.Co2R.ZI2
public import Certificates.Kernel.Census.Co2R.ZI3
public import Certificates.Kernel.Census.Co2R.ZRL
public import Certificates.Kernel.Census.Co2R.T
public import Certificates.Kernel.Census.Co2R.TI0
public import Certificates.Kernel.Census.Co2R.TI1
public import Certificates.Kernel.Census.Co2R.TRL
public import Certificates.Kernel.Census.Co2R.U
public import CFSG.Certificates.Kernel.Census.PackedConjLProof
public import Certificates.Kernel.Census.Co2R.L
public import Certificates.Kernel.SporSch.Co2M.FratG
public import CFSG.Certificates.Kernel.Census.TreeProof
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2R
import all Certificates.Kernel.Census.Co2R.Data
import all CFSG.Certificates.Kernel.Census.ToMain
import all CFSG.Certificates.Kernel.Census.ToMainConj
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedConj
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.Kernel.Census.ConjSound
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Sporadic.Co2Schreier.ThirdNode
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile

public section

namespace CertificateChecks.KernelCensus.Co2R

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Co2
open CFSG.ComponentClassification.RankTwoSporadic.RootR CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CertificateChecks.KernelSporSch
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert

theorem eqA_self (n : ℕ) (a : Array ℕ) : eqA n a a = true := by
  unfold eqA
  rw [allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem pinvRest_append {n w : ℕ} (xs : List ℕ) : ∀ (l₁ l₂ : List ℕ) (m : ℕ) (im : List ℕ),
    pinvRest n w xs m im (l₁ ++ l₂) =
      (pinvRest n w xs m im l₁).bind fun im' => pinvRest n w xs (m + l₁.length) im' l₂
  | [], l₂, m, im => by simp [pinvRest]
  | x :: l₁, l₂, m, im => by
    rw [List.cons_append]
    simp only [pinvRest, cond_eq_if, List.length_cons]
    split_ifs <;> simp [pinvRest_append xs l₁, Nat.add_assoc, Nat.add_comm 1]

theorem pinvRest_chunks {n w : ℕ} (xs wt : List ℕ) (S K : ℕ) (I : ℕ → List ℕ)
    (hlen : wt.length = K * S)
    (hc : ∀ c < K, pinvRest n w xs (c * S) (I c) ((wt.drop (c * S)).take S) = some (I (c + 1))) :
    pinvRest n w xs 0 (I 0) wt = some (I K) := by
  have key : ∀ k ≤ K,
      pinvRest n w xs ((K - k) * S) (I (K - k)) (wt.drop ((K - k) * S)) = some (I K) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hlen])]
      rfl
    | succ k ih =>
      intro hk
      have hc1 : K - (k + 1) + 1 = K - k := by omega
      have hm : (K - (k + 1)) * S + S = (K - k) * S := by rw [← hc1, Nat.succ_mul]
      have hle : (K - k) * S ≤ K * S := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have hS : min S (wt.length - (K - (k + 1)) * S) = S := by
        apply Nat.min_eq_left
        rw [hlen]
        omega
      rw [← List.take_append_drop S (wt.drop ((K - (k + 1)) * S)), pinvRest_append,
        hc _ (by omega), Option.bind_some, List.drop_drop, List.length_take, List.length_drop, hS,
        hm, hc1]
      exact ih (by omega)
  simpa using key K le_rfl

theorem pinvOK_of_chunks {m S K : ℕ} {r : RootR} (hh : invHead m r = true)
    (hK : K * S = 2 ^ r.d.xs.length) (hc : ∀ c < K, invChunk m r S c = true) :
    pinvOK m 5 r.d.xs r.d.us r.d.im r.d.wt = true := by
  unfold invHead at hh
  unfold pinvOK
  simp only [Bool.and_eq_true] at hh ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hh
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  have hlen : r.d.wt.length = K * S := by rw [hK]; exact Nat.eq_of_beq_eq_true h3
  have hw := pinvRest_chunks (n := m) (w := 5) r.d.xs r.d.wt S K (imFrom r S) hlen
    fun c hc' => by
      have := hc c hc'
      unfold invChunk at this
      exact beq_iff_eq.1 this
  have h0 : imFrom r S 0 = r.d.im := by
    unfold imFrom
    exact List.filter_eq_self.2 fun x _ => by simp [Nat.ble_eq]
  have hKe : imFrom r S K = [] := by
    unfold imFrom
    refine List.filter_eq_nil_iff.2 fun x hx => ?_
    have := List.all_eq_true.1 h4 x hx
    simp only [Nat.blt_eq] at this
    rw [← hK] at this
    simp only [Nat.ble_eq, Bool.not_eq_true, decide_eq_true_eq]
    omega
  rw [h0, hKe] at hw
  rw [hw]
  rfl

theorem all_of_chunks {α : Type*} (f : α → Bool) (l : List α) (S K : ℕ) (hlen : l.length ≤ K * S)
    (hc : ∀ c < K, ((l.drop (c * S)).take S).all f = true) : l.all f = true := by
  have key : ∀ k ≤ K, (l.drop ((K - k) * S)).all f = true := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.sub_zero, List.drop_eq_nil_of_le hlen]
      rfl
    | succ k ih =>
      intro hk
      have hc1 : K - (k + 1) + 1 = K - k := by omega
      have hm : (K - (k + 1)) * S + S = (K - k) * S := by rw [← hc1, Nat.succ_mul]
      rw [← List.take_append_drop S (l.drop ((K - (k + 1)) * S)), List.all_append,
        Bool.and_eq_true, List.drop_drop, hm]
      exact ⟨hc _ (by omega), ih (by omega)⟩
  simpa using key K le_rfl

theorem roots_of_chunks {m : ℕ} {r : RootR}
    (hl : Nat.ble (r.d.us.toList.zip r.d.roots).length (4 * 1536) = true)
    (hcs : fitW 160 r.d.cs.toList = true) (hci : fitW 160 r.d.ci.toList = true)
    (h0 : rootChunkL m 160 r 1536 0 = true) (h1 : rootChunkL m 160 r 1536 1 = true)
    (h2 : rootChunkL m 160 r 1536 2 = true) (h3 : rootChunkL m 160 r 1536 3 = true) :
    (r.d.us.toList.zip r.d.roots).all
      (fun ur => prootOKC m 5 (r.d.nodes.map NodeP.basis) (cN m r) r.d.cs r.d.ci ur.1 ur.2) =
        true := by
  have hC : ∀ c, rootChunkL m 160 r 1536 c = rootChunk m r 1536 c := fun c => by
    unfold rootChunkL rootChunk cN
    exact prootsL_eq (fun j hj => pcN_getElem! r.d.nodes hj) hcs hci _
  rw [hC] at h0 h1 h2 h3
  refine all_of_chunks _ _ 1536 4 (by simpa using hl) fun c hc => ?_
  interval_cases c
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem all16 {f : ℕ → Bool} (h0 : (List.range' 0 4).all f = true)
    (h1 : (List.range' 4 4).all f = true) (h2 : (List.range' 8 4).all f = true)
    (h3 : (List.range' 12 4).all f = true) : ∀ c < 16, f c = true := by
  intro c hc
  by_cases a : c < 4
  · exact List.all_eq_true.1 h0 c (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases b : c < 8
  · exact List.all_eq_true.1 h1 c (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases d : c < 12
  · exact List.all_eq_true.1 h2 c (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 h3 c (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem all8 {f : ℕ → Bool} (h0 : (List.range' 0 4).all f = true)
    (h1 : (List.range' 4 4).all f = true) : ∀ c < 8, f c = true := by
  intro c hc
  by_cases a : c < 4
  · exact List.all_eq_true.1 h0 c (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 h1 c (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem root_ok {m : ℕ} (hm : m ≤ 2 ^ 5) {r : RootR} {i : ℕ}
    (kCanon : canonC m 5 r.d = true) (kPc : ppcOK m 5 r.d.xs r.d.rs r.d.cjs r.d.bs = true)
    (kInv : pinvOK m 5 r.d.xs r.d.us r.d.im r.d.wt = true)
    (kTab : ptabOK m 5 r.d.xs r.d.cm r.d.cs r.d.ci = true)
    (kRl : Nat.beq r.d.roots.length r.d.us.size = true)
    (kR : (r.d.us.toList.zip r.d.roots).all
      (fun ur => prootOKC m 5 (r.d.nodes.map NodeP.basis) (cN m r) r.d.cs r.d.ci ur.1 ur.2) = true)
    (kN : (List.range r.d.nodes.size).all (nodeF m r) = true)
    (kPs : r.ps.all (fun p => Nat.blt p m) = true)
    (kPts : (List.range m).all (fun q => Nat.blt (at' 12 r.O q) 2300 &&
      Nat.beq (at' 5 r.ix (at' 12 r.O q)) q) = true)
    (kXl : Nat.beq r.xw.length r.d.xs.length = true)
    (kXw : r.xw.all (fun x => x.all fun k => Nat.blt k (2 * 11)) = true)
    (kRel : pcRelB 12 L base r.xw r.d.rs r.d.cjs = true)
    (kRes : (r.xw.zip r.d.xs).all (fun p => resB 12 L 5 m r.O r.ix p.1 p.2) = true)
    (kX : rootXR 12 L base (pxs.getD i 0) r = true) (kCls : clsF m r = true)
    (kLeaf : rootLeafR 12 11 L base pxs i r = true) :
    rootCheckR 2300 12 11 L co2BaseR m 5 pxs i r = true := by
  obtain ⟨e1, e2, hid⟩ := SP.pid_good24 (n := m) (w := 5) hm (by omega)
  have G : SP.Good m 5 := ⟨by omega, hm, e1, e2⟩
  have C := SP.canonC_facts kCanon
  have hinW : ∀ P, canon1 m 5 P = true → pvalid m 5 P = true →
      inWP m P = (fun a => eqA m a (idA m)) (unpackP m 5 P) :=
    fun P hP _ => (SP.eqA_pid G hP).symm
  have htree := ptree_sound_proved (n := m) (w := 5) (ps := r.ps)
    (inW := fun a => eqA m a (idA m)) (inWP := inWP m) (d := r.d) (e0 := #[])
    (by omega) (by omega) hm kCanon rfl hinW kPc kInv kTab kRl kR
    (fun i hi => List.all_eq_true.1 kN i (List.mem_range.2 hi))
  rw [Array.map_empty] at htree
  have hcls : rootClsR 12 L co2BaseR m 5 r = true := by
    unfold clsF at kCls
    unfold rootClsR
    simp only [Bool.and_eq_true, List.all_eq_true] at kCls ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := kCls
    refine ⟨⟨h1, h2⟩, fun j hj => ?_⟩
    obtain ⟨⟨⟨ha, hb⟩, hc⟩, he⟩ := h3 j hj
    refine ⟨⟨⟨ha, ?_⟩, hc⟩, he⟩
    rw [Nat.eq_of_beq_eq_true hb, (SP.ppcA_eq G r.d.xs _ C.xs).1]
    exact eqA_self _ _
  unfold rootCheckR rootTreeR
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨htree, kPs⟩, kPts⟩, kXl⟩, kXw⟩, kRel⟩, kRes⟩, kX⟩, hcls⟩, kLeaf⟩

theorem ztP_zero : Co2M.ztP 0 = Co2M.zP := by simp [Co2M.ztP]

theorem ztP_one : Co2M.ztP 1 = Co2M.tP := by simp [Co2M.ztP]

set_option maxRecDepth 100000 in
theorem co2_census : ∃ (L : ℕ → ℕ) (pxs : List ℕ) (rs : List RootR), co2CheckR L pxs rs = true := by
  refine ⟨L, pxs, [Z.r, T.r, U.r], ?_⟩
  unfold co2CheckR
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, kInvL⟩, rfl⟩, rfl⟩, List.all_eq_true.2 fun i hi => ?_⟩
  · refine List.all_eq_true.2 fun k hk => ?_
    have hk' : k < 11 := List.mem_range.1 hk
    have hL : L k = CertificateChecks.KernelSpor.Co2A.S k := by
      have hb : Nat.blt k 11 = true := Nat.blt_eq.mpr hk'
      unfold L
      rw [hb]
      rfl
    rw [hL, CertificateChecks.KernelSpor.Co2A.binds.2.2.2.2.1 k hk']
    exact eqA_self _ _
  have hi' : i < 3 := List.mem_range.1 hi
  simp only [Bool.and_eq_true]
  interval_cases i
  · have hz : CFSG.KS.Raw.unpack 2300 12 (Co2M.WE 0) = zArr :=
      Co2M.unpack_eq Co2M.zRep (ztP_zero ▸ CFSG.KS.allN_spec Co2M.bind_e 0 (by norm_num))
    have hInv := pinvOK_of_chunks (K := 16) Z.kIH
      (by rw [Nat.eq_of_beq_eq_true Z.kLen]; norm_num) (all16 Z.kI0 Z.kI1 Z.kI2 Z.kI3)
    have hR := roots_of_chunks Z.kZl Z.kFitC Z.kFitI Z.kRL0 Z.kRL1 Z.kRL2 Z.kRL3
    refine ⟨⟨?_, Z.kLen⟩, root_ok (m := 32) (by norm_num) Z.kCanon Z.kPc hInv Z.kTab Z.kRl hR Z.kN
      Z.kPs Z.kPts Z.kXl Z.kXw Z.kRel Z.kRes Z.kX Z.kCls Z.kLeaf⟩
    simp only [co2Xs, List.getD_cons_zero, pxs, List.getElem!_cons_zero]
    rw [← hz]
    exact eqA_self _ _
  · have ht : CFSG.KS.Raw.unpack 2300 12 (Co2M.WE 1) = tArr :=
      Co2M.unpack_eq Co2M.tRep (ztP_one ▸ CFSG.KS.allN_spec Co2M.bind_e 1 (by norm_num))
    have hInv := pinvOK_of_chunks (K := 8) T.kIH
      (by rw [Nat.eq_of_beq_eq_true T.kLen]; norm_num) (all8 T.kI0 T.kI1)
    have hR := roots_of_chunks T.kZl T.kFitC T.kFitI T.kRL0 T.kRL1 T.kRL2 T.kRL3
    refine ⟨⟨?_, T.kLen⟩, root_ok (m := 32) (by norm_num) T.kCanon T.kPc hInv T.kTab T.kRl hR T.kN
      T.kPs T.kPts T.kXl T.kXw T.kRel T.kRes T.kX T.kCls T.kLeaf⟩
    simp only [co2Xs, List.getD_cons_succ, List.getD_cons_zero, pxs]
    rw [← ht]
    exact eqA_self _ _
  · refine ⟨⟨?_, U.kLen⟩, root_ok (m := 24) (by norm_num) U.kCanon U.kPc U.kInv U.kTab U.kRl U.kR U.kN
      U.kPs U.kPts U.kXl U.kXw U.kRel U.kRes U.kX U.kCls U.kLeaf⟩
    simp only [co2Xs, List.getD_cons_succ, List.getD_cons_zero, pxs, co2UArr]
    rw [SP.unpackP_pc' (by norm_num) (by norm_num) kCanon8, Co2M.s_eq (by norm_num),
      Co2M.s_eq (by norm_num)]
    exact eqA_self _ _

end CertificateChecks.KernelCensus.Co2R

end
