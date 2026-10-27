module

public import Certificates.Kernel.Co3Pump36903.Chk
public import Certificates.Kernel.Co3T.Facts
public import Certificates.Kernel.Co3Pair.Facts
public import Certificates.Kernel.Co3Five.Facts
public import Certificates.Data.Co3Pump
public meta import Certificates.Data.Co3Pump
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Pump36903

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.Co3TK
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T CertificateChecks.KernelCo3T
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
open CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native
open CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump
open CFSG.Monster.B.Co2 (allLt_iff)

theorem pL {k : Nat} (hk : k < 6) : permB 276 9 (KernelCo3Pair.PTN.L k) = true :=
  KernelCo3Pair.pP hk

theorem sift_of {k : Nat} (hk : k < 6) :
    inP (levels ()) (unpack 276 9 (KernelCo3Pair.PTN.L k)) = true :=
  inP_of (Orb.allN_iff.1 kSift k hk)

theorem fg_get {i : Nat} (hi : i < 2) :
    (fuseGens ())[i]! = unpack 276 9 (KernelCo3Pair.PTN.L i) := by
  unfold fuseGens
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact KernelCo3Pair.perm_eq (by omega)

theorem pgA_get {i : Nat} (hi : i < 2) :
    (pairGensA ())[i]! = unpack 276 9 (KernelCo3Pair.PTN.L (2 + i)) := by
  unfold pairGensA
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact KernelCo3Pair.perm_eq (by omega)

theorem pgB_get {i : Nat} (hi : i < 2) :
    (pairGensB ())[i]! = unpack 276 9 (KernelCo3Pair.PTN.L (4 + i)) := by
  unfold pairGensB
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact KernelCo3Pair.perm_eq (by omega)

theorem fuse_all : ∀ k < 243, fuseK k = true := by
  intro k hk
  have e : ∀ lo l, Nat.add lo l = lo + l := fun _ _ => rfl
  have key : ∀ c < 3, allBlk (81 * c) fuseK 81 = true := by
    intro c hc
    interval_cases c
    exacts [kFuse0, kFuse1, kFuse2]
  have h := allBlk_spec (key (k / 81) (by omega)) (k % 81) (Nat.mod_lt _ (by norm_num))
  rwa [e, Nat.div_add_mod] at h

theorem fuseCheck_eq : fuseCheck () = true := by
  unfold fuseCheck
  dsimp only
  simp only [Bool.and_eq_true, allLt_iff]
  refine ⟨fun i hi => ?_, fun k hk => ?_⟩
  · rw [fg_get hi, validA_of (pL (by omega)), sift_of (by omega)]
    exact ⟨rfl, rfl⟩
  · have h := fuse_all k hk
    unfold fuseK at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', bq, bqf] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    rcases h with (h | ⟨hp, hr⟩) | ⟨⟨⟨⟨hp1, hp2⟩, hg⟩, hd⟩, he⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨hp, hr⟩)
    · refine Or.inr ⟨⟨⟨⟨hp1, hp2⟩, hg⟩, hd⟩, ?_⟩
      have pc := pcj (pL (k := tGen[k]!) (by omega)) (pDE hp1)
      have e := eqU (pDE hk) pc
      rw [E_get hk, E_get hp1, fg_get hg, conj_unpack' hw (pL (by omega)) (pDE hp1)]
      unfold cj cm at e he
      rw [e]
      exact bq.2 he

theorem pair_core {gs : Array (Array ℕ)} {b C : ℕ} (hb : b + 2 ≤ 6)
    (hg : ∀ i < 2, gs[i]! = unpack 276 9 (KernelCo3Pair.PTN.L (b + i)))
    (hC : permB 276 9 C = true) (hk : pairK b C = true) :
    allLt 2 (fun i => validA 276 gs[i]! && inP (levels ()) gs[i]! &&
      commA 276 gs[i]! (unpack 276 9 C) && eqA 276 (powArr 276 gs[i]! 5) (idA 276) &&
      !(eqA 276 gs[i]! (idA 276))) = true := by
  rw [allLt_iff]
  intro i hi
  have h := Orb.allN_iff.1 hk i hi
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hc, h5⟩, h1⟩ := h
  have p := pL (k := b + i) (by omega)
  rw [hg i hi, validA_of p, sift_of (by omega), commA_eq p hC, powEq_id hw p, eqA_id hw p, hc, h5,
    h1]
  rfl

theorem pairACheck_eq : pairACheck () = true := by
  have hs : (pairGensA ()).size = 2 := by simp [pairGensA]
  have hE := enum_of KernelCo3Pair.bindA KernelCo3Pair.pAG KernelCo3Pair.EA.ok
    KernelCo3Pair.hkeys KernelCo3Pair.kEAkeys
    (fuel := 2000) (by rw [Nat.eq_of_beq_eq_true KernelCo3Pair.eA.2.1]; norm_num)
  have hN := Nat.eq_of_beq_eq_true KernelCo3Pair.eA.2.1
  unfold pairACheck pairCheck
  dsimp only
  rw [E_get (by decide : kA < 243), KernelCo3Pair.keys_eq, hE.1, hE.2.1, hN, hs,
    pair_core (by norm_num) (fun i hi => pgA_get hi) (pDE (by decide)) kPairA]
  decide

theorem pairBCheck_eq : pairBCheck () = true := by
  have hs : (pairGensB ()).size = 2 := by simp [pairGensB]
  have hE := enum_of KernelCo3Pair.bindB KernelCo3Pair.pBG KernelCo3Pair.EB.ok
    KernelCo3Pair.hkeys KernelCo3Pair.kEBkeys
    (fuel := 20000) (by rw [Nat.eq_of_beq_eq_true KernelCo3Pair.eB.2.1]; norm_num)
  have hN := Nat.eq_of_beq_eq_true KernelCo3Pair.eB.2.1
  unfold pairBCheck pairCheck
  dsimp only
  rw [E_get (by decide : kB < 243), KernelCo3Pair.keys_eq, hE.1, hE.2.1, hN, hs,
    pair_core (by norm_num) (fun i hi => pgB_get hi) (pDE (by decide)) kPairB]
  decide

theorem length_filter_range (f : Nat → Bool) :
    ∀ N, ((List.range N).filter f).length = cntN N f
  | 0 => rfl
  | N + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, length_filter_range f N]
    change _ = Nat.add (cntN N f) (cond (f N) 1 0)
    cases hf : f N <;> simp [List.filter_cons, hf]

theorem five_all : ∀ k < 1500, fiveK k = true := by
  intro k hk
  have e : ∀ lo l, Nat.add lo l = lo + l := fun _ _ => rfl
  have key : ∀ c < 6, allBlk (250 * c) fiveK 250 = true := by
    intro c hc
    interval_cases c
    exacts [kFive0, kFive1, kFive2, kFive3, kFive4, kFive5]
  have h := allBlk_spec (key (k / 250) (by omega)) (k % 250) (Nat.mod_lt _ (by norm_num))
  rwa [e, Nat.div_add_mod] at h

theorem fiveCheck_eq : fiveCheck () = true := by
  have hN : co3FiveC25Cert.pts.size = 1500 := by
    rw [KernelCo3Five.c25.2, Array.size_ofFn, KernelCo3Five.nums.2.1]
  have hQ : co3FiveQCert.pts.size = 125 := by
    rw [KernelCo3Five.cq.2, Array.size_ofFn, KernelCo3Five.nums.2.2.2.1]
  unfold fiveCheck
  dsimp only
  rw [hN, hQ, allLt_iff]
  intro k hk
  have h := five_all k hk
  unfold fiveK at h
  have p := KernelCo3Five.c25P hk
  have hf : (List.range 125).filter (fun j => commA 276 co3FiveQCert.pts[j]! co3FiveC25Cert.pts[k]!) =
      (List.range 125).filter fun j => commPt (KernelCo3Five.SQ.T j) (KernelCo3Five.S25.T k) := by
    apply List.filter_congr
    intro j hj
    have q := KernelCo3Five.qP (List.mem_range.1 hj)
    rw [q.1, p.1, commA_eq q.2 p.2]
  rw [hf, length_filter_range, p.1, powEq_id hw p.2, eqA_id hw p.2]
  simp only [Bool.or_eq_true, Bool.not_eq_true', Nat.blt_eq] at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  exact h

theorem facts : fuseCheck () = true ∧ pairACheck () = true ∧ pairBCheck () = true ∧
    fiveCheck () = true :=
  ⟨fuseCheck_eq, pairACheck_eq, pairBCheck_eq, fiveCheck_eq⟩

end CertificateChecks.KernelCo3Pump36903

end
