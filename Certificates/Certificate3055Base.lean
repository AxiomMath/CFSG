
module

public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertInputs
public import CFSG.Certificates.Kernel.SortTreeMul
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
public import Certificates.Kernel.MonsterB.Frame3055K
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

open CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.TwoA.Census CFSG.KC.SortTree CFSG.KLie.CT
  CFSG.KC.U6Orb CFSG.KC.Bfs

namespace CertificateChecks.Batch3055

set_option maxRecDepth 100000

@[expose] def cR : Array (Array ℕ) := ((List.range 21).map cRows).toArray

theorem kVec : boundL (pw2 22) frameOrbit.toList = true := by quickRfl

theorem kDist : nodupM frameOrbit.toList 0 = true := by quickRfl

theorem kRow : shapeL 22 (pw2 22) cR.toList = true := by quickRfl

theorem kEdge : edgeLOK frameOrbit.toList cR.toList Frame3055.PD (permTab 63 6) 63 21 = true := by
  quickRfl

theorem kReplay : replayDOK Frame3055.PD (permTab 63 6) 21 63 = true := by quickRfl

theorem kSizes : frameOrbit.size = 63 ∧ cR.size = 21 ∧ frameOrbit[0]! = 31 := by decide +kernel

theorem cR_get {k : ℕ} (hk : k < 21) : cR[k]! = cRows k := by
  rw [cR, getElem!_pos _ k (by simpa using hk)]
  simp

theorem frame : natCertOK actFrame 21 validW 31 frameCert = true ∧ frameCert.pts = frameOrbit := by
  have hE := edge_sound kSizes.1 kSizes.2.1 kVec kRow kEdge
  have hr := kReplay
  rw [replayDOK, strictB_eq, ← kSizes.1] at hr
  obtain ⟨h1, h2⟩ := natBfs_of_replay (act := actFrame) (valid := validW) (root := 31)
    (fuel := 200) (E := permTab 63 6 Frame3055.PD) (by rw [kSizes.1]; norm_num) kSizes.2.2
    (vec_inj (nodupM_spec _ _ kDist).1)
    (fun i hi k hk => by
      have e : actFrame k frameOrbit[i]! =
          CFSG.Monster.B.Co2.Native.actD 22 cR[k]! frameOrbit[i]! := by
        rw [cR_get hk]
        rfl
      rw [e]
      exact hE i (kSizes.1 ▸ hi) k hk)
    hr (fun j hj => by simpa [validW] using vec_lt kVec j hj) (by rw [kSizes.1]; norm_num)
  exact ⟨h2, h1⟩

open Frame3055 (actM recF edgeF)

@[expose] noncomputable def fixK (c : ℕ) : Bool := allN 8 fun j => Nat.beq (digK c j) j

@[expose] noncomputable def inOK (v : ℕ) : Bool :=
  anyN 16 fun j => Nat.beq (fget Frame3055.OK j 111) v

theorem kGen : (List.range 9).all (fun k => PermArr fPerms[k]!) = true ∧ fPerms.size = 9 := by
  decide +kernel

theorem kGF : ∀ k < 9, fget Frame3055.GF k 120 = packL 5 fPerms[k]!.toList := by decide +kernel

theorem kTree : treeOK actM 9 (fun _ => true) (akey idArr) recF 11520 111 4 14 64 180 = true :=
  treeOK_of_chunks (by decide) (sl_add (sl_add (sl_add none_lt Frame3055.t0 rfl) Frame3055.t1 rfl)
    Frame3055.t2 rfl)

theorem kClose : closeOK actM 9 recF edgeF 11520 111 64 180 = true := by
  refine closeOK_of_chunks (by decide) ?_
  open CertificateChecks.Frame3055 in
  exact sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add (sl_add
    (sl_add none_lt c0 rfl) c1 rfl) c2 rfl) c3 rfl) c4 rfl) c5 rfl) c6 rfl) c7 rfl) c8 rfl) c9 rfl)
    c10 rfl) c11 rfl

theorem kFix : allN 180 (fun c => allN 64 fun j => (fun v => orB (notB (fixK v)) (inOK v))
    (valF 111 (recF (Nat.add (Nat.mul c 64) j)))) = true := by quickRfl

@[expose] def octIdx : List ℕ :=
  [11519, 10788, 9979, 9248, 8415, 7684, 6875, 6144, 5375, 4644, 3835, 3104, 2271, 1540, 731, 0]

theorem kOct : ∀ j < 16, PermArr octPerms[j]! = true ∧ fixJ octPerms[j]! = true ∧
    octIdx[j]! < 11520 ∧ valF 111 (recF octIdx[j]!) = akey octPerms[j]! := by decide +kernel

theorem kOK : octPerms.size = 16 ∧ (octPerms.toList.map akey).Nodup ∧
    ∀ j < 16, fget Frame3055.OK j 111 ∈ octPerms.toList.map akey := by decide +kernel

theorem anyN_true {n : ℕ} {f : ℕ → Bool} (h : anyN n f = true) : ∃ i < n, f i = true := by
  induction n with
  | zero => exact absurd h (by simp [anyN])
  | succ n ih =>
    change orB (f n) (anyN n f) = true at h
    cases e : f n
    · rw [e] at h
      obtain ⟨i, hi, hv⟩ := ih h
      exact ⟨i, by omega, hv⟩
    · exact ⟨n, by omega, e⟩

theorem fixK_akey {x : Array ℕ} (hx : PermArr x = true) : fixK (akey x) = fixJ x := by
  have h : ∀ j < 8, digK (akey x) j = x[j]! := fun j hj => akey_digit hx (by omega)
  rw [fixK, fixJ, Bool.eq_iff_iff, CFSG.KC.SortTree.allN_iff, List.all_eq_true]
  simp only [List.mem_range, beq_iff_eq]
  constructor
  · intro H j hj
    rw [← h j hj]
    exact beq_iff.1 (H j hj)
  · intro H j hj
    rw [h j hj]
    exact beq_iff.2 (H j hj)

theorem mergeSort_eq_of_perm {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) :
    (l₁.mergeSort fun a b => decide (a ≤ b)) = l₂.mergeSort fun a b => decide (a ≤ b) := by
  have hs : ∀ l : List ℕ, (l.mergeSort fun a b => decide (a ≤ b)).Pairwise (· ≤ ·) := fun l =>
    (List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l).imp
      fun h => by simpa using h
  exact List.Perm.eq_of_pairwise' (hs l₁) (hs l₂)
    ((List.mergeSort_perm _ _).trans (h.trans (List.mergeSort_perm _ _).symm))

theorem group : fCheck = true := by
  obtain ⟨hg, hs⟩ := kGen
  rw [List.all_eq_true] at hg
  have hg' : ∀ k < fPerms.size, PermArr fPerms[k]! = true := fun k hk =>
    hg k (List.mem_range.2 (by omega))
  have T := kTree
  have E := kClose
  rw [← hs] at T E
  obtain ⟨h1, h2, h3, h4⟩ := bfsCert_tree_mem (fuel := 20000)
    (fun k hk x hx => PermArr_amul (hg' k hk) hx)
    (fun k hk x hx => by
      rw [Frame3055.actM, kGF k (by omega)]
      exact amulK_eq (hg' k hk) hx)
    PermArr_idArr (by norm_num) (by norm_num) T E
  have hfix := kFix
  rw [CFSG.KC.SortTree.allN_iff] at hfix
  have hrec : ∀ i < 11520, fixK (valF 111 (recF i)) = true → inOK (valF 111 (recF i)) = true := by
    intro i hi hf
    have := (CFSG.KC.SortTree.allN_iff _ _).1 (hfix (i / 64) (by omega)) (i % 64) (by omega)
    have e : Nat.add (Nat.mul (i / 64) 64) (i % 64) = i := by
      simp only [Nat.add_eq, Nat.mul_eq]
      omega
    rw [e] at this
    change orB (notB (fixK (valF 111 (recF i)))) (inOK (valF 111 (recF i))) = true at this
    rw [hf] at this
    exact this
  obtain ⟨hOs, hOn, hOm⟩ := kOK
  have hperm : ((fCert.pts.toList.filter fixJ).map akey).Perm (octPerms.toList.map akey) := by
    refine (List.perm_ext_iff_of_nodup (h4.sublist (List.filter_sublist.map _)) hOn).2 fun k => ?_
    simp only [List.mem_map, List.mem_filter, Array.mem_toList_iff]
    constructor
    · rintro ⟨x, ⟨hx, hfx⟩, rfl⟩
      obtain ⟨hpx, i, hi, e⟩ := (h3 x).1 hx
      have hin := hrec i hi (by rw [e, fixK_akey hpx]; exact hfx)
      obtain ⟨j, hj, ej⟩ := anyN_true hin
      rw [beq_iff, e] at ej
      have := hOm j hj
      rw [ej] at this
      simpa using this
    · rintro ⟨o, ho, rfl⟩
      obtain ⟨j, hj, e0⟩ := Array.mem_iff_getElem.1 ho
      have hj' : j < 16 := by rw [hOs] at hj; exact hj
      obtain ⟨hp, hf, hi, e⟩ := kOct j hj'
      rw [getElem!_pos octPerms j hj, e0] at hp hf e
      exact ⟨o, ⟨(h3 _).2 ⟨hp, _, hi, e⟩, hf⟩, rfl⟩
  simp only [fCheck, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨h1, h2⟩, mergeSort_eq_of_perm hperm⟩

end CertificateChecks.Batch3055

namespace Certificates

open CertificateChecks

end Certificates
