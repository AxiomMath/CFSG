module

public import Certificates.Kernel.Co3Five.Checks
public import CFSG.Certificates.Kernel.Co3Five.TailSound
public import CFSG.Certificates.Kernel.Item434.PkSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.RawSiftK
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.Misc.ChainTailQSound
import CFSG.Monster.B.Mathieu.SylowSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCo3Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermWit CFSG.KC.Misc.ChainTail
open CFSG.KC.Misc.ArrEnum (permB memK any_eqA_unpack' ag_unpack)
open CFSG.KC.B3S3K (cm pw)
open CFSG.KC.Item434 (Pk pk_id pk_conjA pk_commutatorA pk_powArr pk_comp eqA_pk isInvA_pk
  allLt_of_allN any_range_of)
open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Co3

local notation "AI" => CFSG.KS.Raw.Orb.allN_iff

theorem and_of {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa using h

theorem pF {k : ℕ} (hk : k < 40) : Pk 276 9 (co3FiveArr k) (FC.F k) := by
  refine ⟨?_, AI.1 kPerm k hk⟩
  unfold co3FiveArr
  rw [FC.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable3_sound FC.all k hk

theorem pI : Pk 276 9 (idA 276) I := pk_id kW

theorem pX25 : Pk 276 9 co3FiveX25Arr (FC.F 1) := by
  unfold co3FiveX25Arr
  exact pF (by norm_num)

theorem pX0 : Pk 276 9 co3FiveX0Arr (FC.F 0) := by
  unfold co3FiveX0Arr
  exact pF (by norm_num)

theorem pH {j : ℕ} (hj : j < 31) : Pk 276 9 (co3FiveHArr j) (hP j) := by
  unfold co3FiveHArr hP
  split_ifs
  · exact pI
  · exact pF (by omega)
  · exact pF (by omega)

theorem pLine {j : ℕ} (hj : j < 31) : Pk 276 9 (co3FiveLineArr j) (LN j) := by
  rw [Nat.eq_of_beq_eq_true (AI.1 kLN j hj)]
  unfold co3FiveLineArr lineP
  split_ifs
  · exact pF (by norm_num)
  · exact pF (by norm_num)
  · exact pk_conjA kW (pH hj) (pF (by norm_num))

theorem lines_get {j : ℕ} (hj : j < 31) : co3FiveLines[j]! = co3FiveLineArr j := by
  unfold co3FiveLines
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem pZ : Pk 276 9 co3FiveZArr (ZZ 0) := by
  rw [Nat.eq_of_beq_eq_true (and_of (and_of kZD).1).1]
  exact pk_conjA kW (pF (by norm_num)) (pF (by norm_num))

theorem c25g {k : ℕ} (hk : k < 4) : Pk 276 9 co3FiveC25GenArrs[k]! (S25.G k) := by
  rw [Nat.eq_of_beq_eq_true (AI.1 (and_of (and_of (and_of (and_of (and_of (and_of kGens).1).1).1).1).1).1 k hk)]
  interval_cases k
  · exact pF (k := 2) (by norm_num)
  · exact pF (k := 3) (by norm_num)
  · exact pF (k := 4) (by norm_num)
  · exact pF (k := 5) (by norm_num)

theorem qg {k : ℕ} (hk : k < 2) : Pk 276 9 co3FiveQGenArrs[k]! (SQ.G k) := by
  rw [Nat.eq_of_beq_eq_true (AI.1 (and_of (and_of (and_of (and_of (and_of (and_of kGens).1).1).1).1).1).2 k hk)]
  interval_cases k
  · exact pF (k := 2) (by norm_num)
  · exact pF (k := 3) (by norm_num)

theorem ag {k : ℕ} (hk : k < 2) : Pk 276 9 co3FiveAGenArrs[k]! (FC.F (k + 2)) := by
  interval_cases k
  · exact pF (k := 2) (by norm_num)
  · exact pF (k := 3) (by norm_num)

theorem pDG0 : Pk 276 9 co3FiveDGenArrs[0]! (DG 0) := by
  rw [Nat.eq_of_beq_eq_true (and_of (and_of kZD).1).2]
  exact pk_commutatorA kW (pF (k := 6) (by norm_num)) (pF (k := 7) (by norm_num))

theorem pDG1 : Pk 276 9 co3FiveDGenArrs[1]! (DG 1) := by
  rw [Nat.eq_of_beq_eq_true (and_of kZD).2]
  exact pF (k := 7) (by norm_num)

theorem dg {k : ℕ} (hk : k < 2) : Pk 276 9 co3FiveDGenArrs[k]! (DG k) := by
  interval_cases k
  · exact pDG0
  · exact pDG1

theorem c0g {k : ℕ} (hk : k < 3) : Pk 276 9 co3FiveC0GenArrs[k]! (S0.G k) := by
  have h := kGens
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, h0⟩, h1⟩, h2⟩, -⟩, -⟩ := h
  interval_cases k
  · rw [Nat.eq_of_beq_eq_true h0]
    exact pF (k := 0) (by norm_num)
  · rw [Nat.eq_of_beq_eq_true h1]
    exact pF (k := 6) (by norm_num)
  · rw [Nat.eq_of_beq_eq_true h2]
    exact pF (k := 7) (by norm_num)

theorem sdg {k : ℕ} (hk : k < 2) : Pk 276 9 co3FiveDGenArrs[k]! (SD.G k) := by
  have h := kGens
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, h0⟩, h1⟩ := h
  interval_cases k
  · rw [Nat.eq_of_beq_eq_true h0]
    exact pDG0
  · rw [Nat.eq_of_beq_eq_true h1]
    exact pDG1

theorem keysOK : ∀ p ∈ co3FiveKeyPts, p < 276 := by decide

theorem nums : S25.ng = 4 ∧ S25.N = 1500 ∧ SQ.ng = 2 ∧ SQ.N = 125 ∧ S0.ng = 3 ∧ S0.N = 300 ∧
    SD.ng = 2 ∧ SD.N = 60 := by
  have h := kNums
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  tauto

theorem bfsPerm {ng N : ℕ} {G T E S : ℕ → ℕ} (hp : ∀ k < ng, permB 276 9 (G k) = true)
    (hk : bfsK 276 9 ng G N T E S = true) : ∀ i < N, permB 276 9 (T i) = true :=
  (bfsK_points (fun y => permB 276 9 y = true) (pk_id kW).2
    (fun _ hy k hk' => (pk_comp kW ⟨rfl, hp k hk'⟩ ⟨rfl, hy⟩).2) hk).2.2.1

theorem tperm : (∀ i < 1500, permB 276 9 (S25.T i) = true) ∧ (∀ i < 125, permB 276 9 (SQ.T i) = true) ∧
    (∀ i < 300, permB 276 9 (S0.T i) = true) ∧ (∀ i < 60, permB 276 9 (SD.T i) = true) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · exact bfsPerm (fun k hk => (c25g (by rw [nums.1] at hk; exact hk)).2) S25.ok i
      (by rw [nums.2.1]; exact hi)
  · exact bfsPerm (fun k hk => (qg (by rw [nums.2.2.1] at hk; exact hk)).2) SQ.ok i
      (by rw [nums.2.2.2.1]; exact hi)
  · exact bfsPerm (fun k hk => (c0g (by rw [nums.2.2.2.2.1] at hk; exact hk)).2) S0.ok i
      (by rw [nums.2.2.2.2.2.1]; exact hi)
  · exact bfsPerm (fun k hk => (sdg (by rw [nums.2.2.2.2.2.2.1] at hk; exact hk)).2) SD.ok i
      (by rw [nums.2.2.2.2.2.2.2]; exact hi)

theorem pinned {gs : Array (Array ℕ)} {ng N fuel : ℕ} {G T E S : ℕ → ℕ} {SK : List ℕ}
    (hs : gs.size = ng) (hg : ∀ k < ng, Pk 276 9 gs[k]! (G k))
    (hk : bfsK 276 9 ng G N T E S = true)
    (hK : keysSK 276 9 co3FiveKeyPts N T SK = true) (hf : N ≤ fuel) :
    enumOK 276 gs co3FiveKeyPts (enumBfs 276 gs co3FiveKeyPts fuel) = true ∧
      (enumBfs 276 gs co3FiveKeyPts fuel).pts =
        Array.ofFn (n := N) fun i => unpack 276 9 (T i.val) :=
  ⟨enumOK_of_bfsK_base hs (fun k h => (hg k h).1) (fun k h => (hg k h).2) hk keysOK hK hf,
    enumBfs_pts_base hs (fun k h => (hg k h).1) hk keysOK hK hf⟩

theorem ofFn_get {N : ℕ} {T : ℕ → ℕ} {i : ℕ} (hi : i < N) :
    (Array.ofFn (n := N) fun i => unpack 276 9 (T i.val))[i]! = unpack 276 9 (T i) := by
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]

theorem c25 : enumOK 276 co3FiveC25GenArrs co3FiveKeyPts co3FiveC25Cert = true ∧
    co3FiveC25Cert.pts = Array.ofFn (n := S25.N) fun i => unpack 276 9 (S25.T i.val) :=
  pinned (by rw [nums.1]; rfl) (fun k hk => c25g (by rw [nums.1] at hk; exact hk)) S25.ok kK25
    (by rw [nums.2.1]; norm_num)

theorem cq : enumOK 276 co3FiveQGenArrs co3FiveKeyPts co3FiveQCert = true ∧
    co3FiveQCert.pts = Array.ofFn (n := SQ.N) fun i => unpack 276 9 (SQ.T i.val) :=
  pinned (by rw [nums.2.2.1]; rfl) (fun k hk => qg (by rw [nums.2.2.1] at hk; exact hk)) SQ.ok kKQ
    (by rw [nums.2.2.2.1]; norm_num)

theorem c0 : enumOK 276 co3FiveC0GenArrs co3FiveKeyPts co3FiveC0Cert = true ∧
    co3FiveC0Cert.pts = Array.ofFn (n := S0.N) fun i => unpack 276 9 (S0.T i.val) :=
  pinned (by rw [nums.2.2.2.2.1]; rfl) (fun k hk => c0g (by rw [nums.2.2.2.2.1] at hk; exact hk))
    S0.ok kK0 (by rw [nums.2.2.2.2.2.1]; norm_num)

theorem cd : enumOK 276 co3FiveDGenArrs co3FiveKeyPts co3FiveDCert = true ∧
    co3FiveDCert.pts = Array.ofFn (n := SD.N) fun i => unpack 276 9 (SD.T i.val) :=
  pinned (by rw [nums.2.2.2.2.2.2.1]; rfl)
    (fun k hk => sdg (by rw [nums.2.2.2.2.2.2.1] at hk; exact hk)) SD.ok kKD
    (by rw [nums.2.2.2.2.2.2.2]; norm_num)

theorem mem_of {c : ArrCert} {N : ℕ} {T : ℕ → ℕ}
    (hc : c.pts = Array.ofFn (n := N) fun i => unpack 276 9 (T i.val))
    (hT : ∀ i < N, permB 276 9 (T i) = true) {x : Array ℕ} {p : ℕ} (hx : Pk 276 9 x p)
    (h : memK N T p = true) : c.pts.toList.any (eqA 276 x) = true := by
  rw [hx.1, any_eqA_unpack' kW (by rw [hc, Array.size_ofFn])
    (fun i hi => by rw [hc]; exact ofFn_get hi) hT hx.2]
  exact h

theorem commA_pk {a b : Array ℕ} {p q : ℕ} (ha : Pk 276 9 a p) (hb : Pk 276 9 b q) :
    commA 276 a b = cmK p q :=
  eqA_pk kW (pk_comp kW ha hb) (pk_comp kW hb ha)

theorem siftOf {x : Array ℕ} {p : ℕ} (hx : Pk 276 9 x p)
    (h : siftR 276 9 CertificateChecks.KernelSpor.Co3C.LR CertificateChecks.KernelSpor.Co3C.TRI
      CertificateChecks.KernelSpor.Co3C.BP 7 p = true) :
    siftA 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3ChainBaseArr 0 x = true := by
  rw [hx.1]
  exact siftR_sound CertificateChecks.KernelSpor.Co3C.binds CertificateChecks.KernelSpor.Co3C.perm
    CertificateChecks.KernelSpor.Co3C.hl h

theorem siftF {k : ℕ} (hk : k < 40) :
    siftA 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3ChainBaseArr 0 (co3FiveArr k) =
      true :=
  siftOf (pF hk) (AI.1 (and_of kSift).1 k hk)

theorem sifts : co3FiveSiftArrs.all
    (siftA 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3ChainBaseArr 0) = true := by
  have e : co3FiveSiftArrs = [co3FiveArr 0, co3FiveArr 1, co3FiveArr 10, co3FiveArr 8,
      co3FiveArr 9, co3FiveArr 2, co3FiveArr 3, co3FiveArr 4, co3FiveArr 5, co3FiveArr 2,
      co3FiveArr 3, co3FiveArr 0, co3FiveArr 6, co3FiveArr 7] ++
      (List.range 31).map co3FiveHArr := rfl
  rw [e, List.all_append, Bool.and_eq_true]
  refine ⟨by simp only [List.all_cons, List.all_nil, siftF (k := 0) (by norm_num),
    siftF (k := 1) (by norm_num), siftF (k := 2) (by norm_num), siftF (k := 3) (by norm_num),
    siftF (k := 4) (by norm_num), siftF (k := 5) (by norm_num), siftF (k := 6) (by norm_num),
    siftF (k := 7) (by norm_num), siftF (k := 8) (by norm_num), siftF (k := 9) (by norm_num),
    siftF (k := 10) (by norm_num), Bool.and_self], ?_⟩
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  have hj' := List.mem_range.1 hj
  refine siftOf (pH hj') ?_
  unfold hP
  split_ifs
  · exact (and_of kSift).2
  · exact AI.1 (and_of kSift).1 _ (by omega)
  · exact AI.1 (and_of kSift).1 _ (by omega)

theorem fixes : (co3FiveZArr[0]! == 0 && co3FiveZArr[1]! == 1 && co3FiveZArr[2]! == 2 &&
    co3FiveZArr[3]! == 3) = true := by
  rw [pZ.1, CFSG.KS.Raw.Orb.unpack_get (by norm_num), CFSG.KS.Raw.Orb.unpack_get (by norm_num),
    CFSG.KS.Raw.Orb.unpack_get (by norm_num), CFSG.KS.Raw.Orb.unpack_get (by norm_num)]
  have h0 := Nat.eq_of_beq_eq_true (AI.1 kZ 0 (by norm_num))
  have h1 := Nat.eq_of_beq_eq_true (AI.1 kZ 1 (by norm_num))
  have h2 := Nat.eq_of_beq_eq_true (AI.1 kZ 2 (by norm_num))
  have h3 := Nat.eq_of_beq_eq_true (AI.1 kZ 3 (by norm_num))
  rw [h0, h1, h2, h3]
  rfl

theorem fixLev (i : ℕ) (hi : i < 7) :
    fixLevCount 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3FiveZArr i = fixZ i := by
  rw [pZ.1]
  exact fixLevCount_eq CertificateChecks.KernelSpor.Co3C.binds CertificateChecks.KernelSpor.Co3C.perm
    CertificateChecks.KernelSpor.Co3C.hl hi (ZZ 0)

theorem tail : tailOK 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3FiveZArr co3FiveZPows 3 4
    (idA 276) = true := by
  have hE : co3FiveZPows = (List.range 5).map fun e => unpack 276 9 (pw 276 9 (ZZ 0) e) := by
    unfold co3FiveZPows
    exact List.map_congr_left fun e _ => (pk_powArr kW pZ e).1
  refine tailOK_of_ptailK CertificateChecks.KernelSpor.Co3C.binds
    CertificateChecks.KernelSpor.Co3C.perm CertificateChecks.KernelSpor.Co3C.hl kW pZ.1 pZ.2
    (pw 276 9 (ZZ 0)) hE (fun e _ => (pk_powArr kW pZ e).2) 3 4 rfl (idA 276) I (PP.id kW)
    ?_ (ptailK_of_ptailQ (CFSG.KC.Misc.ArrEnum.pp_of_permB kW pZ.2) (by norm_num) (by norm_num) 2 4 I kTail)
  rw [pI.1]
  exact ag_unpack 276 9 I

theorem relsC : (co3FiveRels.all fun r => decide (r.2.2 < co3FiveX25PowArrs.size) &&
      decide (r.1 < co3ChainBaseArr.size) && decide (r.2.1 < co3ChainBaseArr.size) &&
      (co3FiveX25PowArrs[r.2.2]!)[co3ChainBaseArr[r.1]!]! == co3ChainBaseArr[r.2.1]!) = true := by
  have hb := CertificateChecks.KernelSpor.Co3C.binds
  have hbs : co3ChainBaseArr.size = 7 := hb.2.2.2.2.2.1
  have hbl := CFSG.KS.Raw.Orb.base_lt_of_levels hb CertificateChecks.KernelSpor.Co3C.hl
  have hps : co3FiveX25PowArrs.size = 5 := by simp [co3FiveX25PowArrs]
  rw [List.all_eq_true]
  intro r hr
  have h := List.all_eq_true.1 kRels r hr
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hps, hbs]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  have hx : co3FiveX25PowArrs[r.2.2]! = unpack 276 9 (pw 276 9 (FC.F 1) r.2.2) := by
    rw [getElem!_pos _ _ (by rw [hps]; exact h1)]
    simp only [co3FiveX25PowArrs, Array.getElem_ofFn]
    exact (pk_powArr kW pX25 _).1
  rw [hx, hb.2.2.2.2.2.2 _ h2, hb.2.2.2.2.2.2 _ h3,
    CFSG.KS.Raw.Orb.unpack_get (by rw [← hb.2.2.2.2.2.2 _ h2]; exact hbl _ h2)]
  exact Nat.eq_of_beq_eq_true h4

theorem x0s : (co3FiveX25Arr[0]! == 0) = true := by
  rw [pX25.1, CFSG.KS.Raw.Orb.unpack_get (by norm_num), Nat.eq_of_beq_eq_true (and_of kFixX).1]
  rfl

theorem fixxs : allLt 275 (fun p => co3FiveX25Arr[p + 1]! != p + 1) = true := by
  refine allLt_of_allN (and_of kFixX).2 fun p hp h => ?_
  have hp' : p + 1 < 276 := by omega
  rw [pX25.1, CFSG.KS.Raw.Orb.unpack_get hp']
  exact h

theorem brs : allLt ((rawLevels 276 co3ChainArrs co3ChainBaseArr)[1]!).pts.size (fun k =>
    !((List.range 3).any fun i =>
      ((rawLevels 276 co3ChainArrs co3ChainBaseArr)[1]!).pts[k]! == co3FiveC25Rep i) ||
    ptailOK 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3ChainBaseArr co3FiveX25Arr
      co3FiveX25PowArrs co3FiveRels co3FiveC25Cert.pts.toList 5 2
      ((rawLevels 276 co3ChainArrs co3ChainBaseArr)[1]!).tr[k]!) = true := by
  have hps : co3FiveX25PowArrs.size = 5 := by simp [co3FiveX25PowArrs]
  have hE : co3FiveC25Cert.pts.toList = (List.range S25.N).map fun e => unpack 276 9 (S25.T e) := by
    rw [c25.2]
    exact pts_toList (N := S25.N) (fun e => unpack 276 9 (S25.T e))
  have hR : ∀ r ∈ co3FiveRels, r.2.2 < co3FiveX25PowArrs.size := by
    rw [hps]
    decide
  have hxs : ∀ e < co3FiveX25PowArrs.size,
      co3FiveX25PowArrs[e]! = unpack 276 9 (pw 276 9 (FC.F 1) e) := by
    intro e he
    rw [getElem!_pos _ e he]
    simp only [co3FiveX25PowArrs, Array.getElem_ofFn]
    exact (pk_powArr kW pX25 _).1
  have key := ptailOK_of_ptailK CertificateChecks.KernelSpor.Co3C.binds
    CertificateChecks.KernelSpor.Co3C.perm CertificateChecks.KernelSpor.Co3C.hl kW pX25.1 pX25.2
    hxs hR hE (fun e he => tperm.1 e (by rw [nums.2.1] at he; exact he))
  obtain ⟨hsz, hpt⟩ := levels_agK CertificateChecks.KernelSpor.Co3C.binds
    CertificateChecks.KernelSpor.Co3C.perm CertificateChecks.KernelSpor.Co3C.hl 1 (by norm_num)
  have hc := Nat.eq_of_beq_eq_true kRc.2
  rw [hsz, hc]
  refine allLt_of_allN kBrC fun k hk h => ?_
  obtain ⟨hp1, -, hp3, hp4⟩ := hpt k (by rw [hc]; exact hk)
  unfold brC at h
  rw [hp1]
  rw [CFSG.KC.Misc.ArrEnum.anyNP_eq] at h
  rw [Bool.or_eq_true] at h ⊢
  exact h.imp id fun h' => key 5 2 rfl _ _ hp3 hp4 h'

theorem orbs : allLt 275 (fun q => (List.range co3FiveC25Cert.pts.size).any fun w =>
    (List.range 3).any fun i => (co3FiveC25Cert.pts[w]!)[co3FiveC25Rep i]! == q + 1) = true := by
  have hN : co3FiveC25Cert.pts.size = 1500 := by rw [c25.2, Array.size_ofFn, nums.2.1]
  rw [hN]
  refine allLt_of_allN kWC fun q hq h => ?_
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  refine any_range_of (WC q / 3) h.1 (any_range_of (WC q % 3) (Nat.mod_lt _ (by norm_num)) ?_)
  have hr : co3FiveC25Rep (WC q % 3) < 276 := by
    unfold co3FiveC25Rep
    split_ifs <;> norm_num
  rw [c25.2, ofFn_get (by rw [nums.2.1]; exact h.1), CFSG.KS.Raw.Orb.unpack_get hr]
  exact h.2

theorem chain_ok :
    co3FiveChainCheck (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3FiveC25Cert = true := by
  unfold co3FiveChainCheck
  have hf := kFix
  simp only [Bool.and_eq_true] at hf
  obtain ⟨⟨⟨f0, f1⟩, f2⟩, f3⟩ := hf
  rw [sifts, fixes, fixLev 0 (by norm_num), fixLev 1 (by norm_num), fixLev 2 (by norm_num),
    fixLev 3 (by norm_num), Nat.eq_of_beq_eq_true f0, Nat.eq_of_beq_eq_true f1,
    Nat.eq_of_beq_eq_true f2, Nat.eq_of_beq_eq_true f3, tail, relsC, x0s, fixxs, brs, orbs]
  rfl

theorem qP {k : ℕ} (hk : k < 125) : Pk 276 9 co3FiveQCert.pts[k]! (SQ.T k) := by
  rw [cq.2]
  exact ⟨ofFn_get (by rw [nums.2.2.2.1]; exact hk), tperm.2.1 k hk⟩

theorem q_ok : co3FiveQCheck co3FiveQCert co3FiveLines = true := by
  have hN : co3FiveQCert.pts.size = 125 := by rw [cq.2, Array.size_ofFn, nums.2.2.2.1]
  have hl := kQL
  unfold co3FiveQCheck
  rw [cq.1, hN]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine CFSG.Monster.B.Co2.allLt_iff.2 fun k hk => ?_
    have hP := qP hk
    have h := AI.1 kQW k hk
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [eqA_pk kW (pk_powArr kW hP 5) pI, Nat.eq_of_beq_eq_true h]
      quickRfl
    · rw [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨hj, he⟩ := h
      have hL := pLine hj
      have hpow := pk_powArr kW hL (WQ k % 5)
      rw [← Nat.eq_of_beq_eq_true he] at hpow
      rw [hP.1.trans hpow.1.symm]
      have hv := validA_unpack hL.2
      rw [← hL.1] at hv
      have hR := rep_of_validA hv
      have h5 : (CFSG.Monster.B.Co2.permOfArr 276 (co3FiveLineArr (WQ k / 5))) ^ 5 = 1 := by
        refine (CFSG.Monster.B.Co2.eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hR 5)
          CFSG.Monster.B.Co2.rep_idA).1 ?_
        rw [eqA_pk kW (pk_powArr kW hL 5) pI]
        exact (and_of (and_of (AI.1 kQL _ hj)).1).1
      refine (CFSG.Monster.B.Co2.eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr
        (CFSG.Monster.B.Mathieu.rep_powArr hR _) 5) CFSG.Monster.B.Co2.rep_idA).2 ?_
      rw [← pow_mul, mul_comm, pow_mul, h5, one_pow]
  · refine allLt_of_allN kQW fun k hk h => ?_
    rw [Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · left
      rw [eqA_pk kW (qP hk) pI]
      exact h
    · right
      rw [Bool.and_eq_true, Nat.blt_eq] at h
      refine any_range_of (WQ k / 5) h.1 (any_range_of (WQ k % 5) (Nat.mod_lt _ (by norm_num)) ?_)
      rw [lines_get h.1, eqA_pk kW (qP hk) (pk_powArr kW (pLine h.1) _)]
      exact h.2
  · refine allLt_of_allN kQD fun j hj h => allLt_of_allN h fun j' hj' h' => ?_
    rw [Bool.or_eq_true] at h' ⊢
    refine h'.imp id fun h'' => allLt_of_allN h'' fun e _ h3 => ?_
    rw [lines_get hj, lines_get hj', eqA_pk kW (pLine hj) (pk_powArr kW (pLine hj') e)]
    exact h3
  · refine allLt_of_allN hl fun j hj h => ?_
    simp only [Bool.and_eq_true] at h ⊢
    obtain ⟨⟨h5, hn⟩, hm⟩ := h
    rw [lines_get hj]
    refine ⟨⟨⟨isInvA_pk (pLine hj), ?_⟩, ?_⟩, mem_of cq.2 tperm.2.1 (pLine hj) hm⟩
    · rw [eqA_pk kW (pk_powArr kW (pLine hj) 5) pI]
      exact h5
    · rw [eqA_pk kW (pLine hj) pI]
      exact hn
  · exact CFSG.Monster.B.Co2.allLt_iff.2 fun j hj => isInvA_pk (pH hj)

theorem c25P {k : ℕ} (hk : k < 1500) : Pk 276 9 co3FiveC25Cert.pts[k]! (S25.T k) := by
  rw [c25.2]
  exact ⟨ofFn_get (by rw [nums.2.1]; exact hk), tperm.1 k hk⟩

theorem c25_all : ∀ k < 1500, c25Pt k = true := AI.1 kC25b

theorem cmP16_eq (p q : ℕ) : cmP16 p q = cmK p q := by
  unfold cmP16
  cases h : cmK p q
  · exact Bool.and_false _
  · rw [Bool.and_true]
    refine AI.2 fun i hi => ?_
    have e0 : cm 276 9 p q = cm 276 9 q p := Nat.eq_of_beq_eq_true h
    have e : pg 9 (mask 9) (pcomp 276 9 (mask 9) p q) i =
        pg 9 (mask 9) (pcomp 276 9 (mask 9) q p) i := congrArg (fun t => pg 9 (mask 9) t i) e0
    rw [CFSG.KS.PF.pg_pcomp (by norm_num) (by omega),
      CFSG.KS.PF.pg_pcomp (by norm_num) (by omega)] at e
    simp only [Nat.beq_eq]
    exact e

theorem c25_ok : co3FiveC25Check co3FiveC25Cert co3FiveQCert = true := by
  have hN : co3FiveC25Cert.pts.size = 1500 := by rw [c25.2, Array.size_ofFn, nums.2.1]
  have ha := kC25a
  simp only [Bool.and_eq_true] at ha
  obtain ⟨⟨⟨hc, hm2⟩, hm3⟩, hq⟩ := ha
  unfold co3FiveC25Check
  rw [c25.1, hN]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · refine allLt_of_allN hc fun k hk h => ?_
    rw [commA_pk (c25g hk) pX25]
    rw [Nat.eq_of_beq_eq_true (AI.1 (and_of (and_of (and_of (and_of (and_of (and_of
      kGens).1).1).1).1).1).1 k hk)]
    exact h
  · refine CFSG.Monster.B.Co2.allLt_iff.2 fun k hk => ?_
    interval_cases k
    · exact mem_of c25.2 tperm.1 (ag (k := 0) (by norm_num)) hm2
    · exact mem_of c25.2 tperm.1 (ag (k := 1) (by norm_num)) hm3
  · refine allLt_of_allN hq fun k hk h => allLt_of_allN h fun l hl h' => ?_
    have e := Nat.eq_of_beq_eq_true (AI.1 (and_of (and_of (and_of (and_of (and_of (and_of
      kGens).1).1).1).1).1).1 k hk)
    have hg := c25g hk
    rw [e] at hg
    exact mem_of cq.2 tperm.2.1 (pk_conjA kW hg (ag hl)) h'
  · refine CFSG.Monster.B.Co2.allLt_iff.2 fun k hk => ?_
    have h := c25_all k hk
    unfold c25Pt at h
    rw [cmP16_eq, cmP16_eq] at h
    rw [commA_pk (c25P hk) (ag (k := 0) (by norm_num)),
      commA_pk (c25P hk) (ag (k := 1) (by norm_num))]
    rw [Bool.or_eq_true] at h ⊢
    refine h.imp id fun h' => ?_
    rw [CFSG.KC.Misc.ArrEnum.anyNP_eq, List.any_eq_true] at h'
    obtain ⟨e, he, h3⟩ := h'
    refine any_range_of e (List.mem_range.1 he) ?_
    rw [eqA_pk kW (c25P hk) (pk_powArr kW pX25 e)]
    exact h3

theorem c0P {k : ℕ} (hk : k < 300) : Pk 276 9 co3FiveC0Cert.pts[k]! (S0.T k) := by
  rw [c0.2]
  exact ⟨ofFn_get (by rw [nums.2.2.2.2.2.1]; exact hk), tperm.2.2.1 k hk⟩

theorem keyInj {N : ℕ} {T : ℕ → ℕ} {SK : List ℕ}
    (hK : keysSK 276 9 co3FiveKeyPts N T SK = true) :
    ∀ i < N, ∀ j < N, keyA 276 co3FiveKeyPts (unpack 276 9 (T i)) =
      keyA 276 co3FiveKeyPts (unpack 276 9 (T j)) → i = j := by
  intro i hi j hj e
  rw [keyA_unpack keysOK, keyA_unpack keysOK] at e
  exact keysSK_spec hK i hi j hj e

theorem c0_ok : co3FiveC0Check co3FiveC0GenArrs co3FiveDGenArrs co3FiveC0Cert co3FiveDCert =
    true := by
  have hN0 : co3FiveC0Cert.pts.size = 300 := by rw [c0.2, Array.size_ofFn, nums.2.2.2.2.2.1]
  have hND : co3FiveDCert.pts.size = 60 := by rw [cd.2, Array.size_ofFn, nums.2.2.2.2.2.2.2]
  have ha := kC0a
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc0, hc1⟩, hc2⟩, hg⟩, hk⟩, hb⟩, hcj⟩, hcm⟩, hnd⟩ := ha
  have pG : Pk 276 9 co3FiveGArr (FC.F 8) := pF (by norm_num)
  have pK : Pk 276 9 co3FiveKArr (FC.F 9) := pF (by norm_num)
  have hDT : co3FiveDCert.pts = Array.ofFn (n := 60) fun i => unpack 276 9 (SD.T i.val) := by
    rw [cd.2, nums.2.2.2.2.2.2.2]
  unfold co3FiveC0Check
  rw [c0.1, hN0, cd.1, hND]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, isInvA_pk pG⟩, isInvA_pk pK⟩, mem_of c0.2 tperm.2.2.1 pG hg⟩,
    mem_of c0.2 tperm.2.2.1 pK hk⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine CFSG.Monster.B.Co2.allLt_iff.2 fun k hk => ?_
    have h := c0g hk
    rw [commA_pk h pX0]
    have hgk := kGens
    simp only [Bool.and_eq_true] at hgk
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, h0⟩, h1⟩, h2⟩, -⟩, -⟩ := hgk
    interval_cases k
    · rw [Nat.eq_of_beq_eq_true h0]
      exact hc0
    · rw [Nat.eq_of_beq_eq_true h1]
      exact hc1
    · rw [Nat.eq_of_beq_eq_true h2]
      exact hc2
  · have p7 : Pk 276 9 co3FiveC0GenArrs[2]! (FC.F 7) := pF (k := 7) (by norm_num)
    rw [eqA_pk kW p7 (pk_commutatorA kW pG pK)]
    exact hb
  · refine allLt_of_allN hcj fun k hk h => allLt_of_allN h fun l hl h' => ?_
    exact mem_of cd.2 tperm.2.2.2 (pk_conjA kW (c0g hk) (dg hl)) h'
  · refine allLt_of_allN hcm fun k hk h => allLt_of_allN h fun l hl h' => ?_
    exact mem_of cd.2 tperm.2.2.2 (pk_commutatorA kW (c0g hk) (c0g hl)) h'
  · rw [commA_pk (dg (k := 0) (by norm_num)) (dg (k := 1) (by norm_num)), hnd]
    rfl
  · refine conjSimpleOK_of_ctreeR (WT := WT) kW keysOK cd.1 hDT
      (fun i hi => tperm.2.2.2 i hi) (Nat.eq_of_beq_eq_true kD0)
      (fun i hi j hj e => keyInj (N := 60) (by rw [← nums.2.2.2.2.2.2.2]; exact kKD) i hi j hj e)
      (fun k hk => ?_)
    have h := AI.1 kCls k hk
    rw [Bool.or_eq_true] at h
    refine h.imp id fun h' => ?_
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨⟨hx, hr⟩, hrr⟩, he⟩ := h'
    have ht : (!Nat.beq (WR (WR k % 64) % 64) (WR k % 64) ||
        allN 60 (ctreePt 276 9 60 (WR k % 64) SD.T (WT (WR k % 64)))) = true :=
      AI.1 kTree _ (Nat.blt_eq.mp hr)
    rw [hrr, Bool.not_true, Bool.false_or] at ht
    exact ⟨WR k % 64, Nat.blt_eq.mp hr, WR k / 64, Nat.blt_eq.mp hx, Nat.eq_of_beq_eq_true he,
      AI.1 ht⟩
  · refine allLt_of_allN kC0b fun k hk h => ?_
    unfold c0Pt at h
    rw [cmP16_eq, cmP16_eq] at h
    rw [commA_pk (c0P hk) (dg (k := 0) (by norm_num)), commA_pk (c0P hk) (dg (k := 1) (by norm_num))]
    rw [Bool.or_eq_true] at h ⊢
    refine h.imp id fun h' => ?_
    rw [CFSG.KC.Misc.ArrEnum.anyNP_eq, List.any_eq_true] at h'
    obtain ⟨e, he, h3⟩ := h'
    refine any_range_of e (List.mem_range.1 he) ?_
    rw [eqA_pk kW (c0P hk) (pk_powArr kW pX0 e)]
    exact h3
  · exact isInvA_pk (pF (k := 10) (by norm_num))

end CertificateChecks.KernelCo3Five

end
