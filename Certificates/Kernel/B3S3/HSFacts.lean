module

public import Certificates.Kernel.B3S3.HSChecks
public import Certificates.Kernel.B3S3.HSTail
public import Certificates.Kernel.B3S3.HSJoin
public import CFSG.Certificates.Kernel.B3S3KCard
public import CFSG.Certificates.Kernel.HexArrsSound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.Sporadic.Schreier.PairHSOrder
public import Certificates.Kernel.Misc.Perm.HSMcL
import Certificates.Certificate2218
import Certificates.Certificate2219
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Simproc.Factors
public import CFSG.Certificates.Kernel.BfsPinSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelB3S3.HS

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.RankThree.PartTwo.KFacts.K426
open CFSG.Monster.B.Co2 (permOfArr)
open CFSG.KC.Misc.Clos (allR forall_of_chunks)

theorem bindHex {s : String} {cs : List Char} {N : ℕ} {F : ℕ → ℕ} (hs : s = String.ofList cs)
    (h : CFSG.KC.HexArrs.hexArrsK cs 3 3850 12 N F = true) : BindA 3850 12 (hexArrs 3850 3 s) N F := by
  rw [hs]
  exact CFSG.KC.HexArrs.hexArrs_sound h

theorem nQ : QG.N = 2 := Nat.eq_of_beq_eq_true nT.1
theorem nL : LX.N = 4 := Nat.eq_of_beq_eq_true nT.2.1
theorem nH : H.N = 4 := Nat.eq_of_beq_eq_true nT.2.2.1
theorem nX : XC.N = 1 := Nat.eq_of_beq_eq_true nT.2.2.2.1
theorem nS : SS.N = 11 := Nat.eq_of_beq_eq_true nT.2.2.2.2.1
theorem nG : GG.N = 4 := Nat.eq_of_beq_eq_true nT.2.2.2.2.2

theorem bindQ0 : BindA 3850 12 hsS3QGens 2 QG.F := nQ ▸ bindHex QG.eq QG.all
theorem bindL : BindA 3850 12 hsS3Lines 4 LX.F := nL ▸ bindHex LX.eq LX.all
theorem bindH : BindA 3850 12 hsS3Trans 4 H.F := nH ▸ bindHex H.eq H.all
theorem bindX : BindA 3850 12 hsS3CaseX 1 XC.F := nX ▸ bindHex XC.eq XC.all
theorem bindS : BindA 3850 12 hsS3C0S 11 SS.F := nS ▸ bindHex SS.eq SS.all
theorem bindG0 : BindA 3850 12 hsS3C0Gens 4 GG.F := nG ▸ bindHex GG.eq GG.all

theorem binds0 : Binds 3850 12 C0.S 11 6 C0.BP hsS3C0S hsS3C0Base := by
  refine ⟨by norm_num, by norm_num, by norm_num, bindS.1, fun j hj => ?_, by decide +kernel,
    bget0⟩
  rw [bindS.2 j hj, Nat.eq_of_beq_eq_true (bS j hj)]

theorem bindQ : BindA 3850 12 hsS3QGens EQ.ng EQ.G := by
  rw [Nat.eq_of_beq_eq_true n0.2.2.2]
  refine ⟨bindQ0.1, fun j hj => ?_⟩
  rw [bindQ0.2 j hj, Nat.eq_of_beq_eq_true (bQE j hj)]

theorem bindG : BindA 3850 12 hsS3C0Gens E0.ng E0.G := by
  rw [Nat.eq_of_beq_eq_true n0.2.2.1]
  refine ⟨bindG0.1, fun j hj => ?_⟩
  rw [bindG0.2 j hj, Nat.eq_of_beq_eq_true (bG j hj)]

theorem pQE : ∀ j < EQ.ng, permB 3850 12 (EQ.G j) = true := by
  intro j hj
  rw [Nat.eq_of_beq_eq_true n0.2.2.2] at hj
  rw [Nat.eq_of_beq_eq_true (bQE j hj)]
  exact Orb.allN_iff.1 pQ j hj

theorem pG : ∀ k < E0.ng, permB 3850 12 (E0.G k) = true := by
  intro k hk
  have h := Orb.allN_iff.1 comm0 k (by rw [Nat.eq_of_beq_eq_true n0.2.2.1] at hk; exact hk)
  rw [Bool.and_eq_true] at h
  exact h.1

theorem hE0p : allN E0.N (fun i => permB 3850 12 (E0.T i)) = true :=
  perm_of_bfsK szOK' pG E0.ok

theorem hEQp : allN EQ.N (fun i => permB 3850 12 (EQ.T i)) = true :=
  perm_of_bfsK szOK' pQE EQ.ok

theorem head0 : Nat.beq (C0.S 0) (CertificateChecks.KernelMisc.HSMcL.HS.F 0) = true ∧
    Nat.beq (C0.S 1) (CertificateChecks.KernelMisc.HSMcL.HS.F 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem hA (j : ℕ) (hj : j < 2) :
    CFSG.Sporadic.Schreier.hsStrongArrs[j]! = unpack 3850 12 (C0.S j) := by
  rw [CertificateChecks.KernelMisc.HSMcL.hsStrongArrs_get j hj]
  interval_cases j
  · rw [Nat.eq_of_beq_eq_true head0.1]
  · rw [Nat.eq_of_beq_eq_true head0.2]

theorem pS : ∀ j < 11, permB 3850 12 (C0.S j) = true := fun j hj =>
  permB_of_pp (pp_of_permOK szOK' (Orb.allN_iff.1 perm0 j hj))

theorem enumQ : enumOK 3850 hsS3QGens hsS3C0Base.toList
      (enumBfs 3850 hsS3QGens hsS3C0Base.toList (9 + 1)) = true ∧
    (enumBfs 3850 hsS3QGens hsS3C0Base.toList (9 + 1)).pts.size = EQ.N ∧
    ∀ i < EQ.N, (enumBfs 3850 hsS3QGens hsS3C0Base.toList (9 + 1)).pts[i]! =
      unpack 3850 12 (EQ.T i) :=
  enum_of bindQ pQE EQ.ok (mem_base_lt binds0 C0.hl) EQ.keys
    (by rw [Nat.eq_of_beq_eq_true n0.1]; omega)

theorem hW0 : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 11 d0 = hsS3C0W := by decide +kernel

theorem hnd0 : hsS3C0Base.toList.Nodup := by decide +kernel

theorem lev : rawOrbitSizes 3850 hsS3C0S hsS3C0Base =
    (List.range 6).map fun i => rcnt (C0.LR i) :=
  rawOrbitSizesK_sound binds0 perm0 C0.hl

theorem siftL {G : ℕ}
    (h : Nat.beq (Nat.shiftRight G (3850 * 12)) 0 = true ∧
      allN 3850 (fun t => Nat.blt (pg 12 (mask 12) G t) 3850) = true ∧
      siftK 3850 12 (mask 12) (3850 * 12) (pidn 3850 12) C0.LR C0.TRI C0.BP 6 0 G = true) :
    siftA 3850 (rawLevels 3850 hsS3C0S hsS3C0Base) hsS3C0Base 0 (unpack 3850 12 G) = true :=
  siftA_of binds0 perm0 C0.hl h

theorem hord : Nat.card (Subgroup.closure (Set.range fun j : Fin 2 =>
    permOfArr 3850 hsS3C0S[j.val]!)) ≤ (rawOrbitSizes 3850 hsS3C0S hsS3C0Base).prod := by
  have g0 : permOfArr 3850 hsS3C0S[0]! = CFSG.Sporadic.Schreier.hsGen 0 := by
    rw [binds0.2.2.2.2.1 0 (by norm_num), ← hA 0 (by norm_num)]
    rfl
  have g1 : permOfArr 3850 hsS3C0S[1]! = CFSG.Sporadic.Schreier.hsGen 1 := by
    rw [binds0.2.2.2.2.1 1 (by norm_num), ← hA 1 (by norm_num)]
    rfl
  have e : Set.range (fun j : Fin 2 => permOfArr 3850 hsS3C0S[j.val]!) =
      {CFSG.Sporadic.Schreier.hsGen 0, CFSG.Sporadic.Schreier.hsGen 1} := by
    ext g
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two,
      Fin.val_zero, Fin.val_one, g0, g1]
    exact ⟨fun h => h.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm),
      fun h => h.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)⟩
  have hc := @CFSG.Sporadic.Schreier.card_hsP
   
  rw [e, lev, Nat.eq_of_beq_eq_true orb0]
  exact le_of_eq hc

theorem crit0 (pts : Array (Array ℕ)) (hs : pts.size = E0.N)
    (hp : ∀ i < E0.N, pts[i]! = unpack 3850 12 (E0.T i)) :
    critOK 3850 pts 360 ⟨1, 0, 0, [2, 5], [1]⟩ = true := by
  change (convProdOK 3850 pts [2, 5] [1] &&
    (Nat.primeFactorsList 360).all fun q => q == 3 || [2, 5].contains q) = true
  rw [Bool.and_eq_true]
  have hcv : allN E0.N (convAt 3850 12 E0.N E0.T [2, 5] [1] WJ WR) = true := by
    rw [Orb.allN_iff, Nat.eq_of_beq_eq_true n0.2.1]
    exact forall_of_chunks 60 6 cv fun c hc => by
      interval_cases c
      · exact cv_0
      · exact cv_1
      · exact cv_2
      · exact cv_3
      · exact cv_4
      · exact cv_5
  exact ⟨convProdOK_of szOK' hs hp (fun i hi => Orb.allN_iff.1 hE0p i hi) hcv,
    by simp only [Nat.primeFactorsList_ofNat]; decide⟩

theorem tail0 : allN (rcnt (C0.LR 0)) (ptailBranchK 3850 12 C0.LR C0.TR C0.BP (XC.F 0)
    (pw 3850 12 (XC.F 0)) hsS3C0Rels E0.N E0.T 6) = true := by
  rw [Orb.allN_iff, Nat.eq_of_beq_eq_true rc0]
  exact forall_of_chunks 350 11 br fun c hc => by
    interval_cases c
    · exact br_0
    · exact br_1
    · exact br_2
    · exact br_3
    · exact br_4
    · exact br_5
    · exact br_6
    · exact br_7
    · exact br_8
    · exact br_9
    · exact br_10

theorem case_of {D : Data} {k : Case} (hn : D.n = 3850)
    (hDA : D.A = CFSG.Sporadic.Schreier.hsStrongArrs[0]!)
    (hDB : D.B = CFSG.Sporadic.Schreier.hsStrongArrs[1]!)
    (hS : k.S = hsS3C0S) (hW : k.W = hsS3C0W) (hbase : k.base = hsS3C0Base)
    (hrels : k.rels = hsS3C0Rels) (hgens : k.gens = hsS3C0Gens) (hcard : k.card = 360)
    (hcrit : k.crit = ⟨1, 0, 0, [2, 5], [1]⟩) :
    caseOK D k (unpack 3850 12 (XC.F 0)) = true := by
  have hN : E0.N = k.card := by rw [hcard]; exact Nat.eq_of_beq_eq_true n0.2.1
  have hb : Binds 3850 12 C0.S 11 6 C0.BP k.S k.base := by rw [hS, hbase]; exact binds0
  have hor : Nat.card (Subgroup.closure (Set.range fun j : Fin 2 => permOfArr 3850 k.S[j.val]!)) ≤
      (rawOrbitSizes 3850 k.S k.base).prod := by rw [hS, hbase]; exact hord
  have hW' : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 11 d0 = k.W := by rw [hW]; exact hW0
  have hnd : k.base.toList.Nodup := by rw [hbase]; exact hnd0
  have hg : BindA 3850 12 k.gens E0.ng E0.G := by rw [hgens]; exact bindG
  have hK : CFSG.KC.BfsPin.keysSK 3850 12 k.base.toList E0.N E0.T E0.SK = true := by
    rw [hbase]; exact E0.keys
  have hr : relsK 3850 12 3 C0.BP (XC.F 0) 6 k.rels = true := by rw [hrels]; exact rels0
  have ht : allN (rcnt (C0.LR 0)) (ptailBranchK 3850 12 C0.LR C0.TR C0.BP (XC.F 0)
      (pw 3850 12 (XC.F 0)) k.rels E0.N E0.T 6) = true := by rw [hrels]; exact tail0
  have hc : ∀ pts : Array (Array ℕ), pts.size = E0.N →
      (∀ i < E0.N, pts[i]! = unpack 3850 12 (E0.T i)) → critOK 3850 pts k.card k.crit = true := by
    rw [hcard, hcrit]; exact crit0
  refine caseOK_of_card szOK' hn (by rw [hDA]; exact hA 0 (by norm_num))
    (by rw [hDB]; exact hA 1 (by norm_num))
    (pS 0 (by norm_num)) (pS 1 (by norm_num)) rfl x0.1 x0.2 hb perm0
    C0.head C0.hl hor hW' (Nat.beq_refl _) (Nat.beq_refl _) (by norm_num) hnd (by norm_num)
    hg comm0 (fun j hj => ?_) E0.ok hK hE0p hN hr ht hc
  rw [Nat.eq_of_beq_eq_true n0.2.2.1] at hj
  exact siftG j hj

theorem trans_ok : transOK2 4 3850 hsS3Trans hsS3CaseX hsS3Lines hsS3Rec
    (rawLevels 3850 hsS3C0S hsS3C0Base) hsS3C0Base = true :=
  transOK2_of szOK' bindH bindX (fun c hc => by
      have : c = 0 := by omega
      subst this
      exact x0.1) bindL (Orb.allN_iff.1 pL) (by decide +kernel)
    (fun j hj => by rw [bindH.2 j hj]; exact siftL (siftH j hj)) trans

theorem lines_ok : linesOK3 3 9 4 3850 hsS3QGens hsS3C0Base.toList
    (enumBfs 3850 hsS3QGens hsS3C0Base.toList (9 + 1)) hsS3Lines = true := by
  obtain ⟨h1, h2, h3⟩ := enumQ
  rw [Nat.eq_of_beq_eq_true n0.1] at h2 h3
  have hl := lines
  rw [Nat.eq_of_beq_eq_true n0.1] at hl
  exact linesOK3_of szOK' h1 h2 h3 (fun i hi => Orb.allN_iff.1 hEQp i
    (by rw [Nat.eq_of_beq_eq_true n0.1]; exact hi)) bindL hl

theorem hs_check {D : Data} (hn : D.n = 3850) (hQ : D.QGens = hsS3QGens)
    (hord' : D.ord = 44352000) (hk3 : D.k3 = 2) (hm3 : D.m3 = 4928000) (hN3 : D.N3 = 9)
    (hl : D.lines = hsS3Lines) (ht : D.trans = hsS3Trans) (hr : D.recs = hsS3Rec)
    (hx : D.caseX = hsS3CaseX) (hsz : D.cases.size = 1)
    (hc : caseOK D D.cases[0]! (unpack 3850 12 (XC.F 0)) = true)
    (hS : D.cases[0]!.S = hsS3C0S) (hbase : D.cases[0]!.base = hsS3C0Base) :
    check D = true := by
  have hlsz : hsS3Lines.size = 4 := bindL.1
  have hxsz : hsS3CaseX.size = 1 := bindX.1
  have hqsz : hsS3QGens.size = 2 := bindQ0.1
  refine check_of (by omega) ?_ (by rw [hord', hk3, hm3]; norm_num) (by rw [hm3]; decide)
    (by rw [hN3, hk3]; norm_num) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hn, hS, hbase, lev, hord']
    exact Nat.eq_of_beq_eq_true orb0
  · rw [hn, hQ, hN3, hl, hbase, hlsz]
    exact lines_ok
  · intro l hl'
    rw [hQ, hqsz] at hl'
    rw [hn, hS, hbase, hQ, bindQ0.2 l hl']
    exact siftL (siftQ l hl')
  · rw [hn, hS, hbase, hl, ht, hx, hr, hlsz]
    exact trans_ok
  · intro j hj
    rw [hsz, hr]
    rw [hl, hlsz] at hj
    interval_cases j <;> decide
  · rw [hx, hsz, hxsz]
  · intro c hcl
    rw [hsz] at hcl
    have : c = 0 := by omega
    subst this
    rw [hx, bindX.2 0 (by norm_num)]
    exact hc

theorem e_n : hsS3Data.n = 3850 := by simp only [hsS3Data]
theorem e_Q : hsS3Data.QGens = hsS3QGens := by simp only [hsS3Data]
theorem e_ord : hsS3Data.ord = 44352000 := by simp only [hsS3Data]
theorem e_k3 : hsS3Data.k3 = 2 := by simp only [hsS3Data]
theorem e_m3 : hsS3Data.m3 = 4928000 := by simp only [hsS3Data]
theorem e_N3 : hsS3Data.N3 = 9 := by simp only [hsS3Data]
theorem e_l : hsS3Data.lines = hsS3Lines := by simp only [hsS3Data]
theorem e_t : hsS3Data.trans = hsS3Trans := by simp only [hsS3Data]
theorem e_r : hsS3Data.recs = hsS3Rec := by simp only [hsS3Data]
theorem e_x : hsS3Data.caseX = hsS3CaseX := by simp only [hsS3Data]
theorem e_sz : hsS3Data.cases.size = 1 := by
  simp only [hsS3Data, List.size_toArray, List.length_cons, List.length_nil]
theorem e_A : hsS3Data.A = CFSG.Sporadic.Schreier.hsStrongArrs[0]! := by simp only [hsS3Data]
theorem e_B : hsS3Data.B = CFSG.Sporadic.Schreier.hsStrongArrs[1]! := by simp only [hsS3Data]
theorem e_c : hsS3Data.cases[0]! = (⟨hsS3C0S, hsS3C0W, hsS3C0Base, hsS3C0Rels, hsS3C0Gens, 360,
    ⟨1, 0, 0, [2, 5], [1]⟩⟩ : Case) := by simp only [hsS3Data]; exact getElem!_pos _ 0 (by simp)

theorem hs_ok : check hsS3Data = true := by
  refine hs_check e_n e_Q e_ord e_k3 e_m3 e_N3 e_l e_t e_r e_x e_sz ?_ ?_ ?_
  · rw [e_c]
    exact case_of e_n e_A e_B (by simp only) (by simp only) (by simp only) (by simp only)
      (by simp only) (by simp only) (by simp only)
  · simp only [e_c]
  · simp only [e_c]

end CertificateChecks.KernelB3S3.HS

end
