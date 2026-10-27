module

public import Certificates.Kernel.B3S3.M11
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelB3S3.M11

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.RankThree.PartTwo.KFacts.K426

theorem binds0 : Binds 11 4 C0.S 6 11 C0.BP m11S3C0S m11S3C0Base :=
  ⟨by norm_num, by norm_num, by norm_num, by decide +kernel, fun j hj => arrBind_sound (bS j hj),
    by decide +kernel, bget0⟩

theorem bindQ : BindA 11 4 m11S3QGens EQ.ng EQ.G := by
  refine ⟨by rw [Nat.eq_of_beq_eq_true n0.2.2.2]; decide +kernel, fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true n0.2.2.2] at hj
  rw [Nat.eq_of_beq_eq_true (bQE j hj)]
  exact arrBind_sound (bQ j hj)

theorem pQE : ∀ j < EQ.ng, permB 11 4 (EQ.G j) = true := by
  intro j hj
  rw [Nat.eq_of_beq_eq_true n0.2.2.2] at hj
  rw [Nat.eq_of_beq_eq_true (bQE j hj)]
  exact Orb.allN_iff.1 pQ j hj

theorem bindL : BindA 11 4 m11S3Lines 4 LX :=
  ⟨by decide +kernel, fun j hj => arrBind_sound (bL j hj)⟩

theorem bindH : BindA 11 4 m11S3Trans 4 H :=
  ⟨by decide +kernel, fun j hj => arrBind_sound (bH j hj)⟩

theorem bindX : BindA 11 4 m11S3CaseX 1 XC := by
  refine ⟨by decide +kernel, fun j hj => ?_⟩
  have : j = 0 := by omega
  subst this
  exact arrBind_sound bX

theorem bindG : BindA 11 4 m11S3C0Gens E0.ng E0.G := by
  refine ⟨by rw [Nat.eq_of_beq_eq_true n0.2.2.1]; decide +kernel, fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true n0.2.2.1] at hj
  exact arrBind_sound (bG j hj)

theorem enumQ : enumOK 11 m11S3QGens m11S3C0Base.toList
      (enumBfs 11 m11S3QGens m11S3C0Base.toList (9 + 1)) = true ∧
    (enumBfs 11 m11S3QGens m11S3C0Base.toList (9 + 1)).pts.size = EQ.N ∧
    ∀ i < EQ.N, (enumBfs 11 m11S3QGens m11S3C0Base.toList (9 + 1)).pts[i]! =
      unpack 11 4 (EQ.T i) :=
  enum_of bindQ pQE EQ.ok (mem_base_lt binds0 C0.hl) EQ.keys
    (by rw [Nat.eq_of_beq_eq_true n0.1]; omega)

theorem hNS0 : 11 ≤ C0.NS * 11 := by decide +kernel

theorem hW0 : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 6 d0 = m11S3C0W := by decide +kernel

theorem hnd0 : m11S3C0Base.toList.Nodup := by decide +kernel

theorem lev : rawOrbitSizes 11 m11S3C0S m11S3C0Base = (List.range 11).map fun i => rcnt (C0.LR i) :=
  rawOrbitSizesK_sound binds0 perm0 C0.hl

theorem siftL {G : ℕ}
    (h : Nat.beq (Nat.shiftRight G (11 * 4)) 0 = true ∧
      allN 11 (fun t => Nat.blt (pg 4 (mask 4) G t) 11) = true ∧
      siftK 11 4 (mask 4) (11 * 4) (pidn 11 4) C0.LR C0.TRI C0.BP 11 0 G = true) :
    siftA 11 (rawLevels 11 m11S3C0S m11S3C0Base) m11S3C0Base 0 (unpack 11 4 G) = true :=
  siftA_of binds0 perm0 C0.hl h

theorem case_of {D : Data} {k : Case} (hn : D.n = 11) (hA : D.A = m11S3A) (hB : D.B = m11S3B)
    (hS : k.S = m11S3C0S) (hW : k.W = m11S3C0W) (hbase : k.base = m11S3C0Base)
    (hrels : k.rels = m11S3C0Rels) (hgens : k.gens = m11S3C0Gens) (hcard : k.card = 18)
    (hcrit : ∀ pts : Array (Array ℕ), pts.size = 18 →
      (∀ i < 18, pts[i]! = unpack 11 4 (E0.T i)) → critOK 11 pts 18 k.crit = true) :
    caseOK D k m11S3CaseX[0]! = true := by
  obtain ⟨S, W, base, rels, gens, card, crit⟩ := k
  simp only at hS hW hbase hrels hgens hcard hcrit
  subst hS hW hbase hrels hgens hcard
  have hN := Nat.eq_of_beq_eq_true n0.2.1
  refine caseOK_of szOK' hn (by rw [hA]; exact arrBind_sound bA)
    (by rw [hB]; exact arrBind_sound bB) pAB.1 pAB.2 (arrBind_sound bX) x0.1 x0.2
    binds0 perm0 C0.head C0.hl hNS0 C0.hs hW0 head0.1 head0.2 (by norm_num) hnd0 (by norm_num)
    bindG
    comm0 (fun j hj => ?_) E0.ok E0.keys E0.perm hN rels0 ?_ (by rw [hN]; exact hcrit)
  · rw [Nat.eq_of_beq_eq_true n0.2.2.1] at hj
    exact siftG j hj
  · rw [Nat.eq_of_beq_eq_true rc0]
    exact tail0

theorem trans_ok : transOK2 4 11 m11S3Trans m11S3CaseX m11S3Lines m11S3Rec
    (rawLevels 11 m11S3C0S m11S3C0Base) m11S3C0Base = true :=
  transOK2_of szOK' bindH bindX (fun c hc => by
      have : c = 0 := by omega
      subst this
      exact x0.1) bindL (Orb.allN_iff.1 pL) (by decide +kernel)
    (fun j hj => by rw [bindH.2 j hj]; exact siftL (siftH j hj)) trans

theorem lines_ok : linesOK3 3 9 4 11 m11S3QGens m11S3C0Base.toList
    (enumBfs 11 m11S3QGens m11S3C0Base.toList (9 + 1)) m11S3Lines = true := by
  obtain ⟨h1, h2, h3⟩ := enumQ
  rw [Nat.eq_of_beq_eq_true n0.1] at h2 h3
  have hl := lines
  rw [Nat.eq_of_beq_eq_true n0.1] at hl
  exact linesOK3_of szOK' h1 h2 h3 (fun i hi => Orb.allN_iff.1 EQ.perm i
    (by rw [Nat.eq_of_beq_eq_true n0.1]; exact hi)) bindL hl

theorem m11_check {D : Data} (hn : D.n = 11) (hA : D.A = m11S3A) (hB : D.B = m11S3B)
    (hQ : D.QGens = m11S3QGens) (hord : D.ord = 7920) (hk3 : D.k3 = 2) (hm3 : D.m3 = 880)
    (hN3 : D.N3 = 9) (hl : D.lines = m11S3Lines) (ht : D.trans = m11S3Trans)
    (hr : D.recs = m11S3Rec) (hx : D.caseX = m11S3CaseX) (hsz : D.cases.size = 1)
    (hc : caseOK D D.cases[0]! m11S3CaseX[0]! = true)
    (hS : D.cases[0]!.S = m11S3C0S) (hbase : D.cases[0]!.base = m11S3C0Base) :
    check D = true := by
  refine check_of (by omega) ?_ (by rw [hord, hk3, hm3]; norm_num) (by rw [hm3]; decide)
    (by rw [hN3, hk3]; norm_num) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hn, hS, hbase, lev, hord]
    exact Nat.eq_of_beq_eq_true orb0
  · rw [hn, hQ, hN3, hl, hbase]
    exact lines_ok
  · intro l hl'
    rw [hQ] at hl' ⊢
    have hl2 : l < 2 := by
      rw [bindQ.1, Nat.eq_of_beq_eq_true n0.2.2.2] at hl'
      exact hl'
    rw [hn, hS, hbase, bindQ.2 l (by rw [Nat.eq_of_beq_eq_true n0.2.2.2]; exact hl2)]
    exact siftL (siftQ l hl2)
  · rw [hn, hS, hbase, hl, ht, hx, hr]
    exact trans_ok
  · intro j hj
    rw [hsz, hr]
    rw [hl] at hj
    have : j < 4 := by
      rw [bindL.1] at hj
      exact hj
    interval_cases j <;> decide
  · rw [hx, hsz]
    decide +kernel
  · intro c hcl
    rw [hsz] at hcl
    have : c = 0 := by omega
    subst this
    rw [hx]
    exact hc

theorem m11_ok : check m11S3Data = true :=
  m11_check rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (case_of rfl rfl rfl rfl rfl rfl rfl rfl rfl fun _ _ _ => rfl) rfl rfl

theorem m11O_ok : check m11S3DataO = true :=
  m11_check rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (case_of rfl rfl rfl rfl rfl rfl rfl rfl rfl fun pts hs hp => by
      change (convProdOK 11 pts [2] [1] &&
        (Nat.primeFactorsList 18).all fun q => q == 3 || [2].contains q) = true
      rw [Bool.and_eq_true]
      refine ⟨convProdOK_of szOK' (hs.trans (Nat.eq_of_beq_eq_true n0.2.1).symm)
        (fun i hi => hp i (by rwa [Nat.eq_of_beq_eq_true n0.2.1] at hi))
        (fun i hi => Orb.allN_iff.1 E0.perm i hi) conv0,
        by simp only [Nat.primeFactorsList_ofNat]; decide⟩) rfl rfl

end CertificateChecks.KernelB3S3.M11

end
