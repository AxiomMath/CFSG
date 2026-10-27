module

public import Certificates.Kernel.B3S3.J2
public import Certificates.Kernel.GFR3.J2Facts
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelB3S3.J2

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.RankThree.PartTwo.KFacts.K426

theorem szOK' : szOK 315 9 = true := KernelGFR3.J2.szOK'

theorem binds1 : Binds 315 9 C1.S 9 5 C1.BP j2S3C1S j2S3C1Base :=
  ⟨by norm_num, by norm_num, by norm_num, by decide +kernel, fun j hj => arrBind_sound (bS1 j hj),
    by decide +kernel, bget1⟩

theorem hngQ : EQ.ng = 3 := Nat.eq_of_beq_eq_true n0.2.1

theorem hng1 : E1.ng = 3 := Nat.eq_of_beq_eq_true n0.2.2.2

theorem bindQ : BindA 315 9 j2S3QGens EQ.ng EQ.G := by
  refine ⟨by rw [hngQ]; decide +kernel, fun j hj => ?_⟩
  rw [hngQ] at hj
  rw [Nat.eq_of_beq_eq_true (bQE j hj)]
  exact arrBind_sound (bQ j hj)

theorem pQE : ∀ j < EQ.ng, permB 315 9 (EQ.G j) = true := by
  intro j hj
  rw [hngQ] at hj
  rw [Nat.eq_of_beq_eq_true (bQE j hj)]
  exact Orb.allN_iff.1 pQ j hj

theorem bindL : BindA 315 9 j2S3Lines 13 LX :=
  ⟨by decide +kernel, fun j hj => arrBind_sound (bL j hj)⟩

theorem bindH : BindA 315 9 j2S3Trans 13 H :=
  ⟨by decide +kernel, fun j hj => arrBind_sound (bH j hj)⟩

theorem hx0 : j2S3Data.caseX[0]! = unpack 315 9 (XC 0) := by
  have e : j2S3Data.caseX[0]! = j2ThreeGens[0]! := rfl
  rw [e, KernelGFR3.J2.bindG.2 0 (by rw [KernelGFR3.J2.hng]; norm_num),
    Nat.eq_of_beq_eq_true bX0]

theorem hx1 : j2S3Data.caseX[1]! = unpack 315 9 (XC 1) := by
  have e : j2S3Data.caseX[1]! = j2S3X1 := rfl
  rw [e]
  exact arrBind_sound bX1

theorem pX0 : permB 315 9 (XC 0) = true := by
  rw [Nat.eq_of_beq_eq_true bX0]
  exact KernelGFR3.J2.x0.1

theorem bindX : BindA 315 9 j2S3Data.caseX 2 XC := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · exact hx0
  · exact hx1

theorem bindG1 : BindA 315 9 j2S3C1Gens E1.ng E1.G := by
  refine ⟨by rw [hng1]; decide +kernel, fun j hj => ?_⟩
  rw [hng1] at hj
  exact arrBind_sound (bG1 j hj)

theorem enumQ : enumOK 315 j2S3QGens j2ThreeBaseArr.toList
      (enumBfs 315 j2S3QGens j2ThreeBaseArr.toList (27 + 1)) = true ∧
    (enumBfs 315 j2S3QGens j2ThreeBaseArr.toList (27 + 1)).pts.size = EQ.N ∧
    ∀ i < EQ.N, (enumBfs 315 j2S3QGens j2ThreeBaseArr.toList (27 + 1)).pts[i]! =
      unpack 315 9 (EQ.T i) :=
  enum_of bindQ pQE EQ.ok (mem_base_lt KernelGFR3.J2.binds KernelGFR3.J2.C.hl) EQ.keys
    (by rw [Nat.eq_of_beq_eq_true n0.1]; omega)

theorem hNS1 : 315 ≤ C1.NS * 63 := by decide +kernel

theorem hW1 : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 9 d1 = j2S3C1W := by decide +kernel

theorem hnd0 : j2ThreeBaseArr.toList.Nodup := by decide +kernel

theorem hnd1 : j2S3C1Base.toList.Nodup := by decide +kernel

theorem lev : rawOrbitSizes 315 j2ThreeArrs j2ThreeBaseArr =
    (List.range 7).map fun i => rcnt (KernelGFR3.J2.C.LR i) :=
  rawOrbitSizesK_sound KernelGFR3.J2.binds KernelGFR3.J2.perm KernelGFR3.J2.C.hl

theorem siftL {G : ℕ}
    (h : Nat.beq (Nat.shiftRight G (315 * 9)) 0 = true ∧
      allN 315 (fun t => Nat.blt (pg 9 (mask 9) G t) 315) = true ∧
      siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) KernelGFR3.J2.C.LR KernelGFR3.J2.C.TRI
        KernelGFR3.J2.C.BP 7 0 G = true) :
    siftA 315 (rawLevels 315 j2ThreeArrs j2ThreeBaseArr) j2ThreeBaseArr 0 (unpack 315 9 G) = true :=
  siftA_of KernelGFR3.J2.binds KernelGFR3.J2.perm KernelGFR3.J2.C.hl h

theorem crit0 (pts : Array (Array ℕ)) (hs : pts.size = KernelGFR3.J2.E.N)
    (hp : ∀ i < KernelGFR3.J2.E.N, pts[i]! = unpack 315 9 (KernelGFR3.J2.E.T i)) :
    critOK 315 pts 1080 ⟨1, 0, 0, [2, 5], [1, 2, 5]⟩ = true := by
  change (convProdOK 315 pts [2, 5] [1, 2, 5] &&
    (Nat.primeFactorsList 1080).all fun q => q == 3 || [2, 5].contains q) = true
  rw [Bool.and_eq_true]
  exact ⟨convProdOK_of szOK' hs hp (fun i hi => Orb.allN_iff.1 KernelGFR3.J2.E.perm i hi) conv0,
    by simp only [Nat.primeFactorsList_ofNat]; decide⟩

theorem crit1 (pts : Array (Array ℕ)) (_hs : pts.size = E1.N)
    (_hp : ∀ i < E1.N, pts[i]! = unpack 315 9 (E1.T i)) :
    critOK 315 pts 36 ⟨0, 2, 2, [], []⟩ = true := by
  unfold critOK
  rfl

theorem case0 : caseOK j2S3Data j2S3Data.cases[0]! j2S3Data.caseX[0]! = true := by
  have hN := KernelGFR3.J2.hN
  refine caseOK_of_orb szOK' (n := 315) rfl KernelGFR3.J2.hA KernelGFR3.J2.hB KernelGFR3.J2.pAB.1
    KernelGFR3.J2.pAB.2 hx0 pX0 (by rw [Nat.eq_of_beq_eq_true bX0]; exact KernelGFR3.J2.x0.2.1)
    KernelGFR3.J2.binds KernelGFR3.J2.perm KernelGFR3.J2.C.head KernelGFR3.J2.C.hl KernelGFR3.J2.hNS
    KernelGFR3.J2.C.hs KernelGFR3.J2.hW KernelGFR3.J2.head.1 KernelGFR3.J2.head.2 (by norm_num) hnd0
    (by norm_num) KernelGFR3.J2.bindG ?_ (fun j hj => ?_) KernelGFR3.J2.E.ok KernelGFR3.J2.E.keys
    KernelGFR3.J2.E.perm hN ?_ (NR := 1) (RB := KernelGFR3.J2.RB) (RI := KernelGFR3.J2.RI)
    (EK := KernelGFR3.J2.EK) (fun j hj => ?_) (fun q hq => ?_) crit0
  · rw [Nat.eq_of_beq_eq_true bX0]
    exact KernelGFR3.J2.comm
  · rw [KernelGFR3.J2.hng] at hj
    exact KernelGFR3.J2.siftG j hj
  · rw [Nat.eq_of_beq_eq_true bX0]
    exact KernelGFR3.J2.rels
  · obtain rfl : j = 0 := by omega
    rw [Nat.eq_of_beq_eq_true bX0]
    exact KernelGFR3.J2.rep0
  · rw [Nat.eq_of_beq_eq_true KernelGFR3.J2.rc] at hq
    rw [Nat.eq_of_beq_eq_true bX0]
    exact allN_spec KernelGFR3.J2.kOrb q hq

theorem case1 : caseOK j2S3Data j2S3Data.cases[1]! j2S3Data.caseX[1]! = true := by
  have hN := Nat.eq_of_beq_eq_true n0.2.2.1
  refine caseOK_of szOK' (n := 315) rfl KernelGFR3.J2.hA KernelGFR3.J2.hB KernelGFR3.J2.pAB.1
    KernelGFR3.J2.pAB.2 hx1 x1.1 x1.2 binds1 perm1 C1.head C1.hl hNS1 C1.hs hW1 head1.1 head1.2
    (by norm_num) hnd1 (by norm_num) bindG1 comm1 (fun j hj => ?_) E1.ok E1.keys E1.perm hN rels1
    ?_ crit1
  · rw [hng1] at hj
    exact siftG1 j hj
  · rw [Nat.eq_of_beq_eq_true rc1]
    exact tail1

theorem trans_ok : transOK2 13 315 j2S3Trans j2S3Data.caseX j2S3Lines j2S3Rec
    (rawLevels 315 j2ThreeArrs j2ThreeBaseArr) j2ThreeBaseArr = true :=
  transOK2_of szOK' bindH bindX (fun c hc => by
      interval_cases c
      · exact pX0
      · exact x1.1) bindL (Orb.allN_iff.1 pL) (by decide +kernel)
    (fun j hj => by rw [bindH.2 j hj]; exact siftL (siftH j hj)) trans

theorem lines_ok : linesOK3 3 27 13 315 j2S3QGens j2ThreeBaseArr.toList
    (enumBfs 315 j2S3QGens j2ThreeBaseArr.toList (27 + 1)) j2S3Lines = true := by
  obtain ⟨h1, h2, h3⟩ := enumQ
  rw [Nat.eq_of_beq_eq_true n0.1] at h2 h3
  have hl := lines
  rw [Nat.eq_of_beq_eq_true n0.1] at hl
  exact linesOK3_of szOK' h1 h2 h3 (fun i hi => Orb.allN_iff.1 EQ.perm i
    (by rw [Nat.eq_of_beq_eq_true n0.1]; exact hi)) bindL hl

theorem j2_ok : check j2S3Data = true := by
  refine check_of (by decide) ?_ (by change 604800 = 3 ^ 3 * 22400; norm_num) (by decide)
    (by change 27 = 3 ^ 3; norm_num) lines_ok ?_ trans_ok ?_ (by decide +kernel) ?_
  · change (rawOrbitSizes 315 j2ThreeArrs j2ThreeBaseArr).prod = 604800
    rw [lev, KernelGFR3.J2.orb]
    rfl
  · intro l hl'
    change l < j2S3QGens.size at hl'
    have hl3 : l < 3 := by
      rw [bindQ.1, hngQ] at hl'
      exact hl'
    change siftA 315 (rawLevels 315 j2ThreeArrs j2ThreeBaseArr) j2ThreeBaseArr 0 j2S3QGens[l]! = true
    rw [bindQ.2 l (by rw [hngQ]; exact hl3)]
    exact siftL (siftQ l hl3)
  · intro j hj
    change j < j2S3Lines.size at hj
    have : j < 13 := by
      rw [bindL.1] at hj
      exact hj
    interval_cases j <;> decide
  · intro c hcl
    have : c < 2 := hcl
    interval_cases c
    · exact case0
    · exact case1

end CertificateChecks.KernelB3S3.J2

end
