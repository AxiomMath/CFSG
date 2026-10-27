module

public import Certificates.Kernel.B3S3.M12
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelB3S3.M12

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.RankThree.PartTwo.KFacts.K426

theorem binds0 : Binds 12 4 C0.S 10 12 C0.BP m12S3C0S m12S3C0Base :=
  ⟨by norm_num, by norm_num, by norm_num, by decide +kernel, fun j hj => arrBind_sound (bS0 j hj),
    by decide +kernel, bget0⟩

theorem binds1 : Binds 12 4 C1.S 10 12 C1.BP m12S3C1S m12S3C1Base :=
  ⟨by norm_num, by norm_num, by norm_num, by decide +kernel, fun j hj => arrBind_sound (bS1 j hj),
    by decide +kernel, bget1⟩

theorem bindQ : BindA 12 4 m12S3QGens EQ.ng EQ.G := by
  refine ⟨by rw [Nat.eq_of_beq_eq_true n0.2.2.2.1]; decide +kernel, fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true n0.2.2.2.1] at hj
  rw [Nat.eq_of_beq_eq_true (bQE j hj)]
  exact arrBind_sound (bQ j hj)

theorem pQE : ∀ j < EQ.ng, permB 12 4 (EQ.G j) = true := by
  intro j hj
  rw [Nat.eq_of_beq_eq_true n0.2.2.2.1] at hj
  rw [Nat.eq_of_beq_eq_true (bQE j hj)]
  exact Orb.allN_iff.1 pQ j hj

theorem bindL : BindA 12 4 m12S3Lines 13 LX :=
  ⟨by decide +kernel, fun j hj => arrBind_sound (bL j hj)⟩

theorem bindH : BindA 12 4 m12S3Trans 13 H :=
  ⟨by decide +kernel, fun j hj => arrBind_sound (bH j hj)⟩

theorem bindX : BindA 12 4 m12S3CaseX 2 XC :=
  ⟨by decide +kernel, fun j hj => arrBind_sound (bX j hj)⟩

theorem bindG0 : BindA 12 4 m12S3C0Gens E0.ng E0.G := by
  refine ⟨by rw [Nat.eq_of_beq_eq_true n0.2.2.1]; decide +kernel, fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true n0.2.2.1] at hj
  exact arrBind_sound (bG0 j hj)

theorem bindG1 : BindA 12 4 m12S3C1Gens E1.ng E1.G := by
  refine ⟨by rw [Nat.eq_of_beq_eq_true n0.2.2.2.2.2]; decide +kernel, fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true n0.2.2.2.2.2] at hj
  exact arrBind_sound (bG1 j hj)

theorem enumQ : enumOK 12 m12S3QGens m12S3C0Base.toList
      (enumBfs 12 m12S3QGens m12S3C0Base.toList (27 + 1)) = true ∧
    (enumBfs 12 m12S3QGens m12S3C0Base.toList (27 + 1)).pts.size = EQ.N ∧
    ∀ i < EQ.N, (enumBfs 12 m12S3QGens m12S3C0Base.toList (27 + 1)).pts[i]! =
      unpack 12 4 (EQ.T i) :=
  enum_of bindQ pQE EQ.ok (mem_base_lt binds0 C0.hl) EQ.keys
    (by rw [Nat.eq_of_beq_eq_true n0.1]; omega)

theorem hNS0 : 12 ≤ C0.NS * 12 := by decide +kernel

theorem hNS1 : 12 ≤ C1.NS * 12 := by decide +kernel

theorem hW0 : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 10 d0 = m12S3C0W := by decide +kernel

theorem hW1 : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 10 d1 = m12S3C1W := by decide +kernel

theorem hnd0 : m12S3C0Base.toList.Nodup := by decide +kernel

theorem hnd1 : m12S3C1Base.toList.Nodup := by decide +kernel

theorem lev : rawOrbitSizes 12 m12S3C0S m12S3C0Base = (List.range 12).map fun i => rcnt (C0.LR i) :=
  rawOrbitSizesK_sound binds0 perm0 C0.hl

theorem siftL {G : ℕ}
    (h : Nat.beq (Nat.shiftRight G (12 * 4)) 0 = true ∧
      allN 12 (fun t => Nat.blt (pg 4 (mask 4) G t) 12) = true ∧
      siftK 12 4 (mask 4) (12 * 4) (pidn 12 4) C0.LR C0.TRI C0.BP 12 0 G = true) :
    siftA 12 (rawLevels 12 m12S3C0S m12S3C0Base) m12S3C0Base 0 (unpack 12 4 G) = true :=
  siftA_of binds0 perm0 C0.hl h

theorem case0 : caseOK m12S3Data m12S3Data.cases[0]! m12S3CaseX[0]! = true := by
  have hN := Nat.eq_of_beq_eq_true n0.2.1
  refine caseOK_of szOK' (n := 12) rfl (arrBind_sound bA) (arrBind_sound bB) pAB.1 pAB.2
    (arrBind_sound (bX 0 (by norm_num))) x0.1 x0.2 binds0 perm0 C0.head C0.hl hNS0 C0.hs hW0
    head0.1 head0.2 (by norm_num) hnd0 (by norm_num) bindG0 comm0 (fun j hj => ?_) E0.ok E0.keys
    E0.perm hN rels0 ?_ (fun _ _ _ => rfl)
  · rw [Nat.eq_of_beq_eq_true n0.2.2.1] at hj
    exact siftG0 j hj
  · rw [Nat.eq_of_beq_eq_true rc0]
    exact tail0

theorem case1 : caseOK m12S3Data m12S3Data.cases[1]! m12S3CaseX[1]! = true := by
  have hN := Nat.eq_of_beq_eq_true n0.2.2.2.2.1
  refine caseOK_of szOK' (n := 12) rfl (arrBind_sound bA) (arrBind_sound bB) pAB.1 pAB.2
    (arrBind_sound (bX 1 (by norm_num))) x1.1 x1.2 binds1 perm1 C1.head C1.hl hNS1 C1.hs hW1
    head1.1 head1.2 (by norm_num) hnd1 (by norm_num) bindG1 comm1 (fun j hj => ?_) E1.ok E1.keys
    E1.perm hN rels1 ?_ (fun _ _ _ => rfl)
  · rw [Nat.eq_of_beq_eq_true n0.2.2.2.2.2] at hj
    exact siftG1 j hj
  · rw [Nat.eq_of_beq_eq_true rc1]
    exact tail1

theorem trans_ok : transOK2 13 12 m12S3Trans m12S3CaseX m12S3Lines m12S3Rec
    (rawLevels 12 m12S3C0S m12S3C0Base) m12S3C0Base = true :=
  transOK2_of szOK' bindH bindX (fun c hc => by
      interval_cases c
      · exact x0.1
      · exact x1.1) bindL (Orb.allN_iff.1 pL) (by decide +kernel)
    (fun j hj => by rw [bindH.2 j hj]; exact siftL (siftH j hj)) trans

theorem lines_ok : linesOK3 3 27 13 12 m12S3QGens m12S3C0Base.toList
    (enumBfs 12 m12S3QGens m12S3C0Base.toList (27 + 1)) m12S3Lines = true := by
  obtain ⟨h1, h2, h3⟩ := enumQ
  rw [Nat.eq_of_beq_eq_true n0.1] at h2 h3
  have hl := lines
  rw [Nat.eq_of_beq_eq_true n0.1] at hl
  exact linesOK3_of szOK' h1 h2 h3 (fun i hi => Orb.allN_iff.1 EQ.perm i
    (by rw [Nat.eq_of_beq_eq_true n0.1]; exact hi)) bindL hl

theorem m12_ok : check m12S3Data = true := by
  refine check_of (by decide) ?_ (by change 95040 = 3 ^ 3 * 3520; norm_num) (by decide)
    (by change 27 = 3 ^ 3; norm_num) lines_ok ?_ trans_ok ?_ (by decide +kernel) ?_
  · change (rawOrbitSizes 12 m12S3C0S m12S3C0Base).prod = 95040
    rw [lev]
    exact Nat.eq_of_beq_eq_true orb0
  · intro l hl'
    change l < m12S3QGens.size at hl'
    have hl2 : l < 2 := by
      rw [bindQ.1, Nat.eq_of_beq_eq_true n0.2.2.2.1] at hl'
      exact hl'
    change siftA 12 (rawLevels 12 m12S3C0S m12S3C0Base) m12S3C0Base 0 m12S3QGens[l]! = true
    rw [bindQ.2 l (by rw [Nat.eq_of_beq_eq_true n0.2.2.2.1]; exact hl2)]
    exact siftL (siftQ l hl2)
  · intro j hj
    change j < m12S3Lines.size at hj
    have : j < 13 := by
      rw [bindL.1] at hj
      exact hj
    interval_cases j <;> decide
  · intro c hcl
    have : c < 2 := hcl
    interval_cases c
    · exact case0
    · exact case1

end CertificateChecks.KernelB3S3.M12

end
