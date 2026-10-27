module

public import Certificates.Kernel.B3S3.M22
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelB3S3.M22

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.RankThree.PartTwo.KFacts.K426

theorem binds0 : Binds 22 5 C0.S 11 22 C0.BP m22S3C0S m22S3C0Base :=
  ⟨by norm_num, by norm_num, by norm_num, by decide +kernel, fun j hj => arrBind_sound (bS j hj),
    by decide +kernel, bget0⟩

theorem bindQ : BindA 22 5 m22S3QGens EQ.ng EQ.G := by
  refine ⟨by rw [Nat.eq_of_beq_eq_true n0.2.2.2]; decide +kernel, fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true n0.2.2.2] at hj
  rw [Nat.eq_of_beq_eq_true (bQE j hj)]
  exact arrBind_sound (bQ j hj)

theorem pQE : ∀ j < EQ.ng, permB 22 5 (EQ.G j) = true := by
  intro j hj
  rw [Nat.eq_of_beq_eq_true n0.2.2.2] at hj
  rw [Nat.eq_of_beq_eq_true (bQE j hj)]
  exact Orb.allN_iff.1 pQ j hj

theorem bindL : BindA 22 5 m22S3Lines 4 LX :=
  ⟨by decide +kernel, fun j hj => arrBind_sound (bL j hj)⟩

theorem bindH : BindA 22 5 m22S3Trans 4 H :=
  ⟨by decide +kernel, fun j hj => arrBind_sound (bH j hj)⟩

theorem bindX : BindA 22 5 m22S3CaseX 1 XC := by
  refine ⟨by decide +kernel, fun j hj => ?_⟩
  have : j = 0 := by omega
  subst this
  exact arrBind_sound bX

theorem bindG : BindA 22 5 m22S3C0Gens E0.ng E0.G := by
  refine ⟨by rw [Nat.eq_of_beq_eq_true n0.2.2.1]; decide +kernel, fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true n0.2.2.1] at hj
  exact arrBind_sound (bG j hj)

theorem enumQ : enumOK 22 m22S3QGens m22S3C0Base.toList
      (enumBfs 22 m22S3QGens m22S3C0Base.toList (9 + 1)) = true ∧
    (enumBfs 22 m22S3QGens m22S3C0Base.toList (9 + 1)).pts.size = EQ.N ∧
    ∀ i < EQ.N, (enumBfs 22 m22S3QGens m22S3C0Base.toList (9 + 1)).pts[i]! =
      unpack 22 5 (EQ.T i) :=
  enum_of bindQ pQE EQ.ok (mem_base_lt binds0 C0.hl) EQ.keys
    (by rw [Nat.eq_of_beq_eq_true n0.1]; omega)

theorem hNS0 : 22 ≤ C0.NS * 22 := by decide +kernel

theorem hW0 : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 11 d0 = m22S3C0W := by decide +kernel

theorem hnd0 : m22S3C0Base.toList.Nodup := by decide +kernel

theorem lev : rawOrbitSizes 22 m22S3C0S m22S3C0Base = (List.range 22).map fun i => rcnt (C0.LR i) :=
  rawOrbitSizesK_sound binds0 perm0 C0.hl

theorem siftL {G : ℕ}
    (h : Nat.beq (Nat.shiftRight G (22 * 5)) 0 = true ∧
      allN 22 (fun t => Nat.blt (pg 5 (mask 5) G t) 22) = true ∧
      siftK 22 5 (mask 5) (22 * 5) (pidn 22 5) C0.LR C0.TRI C0.BP 22 0 G = true) :
    siftA 22 (rawLevels 22 m22S3C0S m22S3C0Base) m22S3C0Base 0 (unpack 22 5 G) = true :=
  siftA_of binds0 perm0 C0.hl h

theorem case_ok : caseOK m22S3Data m22S3Data.cases[0]! m22S3CaseX[0]! = true := by
  have hN := Nat.eq_of_beq_eq_true n0.2.1
  refine caseOK_of szOK' (n := 22) rfl (arrBind_sound bA) (arrBind_sound bB) pAB.1 pAB.2
    (arrBind_sound bX) x0.1 x0.2 binds0 perm0 C0.head C0.hl hNS0 C0.hs hW0 head0.1 head0.2
    (by norm_num) hnd0 (by norm_num) bindG comm0 (fun j hj => ?_) E0.ok E0.keys E0.perm hN rels0
    ?_ (fun _ _ _ => rfl)
  · rw [Nat.eq_of_beq_eq_true n0.2.2.1] at hj
    exact siftG j hj
  · rw [Nat.eq_of_beq_eq_true rc0]
    exact tail0

theorem trans_ok : transOK2 4 22 m22S3Trans m22S3CaseX m22S3Lines m22S3Rec
    (rawLevels 22 m22S3C0S m22S3C0Base) m22S3C0Base = true :=
  transOK2_of szOK' bindH bindX (fun c hc => by
      have : c = 0 := by omega
      subst this
      exact x0.1) bindL (Orb.allN_iff.1 pL) (by decide +kernel)
    (fun j hj => by rw [bindH.2 j hj]; exact siftL (siftH j hj)) trans

theorem lines_ok : linesOK3 3 9 4 22 m22S3QGens m22S3C0Base.toList
    (enumBfs 22 m22S3QGens m22S3C0Base.toList (9 + 1)) m22S3Lines = true := by
  obtain ⟨h1, h2, h3⟩ := enumQ
  rw [Nat.eq_of_beq_eq_true n0.1] at h2 h3
  have hl := lines
  rw [Nat.eq_of_beq_eq_true n0.1] at hl
  exact linesOK3_of szOK' h1 h2 h3 (fun i hi => Orb.allN_iff.1 EQ.perm i
    (by rw [Nat.eq_of_beq_eq_true n0.1]; exact hi)) bindL hl

theorem m22_ok : check m22S3Data = true := by
  refine check_of (by decide) ?_ (by change 443520 = 3 ^ 2 * 49280; norm_num) (by decide)
    (by change 9 = 3 ^ 2; norm_num) lines_ok ?_ trans_ok ?_ (by decide +kernel) ?_
  · change (rawOrbitSizes 22 m22S3C0S m22S3C0Base).prod = 443520
    rw [lev]
    exact Nat.eq_of_beq_eq_true orb0
  · intro l hl'
    change l < m22S3QGens.size at hl'
    have hl2 : l < 2 := by
      rw [bindQ.1, Nat.eq_of_beq_eq_true n0.2.2.2] at hl'
      exact hl'
    change siftA 22 (rawLevels 22 m22S3C0S m22S3C0Base) m22S3C0Base 0 m22S3QGens[l]! = true
    rw [bindQ.2 l (by rw [Nat.eq_of_beq_eq_true n0.2.2.2]; exact hl2)]
    exact siftL (siftQ l hl2)
  · intro j hj
    change j < m22S3Lines.size at hj
    have : j < 4 := by
      rw [bindL.1] at hj
      exact hj
    interval_cases j <;> decide
  · intro c hcl
    have : c = 0 := by
      have : c < 1 := hcl
      omega
    subst this
    exact case_ok

end CertificateChecks.KernelB3S3.M22

end
