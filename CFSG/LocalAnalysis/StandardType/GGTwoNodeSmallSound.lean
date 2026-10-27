module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Check
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallVerifyK
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallVerifyT
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallVerifyW

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem verify_elim {P : Pt}
    [Fact P.p.Prime] {w : Witness} (h : verify P w = true) {C : Prop}
    (hK : P.FrameViolation → C) (hT : (∃ g ∈ P.group, IsTransv g) → C)
    (hO : P.bound < Nat.card P.group → C) (hW : CFSG.StandardType.ZS.LinWeyl P.p P.group → C) : C := by
  cases w with
  | kernel v =>
    simp only [verify] at h
    exact hK (verifyK_sound h)
  | transv t =>
    simp only [verify, Bool.and_eq_true] at h
    exact hT (verifyT_sound (wfCheck_sound h.1) h.2)
  | order o =>
    simp only [verify, Bool.and_eq_true] at h
    exact hO (verifyO_sound (wfCheck_sound h.1) h.2)
  | weyl c =>
    simp only [verify, Bool.and_eq_true] at h
    exact hW (verifyW_sound (wfCheck_sound h.1) h.2)

theorem check1_elim {P : Pt}
    [Fact P.p.Prime] (h : check1 P = true) {C : Prop}
    (hK : P.FrameViolation → C) (hT : (∃ g ∈ P.group, IsTransv g) → C)
    (hO : P.bound < Nat.card P.group → C) (hW : CFSG.StandardType.ZS.LinWeyl P.p P.group → C) : C := by
  unfold check1 at h
  split at h
  · exact verify_elim h hK hT hO hW
  · exact absurd h (by simp)

end CFSG.TwoNodeSmall
