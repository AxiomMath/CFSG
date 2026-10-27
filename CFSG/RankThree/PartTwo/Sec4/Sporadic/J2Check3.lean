
module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3Base

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data3
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.Monster.B.Mathieu.SylowCore
public import Certificates.Data.CFSGNative.Schreier.Enum3
public meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data3
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public meta import CFSG.RankThree.Native.PermEnumeration
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import Certificates.Data.CFSGNative.Schreier.Enum3
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3Inputs
public import Certificates.Certificate8168
public import Certificates.Certificate8168Base

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

open CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Mathieu

theorem j2_check3 : j2Check3 = true :=
  Certificates.certificate8168

theorem j2_check3_parts :
    chkElts = true ∧ chkEnum = true ∧ chkClass = true ∧ chkNP = true ∧
    chkFix = true ∧ chkSix = true ∧ chkTen = true ∧ chkSets = true ∧ chkDelta = true := by
  have h := j2_check3
  simp only [j2Check3, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
