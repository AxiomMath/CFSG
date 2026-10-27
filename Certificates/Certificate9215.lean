module

public import CFSG.Sporadic.Bridge.M24SurjInputs
import Certificates.Kernel.Sporadic.MathieuRels
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu.TwentyFour

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.M24 in
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native TauCeti in
open CFSG.Sporadic.Mathieu (m24a m24b rep_m24a rep_m24b m24_eq card_M24 closure_pair_eq_top) in
open CFSG.Sporadic.Mathieu.Native (m24Data) in
theorem certificate9215 : relCheck 24 m24Data.tA m24Data.tA CFSG.Sporadic.Bridge.M24.tabBi m24Data.tB
      Sporadic.m24Presentation.relatorLetters = true := KernelSpor.MathieuRels.m24

end Certificates
