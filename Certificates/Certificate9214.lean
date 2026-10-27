module

public import CFSG.Sporadic.Bridge.M23SurjInputs
import Certificates.Kernel.Sporadic.MathieuRels

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.M23 in
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native TauCeti in
open CFSG.Sporadic.Schreier (m23GenA m23GenB m23_eq_closure m23_card) in
open CFSG.Sporadic.Mathieu (closure_pair_eq_top) in
theorem certificate9214 : relCheck 23 tabA tabA CFSG.Sporadic.Bridge.M23.tabBi tabB Sporadic.m23Presentation.relatorLetters =
      true := KernelSpor.MathieuRels.m23

end Certificates
