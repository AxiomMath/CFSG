module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GH74.E2.SD16CertBase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Certificates.Certificate5018Base

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

open Certificates in
open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open Subgroup in
theorem check5010 : ∃ z : SD16M, z ≠ 1 ∧ z * z = 1 ∧ ∀ y : SD16M, y * z = z * y := by
  decide +kernel

end CertificateChecks.KernelCensus
