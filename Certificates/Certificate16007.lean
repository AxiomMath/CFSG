module

public import CFSG.Monster.Existence.TwoPoint.Y433MInputs
public import Certificates.Certificate1011
public import Certificates.Certificate8955

public section

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.AxisCount CFSG.Monster.Griess
  CFSG.YGroups
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels powWord)
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

namespace CertificateChecks.Batch16007

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.AxisCount CFSG.Monster.Griess
  CFSG.YGroups
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels powWord)
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

private theorem y433M_square_mem_rels_0 : ∀ i < 10, [(i, true), (i, true)] ∈ rels := by
  decide +kernel

private theorem y433M_fiCox_mem_rels_aux_1 :
    ∀ i ∈ List.range 10, ∀ j ∈ List.range 10, i < j →
      powWord [(i, true), (j, true)] (fiCox i j) ∈ rels := by
  decide +kernel

end CertificateChecks.Batch16007

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.AxisCount CFSG.Monster.Griess
  CFSG.YGroups in
open CFSG.Sporadic.Bridge (wordProd) in
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels powWord) in
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons) in
theorem certificate16007 : (
    ∀ i < 10, [(i, true), (i, true)] ∈ rels
  ) ∧ (
    ∀ i ∈ List.range 10, ∀ j ∈ List.range 10, i < j →
      powWord [(i, true), (j, true)] (fiCox i j) ∈ rels
  ) := by
  exact ⟨CertificateChecks.Batch16007.y433M_square_mem_rels_0, CertificateChecks.Batch16007.y433M_fiCox_mem_rels_aux_1⟩

end Certificates
