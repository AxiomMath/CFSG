module

public import CFSG.GH74.GLS.C3.Prop121.Card7Facts
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import CFSG.GH74.GLS.C3.Prop121.Card7H1Inputs
meta import Mathlib.Algebra.Group.End
meta import Mathlib.GroupTheory.Perm.Sign
meta import Mathlib.GroupTheory.Perm.Basic
meta import Mathlib.GroupTheory.Perm.Fin
meta import Mathlib.Logic.Equiv.Fin.Basic
meta import Mathlib.Logic.Equiv.Option
meta import Mathlib.Data.List.FinRange
meta import CFSG.GH74.GLS.C3.Prop121.Card7H1Inputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open CFSG.GH74.GLS.C3.Prop121.Card7
open CFSG.GH74.GLS.C3.Prop121.Card7.HC
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3

namespace CertificateChecks.Batch5080

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open CFSG.GH74.GLS.C3.Prop121.Card7
open CFSG.GH74.GLS.C3.Prop121.Card7.HC
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem HL_len_true_0 : decide (HL.length = 1152) = true := by
  decide +kernel

private theorem HL_nodup_true_1 : decide HL.Nodup = true := by
  decide +kernel

private theorem HL_hp_true_2 : (HL.all fun σ => decide (Hp σ)) = true := by
  decide +kernel

end CertificateChecks.Batch5080

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open CFSG.GH74.GLS.C3.Prop121.Card7 in
open CFSG.GH74.GLS.C3.Prop121.Card7.HC in
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3 in
theorem certificate5080 : (decide (HL.length = 1152) = true)
    ∧ (decide HL.Nodup = true)
    ∧ ((HL.all fun σ => decide (Hp σ)) = true) := by
  exact ⟨CertificateChecks.Batch5080.HL_len_true_0, CertificateChecks.Batch5080.HL_nodup_true_1, CertificateChecks.Batch5080.HL_hp_true_2⟩

end Certificates
