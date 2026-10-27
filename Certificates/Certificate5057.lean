module

public import CFSG.GH74.GLS.C3.Layer2.L5C2e
public import CFSG.GH74.GLS.C3.Layer2.L5C2gInputs
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
meta import CFSG.GH74.GLS.C3.Layer2.L5A1
meta import CFSG.GH74.GLS.C3.Layer2.L5B2
meta import CFSG.GH74.GLS.C3.Layer2.L5C0
meta import CFSG.GH74.GLS.C3.Layer2.L5C2
meta import CFSG.GH74.GLS.C3.Layer2.L5C2a
meta import CFSG.GH74.GLS.C3.Layer2.L5C2b
meta import CFSG.GH74.GLS.C3.Layer2.L5C2c
meta import CFSG.GH74.GLS.C3.Layer2.L5C2d
meta import CFSG.GH74.GLS.C3.Layer2.L5C2e
meta import CFSG.GH74.GLS.C3.Layer2.L5C2gInputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.GH74.GLS.C3.Layer2.L5.Fus
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5057

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.GH74.GLS.C3.Layer2.L5.Fus
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

private theorem sh1WW_chk_0 : (sh1WW.all fun pw => decide (evalWG sh1Gens pw.2 = pw.1)) = true ∧
    sh1WW.length = 128 ∧ (sh1WW.map fun pw => codeP16 pw.1).Nodup := by
  decide +kernel

end CertificateChecks.Batch5057

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open CFSG.GH74.GLS.C3.Layer2.L5.Fus in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5057 : (sh1WW.all fun pw => decide (evalWG sh1Gens pw.2 = pw.1)) = true ∧
    sh1WW.length = 128 ∧ (sh1WW.map fun pw => codeP16 pw.1).Nodup := by
  exact CertificateChecks.Batch5057.sh1WW_chk_0

end Certificates
