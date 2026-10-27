module

public import CFSG.GH74.GLS.C3.Layer2.L5C4b
public import CFSG.GH74.GLS.C3.Layer2.L5C4cInputs
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
meta import CFSG.GH74.GLS.C3.Layer2.L5C4a
meta import CFSG.GH74.GLS.C3.Layer2.L5C4b
meta import CFSG.GH74.GLS.C3.Layer2.L5C4cInputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.GH74.GLS.C3.Layer2.L5.Rec1
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5064

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.GH74.GLS.C3.Layer2.L5.Rec1
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

private theorem Dg_bit_chk_0 : (List.finRange 8).all (fun j => (List.finRange 16).all fun v =>
    (List.finRange 4).all fun c =>
      decide ((Dg j v).val.testBit c.val =
        xor (xor (xor (Mj j c.val 0 && v.val.testBit 0) (Mj j c.val 1 && v.val.testBit 1))
          (Mj j c.val 2 && v.val.testBit 2)) (Mj j c.val 3 && v.val.testBit 3))) = true := by
  decide +kernel

private theorem fsCheck_cc1_1 : fsCheck cc1 eFdata bFdata = true := by
  decide +kernel

end CertificateChecks.Batch5064

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open CFSG.GH74.GLS.C3.Layer2.L5.Rec1 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5064 : ((List.finRange 8).all (fun j => (List.finRange 16).all fun v =>
    (List.finRange 4).all fun c =>
      decide ((Dg j v).val.testBit c.val =
        xor (xor (xor (Mj j c.val 0 && v.val.testBit 0) (Mj j c.val 1 && v.val.testBit 1))
          (Mj j c.val 2 && v.val.testBit 2)) (Mj j c.val 3 && v.val.testBit 3))) = true)
    ∧ (fsCheck cc1 eFdata bFdata = true) := by
  exact ⟨CertificateChecks.Batch5064.Dg_bit_chk_0, CertificateChecks.Batch5064.fsCheck_cc1_1⟩

end Certificates
