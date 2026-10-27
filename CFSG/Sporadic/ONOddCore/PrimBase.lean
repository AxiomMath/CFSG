
module

public import CFSG.Sporadic.ONOddCore.PrimCheckInputs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.Schreier.ONVectorOrder

@[expose] public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Certificates CFSG.Certificates.Native

theorem lineRegs_one :
    lineRegs 1 = (d0 * d1)⁻¹ * (d0 * (d0 * d1)) := by
  simp [lineRegs, runProgram, Data.subgroupProgram, lineRegs0, mul_assoc]

theorem lineRegs_two :
    lineRegs 2 = ((d0 * (d1 * d1)) * (d0 * (d1 * d1)))⁻¹ *
    (d1 * ((d0 * (d1 * d1)) * (d0 * (d1 * d1)))) := by
  simp [lineRegs, runProgram, Data.subgroupProgram, lineRegs0, mul_assoc]

theorem lineTabs_eq : lineTabs = lineOrbit := by
  rw [lineOrbit_def]
  rfl

theorem prep_dArr0 :
    PRep nL dArr0 d0 := fun j => by
  rw [dArr0, lineTabs_eq, natTab_getElem! (by rw [lparts.2.1]; exact j.isLt), ← l0_eq j.isLt,
    d0_apply]

theorem prep_dArr1 :
    PRep nL dArr1 d1 := fun j => by
  rw [dArr1, lineTabs_eq, natTab_getElem! (by rw [lparts.2.2.1]; exact j.isLt), ← l1_eq j.isLt,
    d1_apply]

end CFSG.Sporadic.ONOddCore
