
module

public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphBase
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Base

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0 wAct_mul)

@[expose] def cPi
    (s : Shat) : Set CVert :=
  {v | ∃ k : Shat, (k : Dfull) ∈ Jhat ∧ v = cvOf (k * s)}

abbrev cPi0 : Set CVert := cPi 1

@[expose] def jhatS (k : Jhat) : Shat := ⟨k, Jhat_le_Shat k.2⟩

theorem jhatS_mem_cPi0
    (k : Jhat) : cvOf (jhatS k) ∈ cPi0 := ⟨jhatS k, k.2, by rw [mul_one]⟩

@[expose] def piPt
    (k : Jhat) : Unitary.OmegaPt :=
  ⟨wAct v0 (jhatToKv0 k) Unitary.sigmaW, ⟨jhatToKv0 k, rfl⟩⟩

@[expose] def cpsi
    (v : cPi0) : Unitary.OmegaPt :=
  piPt ⟨(v.2.choose : Dfull), v.2.choose_spec.1⟩

end CFSG.Monster.B.TwoA.Amalgam
