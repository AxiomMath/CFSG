module

public import Certificates.Data.Holder1711.Om1Check
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711OmGen
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscR10QVm
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.ClassicalInvolution.Asc77.AscT7K4
public import CFSG.ClassicalInvolution.Asc77.AscThmABasic
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwinDefs
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3CPSix67
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Facts

open CFSG.Monster.B.Co2
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check

@[expose] noncomputable def E (w : List ℕ) : Equiv.Perm (Fin 240) :=
  permOfArr 240 (wA (reflTab ()) w)

@[expose] noncomputable def G (ws : List (List ℕ)) : Subgroup (Equiv.Perm (Fin 240)) :=
  Subgroup.closure (E '' {w | w ∈ ws})

@[expose] noncomputable def Wp : Subgroup (Equiv.Perm (Fin 240)) :=
  Subgroup.closure (E '' {w | wordOK w = true})

@[expose] noncomputable def e (m : ℕ) : Equiv.Perm (Fin 240) := permOfArr 240 (eA m)

@[expose] noncomputable def t : Equiv.Perm (Fin 240) := e 15

@[expose] noncomputable def ta : Equiv.Perm (Fin 240) := e 3

@[expose] noncomputable def tb : Equiv.Perm (Fin 240) := e 252

@[expose] noncomputable def tc : Equiv.Perm (Fin 240) := e 23

@[expose] noncomputable def z : Equiv.Perm (Fin 240) := permOfArr 240 zA

@[expose] noncomputable def R : Subgroup (Equiv.Perm (Fin 240)) :=
  Subgroup.closure {E wI0, E wJ0}

@[expose] noncomputable def i0' : Equiv.Perm (Fin 240) := E wS1 * E wI0 * (E wS1)⁻¹

@[expose] noncomputable def j0' : Equiv.Perm (Fin 240) := E wS1 * E wJ0 * (E wS1)⁻¹

@[expose] noncomputable def R' : Subgroup (Equiv.Perm (Fin 240)) := Subgroup.closure {i0', j0'}

@[expose] def neg (m : ℕ) : Set (Fin 240) := {i | e m i = z i}

@[expose] def orb (H : Subgroup (Equiv.Perm (Fin 240))) (S : Set (Fin 240)) :
    Set (Set (Fin 240)) :=
  {S' | ∃ g ∈ H, S' = g '' S}

@[expose] def D : Set (Equiv.Perm (Fin 240)) :=
  {d | ∃ g ∈ Wp, d = g * t * g⁻¹ ∧ d ≠ t ∧ d ≠ t * z}

@[expose] def TwinFail (x y s : Equiv.Perm (Fin 240)) : Prop :=
  (∃ g ∈ ({x, y} : Set (Equiv.Perm (Fin 240))), ∀ k < 4,
      s * g * s⁻¹ ≠ x ^ k ∧ s * g * s⁻¹ ≠ y * x ^ k) ∧
    ∃ a ∈ ({x, y} : Set (Equiv.Perm (Fin 240))), ∃ b ∈ ({x, y} : Set (Equiv.Perm (Fin 240))),
      a * (s * b * s⁻¹) ≠ (s * b * s⁻¹) * a

@[expose] noncomputable def tup (s : Equiv.Perm (Fin 240)) :
    Equiv.Perm (Fin 240) × Equiv.Perm (Fin 240) × Equiv.Perm (Fin 240) × Equiv.Perm (Fin 240) :=
  (s * E wI0 * s⁻¹, s * E wJ0 * s⁻¹, s * i0' * s⁻¹, s * j0' * s⁻¹)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Facts

end
