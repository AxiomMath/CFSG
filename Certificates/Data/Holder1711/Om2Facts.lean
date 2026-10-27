module

public import Certificates.Data.Holder1711.Om2Check
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

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Facts

open CFSG.Monster.B.Co2
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab)

@[expose] noncomputable def E (w : List ℕ) : Equiv.Perm (Fin 480) :=
  permOfArr 480 (wY (lettersY (reflTab ())) w)

@[expose] noncomputable def G (ws : List (List ℕ)) : Subgroup (Equiv.Perm (Fin 480)) :=
  Subgroup.closure (E '' {w | w ∈ ws})

@[expose] noncomputable def Yg : Subgroup (Equiv.Perm (Fin 480)) :=
  G ((List.range 8).map fun i => [i])

@[expose] noncomputable def t : Equiv.Perm (Fin 480) := E wT0

@[expose] noncomputable def tc : Equiv.Perm (Fin 480) := E wTc

@[expose] noncomputable def R : Subgroup (Equiv.Perm (Fin 480)) :=
  Subgroup.closure {E wI0, E wJ0}

@[expose] noncomputable def cP (k : ℕ) : Equiv.Perm (Fin 480) := permOfArr 480 (cA k)

@[expose] noncomputable def Zt1 : Set (Equiv.Perm (Fin 480)) := {t}

@[expose] noncomputable def Zt4 : Set (Equiv.Perm (Fin 480)) := {t, t * cP 0, t * cP 1, t * cP 2}

@[expose] noncomputable def D (Z : Set (Equiv.Perm (Fin 480))) : Set (Equiv.Perm (Fin 480)) :=
  {d | ∃ g ∈ Yg, d = g * t * g⁻¹ ∧ d ∉ Z}

@[expose] def TwinFail (x y s : Equiv.Perm (Fin 480)) : Prop :=
  (∃ g ∈ ({x, y} : Set (Equiv.Perm (Fin 480))), ∀ k < 4,
      s * g * s⁻¹ ≠ x ^ k ∧ s * g * s⁻¹ ≠ y * x ^ k) ∧
    ∃ a ∈ ({x, y} : Set (Equiv.Perm (Fin 480))), ∃ b ∈ ({x, y} : Set (Equiv.Perm (Fin 480))),
      a * (s * b * s⁻¹) ≠ (s * b * s⁻¹) * a

@[expose] noncomputable def S8 : Set (Equiv.Perm (Fin 480)) :=
  {u | ∃ w ∈ ([] :: wFuse0 : List (List ℕ)), ∃ v ∈ [wI0, wJ0], u = E w * E v * (E w)⁻¹}

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Facts

end
