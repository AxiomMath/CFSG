
module

public import CFSG.Monster.B.TwoA.Unitary.Stab891Base
public import CFSG.Monster.B.TwoA.Unitary.Order
public import CFSG.Monster.B.TwoA.Unitary.WittBase
public meta import CFSG.Monster.B.TwoA.Unitary.BData
public import Certificates.Certificate3062
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import CFSG.Monster.B.TwoA.Unitary.PlanesInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.Monster.B.TwoA.Unitary.PlanesBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
open CFSG.ClassicalGroups.UnitaryFlag Matrix

theorem b6IsoArr_inj :
    ∀ i < 891, ∀ j < 891, b6IsoArr[i]! % 891 = b6IsoArr[j]! % 891 → i = j :=
  Certificates.certificate3062

theorem b6Iso_val (j : Fin 891) : (b6Iso j : ℕ) = b6IsoArr[(j : ℕ)]! % 891 := rfl

theorem b6Iso_bijective : Function.Bijective b6Iso := by
  refine (Finite.injective_iff_bijective).1 fun i j h => ?_
  have h' := congrArg Fin.val h
  rw [b6Iso_val, b6Iso_val] at h'
  exact Fin.ext (b6IsoArr_inj i i.2 j j.2 h')

@[expose] def Lp (j : Fin 891) : Submodule F4 V6 := plane (b6Iso j)

@[expose] def Permutes (x : SigmaU6) : Prop := ∀ j, ∃ j', sigmaAct (Lp j) x = Lp j'

theorem sigmaAct_inv_cancel (P : Submodule F4 V6) (x : SigmaU6) :
    sigmaAct (sigmaAct P x) x⁻¹ = P := by
  rw [← sigmaAct_mul, mul_inv_cancel, sigmaAct_one]

theorem Permutes.mul {x y : SigmaU6} (hx : Permutes x) (hy : Permutes y) : Permutes (x * y) := by
  intro j
  obtain ⟨j', hj'⟩ := hx j
  obtain ⟨j'', hj''⟩ := hy j'
  exact ⟨j'', by rw [sigmaAct_mul, hj', hj'']⟩

instance finite_SigmaU6 : Finite SigmaU6 :=
  Nat.finite_of_card_ne_zero (by rw [natCard_SigmaU6]; norm_num)

end CFSG.Monster.B.TwoA.Unitary
