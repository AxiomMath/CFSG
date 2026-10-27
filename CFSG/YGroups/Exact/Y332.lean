module

public import CFSG.YGroups.Chain
public import CFSG.YGroups.Exact.Model
public import CFSG.YGroups.Exact.Y332Inputs
public import Certificates.Certificate10099
public import Certificates.Data.CFSGNative.YGroups.ExactData
public meta import CFSG.YGroups.Defs
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.YGroups.ExactData
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.YGroups

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.CosetEnumeration (evalWord)

theorem y332_check : y332Arrays.size = 9 ∧
    ModelNative.permsOK 28162 y332Arrays = true ∧
    ModelNative.relatorsOK 28162 y332Arrays (yRels 3 3 2) = true ∧
    ModelNative.chainOK 28162 y332Arrays y332Words y332Base = true ∧
    ModelNative.chainSizes 28162 y332Arrays y332Words y332Base =
      [2, 28160, 3159, 288, 35, 12, 3, 2, 2] :=
  Certificates.certificate10099

@[expose] noncomputable def y332Gen (c : ℕ) : Equiv.Perm (Fin 28162) :=
  arrGen 28162 y332Arrays c

theorem y332_relators : ∀ w ∈ yRels 3 3 2, evalWord y332Gen w = 1 :=
  evalWord_arrGen_eq_one y332_check.2.1 y332_check.2.2.1

noncomputable def y332Model :
    YGroup 3 3 2 →* Equiv.Perm (Fin 28162) :=
  yModelHom y332Gen y332_relators

private theorem y332_model_spec :
    Function.Injective y332Model ∧ Nat.card (YGroup 3 3 2) = 258247006617600 :=
  yModelHom_injective_and_card (n := 28162) (O := y332Arrays) (W := y332Words)
    (base := y332Base) y332 (by simp [ngen, y332_check.1]) y332_relators
    y332_check.2.2.2.1 (by rw [y332_check.2.2.2.2]; norm_num)

theorem y332Model_injective :
    Function.Injective y332Model := y332_model_spec.1

theorem card_y332 :
    Nat.card (YGroup 3 3 2) = 258247006617600 := y332_model_spec.2

theorem evalWord_yGen_332_eq_iff
    (u v : List ℕ) :
    evalWord (yGen 3 3 2) u = evalWord (yGen 3 3 2) v ↔
      eqA 28162 (ModelNative.evalW 28162 y332Arrays u)
        (ModelNative.evalW 28162 y332Arrays v) = true :=
  evalWord_yGen_eq_iff (by simp [ngen, y332_check.1]) y332_check.2.1 y332_relators
    y332Model_injective u v

theorem evalWord_yGen_332_eq_one_iff
    (w : List ℕ) :
    evalWord (yGen 3 3 2) w = 1 ↔
      eqA 28162 (ModelNative.evalW 28162 y332Arrays w) (idA 28162) = true :=
  evalWord_yGen_eq_one_iff (by simp [ngen, y332_check.1]) y332_check.2.1 y332_relators
    y332Model_injective w

end CFSG.YGroups
