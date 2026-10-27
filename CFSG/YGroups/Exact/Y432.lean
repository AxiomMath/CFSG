module

public import CFSG.YGroups.Chain
public import CFSG.YGroups.Exact.Model
public import CFSG.YGroups.Exact.Y432Inputs
public import Certificates.Certificate10100
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

theorem y432_check : y432Arrays.size = 10 ∧
    ModelNative.permsOK 31673 y432Arrays = true ∧
    ModelNative.relatorsOK 31673 y432Arrays (yRels 4 3 2) = true ∧
    ModelNative.chainOK 31673 y432Arrays y432Words y432Base = true ∧
    ModelNative.chainSizes 31673 y432Arrays y432Words y432Base =
      [2, 31671, 28160, 3159, 288, 35, 12, 3, 2, 2] :=
  Certificates.certificate10100

@[expose] noncomputable def y432Gen (c : ℕ) : Equiv.Perm (Fin 31673) :=
  arrGen 31673 y432Arrays c

theorem rep_y432Gen {c : ℕ} (hc : c < 10) :
    Rep 31673 y432Arrays[c]! (y432Gen c) := by
  have h := rep_letterOf y432_check.2.1 c
  rwa [ModelNative.letterOf, ite_eq_left (by have := y432_check.1; omega)] at h

theorem y432_relators : ∀ w ∈ yRels 4 3 2, evalWord y432Gen w = 1 :=
  evalWord_arrGen_eq_one y432_check.2.1 y432_check.2.2.1

noncomputable def y432Model :
    YGroup 4 3 2 →* Equiv.Perm (Fin 31673) :=
  yModelHom y432Gen y432_relators

theorem y432Model_yGen {c : ℕ} (hc : c < 10) :
    y432Model (yGen 4 3 2 c) = y432Gen c :=
  yModelHom_yGen hc

theorem y432Model_rep {c : ℕ} (hc : c < 10) :
    Rep 31673 y432Arrays[c]! (y432Model (yGen 4 3 2 c)) := by
  rw [y432Model_yGen hc]
  exact rep_y432Gen hc

private theorem y432_model_spec :
    Function.Injective y432Model ∧ Nat.card (YGroup 4 3 2) = 8178940946586009600 :=
  yModelHom_injective_and_card (n := 31673) (O := y432Arrays) (W := y432Words)
    (base := y432Base) y432 (by simp [ngen, y432_check.1]) y432_relators
    y432_check.2.2.2.1 (by rw [y432_check.2.2.2.2]; norm_num)

theorem y432Model_injective :
    Function.Injective y432Model := y432_model_spec.1

theorem card_y432 :
    Nat.card (YGroup 4 3 2) = 8178940946586009600 := y432_model_spec.2

theorem evalWord_yGen_432_eq_iff
    (u v : List ℕ) :
    evalWord (yGen 4 3 2) u = evalWord (yGen 4 3 2) v ↔
      eqA 31673 (ModelNative.evalW 31673 y432Arrays u)
        (ModelNative.evalW 31673 y432Arrays v) = true :=
  evalWord_yGen_eq_iff (by simp [ngen, y432_check.1]) y432_check.2.1 y432_relators
    y432Model_injective u v

theorem evalWord_yGen_432_eq_one_iff
    (w : List ℕ) :
    evalWord (yGen 4 3 2) w = 1 ↔
      eqA 31673 (ModelNative.evalW 31673 y432Arrays w) (idA 31673) = true :=
  evalWord_yGen_eq_one_iff (by simp [ngen, y432_check.1]) y432_check.2.1 y432_relators
    y432Model_injective w

end CFSG.YGroups
