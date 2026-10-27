module

public import CFSG.YGroups.Chain
public import CFSG.YGroups.Exact.Model
public import CFSG.YGroups.Exact.Y322Inputs
public import Certificates.Certificate10098
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

theorem y322_check : y322Arrays.size = 8 ∧
    ModelNative.permsOK 728 y322Arrays = true ∧
    ModelNative.relatorsOK 728 y322Arrays (yRels 3 2 2) = true ∧
    ModelNative.chainOK 728 y322Arrays y322Words y322Base = true ∧
    ModelNative.chainSizes 728 y322Arrays y322Words y322Base =
      [728, 243, 72, 20, 9, 2, 2] :=
  Certificates.certificate10098

@[expose] noncomputable def y322Gen (c : ℕ) : Equiv.Perm (Fin 728) :=
  arrGen 728 y322Arrays c

theorem rep_y322Gen {c : ℕ} (hc : c < 8) :
    Rep 728 y322Arrays[c]! (y322Gen c) := by
  have h := rep_letterOf y322_check.2.1 c
  rwa [ModelNative.letterOf, ite_eq_left (by have := y322_check.1; omega)] at h

theorem y322_relators : ∀ w ∈ yRels 3 2 2, evalWord y322Gen w = 1 :=
  evalWord_arrGen_eq_one y322_check.2.1 y322_check.2.2.1

noncomputable def y322Model :
    YGroup 3 2 2 →* Equiv.Perm (Fin 728) :=
  yModelHom y322Gen y322_relators

theorem y322Model_yGen {c : ℕ} (hc : c < 8) :
    y322Model (yGen 3 2 2 c) = y322Gen c :=
  yModelHom_yGen hc

theorem y322Model_rep {c : ℕ} (hc : c < 8) :
    Rep 728 y322Arrays[c]! (y322Model (yGen 3 2 2 c)) := by
  rw [y322Model_yGen hc]
  exact rep_y322Gen hc

private theorem y322_model_spec :
    Function.Injective y322Model ∧ Nat.card (YGroup 3 2 2) = 9170703360 :=
  yModelHom_injective_and_card (n := 728) (O := y322Arrays) (W := y322Words)
    (base := y322Base) y322 (by simp [ngen, y322_check.1]) y322_relators
    y322_check.2.2.2.1 (by rw [y322_check.2.2.2.2]; norm_num)

theorem y322Model_injective :
    Function.Injective y322Model := y322_model_spec.1

theorem card_y322 :
    Nat.card (YGroup 3 2 2) = 9170703360 := y322_model_spec.2

theorem evalWord_yGen_322_eq_iff
    (u v : List ℕ) :
    evalWord (yGen 3 2 2) u = evalWord (yGen 3 2 2) v ↔
      eqA 728 (ModelNative.evalW 728 y322Arrays u)
        (ModelNative.evalW 728 y322Arrays v) = true :=
  evalWord_yGen_eq_iff (by simp [ngen, y322_check.1]) y322_check.2.1 y322_relators
    y322Model_injective u v

theorem evalWord_yGen_322_eq_one_iff
    (w : List ℕ) :
    evalWord (yGen 3 2 2) w = 1 ↔
      eqA 728 (ModelNative.evalW 728 y322Arrays w) (idA 728) = true :=
  evalWord_yGen_eq_one_iff (by simp [ngen, y322_check.1]) y322_check.2.1 y322_relators
    y322Model_injective w

end CFSG.YGroups
