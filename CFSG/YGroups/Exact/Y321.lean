module

public import CFSG.YGroups.Chain
public import CFSG.YGroups.Exact.Model
public import CFSG.YGroups.Exact.ModelRep
public import CFSG.YGroups.Exact.Y321Inputs
public import Certificates.Certificate10097
public import Certificates.Data.CFSGNative.YGroups.ExactData
public meta import CFSG.YGroups.Defs
public meta import Certificates.Data.CFSGNative.YGroups.Check
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.YGroups.ExactData
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.YGroups

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.CosetEnumeration (evalWord)

theorem rels_y221_y321 : ∀ w ∈ yRels 2 2 1, w.map (shiftAt 2) ∈ yRels 3 2 1 := by decide

theorem y321 :
    Finite (YGroup 3 2 1) ∧ Nat.card (YGroup 3 2 1) ≤ 2903040 :=
  Certificates.certificate10097.1

theorem y321_check : y321Arrays.size = 7 ∧
    (∀ c < 7, Rep 56 y321Arrays[c]! (arrGen 56 y321Arrays c)) ∧
    (∀ w ∈ yRels 3 2 1, evalWord (arrGen 56 y321Arrays) w = 1) ∧
    2903040 ≤ Nat.card (arrClosure 56 y321Arrays) :=
  Certificates.certificate10097.2

@[expose] noncomputable def y321Gen (c : ℕ) : Equiv.Perm (Fin 56) :=
  arrGen 56 y321Arrays c

theorem rep_y321Gen {c : ℕ} (hc : c < 7) :
    Rep 56 y321Arrays[c]! (y321Gen c) :=
  y321_check.2.1 c hc

theorem y321_relators : ∀ w ∈ yRels 3 2 1, evalWord y321Gen w = 1 :=
  y321_check.2.2.1

noncomputable def y321Model : YGroup 3 2 1 →* Equiv.Perm (Fin 56) :=
  yModelHom y321Gen y321_relators

theorem y321Model_yGen {c : ℕ} (hc : c < 7) :
    y321Model (yGen 3 2 1 c) = y321Gen c :=
  yModelHom_yGen hc

theorem y321Model_rep {c : ℕ} (hc : c < 7) :
    Rep 56 y321Arrays[c]! (y321Model (yGen 3 2 1 c)) := by
  rw [y321Model_yGen hc]
  exact rep_y321Gen hc

private theorem y321_rep :
    ∀ c < y321Arrays.size, Rep 56 y321Arrays[c]! (arrGen 56 y321Arrays c) := by
  intro c hc
  rw [y321_check.1] at hc
  exact y321_check.2.1 c hc

private theorem y321_model_spec :
    Function.Injective y321Model ∧ Nat.card (YGroup 3 2 1) = 2903040 :=
  yModelHom_injective_and_card_of_le (n := 56) (O := y321Arrays) y321
    (by simp [ngen, y321_check.1]) y321_relators y321_check.2.2.2

theorem y321Model_injective :
    Function.Injective y321Model := y321_model_spec.1

theorem card_y321 :
    Nat.card (YGroup 3 2 1) = 2903040 := y321_model_spec.2

theorem evalWord_yGen_321_eq_iff (u v : List ℕ) :
    evalWord (yGen 3 2 1) u = evalWord (yGen 3 2 1) v ↔
      eqA 56 (ModelNative.evalW 56 y321Arrays u)
        (ModelNative.evalW 56 y321Arrays v) = true :=
  evalWord_yGen_eq_iff_of_rep (by simp [ngen, y321_check.1]) y321_rep y321_relators
    y321Model_injective u v

theorem evalWord_yGen_321_eq_one_iff (w : List ℕ) :
    evalWord (yGen 3 2 1) w = 1 ↔
      eqA 56 (ModelNative.evalW 56 y321Arrays w) (idA 56) = true :=
  evalWord_yGen_eq_one_iff_of_rep (by simp [ngen, y321_check.1]) y321_rep y321_relators
    y321Model_injective w

end CFSG.YGroups
