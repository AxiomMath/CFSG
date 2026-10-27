module

public import CFSG.Sporadic.Schreier.RuCheckWit
public import CFSG.Sporadic.Schreier.RuReps

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem rep_ruM1 :
    Rep 4060 ruM1A ruM1 :=
  (rep_slotRunA ruMProg rep_ruA0 rep_ruA1 ruWit_check.1).1

theorem rep_ruM2 :
    Rep 4060 ruM2A ruM2 :=
  (rep_slotRunA ruMProg rep_ruA0 rep_ruA1 ruWit_check.1).2

theorem rep_ruSeedWordA {w : List ℤ} (hw : lettersOK 2 w = true) :
    Rep 4060 (ruSeedWordA w) (evalSigned [ruA0, ruA1] w) :=
  rep_wordA_evalSigned (k := 2) (rep_pair_getD rep_ruA0 rep_ruA1)
    (rep_pair_getD_inv (rep_ruInv rep_ruA0 ruBasic_check.1)
      (rep_ruInv rep_ruA1 ruBasic_check.2.1)) w hw

theorem rep_ruMWordA
    {w : List ℤ} (hw : lettersOK 2 w = true) :
    Rep 4060 (ruMWordA w) (evalSigned [ruM1, ruM2] w) :=
  rep_wordA_evalSigned (k := 2) (rep_pair_getD rep_ruM1 rep_ruM2)
    (rep_pair_getD_inv (rep_ruInv rep_ruM1 ruWit_check.2.1)
      (rep_ruInv rep_ruM2 ruWit_check.2.2.1)) w hw

theorem rep_ruRw :
    Rep 4060 ruRwA ruRw :=
  rep_ruMWordA ruWit_check.2.2.2.2.2.2.2.1

theorem rep_ruWw :
    Rep 4060 ruWwA ruWw :=
  rep_ruSeedWordA ruWit_check.2.2.2.2.2.2.2.2.1

theorem rep_ruUw :
    Rep 4060 ruUwA ruUw :=
  rep_compA (rep_compA (rep_compA rep_ruWw rep_ruRw)
    (rep_ruInv rep_ruWw ruWit_check.2.2.2.1)) rep_ruA0

theorem rep_ruHw :
    Rep 4060 ruHwA ruHw := rep_compA (rep_powA rep_ruUw 7) rep_ruWw

theorem rep_ruLGens :
    ∀ i < 3, Rep 4060 ruLGensA[i]! (ruLGens.getD i 1) := by
  have hl : ∀ w ∈ ruLMWords, lettersOK 2 w = true :=
    List.all_eq_true.1 ruWit_check.2.2.2.2.2.2.2.2.2.1
  exact rep_map_getD (ws := ruLMWords) fun w hw =>
    rep_compA (rep_compA rep_ruHw (rep_ruMWordA (hl w hw)))
      (rep_ruInv rep_ruHw ruWit_check.2.2.2.2.1)

theorem ruLGensA_size : ruLGensA.size = 3 := by
  simp [ruLGensA, ruLMWords]

theorem ruLGens_length : ruLGens.length = 3 := by
  simp [ruLGens, ruLMWords]

theorem rep_ruLGensInv :
    ∀ i < 3, Rep 4060 (ruLGensA.map ruInv)[i]! (ruLGens.getD i 1)⁻¹ := by
  intro i hi
  have e : (ruLGensA.map ruInv)[i]! = ruInv ruLGensA[i]! := by
    rw [getElem!_pos _ i (by simpa [ruLGensA_size] using hi),
      getElem!_pos _ i (by simpa [ruLGensA_size] using hi)]
    simp
  rw [e]
  exact rep_ruInv (rep_ruLGens i hi) (ruWit_check.2.2.2.2.2.1 i hi)

theorem rep_ruLGen
    {i : ℕ} (hi : i < 3) : Rep 4060 ruLGensA[i]! (ruLGen (i + 1)) := by
  have := rep_ruLGens i hi
  simpa [ruLGen] using this

theorem rep_ruSGensInv :
    ∀ h < 4, Rep 4060 (ruSGensA.map ruInv)[h]! (ruSGens.getD h 1)⁻¹ := by
  intro h hh
  have e : (ruSGensA.map ruInv)[h]! = ruInv ruSGensA[h]! := by
    rw [getElem!_pos _ h (by simpa [ruSGensA_size] using hh),
      getElem!_pos _ h (by simpa [ruSGensA_size] using hh)]
    simp
  rw [e]
  exact rep_ruInv (rep_ruSGens h hh) (ruBasic_check.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh)

theorem rep_ruFusX
    {i : ℕ} (hi : i ∈ [1, 2, 3]) : Rep 4060 (ruFusXA i) (ruFusX i) :=
  rep_wordA_evalSigned (k := 4) rep_ruSGens rep_ruSGensInv _
    (ruWit_check.2.2.2.2.2.2.2.2.2.2.1 i hi).1

theorem rep_ruFusG
    {i : ℕ} (hi : i ∈ [1, 2, 3]) : Rep 4060 (ruFusGA i) (ruFusG i) :=
  rep_ruSeedWordA (ruWit_check.2.2.2.2.2.2.2.2.2.2.1 i hi).2

theorem rep_ruFusH
    {i : ℕ} (hi : i ∈ [1, 2, 3]) : Rep 4060 (ruFusHA i) (ruFusH i) :=
  rep_compA (rep_powA (rep_compA (rep_compA (rep_compA (rep_ruFusG hi) rep_ruA0)
    (rep_ruInv (rep_ruFusG hi) (ruWit_check.2.2.2.2.2.2.1 i hi))) (rep_ruFusX hi)) _)
    (rep_ruFusG hi)

theorem rep_ruYp
    {p : ℕ} (hp : p ∈ [5, 7, 13]) : Rep 4060 (ruYpA p) (ruYp p) :=
  rep_wordA_evalSigned (k := 3) rep_ruLGens rep_ruLGensInv _
    (ruWit_check.2.2.2.2.2.2.2.2.2.2.2.1 p hp)

end CFSG.Sporadic.RuSchreier
