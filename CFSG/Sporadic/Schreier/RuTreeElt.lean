module

public import CFSG.Sporadic.Schreier.RuTreeEltA
public import CFSG.Sporadic.Schreier.RuReps
public import CFSG.Sporadic.Schreier.RuCertData
public import CFSG.Sporadic.Schreier.RuConj

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

abbrev ruZP : Set (Equiv.Perm (Fin 4060)) := conjSet ruP ruZ

abbrev ruAP : Set (Equiv.Perm (Fin 4060)) := conjSet ruP ruA0

@[expose] def ruTGen (k : ℕ) : Equiv.Perm (Fin 4060) := if k = 0 then ruA0 else ruA1

@[expose] def ruTElt : ℕ → ℕ → Equiv.Perm (Fin 4060)
  | 0, _ => 1
  | f + 1, j => if j = 0 then 1 else ruTGen ruTreeLab[j]! * ruTElt f ruTreePar[j]!

@[expose] def ruTZ (j : ℕ) : Equiv.Perm (Fin 4060) := ruTElt 64 j * ruZ * (ruTElt 64 j)⁻¹

theorem rep_ruTGen (k : ℕ) : Rep 4060 (ruTGenA k) (ruTGen k) := by
  by_cases hk : k = 0
  · simp only [ruTGenA, ruTGen, hk, ↓reduceIte]
    exact rep_ruA0
  · simp only [ruTGenA, ruTGen, hk, ↓reduceIte]
    exact rep_ruA1

theorem rep_ruTGenInv
    (k : ℕ) : Rep 4060 (ruTGenInvA k) (ruTGen k)⁻¹ := by
  by_cases hk : k = 0
  · simp only [ruTGenInvA, ruTGen, hk, ↓reduceIte]
    exact rep_ruInv rep_ruA0 ruBasic_check.1
  · simp only [ruTGenInvA, ruTGen, hk, ↓reduceIte]
    exact rep_ruInv rep_ruA1 ruBasic_check.2.1

theorem rep_ruTElt : ∀ f j, Rep 4060 (ruTEltA f j) (ruTElt f j)
  | 0, _ => rep_idA
  | f + 1, j => by
    by_cases hj : j = 0
    · simp only [ruTEltA, ruTElt, hj, ↓reduceIte]
      exact rep_idA
    · simp only [ruTEltA, ruTElt, hj, ↓reduceIte]
      exact rep_compA (rep_ruTGen _) (rep_ruTElt f _)

theorem rep_ruTEltInv :
    ∀ f j, Rep 4060 (ruTEltInvA f j) (ruTElt f j)⁻¹
  | 0, _ => by
    rw [ruTEltInvA, ruTElt, inv_one]
    exact rep_idA
  | f + 1, j => by
    by_cases hj : j = 0
    · simp only [ruTEltInvA, ruTElt, hj, ↓reduceIte, inv_one]
      exact rep_idA
    · simp only [ruTEltInvA, ruTElt, hj, ↓reduceIte, mul_inv_rev]
      exact rep_compA (rep_ruTEltInv f _) (rep_ruTGenInv _)

theorem ruTGen_mem (k : ℕ) : ruTGen k ∈ ruP := by
  by_cases hk : k = 0
  · simp only [ruTGen, hk, ↓reduceIte]
    exact ruA0_mem
  · simp only [ruTGen, hk, ↓reduceIte]
    exact ruA1_mem

theorem ruTElt_mem : ∀ f j, ruTElt f j ∈ ruP
  | 0, _ => ruP.one_mem
  | f + 1, j => by
    by_cases hj : j = 0
    · simp only [ruTElt, hj, ↓reduceIte]
      exact ruP.one_mem
    · simp only [ruTElt, hj, ↓reduceIte]
      exact ruP.mul_mem (ruTGen_mem _) (ruTElt_mem f _)

theorem rep_ruTZ (j : ℕ) : Rep 4060 (ruTZA j) (ruTZ j) :=
  rep_compA (rep_compA (rep_ruTElt 64 j) rep_ruZ) (rep_ruTEltInv 64 j)

theorem ruTZ_mem (j : ℕ) : ruTZ j ∈ ruZP := ⟨ruTElt 64 j, ruTElt_mem 64 j, rfl⟩

theorem mem_ruZP_of_ruZWit
    {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (h : ruZWit t = true) : g ∈ ruZP := by
  have := eq_of_eqA (rep_ruTZ _) ht h
  rw [← this]
  exact ruTZ_mem _

end CFSG.Sporadic.RuSchreier
