module

public import CFSG.Sporadic.HNSchreier.Data
public import CFSG.Sporadic.HNSchreier.BFSList
public import CFSG.Sporadic.HNSchreier.Seeds

public section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic Matrix

abbrev nPts : ℕ := 1140000

abbrev Vec : Type := Fin 133 → ZMod 5

@[expose] def fixedVector : Vec :=
  fun j => (((Data.rootDigits.toList.getD j.val '0').toNat - '0'.toNat : ℕ) : ZMod 5)

@[expose, irreducible] noncomputable def formM : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  decode 5 133 1 Data.formPayload

theorem formM_eq : formM = decode 5 133 1 Data.formPayload := by unfold formM; rfl

@[expose, irreducible] noncomputable def orbitL : List Vec :=
  orbitList (fun x => matA *ᵥ x) (fun x => matB *ᵥ x) fixedVector nPts

theorem orbitL_eq :
    orbitL = orbitList (fun x => matA *ᵥ x) (fun x => matB *ᵥ x) fixedVector nPts := by
  unfold orbitL; rfl

@[expose] noncomputable def vL (i : ℕ) : Vec := orbitL.getD i 0

@[expose] noncomputable def firstIndex (w : Vec) : ℕ :=
  if orbitL.idxOf w < nPts ∧ orbitL.idxOf w < orbitL.length then orbitL.idxOf w else 0

@[expose] noncomputable def f0 (i : ℕ) : ℕ :=
  if i < orbitL.length then firstIndex (matA *ᵥ vL i) else 0

@[expose] noncomputable def f1 (i : ℕ) : ℕ :=
  if i < orbitL.length then firstIndex (matB *ᵥ vL i) else 0

@[expose] noncomputable def pairing (i j : ℕ) : ZMod 5 :=
  if i < orbitL.length ∧ j < orbitL.length then vL i ⬝ᵥ (formM *ᵥ vL j) else 0

@[expose] def runProg {G : Type*} [Group G] : (ℕ → G) → List (ℕ × ℕ × ℕ) → ℕ → G
  | regs, [] => regs
  | regs, (a, b, c) :: rest => runProg (Function.update regs c (regs a * regs b)) rest

@[expose] def progReadsInit : List ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | init, (a, b, c) :: rest => decide (a ∈ init) && decide (b ∈ init) &&
      progReadsInit (c :: init) rest

theorem rootDigits_facts : Data.rootDigits.toList.length = 133 ∧
    Data.rootDigits.toList.all (fun c => c ∈ ['0', '1', '2', '3', '4']) = true := by
  decide +kernel

theorem base_facts : Data.baseList.length = 22 ∧ Data.baseList.Nodup ∧
    ∀ b ∈ Data.baseList, b < nPts := by
  decide +kernel

theorem words_facts : Data.strongWords.size = 9 ∧ Data.strongWords[0]! = [] ∧
    Data.strongWords[1]! = [] ∧
    ∀ j < 9, 2 ≤ j → ∀ l ∈ Data.strongWords[j]!, l ≠ 0 ∧ l.natAbs ≤ j := by
  decide +kernel

theorem program_facts : Data.subgroupProgram.length = 10 ∧
    progReadsInit [1, 2] Data.subgroupProgram = true ∧
    ∀ t ∈ Data.subgroupProgram, 1 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ 1 ≤ t.2.2 := by
  decide +kernel

theorem cert_hn_vector_orbit_data :
    (Data.rootDigits.toList.length = 133 ∧
      Data.rootDigits.toList.all (fun c => c ∈ ['0', '1', '2', '3', '4']) = true) ∧
    (Data.baseList.length = 22 ∧ Data.baseList.Nodup ∧ ∀ b ∈ Data.baseList, b < nPts) ∧
    (Data.strongWords.size = 9 ∧ Data.strongWords[0]! = [] ∧ Data.strongWords[1]! = [] ∧
      ∀ j < 9, 2 ≤ j → ∀ l ∈ Data.strongWords[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
    (Data.subgroupProgram.length = 10 ∧ progReadsInit [1, 2] Data.subgroupProgram = true ∧
      ∀ t ∈ Data.subgroupProgram, 1 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ 1 ≤ t.2.2) ∧
    orbitL = orbitList (fun x => matA *ᵥ x) (fun x => matB *ᵥ x) fixedVector nPts ∧
    orbitL.length ≤ 2 * nPts + 1 ∧
    (∀ i, f0 i = if i < orbitL.length then firstIndex (matA *ᵥ vL i) else 0) ∧
    (∀ i, f1 i = if i < orbitL.length then firstIndex (matB *ᵥ vL i) else 0) ∧
    ∀ i j, pairing i j =
      if i < orbitL.length ∧ j < orbitL.length then vL i ⬝ᵥ (formM *ᵥ vL j) else 0 :=
  ⟨rootDigits_facts, base_facts, words_facts, program_facts, orbitL_eq,
    by rw [orbitL_eq]; exact orbitList_length_le _ _ _ _, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl⟩

end CFSG.Sporadic.HNSchreier
