module

public import CFSG.Monster.B.Pinned.Primes.SeedGL

public section

namespace CFSG.Monster.B.Pinned

open CFSG.Blueprint Primes.Native

@[expose] noncomputable def xFive :
    NativeSporadic.B := runG fiveProg bA₁ bA₂ 1

@[expose] noncomputable def hFive :
    NativeSporadic.B := runG fiveProg bA₁ bA₂ 2

@[expose] noncomputable def wFive :
    NativeSporadic.B := xFive * hFive ^ 3

@[expose] noncomputable def qBaseFive : NativeSporadic.B := wFive ^ 8

@[expose] noncomputable def qFive : Fin 4 → NativeSporadic.B :=
  ![qBaseFive, hFive⁻¹ * qBaseFive * hFive, xFive⁻¹ * qBaseFive * xFive,
    (hFive * xFive)⁻¹ * qBaseFive * (hFive * xFive)]

@[expose] noncomputable def zFive :
    NativeSporadic.B := bcomm (qFive 0) (qFive 1)

@[expose] noncomputable def QFive :
    Subgroup NativeSporadic.B := Subgroup.closure (Set.range qFive)

@[expose] noncomputable def PFive :
    Subgroup NativeSporadic.B := QFive ⊔ Subgroup.zpowers xFive

theorem range_qFive :
    Set.range qFive = {qFive 0, qFive 1, qFive 2, qFive 3} := by
  ext g
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

theorem fiveProg_lt : ∀ ins ∈ fiveProg, ins.lt 22 = true := by decide +kernel

theorem pinned_B_five_primary_word_data :
    fiveProg.length = 87 ∧ (∀ ins ∈ fiveProg, ins.lt 22 = true) ∧
      (∀ ins ∈ fiveProg, 0 < insOut ins) ∧
      initOK fiveProg [1, 2] = true ∧
      (∀ r : ℕ → NativeSporadic.B, r 1 = bA₁ → r 2 = bA₂ →
        fiveProg.foldl insStepG r 1 = xFive ∧ fiveProg.foldl insStepG r 2 = hFive) ∧
      xFive = runG fiveProg bA₁ bA₂ 1 ∧ hFive = runG fiveProg bA₁ bA₂ 2 ∧
      (bSeedGL xFive : GL (Fin 4370) (ZMod 2)) = runG fiveProg glA₁ glA₂ 1 ∧
      (bSeedGL hFive : GL (Fin 4370) (ZMod 2)) = runG fiveProg glA₁ glA₂ 2 ∧
      wFive = xFive * hFive ^ 3 ∧ qBaseFive = wFive ^ 8 ∧ qFive 0 = qBaseFive ∧
      qFive 1 = hFive⁻¹ * qBaseFive * hFive ∧ qFive 2 = xFive⁻¹ * qBaseFive * xFive ∧
      qFive 3 = (hFive * xFive)⁻¹ * qBaseFive * (hFive * xFive) ∧
      zFive = (qFive 0)⁻¹ * (qFive 1)⁻¹ * qFive 0 * qFive 1 ∧
      QFive = Subgroup.closure {qFive 0, qFive 1, qFive 2, qFive 3} ∧
      PFive = QFive ⊔ Subgroup.zpowers xFive :=
  ⟨by decide +kernel, fiveProg_lt, by decide +kernel, by decide +kernel,
    fun r h1 h2 => runG_of_initOK (by decide +kernel) r h1 h2, rfl, rfl, bSeedGL_runG _ _,
    bSeedGL_runG _ _, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, by rw [QFive, range_qFive], rfl⟩

end CFSG.Monster.B.Pinned
