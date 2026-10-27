module

public import CFSG.Monster.B.Pinned.Primes.SeedGL

public section

namespace CFSG.Monster.B.Pinned

open CFSG.Blueprint Primes.Native

@[expose] noncomputable def xThree :
    NativeSporadic.B := runG threeProg bA₁ bA₂ 1

@[expose] noncomputable def hThree :
    NativeSporadic.B := runG threeProg bA₁ bA₂ 2

@[expose] noncomputable def LThree :
    Subgroup NativeSporadic.B := Subgroup.closure {xThree, hThree}

@[expose] noncomputable def qBaseThree : NativeSporadic.B :=
  xThree ^ 20 * (hThree⁻¹ * xThree ^ 20 * hThree)

@[expose] noncomputable def qThree : Fin 8 → NativeSporadic.B :=
  ![qBaseThree, xThree⁻¹ * qBaseThree * xThree, hThree⁻¹ * qBaseThree * hThree,
    (xThree * xThree)⁻¹ * qBaseThree * (xThree * xThree),
    (xThree * hThree)⁻¹ * qBaseThree * (xThree * hThree),
    (hThree * xThree)⁻¹ * qBaseThree * (hThree * xThree),
    (hThree * hThree)⁻¹ * qBaseThree * (hThree * hThree),
    (xThree * xThree * xThree)⁻¹ * qBaseThree * (xThree * xThree * xThree)]

@[expose] noncomputable def zThree :
    NativeSporadic.B := bcomm (qThree 0) (qThree 1)

@[expose] noncomputable def QThree : Subgroup NativeSporadic.B :=
  Subgroup.closure (Set.range qThree)

theorem threeProg_lt : ∀ ins ∈ threeProg, ins.lt 18 = true := by decide +kernel

theorem xThree_mem :
    xThree ∈ LThree := Subgroup.subset_closure (Set.mem_insert _ _)

theorem hThree_mem :
    hThree ∈ LThree := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem qThree_mem_L (i : Fin 8) : qThree i ∈ LThree := by
  have hx := xThree_mem
  have hh := hThree_mem
  have hq : qBaseThree ∈ LThree :=
    mul_mem (pow_mem hx 20) (mul_mem (mul_mem (inv_mem hh) (pow_mem hx 20)) hh)
  have conj : ∀ b ∈ LThree, b⁻¹ * qBaseThree * b ∈ LThree :=
    fun b hb => mul_mem (mul_mem (inv_mem hb) hq) hb
  fin_cases i
  · exact hq
  · exact conj _ hx
  · exact conj _ hh
  · exact conj _ (mul_mem hx hx)
  · exact conj _ (mul_mem hx hh)
  · exact conj _ (mul_mem hh hx)
  · exact conj _ (mul_mem hh hh)
  · exact conj _ (mul_mem (mul_mem hx hx) hx)

theorem QThree_le_LThree : QThree ≤ LThree := by
  rw [QThree, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact qThree_mem_L i

theorem pinned_B_three_primary_word_data :
    threeProg.length = 80 ∧ (∀ ins ∈ threeProg, ins.lt 18 = true) ∧
      (∀ ins ∈ threeProg, 0 < insOut ins) ∧
      initOK threeProg [1, 2] = true ∧
      (∀ r : ℕ → NativeSporadic.B, r 1 = bA₁ → r 2 = bA₂ →
        threeProg.foldl insStepG r 1 = xThree ∧ threeProg.foldl insStepG r 2 = hThree) ∧
      xThree = runG threeProg bA₁ bA₂ 1 ∧ hThree = runG threeProg bA₁ bA₂ 2 ∧
      (bSeedGL xThree : GL (Fin 4370) (ZMod 2)) = runG threeProg glA₁ glA₂ 1 ∧
      (bSeedGL hThree : GL (Fin 4370) (ZMod 2)) = runG threeProg glA₁ glA₂ 2 ∧
      LThree = Subgroup.closure {xThree, hThree} ∧
      qBaseThree = xThree ^ 20 * (hThree⁻¹ * xThree ^ 20 * hThree) ∧
      qThree = ![qBaseThree, xThree⁻¹ * qBaseThree * xThree, hThree⁻¹ * qBaseThree * hThree,
        (xThree * xThree)⁻¹ * qBaseThree * (xThree * xThree),
        (xThree * hThree)⁻¹ * qBaseThree * (xThree * hThree),
        (hThree * xThree)⁻¹ * qBaseThree * (hThree * xThree),
        (hThree * hThree)⁻¹ * qBaseThree * (hThree * hThree),
        (xThree * xThree * xThree)⁻¹ * qBaseThree * (xThree * xThree * xThree)] ∧
      zThree = (qThree 0)⁻¹ * (qThree 1)⁻¹ * qThree 0 * qThree 1 ∧
      QThree = Subgroup.closure (Set.range qThree) ∧ QThree ≤ LThree ∧
      MThree = rowsMat 3 8 threeCommRows ∧ XThree = rowsMat 3 8 threeXRows ∧
      YThree = rowsMat 3 8 threeYRows ∧ cThree = rowsVec 3 8 threeCVec ∧
      dThree = rowsVec 3 8 threeDVec :=
  ⟨by decide +kernel, threeProg_lt, by decide +kernel, by decide +kernel,
    fun r h1 h2 => runG_of_initOK (by decide +kernel) r h1 h2, rfl, rfl, bSeedGL_runG _ _,
    bSeedGL_runG _ _, rfl, rfl, rfl,
    rfl, rfl, QThree_le_LThree, rfl, rfl, rfl, rfl, rfl⟩

end CFSG.Monster.B.Pinned
