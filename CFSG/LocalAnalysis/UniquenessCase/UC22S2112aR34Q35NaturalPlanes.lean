module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalPlane
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalBlocks
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open Matrix CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

variable {K : Type*} [Field K]

@[expose] def planeFst (L : Type*) [Field L] : Submodule L ((Fin 2 ⊕ Fin 2) → L) :=
  LinearMap.ker (LinearMap.funLeft L L Sum.inr)

@[expose] def planeSnd (L : Type*) [Field L] : Submodule L ((Fin 2 ⊕ Fin 2) → L) :=
  LinearMap.ker (LinearMap.funLeft L L Sum.inl)

private theorem mem_planeFst_iff {L : Type*} [Field L] (v : (Fin 2 ⊕ Fin 2) → L) :
    v ∈ planeFst L ↔ ∀ k, v (Sum.inr k) = 0 := by
  rw [planeFst, LinearMap.mem_ker]
  constructor
  · intro h k
    have hk := congrFun h k
    simpa [LinearMap.funLeft_apply] using hk
  · intro h
    funext k
    simpa [LinearMap.funLeft_apply] using h k

private theorem mem_planeSnd_iff {L : Type*} [Field L] (v : (Fin 2 ⊕ Fin 2) → L) :
    v ∈ planeSnd L ↔ ∀ k, v (Sum.inl k) = 0 := by
  rw [planeSnd, LinearMap.mem_ker]
  constructor
  · intro h k
    have hk := congrFun h k
    simpa [LinearMap.funLeft_apply] using hk
  · intro h
    funext k
    simpa [LinearMap.funLeft_apply] using h k

@[expose] def IsPlaneMonomial (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) : Prop :=
  (M.toBlocks₁₂ = 0 ∧ M.toBlocks₂₁ = 0) ∨ (M.toBlocks₁₁ = 0 ∧ M.toBlocks₂₂ = 0)

@[expose] def planeMonomial (K : Type*) [Field K] : Subgroup (GL (Fin 2 ⊕ Fin 2) K) where
  carrier := {g | IsPlaneMonomial (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)}
  mul_mem' := by
    intro M N hM hN
    rcases hM with ⟨hM₁₂, hM₂₁⟩ | ⟨hM₁₁, hM₂₂⟩ <;>
      rcases hN with ⟨hN₁₂, hN₂₁⟩ | ⟨hN₁₁, hN₂₂⟩
    · left
      have h : ((M * N : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          fromBlocks ((M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁ *
            (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁) 0 0
            ((M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂ *
              (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂) := by
        rw [Units.val_mul, ← fromBlocks_toBlocks (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
          hM₁₂, hM₂₁, ← fromBlocks_toBlocks (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
          hN₁₂, hN₂₁, fromBlocks_multiply]
        simp
      rw [h, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁]
      exact ⟨rfl, rfl⟩
    · right
      have h : ((M * N : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          fromBlocks 0 ((M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁ *
            (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂)
            ((M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂ *
              (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁) 0 := by
        rw [Units.val_mul, ← fromBlocks_toBlocks (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
          hM₁₂, hM₂₁, ← fromBlocks_toBlocks (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
          hN₁₁, hN₂₂, fromBlocks_multiply]
        simp
      rw [h, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]
      exact ⟨rfl, rfl⟩
    · right
      have h : ((M * N : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          fromBlocks 0 ((M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂ *
            (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂)
            ((M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁ *
              (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁) 0 := by
        rw [Units.val_mul, ← fromBlocks_toBlocks (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
          hM₁₁, hM₂₂, ← fromBlocks_toBlocks (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
          hN₁₂, hN₂₁, fromBlocks_multiply]
        simp
      rw [h, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]
      exact ⟨rfl, rfl⟩
    · left
      have h : ((M * N : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          fromBlocks ((M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂ *
            (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁) 0 0
            ((M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁ *
              (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂) := by
        rw [Units.val_mul, ← fromBlocks_toBlocks (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
          hM₁₁, hM₂₂, ← fromBlocks_toBlocks (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
          hN₁₁, hN₂₂, fromBlocks_multiply]
        simp
      rw [h, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁]
      exact ⟨rfl, rfl⟩
  one_mem' := by
    left
    have hone : ((1 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := rfl
    rw [hone, ← fromBlocks_one, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁]
    exact ⟨rfl, rfl⟩
  inv_mem' := by
    intro g hg
    have hge : IsPlaneMonomial (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := hg
    set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
    set M' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
      ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM'
    change IsPlaneMonomial M'
    have hMe : IsPlaneMonomial M := by rw [hM]; exact hge
    have hmul : M * M' = 1 := by
      rw [hM, hM', ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hmul' : M' * M = 1 := by
      rw [hM, hM', ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hM'eq : M' = fromBlocks M'.toBlocks₁₁ M'.toBlocks₁₂ M'.toBlocks₂₁ M'.toBlocks₂₂ :=
      (fromBlocks_toBlocks M').symm
    rcases hMe with ⟨h₁₂, h₂₁⟩ | ⟨h₁₁, h₂₂⟩
    · have hMeq : M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
        have h := (fromBlocks_toBlocks M).symm
        rw [h₁₂, h₂₁] at h
        exact h
      have hp : M.toBlocks₁₁ * M'.toBlocks₁₁ = 1 ∧ M.toBlocks₁₁ * M'.toBlocks₁₂ = 0 ∧
          M.toBlocks₂₂ * M'.toBlocks₂₁ = 0 ∧ M.toBlocks₂₂ * M'.toBlocks₂₂ = 1 := by
        have h := hmul
        rw [hMeq, hM'eq, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h
        simpa only [mul_zero, zero_mul, add_zero, zero_add] using h
      have hp' : M'.toBlocks₁₁ * M.toBlocks₁₁ = 1 ∧ M'.toBlocks₁₂ * M.toBlocks₂₂ = 0 ∧
          M'.toBlocks₂₁ * M.toBlocks₁₁ = 0 ∧ M'.toBlocks₂₂ * M.toBlocks₂₂ = 1 := by
        have h := hmul'
        rw [hM'eq, hMeq, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h
        simpa only [mul_zero, zero_mul, add_zero, zero_add] using h
      have hB : M'.toBlocks₁₂ = 0 := by
        calc M'.toBlocks₁₂ = (M'.toBlocks₁₁ * M.toBlocks₁₁) * M'.toBlocks₁₂ := by
              rw [hp'.1, one_mul]
          _ = M'.toBlocks₁₁ * (M.toBlocks₁₁ * M'.toBlocks₁₂) := by rw [mul_assoc]
          _ = 0 := by rw [hp.2.1, mul_zero]
      have hC : M'.toBlocks₂₁ = 0 := by
        calc M'.toBlocks₂₁ = (M'.toBlocks₂₂ * M.toBlocks₂₂) * M'.toBlocks₂₁ := by
              rw [hp'.2.2.2, one_mul]
          _ = M'.toBlocks₂₂ * (M.toBlocks₂₂ * M'.toBlocks₂₁) := by rw [mul_assoc]
          _ = 0 := by rw [hp.2.2.1, mul_zero]
      left
      rw [hM'eq, hB, hC, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁]
      exact ⟨rfl, rfl⟩
    · have hMeq : M = fromBlocks 0 M.toBlocks₁₂ M.toBlocks₂₁ 0 := by
        have h := (fromBlocks_toBlocks M).symm
        rw [h₁₁, h₂₂] at h
        exact h
      have hp : M.toBlocks₁₂ * M'.toBlocks₂₁ = 1 ∧ M.toBlocks₁₂ * M'.toBlocks₂₂ = 0 ∧
          M.toBlocks₂₁ * M'.toBlocks₁₁ = 0 ∧ M.toBlocks₂₁ * M'.toBlocks₁₂ = 1 := by
        have h := hmul
        rw [hMeq, hM'eq, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h
        simpa only [mul_zero, zero_mul, add_zero, zero_add] using h
      have hp' : M'.toBlocks₁₂ * M.toBlocks₂₁ = 1 ∧ M'.toBlocks₁₁ * M.toBlocks₁₂ = 0 ∧
          M'.toBlocks₂₂ * M.toBlocks₂₁ = 0 ∧ M'.toBlocks₂₁ * M.toBlocks₁₂ = 1 := by
        have h := hmul'
        rw [hM'eq, hMeq, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h
        simpa only [mul_zero, zero_mul, add_zero, zero_add] using h
      have hA : M'.toBlocks₁₁ = 0 := by
        calc M'.toBlocks₁₁ = M'.toBlocks₁₁ * (M.toBlocks₁₂ * M'.toBlocks₂₁) := by
              rw [hp.1, mul_one]
          _ = (M'.toBlocks₁₁ * M.toBlocks₁₂) * M'.toBlocks₂₁ := by rw [mul_assoc]
          _ = 0 := by rw [hp'.2.1, zero_mul]
      have hD : M'.toBlocks₂₂ = 0 := by
        calc M'.toBlocks₂₂ = M'.toBlocks₂₂ * (M.toBlocks₂₁ * M'.toBlocks₁₂) := by
              rw [hp.2.2.2, mul_one]
          _ = (M'.toBlocks₂₂ * M.toBlocks₂₁) * M'.toBlocks₁₂ := by rw [mul_assoc]
          _ = 0 := by rw [hp'.2.2.1, zero_mul]
      right
      rw [hM'eq, hA, hD, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]
      exact ⟨rfl, rfl⟩

theorem mem_planeMonomial {g : GL (Fin 2 ⊕ Fin 2) K} :
    g ∈ planeMonomial K ↔ IsPlaneMonomial (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
  Iff.rfl

private theorem adjoin_quatHom_eq_top (hK : ringChar K ≠ 2) {a b : K}
    (h : a ^ 2 + b ^ 2 = -1) :
    Algebra.adjoin K (Set.range fun q : QuaternionGroup 2 =>
      (quatHom h q : Matrix (Fin 2) (Fin 2) K)) = ⊤ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  let S : Subalgebra K (Matrix (Fin 2) (Fin 2) K) :=
    Algebra.adjoin K (Set.range fun q : QuaternionGroup 2 =>
      (quatHom h q : Matrix (Fin 2) (Fin 2) K))
  have hmem : ∀ q : QuaternionGroup 2, (quatHom h q : Matrix (Fin 2) (Fin 2) K) ∈ S :=
    fun q => Algebra.subset_adjoin (Set.mem_range_self q)
  have h1 : (1 : Matrix (Fin 2) (Fin 2) K) ∈ S := S.one_mem
  have hI : quatI K ∈ S := by rw [← quatHom_a_one h]; exact hmem _
  have hJ : quatJ a b ∈ S := by rw [← quatHom_xa_zero h]; exact hmem _
  have hIJ : quatI K * quatJ a b ∈ S := by rw [← quatHom_xa_three h]; exact hmem _
  have hD : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
    have hcomb : a • quatJ a b + b • (quatI K * quatJ a b) = -!![1, 0; 0, -1] := by
      rw [quatI_mul_quatJ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [quatJ]
      all_goals first
        | linear_combination h
        | linear_combination -h
        | ring
    rw [show (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) K) =
      -(a • quatJ a b + b • (quatI K * quatJ a b)) by rw [hcomb, neg_neg]]
    exact S.neg_mem (S.add_mem (S.smul_mem hJ a) (S.smul_mem hIJ b))
  have hS : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
    have hcomb : a • (quatI K * quatJ a b) - b • quatJ a b = !![0, 1; 1, 0] := by
      rw [quatI_mul_quatJ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [quatJ]
      all_goals first
        | linear_combination h
        | linear_combination -h
        | ring
    rw [← hcomb]
    exact S.sub_mem (S.smul_mem hIJ a) (S.smul_mem hJ b)
  have hE00 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
    have hEq : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) =
        (2⁻¹ : K) • ((1 : Matrix (Fin 2) (Fin 2) K) + !![1, 0; 0, -1]) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, one_add_one_eq_two, inv_mul_cancel₀ h2]
    rw [hEq]
    exact S.smul_mem (S.add_mem h1 hD) 2⁻¹
  have hE11 : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
    have hEq : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) =
        (2⁻¹ : K) • ((1 : Matrix (Fin 2) (Fin 2) K) - !![1, 0; 0, -1]) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, one_add_one_eq_two, inv_mul_cancel₀ h2]
    rw [hEq]
    exact S.smul_mem (S.sub_mem h1 hD) 2⁻¹
  have hE01 : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
    have hEq : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) K) =
        (2⁻¹ : K) • ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) + quatI K) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, quatI, one_add_one_eq_two, inv_mul_cancel₀ h2]
    rw [hEq]
    exact S.smul_mem (S.add_mem hS hI) 2⁻¹
  have hE10 : (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) K) ∈ S := by
    have hEq : (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) K) =
        (2⁻¹ : K) • ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) - quatI K) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, quatI, one_add_one_eq_two, inv_mul_cancel₀ h2]
    rw [hEq]
    exact S.smul_mem (S.sub_mem hS hI) 2⁻¹
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro X _
    have hX : X = X 0 0 • !![1, 0; 0, 0] + X 0 1 • !![0, 1; 0, 0] +
        X 1 0 • !![0, 0; 1, 0] + X 1 1 • !![0, 0; 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [hX]
    exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem hE00 _) (S.smul_mem hE01 _))
      (S.smul_mem hE10 _)) (S.smul_mem hE11 _)
  exact htop

private theorem glRep_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Type*) [Field L]
    [Algebra K L] (x y : GL ι K) : glRep L (x * y) = glRep L x * glRep L y := by
  refine LinearMap.ext fun u => funext fun i => ?_
  change (glRep L (x * y) u) i = (glRep L x (glRep L y u)) i
  rw [glRep_apply, glRep_apply, glRep_apply, Units.val_mul, Matrix.map_mul,
    Matrix.mulVec_mulVec]

private theorem glRep_one {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Type*) [Field L]
    [Algebra K L] : glRep L (1 : GL ι K) = 1 := by
  refine LinearMap.ext fun u => funext fun i => ?_
  change (glRep L (1 : GL ι K) u) i = u i
  rw [glRep_apply, Units.val_one, Matrix.map_one (algebraMap K L) (map_zero _) (map_one _),
    Matrix.one_mulVec]

private theorem glRep_unit_injective {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Type*)
    [Field L] [Algebra K L] (x : GL ι K) : Function.Injective (glRep L x) := by
  have hcomp : glRep L x⁻¹ * glRep L x = 1 := by
    rw [← glRep_mul, inv_mul_cancel, glRep_one]
  have hleft : Function.LeftInverse (glRep L x⁻¹) (glRep L x) := by
    intro u
    have h := congrArg (fun f : (ι → L) →ₗ[L] (ι → L) => f u) hcomp
    exact h
  exact hleft.injective

private theorem apply_apply_eq_of_card_two {κ : Type*} (hκ : Nat.card κ = 2)
    {σ : κ → κ} (hσ : Function.Injective σ) (i : κ) : σ (σ i) = i := by
  obtain ⟨j, hji, hju⟩ := (Nat.card_eq_two_iff' i).mp hκ
  have h_only : ∀ z : κ, z = i ∨ z = j := by
    intro z
    by_cases hz : z = i
    · exact Or.inl hz
    · exact Or.inr (hju z hz)
  rcases h_only (σ i) with h1 | h1
  · rw [h1, h1]
  · rcases h_only (σ j) with h2 | h2
    · rw [h1, h2]
    · exact absurd (hσ (h1.trans h2.symm)) (Ne.symm hji)

private theorem map_sq_eq_self {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (L : Type*) [Field L] [Algebra K L] {κ : Type*}
    {W : κ → Submodule L ((Fin 2 ⊕ Fin 2) → L)} (hind : iSupIndep W) (hW0 : ∀ i, W i ≠ ⊥)
    (hκ : Nat.card κ = 2) (hperm : ∀ x ∈ planeP0 h, ∀ i, ∃ j, (W i).map (glRep L x) = W j)
    {x : GL (Fin 2 ⊕ Fin 2) K} (hx : x ∈ planeP0 h) (i : κ) :
    (W i).map (glRep L (x * x)) = W i := by
  have hWinj : Function.Injective W := hind.injective hW0
  let σ : κ → κ := fun i => Classical.choose (hperm x hx i)
  have hσ : ∀ i, (W i).map (glRep L x) = W (σ i) := fun i => Classical.choose_spec (hperm x hx i)
  have hσinj : Function.Injective σ := by
    intro i j hij
    have hm : (W i).map (glRep L x) = (W j).map (glRep L x) := by rw [hσ i, hσ j, hij]
    exact hWinj (Submodule.map_injective_of_injective (glRep_unit_injective L x) hm)
  have hsq : σ (σ i) = i := apply_apply_eq_of_card_two hκ hσinj i
  calc (W i).map (glRep L (x * x))
      = (W i).map (glRep L x * glRep L x) := by rw [glRep_mul]
    _ = ((W i).map (glRep L x)).map (glRep L x) :=
        Submodule.map_comp (glRep L x) (glRep L x) (W i)
    _ = (W (σ i)).map (glRep L x) := by rw [hσ i]
    _ = W (σ (σ i)) := hσ (σ i)
    _ = W i := by rw [hsq]

private theorem fromBlocks_diag_mulVec_apply_inl {L : Type*} [Field L]
    (A : Matrix (Fin 2) (Fin 2) L) (u : (Fin 2 ⊕ Fin 2) → L) (k : Fin 2) :
    (fromBlocks A 0 0 A *ᵥ u) (Sum.inl k) = (A *ᵥ (u ∘ Sum.inl)) k := by
  rw [Matrix.fromBlocks_mulVec]
  simp

private theorem fromBlocks_diag_mulVec_apply_inr {L : Type*} [Field L]
    (A : Matrix (Fin 2) (Fin 2) L) (u : (Fin 2 ⊕ Fin 2) → L) (k : Fin 2) :
    (fromBlocks A 0 0 A *ᵥ u) (Sum.inr k) = (A *ᵥ (u ∘ Sum.inr)) k := by
  rw [Matrix.fromBlocks_mulVec]
  simp

private theorem glRep_planeQuat_z_apply {a b : K} (h : a ^ 2 + b ^ 2 = -1) (L : Type*)
    [Field L] [Algebra K L] (u : (Fin 2 ⊕ Fin 2) → L) :
    glRep L (planeQuat h (.a 2, 1)) u =
      Sum.elim (fun k => -u (Sum.inl k)) (fun k => u (Sum.inr k)) := by
  have hmap : (((planeQuat h (.a 2, 1) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map (algebraMap K L)) =
      fromBlocks (-1 : Matrix (Fin 2) (Fin 2) L) 0 0 (1 : Matrix (Fin 2) (Fin 2) L) := by
    rw [coe_planeQuat_z, Matrix.fromBlocks_map,
      show (-1 : Matrix (Fin 2) (Fin 2) K) = -(1 : Matrix (Fin 2) (Fin 2) K) from rfl,
      Matrix.map_neg _ (map_neg _),
      Matrix.map_one (algebraMap K L) (map_zero _) (map_one _)]
    simp
  rw [glRep_apply, hmap, Matrix.fromBlocks_mulVec]
  funext p
  rcases p with k | k <;> fin_cases k <;> simp [Matrix.neg_mulVec]

private theorem glRep_planeQuat_diag_mem_planeFst {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (L : Type*) [Field L] [Algebra K L] (q : QuaternionGroup 2)
    {u : (Fin 2 ⊕ Fin 2) → L} (hu : u ∈ planeFst L) :
    glRep L (planeQuat h (q, q)) u ∈ planeFst L := by
  rw [mem_planeFst_iff] at hu ⊢
  have hz : (u ∘ Sum.inr) = 0 := funext hu
  have hmap : (((planeQuat h (q, q) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map (algebraMap K L)) =
      fromBlocks (((quatHom h q : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).map (algebraMap K L)) 0 0
        (((quatHom h q : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).map (algebraMap K L)) := by
    rw [coe_planeQuat h (q, q), Matrix.fromBlocks_map]
    simp
  intro k
  rw [glRep_apply, hmap, fromBlocks_diag_mulVec_apply_inr, hz]
  simp

private theorem glRep_planeQuat_diag_mem_planeSnd {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (L : Type*) [Field L] [Algebra K L] (q : QuaternionGroup 2)
    {u : (Fin 2 ⊕ Fin 2) → L} (hu : u ∈ planeSnd L) :
    glRep L (planeQuat h (q, q)) u ∈ planeSnd L := by
  rw [mem_planeSnd_iff] at hu ⊢
  have hz : (u ∘ Sum.inl) = 0 := funext hu
  have hmap : (((planeQuat h (q, q) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map (algebraMap K L)) =
      fromBlocks (((quatHom h q : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).map (algebraMap K L)) 0 0
        (((quatHom h q : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).map (algebraMap K L)) := by
    rw [coe_planeQuat h (q, q), Matrix.fromBlocks_map]
    simp
  intro k
  rw [glRep_apply, hmap, fromBlocks_diag_mulVec_apply_inl, hz]
  simp

private theorem planeFst_inf_planeSnd (L : Type*) [Field L] :
    planeFst L ⊓ planeSnd L = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hu
  rw [mem_planeFst_iff] at h1
  rw [mem_planeSnd_iff] at h2
  funext p
  rcases p with k | k
  · exact h2 k
  · exact h1 k

private theorem planeFst_sup_planeSnd (L : Type*) [Field L] :
    planeFst L ⊔ planeSnd L = ⊤ := by
  rw [eq_top_iff]
  intro u _
  refine Submodule.mem_sup.mpr
    ⟨Sum.elim (u ∘ Sum.inl) 0, ?_, Sum.elim 0 (u ∘ Sum.inr), ?_, ?_⟩
  · rw [mem_planeFst_iff]
    intro k
    simp
  · rw [mem_planeSnd_iff]
    intro k
    simp
  · funext p
    rcases p with k | k <;> simp

private theorem inf_planeFst_eq_bot_or_eq (hK : ringChar K ≠ 2) {a b : K}
    (h : a ^ 2 + b ^ 2 = -1) (L : Type*) [Field L] [Algebra K L]
    {U : Submodule L ((Fin 2 ⊕ Fin 2) → L)} (hUle : U ≤ planeFst L)
    (hU : ∀ q : QuaternionGroup 2, ∀ u ∈ U, glRep L (planeQuat h (q, q)) u ∈ U) :
    U = ⊥ ∨ U = planeFst L := by
  let φ : ((Fin 2 ⊕ Fin 2) → L) →ₗ[L] (Fin 2 → L) := LinearMap.funLeft L L Sum.inl
  let V : Submodule L (Fin 2 → L) := U.map φ
  have hdiag : ∀ q : QuaternionGroup 2,
      (((planeQuat h (q, q) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map (algebraMap K L)) =
        fromBlocks (((quatHom h q : SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K).map (algebraMap K L)) 0 0
          (((quatHom h q : SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K).map (algebraMap K L)) := by
    intro q
    rw [coe_planeQuat h (q, q), Matrix.fromBlocks_map]
    simp
  have hVinv : ∀ q : QuaternionGroup 2, ∀ v ∈ V,
      glRep L (SpecialLinearGroup.toGL (quatHom h q)) v ∈ V := by
    intro q v hv
    rw [Submodule.mem_map] at hv ⊢
    obtain ⟨u, hu, rfl⟩ := hv
    refine ⟨glRep L (planeQuat h (q, q)) u, hU q u hu, ?_⟩
    funext k
    rw [show φ (glRep L (planeQuat h (q, q)) u) k =
        (glRep L (planeQuat h (q, q)) u) (Sum.inl k) from rfl,
      glRep_apply, hdiag q, fromBlocks_diag_mulVec_apply_inl, glRep_apply]
    rfl
  have hf : Algebra.adjoin K (Set.range fun q : QuaternionGroup 2 =>
      (SpecialLinearGroup.toGL (quatHom h q) : Matrix (Fin 2) (Fin 2) K)) = ⊤ := by
    simpa using adjoin_quatHom_eq_top hK h
  rcases eq_bot_or_eq_top_of_adjoin_eq_top (fun q => SpecialLinearGroup.toGL (quatHom h q)) hf L V
    hVinv with hVbot | hVtop
  · left
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hmem : φ u ∈ V := Submodule.mem_map_of_mem hu
    rw [hVbot] at hmem
    have hS : u ∈ planeSnd L := by
      rw [planeSnd, LinearMap.mem_ker]
      simpa using ((Submodule.mem_bot L).mp hmem)
    have hboth : u ∈ planeFst L ⊓ planeSnd L := ⟨hUle hu, hS⟩
    rw [planeFst_inf_planeSnd L] at hboth
    exact (Submodule.mem_bot L).mp hboth
  · right
    refine le_antisymm hUle ?_
    intro x hx
    have hmem : φ x ∈ V := by rw [hVtop]; exact Submodule.mem_top
    rw [Submodule.mem_map] at hmem
    obtain ⟨u, hu, hφu⟩ := hmem
    have hsub : x - u = 0 := by
      have hker : x - u ∈ planeSnd L := by
        rw [planeSnd, LinearMap.mem_ker]
        show φ (x - u) = 0
        rw [map_sub, hφu, sub_self]
      have hboth : x - u ∈ planeFst L ⊓ planeSnd L := ⟨Submodule.sub_mem (planeFst L) hx (hUle hu), hker⟩
      rw [planeFst_inf_planeSnd L] at hboth
      exact (Submodule.mem_bot L).mp hboth
    rw [sub_eq_zero.mp hsub]
    exact hu

private theorem inf_planeSnd_eq_bot_or_eq (hK : ringChar K ≠ 2) {a b : K}
    (h : a ^ 2 + b ^ 2 = -1) (L : Type*) [Field L] [Algebra K L]
    {U : Submodule L ((Fin 2 ⊕ Fin 2) → L)} (hUle : U ≤ planeSnd L)
    (hU : ∀ q : QuaternionGroup 2, ∀ u ∈ U, glRep L (planeQuat h (q, q)) u ∈ U) :
    U = ⊥ ∨ U = planeSnd L := by
  let φ : ((Fin 2 ⊕ Fin 2) → L) →ₗ[L] (Fin 2 → L) := LinearMap.funLeft L L Sum.inr
  let V : Submodule L (Fin 2 → L) := U.map φ
  have hdiag : ∀ q : QuaternionGroup 2,
      (((planeQuat h (q, q) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map (algebraMap K L)) =
        fromBlocks (((quatHom h q : SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K).map (algebraMap K L)) 0 0
          (((quatHom h q : SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K).map (algebraMap K L)) := by
    intro q
    rw [coe_planeQuat h (q, q), Matrix.fromBlocks_map]
    simp
  have hVinv : ∀ q : QuaternionGroup 2, ∀ v ∈ V,
      glRep L (SpecialLinearGroup.toGL (quatHom h q)) v ∈ V := by
    intro q v hv
    rw [Submodule.mem_map] at hv ⊢
    obtain ⟨u, hu, rfl⟩ := hv
    refine ⟨glRep L (planeQuat h (q, q)) u, hU q u hu, ?_⟩
    funext k
    rw [show φ (glRep L (planeQuat h (q, q)) u) k =
        (glRep L (planeQuat h (q, q)) u) (Sum.inr k) from rfl,
      glRep_apply, hdiag q, fromBlocks_diag_mulVec_apply_inr, glRep_apply]
    rfl
  have hf : Algebra.adjoin K (Set.range fun q : QuaternionGroup 2 =>
      (SpecialLinearGroup.toGL (quatHom h q) : Matrix (Fin 2) (Fin 2) K)) = ⊤ := by
    simpa using adjoin_quatHom_eq_top hK h
  rcases eq_bot_or_eq_top_of_adjoin_eq_top (fun q => SpecialLinearGroup.toGL (quatHom h q)) hf L V
    hVinv with hVbot | hVtop
  · left
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hmem : φ u ∈ V := Submodule.mem_map_of_mem hu
    rw [hVbot] at hmem
    have hS : u ∈ planeFst L := by
      rw [planeFst, LinearMap.mem_ker]
      simpa using ((Submodule.mem_bot L).mp hmem)
    have hboth : u ∈ planeFst L ⊓ planeSnd L := ⟨hS, hUle hu⟩
    rw [planeFst_inf_planeSnd L] at hboth
    exact (Submodule.mem_bot L).mp hboth
  · right
    refine le_antisymm hUle ?_
    intro x hx
    have hmem : φ x ∈ V := by rw [hVtop]; exact Submodule.mem_top
    rw [Submodule.mem_map] at hmem
    obtain ⟨u, hu, hφu⟩ := hmem
    have hsub : x - u = 0 := by
      have hker : x - u ∈ planeFst L := by
        rw [planeFst, LinearMap.mem_ker]
        show φ (x - u) = 0
        rw [map_sub, hφu, sub_self]
      have hboth : x - u ∈ planeFst L ⊓ planeSnd L :=
        ⟨hker, Submodule.sub_mem (planeSnd L) hx (hUle hu)⟩
      rw [planeFst_inf_planeSnd L] at hboth
      exact (Submodule.mem_bot L).mp hboth
    rw [sub_eq_zero.mp hsub]
    exact hu

theorem eq_planeFst_or_eq_planeSnd (hK : ringChar K ≠ 2) {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    (L : Type*) [Field L] [Algebra K L] {κ : Type*}
    {W : κ → Submodule L ((Fin 2 ⊕ Fin 2) → L)} (hind : iSupIndep W) (hW0 : ∀ i, W i ≠ ⊥)
    (hκ : Nat.card κ = 2) (hperm : ∀ x ∈ planeP0 h, ∀ i, ∃ j, (W i).map (glRep L x) = W j)
    (i : κ) : W i = planeFst L ∨ W i = planeSnd L := by
  have hfixz : (W i).map (glRep L (planeQuat h (.a 2, 1))) = W i := by
    have hsq : planeQuat h (.a 1, 1) * planeQuat h (.a 1, 1) = planeQuat h (.a 2, 1) := by
      rw [← map_mul]
      congr 1
    rw [← hsq]
    exact map_sq_eq_self h L hind hW0 hκ hperm (planeQuat_mem_planeP0 h (.a 1, 1)) i
  have hfixq : ∀ q : QuaternionGroup 2, (W i).map (glRep L (planeQuat h (q, q))) = W i := by
    intro q
    have hsq : (planeSwap * planeQuat h (q, 1)) ^ 2 = planeQuat h (q, q) := by
      rw [pow_two]
      have hss : (planeSwap : GL (Fin 2 ⊕ Fin 2) K)⁻¹ = planeSwap :=
        inv_eq_of_mul_eq_one_right planeSwap_mul_self
      have hconj : planeSwap * planeQuat h (q, 1) * planeSwap = planeQuat h (q, 1).swap := by
        have h := planeSwap_conj_planeQuat h (q, 1)
        rwa [hss] at h
      calc planeSwap * planeQuat h (q, 1) * (planeSwap * planeQuat h (q, 1))
          = (planeSwap * planeQuat h (q, 1) * planeSwap) * planeQuat h (q, 1) := by group
        _ = planeQuat h (q, 1).swap * planeQuat h (q, 1) := by rw [hconj]
        _ = planeQuat h (q, q) := by
            rw [← map_mul]
            simp
    rw [← hsq, pow_two]
    exact map_sq_eq_self h L hind hW0 hκ hperm
      (mul_mem (planeSwap_mem_planeP0 h) (planeQuat_mem_planeP0 h (q, 1))) i
  have hzmem : ∀ w ∈ W i, glRep L (planeQuat h (.a 2, 1)) w ∈ W i := by
    intro w hw
    have h := Submodule.mem_map_of_mem (f := glRep L (planeQuat h (.a 2, 1))) hw
    rwa [hfixz] at h
  have hqmem : ∀ q, ∀ w ∈ W i, glRep L (planeQuat h (q, q)) w ∈ W i := by
    intro q w hw
    have h := Submodule.mem_map_of_mem (f := glRep L (planeQuat h (q, q))) hw
    rwa [hfixq q] at h
  have h2 : (2 : L) ≠ 0 := by
    intro h0
    apply Ring.two_ne_zero hK
    apply (algebraMap K L).injective
    rw [map_ofNat, h0, map_zero]
  have hsplit : W i = (W i ⊓ planeFst L) ⊔ (W i ⊓ planeSnd L) := by
    refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
    intro w hw
    have hzw := hzmem w hw
    refine Submodule.mem_sup.mpr ⟨(2 : L)⁻¹ • (w - glRep L (planeQuat h (.a 2, 1)) w), ?_,
      (2 : L)⁻¹ • (w + glRep L (planeQuat h (.a 2, 1)) w), ?_, ?_⟩
    · refine Submodule.mem_inf.mpr ⟨Submodule.smul_mem (W i) (2 : L)⁻¹ (Submodule.sub_mem (W i) hw hzw), ?_⟩
      rw [mem_planeFst_iff]
      intro k
      simp [glRep_planeQuat_z_apply]
    · refine Submodule.mem_inf.mpr ⟨Submodule.smul_mem (W i) (2 : L)⁻¹ (Submodule.add_mem (W i) hw hzw), ?_⟩
      rw [mem_planeSnd_iff]
      intro k
      simp [glRep_planeQuat_z_apply]
    · rw [← smul_add]
      have h2w : w - glRep L (planeQuat h (.a 2, 1)) w +
          (w + glRep L (planeQuat h (.a 2, 1)) w) = (2 : L) • w := by
        rw [two_smul]
        abel
      rw [h2w, inv_smul_smul₀ h2]
  have hU1 : W i ⊓ planeFst L = ⊥ ∨ W i ⊓ planeFst L = planeFst L := by
    refine inf_planeFst_eq_bot_or_eq hK h L inf_le_right ?_
    intro q u hu
    exact Submodule.mem_inf.mpr ⟨hqmem q u hu.1, glRep_planeQuat_diag_mem_planeFst h L q hu.2⟩
  have hU2 : W i ⊓ planeSnd L = ⊥ ∨ W i ⊓ planeSnd L = planeSnd L := by
    refine inf_planeSnd_eq_bot_or_eq hK h L inf_le_right ?_
    intro q u hu
    exact Submodule.mem_inf.mpr ⟨hqmem q u hu.1, glRep_planeQuat_diag_mem_planeSnd h L q hu.2⟩
  rcases hU1 with h1 | h1 <;> rcases hU2 with h2 | h2
  · exact absurd (by rw [hsplit, h1, h2, sup_bot_eq]) (hW0 i)
  · right
    rw [hsplit, h1, h2, bot_sup_eq]
  · left
    rw [hsplit, h1, h2, sup_bot_eq]
  · exfalso
    have htop : W i = ⊤ := by rw [hsplit, h1, h2, planeFst_sup_planeSnd L]
    obtain ⟨j, hji, -⟩ := (Nat.card_eq_two_iff' i).mp hκ
    have hle : W j ≤ ⨆ l : κ, ⨆ (_ : l ≠ j), W l := by
      calc W j ≤ ⊤ := le_top
        _ = W i := htop.symm
        _ ≤ ⨆ l : κ, ⨆ (_ : l ≠ j), W l := le_iSup_of_le i (le_iSup_of_le hji.symm le_rfl)
    have hdisj := (iSupIndep_def.mp hind) j
    have hbot : W j = ⊥ := by
      rw [← le_bot_iff]
      calc W j ≤ W j ⊓ ⨆ l : κ, ⨆ (_ : l ≠ j), W l := le_inf le_rfl hle
        _ = ⊥ := hdisj.eq_bot
    exact hW0 j hbot

private theorem single_inl_mem_planeFst {L : Type*} [Field L] (j : Fin 2) :
    (Pi.single (Sum.inl j) (1 : L) : (Fin 2 ⊕ Fin 2) → L) ∈ planeFst L := by
  rw [mem_planeFst_iff]
  intro k
  exact Pi.single_eq_of_ne (by simp) 1

private theorem single_inr_mem_planeSnd {L : Type*} [Field L] (j : Fin 2) :
    (Pi.single (Sum.inr j) (1 : L) : (Fin 2 ⊕ Fin 2) → L) ∈ planeSnd L := by
  rw [mem_planeSnd_iff]
  intro k
  exact Pi.single_eq_of_ne (by simp) 1

private theorem algebraMap_entry_eq_zero_of_mapsTo {L : Type*} [Field L] [Algebra K L]
    (g : GL (Fin 2 ⊕ Fin 2) K) {s t : Fin 2 ⊕ Fin 2}
    {P Q : Submodule L ((Fin 2 ⊕ Fin 2) → L)}
    (hP : (Pi.single t (1 : L) : (Fin 2 ⊕ Fin 2) → L) ∈ P)
    (hQ : ∀ v ∈ Q, v s = 0)
    (h : ∀ v ∈ P, glRep L g v ∈ Q) :
    algebraMap K L ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) s t) = 0 := by
  have hm : glRep L g (Pi.single t (1 : L) : (Fin 2 ⊕ Fin 2) → L) ∈ Q := h _ hP
  have hcoord : (glRep L g (Pi.single t (1 : L) : (Fin 2 ⊕ Fin 2) → L)) s = 0 := hQ _ hm
  rw [glRep_apply] at hcoord
  simpa [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply] using hcoord

private theorem toBlocks₂₁_eq_zero_of_planeFst {L : Type*} [Field L] [Algebra K L]
    (g : GL (Fin 2 ⊕ Fin 2) K)
    (h : ∀ v ∈ planeFst L, glRep L g v ∈ planeFst L) :
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁ = 0 := by
  ext i j
  exact (algebraMap K L).injective (by
    simpa [Matrix.toBlocks₂₁, Matrix.submatrix_apply] using algebraMap_entry_eq_zero_of_mapsTo (K := K) g (s := Sum.inr i) (t := Sum.inl j)
      (single_inl_mem_planeFst j) (fun v hv => (mem_planeFst_iff v).mp hv i) h)

private theorem toBlocks₁₂_eq_zero_of_planeSnd {L : Type*} [Field L] [Algebra K L]
    (g : GL (Fin 2 ⊕ Fin 2) K)
    (h : ∀ v ∈ planeSnd L, glRep L g v ∈ planeSnd L) :
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂ = 0 := by
  ext i j
  exact (algebraMap K L).injective (by
    simpa [Matrix.toBlocks₁₂, Matrix.submatrix_apply] using algebraMap_entry_eq_zero_of_mapsTo (K := K) g (s := Sum.inl i) (t := Sum.inr j)
      (single_inr_mem_planeSnd j) (fun v hv => (mem_planeSnd_iff v).mp hv i) h)

private theorem toBlocks₁₁_eq_zero_of_planeFst_to_planeSnd {L : Type*} [Field L] [Algebra K L]
    (g : GL (Fin 2 ⊕ Fin 2) K)
    (h : ∀ v ∈ planeFst L, glRep L g v ∈ planeSnd L) :
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁ = 0 := by
  ext i j
  exact (algebraMap K L).injective (by
    simpa [Matrix.toBlocks₁₁, Matrix.submatrix_apply] using algebraMap_entry_eq_zero_of_mapsTo (K := K) g (s := Sum.inl i) (t := Sum.inl j)
      (single_inl_mem_planeFst j) (fun v hv => (mem_planeSnd_iff v).mp hv i) h)

private theorem toBlocks₂₂_eq_zero_of_planeSnd_to_planeFst {L : Type*} [Field L] [Algebra K L]
    (g : GL (Fin 2 ⊕ Fin 2) K)
    (h : ∀ v ∈ planeSnd L, glRep L g v ∈ planeFst L) :
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂ = 0 := by
  ext i j
  exact (algebraMap K L).injective (by
    simpa [Matrix.toBlocks₂₂, Matrix.submatrix_apply] using algebraMap_entry_eq_zero_of_mapsTo (K := K) g (s := Sum.inr i) (t := Sum.inr j)
      (single_inr_mem_planeSnd j) (fun v hv => (mem_planeFst_iff v).mp hv i) h)

theorem mem_planeMonomial_of_map (L : Type*) [Field L] [Algebra K L]
    (g : GL (Fin 2 ⊕ Fin 2) K)
    (hg : ((planeFst L).map (glRep L g) = planeFst L ∧
        (planeSnd L).map (glRep L g) = planeSnd L) ∨
      ((planeFst L).map (glRep L g) = planeSnd L ∧
        (planeSnd L).map (glRep L g) = planeFst L)) :
    g ∈ planeMonomial K := by
  rw [mem_planeMonomial]
  rcases hg with ⟨hf, hs⟩ | ⟨hf, hs⟩
  · left
    exact ⟨toBlocks₁₂_eq_zero_of_planeSnd g
        (fun v hv => by rw [← hs]; exact Submodule.mem_map_of_mem hv),
      toBlocks₂₁_eq_zero_of_planeFst g
        (fun v hv => by rw [← hf]; exact Submodule.mem_map_of_mem hv)⟩
  · right
    exact ⟨toBlocks₁₁_eq_zero_of_planeFst_to_planeSnd g
        (fun v hv => by rw [← hf]; exact Submodule.mem_map_of_mem hv),
      toBlocks₂₂_eq_zero_of_planeSnd_to_planeFst g
        (fun v hv => by rw [← hs]; exact Submodule.mem_map_of_mem hv)⟩

theorem glRep_reindexGL_apply {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι ≃ ι') (L : Type*) [Field L] [Algebra K L] (g : GL ι K)
    (v : ι' → L) : glRep L (e.reindexGL K g) v = (glRep L g (v ∘ e)) ∘ e.symm := by
  rw [glRep_apply, glRep_apply, Equiv.coe_reindexGL, ← Matrix.submatrix_map]
  ext j
  simp only [Matrix.mulVec_apply, dotProduct, Matrix.row, Matrix.submatrix_apply,
    Matrix.map_apply, Function.comp_apply]
  exact Fintype.sum_equiv e.symm
    (fun i' => algebraMap K L ((g : Matrix ι ι K) (e.symm j) (e.symm i')) * v i')
    (fun i => algebraMap K L ((g : Matrix ι ι K) (e.symm j) i) * v (e i))
    (by intro i'; simp)

private theorem planeFst_ne_planeSnd (L : Type*) [Field L] : planeFst L ≠ planeSnd L := by
  intro hEq
  have hmem : (Pi.single (Sum.inl 0) (1 : L) : (Fin 2 ⊕ Fin 2) → L) ∈ planeFst L :=
    single_inl_mem_planeFst 0
  rw [hEq] at hmem
  have h0 := (mem_planeSnd_iff _).mp hmem 0
  simp at h0

theorem symm_reindexGL_mem_planeMonomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Fin 2 ⊕ Fin 2 ≃ ι) (hK : ringChar K ≠ 2) {a b : K} (h : a ^ 2 + b ^ 2 = -1)
    {H : Subgroup (GL ι K)} (hP0 : (planeP0 h).map (e.reindexGL K).toMonoidHom ≤ H)
    (L : Type*) [Field L] [Algebra K L] {κ : Type*} {W : κ → Submodule L (ι → L)}
    (hind : iSupIndep W) (hW0 : ∀ i, W i ≠ ⊥) (hκ : Nat.card κ = 2)
    (hperm : ∀ x ∈ H, ∀ i, ∃ j, (W i).map (glRep L x) = W j) {x : GL ι K} (hx : x ∈ H) :
    (e.reindexGL K).symm x ∈ planeMonomial K := by
  set y : GL (Fin 2 ⊕ Fin 2) K := (e.reindexGL K).symm x with hy
  have hxy : e.reindexGL K y = x := by
    rw [hy]
    exact (e.reindexGL K).apply_symm_apply x
  let Ψ : (ι → L) ≃ₗ[L] ((Fin 2 ⊕ Fin 2) → L) := LinearEquiv.funCongrLeft L L e
  let W' : κ → Submodule L ((Fin 2 ⊕ Fin 2) → L) := fun i => (W i).map Ψ.toLinearMap
  have hinter : ∀ (u : GL ι K) (v : GL (Fin 2 ⊕ Fin 2) K), e.reindexGL K v = u →
      Ψ.toLinearMap.comp (glRep L u) = (glRep L v).comp Ψ.toLinearMap := by
    intro u v huv
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    have hh := glRep_reindexGL_apply (K := K) e L v w
    rw [huv] at hh
    rw [hh]
    funext i
    change (glRep L v (w ∘ ⇑e)) (⇑e.symm (⇑e i)) = (glRep L v (w ∘ ⇑e)) i
    simp
  have hInd : iSupIndep W' := by
    have hmap := iSupIndep.map_orderIso (Submodule.orderIsoMapComap Ψ) hind
    simpa [W', Submodule.orderIsoMapComap_apply, Function.comp_def] using hmap
  have hW'0 : ∀ i, W' i ≠ ⊥ := by
    intro i hi
    exact hW0 i (Submodule.map_eq_bot_iff.mp hi)
  have hperm' : ∀ z ∈ planeP0 h, ∀ i, ∃ j, (W' i).map (glRep L z) = W' j := by
    intro z hz i
    have hzH : e.reindexGL K z ∈ H :=
      hP0 (Subgroup.mem_map_of_mem (e.reindexGL K).toMonoidHom hz)
    obtain ⟨j, hj⟩ := hperm (e.reindexGL K z) hzH i
    refine ⟨j, ?_⟩
    have hcz := hinter (e.reindexGL K z) z rfl
    calc (W' i).map (glRep L z)
        = ((W i).map Ψ.toLinearMap).map (glRep L z) := rfl
      _ = (W i).map ((glRep L z).comp Ψ.toLinearMap) :=
          (Submodule.map_comp Ψ.toLinearMap (glRep L z) (W i)).symm
      _ = (W i).map (Ψ.toLinearMap.comp (glRep L (e.reindexGL K z))) := by rw [← hcz]
      _ = ((W i).map (glRep L (e.reindexGL K z))).map Ψ.toLinearMap :=
          Submodule.map_comp (glRep L (e.reindexGL K z)) Ψ.toLinearMap (W i)
      _ = (W j).map Ψ.toLinearMap := by rw [hj]
      _ = W' j := rfl
  have hclass : ∀ i, W' i = planeFst L ∨ W' i = planeSnd L := fun i =>
    eq_planeFst_or_eq_planeSnd hK h L hInd hW'0 hκ hperm' i
  have hpermy : ∀ i, ∃ j, (W' i).map (glRep L y) = W' j := by
    intro i
    obtain ⟨j, hj⟩ := hperm x hx i
    refine ⟨j, ?_⟩
    have hcy := hinter x y hxy
    calc (W' i).map (glRep L y)
        = ((W i).map Ψ.toLinearMap).map (glRep L y) := rfl
      _ = (W i).map ((glRep L y).comp Ψ.toLinearMap) :=
          (Submodule.map_comp Ψ.toLinearMap (glRep L y) (W i)).symm
      _ = (W i).map (Ψ.toLinearMap.comp (glRep L x)) := by rw [← hcy]
      _ = ((W i).map (glRep L x)).map Ψ.toLinearMap :=
          Submodule.map_comp (glRep L x) Ψ.toLinearMap (W i)
      _ = (W j).map Ψ.toLinearMap := by rw [hj]
      _ = W' j := rfl
  obtain ⟨i₀, i₁, hi₀₁, -⟩ := Nat.card_eq_two_iff.mp hκ
  have hdistinct : W' i₀ ≠ W' i₁ := by
    intro hEq
    exact hi₀₁ (hind.injective hW0 (Submodule.map_injective_of_injective Ψ.injective hEq))
  obtain ⟨iF, hF⟩ : ∃ i, W' i = planeFst L := by
    rcases hclass i₀ with h0 | h0
    · exact ⟨i₀, h0⟩
    · rcases hclass i₁ with h1 | h1
      · exact ⟨i₁, h1⟩
      · exact absurd (h0.trans h1.symm) hdistinct
  obtain ⟨iS, hS⟩ : ∃ i, W' i = planeSnd L := by
    rcases hclass i₀ with h0 | h0
    · rcases hclass i₁ with h1 | h1
      · exact absurd (h0.trans h1.symm) hdistinct
      · exact ⟨i₁, h1⟩
    · exact ⟨i₀, h0⟩
  obtain ⟨jF, hjF⟩ := hpermy iF
  obtain ⟨jS, hjS⟩ := hpermy iS
  have hA : (planeFst L).map (glRep L y) = W' jF := by rw [← hF]; exact hjF
  have hB : (planeSnd L).map (glRep L y) = W' jS := by rw [← hS]; exact hjS
  have hne : (planeFst L).map (glRep L y) ≠ (planeSnd L).map (glRep L y) := by
    intro hEq
    exact planeFst_ne_planeSnd L
      (Submodule.map_injective_of_injective (glRep_unit_injective L y) hEq)
  refine mem_planeMonomial_of_map L y ?_
  rcases hclass jF with h1 | h1 <;> rcases hclass jS with h2 | h2
  · exact absurd (hA.trans (h1.trans h2.symm) |>.trans hB.symm) hne
  · left
    exact ⟨hA.trans h1, hB.trans h2⟩
  · right
    exact ⟨hA.trans h1, hB.trans h2⟩
  · exact absurd (hA.trans (h1.trans h2.symm) |>.trans hB.symm) hne

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
