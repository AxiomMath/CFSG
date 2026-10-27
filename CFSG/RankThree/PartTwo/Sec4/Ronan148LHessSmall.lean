module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessMat
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open Matrix CFSG.RankThree.PartTwo.Sec4.Ronan148B

section Model

variable {K : Type*} [CommRing K]

@[expose] def hessModelPhi (ω μ : K) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => ω ^ (i.val * j.val) * μ

@[expose] def hessModelT (i : Fin 3) : Matrix (Fin 3) (Fin 3) K :=
  diagonal fun j => if j = i then 1 else -1

@[expose] def hessModelS (ω ν : K) (k : Fin 3) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => 2 * ν * ω ^ (k.val * i.val + 2 * (k.val * j.val)) - if i = j then 1 else 0

@[expose] def hessModelGen (ω ν : K) : Fin 3 ⊕ Fin 3 → Matrix (Fin 3) (Fin 3) K
  | .inl i => hessModelT i
  | .inr k => hessModelS ω ν k

end Model

section Transfer

variable {F : Type*} [Field F] {ω : F}

@[expose] def hessGen (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    Fin 3 ⊕ Fin 3 → GL (Fin 3) F
  | .inl i => hessT i
  | .inr k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹

theorem hessGen_mem_closure (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) (g : Fin 3 ⊕ Fin 3) :
    hessGen hω h3 g ∈ Subgroup.closure (Set.range (hessT (F := F)) ∪
      Set.range fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹) := by
  apply Subgroup.subset_closure
  cases g with
  | inl i => exact Or.inl ⟨i, rfl⟩
  | inr k => exact Or.inr ⟨k, rfl⟩

theorem coe_hessGen {K : Type*} [CommRing K] (ψ : K →+* F) {ωK ν : K} (hψω : ψ ωK = ω)
    (hψν : ψ ν = 3⁻¹) (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) (g : Fin 3 ⊕ Fin 3) :
    ((hessGen hω h3 g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (hessModelGen ωK ν g).map ψ := by
  cases g with
  | inl i =>
    change hessTMat i = (hessModelT i).map ψ
    ext a b
    simp only [Matrix.map_apply, hessTMat, hessModelT, Matrix.diagonal_apply]
    split_ifs <;> simp
  | inr k =>
    change ((hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = (hessModelS ωK ν k).map ψ
    rw [hessPhi_conj_hessT hω h3 k]
    ext a b
    simp only [hessSMat, hessModelS, Matrix.map_apply, map_sub, map_mul, map_pow, map_ofNat, hψω,
      hψν, div_eq_mul_inv]
    split_ifs <;> simp

theorem map_hessModelPhi {K : Type*} [CommRing K] (ψ : K →+* F) {ωK μ : K} (hψω : ψ ωK = ω)
    (hψμ : ψ μ = (1 + 2 * ω)⁻¹) : (hessModelPhi ωK μ).map ψ = hessPhiMat ω := by
  ext i j
  simp only [hessModelPhi, hessPhiMat, Matrix.map_apply, map_mul, map_pow, hψω, hψμ,
    div_eq_mul_inv]

theorem hessPhi_mem_closure_of_model {K : Type*} [CommRing K] (ψ : K →+* F) {ωK μ ν : K}
    (hμ : μ * (1 + 2 * ωK) = 1) (hν : ν * 3 = 1) (X Y : List (Fin 3 ⊕ Fin 3)) (a : ℕ)
    (hword : hessModelPhi ωK μ =
      (X.map (hessModelGen ωK ν)).prod ^ a * (Y.map (hessModelGen ωK ν)).prod)
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) (hψω : ψ ωK = ω) :
    hessPhi hω h3 ∈ Subgroup.closure (Set.range (hessT (F := F)) ∪
      Set.range fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹) := by
  have hψμ : ψ μ = (1 + 2 * ω)⁻¹ := by
    have h := congrArg ψ hμ
    rw [map_mul, map_add, map_one, map_mul, map_ofNat, hψω] at h
    exact eq_inv_of_mul_eq_one_left h
  have hψν : ψ ν = 3⁻¹ := by
    have h := congrArg ψ hν
    rw [map_mul, map_ofNat, map_one] at h
    exact eq_inv_of_mul_eq_one_left h
  have hlist : ∀ L : List (Fin 3 ⊕ Fin 3),
      (((L.map (hessGen hω h3)).prod : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ψ.mapMatrix (L.map (hessModelGen ωK ν)).prod := by
    intro L
    rw [map_list_prod, ← Units.coeHom_apply, map_list_prod, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun g _ => ?_
    simp only [Function.comp_apply, Units.coeHom_apply, RingHom.mapMatrix_apply]
    exact coe_hessGen ψ hψω hψν hω h3 g
  have hGL : hessPhi hω h3 =
      (X.map (hessGen hω h3)).prod ^ a * (Y.map (hessGen hω h3)).prod := by
    apply Units.ext
    rw [coe_hessPhi, ← map_hessModelPhi ψ hψω hψμ, hword, Units.val_mul, Units.val_pow_eq_pow_val,
      hlist, hlist, ← RingHom.mapMatrix_apply, map_mul, map_pow]
  have key : (X.map (hessGen hω h3)).prod ^ a * (Y.map (hessGen hω h3)).prod ∈
      Subgroup.closure (Set.range (hessT (F := F)) ∪
        Set.range fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹) := by
    refine Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.list_prod_mem _ ?_) _)
      (Subgroup.list_prod_mem _ ?_) <;>
    · intro x hx
      obtain ⟨g, -, rfl⟩ := List.mem_map.mp hx
      exact hessGen_mem_closure hω h3 g
  rwa [← hGL] at key

end Transfer

section Quadratic

variable {F : Type} [Field F] {p : ℕ} [CharP F p] {ω : F}

@[expose] noncomputable def hessQuadLift (hω : ω ^ 2 + ω + 1 = 0) :
    QuadraticAlgebra (ZMod p) (-1) (-1) →+* F :=
  letI := ZMod.algebra F p
  (QuadraticAlgebra.lift ⟨ω, by
    rw [neg_smul, one_smul, neg_smul, one_smul]
    linear_combination hω⟩).toRingHom

theorem hessQuadLift_omega (hω : ω ^ 2 + ω + 1 = 0) :
    hessQuadLift (p := p) hω QuadraticAlgebra.omega = ω := by
  letI := ZMod.algebra F p
  simp [hessQuadLift, QuadraticAlgebra.lift_apply_apply]

end Quadratic

section Split

variable {F : Type} [Field F] {p : ℕ} [CharP F p] {ω : F}

theorem hessPhi_mem_closure_of_split (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0)
    {w₀ w₁ μ₀ μ₁ ν : ZMod p} (hsum : w₀ + w₁ = -1) (hprod : w₀ * w₁ = 1)
    (hμ₀ : μ₀ * (1 + 2 * w₀) = 1) (hμ₁ : μ₁ * (1 + 2 * w₁) = 1) (hν : ν * 3 = 1)
    (X Y : List (Fin 3 ⊕ Fin 3)) (a : ℕ)
    (h₀ : hessModelPhi w₀ μ₀ =
      (X.map (hessModelGen w₀ ν)).prod ^ a * (Y.map (hessModelGen w₀ ν)).prod)
    (h₁ : hessModelPhi w₁ μ₁ =
      (X.map (hessModelGen w₁ ν)).prod ^ a * (Y.map (hessModelGen w₁ ν)).prod) :
    hessPhi hω h3 ∈ Subgroup.closure (Set.range (hessT (F := F)) ∪
      Set.range fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹) := by
  set ψ : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  have hs := congrArg ψ hsum
  have hp := congrArg ψ hprod
  rw [map_add, map_neg, map_one] at hs
  rw [map_mul, map_one] at hp
  have hroot : (ω - ψ w₀) * (ω - ψ w₁) = 0 := by
    linear_combination hω - ω * hs + hp
  rcases mul_eq_zero.mp hroot with h | h
  · exact hessPhi_mem_closure_of_model ψ hμ₀ hν X Y a h₀ hω h3 (sub_eq_zero.mp h).symm
  · exact hessPhi_mem_closure_of_model ψ hμ₁ hν X Y a h₁ hω h3 (sub_eq_zero.mp h).symm

end Split

theorem hessPhi_mem_closure_five {F : Type} [Field F] [CharP F 5] {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    hessPhi hω h3 ∈ Subgroup.closure (Set.range (hessT (F := F)) ∪
      Set.range fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹) :=
  hessPhi_mem_closure_of_model (hessQuadLift (p := 5) hω)
    (ωK := QuadraticAlgebra.omega) (μ := ⟨3, 1⟩) (ν := ⟨2, 0⟩) (by decide) (by decide)
    [.inl 1, .inr 2, .inl 2, .inr 1] [.inl 1] 5 (by decide +kernel) hω h3 (hessQuadLift_omega hω)

theorem hessPhi_mem_closure_seven {F : Type} [Field F] [CharP F 7] {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    hessPhi hω h3 ∈ Subgroup.closure (Set.range (hessT (F := F)) ∪
      Set.range fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹) :=
  hessPhi_mem_closure_of_split (p := 7) hω h3 (w₀ := 2) (w₁ := 4) (μ₀ := 3) (μ₁ := 4) (ν := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    [.inl 1, .inr 1, .inl 2, .inr 2] [.inl 1, .inr 1, .inl 2] 4 (by decide +kernel)
    (by decide +kernel)

theorem hessPhi_mem_closure_eleven {F : Type} [Field F] [CharP F 11] {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    hessPhi hω h3 ∈ Subgroup.closure (Set.range (hessT (F := F)) ∪
      Set.range fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹) :=
  hessPhi_mem_closure_of_model (hessQuadLift (p := 11) hω)
    (ωK := QuadraticAlgebra.omega) (μ := ⟨7, 3⟩) (ν := ⟨4, 0⟩) (by decide) (by decide)
    [.inl 1, .inr 1, .inl 2, .inr 2] [.inl 1, .inr 1, .inl 2] 27 (by decide +kernel) hω h3
    (hessQuadLift_omega hω)

theorem hessPhi_mem_closure_thirteen {F : Type} [Field F] [CharP F 13] {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    hessPhi hω h3 ∈ Subgroup.closure (Set.range (hessT (F := F)) ∪
      Set.range fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹) :=
  hessPhi_mem_closure_of_split (p := 13) hω h3 (w₀ := 3) (w₁ := 9) (μ₀ := 2) (μ₁ := 11) (ν := 9)
    (by decide) (by decide) (by decide) (by decide) (by decide) []
    [.inl 0, .inr 0, .inl 0, .inr 0, .inl 1, .inr 2, .inl 2, .inr 1, .inl 2, .inr 2, .inl 0,
      .inr 2, .inl 0, .inr 0, .inl 2, .inr 0, .inl 0, .inr 1, .inl 0, .inr 1, .inl 2, .inr 2,
      .inl 2, .inr 1, .inl 1] 0 (by decide +kernel) (by decide +kernel)

theorem hessPhi_mem_closure_seventeen {F : Type} [Field F] [CharP F 17] {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    hessPhi hω h3 ∈ Subgroup.closure (Set.range (hessT (F := F)) ∪
      Set.range fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹) :=
  hessPhi_mem_closure_of_model (hessQuadLift (p := 17) hω)
    (ωK := QuadraticAlgebra.omega) (μ := ⟨11, 5⟩) (ν := ⟨6, 0⟩) (by decide) (by decide) []
    [.inl 0, .inr 0, .inl 1, .inr 0, .inl 1, .inr 0, .inl 0, .inr 1, .inl 0, .inr 2, .inl 1,
      .inr 1, .inl 1, .inr 1, .inl 0, .inr 2, .inl 1, .inr 0, .inl 2, .inr 2, .inl 2, .inr 2,
      .inl 1, .inr 0, .inl 2] 0 (by decide +kernel) hω h3 (hessQuadLift_omega hω)

theorem hessPhi_mem_closure_nineteen {F : Type} [Field F] [CharP F 19] {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    hessPhi hω h3 ∈ Subgroup.closure (Set.range (hessT (F := F)) ∪
      Set.range fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹) :=
  hessPhi_mem_closure_of_split (p := 19) hω h3 (w₀ := 7) (w₁ := 11) (μ₀ := 14) (μ₁ := 5)
    (ν := 13) (by decide) (by decide) (by decide) (by decide) (by decide)
    [.inl 0, .inr 1, .inl 1, .inr 2, .inl 1] [.inl 0, .inr 2] 11 (by decide +kernel)
    (by decide +kernel)

theorem hessPhiMemClosure_small (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (hp : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19)
    (ω : F) (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    hessPhi hω h3 ∈ Subgroup.closure
      (Set.range (hessT (F := F)) ∪
        Set.range fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹) := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hessPhi_mem_closure_five hω h3
  · exact hessPhi_mem_closure_seven hω h3
  · exact hessPhi_mem_closure_eleven hω h3
  · exact hessPhi_mem_closure_thirteen hω h3
  · exact hessPhi_mem_closure_seventeen hω h3
  · exact hessPhi_mem_closure_nineteen hω h3

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
