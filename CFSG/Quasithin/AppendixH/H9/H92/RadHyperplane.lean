module

public import CFSG.Quasithin.AppendixH.H9.H92.RadHyperplane.DotOrthogonal
public import CFSG.Quasithin.AppendixH.H9.H92.RadHyperplane.RadNilLargeSubspace

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

@[expose] def dotPerp (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {b | ∀ d ∈ D, b ⬝ᵥ d = 0}
  add_mem' := by
    intro a b ha hb d hd
    rw [add_dotProduct, ha d hd, hb d hd, add_zero]
  zero_mem' := by
    intro d _
    rw [zero_dotProduct]
  smul_mem' := by
    intro c a ha d hd
    rw [smul_dotProduct, ha d hd, smul_zero]

theorem mem_dotPerp {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)} {b : Fin n → ZMod 2} :
    b ∈ dotPerp n D ↔ ∀ d ∈ D, b ⬝ᵥ d = 0 := Iff.rfl

private theorem dotPerp_eq_orthogonal (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    dotPerp n D = (dotBilin n).orthogonal D := by
  ext b
  rw [mem_dotPerp, LinearMap.BilinForm.mem_orthogonal_iff]
  refine ⟨fun h d hd => ?_, fun h d hd => ?_⟩
  · rw [dotBilin_apply, dotProduct_comm]
    exact h d hd
  · rw [dotProduct_comm]
    exact h d hd

theorem finrank_dotPerp_add (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Module.finrank (ZMod 2) (dotPerp n D) + Module.finrank (ZMod 2) D = n := by
  rw [dotPerp_eq_orthogonal]
  exact finrank_dotBilin_orthogonal_add n D

theorem dotPerp_dotPerp (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    dotPerp n (dotPerp n D) = D := by
  rw [dotPerp_eq_orthogonal, dotPerp_eq_orthogonal, dotBilin_orthogonal_orthogonal]

theorem transpose_mem_radNil (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (N : Matrix (Fin n) (Fin n) (ZMod 2)) (hN : N ∈ radNil n D) :
    Nᵀ ∈ radNil n (dotPerp n D) := by
  obtain ⟨hN1, hN2⟩ := mem_radNil.1 hN
  refine mem_radNil.2 ⟨fun b d hd => ?_, fun b hb => ?_⟩
  · rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hN2 d hd, dotProduct_zero]
  · funext i
    have h := hb (N *ᵥ Pi.single i 1) (hN1 _)
    rw [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h
    rw [Matrix.mulVec_transpose]
    exact h

theorem radNil_large_subspace_facts (D : Submodule (ZMod 2) (Fin 5 → ZMod 2))
    (hD : Module.finrank (ZMod 2) D = 3)
    (𝒜 : Submodule (ZMod 2) (Matrix (Fin 5) (Fin 5) (ZMod 2))) (h𝒜 : 𝒜 ≤ radNil 5 D)
    (h5 : 5 ≤ Module.finrank (ZMod 2) 𝒜) :
    (∀ x : Fin 5 → ZMod 2, (∀ N ∈ 𝒜, N *ᵥ x = 0) ↔ x ∈ D) ∧
    (∀ b : Fin 5 → ZMod 2, (∀ N ∈ 𝒜, Nᵀ *ᵥ b = 0) ↔ b ∈ dotPerp 5 D) ∧
    Submodule.span (ZMod 2) {y | ∃ N ∈ 𝒜, ∃ a : Fin 5 → ZMod 2, y = N *ᵥ a} = D ∧
    Submodule.span (ZMod 2) {y | ∃ N ∈ 𝒜, ∃ b : Fin 5 → ZMod 2, y = Nᵀ *ᵥ b} = dotPerp 5 D ∧
    Module.finrank (ZMod 2) (dotPerp 5 D) = 2 := by
  have hD' : Module.finrank (ZMod 2) (dotPerp 5 D) = 2 := by
    have := finrank_dotPerp_add 5 D
    omega
  set 𝒜T : Submodule (ZMod 2) (Matrix (Fin 5) (Fin 5) (ZMod 2)) :=
    𝒜.map (Matrix.transposeLinearEquiv (Fin 5) (Fin 5) (ZMod 2) (ZMod 2) :
      Matrix (Fin 5) (Fin 5) (ZMod 2) →ₗ[ZMod 2] Matrix (Fin 5) (Fin 5) (ZMod 2)) with h𝒜T
  have hmem : ∀ M, M ∈ 𝒜T ↔ ∃ N ∈ 𝒜, Nᵀ = M := fun M => by
    rw [h𝒜T, Submodule.mem_map]
    rfl
  have hT : 𝒜T ≤ radNil 5 (dotPerp 5 D) := by
    intro M hM
    obtain ⟨N, hN, rfl⟩ := (hmem M).1 hM
    exact transpose_mem_radNil 5 D N (h𝒜 hN)
  have hTrank : Module.finrank (ZMod 2) 𝒜T = Module.finrank (ZMod 2) 𝒜 :=
    LinearEquiv.finrank_map_eq _ 𝒜
  have hK := forall_mulVec_eq_zero_iff_mem_of_le_radNil h𝒜 (by rw [hD]; omega)
  have hK' := forall_mulVec_eq_zero_iff_mem_of_le_radNil hT (by rw [hD', hTrank]; omega)
  have hI := span_mulVec_eq_of_le_radNil h𝒜 (by rw [hD]; omega)
  have hI' := span_mulVec_eq_of_le_radNil hT (by rw [hD', hTrank]; omega)
  refine ⟨hK, fun b => ?_, hI, ?_, hD'⟩
  · rw [← hK' b]
    refine ⟨fun h M hM => ?_, fun h N hN => h Nᵀ ((hmem _).2 ⟨N, hN, rfl⟩)⟩
    obtain ⟨N, hN, rfl⟩ := (hmem M).1 hM
    exact h N hN
  · rw [← hI']
    congr 1
    ext y
    constructor
    · rintro ⟨N, hN, b, rfl⟩
      exact ⟨Nᵀ, (hmem _).2 ⟨N, hN, rfl⟩, b, rfl⟩
    · rintro ⟨M, hM, b, rfl⟩
      obtain ⟨N, hN, rfl⟩ := (hmem M).1 hM
      exact ⟨N, hN, b, rfl⟩

end CFSG.ASVolI.ChH
