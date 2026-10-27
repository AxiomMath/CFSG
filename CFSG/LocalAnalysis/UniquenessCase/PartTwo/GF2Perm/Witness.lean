module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

@[expose] def PermWitnessAt (G : Type*) [Group G] (U : Subgroup G) : Prop :=
  ∃ X R : Subgroup G,
    (∀ φ : MulAut G, U.map φ.toMonoidHom = U → X.map φ.toMonoidHom = X) ∧
    R ≤ U ∧ R ≤ X ∧ X ≤ Subgroup.normalizer (R : Set G) ∧ IsPGroup 2 R ∧
    (∀ x ∈ X, x ^ 3 ∈ R) ∧ (∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ R) ∧
    9 * Nat.card R ≤ Nat.card X

@[expose] def PermWitness (G : Type*) [Group G] : Prop :=
  ∀ U : Sylow 2 G, PermWitnessAt G U

variable {G G' : Type*} [Group G] [Group G']

theorem PermWitnessAt.map_mulEquiv (e : G ≃* G') {U : Subgroup G} (h : PermWitnessAt G U) :
    PermWitnessAt G' (U.map e.toMonoidHom) := by
  obtain ⟨X, R, hfix, hRU, hRX, hXR, hR2, hcube, hcomm, hcard⟩ := h
  refine ⟨X.map e.toMonoidHom, R.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ' hφ'
    have hcomp : (e.trans (φ'.trans e.symm)).toMonoidHom =
        e.symm.toMonoidHom.comp (φ'.toMonoidHom.comp e.toMonoidHom) := by
      ext x
      simp [MulEquiv.trans_apply]
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    have hψ : U.map (e.trans (φ'.trans e.symm)).toMonoidHom = U := by
      rw [hcomp, ← Subgroup.map_map, ← Subgroup.map_map, hφ', Subgroup.map_map, hid,
        Subgroup.map_id]
    have hX : X.map (e.trans (φ'.trans e.symm)).toMonoidHom = X := hfix _ hψ
    have hmain : ((X.map e.toMonoidHom).map φ'.toMonoidHom).map e.symm.toMonoidHom =
        (X.map e.toMonoidHom).map e.symm.toMonoidHom := by
      have h1 : (X.map e.toMonoidHom).map φ'.toMonoidHom =
          X.map (φ'.toMonoidHom.comp e.toMonoidHom) :=
        Subgroup.map_map (K := X) (f := e.toMonoidHom) (g := φ'.toMonoidHom)
      have h2 : (X.map (φ'.toMonoidHom.comp e.toMonoidHom)).map e.symm.toMonoidHom =
          X.map (e.symm.toMonoidHom.comp (φ'.toMonoidHom.comp e.toMonoidHom)) :=
        Subgroup.map_map (K := X) (f := φ'.toMonoidHom.comp e.toMonoidHom)
          (g := e.symm.toMonoidHom)
      rw [h1, h2, ← hcomp, hX, Subgroup.map_map, hid, Subgroup.map_id]
    have hinj : Function.Injective (e.symm.toMonoidHom : G' →* G) := by
      intro x y h
      exact e.symm.injective h
    exact Subgroup.map_injective hinj hmain
  · exact Subgroup.map_mono hRU
  · exact Subgroup.map_mono hRX
  · have h := Subgroup.map_mono (f := e.toMonoidHom) hXR
    rwa [Subgroup.map_equiv_normalizer_eq] at h
  · exact hR2.map e.toMonoidHom
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [map_pow] using Subgroup.mem_map_of_mem e.toMonoidHom (hcube y hy)
  · intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    simpa only [← map_mul, ← map_inv] using
      Subgroup.mem_map_of_mem e.toMonoidHom (hcomm x' hx' y' hy')
  · rw [Subgroup.card_map_of_injective e.injective,
      Subgroup.card_map_of_injective e.injective]
    exact hcard

theorem PermWitnessAt.conj {U : Subgroup G} (h : PermWitnessAt G U) (g : G) :
    PermWitnessAt G (U.map (MulAut.conj g).toMonoidHom) :=
  h.map_mulEquiv (MulAut.conj g)

theorem permWitness_of_permWitnessAt [Finite G] (U : Sylow 2 G) (h : PermWitnessAt G U) :
    PermWitness G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro U'
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G U U'
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  exact h.conj g

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
