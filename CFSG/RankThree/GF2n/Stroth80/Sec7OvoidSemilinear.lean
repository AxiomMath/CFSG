module

public import Mathlib.LinearAlgebra.Dimension.Finrank

public section

namespace CFSG.RankThree.GF2n.Stroth80

def sec7_semi {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] (σ : K ≃+* K) (ν : V ≃+ V')
    (hν : ∀ (c : K) (v : V), ν (c • v) = σ c • ν v) : V →ₛₗ[(σ : K →+* K)] V' where
  toFun := ν
  map_add' := fun x y => map_add ν x y
  map_smul' := hν

theorem sec7_map_coe {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (σ : K ≃+* K) (ν : V ≃+ V')
    (hν : ∀ (c : K) (v : V), ν (c • v) = σ c • ν v) (P : Submodule K V) :
    (Submodule.map (sec7_semi σ ν hν) P : Set V') = ν '' (P : Set V) :=
  Submodule.map_coe (sec7_semi σ ν hν) P

theorem sec7_finrank_map_semi {K M M' : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup M'] [Module K M'] (σ : K ≃+* K) (f : M →ₛₗ[(σ : K →+* K)] M')
    (hf : Function.Injective f) (p : Submodule K M) :
    Module.finrank K (p.map f) = Module.finrank K p := by
  have : RingHomInvPair (σ : K →+* K) (σ.symm : K →+* K) := RingHomInvPair.of_ringEquiv σ
  have : RingHomInvPair (σ.symm : K →+* K) (σ : K →+* K) := RingHomInvPair.of_ringEquiv_symm σ
  have e := Submodule.equivMapOfInjective f hf p
  have h := lift_rank_eq_of_equiv_equiv (R := K) (R' := K) (M := ↥p) (M' := ↥(p.map f))
    ⇑σ e.toAddEquiv σ.bijective (fun r m => e.map_smulₛₗ r m)
  have h2 := congrArg Cardinal.toNat h
  simp only [Cardinal.toNat_lift] at h2
  exact h2.symm

theorem sec7_finrank_comap_semi {K M M' : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup M'] [Module K M'] (σ : K ≃+* K) (f : M →ₛₗ[(σ : K →+* K)] M')
    (hf : Function.Injective f) (hs : Function.Surjective f) (l : Submodule K M') :
    Module.finrank K (l.comap f) = Module.finrank K l := by
  rw [← sec7_finrank_map_semi σ f hf (l.comap f), Submodule.map_comap_eq_of_surjective hs l]

theorem sec7_setOf_image_le {K M M' : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup M'] [Module K M'] (σ : K ≃+* K) (f : M →ₛₗ[(σ : K →+* K)] M')
    (O : Set (Submodule K M)) (l : Submodule K M') :
    {P | P ∈ Submodule.map f '' O ∧ P ≤ l} = Submodule.map f '' {Q | Q ∈ O ∧ Q ≤ l.comap f} := by
  ext P'
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨Q, hQ, rfl⟩, hle⟩
    exact ⟨Q, ⟨hQ, Submodule.map_le_iff_le_comap.mp hle⟩, rfl⟩
  · rintro ⟨Q, ⟨hQ, hle⟩, rfl⟩
    exact ⟨⟨Q, hQ, rfl⟩, Submodule.map_le_iff_le_comap.mpr hle⟩

theorem sec7_ovoid_map_semilinear {K V V' : Type*} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (σ : K ≃+* K) (ν : V ≃+ V') (hν : ∀ (c : K) (v : V), ν (c • v) = σ c • ν v)
    (O : Set (Submodule K V)) (hO1 : ∀ P ∈ O, Module.finrank K P = 1)
    (hcard : O.ncard = Nat.card K ^ 2 + 1)
    (hline : ∀ l : Submodule K V, Module.finrank K l = 2 → {P | P ∈ O ∧ P ≤ l}.ncard ≤ 2)
    (hplane : ∀ π : Submodule K V, Module.finrank K π = 3 →
      {P | P ∈ O ∧ P ≤ π}.ncard ≤ Nat.card K + 1) :
    ∃ O' : Set (Submodule K V'),
      (∀ P ∈ O, ∃ P' ∈ O', (P' : Set V') = ν '' (P : Set V)) ∧
      (∀ P' ∈ O', ∃ P ∈ O, (P' : Set V') = ν '' (P : Set V)) ∧
      (∀ P ∈ O', Module.finrank K P = 1) ∧ O'.ncard = Nat.card K ^ 2 + 1 ∧
      (∀ l : Submodule K V', Module.finrank K l = 2 → {P | P ∈ O' ∧ P ≤ l}.ncard ≤ 2) ∧
      (∀ π : Submodule K V', Module.finrank K π = 3 →
        {P | P ∈ O' ∧ P ≤ π}.ncard ≤ Nat.card K + 1) := by
  have hf : Function.Injective (sec7_semi σ ν hν) := ν.injective
  have hs : Function.Surjective (sec7_semi σ ν hν) := ν.surjective
  have hmap : Function.Injective (Submodule.map (sec7_semi σ ν hν)) :=
    Submodule.map_injective_of_injective hf
  refine ⟨Submodule.map (sec7_semi σ ν hν) '' O, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    exact ⟨Submodule.map (sec7_semi σ ν hν) P, ⟨P, hP, rfl⟩, sec7_map_coe σ ν hν P⟩
  · rintro P' ⟨P, hP, rfl⟩
    exact ⟨P, hP, sec7_map_coe σ ν hν P⟩
  · rintro P' ⟨P, hP, rfl⟩
    rw [sec7_finrank_map_semi σ (sec7_semi σ ν hν) hf P]
    exact hO1 P hP
  · rw [Set.ncard_image_of_injective O hmap, hcard]
  · intro l hl
    rw [sec7_setOf_image_le σ (sec7_semi σ ν hν) O l, Set.ncard_image_of_injective _ hmap]
    apply hline
    rw [sec7_finrank_comap_semi σ (sec7_semi σ ν hν) hf hs l]
    exact hl
  · intro π hπ
    rw [sec7_setOf_image_le σ (sec7_semi σ ν hν) O π, Set.ncard_image_of_injective _ hmap]
    apply hplane
    rw [sec7_finrank_comap_semi σ (sec7_semi σ ν hν) hf hs π]
    exact hπ

end CFSG.RankThree.GF2n.Stroth80
