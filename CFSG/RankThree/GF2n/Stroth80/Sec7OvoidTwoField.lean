module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.Orthogonal.Basic
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap CFSG.Open
open scoped Matrix

@[expose] def sec7_two_semi {K K' V V' : Type*} [Field K] [Field K'] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K' V'] (θ : K ≃+* K') (ν : V ≃+ V')
    (hν : ∀ (c : K) (v : V), ν (c • v) = θ c • ν v) : V →ₛₗ[(θ : K →+* K')] V' where
  toFun := ν
  map_add' := fun x y => map_add ν x y
  map_smul' := hν

theorem sec7_two_map_coe {K K' V V' : Type*} [Field K] [Field K'] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K' V'] (θ : K ≃+* K') (ν : V ≃+ V')
    (hν : ∀ (c : K) (v : V), ν (c • v) = θ c • ν v) (P : Submodule K V) :
    (Submodule.map (sec7_two_semi θ ν hν) P : Set V') = ν '' (P : Set V) :=
  Submodule.map_coe (sec7_two_semi θ ν hν) P

theorem sec7_two_finrank_map_semi {K K' M M' : Type*} [Field K] [Field K'] [AddCommGroup M]
    [Module K M] [AddCommGroup M'] [Module K' M'] (θ : K ≃+* K')
    (f : M →ₛₗ[(θ : K →+* K')] M') (hf : Function.Injective f) (p : Submodule K M) :
    Module.finrank K' (p.map f) = Module.finrank K p := by
  have : RingHomInvPair (θ : K →+* K') (θ.symm : K' →+* K) := RingHomInvPair.of_ringEquiv θ
  have : RingHomInvPair (θ.symm : K' →+* K) (θ : K →+* K') := RingHomInvPair.of_ringEquiv_symm θ
  have e := Submodule.equivMapOfInjective f hf p
  have h := lift_rank_eq_of_equiv_equiv (R := K) (R' := K') (M := ↥p) (M' := ↥(p.map f))
    ⇑θ e.toAddEquiv θ.bijective (fun r m => e.map_smulₛₗ r m)
  have h2 := congrArg Cardinal.toNat h
  simp only [Cardinal.toNat_lift] at h2
  exact h2.symm

theorem sec7_two_finrank_comap_semi {K K' M M' : Type*} [Field K] [Field K'] [AddCommGroup M]
    [Module K M] [AddCommGroup M'] [Module K' M'] (θ : K ≃+* K')
    (f : M →ₛₗ[(θ : K →+* K')] M') (hf : Function.Injective f) (hs : Function.Surjective f)
    (l : Submodule K' M') :
    Module.finrank K (l.comap f) = Module.finrank K' l := by
  rw [← sec7_two_finrank_map_semi θ f hf (l.comap f), Submodule.map_comap_eq_of_surjective hs l]

theorem sec7_two_setOf_image_le {K K' M M' : Type*} [Field K] [Field K'] [AddCommGroup M]
    [Module K M] [AddCommGroup M'] [Module K' M'] (θ : K ≃+* K')
    (f : M →ₛₗ[(θ : K →+* K')] M') (O : Set (Submodule K M)) (l : Submodule K' M') :
    {P | P ∈ Submodule.map f '' O ∧ P ≤ l} =
      Submodule.map f '' {Q | Q ∈ O ∧ Q ≤ l.comap f} := by
  ext P'
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨Q, hQ, rfl⟩, hle⟩
    exact ⟨Q, ⟨hQ, Submodule.map_le_iff_le_comap.mp hle⟩, rfl⟩
  · rintro ⟨Q, ⟨hQ, hle⟩, rfl⟩
    exact ⟨⟨Q, hQ, rfl⟩, Submodule.map_le_iff_le_comap.mpr hle⟩

theorem sec7_ovoid_map_semilinear2 {K K' V V' : Type*} [Field K] [Field K'] [Finite K] [Finite K']
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V']
    (θ : K ≃+* K') (ν : V ≃+ V') (hν : ∀ (c : K) (v : V), ν (c • v) = θ c • ν v)
    (hKK : Nat.card K = Nat.card K')
    (O : Set (Submodule K V)) (hO1 : ∀ P ∈ O, Module.finrank K P = 1)
    (hcard : O.ncard = Nat.card K ^ 2 + 1)
    (hline : ∀ l : Submodule K V, Module.finrank K l = 2 → {P | P ∈ O ∧ P ≤ l}.ncard ≤ 2)
    (hplane : ∀ π : Submodule K V, Module.finrank K π = 3 →
      {P | P ∈ O ∧ P ≤ π}.ncard ≤ Nat.card K + 1) :
    ∃ O' : Set (Submodule K' V'),
      (∀ P ∈ O, ∃ P' ∈ O', (P' : Set V') = ν '' (P : Set V)) ∧
      (∀ P' ∈ O', ∃ P ∈ O, (P' : Set V') = ν '' (P : Set V)) ∧
      (∀ P ∈ O', Module.finrank K' P = 1) ∧ O'.ncard = Nat.card K' ^ 2 + 1 ∧
      (∀ l : Submodule K' V', Module.finrank K' l = 2 → {P | P ∈ O' ∧ P ≤ l}.ncard ≤ 2) ∧
      (∀ π : Submodule K' V', Module.finrank K' π = 3 →
        {P | P ∈ O' ∧ P ≤ π}.ncard ≤ Nat.card K' + 1) := by
  have hf : Function.Injective (sec7_two_semi θ ν hν) := ν.injective
  have hs : Function.Surjective (sec7_two_semi θ ν hν) := ν.surjective
  have hmap : Function.Injective (Submodule.map (sec7_two_semi θ ν hν)) :=
    Submodule.map_injective_of_injective hf
  refine ⟨Submodule.map (sec7_two_semi θ ν hν) '' O, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    exact ⟨Submodule.map (sec7_two_semi θ ν hν) P, ⟨P, hP, rfl⟩, sec7_two_map_coe θ ν hν P⟩
  · rintro P' ⟨P, hP, rfl⟩
    exact ⟨P, hP, sec7_two_map_coe θ ν hν P⟩
  · rintro P' ⟨P, hP, rfl⟩
    rw [sec7_two_finrank_map_semi θ (sec7_two_semi θ ν hν) hf P]
    exact hO1 P hP
  · rw [Set.ncard_image_of_injective O hmap, hcard, hKK]
  · intro l hl
    rw [sec7_two_setOf_image_le θ (sec7_two_semi θ ν hν) O l, Set.ncard_image_of_injective _ hmap]
    apply hline
    rw [sec7_two_finrank_comap_semi θ (sec7_two_semi θ ν hν) hf hs l]
    exact hl
  · intro π hπ
    rw [sec7_two_setOf_image_le θ (sec7_two_semi θ ν hν) O π, Set.ncard_image_of_injective _ hmap,
      ← hKK]
    apply hplane
    rw [sec7_two_finrank_comap_semi θ (sec7_two_semi θ ν hν) hf hs π]
    exact hπ

theorem sec7p_finrank_perp {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {u : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K}
    (hu : u ≠ 0) :
    Module.finrank K (LinearMap.ker (polarBilin (quadMinus 2 K b c) u)) = 3 := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hu
  have hsurj : Function.Surjective (polarBilin (quadMinus 2 K b c) u) := by
    intro s
    refine ⟨(s / polar (quadMinus 2 K b c) u y) • y, ?_⟩
    rw [map_smul, polarBilin_apply_apply, smul_eq_mul]
    field_simp
  have h := LinearMap.finrank_range_add_finrank_ker (polarBilin (quadMinus 2 K b c) u)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at h
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

theorem sec7p_natCard_perp {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {u : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K}
    (hu : u ≠ 0) :
    Nat.card (LinearMap.ker (polarBilin (quadMinus 2 K b c) u)) = Nat.card K ^ 3 := by
  have h := Module.natCard_eq_pow_finrank (K := K)
    (V := ↥(LinearMap.ker (polarBilin (quadMinus 2 K b c) u)))
  rw [h, sec7p_finrank_perp hirr hu]

theorem sec7_natCard_polar_perp {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {u : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K}
    (hu : u ≠ 0) (X : AddSubgroup (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K))
    (hX : ∀ y, y ∈ X ↔ polar (quadMinus 2 K b c) u y = 0) : Nat.card X = Nat.card K ^ 3 := by
  have hker : ∀ y, y ∈ X ↔ y ∈ LinearMap.ker (polarBilin (quadMinus 2 K b c) u) := by
    intro y
    rw [hX y, LinearMap.mem_ker, polarBilin_apply_apply]
  rw [← sec7p_natCard_perp hirr hu]
  exact Nat.card_congr (Equiv.subtypeEquivRight hker)

end CFSG.RankThree.GF2n.Stroth80
