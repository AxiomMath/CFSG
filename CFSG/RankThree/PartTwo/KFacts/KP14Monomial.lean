module

public import CFSG.RankThree.Classical.TransvectionReciprocalPair

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP14

open Matrix

abbrev Mat3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 3)

@[expose] def signedMat (π : Fin 3 → Fin 3) (s : Fin 3 → ZMod 3) : Mat3 :=
  Matrix.of fun i j => if i = π j then s j else 0

theorem signedMat_mul (π τ : Fin 3 → Fin 3) (s t : Fin 3 → ZMod 3) :
    signedMat π s * signedMat τ t = signedMat (π ∘ τ) (fun j => s (τ j) * t j) := by
  ext i j
  simp only [signedMat, Matrix.mul_apply, Matrix.of_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (τ j)]
  · by_cases h : i = π (τ j) <;> simp [h]
  · intro k _ hk
    simp [hk]
  · simp

theorem signedMat_id_one : signedMat id (fun _ => 1) = 1 := by
  ext i j
  simp [signedMat, Matrix.one_apply]

@[expose] def IsMonomial (M : Mat3) : Prop :=
  ∃ π : Fin 3 → Fin 3, Function.Bijective π ∧ ∃ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) ∧
    M = signedMat π s

@[expose] def monomial : Subgroup (GL (Fin 3) (ZMod 3)) where
  carrier := {g | IsMonomial g}
  mul_mem' := by
    rintro a b ⟨π, hπ, s, hs, ha⟩ ⟨τ, hτ, t, ht, hb⟩
    exact ⟨π ∘ τ, hπ.comp hτ, fun j => s (τ j) * t j, fun j => mul_ne_zero (hs _) (ht _), by
      show ((a * b : GL (Fin 3) (ZMod 3)) : Mat3) = _
      rw [Units.val_mul, ha, hb, signedMat_mul]⟩
  one_mem' := ⟨id, Function.bijective_id, fun _ => 1, fun _ => one_ne_zero, by
    rw [Units.val_one, signedMat_id_one]⟩
  inv_mem' := by
    rintro a ⟨π, hπ, s, hs, ha⟩
    set e := Equiv.ofBijective π hπ
    refine ⟨e.symm, e.symm.bijective, fun j => (s (e.symm j))⁻¹, fun j => inv_ne_zero (hs _), ?_⟩
    apply Units.inv_eq_of_mul_eq_one_right
    rw [ha, signedMat_mul]
    have h1 : (π ∘ e.symm) = id := by
      funext j
      exact Equiv.ofBijective_apply_symm_apply π hπ j
    have h2 : (fun j => s (e.symm j) * (s (e.symm j))⁻¹) = fun _ => (1 : ZMod 3) := by
      funext j
      exact mul_inv_cancel₀ (hs _)
    rw [h1, h2, signedMat_id_one]

theorem mem_monomial {g : GL (Fin 3) (ZMod 3)} : g ∈ monomial ↔ IsMonomial g := Iff.rfl

theorem mem_monomial_of {g : GL (Fin 3) (ZMod 3)} (π : Fin 3 → Fin 3) (s : Fin 3 → ZMod 3)
    (hπ : Function.Bijective π) (hs : ∀ j, s j ≠ 0) (h : (g : Mat3) = signedMat π s) :
    g ∈ monomial :=
  ⟨π, hπ, s, hs, h⟩

theorem forall_mem_monomial {P : Mat3 → Prop}
    (h : ∀ π : Fin 3 → Fin 3, Function.Bijective π → ∀ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) →
      P (signedMat π s)) {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ monomial) : P g := by
  obtain ⟨π, hπ, s, hs, he⟩ := hg
  rw [he]
  exact h π hπ s hs

theorem mat_no_unipotent : ∀ π : Fin 3 → Fin 3, Function.Bijective π →
    ∀ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) →
      (signedMat π s - 1) * (signedMat π s - 1) = 0 → signedMat π s = 1 := by
  decide +kernel

theorem eq_one_of_sub_one_sq_eq_zero {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ monomial)
    (h : ((g : Mat3) - 1) * ((g : Mat3) - 1) = 0) : g = 1 :=
  Units.ext (forall_mem_monomial (P := fun M => (M - 1) * (M - 1) = 0 → M = 1)
    mat_no_unipotent hg h)

theorem not_isTransvectionWith {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ monomial) {V : Type*}
    [AddCommGroup V] [Module (ZMod 3) V] (e : V ≃ₗ[ZMod 3] (Fin 3 → ZMod 3)) (t : V ≃ₗ[ZMod 3] V)
    (htg : ∀ x, e (t x) = (g : Mat3) *ᵥ e x) (v : V) (f : Module.Dual (ZMod 3) V) :
    ¬ CFSG.RankThree.Classical.IsTransvectionWith t v f := by
  rintro ⟨hv, hf, hfv, ht⟩
  have hsub : ∀ y, ((g : Mat3) - 1) *ᵥ y = f (e.symm y) • e v := by
    intro y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    conv_lhs => rw [← e.apply_symm_apply y, ← htg, ht, map_add, map_smul, e.apply_symm_apply]
    abel
  have hsq : ((g : Mat3) - 1) * ((g : Mat3) - 1) = 0 := by
    refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
    rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      hsub, hsub, map_smul, e.symm_apply_apply, map_smul, hfv, smul_zero, zero_smul, map_zero,
      LinearMap.zero_apply]
  have h1 := eq_one_of_sub_one_sq_eq_zero hg hsq
  apply hf
  ext x
  have h2 := hsub (e x)
  rw [h1, Units.val_one, sub_self, Matrix.zero_mulVec, e.symm_apply_apply] at h2
  have h3 : f x • v = 0 := e.injective (by rw [map_smul, ← h2, map_zero])
  exact (smul_eq_zero.mp h3).resolve_right hv

@[expose] def IsReflection (g : GL (Fin 3) (ZMod 3)) : Prop :=
  orderOf g = 2 ∧ Nat.card (Set.range fun v : Fin 3 → ZMod 3 => ((g : Mat3) - 1) *ᵥ v) = 3

theorem card_range_eq (M : Mat3) :
    Nat.card (Set.range fun v : Fin 3 → ZMod 3 => M *ᵥ v) =
      (Finset.univ.image fun v : Fin 3 → ZMod 3 => M *ᵥ v).card := by
  rw [Nat.card_eq_card_toFinset, Set.toFinset_range]

theorem isReflection_iff (g : GL (Fin 3) (ZMod 3)) : IsReflection g ↔
    (g : Mat3) * g = 1 ∧ (g : Mat3) ≠ 1 ∧
      (Finset.univ.image fun v : Fin 3 → ZMod 3 => ((g : Mat3) - 1) *ᵥ v).card = 3 := by
  rw [IsReflection, card_range_eq]
  have : orderOf g = 2 ↔ (g : Mat3) * g = 1 ∧ (g : Mat3) ≠ 1 := by
    constructor
    · intro h
      refine ⟨?_, fun h1 => ?_⟩
      · rw [← Units.val_mul, ← pow_two, ← h, pow_orderOf_eq_one, Units.val_one]
      · rw [show g = 1 from Units.ext h1, orderOf_one] at h
        omega
    · rintro ⟨h2, h1⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (Units.ext (by rw [pow_two, Units.val_mul, h2, Units.val_one]))
        (fun h => h1 (by rw [h, Units.val_one]))
  rw [this, and_assoc]

@[expose] def reflMats : List Mat3 :=
  [!![2, 0, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 0, 2, 0; 0, 0, 1], !![1, 0, 0; 0, 1, 0; 0, 0, 2],
   !![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 2, 0; 2, 0, 0; 0, 0, 1],
   !![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 2; 0, 2, 0],
   !![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 2; 0, 1, 0; 2, 0, 0]]

theorem mat_refl : ∀ π : Fin 3 → Fin 3, Function.Bijective π →
    ∀ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) →
      signedMat π s * signedMat π s = 1 → signedMat π s ≠ 1 →
      (Finset.univ.image fun v : Fin 3 → ZMod 3 => (signedMat π s - 1) *ᵥ v).card = 3 →
      signedMat π s ∈ reflMats := by
  decide +kernel

@[expose] def ofInvol (M : Mat3) (h : M * M = 1) : GL (Fin 3) (ZMod 3) := ⟨M, M, h, h⟩

@[expose] def d0 : GL (Fin 3) (ZMod 3) := ofInvol !![2, 0, 0; 0, 1, 0; 0, 0, 1] (by decide)

@[expose] def d1 : GL (Fin 3) (ZMod 3) := ofInvol !![1, 0, 0; 0, 2, 0; 0, 0, 1] (by decide)

@[expose] def d2 : GL (Fin 3) (ZMod 3) := ofInvol !![1, 0, 0; 0, 1, 0; 0, 0, 2] (by decide)

@[expose] def p01 : GL (Fin 3) (ZMod 3) := ofInvol !![0, 1, 0; 1, 0, 0; 0, 0, 1] (by decide)

@[expose] def m01 : GL (Fin 3) (ZMod 3) := ofInvol !![0, 2, 0; 2, 0, 0; 0, 0, 1] (by decide)

@[expose] def p12 : GL (Fin 3) (ZMod 3) := ofInvol !![1, 0, 0; 0, 0, 1; 0, 1, 0] (by decide)

@[expose] def m12 : GL (Fin 3) (ZMod 3) := ofInvol !![1, 0, 0; 0, 0, 2; 0, 2, 0] (by decide)

@[expose] def p02 : GL (Fin 3) (ZMod 3) := ofInvol !![0, 0, 1; 0, 1, 0; 1, 0, 0] (by decide)

@[expose] def m02 : GL (Fin 3) (ZMod 3) := ofInvol !![0, 0, 2; 0, 1, 0; 2, 0, 0] (by decide)

@[expose] def diagRefl : Set (GL (Fin 3) (ZMod 3)) := {d0, d1, d2}

@[expose] def swapRefl : Set (GL (Fin 3) (ZMod 3)) := {p01, m01, p12, m12, p02, m02}

@[expose] def monoRefl : Set (GL (Fin 3) (ZMod 3)) := diagRefl ∪ swapRefl

theorem mem_monoRefl_of_isReflection {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ monomial)
    (hr : IsReflection g) : g ∈ monoRefl := by
  rw [isReflection_iff] at hr
  have hM := forall_mem_monomial (P := fun M => M * M = 1 → M ≠ 1 →
      (Finset.univ.image fun v : Fin 3 → ZMod 3 => (M - 1) *ᵥ v).card = 3 → M ∈ reflMats)
    mat_refl hg hr.1 hr.2.1 hr.2.2
  simp only [reflMats, List.mem_cons, List.not_mem_nil, or_false] at hM
  simp only [monoRefl, diagRefl, swapRefl, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  rcases hM with h | h | h | h | h | h | h | h | h
  · exact Or.inl (Or.inl (Units.ext h))
  · exact Or.inl (Or.inr (Or.inl (Units.ext h)))
  · exact Or.inl (Or.inr (Or.inr (Units.ext h)))
  · exact Or.inr (Or.inl (Units.ext h))
  · exact Or.inr (Or.inr (Or.inl (Units.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Units.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Units.ext h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Units.ext h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Units.ext h))))))

theorem monoRefl_subset_monomial : monoRefl ⊆ monomial := by
  intro x hx
  simp only [monoRefl, diagRefl, swapRefl, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact mem_monomial_of id ![2, 1, 1] Function.bijective_id (by decide) (by decide)
  · exact mem_monomial_of id ![1, 2, 1] Function.bijective_id (by decide) (by decide)
  · exact mem_monomial_of id ![1, 1, 2] Function.bijective_id (by decide) (by decide)
  · exact mem_monomial_of ![1, 0, 2] ![1, 1, 1] (by decide) (by decide) (by decide)
  · exact mem_monomial_of ![1, 0, 2] ![2, 2, 1] (by decide) (by decide) (by decide)
  · exact mem_monomial_of ![0, 2, 1] ![1, 1, 1] (by decide) (by decide) (by decide)
  · exact mem_monomial_of ![0, 2, 1] ![1, 2, 2] (by decide) (by decide) (by decide)
  · exact mem_monomial_of ![2, 1, 0] ![1, 1, 1] (by decide) (by decide) (by decide)
  · exact mem_monomial_of ![2, 1, 0] ![2, 1, 2] (by decide) (by decide) (by decide)

theorem isReflection_of_mem_monoRefl {x : GL (Fin 3) (ZMod 3)} (hx : x ∈ monoRefl) :
    IsReflection x := by
  rw [isReflection_iff]
  simp only [monoRefl, diagRefl, swapRefl, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide +kernel

theorem isReflection_iff_mem_monoRefl {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ monomial) :
    IsReflection g ↔ g ∈ monoRefl :=
  ⟨mem_monoRefl_of_isReflection hg, isReflection_of_mem_monoRefl⟩

@[expose] def cyc : GL (Fin 3) (ZMod 3) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide, by decide⟩

@[expose] def cyc' : GL (Fin 3) (ZMod 3) :=
  ⟨!![0, 0, 2; 2, 0, 0; 0, 1, 0], !![0, 2, 0; 0, 0, 1; 2, 0, 0], by decide, by decide⟩

theorem cyc_d0 : cyc * d0 * cyc⁻¹ = d1 := by decide +kernel

theorem cyc_d1 : cyc * d1 * cyc⁻¹ = d2 := by decide +kernel

theorem cyc_d2 : cyc * d2 * cyc⁻¹ = d0 := by decide +kernel

theorem cyc_p01 : cyc * p01 * cyc⁻¹ = p12 := by decide +kernel

theorem cyc_p12 : cyc * p12 * cyc⁻¹ = p02 := by decide +kernel

theorem cyc_p02 : cyc * p02 * cyc⁻¹ = p01 := by decide +kernel

theorem cyc_m01 : cyc * m01 * cyc⁻¹ = m12 := by decide +kernel

theorem cyc_m12 : cyc * m12 * cyc⁻¹ = m02 := by decide +kernel

theorem cyc_m02 : cyc * m02 * cyc⁻¹ = m01 := by decide +kernel

theorem cyc'_p01 : cyc' * p01 * cyc'⁻¹ = m12 := by decide +kernel

theorem cyc'_m01 : cyc' * m01 * cyc'⁻¹ = p12 := by decide +kernel

theorem cyc'_m12 : cyc' * m12 * cyc'⁻¹ = p02 := by decide +kernel

theorem cyc'_m02 : cyc' * m02 * cyc'⁻¹ = m01 := by decide +kernel

theorem diagRefl_commute {x y : GL (Fin 3) (ZMod 3)} (hx : x ∈ diagRefl) (hy : y ∈ diagRefl) :
    x * y = y * x := by
  simp only [diagRefl, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> decide +kernel

section Invariant

variable {D : Set (GL (Fin 3) (ZMod 3))} (hc : ∀ d ∈ D, cyc * d * cyc⁻¹ ∈ D)
  (hc' : ∀ d ∈ D, cyc' * d * cyc'⁻¹ ∈ D)
include hc hc'

theorem swapRefl_subset_of_mem {x : GL (Fin 3) (ZMod 3)} (hx : x ∈ swapRefl) (hxD : x ∈ D) :
    swapRefl ⊆ D := by
  have hp01 : p01 ∈ D := by
    simp only [swapRefl, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hxD
    · have h1 := hc' _ hxD
      rw [cyc'_m01] at h1
      have h2 := hc _ h1
      rw [cyc_p12] at h2
      have h3 := hc _ h2
      rwa [cyc_p02] at h3
    · have h2 := hc _ hxD
      rw [cyc_p12] at h2
      have h3 := hc _ h2
      rwa [cyc_p02] at h3
    · have h1 := hc' _ hxD
      rw [cyc'_m12] at h1
      have h3 := hc _ h1
      rwa [cyc_p02] at h3
    · have h3 := hc _ hxD
      rwa [cyc_p02] at h3
    · have h0 := hc' _ hxD
      rw [cyc'_m02] at h0
      have h1 := hc' _ h0
      rw [cyc'_m01] at h1
      have h2 := hc _ h1
      rw [cyc_p12] at h2
      have h3 := hc _ h2
      rwa [cyc_p02] at h3
  have hp12 : p12 ∈ D := by have := hc _ hp01; rwa [cyc_p01] at this
  have hp02 : p02 ∈ D := by have := hc _ hp12; rwa [cyc_p12] at this
  have hm12 : m12 ∈ D := by have := hc' _ hp01; rwa [cyc'_p01] at this
  have hm02 : m02 ∈ D := by have := hc _ hm12; rwa [cyc_m12] at this
  have hm01 : m01 ∈ D := by have := hc _ hm02; rwa [cyc_m02] at this
  intro y hy
  simp only [swapRefl, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

omit hc' in
theorem diagRefl_subset_of_mem {x : GL (Fin 3) (ZMod 3)} (hx : x ∈ diagRefl) (hxD : x ∈ D) :
    diagRefl ⊆ D := by
  have hd0 : d0 ∈ D := by
    simp only [diagRefl, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hxD
    · have h1 := hc _ hxD
      rw [cyc_d1] at h1
      have h2 := hc _ h1
      rwa [cyc_d2] at h2
    · have h2 := hc _ hxD
      rwa [cyc_d2] at h2
  have hd1 : d1 ∈ D := by have := hc _ hd0; rwa [cyc_d0] at this
  have hd2 : d2 ∈ D := by have := hc _ hd1; rwa [cyc_d1] at this
  intro y hy
  simp only [diagRefl, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl <;> assumption

theorem eq_swapRefl_or_eq_monoRefl (hD : D ⊆ monoRefl)
    (hst : ∃ s ∈ D, ∃ t ∈ D, s * t ≠ t * s) : D = swapRefl ∨ D = monoRefl := by
  obtain ⟨s, hs, t, ht, hst⟩ := hst
  have hsw : swapRefl ⊆ D := by
    rcases hD hs with hs' | hs'
    · rcases hD ht with ht' | ht'
      · exact absurd (diagRefl_commute hs' ht') hst
      · exact swapRefl_subset_of_mem hc hc' ht' ht
    · exact swapRefl_subset_of_mem hc hc' hs' hs
  by_cases hd : ∃ x ∈ D, x ∈ diagRefl
  · obtain ⟨x, hxD, hx⟩ := hd
    right
    exact Set.Subset.antisymm hD (Set.union_subset (diagRefl_subset_of_mem hc hx hxD) hsw)
  · left
    refine Set.Subset.antisymm (fun y hy => ?_) hsw
    rcases hD hy with h | h
    · exact absurd ⟨y, hy, h⟩ hd
    · exact h

end Invariant

@[expose] def cubeOneMats : Finset Mat3 :=
  {!![1, 0, 0; 0, 1, 0; 0, 0, 1], !![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 0, 2; 1, 0, 0; 0, 2, 0],
   !![0, 0, 2; 2, 0, 0; 0, 1, 0], !![0, 0, 1; 2, 0, 0; 0, 2, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0],
   !![0, 2, 0; 0, 0, 2; 1, 0, 0], !![0, 1, 0; 0, 0, 2; 2, 0, 0], !![0, 2, 0; 0, 0, 1; 2, 0, 0]}

theorem card_cubeOneMats : cubeOneMats.card = 9 := by decide +kernel

theorem mat_cube_one : ∀ π : Fin 3 → Fin 3, Function.Bijective π →
    ∀ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) →
      signedMat π s * signedMat π s * signedMat π s = 1 → signedMat π s ∈ cubeOneMats := by
  decide +kernel

theorem card_alternatingGroup_cube_one :
    Nat.card {x : alternatingGroup (Fin 4) // x ^ 3 = 1} = 9 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem mem_of_pow_three_eq_one {G₀ : Subgroup (GL (Fin 3) (ZMod 3))} (hG₀ : G₀ ≤ monomial)
    (e : G₀ ≃* alternatingGroup (Fin 4)) {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ monomial)
    (hg3 : g ^ 3 = 1) : g ∈ G₀ := by
  have hmat : ∀ x : GL (Fin 3) (ZMod 3), x ∈ monomial → x ^ 3 = 1 →
      (x : Mat3) ∈ cubeOneMats := by
    intro x hx hx3
    refine forall_mem_monomial (P := fun M => M * M * M = 1 → M ∈ cubeOneMats) mat_cube_one hx
      ?_
    rw [← Units.val_mul, ← Units.val_mul, ← pow_three', hx3, Units.val_one]
  let F : {x : G₀ // x ^ 3 = 1} → {M : Mat3 // M ∈ cubeOneMats} := fun x =>
    ⟨((x.1 : GL (Fin 3) (ZMod 3)) : Mat3), hmat _ (hG₀ x.1.2) (by
      rw [← Subgroup.coe_pow, x.2, Subgroup.coe_one])⟩
  have hF : Function.Injective F := by
    intro x y h
    exact Subtype.ext (Subtype.ext (Units.ext (congrArg Subtype.val h)))
  have hcard : Nat.card {x : G₀ // x ^ 3 = 1} = 9 := by
    rw [← card_alternatingGroup_cube_one]
    exact Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
      rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_pow, MulEquiv.map_eq_one_iff])
  have hcard' : Nat.card {M : Mat3 // M ∈ cubeOneMats} = 9 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_cubeOneMats]
  obtain ⟨x, hx⟩ := (hF.bijective_of_nat_card_le (by rw [hcard, hcard'])).2
    ⟨(g : Mat3), hmat g hg hg3⟩
  have : (x.1 : GL (Fin 3) (ZMod 3)) = g := Units.ext (congrArg Subtype.val hx)
  rw [← this]
  exact x.1.2

theorem cyc_mem_monomial : cyc ∈ monomial :=
  mem_monomial_of ![1, 2, 0] ![1, 1, 1] (by decide) (by decide) (by decide)

theorem cyc'_mem_monomial : cyc' ∈ monomial :=
  mem_monomial_of ![1, 2, 0] ![2, 1, 2] (by decide) (by decide) (by decide)

theorem cyc_pow_three : cyc ^ 3 = 1 := by decide +kernel

theorem cyc'_pow_three : cyc' ^ 3 = 1 := by decide +kernel

theorem eq_swapRefl_or_eq_monoRefl_of_alternating {G₀ : Subgroup (GL (Fin 3) (ZMod 3))}
    (hG₀ : G₀ ≤ monomial) (e : G₀ ≃* alternatingGroup (Fin 4)) {D : Set (GL (Fin 3) (ZMod 3))}
    (hD : D ⊆ monomial) (hDr : ∀ d ∈ D, IsReflection d)
    (hinv : ∀ g ∈ G₀, ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hst : ∃ s ∈ D, ∃ t ∈ D, s * t ≠ t * s) :
    D = swapRefl ∨ D = monoRefl :=
  eq_swapRefl_or_eq_monoRefl
    (hinv _ (mem_of_pow_three_eq_one hG₀ e cyc_mem_monomial cyc_pow_three))
    (hinv _ (mem_of_pow_three_eq_one hG₀ e cyc'_mem_monomial cyc'_pow_three))
    (fun d hd => mem_monoRefl_of_isReflection (hD hd) (hDr d hd)) hst

theorem cyc_eq : cyc = p01 * p12 := by decide +kernel

theorem cyc'_eq : cyc' = m01 * p12 := by decide +kernel

theorem cyc_mem_closure : cyc ∈ Subgroup.closure swapRefl := by
  rw [cyc_eq]
  exact mul_mem (Subgroup.subset_closure (by simp [swapRefl]))
    (Subgroup.subset_closure (by simp [swapRefl]))

theorem cyc'_mem_closure : cyc' ∈ Subgroup.closure swapRefl := by
  rw [cyc'_eq]
  exact mul_mem (Subgroup.subset_closure (by simp [swapRefl]))
    (Subgroup.subset_closure (by simp [swapRefl]))

theorem exists_conj_p01 {x : GL (Fin 3) (ZMod 3)} (hx : x ∈ swapRefl) :
    ∃ g ∈ Subgroup.closure swapRefl, g * p01 * g⁻¹ = x := by
  have h1 := cyc_mem_closure
  have h2 := cyc'_mem_closure
  simp only [swapRefl, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, by group⟩
  · exact ⟨cyc ^ 2 * cyc', mul_mem (pow_mem h1 _) h2, by decide +kernel⟩
  · exact ⟨cyc, h1, cyc_p01⟩
  · exact ⟨cyc', h2, cyc'_p01⟩
  · exact ⟨cyc ^ 2, pow_mem h1 _, by decide +kernel⟩
  · exact ⟨cyc * cyc', mul_mem h1 h2, by decide +kernel⟩

theorem exists_conj_swapRefl {x y : GL (Fin 3) (ZMod 3)} (hx : x ∈ swapRefl)
    (hy : y ∈ swapRefl) : ∃ g ∈ Subgroup.closure swapRefl, g * y * g⁻¹ = x := by
  obtain ⟨g, hg, rfl⟩ := exists_conj_p01 hx
  obtain ⟨h, hh, rfl⟩ := exists_conj_p01 hy
  exact ⟨g * h⁻¹, mul_mem hg (inv_mem hh), by group⟩

end CFSG.RankThree.PartTwo.KFacts.KP14
