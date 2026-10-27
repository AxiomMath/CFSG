module

public import CFSG.LocalAnalysis.WeakClosure81.Orth6Minus.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Orth6Minus

open CFSG.ClassicalGroups.Orthogonal

private theorem permutationGL_mul_diagGL_mul_inv {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Semiring K]
    (σ : Equiv.Perm ι) (t : ι → Kˣ) :
    TauCeti.permutationGL (k := K) σ * TauCeti.diagGL t *
        (TauCeti.permutationGL (k := K) σ)⁻¹ =
      TauCeti.diagGL fun i => t (σ⁻¹ i) := by
  rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix
    (g := TauCeti.permutationGL (k := K) σ) (π := σ⁻¹) (TauCeti.permutationGL_coe σ),
    mul_inv_cancel_right]
  congr

private lemma units_neg_one_mul_self (K : Type*) [Field K] : (-1 : Kˣ) * (-1) = 1 := by
  ext
  simp

private lemma units_neg_one_inv (K : Type*) [Field K] : (-1 : Kˣ)⁻¹ = -1 := by
  rw [inv_eq_of_mul_eq_one_right (units_neg_one_mul_self K)]

private lemma sign_mul_self {K : Type*} [Field K] {a : Kˣ} (ha : a = 1 ∨ a = -1) :
    a * a = 1 := by
  rcases ha with rfl | rfl
  · simp
  · exact units_neg_one_mul_self K

private lemma sign_mul {K : Type*} [Field K] {a b : Kˣ} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) : a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

private lemma sign_inv {K : Type*} [Field K] {a : Kˣ} (ha : a = 1 ∨ a = -1) :
    a⁻¹ = 1 ∨ a⁻¹ = -1 := by
  rcases ha with rfl | rfl
  · simp
  · exact Or.inr (units_neg_one_inv K)

private abbrev diagSign (K : Type*) [Field K] : Subgroup (GL Six K) where
  carrier := {g | ∃ ε : Six → Kˣ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ g = TauCeti.diagGL ε}
  one_mem' := ⟨1, fun _ => Or.inl rfl, (map_one (TauCeti.diagGL (k := K) (ι := Six))).symm⟩
  mul_mem' := by
    rintro g h ⟨ε, hε, rfl⟩ ⟨ε', hε', rfl⟩
    exact ⟨ε * ε', fun i => sign_mul (hε i) (hε' i),
      (map_mul (TauCeti.diagGL (k := K) (ι := Six)) ε ε').symm⟩
  inv_mem' := by
    rintro g ⟨ε, hε, rfl⟩
    exact ⟨ε⁻¹, fun i => sign_inv (hε i),
      (map_inv (TauCeti.diagGL (k := K) (ι := Six)) ε).symm⟩

private theorem isPGroup_diagSign (K : Type*) [Field K] : IsPGroup 2 (diagSign K) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  obtain ⟨ε, hε, hg⟩ := g.2
  rw [hg]
  have hε2 : ε * ε = 1 := by
    funext i
    exact sign_mul_self (hε i)
  show TauCeti.diagGL (k := K) (ι := Six) ε ^ 2 = 1
  rw [pow_two, ← map_mul, hε2, map_one]

private abbrev rot : Equiv.Perm Six := permA * permC

private abbrev perms : Finset (Equiv.Perm Six) :=
  {1, rot, rot ^ 2, rot ^ 3, permA, permA * rot, permA * rot ^ 2, permA * rot ^ 3}

private lemma mem_perms_iff (σ : Equiv.Perm Six) :
    σ ∈ perms ↔ σ = 1 ∨ σ = rot ∨ σ = rot ^ 2 ∨ σ = rot ^ 3 ∨ σ = permA ∨
      σ = permA * rot ∨ σ = permA * rot ^ 2 ∨ σ = permA * rot ^ 3 := by
  simp [perms]

private lemma mul_mem_perms {a b : Equiv.Perm Six} (ha : a ∈ perms) (hb : b ∈ perms) :
    a * b ∈ perms := by
  rw [mem_perms_iff] at ha hb ⊢
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private lemma inv_mem_perms {a : Equiv.Perm Six} (ha : a ∈ perms) : a⁻¹ ∈ perms := by
  rw [mem_perms_iff] at ha ⊢
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private abbrev dihedral : Subgroup (Equiv.Perm Six) where
  carrier := ↑perms
  one_mem' := by decide +kernel
  mul_mem' := fun ha hb => mul_mem_perms ha hb
  inv_mem' := fun ha => inv_mem_perms ha

private lemma pow_four_eq_one_of_mem_perms {σ : Equiv.Perm Six} (hσ : σ ∈ perms) :
    σ ^ 4 = 1 := by
  rw [mem_perms_iff] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem isPGroup_dihedral : IsPGroup 2 dihedral := by
  intro σ
  refine ⟨2, ?_⟩
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact pow_four_eq_one_of_mem_perms σ.2

private abbrev dihedralGL (K : Type*) [Field K] : Subgroup (GL Six K) :=
  dihedral.map (TauCeti.permutationGL (k := K))

private theorem isPGroup_dihedralGL (K : Type*) [Field K] : IsPGroup 2 (dihedralGL K) :=
  isPGroup_dihedral.map (TauCeti.permutationGL (k := K))

private lemma mem_diagSign_negCoordGL (K : Type*) [Field K] (r s : Six) :
    negCoordGL (K := K) {r, s} ∈ diagSign K :=
  ⟨fun i => if i ∈ ({r, s} : Finset Six) then -1 else 1, fun i => by
    by_cases h : i ∈ ({r, s} : Finset Six) <;> simp [h], rfl⟩

private lemma permA_mem_dihedral : permA ∈ dihedral := by
  show permA ∈ perms
  decide +kernel

private lemma permC_mem_dihedral : permC ∈ dihedral := by
  show permC ∈ perms
  decide +kernel

private theorem dihedralGL_le_normalizer (K : Type*) [Field K] :
    dihedralGL K ≤ Subgroup.normalizer (diagSign K) := by
  rintro x ⟨σ, -, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨ε, hε, rfl⟩
    exact ⟨fun i => ε (σ⁻¹ i), fun i => hε (σ⁻¹ i),
      permutationGL_mul_diagGL_mul_inv σ ε⟩
  · rintro ⟨ε, hε, hg⟩
    refine ⟨fun i => ε (σ i), fun i => hε (σ i), ?_⟩
    have h2 := permutationGL_mul_diagGL_mul_inv (K := K) (σ := σ⁻¹) ε
    simp only [map_inv, inv_inv] at h2
    calc g = (TauCeti.permutationGL (k := K) σ)⁻¹ *
          (TauCeti.permutationGL (k := K) σ * g *
            (TauCeti.permutationGL (k := K) σ)⁻¹) *
          TauCeti.permutationGL (k := K) σ := by group
      _ = (TauCeti.permutationGL (k := K) σ)⁻¹ * TauCeti.diagGL ε *
          TauCeti.permutationGL (k := K) σ := by rw [hg]
      _ = TauCeti.diagGL (fun i => ε (σ i)) := h2

theorem isPGroup_closure_gens (K : Type*) [Field K] :
    IsPGroup 2 (Subgroup.closure (gens K)) := by
  refine IsPGroup.to_le (H := Subgroup.closure (gens K))
    (K := dihedralGL K ⊔ diagSign K) ?_ ?_
  · exact IsPGroup.to_sup_of_normal_right' (isPGroup_dihedralGL K) (isPGroup_diagSign K)
      (dihedralGL_le_normalizer K)
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [gens, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hg
    rcases hg with ⟨r, s, -, rfl⟩ | rfl | rfl
    · exact Subgroup.mem_sup_right (mem_diagSign_negCoordGL K r s)
    · exact Subgroup.mem_sup_left
        (Subgroup.mem_map_of_mem (TauCeti.permutationGL (k := K)) permA_mem_dihedral)
    · exact Subgroup.mem_sup_left
        (Subgroup.mem_map_of_mem (TauCeti.permutationGL (k := K)) permC_mem_dihedral)

end CFSG.LocalAnalysis.WeakClosure81.Orth6Minus
