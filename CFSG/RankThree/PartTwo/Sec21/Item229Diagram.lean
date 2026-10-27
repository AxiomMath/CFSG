module

public import CFSG.RankThree.PartTwo.Sec21.MonomialCoords
public import CFSG.RankThree.PartTwo.KFacts.KP14MonomialStructure

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.RankThree.PartTwo.KFacts.KP14

theorem orderOf_p01_mul_p12 : orderOf (p01 * p12) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem orderOf_p12_mul_m01 : orderOf (p12 * m01) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem orderOf_p12_mul_d2 : orderOf (p12 * d2) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show (4 : ℕ) = 2 ^ (1 + 1) by norm_num]
  exact orderOf_eq_prime_pow (by decide +kernel) (by decide +kernel)

theorem p01_mul_m01 : p01 * m01 = m01 * p01 := by decide +kernel

theorem p01_mul_d2 : p01 * d2 = d2 * p01 := by decide +kernel

theorem p01_ne_m01 : p01 ≠ m01 := by decide +kernel

theorem p01_ne_d2 : p01 ≠ d2 := by decide +kernel

theorem swapRefl_conj :
    ∀ x ∈ swapRefl, ∃ g ∈ Subgroup.closure ({p01, p12, m01} : Set (GL (Fin 3) (ZMod 3))),
      g * p01 * g⁻¹ = x := by
  have h1 : p01 ∈ Subgroup.closure ({p01, p12, m01} : Set (GL (Fin 3) (ZMod 3))) :=
    Subgroup.subset_closure (by simp)
  have h2 : p12 ∈ Subgroup.closure ({p01, p12, m01} : Set (GL (Fin 3) (ZMod 3))) :=
    Subgroup.subset_closure (by simp)
  have h3 : m01 ∈ Subgroup.closure ({p01, p12, m01} : Set (GL (Fin 3) (ZMod 3))) :=
    Subgroup.subset_closure (by simp)
  intro x hx
  simp only [swapRefl, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, Subgroup.one_mem _, by decide +kernel⟩
  · exact ⟨p12 * m01 * (p01 * p12), Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 h3)
      (Subgroup.mul_mem _ h1 h2), by decide +kernel⟩
  · exact ⟨p01 * p12, Subgroup.mul_mem _ h1 h2, by decide +kernel⟩
  · exact ⟨p12 * p01 * p12 * (p12 * m01) * (p01 * p12),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 h1) h2)
        (Subgroup.mul_mem _ h2 h3)) (Subgroup.mul_mem _ h1 h2), by decide +kernel⟩
  · exact ⟨p12, h2, by decide +kernel⟩
  · exact ⟨m01 * p01 * p12, Subgroup.mul_mem _ (Subgroup.mul_mem _ h3 h1) h2, by decide +kernel⟩

theorem monoRefl_conj :
    ∀ x ∈ monoRefl, ∃ g ∈ Subgroup.closure ({p01, p12, d2} : Set (GL (Fin 3) (ZMod 3))),
      g * p01 * g⁻¹ = x ∨ g * d2 * g⁻¹ = x := by
  have h1 : p01 ∈ Subgroup.closure ({p01, p12, d2} : Set (GL (Fin 3) (ZMod 3))) :=
    Subgroup.subset_closure (by simp)
  have h2 : p12 ∈ Subgroup.closure ({p01, p12, d2} : Set (GL (Fin 3) (ZMod 3))) :=
    Subgroup.subset_closure (by simp)
  have h3 : d2 ∈ Subgroup.closure ({p01, p12, d2} : Set (GL (Fin 3) (ZMod 3))) :=
    Subgroup.subset_closure (by simp)
  intro x hx
  simp only [monoRefl, diagRefl, swapRefl, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact ⟨p01 * p12, Subgroup.mul_mem _ h1 h2, Or.inr (by decide +kernel)⟩
  · exact ⟨p12, h2, Or.inr (by decide +kernel)⟩
  · exact ⟨1, Subgroup.one_mem _, Or.inr (by decide +kernel)⟩
  · exact ⟨1, Subgroup.one_mem _, Or.inl (by decide +kernel)⟩
  · exact ⟨p12 * d2 * p12, Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 h3) h2,
      Or.inl (by decide +kernel)⟩
  · exact ⟨p01 * p12, Subgroup.mul_mem _ h1 h2, Or.inl (by decide +kernel)⟩
  · exact ⟨d2 * p01 * p12, Subgroup.mul_mem _ (Subgroup.mul_mem _ h3 h1) h2,
      Or.inl (by decide +kernel)⟩
  · exact ⟨p12, h2, Or.inl (by decide +kernel)⟩
  · exact ⟨d2 * p12, Subgroup.mul_mem _ h3 h2, Or.inl (by decide +kernel)⟩

theorem conj_p01_ne_d2 {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ monomial) : g * p01 * g⁻¹ ≠ d2 := by
  intro h
  have hp : p01 ∈ monomial := monoRefl_subset_monomial (by simp [monoRefl, swapRefl])
  have hd : d2 ∈ monomial := monoRefl_subset_monomial (by simp [monoRefl, diagRefl])
  have hm : (⟨g, hg⟩ : monomial) * ⟨p01, hp⟩ * (⟨g, hg⟩ : monomial)⁻¹ = ⟨d2, hd⟩ :=
    Subtype.ext h
  have hs := congrArg signChar hm
  rw [map_mul, map_mul, map_inv, mul_comm (signChar ⟨g, hg⟩), mul_assoc, mul_inv_cancel,
    mul_one, signChar_mk, signChar_mk] at hs
  revert hs
  decide +kernel

variable {G : Type*} [Group G] {A : Subgroup G}

theorem exists_diagram_of_image_eq_swapRefl (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    {D : Set (MulAut A)} (hD : coordGL f '' D = swapRefl) :
    ∃ t₁ ∈ D, ∃ t₂ ∈ D, ∃ t₃ ∈ D, orderOf (t₁ * t₂) = 3 ∧ orderOf (t₂ * t₃) = 3 ∧
      t₁ * t₃ = t₃ * t₁ ∧ t₁ ≠ t₃ ∧ Subgroup.closure D = Subgroup.closure {t₁, t₂, t₃} ∧
      (∀ φ ∈ D, ∃ g ∈ Subgroup.closure ({t₁, t₂, t₃} : Set (MulAut A)), g * t₁ * g⁻¹ = φ) ∧
      coordGL f t₁ = p01 ∧ coordGL f t₂ = p12 ∧ coordGL f t₃ = m01 := by
  have hinj := coordGL_injective f
  have hmem : ∀ x ∈ swapRefl, ∃ t ∈ D, coordGL f t = x := fun x hx => by
    rw [← hD] at hx
    exact hx
  obtain ⟨t₁, h₁, e₁⟩ := hmem p01 (by simp [swapRefl])
  obtain ⟨t₂, h₂, e₂⟩ := hmem p12 (by simp [swapRefl])
  obtain ⟨t₃, h₃, e₃⟩ := hmem m01 (by simp [swapRefl])
  have hmap : (Subgroup.closure ({t₁, t₂, t₃} : Set (MulAut A))).map (coordGL f) =
      Subgroup.closure {p01, p12, m01} := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
      e₁, e₂, e₃]
  have hconj : ∀ φ ∈ D, ∃ g ∈ Subgroup.closure ({t₁, t₂, t₃} : Set (MulAut A)),
      g * t₁ * g⁻¹ = φ := by
    intro φ hφ
    obtain ⟨g', hg', hgx⟩ := swapRefl_conj (coordGL f φ) (hD ▸ ⟨φ, hφ, rfl⟩)
    rw [← hmap] at hg'
    obtain ⟨g, hg, rfl⟩ := hg'
    refine ⟨g, hg, hinj ?_⟩
    rw [map_mul, map_mul, map_inv, e₁, hgx]
  refine ⟨t₁, h₁, t₂, h₂, t₃, h₃, ?_, ?_, ?_, ?_, ?_, hconj, e₁, e₂, e₃⟩
  · rw [← orderOf_injective _ hinj, map_mul, e₁, e₂, orderOf_p01_mul_p12]
  · rw [← orderOf_injective _ hinj, map_mul, e₂, e₃, orderOf_p12_mul_m01]
  · apply hinj
    rw [map_mul, map_mul, e₁, e₃, p01_mul_m01]
  · intro h
    apply p01_ne_m01
    rw [← e₁, ← e₃, h]
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      intro φ hφ
      obtain ⟨g, hg, rfl⟩ := hconj φ hφ
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (Subgroup.subset_closure (by simp)))
        (Subgroup.inv_mem _ hg)
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.subset_closure h₁
      · exact Subgroup.subset_closure h₂
      · exact Subgroup.subset_closure h₃

theorem exists_diagram_of_image_eq_monoRefl (f : Multiplicative (Fin 3 → ZMod 3) ≃* A)
    {D : Set (MulAut A)} (hD : coordGL f '' D = monoRefl) :
    ∃ t₁ ∈ D, ∃ t₂ ∈ D, ∃ t₃ ∈ D, orderOf (t₁ * t₂) = 3 ∧ orderOf (t₂ * t₃) = 4 ∧
      t₁ * t₃ = t₃ * t₁ ∧ t₁ ≠ t₃ ∧ Subgroup.closure D = Subgroup.closure {t₁, t₂, t₃} ∧
      (∀ φ ∈ D, ∃ g ∈ Subgroup.closure ({t₁, t₂, t₃} : Set (MulAut A)),
        g * t₁ * g⁻¹ = φ ∨ g * t₃ * g⁻¹ = φ) ∧
      (∀ w : MulAut A, coordGL f w ∈ monomial → w * t₁ * w⁻¹ ≠ t₃) ∧
      coordGL f t₁ = p01 ∧ coordGL f t₂ = p12 ∧ coordGL f t₃ = d2 := by
  have hinj := coordGL_injective f
  have hmem : ∀ x ∈ monoRefl, ∃ t ∈ D, coordGL f t = x := fun x hx => by
    rw [← hD] at hx
    exact hx
  obtain ⟨t₁, h₁, e₁⟩ := hmem p01 (by simp [monoRefl, swapRefl])
  obtain ⟨t₂, h₂, e₂⟩ := hmem p12 (by simp [monoRefl, swapRefl])
  obtain ⟨t₃, h₃, e₃⟩ := hmem d2 (by simp [monoRefl, diagRefl])
  have hmap : (Subgroup.closure ({t₁, t₂, t₃} : Set (MulAut A))).map (coordGL f) =
      Subgroup.closure {p01, p12, d2} := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
      e₁, e₂, e₃]
  have hconj : ∀ φ ∈ D, ∃ g ∈ Subgroup.closure ({t₁, t₂, t₃} : Set (MulAut A)),
      g * t₁ * g⁻¹ = φ ∨ g * t₃ * g⁻¹ = φ := by
    intro φ hφ
    obtain ⟨g', hg', hgx⟩ := monoRefl_conj (coordGL f φ) (hD ▸ ⟨φ, hφ, rfl⟩)
    rw [← hmap] at hg'
    obtain ⟨g, hg, rfl⟩ := hg'
    refine ⟨g, hg, ?_⟩
    rcases hgx with hgx | hgx
    · left
      apply hinj
      rw [map_mul, map_mul, map_inv, e₁, hgx]
    · right
      apply hinj
      rw [map_mul, map_mul, map_inv, e₃, hgx]
  refine ⟨t₁, h₁, t₂, h₂, t₃, h₃, ?_, ?_, ?_, ?_, ?_, hconj, ?_, e₁, e₂, e₃⟩
  · rw [← orderOf_injective _ hinj, map_mul, e₁, e₂, orderOf_p01_mul_p12]
  · rw [← orderOf_injective _ hinj, map_mul, e₂, e₃, orderOf_p12_mul_d2]
  · apply hinj
    rw [map_mul, map_mul, e₁, e₃, p01_mul_d2]
  · intro h
    apply p01_ne_d2
    rw [← e₁, ← e₃, h]
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      intro φ hφ
      obtain ⟨g, hg, h | h⟩ := hconj φ hφ <;> rw [← h] <;>
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (Subgroup.subset_closure (by simp)))
          (Subgroup.inv_mem _ hg)
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.subset_closure h₁
      · exact Subgroup.subset_closure h₂
      · exact Subgroup.subset_closure h₃
  · intro w hw h
    apply conj_p01_ne_d2 hw
    rw [← e₁, ← e₃, ← h, map_mul, map_mul, map_inv]

end CFSG.RankThree.PartTwo.Sec21
