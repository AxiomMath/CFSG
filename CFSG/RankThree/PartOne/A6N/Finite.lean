module

public import Certificates.Certificate14971

public section

namespace CFSG.RankThree.PartOne.A6N

open Equiv

@[expose] def Rel (y : alternatingGroup (Fin 6)) : Prop :=
  (y * a₀A) ^ 3 = 1 ∧ (y * a₀A⁻¹) ^ 4 = 1 ∧ (y * s₀A) ^ 5 = 1 ∧ (y * (a₀A * s₀A)) ^ 2 = 1

theorem rel_y₀ : Rel y₀A := by
  have h1 : (y₀ * a₀) ^ 3 = 1 := by decide +kernel
  have h2 : (y₀ * a₀⁻¹) ^ 4 = 1 := by decide +kernel
  have h3 : (y₀ * s₀) ^ 5 = 1 := by decide +kernel
  have h4 : (y₀ * (a₀ * s₀)) ^ 2 = 1 := by decide +kernel
  exact ⟨Subtype.ext (by simpa using h1), Subtype.ext (by simpa using h2),
    Subtype.ext (by simpa using h3), Subtype.ext (by simpa using h4)⟩

theorem rel_y₁ : Rel y₁A := by
  have h1 : (y₁ * a₀) ^ 3 = 1 := by decide +kernel
  have h2 : (y₁ * a₀⁻¹) ^ 4 = 1 := by decide +kernel
  have h3 : (y₁ * s₀) ^ 5 = 1 := by decide +kernel
  have h4 : (y₁ * (a₀ * s₀)) ^ 2 = 1 := by decide +kernel
  exact ⟨Subtype.ext (by simpa using h1), Subtype.ext (by simpa using h2),
    Subtype.ext (by simpa using h3), Subtype.ext (by simpa using h4)⟩

theorem y₀A_ne_y₁A : y₀A ≠ y₁A := fun h => y₀_ne_y₁ (congrArg Subtype.val h)

theorem rel_map (ψ : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6))
    (ha : ψ a₀A = a₀A) (hs : ψ s₀A = s₀A) {y : alternatingGroup (Fin 6)} (h : Rel y) :
    Rel (ψ y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [map_pow, map_mul, ha] using congrArg ψ h1
  · simpa [map_pow, map_mul, map_inv, ha] using congrArg ψ h2
  · simpa [map_pow, map_mul, hs] using congrArg ψ h3
  · simpa [map_pow, map_mul, ha, hs] using congrArg ψ h4

section Facts


theorem a6_finite_checks :
    (∀ x : Perm (Fin 6), x * a₀ = a₀ * x → ∃ i : Fin 5, x = a₀ ^ (i : ℕ)) ∧
      (∀ y : Perm (Fin 6), (y * a₀) ^ 3 = 1 → (y * a₀⁻¹) ^ 4 = 1 → (y * s₀) ^ 5 = 1 →
        (y * (a₀ * s₀)) ^ 2 = 1 → y = y₀ ∨ y = y₁) ∧
      Subgroup.closure ({a₀A, s₀A, y₀A} : Set (alternatingGroup (Fin 6))) = ⊤ :=
  Certificates.certificate14971

theorem centralizer_a₀ {x : alternatingGroup (Fin 6)} (h : x * a₀A = a₀A * x) :
    ∃ i : ℕ, x = a₀A ^ i := by
  obtain ⟨i, hi⟩ := a6_finite_checks.1 x.1
    (by simpa [coe_a₀A] using congrArg Subtype.val h)
  exact ⟨i, Subtype.ext hi⟩

theorem rel_cases {y : alternatingGroup (Fin 6)} (h : Rel y) : y = y₀A ∨ y = y₁A := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have := a6_finite_checks.2.1 y.1
    (by simpa [coe_a₀A] using congrArg Subtype.val h1)
    (by simpa [coe_a₀A] using congrArg Subtype.val h2)
    (by simpa [coe_s₀A] using congrArg Subtype.val h3)
    (by simpa [coe_a₀A, coe_s₀A] using congrArg Subtype.val h4)
  rcases this with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem hom_ext_gen {G : Type*} [Group G] {f g : alternatingGroup (Fin 6) →* G}
    (ha : f a₀A = g a₀A) (hs : f s₀A = g s₀A) (hy : f y₀A = g y₀A) : f = g := by
  have hgen := a6_finite_checks.2.2
  have h : Set.EqOn f g (Subgroup.closure ({a₀A, s₀A, y₀A} : Set (alternatingGroup (Fin 6)))) := by
    refine MonoidHom.eqOn_closure ?_
    intro x hx
    rcases hx with rfl | rfl | rfl
    exacts [ha, hs, hy]
  rw [hgen] at h
  exact MonoidHom.ext fun x => h (Subgroup.mem_top x)

theorem aut_dichotomy (ψ : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6))
    (ha : ψ a₀A = a₀A) (hs : ψ s₀A = s₀A) :
    ψ = MulEquiv.refl _ ∨ (ψ y₀A = y₁A ∧ ψ y₁A = y₀A) := by
  rcases rel_cases (rel_map ψ ha hs rel_y₀) with h | h
  · left
    refine MulEquiv.ext fun x => ?_
    have := DFunLike.congr_fun (hom_ext_gen (f := ψ.toMonoidHom) (g := MonoidHom.id _) ha hs h) x
    simpa using this
  · right
    refine ⟨h, ?_⟩
    rcases rel_cases (rel_map ψ ha hs rel_y₁) with h' | h'
    · exact h'
    · exfalso
      exact y₀A_ne_y₁A (ψ.injective (h.trans h'.symm))

theorem aut_sq (ψ : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6))
    (ha : ψ a₀A = a₀A) (hs : ψ s₀A = s₀A) (x : alternatingGroup (Fin 6)) : ψ (ψ x) = x := by
  rcases aut_dichotomy ψ ha hs with rfl | ⟨h1, h2⟩
  · rfl
  · have := DFunLike.congr_fun (hom_ext_gen (f := (ψ.toMonoidHom).comp ψ.toMonoidHom)
      (g := MonoidHom.id _) (by simp [ha]) (by simp [hs]) (by simp [h1, h2])) x
    simpa using this

end Facts

end CFSG.RankThree.PartOne.A6N
