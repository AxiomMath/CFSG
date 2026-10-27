module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFT7SecDih
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.Quasithin.SBd19F

section Split

variable {E G : Type*} [Group E] [Group G] {ρ : E →* G} {u₁ u₂ : E}

@[expose] def DihedralDistinct (ρ : E →* G) (u₁ u₂ : E) : Prop :=
  ∀ ⦃i j e d : ℕ⦄, i < 4 → j < 4 → e < 2 → d < 2 →
    (ρ u₁ * ρ u₂) ^ i * ρ u₁ ^ e = (ρ u₁ * ρ u₂) ^ j * ρ u₁ ^ d → i = j ∧ e = d

theorem map_dihedral_form (i e : ℕ) :
    ρ ((u₁ * u₂) ^ i * u₁ ^ e) = (ρ u₁ * ρ u₂) ^ i * ρ u₁ ^ e := by
  simp [map_mul, map_pow]

theorem closure_pair_inf_eq_bot {A : Subgroup E} (hA : ∀ a ∈ A, ρ a = 1) (h1 : u₁ * u₁ = 1)
    (h2 : u₂ * u₂ = 1) (h4 : (u₁ * u₂) ^ 4 = 1) (hd : DihedralDistinct ρ u₁ u₂) :
    Subgroup.closure ({u₁, u₂} : Set E) ⊓ A = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  obtain ⟨hxP, hxA⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨i, e, hi, he, rfl⟩ := exists_dihedral_form h1 h2 h4 hxP
  have h := hA _ hxA
  rw [map_dihedral_form] at h
  have h0 : (ρ u₁ * ρ u₂) ^ i * ρ u₁ ^ e = (ρ u₁ * ρ u₂) ^ 0 * ρ u₁ ^ 0 := by simpa using h
  obtain ⟨rfl, rfl⟩ := hd hi (by decide) he (by decide) h0
  simp

theorem dihedral_form_mem (i e : ℕ) :
    (u₁ * u₂) ^ i * u₁ ^ e ∈ Subgroup.closure ({u₁, u₂} : Set E) :=
  Subgroup.mul_mem _
    (Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) i)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) e)

theorem card_closure_pair_eq_eight [Finite E] (h1 : u₁ * u₁ = 1) (h2 : u₂ * u₂ = 1)
    (h4 : (u₁ * u₂) ^ 4 = 1) (hd : DihedralDistinct ρ u₁ u₂) :
    Nat.card (Subgroup.closure ({u₁, u₂} : Set E)) = 8 := by
  let g : Fin 4 × Fin 2 → Subgroup.closure ({u₁, u₂} : Set E) := fun p =>
    ⟨(u₁ * u₂) ^ (p.1 : ℕ) * u₁ ^ (p.2 : ℕ), dihedral_form_mem _ _⟩
  have hinj : Function.Injective g := by
    rintro ⟨i, e⟩ ⟨j, d⟩ h
    have h' : (u₁ * u₂) ^ (i : ℕ) * u₁ ^ (e : ℕ) = (u₁ * u₂) ^ (j : ℕ) * u₁ ^ (d : ℕ) :=
      congrArg Subtype.val h
    have := congrArg ρ h'
    rw [map_dihedral_form, map_dihedral_form] at this
    obtain ⟨hij, hed⟩ := hd i.2 j.2 e.2 d.2 this
    exact Prod.ext (Fin.ext hij) (Fin.ext hed)
  have hsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨i, e, hi, he, rfl⟩ := exists_dihedral_form h1 h2 h4 hx
    exact ⟨(⟨i, hi⟩, ⟨e, he⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)]
  simp

end Split

end CFSG.Quasithin.SBd19F
