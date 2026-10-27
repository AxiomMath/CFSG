module

public import CFSG.Monster.Existence.Co1Bridge

public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Monster CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.Existence.Co1Bridge
  CFSG.Blueprint

theorem exists_conj_three_of_equiv {G M : Type*} [Group G] [Group M] (OL H : Subgroup M)
    (hHO : H = OL) (φ : G ≃* ↥H) (mono : ℕ → M)
    (hmem : ∀ i ∈ ({1, 2, 6} : Finset ℕ), mono i ∈ OL ∧ mono i * mono i = 1 ∧ mono i ≠ 1)
    (hcls : ∀ u ∈ OL, u * u = 1 → u ≠ 1 →
      ∃ i ∈ ({1, 2, 6} : Finset ℕ), ∃ g ∈ OL, g * mono i * g⁻¹ = u) :
    ∃ c : ℕ → G, ∀ s : G, orderOf s = 2 →
      ∃ i ∈ ({1, 2, 6} : Finset ℕ), IsConj (c i) s := by
  have hH : ∀ u ∈ OL, u ∈ H := fun u hu => by
    rw [hHO]
    exact hu
  refine ⟨fun i => if h : i ∈ ({1, 2, 6} : Finset ℕ) then
    φ.symm ⟨mono i, hH _ (hmem i h).1⟩ else 1, ?_⟩
  intro s hs
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [hs, pow_two] at h
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    omega
  have hu : ((φ s : H) : M) ∈ OL := by
    rw [← hHO]
    exact (φ s).2
  have huu : ((φ s : H) : M) * ((φ s : H) : M) = 1 := by
    have h : φ s * φ s = 1 := by
      rw [← map_mul, hs2, map_one]
    exact congrArg Subtype.val h
  have hu1 : ((φ s : H) : M) ≠ 1 := fun h =>
    hs1 (φ.injective (Subtype.ext (by simpa using h)))
  obtain ⟨i, hi, g, hg, hgi⟩ := hcls _ hu huu hu1
  refine ⟨i, hi, isConj_iff.2 ⟨φ.symm ⟨g, hH g hg⟩, ?_⟩⟩
  apply φ.injective
  apply Subtype.ext
  simp only [hi, ↓reduceDIte, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hgi

theorem exists_conj_three_of_chevalley
    (mono : ℕ → GLV)
    (hmem : ∀ i ∈ ({1, 2, 6} : Finset ℕ), mono i ∈ OLvis ∧ mono i * mono i = 1 ∧ mono i ≠ 1)
    (hcls : ∀ u ∈ OLvis, u * u = 1 → u ≠ 1 →
      ∃ i ∈ ({1, 2, 6} : Finset ℕ), ∃ g ∈ OLvis, g * mono i * g⁻¹ = u) :
    ∃ c : ℕ → NativeSporadic.Co1, ∀ s : NativeSporadic.Co1, orderOf s = 2 →
      ∃ i ∈ ({1, 2, 6} : Finset ℕ), IsConj (c i) s :=
  exists_conj_three_of_equiv OLvis Hvis Hvis_eq_OLvis co1EquivHvis mono hmem hcls

end CFSG.Sporadic.Co1.Module
