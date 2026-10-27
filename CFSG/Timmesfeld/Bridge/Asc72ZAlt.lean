module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs

public section

namespace CFSG.Timmesfeld.Bridge.Asc72.AltFive

open Equiv

@[expose] def c0 : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def x0 : alternatingGroup (Fin 5) :=
  ⟨swap 0 2 * swap 1 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def y0 : alternatingGroup (Fin 5) :=
  ⟨swap 0 3 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def o1 : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 2 4, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def o3 : alternatingGroup (Fin 5) :=
  ⟨swap 0 4 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def k1 : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 3 4, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def k3 : alternatingGroup (Fin 5) :=
  ⟨swap 1 4 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem k1_conj : k1 * c0 * k1⁻¹ = o1 := by decide

theorem k3_conj : k3 * c0 * k3⁻¹ = o3 := by decide

set_option maxRecDepth 20000 in
theorem exists_conj_c0 : ∀ g : alternatingGroup (Fin 5), g * g = 1 → g ≠ 1 →
    ∃ σ : alternatingGroup (Fin 5), σ * g * σ⁻¹ = c0 := by
  decide

theorem eq_of_commute_c0 : ∀ g : alternatingGroup (Fin 5), g * g = 1 → g * c0 = c0 * g →
    g = 1 ∨ g = c0 ∨ g = x0 ∨ g = y0 := by
  decide

set_option maxRecDepth 20000 in
theorem perm_cases : ∀ π : Perm (Fin 5), π * π = 1 → π * (c0 : Perm (Fin 5)) = c0 * π →
    π * (x0 : Perm (Fin 5)) * π⁻¹ = y0 →
    (x0 : Perm (Fin 5)) * (π * (x0 : Perm (Fin 5))⁻¹ * π⁻¹) * c0 = 1 ∧
      (π * (o1 : Perm (Fin 5)) * π⁻¹ = o1 ∨ π * (o3 : Perm (Fin 5)) * π⁻¹ = o3) := by
  decide

theorem not_commute_c0 {γ : alternatingGroup (Fin 5)} (hγ : γ = o1 ∨ γ = o3) :
    γ * c0 ≠ c0 * γ := by
  rcases hγ with rfl | rfl <;> decide

set_option maxRecDepth 20000 in
theorem spread {γ : alternatingGroup (Fin 5)} (hγ : γ = o1 ∨ γ = o3) :
    ∀ y : alternatingGroup (Fin 5), y * y = 1 → y * c0 = c0 * y ∨
      ∃ t : alternatingGroup (Fin 5), t * c0 = c0 * t ∧
        y * (t * γ * t⁻¹) = t * γ * t⁻¹ * y := by
  rcases hγ with rfl | rfl <;> decide

theorem aut_facts (ψ : MulAut (alternatingGroup (Fin 5))) (hψψ : ∀ y, ψ (ψ y) = y)
    (hψc : ψ c0 = c0) {e₁ e₂ : alternatingGroup (Fin 5)} (he₁ : e₁ * e₁ = 1)
    (he₂ : e₂ * e₂ = 1) (hc₁ : e₁ * c0 = c0 * e₁) (hc₂ : e₂ * c0 = c0 * e₂) (h₁1 : e₁ ≠ 1)
    (h₂1 : e₂ ≠ 1) (h₁c : e₁ ≠ c0) (h₂c : e₂ ≠ c0) (h₁₂ : e₁ ≠ e₂) (hψe : ψ e₁ = e₂) :
    x0 * ψ x0⁻¹ * c0 = 1 ∧ ∃ γ k : alternatingGroup (Fin 5), (γ = o1 ∨ γ = o3) ∧ ψ γ = γ ∧
      k * c0 * k⁻¹ = γ := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)
  obtain ⟨π, hπ⟩ := hbij.2 ψ
  have key : ∀ y : alternatingGroup (Fin 5),
      ((ψ y : alternatingGroup (Fin 5)) : Perm (Fin 5)) = π * y * π⁻¹ := fun y => by
    rw [← hπ, MulAut.conjNormal_apply]
  have hππ : π * π = 1 := by
    apply hbij.1
    rw [map_mul, hπ, map_one]
    exact MulEquiv.ext fun y => by rw [MulAut.mul_apply, hψψ, MulAut.one_apply]
  have hψx : ψ x0 = y0 := by
    rcases eq_of_commute_c0 e₁ he₁ hc₁ with h | h | h | h
    · exact absurd h h₁1
    · exact absurd h h₁c
    · rcases eq_of_commute_c0 e₂ he₂ hc₂ with h' | h' | h' | h'
      · exact absurd h' h₂1
      · exact absurd h' h₂c
      · exact absurd (h.trans h'.symm) h₁₂
      · rw [← h, hψe, h']
    · rcases eq_of_commute_c0 e₂ he₂ hc₂ with h' | h' | h' | h'
      · exact absurd h' h₂1
      · exact absurd h' h₂c
      · rw [← h', ← hψe, hψψ, h]
      · exact absurd (h.trans h'.symm) h₁₂
  have hπc : π * (c0 : Perm (Fin 5)) = c0 * π := by
    have h := key c0
    rw [hψc] at h
    calc π * (c0 : Perm (Fin 5)) = π * c0 * π⁻¹ * π := by group
      _ = c0 * π := by rw [← h]
  have hπx : π * (x0 : Perm (Fin 5)) * π⁻¹ = y0 := by rw [← key, hψx]
  obtain ⟨h1, h2⟩ := perm_cases π hππ hπc hπx
  refine ⟨Subtype.ext ?_, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, key, Subgroup.coe_inv, Subgroup.coe_one]
    exact h1
  · rcases h2 with h2 | h2
    · exact ⟨o1, k1, Or.inl rfl, Subtype.ext (by rw [key, h2]), k1_conj⟩
    · exact ⟨o3, k3, Or.inr rfl, Subtype.ext (by rw [key, h2]), k3_conj⟩

theorem nonempty_psl2Model_two_equiv :
    Nonempty (CFSG.Theory.Comparator.PSL2Model 2 ≃* alternatingGroup (Fin 5)) := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 two_ne_zero]
    norm_num
  obtain ⟨e⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hK)
  exact ⟨(CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 _).trans e⟩

end CFSG.Timmesfeld.Bridge.Asc72.AltFive
