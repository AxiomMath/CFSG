module

public import CFSG.Quasithin.Vol2.Ch11SecAVi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem exists_isVi (hF : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    ∃ U₁ U₂ U₃ : Subgroup G, IsVi T L I n 1 U₁ ∧ IsVi T L I n 2 U₂ ∧ IsVi T L I n 3 U₃ ∧
      U₁ ≤ U₂ ∧ U₂ ≤ U₃ ∧ (∀ U, IsVi T L I n 1 U → U = U₁) ∧
      (∀ U, IsVi T L I n 2 U → U = U₂) ∧ (∀ U, IsVi T L I n 3 U → U = U₃) := by
  obtain ⟨W₁, W₂, W₃, h₁, h₂, h₃, h₁₂, h₂₃, u₁, u₂, u₃⟩ := hasUniqueFlag hF h1102 h
  refine ⟨W₁.map (fsuV T I).subtype, W₂.map (fsuV T I).subtype, W₃.map (fsuV T I).subtype,
    isVi_of_isFlagW h h₁ u₁, isVi_of_isFlagW h h₂ u₂, isVi_of_isFlagW h h₃ u₃,
    Subgroup.map_mono h₁₂, Subgroup.map_mono h₂₃, fun U hU => eq_map_of_isVi h hU u₁,
    fun U hU => eq_map_of_isVi h hU u₂, fun U hU => eq_map_of_isVi h hU u₃⟩

theorem isVi_existsUnique (hF : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {i : ℕ}
    (hi1 : 1 ≤ i) (hi3 : i ≤ 3) : ∃! U : Subgroup G, IsVi T L I n i U := by
  obtain ⟨U₁, U₂, U₃, h₁, h₂, h₃, -, -, u₁, u₂, u₃⟩ := exists_isVi hF h1102 h
  interval_cases i
  · exact ⟨U₁, h₁, u₁⟩
  · exact ⟨U₂, h₂, u₂⟩
  · exact ⟨U₃, h₃, u₃⟩

theorem IsVi.eq (hF : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {i : ℕ}
    (hi1 : 1 ≤ i) (hi3 : i ≤ 3) {U U' : Subgroup G} (hU : IsVi T L I n i U)
    (hU' : IsVi T L I n i U') : U = U' :=
  (isVi_existsUnique hF h1102 h hi1 hi3).unique hU hU'

theorem IsVi.mono₁₂ (hF : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    {U₁ U₂ : Subgroup G} (hU₁ : IsVi T L I n 1 U₁) (hU₂ : IsVi T L I n 2 U₂) : U₁ ≤ U₂ := by
  obtain ⟨V₁, V₂, -, -, -, -, h₁₂, -, u₁, u₂, -⟩ := exists_isVi hF h1102 h
  rw [u₁ U₁ hU₁, u₂ U₂ hU₂]
  exact h₁₂

theorem IsVi.mono₂₃ (hF : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    {U₂ U₃ : Subgroup G} (hU₂ : IsVi T L I n 2 U₂) (hU₃ : IsVi T L I n 3 U₃) : U₂ ≤ U₃ := by
  obtain ⟨-, V₂, V₃, -, -, -, -, h₂₃, -, u₂, u₃⟩ := exists_isVi hF h1102 h
  rw [u₂ U₂ hU₂, u₃ U₃ hU₃]
  exact h₂₃

theorem IsVi.mono₁₃ (hF : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    {U₁ U₃ : Subgroup G} (hU₁ : IsVi T L I n 1 U₁) (hU₃ : IsVi T L I n 3 U₃) : U₁ ≤ U₃ := by
  obtain ⟨V₁, V₂, V₃, -, -, -, h₁₂, h₂₃, u₁, -, u₃⟩ := exists_isVi hF h1102 h
  rw [u₁ U₁ hU₁, u₃ U₃ hU₃]
  exact h₁₂.trans h₂₃

end CFSG.Quasithin.Vol2.Ch11.SecA
