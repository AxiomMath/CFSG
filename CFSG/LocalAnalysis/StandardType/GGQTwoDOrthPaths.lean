module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPathsPair
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPathsPath
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPathsFar
import CFSG.LocalAnalysis.StandardType.GGOrthRk1AllPairs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus

variable {p r : ℕ}

theorem omPlusRefl_comm_iff_supp (hp : p.Prime) (x y : OmPlusIdx r) :
    omPlusRefl p x * omPlusRefl p y = omPlusRefl p y * omPlusRefl p x ↔
      omSupp x = omSupp y ∨ Disjoint (omSupp x) (omSupp y) := by
  constructor
  · intro h
    rcases (omPlusRefl_commute_iff_supports hp x y).mp h with h1 | h1
    · exact Or.inl (omSupp_eq_iff.mpr h1)
    · exact Or.inr h1
  · intro h
    rcases h with h1 | h1
    · exact (omPlusRefl_commute_iff_supports hp x y).mpr (Or.inl (omSupp_eq_iff.mp h1))
    · exact (omPlusRefl_commute_iff_supports hp x y).mpr (Or.inr h1)

theorem omPlusRefl_not_comm_iff_supp (hp : p.Prime) (x y : OmPlusIdx r) :
    omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x ↔
      omSupp x ≠ omSupp y ∧ ¬ Disjoint (omSupp x) (omSupp y) := by
  exact (not_congr (omPlusRefl_comm_iff_supp hp x y)).trans not_or

theorem disjoint_of_comm_both {A B C : Finset (Fin r)} (hAB : A ≠ B) (hAB' : ¬ Disjoint A B)
    (hA : A = C ∨ Disjoint A C) (hB : B = C ∨ Disjoint B C) : Disjoint A C ∧ Disjoint B C := by
  rcases hA with hAC | hAC <;> rcases hB with hBC | hBC
  · exact absurd (hAC.trans hBC.symm) hAB
  · exact absurd ((hAC.symm ▸ hBC).symm) hAB'
  · exact absurd (hBC.symm ▸ hAC) hAB'
  · exact ⟨hAC, hBC⟩

theorem omSigned_conj_pair (hp : p.Prime) (hr : 3 ≤ r) {x y : OmPlusIdx r}
    (h : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x) :
    ∃ w ∈ omSigned p r,
      omPlusRefl p (omStd r (by omega) ⟨0, by omega⟩) = w * omPlusRefl p x * w⁻¹ ∧
      omPlusRefl p (omStd r (by omega) ⟨1, by omega⟩) = w * omPlusRefl p y * w⁻¹ := by
  have h' := (omPlusRefl_not_comm_iff_supp hp x y).mp h
  obtain ⟨m, hx, hy⟩ := omMove_pair hr h'.1 h'.2
  exact ⟨m.w, m.hw, by rw [← hx, m.hf x], by rw [← hy, m.hf y]⟩

theorem omSigned_conj_path (hp : p.Prime) (hr : 4 ≤ r) {x y z : OmPlusIdx r}
    (hxz : omPlusRefl p x * omPlusRefl p z = omPlusRefl p z * omPlusRefl p x) (hne : x ≠ z)
    (hxy : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x)
    (hyz : omPlusRefl p y * omPlusRefl p z ≠ omPlusRefl p z * omPlusRefl p y) :
    (∃ w ∈ omSigned p r,
      omPlusRefl p (omStd r (by omega) ⟨0, by omega⟩) = w * omPlusRefl p x * w⁻¹ ∧
      omPlusRefl p (omStd r (by omega) ⟨1, by omega⟩) = w * omPlusRefl p y * w⁻¹ ∧
      omPlusRefl p (omStd r (by omega) ⟨2, by omega⟩) = w * omPlusRefl p z * w⁻¹) ∨
    (∃ w ∈ omSigned p r,
      omPlusRefl p (omStd r (by omega) ⟨r - 2, by omega⟩) = w * omPlusRefl p x * w⁻¹ ∧
      omPlusRefl p (omStd r (by omega) ⟨r - 3, by omega⟩) = w * omPlusRefl p y * w⁻¹ ∧
      omPlusRefl p (omStd r (by omega) ⟨r - 1, by omega⟩) = w * omPlusRefl p z * w⁻¹) := by
  rcases (omPlusRefl_comm_iff_supp hp x z).mp hxz with hs | hd
  · right
    obtain ⟨m, hx, hy, hz⟩ := omMove_fork hr hs hne
      ((omPlusRefl_not_comm_iff_supp hp x y).mp hxy).1
      ((omPlusRefl_not_comm_iff_supp hp x y).mp hxy).2
    exact ⟨m.w, m.hw, by rw [← hx, m.hf x], by rw [← hy, m.hf y], by rw [← hz, m.hf z]⟩
  · left
    obtain ⟨m, hx, hy, hz⟩ := omMove_chain hr hd
      ((omPlusRefl_not_comm_iff_supp hp x y).mp hxy).2
      ((omPlusRefl_not_comm_iff_supp hp y z).mp hyz).2
    exact ⟨m.w, m.hw, by rw [← hx, m.hf x], by rw [← hy, m.hf y], by rw [← hz, m.hf z]⟩

theorem omFar_six_le_of_comm (hp : p.Prime) {x₁ x₂ x₃ x₄ : OmPlusIdx r}
    (h12 : omPlusRefl p x₁ * omPlusRefl p x₂ ≠ omPlusRefl p x₂ * omPlusRefl p x₁)
    (h34 : omPlusRefl p x₃ * omPlusRefl p x₄ ≠ omPlusRefl p x₄ * omPlusRefl p x₃)
    (h13 : omPlusRefl p x₁ * omPlusRefl p x₃ = omPlusRefl p x₃ * omPlusRefl p x₁)
    (h14 : omPlusRefl p x₁ * omPlusRefl p x₄ = omPlusRefl p x₄ * omPlusRefl p x₁)
    (h23 : omPlusRefl p x₂ * omPlusRefl p x₃ = omPlusRefl p x₃ * omPlusRefl p x₂)
    (h24 : omPlusRefl p x₂ * omPlusRefl p x₄ = omPlusRefl p x₄ * omPlusRefl p x₂) : 6 ≤ r := by
  have h12' := (omPlusRefl_not_comm_iff_supp hp x₁ x₂).mp h12
  have h34' := (omPlusRefl_not_comm_iff_supp hp x₃ x₄).mp h34
  have h13d : Disjoint (omSupp x₁) (omSupp x₃) :=
    (disjoint_of_comm_both h12'.1 h12'.2
      ((omPlusRefl_comm_iff_supp hp x₁ x₃).mp h13)
      ((omPlusRefl_comm_iff_supp hp x₂ x₃).mp h23)).1
  have h23d : Disjoint (omSupp x₂) (omSupp x₃) :=
    (disjoint_of_comm_both h12'.1 h12'.2
      ((omPlusRefl_comm_iff_supp hp x₁ x₃).mp h13)
      ((omPlusRefl_comm_iff_supp hp x₂ x₃).mp h23)).2
  have h14d : Disjoint (omSupp x₁) (omSupp x₄) :=
    (disjoint_of_comm_both h12'.1 h12'.2
      ((omPlusRefl_comm_iff_supp hp x₁ x₄).mp h14)
      ((omPlusRefl_comm_iff_supp hp x₂ x₄).mp h24)).1
  have h24d : Disjoint (omSupp x₂) (omSupp x₄) :=
    (disjoint_of_comm_both h12'.1 h12'.2
      ((omPlusRefl_comm_iff_supp hp x₁ x₄).mp h14)
      ((omPlusRefl_comm_iff_supp hp x₂ x₄).mp h24)).2
  exact omFar_six_le h12'.1 h12'.2 h34'.1 h34'.2 h13d h14d h23d h24d

theorem omSigned_conj_far (hp : p.Prime) (hr : 6 ≤ r) {x₁ x₂ x₃ x₄ : OmPlusIdx r}
    (h12 : omPlusRefl p x₁ * omPlusRefl p x₂ ≠ omPlusRefl p x₂ * omPlusRefl p x₁)
    (h34 : omPlusRefl p x₃ * omPlusRefl p x₄ ≠ omPlusRefl p x₄ * omPlusRefl p x₃)
    (h13 : omPlusRefl p x₁ * omPlusRefl p x₃ = omPlusRefl p x₃ * omPlusRefl p x₁)
    (h14 : omPlusRefl p x₁ * omPlusRefl p x₄ = omPlusRefl p x₄ * omPlusRefl p x₁)
    (h23 : omPlusRefl p x₂ * omPlusRefl p x₃ = omPlusRefl p x₃ * omPlusRefl p x₂)
    (h24 : omPlusRefl p x₂ * omPlusRefl p x₄ = omPlusRefl p x₄ * omPlusRefl p x₂) :
    ∃ w ∈ omSigned p r,
      omPlusRefl p (omStd r (by omega) ⟨0, by omega⟩) = w * omPlusRefl p x₁ * w⁻¹ ∧
      omPlusRefl p (omStd r (by omega) ⟨1, by omega⟩) = w * omPlusRefl p x₂ * w⁻¹ ∧
      omPlusRefl p (omStd r (by omega) ⟨3, by omega⟩) = w * omPlusRefl p x₃ * w⁻¹ ∧
      omPlusRefl p (omStd r (by omega) ⟨4, by omega⟩) = w * omPlusRefl p x₄ * w⁻¹ := by
  have h12' := (omPlusRefl_not_comm_iff_supp hp x₁ x₂).mp h12
  have h34' := (omPlusRefl_not_comm_iff_supp hp x₃ x₄).mp h34
  have h13d : Disjoint (omSupp x₁) (omSupp x₃) :=
    (disjoint_of_comm_both h12'.1 h12'.2
      ((omPlusRefl_comm_iff_supp hp x₁ x₃).mp h13)
      ((omPlusRefl_comm_iff_supp hp x₂ x₃).mp h23)).1
  have h23d : Disjoint (omSupp x₂) (omSupp x₃) :=
    (disjoint_of_comm_both h12'.1 h12'.2
      ((omPlusRefl_comm_iff_supp hp x₁ x₃).mp h13)
      ((omPlusRefl_comm_iff_supp hp x₂ x₃).mp h23)).2
  have h14d : Disjoint (omSupp x₁) (omSupp x₄) :=
    (disjoint_of_comm_both h12'.1 h12'.2
      ((omPlusRefl_comm_iff_supp hp x₁ x₄).mp h14)
      ((omPlusRefl_comm_iff_supp hp x₂ x₄).mp h24)).1
  have h24d : Disjoint (omSupp x₂) (omSupp x₄) :=
    (disjoint_of_comm_both h12'.1 h12'.2
      ((omPlusRefl_comm_iff_supp hp x₁ x₄).mp h14)
      ((omPlusRefl_comm_iff_supp hp x₂ x₄).mp h24)).2
  obtain ⟨m, h1, h2, h3, h4⟩ :=
    omMove_far hr h12'.1 h12'.2 h34'.1 h34'.2 h13d h14d h23d h24d
  exact ⟨m.w, m.hw, by rw [← h1, m.hf x₁], by rw [← h2, m.hf x₂], by rw [← h3, m.hf x₃],
    by rw [← h4, m.hf x₄]⟩

end CFSG.StandardType.QTwo

end
