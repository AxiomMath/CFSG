module

public import CFSG.LocalAnalysis.StandardType.GGKacTable

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType

theorem lq_fam_cases (D : K0Diag) (c : List ℕ) :
    (k0CompType D c).1 = .A ∨ (k0CompType D c).1 = .C ∨ (k0CompType D c).1 = .D ∨
      (k0CompType D c).1 = .E6 ∨ (k0CompType D c).1 = .E7 ∨ (k0CompType D c).1 = .E8 ∨
      (k0CompType D c).1 = .F4 ∨ (k0CompType D c).1 = .G2 := by
  unfold k0CompType
  dsimp only
  split
  · split
    · simp
    · split_ifs <;> simp
  · split_ifs <;> simp

theorem lq_fam_table (T : GGKacType) :
    ∀ zero ∈ (List.range (k0DiagOf T).marks.length).sublists,
      zero.length < (k0DiagOf T).marks.length →
      ∀ c ∈ k0Comps (k0DiagOf T) zero,
        ((k0CompType (k0DiagOf T) c).1 = .E6 → c.length = 6 ∧ T ≠ .F4) ∧
        ((k0CompType (k0DiagOf T) c).1 = .E7 → c.length = 7 ∧ T ≠ .F4) ∧
        ((k0CompType (k0DiagOf T) c).1 = .E8 → c.length = 8 ∧ T = .E8) ∧
        ((k0CompType (k0DiagOf T) c).1 = .F4 → c.length = 4 ∧ T = .F4) ∧
        ((k0CompType (k0DiagOf T) c).1 = .C → T = .F4) ∧
        ((k0CompType (k0DiagOf T) c).1 = .D → T ≠ .F4) ∧
        (k0CompType (k0DiagOf T) c).1 ≠ .G2 := by
  cases T <;> decide +kernel

theorem lq_fam_rank_table (T : GGKacType) :
    ∀ zero ∈ (List.range (k0DiagOf T).marks.length).sublists,
      zero.length < (k0DiagOf T).marks.length →
      ∀ c ∈ k0Comps (k0DiagOf T) zero,
        ((k0CompType (k0DiagOf T) c).1 = .C →
          2 ≤ c.length ∧ c.length ≤ 4 ∧ (c.length = 4 → c = [0, 1, 2, 3])) ∧
        ((k0CompType (k0DiagOf T) c).1 = .D → 4 ≤ c.length) := by
  cases T <;> decide +kernel

end CFSG.StandardType.GGK0LQ

end
