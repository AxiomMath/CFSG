module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Dihedral.GorensteinWalter

public section

universe u v w

namespace CFSG.Open.Milestones

open Assembly in
theorem _root_.CFSG.Milestones.lr_dihedral_simple_recognition (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) (n : ℕ) (hn : 2 ≤ n)
    (hS : Nonempty ((S : Subgroup G) ≃* DihedralGroup (2 ^ (n - 1)))) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LowTwoRank.StatedClassicalModel G .PSL 2 p f) ∨
      Nonempty (G ≃* alternatingGroup (Fin 7)) := by
  clear hn
  rcases GorensteinWalter.gorenstein_walter G hnonab S ⟨_, hS⟩ with h7 | ⟨p, k, hp, hodd, h5, ⟨e⟩⟩
  · exact Or.inr h7
  · have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h5
      · exact hk
    refine Or.inl ⟨p, k, hp.out, ?_, hk,
      LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv G p k h5 e⟩
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) even_two

end CFSG.Open.Milestones
