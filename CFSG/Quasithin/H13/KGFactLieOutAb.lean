module

public import CFSG.Quasithin.H13.KGFactLieOutAbL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankLin3
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.H13.A5S136abP

public section

namespace CFSG.Quasithin.H13.KGLieOut

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Quasithin.H13.KGInsp4316 (outer_comm_psl2 comm_of_isCyclic outer_cyclic_psp4
  outer_comm_g2 outer_comm_d4 outer_cyclic_2f4 outer_cyclic_sz)

theorem two_le_pRank_three {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : (Even f ∧ StatedClassicalModel X .PSL 3 2 f) ∨
      (Odd f ∧ StatedClassicalModel X .PSU 3 2 f)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h with ⟨hf, -, K, _, _, hK, ⟨e⟩⟩ | ⟨hf, ⟨-, hf1, -⟩, K, _, _, hK, ⟨e⟩⟩
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    refine CFSG.QuasithinUnique.Lin2.OddRank.two_le_pRank_psl3 (F := K) (p := 3) ?_
    have := two_pow_mod_three_of_even hf
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rw [hK]
    exact Nat.dvd_of_mod_eq_zero (by omega)
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    have := two_pow_mod_three_of_odd hf
    obtain ⟨A, hA, hc⟩ := hasElemAb_nine_psu3 Nat.one_le_two_pow hK
      (Nat.dvd_of_mod_eq_zero (by omega))
    exact CFSG.SectionRank.le_pRank (by norm_num) le_top hA (k := 2) (by rw [hc]; norm_num)

theorem factLieOutAbelian_holds :
    CFSG.Quasithin.H13.A5.FactLieOutAbelian := by
  intro X _ _ hX h3
  apply inner_of_outer_comm
  rcases hX with ⟨⟨f, ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ |
      ⟨-, -, hm⟩ | ⟨-, -, hm⟩⟩ | hm⟩ | ⟨n, hn, hm⟩
  ·
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have : Group.IsPerfect X := isPerfect_of_psl hm (Or.inr ⟨rfl, h4⟩)
    have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 f hm).2
    have : Nontrivial X := hs.toNontrivial
    exact outer_comm_psl2 hs exists_noncomm hm
  ·
    rcases Nat.even_or_odd f with he | ho
    · exact absurd (two_le_pRank_three (Or.inl ⟨he, hm⟩)) (by omega)
    · have : Group.IsPerfect X := isPerfect_of_psl hm (Or.inl le_rfl)
      have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 f hm).2
      refine outer_comm_psl hs hm (gcd_three_eq_one ?_)
      have := two_pow_mod_three_of_odd ho
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      omega
  ·
    rcases Nat.even_or_odd f with he | ho
    · have : Group.IsPerfect X := isPerfect_of_psu hm
      have hs := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 2 f hm).2
      refine outer_comm_psu hs hm (gcd_three_eq_one ?_)
      have := two_pow_mod_three_of_even he
      omega
    · exact absurd (two_le_pRank_three (Or.inr ⟨ho, hm⟩)) (by omega)
  · exact comm_of_isCyclic (outer_cyclic_psp4 hm)
  · exact outer_comm_g2 hf hm
  · exact outer_comm_d4 hf hm
  · exact comm_of_isCyclic (outer_cyclic_2f4 hm)
  · exact comm_of_isCyclic (outer_cyclic_sz hm)
  ·
    obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 1 hm
    have h2 : Nat.card (Outer X) = 2 := by
      rw [Nat.card_congr (equivalence e).toEquiv]
      exact CFSG.Sporadic.Schreier.Tits.card_outer_titsD
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact comm_of_isCyclic (isCyclic_of_prime_card h2)
  ·
    have : Group.IsPerfect X := isPerfect_of_psl hm (Or.inl (by omega))
    have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity X n 2 1 hm).2
    exact outer_comm_psl hs hm (by simp)

end CFSG.Quasithin.H13.KGLieOut
