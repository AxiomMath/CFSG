module

import CFSG.LocalAnalysis.UniquenessCase.UC22K148Exc
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Sp4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Cert13
public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem two_le_of_isL2 {X : Type} [Group X] {n : ℕ} (h : IsL2 X n) : 2 ≤ n := by
  obtain ⟨-, h1, -, h2, -⟩ := CFSG.Blueprint.LieModel.admissible h
  by_contra hlt
  obtain rfl : n = 1 := by omega
  exact h2 rfl

theorem not_isL2Odd_two {X : Type} [Group X] : ¬ IsL2Odd X 2 := fun h => by
  obtain ⟨-, -, -, h2, -⟩ := CFSG.Blueprint.LieModel.admissible h
  exact h2 rfl

theorem not_isL2Odd_three {X : Type} [Group X] : ¬ IsL2Odd X 3 := fun h => by
  obtain ⟨-, -, -, -, h3⟩ := CFSG.Blueprint.LieModel.admissible h
  exact h3 rfl

theorem nonempty_equiv_GL32_of_isL2Odd_seven {X : Type} [Group X] (h : IsL2Odd X 7) :
    Nonempty (X ≃* GL (Fin 3) (ZMod 2)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 7) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
  obtain ⟨g⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  exact ⟨(e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv (FiniteField.ringEquivOfCardEq hcard)
      (Fin 2)))).trans g.symm⟩

theorem allowed_shape
    [Finite G] [Finite V] (hρ : Function.Injective ρ) {L : Subgroup G} (hL : IsComponentOf L ⊤)
    (hshape : CompShape148 L) (hLH : ⁅L, hP ρ⁆ ≠ ⊥) :
    (∃ n : ℕ, 2 ≤ n ∧ IsL2 ↥L n) ∨ (IsL2Odd ↥L 7 ∧ Nonempty (↥L ≃* GL (Fin 3) (ZMod 2))) := by
  rcases hshape with ⟨n, hSp, g, hg⟩ | ⟨n, hSU | hL2 | hSz⟩ | ⟨p, hp, hX⟩ | hJ
  · exact absurd (sp4Graph_commute_hP hρ hL hSp hg) hLH
  · exact absurd (excl_commute_hP hρ hL (Or.inr (Or.inr (Or.inl ⟨n, hSU⟩)))) hLH
  · exact Or.inl ⟨n, two_le_of_isL2 hL2, hL2⟩
  · exact absurd (excl_commute_hP hρ hL (Or.inr (Or.inl ⟨n, hSz⟩))) hLH
  · by_cases h11 : 11 ≤ p
    · exact absurd (excl_commute_hP hρ hL (Or.inl ⟨p, hp, h11, hX⟩)) hLH
    have hp11 : p < 11 := by omega
    interval_cases p
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hX not_isL2Odd_two
    · exact absurd hX not_isL2Odd_three
    · exact absurd hp (by norm_num)
    · exact Or.inl ⟨2, le_rfl, PartTwo.s13_isL2_two_of_isL2Odd_five hX⟩
    · exact absurd hp (by norm_num)
    · exact Or.inr ⟨hX, nonempty_equiv_GL32_of_isL2Odd_seven hX⟩
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
  · exact absurd (excl_commute_hP hρ hL (Or.inr (Or.inr (Or.inr hJ)))) hLH

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
