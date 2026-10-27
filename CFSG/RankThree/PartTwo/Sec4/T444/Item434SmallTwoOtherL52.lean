module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherLinTwo
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4
namespace Item434SmallTwoOther

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSL)
open Matrix
open scoped MatrixGroups

namespace L52

noncomputable def t₁ : SL(5, GaloisField 2 1) := blk (show (0 : Fin 5) ≠ 1 by decide)

noncomputable def t₂ : SL(5, GaloisField 2 1) := blk (show (2 : Fin 5) ≠ 3 by decide)

noncomputable def P₀ : Subgroup SL(5, GaloisField 2 1) :=
  Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂

theorem isElemAbelian_P₀ : CFSG.Assembly.IsElemAbelian 3 P₀ ∧ Nat.card P₀ = 9 :=
  isElemAbelian_zpowers_sup (blk_pow_three _) (blk_ne_one _) (blk_pow_three _)
    (notMem_zpowers_of_smul (v := Pi.single 2 1) (blk_smul_of_ne _ (by decide) (by decide))
      (blk_smul_fst_ne _))
    (commute_blk_blk _ _ (by decide) (by decide) (by decide) (by decide)).eq

theorem card_SL5 : Nat.card SL(5, GaloisField 2 1) = 9999360 := by
  rw [card_SL_gf2 (by norm_num)]
  decide

theorem factorization_card_SL5 : (Nat.card SL(5, GaloisField 2 1)).factorization 3 = 2 := by
  rw [card_SL5, show (9999360 : ℕ) = 3 ^ 2 * 1111040 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)]

theorem closure_hyperCent_P₀ : Subgroup.closure (hyperCent P₀) = ⊤ := by
  have h9 := isElemAbelian_P₀.2
  have h1 : blk (show (0 : Fin 5) ≠ 1 by decide) ∈ P₀ :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have h2 : blk (show (2 : Fin 5) ≠ 3 by decide) ∈ P₀ :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  apply eq_top_of_hub (4 : Fin 5)
  · intro i hi
    apply Subgroup.subset_closure
    fin_cases i
    · exact transvection_mem_hyperCent h9 _ h2 hi (by decide) (by decide) (by decide) (by decide)
    · exact transvection_mem_hyperCent h9 _ h2 hi (by decide) (by decide) (by decide) (by decide)
    · exact transvection_mem_hyperCent h9 _ h1 hi (by decide) (by decide) (by decide) (by decide)
    · exact transvection_mem_hyperCent h9 _ h1 hi (by decide) (by decide) (by decide) (by decide)
    · exact absurd rfl hi
  · intro i hi
    apply Subgroup.subset_closure
    fin_cases i
    · exact transvection_mem_hyperCent h9 _ h2 hi (by decide) (by decide) (by decide) (by decide)
    · exact transvection_mem_hyperCent h9 _ h2 hi (by decide) (by decide) (by decide) (by decide)
    · exact transvection_mem_hyperCent h9 _ h1 hi (by decide) (by decide) (by decide) (by decide)
    · exact transvection_mem_hyperCent h9 _ h1 hi (by decide) (by decide) (by decide) (by decide)
    · exact absurd rfl hi

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem gen_SL5 (h : Ctx434Core G A M Q) :
    ∀ P : Subgroup SL(5, GaloisField 2 1), CFSG.Assembly.IsElemAbelian 3 P →
      Nat.card P = Nat.card h.layerStar → Subgroup.closure (hyperCent P) = ⊤ := by
  intro P _ hPc
  rcases h.card_layerStar with h9 | ⟨h27, -⟩
  · rw [h9] at hPc
    obtain ⟨g, rfl⟩ := exists_map_conj_of_sylow (P₀ := P₀)
      (by rw [isElemAbelian_P₀.2, factorization_card_SL5]; norm_num)
      (by rw [hPc, isElemAbelian_P₀.2])
    exact closure_hyperCent_map_conj closure_hyperCent_P₀ g
  · rw [h27] at hPc
    have hd := Subgroup.card_subgroup_dvd_card P
    rw [hPc, card_SL5] at hd
    norm_num at hd

theorem false_of_L52
    (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* projSL 5 (GaloisField 2 1)) : False :=
  false_of_gen h (center_layer_eq_bot_of_projSL_gf2 h (by norm_num) e) e
    (not_three_dvd_card_outer_projSL_gf2 (by norm_num)) (center_projSL_gf2 (by norm_num))
    (gen_of_mulEquiv (slEquivProjSL (by norm_num)) (gen_SL5 h))

end Ctx

end L52

end Item434SmallTwoOther

section Families


theorem item434SmallTwoOtherAtL52 : Item434SecFor IsSmallTwoOtherL52 := by
  intro _ _ _ _ _ G _ _ _ _ _ A M Q hc hL
  obtain ⟨e⟩ := hL
  exact (Item434SmallTwoOther.L52.false_of_L52 hc e).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
