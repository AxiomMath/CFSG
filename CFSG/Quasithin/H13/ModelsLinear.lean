module

public import CFSG.Blueprint.Catalog
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.Quasithin.H13

open Matrix CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports
open scoped MatrixGroups

theorem lieModel_psl_zmod {n p : ℕ} [Fact p.Prime] (hadm : StatedLieAdmissible .PSL n p 1) :
    CFSG.Blueprint.LieModel PSL(n, ZMod p) .PSL n p 1 :=
  Or.inl ⟨by decide, hadm, ZMod p, inferInstance, inferInstance,
    by rw [Nat.card_zmod, pow_one], ⟨projectiveSpecialLinearGroupEquivStatedProj n (ZMod p)⟩⟩

theorem lieModel_of_mulEquiv_psl_zmod {X : Type} [Group X] {n p : ℕ} [Fact p.Prime]
    (hadm : StatedLieAdmissible .PSL n p 1) (e : X ≃* PSL(n, ZMod p)) :
    CFSG.Blueprint.LieModel X .PSL n p 1 :=
  Or.inl ⟨by decide, hadm, ZMod p, inferInstance, inferInstance,
    by rw [Nat.card_zmod, pow_one],
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj n (ZMod p))⟩⟩

theorem lieModel_psl_four_three : CFSG.Blueprint.LieModel PSL(4, ZMod 3) .PSL 4 3 1 :=
  lieModel_psl_zmod ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩

theorem card_sl_four_three : Nat.card SL(4, ZMod 3) = 12130560 := by
  rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_four]
  norm_num

theorem card_center_sl_four_three : Nat.card (Subgroup.center SL(4, ZMod 3)) = 2 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 4)
    (R := ZMod 3)).toEquiv]
  have h : ∀ c : (ZMod 3)ˣ, c ^ 4 = 1 := by decide
  have htop : rootsOfUnity (max (Fintype.card (Fin 4)) 1) (ZMod 3) = ⊤ := by
    ext c
    simp only [Fintype.card_fin, mem_rootsOfUnity, Subgroup.mem_top, iff_true]
    exact h c
  rw [htop, Subgroup.card_top, Nat.card_units, Nat.card_zmod]

theorem card_psl_four_three : Nat.card PSL(4, ZMod 3) = 6065280 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(4, ZMod 3))
  rw [card_sl_four_three, card_center_sl_four_three] at h
  change Nat.card (SL(4, ZMod 3) ⧸ Subgroup.center SL(4, ZMod 3)) = 6065280
  omega

end CFSG.Quasithin.H13
