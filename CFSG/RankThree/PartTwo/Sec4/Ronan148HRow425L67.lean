module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1L67
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Tor

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Open (StatedClassicalModel StatedProj StatedSL)
open scoped MatrixGroups

theorem exists_e27_of_rankThree {X : Type} [Group X] (h : Ronan148R.RankThreeData X) :
    ∃ E : Subgroup X, Late.IsE27 E := by
  obtain ⟨F, F', -, -, -, hF', hF'27, -⟩ := h.exists_pair
  exact ⟨F', hF', hF'27⟩

theorem rowOf425_of_e27Move_model {X Y : Type} [Group X] [Group Y] (eXY : X ≃* Y)
    (h3 : NoThreeCover X) (hR : Ronan148R.RankThreeData Y) (hmove : Ronan148L.E27Move Y) :
    RowOf425 X := fun S _ _ _ _ ⟨e⟩ => by
  let φ : S ≃* Y := e.trans eXY
  obtain ⟨E, hE⟩ := exists_e27_of_rankThree hR
  exact Ronan148L.row425_of_e27Move (NoThreeCover.of_mulEquiv e h3)
    (cubeInner_of_mulEquiv φ hR.cubeInner)
    ⟨E.map φ.symm.toMonoidHom, isElemAbelian_map _ hE.1, by
      rw [Subgroup.card_map_of_injective φ.symm.injective, hE.2]⟩
    (Ronan148L.E27Move.of_mulEquiv φ hmove)

section Hopf


theorem statedClassicalModel_projSL_two {n : ℕ} (hn : 3 ≤ n) :
    StatedClassicalModel (projSL n (GaloisField 2 1)) .PSL n 2 1 := by
  have e₀ : projSL n (GaloisField 2 1) ≃* StatedProj (StatedSL n (GaloisField 2 1)) :=
    ((Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr
        (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL n (GaloisField 2 1)))).symm
  have h22 : (n, 2 ^ 1) ≠ (2, 2) := fun hc => by
    rw [Prod.mk.injEq] at hc
    omega
  have h23 : (n, 2 ^ 1) ≠ (2, 3) := fun hc => by
    rw [Prod.mk.injEq] at hc
    omega
  exact ⟨⟨Nat.prime_two, le_rfl, by omega, h22, h23⟩,
    GaloisField 2 1, inferInstance, inferInstance, GaloisField.card 2 1 (by norm_num), ⟨e₀⟩⟩

theorem noThreeCover_projSL_six_two : NoThreeCover (projSL 6 (GaloisField 2 1)) :=
  Ronan148L.noThreeCover_of_table (by simp [CFSG.Blueprint.Multiplier.genericOrders]) rfl
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row
      (statedClassicalModel_projSL_two (by norm_num))).2

theorem noThreeCover_projSL_seven_two : NoThreeCover (projSL 7 (GaloisField 2 1)) :=
  Ronan148L.noThreeCover_of_table (by simp [CFSG.Blueprint.Multiplier.genericOrders]) rfl
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row
      (statedClassicalModel_projSL_two (by norm_num))).2

theorem k425_eight_SL6 : RowOf425 (projSL 6 (GaloisField 2 1)) :=
  rowOf425_of_e27Move_model (RonanK429F.projSLEquivSLZMod (n := 6) (by norm_num))
    noThreeCover_projSL_six_two Ronan148R.rankThree_sl6 Ronan148R.e27Move_sl6

theorem k425_eight_SL7 : RowOf425 (projSL 7 (GaloisField 2 1)) :=
  rowOf425_of_e27Move_model (RonanK429F.projSLEquivSLZMod (n := 7) (by norm_num))
    noThreeCover_projSL_seven_two Ronan148R.rankThree_sl7 Ronan148R.e27Move_sl7

end Hopf

end CFSG.RankThree.PartTwo.Sec4.Ronan148H
