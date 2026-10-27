module

public import CFSG.Quasithin.H13.U3Local
public import CFSG.Quasithin.H13.L32NModule
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.RankThree.PartOne.S11c.HNAlternating

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

theorem fiveQuotientExactOrders_holds : U3.FiveQuotientExactOrders := by
  intro Q _ _
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [CFSG.RankThree.PartOne.HNRed.card_alternatingGroup_fin 5 (by norm_num)]
    decide
  have h6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [CFSG.RankThree.PartOne.HNRed.card_alternatingGroup_fin 6 (by norm_num)]
    decide
  have hA5 : Nonempty (Q ≃* alternatingGroup (Fin 5)) → Nat.card Q = 60 := fun ⟨e⟩ => by
    rw [Nat.card_congr e.toEquiv, h5]
  have hL : CFSG.Blueprint.LieModel Q .PSL 3 2 1 → Nat.card Q = 168 := fun hL => by
    obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.SteinbergBR.AutGL32.card_GL32]
  have hA6 : Nonempty (Q ≃* alternatingGroup (Fin 6)) → Nat.card Q = 360 := fun ⟨e⟩ => by
    rw [Nat.card_congr e.toEquiv, h6]
  have h3A6 : Group.IsPerfect Q → Nat.card (center Q) = 3 →
      Nonempty (Q ⧸ center Q ≃* alternatingGroup (Fin 6)) → Nat.card Q = 1080 :=
    fun _ hZ ⟨e⟩ => by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q), Nat.card_congr e.toEquiv,
        h6, hZ]
  have hU : CFSG.Blueprint.LieModel Q .PSU 3 3 1 → Nat.card Q = 6048 :=
    card_of_lieModel_PSU_three_three
  refine ⟨hA5, hL, hA6, h3A6, hU, fun h => ?_⟩
  rcases h with h | h | h | ⟨hp, hZ, h⟩ | h
  · rw [hA5 h]
    norm_num
  · rw [hL h]
    norm_num
  · rw [hA6 h]
    norm_num
  · rw [h3A6 hp hZ h]
    norm_num
  · rw [hU h]

end CFSG.Quasithin.H13.NQBlock
