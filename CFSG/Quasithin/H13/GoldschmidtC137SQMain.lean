module

public import CFSG.Quasithin.H13.GoldschmidtC137Stmt
public import CFSG.Quasithin.H13.GoldschmidtC137SQL32
public import CFSG.Quasithin.H13.GoldschmidtC137SQRkHat
public import CFSG.Quasithin.H13.GoldschmidtC137SQRkU33
public import CFSG.Quasithin.H13.GoldschmidtC137SQExt
public import CFSG.Quasithin.Background.C124AsmNormal

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.SectionRank CFSG.Quasithin
  CFSG.QuasithinUnique

@[expose] def U33KGroup : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], LieModel Y .PSU 3 3 1 → IsKGroupCat Y

theorem kRank_of_type {Y : Type} [Group Y] [Finite Y] (hU33 : U33KGroup)
    (htype : LieModel Y .PSL 3 2 1 ∨ Nonempty (Y ≃* alternatingGroup (Fin 6)) ∨
      (Group.IsPerfect Y ∧ Nat.card (Subgroup.center Y) = 3 ∧
        Nonempty ((Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin 6))) ∨
      LieModel Y .PSU 3 3 1) : IsKGroupCat Y ∧ RankLeTwo Y := by
  rcases htype with h | h | ⟨hperf, hZ, h'⟩ | h
  · exact ⟨isKGroupCat_of_lieModel_psl_three_two h,
      rankLeTwo_of_card_168_or_360 (Or.inl (simple_card_of_lieModel_psl_three_two h).2)⟩
  · obtain ⟨e⟩ := h
    exact ⟨isKGroupCat_of_mulEquiv_alternatingGroup_six e,
      rankLeTwo_of_card_168_or_360
        (Or.inr ((Nat.card_congr e.toEquiv).trans card_alternatingGroup_six))⟩
  · obtain ⟨e⟩ := h'
    exact ⟨isKGroupCat_of_hatA6 e, rankLeTwo_of_hatA6 hperf hZ e⟩
  · exact ⟨hU33 Y h, rankLeTwo_of_lieModel_psu_three_three h⟩

theorem c137SQTKSupply_of_u33 (hU33 : U33KGroup) : C137SQTKSupply := by
  intro G _ _ X T L hX hT hprod hL hL2 htype
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hN : X ≤ Subgroup.normalizer (L : Set G) := C124.le_normalizer_of_prod hT hprod hL
  have hnorm : (L.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 hN
  have : (Subgroup.inclusion hLX).range.Normal := by
    rw [Subgroup.inclusion_range]
    exact hnorm
  have hq := isPGroup_quotient_of_prod hT hprod hLX
  have hO : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  obtain ⟨hK, hR⟩ := kRank_of_type hU33 htype
  exact ⟨stronglyQuasithin_of_rankLeTwo (rankLeTwo_of_hom (Subgroup.inclusion hLX)
      (Subgroup.inclusion_injective hLX) hq (CFSG.pCore 2 ↥L) hO hR),
    isKGroupCat_of_ext (Subgroup.inclusion hLX) (Subgroup.inclusion_injective hLX) hq
      (CFSG.pCore 2 ↥L) hO hK⟩

end CFSG.Quasithin.H13.U3.GC137.SQ
