module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers
public import CFSG.RankThree.Asc83Table.M22

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint

namespace Res423Two

theorem census423_of_j1 {X : Type} [Group X] [Finite X]
    (e : X ≃* NativeSporadic.Carrier .J1) : Census423 X := by
  refine Res423Census.census423_of_not_nine_dvd ?_
  have h : Nat.card X = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  rw [h]
  norm_num

theorem census423_of_m11
    {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (e : X ≃* NativeSporadic.Carrier .M11) : Census423 X := by
  refine census423_of_alphaVanishes fun D hD hD9 => ?_
  refine alphaVanishes_of_noSignalizer_mulEquiv hZ e (comm_of_isElemAbelian hD.prop)
    (ne_bot_of_card_nine hD9) fun Q hQ hN => ?_
  have hD' : CFSG.Assembly.IsElemAbelian 3 ((D.map e.toMonoidHom).map
      (MulAut.conj : NativeSporadic.Carrier .M11 →* MulAut (NativeSporadic.Carrier .M11))) :=
    isElemAbelian_map' _ (isElemAbelian_map' _ hD.prop)
  have hinj : Function.Injective (MulAut.conj : NativeSporadic.Carrier .M11 →*
      MulAut (NativeSporadic.Carrier .M11)) := by
    have : IsSimpleGroup NativeSporadic.M11 := CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
    exact Item434Kit.conj_injective_of_center_eq_bot (Item434Spor.center_eq_bot_of_simple
      (Y := NativeSporadic.M11) (by rw [CFSG.Sporadic.Mathieu.card_M11]; norm_num))
  have hD'9 : Nat.card ((D.map e.toMonoidHom).map (MulAut.conj : NativeSporadic.Carrier .M11 →*
      MulAut (NativeSporadic.Carrier .M11))) = 9 := by
    rw [Subgroup.card_map_of_injective hinj, Subgroup.card_map_of_injective e.injective, hD9]
  exact Item434SporM11.eq_bot_of_le_normalizer_mulAut hD' hD'9 hQ hN

theorem census423_of_m22
    {X : Type} [Group X] [Finite X]
    (e : X ≃* NativeSporadic.Carrier .M22) : Census423 X := by
  intro D _ hD9 _ _ _
  refine Or.inr (Or.inl ⟨⟨e⟩, ?_⟩)
  obtain ⟨-, -, h⟩ := CFSG.RankThree.Asc83Table.e9_transport CFSG.RankThree.Asc83Table.M22.E
    CFSG.RankThree.Asc83Table.M22.factorization_card (e : X ≃* NativeSporadic.M22)
  obtain ⟨f⟩ := h D hD9
  obtain ⟨q⟩ := CFSG.RankThree.Asc83Table.M22.automizer_P0
  exact ⟨(Sporadic.automizerEquivAutIn D).symm.trans (f.trans q)⟩

end Res423Two

end CFSG.RankThree.PartTwo.Sec4
