module

public import CFSG.Monster.B.TwoA.Amalgam.DeckIso
public import CFSG.Monster.B.TwoA.Amalgam.Chamber
public import CFSG.LieType.Chevalley.WeylRoots

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Geometry
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem native_order_of_pi2_eq_bot
    {X : ChamberSystem (Fin Tag.F4.rank) Chamber}
    (hconn : X.Connected) (hK : X.pi2 (chamberOf 1) = ⊥)
    {δ : X.Cover (chamberOf 1) → X.Cover (chamberOf 1) → WeylGroup .F4}
    (hδ : IsWeylDistanceBuilding (coxeterSystem .F4) δ)
    (hadj : ∀ (i : Fin Tag.F4.rank) (A B : X.Cover (chamberOf 1)),
      (X.universalCover (chamberOf 1)).adj i A B ↔
        δ A B = 1 ∨ δ A B = (coxeterSystem .F4).simple i)
    (hcard : Nat.card (X.Cover (chamberOf 1)) = 371231385525)
    (hEK : Nat.card Eam * Nat.card (X.pi2 (chamberOf 1)) = 306129918735099415756800)
    (hPK : ((Pc 0).subgroupOf Eam).index * Nat.card (X.pi2 (chamberOf 1)) = 3968055)
    {c : Eam} [(Subgroup.zpowers c).Normal] (hc : Nat.card (Subgroup.zpowers c) = 2)
    {H : Type*} [Group H] (hH : Nonempty (Eam ⧸ Subgroup.zpowers c ≃* H)) :
    Function.Bijective (X.coverProj (chamberOf 1)) ∧
      (∀ (i : Fin Tag.F4.rank) (A B : X.Cover (chamberOf 1)),
        (X.universalCover (chamberOf 1)).adj i A B ↔
          X.adj i (X.coverProj (chamberOf 1) A) (X.coverProj (chamberOf 1) B)) ∧
      (∃ δX : Chamber → Chamber → WeylGroup .F4,
        IsWeylDistanceBuilding (coxeterSystem .F4) δX ∧
          ∀ (i : Fin Tag.F4.rank) (x y : Chamber),
            X.adj i x y ↔ δX x y = 1 ∨ δX x y = (coxeterSystem .F4).simple i) ∧
      Nat.card Chamber = 371231385525 ∧
      Nat.card Eam = 306129918735099415756800 ∧ ((Pc 0).subgroupOf Eam).index = 3968055 ∧
      Nat.card H = 153064959367549707878400 := by
  have hK1 : Nat.card (X.pi2 (chamberOf 1)) = 1 := by
    rw [hK, Subgroup.card_bot]
  rw [hK1, mul_one] at hEK hPK
  obtain ⟨e⟩ := hH
  have hEH : Nat.card Eam = Nat.card H * 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers c),
      Nat.card_congr e.toEquiv, hc]
  refine ⟨coverProj_bijective_of_pi2_eq_bot hconn hK, adj_iff_of_pi2_eq_bot hK,
    exists_building_of_pi2_eq_bot hconn hK hδ hadj,
    (natCard_eq_of_pi2_eq_bot hconn hK).trans hcard, hEK, hPK, ?_⟩
  omega

end CFSG.Monster.B.TwoA.Amalgam
