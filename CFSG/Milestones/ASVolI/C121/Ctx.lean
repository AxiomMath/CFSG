module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Milestones.ASVolI.C1
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits
open scoped MatrixGroups

structure burnsideC121_YCtx {Ω : Type} [Group Ω] (X R T Y W : Subgroup Ω) : Prop where
  charTwo : CharTwo X
  hT : IsPGroup 2 T
  SR : baum T ≤ R
  RT : R ≤ T
  QR : pCoreOf 2 X ≤ R
  RX : R ≤ X
  hY : InYSet X R (baum T) Y
  max : IsR2Max ((baum T ⊔ pCoreOf 2 X) ⊔ Y) W

@[expose] def burnsideC121_R0 {Ω : Type} [Group Ω] (X T : Subgroup Ω) : Subgroup Ω :=
  baum T ⊔ pCoreOf 2 X

@[expose] def burnsideC121_H {Ω : Type} [Group Ω] (X T Y : Subgroup Ω) : Subgroup Ω :=
  burnsideC121_R0 X T ⊔ Y

@[expose] def burnsideC121_P {Ω : Type} [Group Ω] (X R T Y : Subgroup Ω) : Subgroup Ω :=
  burnsideC121_R0 X T ⊔ (R ⊓ Y)

namespace burnsideC121_YCtx

variable {Ω : Type} [Group Ω] [Finite Ω] {X R T Y W : Subgroup Ω}
  (c : burnsideC121_YCtx X R T Y W)

include c

theorem R_pGroup : IsPGroup 2 R := c.hT.to_le c.RT

theorem S_pGroup : IsPGroup 2 (baum T) := c.R_pGroup.to_le c.SR

theorem R0_le_R : burnsideC121_R0 X T ≤ R := sup_le c.SR c.QR

theorem P_le_R : burnsideC121_P X R T Y ≤ R := sup_le c.R0_le_R inf_le_left

theorem P_pGroup : IsPGroup 2 (burnsideC121_P X R T Y) := c.R_pGroup.to_le c.P_le_R

theorem R0_le_normalizer : burnsideC121_R0 X T ≤ Subgroup.normalizer (Y : Set Ω) := c.hY.inv

theorem P_le_normalizer : burnsideC121_P X R T Y ≤ Subgroup.normalizer (Y : Set Ω) :=
  sup_le c.R0_le_normalizer (inf_le_right.trans Subgroup.le_normalizer)

theorem S_le_normalizer : baum T ≤ Subgroup.normalizer (Y : Set Ω) :=
  le_sup_left.trans c.R0_le_normalizer

theorem Q_le_normalizer : pCoreOf 2 X ≤ Subgroup.normalizer (Y : Set Ω) :=
  le_sup_right.trans c.R0_le_normalizer

theorem S_le_P : baum T ≤ burnsideC121_P X R T Y := le_sup_left.trans le_sup_left

theorem Q_le_P : pCoreOf 2 X ≤ burnsideC121_P X R T Y := le_sup_right.trans le_sup_left

theorem RY_le_P : R ⊓ Y ≤ burnsideC121_P X R T Y := le_sup_right

theorem P_inf_Y : burnsideC121_P X R T Y ⊓ Y = R ⊓ Y :=
  le_antisymm (inf_le_inf_right Y c.P_le_R) (le_inf c.RY_le_P inf_le_right)

theorem Y_le_H : Y ≤ burnsideC121_H X T Y := le_sup_right

theorem P_le_H : burnsideC121_P X R T Y ≤ burnsideC121_H X T Y :=
  sup_le le_sup_left (inf_le_right.trans le_sup_right)

theorem H_eq : burnsideC121_H X T Y = Y ⊔ burnsideC121_P X R T Y :=
  le_antisymm (sup_le (le_sup_left.trans le_sup_right) le_sup_left)
    (sup_le c.Y_le_H c.P_le_H)

theorem H_le_X : burnsideC121_H X T Y ≤ X := sup_le (c.R0_le_R.trans c.RX) c.hY.le

theorem H_le_normalizer : burnsideC121_H X T Y ≤ Subgroup.normalizer (Y : Set Ω) :=
  sup_le c.R0_le_normalizer Subgroup.le_normalizer

theorem P_sylow : IsSylowTwoOf (burnsideC121_P X R T Y) (burnsideC121_H X T Y) := by
  rw [c.H_eq]
  refine CFSG.Quasithin.C124.L2.isSylowTwoOf_sup_of_normalizing c.P_le_normalizer c.P_pGroup ?_
  rw [c.P_inf_Y]
  exact c.hY.sylow

theorem baum_R : baum R = baum T := (baum_eq_of_le c.SR c.RT).symm

theorem thompsonJ_R : thompsonJ R = thompsonJ T :=
  (B6.thompsonJ_eq_of_le ((B6.thompsonJ_le_baum T).trans c.SR) c.RT)

theorem thompsonJ_R_le_S : thompsonJ R ≤ baum T := by
  rw [c.thompsonJ_R]
  exact B6.thompsonJ_le_baum T

theorem thompsonJ_P : thompsonJ (burnsideC121_P X R T Y) = thompsonJ R :=
  (B6.thompsonJ_eq_of_le (c.thompsonJ_R_le_S.trans c.S_le_P) c.P_le_R)

theorem baum_P : baum (burnsideC121_P X R T Y) = baum T := by
  rw [← c.baum_R]
  exact (baum_eq_of_le (c.baum_R ▸ c.S_le_P) c.P_le_R).symm

theorem W_red : IsTwoReducedIn (burnsideC121_H X T Y) W := c.max.1

theorem W_le_H : W ≤ burnsideC121_H X T Y := c.W_red.1

theorem H_le_normalizer_W : burnsideC121_H X T Y ≤ Subgroup.normalizer (W : Set Ω) :=
  c.W_red.2.1

theorem W_elem : IsElemAbelian 2 W := c.W_red.2.2.1

theorem Y_le_normalizer_W : Y ≤ Subgroup.normalizer (W : Set Ω) :=
  c.Y_le_H.trans c.H_le_normalizer_W

theorem P_le_normalizer_W : burnsideC121_P X R T Y ≤ Subgroup.normalizer (W : Set Ω) :=
  c.P_le_H.trans c.H_le_normalizer_W

theorem pCore_H_le_centralizer : pCoreOf 2 (burnsideC121_H X T Y) ≤
    Subgroup.centralizer (W : Set Ω) := C124.pCoreOf_le_centralizer c.W_red

theorem W_le_pCore_H : W ≤ pCoreOf 2 (burnsideC121_H X T Y) := C124.le_pCoreOf_of_reduced c.W_red

theorem pCore_Y_le_pCore_H : pCoreOf 2 Y ≤ pCoreOf 2 (burnsideC121_H X T Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans c.Y_le_H)
    (c.H_le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 Y)) (pCoreOf_isPGroup 2 Y)

theorem pCore_Y_le_centralizer : pCoreOf 2 Y ≤ Subgroup.centralizer (W : Set Ω) :=
  c.pCore_Y_le_pCore_H.trans c.pCore_H_le_centralizer

theorem pCore_Y_le_RY : pCoreOf 2 Y ≤ R ⊓ Y := B6.pCoreOf_two_le_of_isSylowTwoOf c.hY.sylow

theorem pCore_Y_le_P : pCoreOf 2 Y ≤ burnsideC121_P X R T Y := c.pCore_Y_le_RY.trans c.RY_le_P

theorem pCore_H_le_P : pCoreOf 2 (burnsideC121_H X T Y) ≤ burnsideC121_P X R T Y :=
  B6.pCoreOf_two_le_of_isSylowTwoOf c.P_sylow

theorem H_prod : ∀ x ∈ burnsideC121_H X T Y, ∃ y ∈ Y, ∃ p ∈ burnsideC121_P X R T Y, x = y * p := by
  intro x hx
  rw [c.H_eq] at hx
  have hx' : x ∈ ((Y ⊔ burnsideC121_P X R T Y : Subgroup Ω) : Set Ω) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y _ c.P_le_normalizer] at hx'
  obtain ⟨y, hy, p, hp, rfl⟩ := hx'
  exact ⟨y, hy, p, hp, rfl⟩

end burnsideC121_YCtx

end CFSG.ASVolI
