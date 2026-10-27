module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F9Tilde

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem relIndex_sup_of_le_normalizer {B TC : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (TC : Set G)) : TC.relIndex (B ⊔ TC) = TC.relIndex B := by
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hB
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hB
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient B TC hB).toEquiv.symm

theorem mIdx_inf_eq_mIdx_sup {B TC : Subgroup G} (hB : B ≤ Subgroup.normalizer (TC : Set G)) :
    mIdx B (B ⊓ TC) = mIdx (B ⊔ TC) TC := by
  unfold mIdx
  rw [Subgroup.inf_relIndex_left, relIndex_sup_of_le_normalizer hB]

structure E7Pair (Z U TC G2 R : Subgroup G) (g : G) : Prop where
  card_Z : Nat.card Z = 2
  ne_A : conjSub g Z ≠ Z
  U_ab : IsElemAbelian 2 U
  U_le : U ≤ G2
  W_le : conjSub g U ≤ G2
  R_le : R ≤ G2
  G2_cent : G2 ≤ Subgroup.centralizer (Z : Set G)
  G2_normU : G2 ≤ Subgroup.normalizer (U : Set G)
  G2_normTC : G2 ≤ Subgroup.normalizer (TC : Set G)
  e5a : ⁅U, TC⁆ ≤ Z
  e5b : centralizerMod Z G2 U = TC
  B_le : conjSub g⁻¹ U ≤ R

end CFSG.Quasithin.H13.NFa2
