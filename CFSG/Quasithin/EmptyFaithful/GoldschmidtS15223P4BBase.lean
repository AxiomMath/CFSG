module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Facts
public import CFSG.Quasithin.EmptyFaithful.A38cAutOn

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223P4

namespace B

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

abbrev MX (M I X : Subgroup G) : Subgroup G := (M ⊓ I) ⊓ X

theorem X_le_normalizer_V (c : P4Ctx T Mc M H B₀ I X) :
    X ≤ Subgroup.normalizer (P4V M I X : Set G) :=
  le_sup_left.trans c.c27.1.2.2.2.1

theorem pCoreOf_X_le_centralizer_V (c : P4Ctx T Mc M H B₀ I X) :
    pCoreOf 2 X ≤ Subgroup.centralizer (P4V M I X : Set G) := fun _ hx =>
  (c.c27.1.1 (pCoreOf_le_pCoreOf_sup_of_normalizer c.R_norm hx)).2

theorem pCoreOf_le_A (f : P4Fact T Mc M H B₀ I X) : pCoreOf 2 X ≤ sOf152 T Mc M B₀ ⊓ X :=
  f.sylow.pCoreOf_le

theorem A_le_MX (c : P4Ctx T Mc M H B₀ I X) : sOf152 T Mc M B₀ ⊓ X ≤ MX M I X :=
  le_inf (inf_le_left.trans c.S_le_N) inf_le_right

theorem pCoreOf_le_MX (c : P4Ctx T Mc M H B₀ I X) (f : P4Fact T Mc M H B₀ I X) :
    pCoreOf 2 X ≤ MX M I X := (pCoreOf_le_A f).trans (A_le_MX c)

theorem not_K_le_MX (c : P4Ctx T Mc M H B₀ I X) : ¬ oTwoUpper H ≤ MX M I X := fun h =>
  c.K_not_le_M (h.trans (inf_le_left.trans inf_le_left))

theorem Y_le_H (c : P4Ctx T Mc M H B₀ I X) :
    oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X) ≤ H :=
  sup_le (oTwoUpper_le H) (c.A_le_T.trans c.sylowH.1)

theorem Y_le_X (f : P4Fact T Mc M H B₀ I X) :
    oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X) ≤ X := f.Y_le.trans inf_le_left

theorem not_isSolvable_X (c : P4Ctx T Mc M H B₀ I X) : ¬ Group.IsSolvable ↥X := by
  intro hs
  have hN : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  have : Group.IsSolvable (↥X ⧸ CFSG.pCore 2 ↥X) := inferInstance
  have := CFSG.LocalCores.isQuasisimple_nontrivial c.quasi
  have := c.quasi.1
  exact Group.IsPerfect.not_isSolvable (↥X ⧸ CFSG.pCore 2 ↥X) inferInstance

theorem Y_ne_X (c : P4Ctx T Mc M H B₀ I X) (f : P4Fact T Mc M H B₀ I X) :
    oTwoUpper H ⊔ (sOf152 T Mc M B₀ ⊓ X) ≠ X := fun h => not_isSolvable_X c (h ▸ f.solv_Y)

theorem isBlock2_of_short (c : P4Ctx T Mc M H B₀ I X) (hs : IsShort2 X) : IsBlock2 I X :=
  ⟨hs, c.X_le_I, (isSubnormal_iff_subgroupOf c.X_le_I).mp (subnormal_of_mem_cComp c.comp)⟩

end B

end S15223P4

end CFSG.Quasithin
