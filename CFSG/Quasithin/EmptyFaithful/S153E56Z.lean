module

public import CFSG.Quasithin.EmptyFaithful.S153E56Ex
public import CFSG.Quasithin.EmptyFaithful.S153E56D
public import CFSG.Quasithin.EmptyFaithful.S153E56E10
public import CFSG.Quasithin.EmptyFaithful.S153E56F8
public import CFSG.Quasithin.EmptyFaithful.S153E56P15

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

namespace S153E

section Assembly

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem lemma_15_3_56 (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} (c : Chain15355 cx N₁ N₂ g s) {y t₁ : G}
    (hy : y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁))
    (ht₁ : t₁ ∈ T ∧ t₁ ∉ UCT153 T M V₁ Mc) (iJ : JStruct56 T Mc M V₁ N₁ y) :
    Concl15356 cx N₁ s y t₁ := by
  have hU : CFSG.IsExtraspecial 2 ↥(UH153 T M V₁ Mc) := c.h55.1
  obtain ⟨horthInv, horthPolar, horthNondeg, horthH⟩ := lemma_15_3_56_orth cx hU
  have hrank := lemma_15_3_56_rank h113 cx c
  have hE := geo56_E_sing h113 cx c hy iJ hrank
  have hGeo : Geo56 cx s y t₁ :=
    { U_ext := hU
      Z_center := geo56_Z_center cx c
      rank := hrank
      Z'_le_U := geo56_Z'_le_U h113 cx c hy iJ hrank
      Z_le_U' := geo56_Z_le_U' h113 cx c hy iJ hrank
      Z_inf_Z' := geo56_Z_inf_Z' h113 cx c hy iJ hrank
      E_eq := geo56_E_eq h113 cx c hy iJ hrank
      E_sing := hE
      V0_le_E := geo56_V0_le_E h113 cx c hy iJ hrank
      F_eq := geo56_F_eq cx
      X_eq := geo56_X_eq h113 cx c hy iJ hrank
      X_le_Mc := geo56_X_le_Mc h113 cx c hy iJ hrank
      X_inf_Q := geo56_X_inf_Q h113 cx c hy iJ hrank
      V_norm_E := geo56_V_norm_E h113 cx c hy iJ hrank
      V_comm_E := geo56_V_comm_E h113 cx c hy iJ hrank
      EN := geo56_EN iJ
      X_perp := geo56_X_perp h113 cx c hy iJ
      EEt := geo56_EEt h113 cx c hy ht₁ iJ }
  have hgeom := concl56_geom_fix cx c.toChain15354.toChain15353 hy.1 ht₁ hGeo
  refine
    { orth_inv := horthInv
      orth_polar := horthPolar
      orth_nondeg := horthNondeg
      orth_inv_H := horthH
      rank := hrank
      X_inf_Q := hGeo.X_inf_Q
      comm_XF := concl56_comm_XF h113 cx c hy iJ hrank
      V0_eq := iJ.V0_eq
      E_sing := hE
      X_norm_E := concl56_X_norm_E h113 cx c hy iJ hrank
      X_rank := concl56_X_rank h113 cx c hy iJ hrank
      X_transv := ?_
      dsum := hgeom.dsum
      X_norm_Et := hgeom.X_norm_Et
      X_axis := ?_
      inter := hgeom.inter
      card_Vstar := hgeom.card_Vstar
      D8s := hgeom.D8s
      fixed := hgeom.fixed }
  · rw [iJ.V0_eq]
    exact hgeom.X_transv
  · rw [iJ.V0_eq]
    exact hgeom.X_axis

theorem exists_y_t₁ (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} (c : Chain15355 cx N₁ N₂ g s) :
    ∃ y t₁ : G, (y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁)) ∧
      (t₁ ∈ T ∧ t₁ ∉ UCT153 T M V₁ Mc) := by
  obtain ⟨y, hy⟩ := exists_y h113 cx c.h53one
  obtain ⟨t₁, ht₁T, ht₁⟩ := exists_t₁ cx c.h51 c.h52
  exact ⟨y, t₁, hy, ht₁T, ht₁⟩

end Assembly

end S153E

end CFSG.Quasithin
