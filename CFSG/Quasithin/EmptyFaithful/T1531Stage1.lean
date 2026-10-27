module

public import CFSG.Quasithin.EmptyFaithful.T1531Basic
public import CFSG.Quasithin.EmptyFaithful.T1531Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stage15344 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → IsUniqueM (Yp ⊔ Sgp153 T V₁) M

structure Res15345 {G : Type} [Group G] (T Mc M V₁ V₂ : Subgroup G) : Prop where
  unique₁ : IsUniqueM ((Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ⊔ Sgp153 T V₁) M
  unique₂ : IsUniqueM ((Y153 Mc M ⊓ Subgroup.centralizer (V₂ : Set G)) ⊔ Sgp153 T V₁) M
  normalizer₁ : Subgroup.normalizer (V₁ : Set G) ≤ M
  normalizer₂ : Subgroup.normalizer (V₂ : Set G) ≤ M
  centralizer₁ : Subgroup.centralizer
    ((V₁ ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) : Subgroup G) : Set G) ≤ M
  centralizer₂ : Subgroup.centralizer
    ((V₂ ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) : Subgroup G) : Set G) ≤ M

section Proof

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem unique_centralizer_Y153 (h44 : Stage15344) (c : Ctx153 G T Mc M V₁ V₂ t) :
    IsUniqueM ((Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ⊔ Sgp153 T V₁) M := by
  have hU : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M :=
    h44 G T Mc M V₁ V₂ (Y153 Mc M) t ⟨c.hyp, c.decomp, Or.inl rfl⟩
  have h2 := h44 G T Mc M V₁ V₂ (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) t
    ⟨c.hyp, c.decomp, Or.inr ⟨hU, rfl⟩⟩
  refine isUniqueM_mono h2 (sup_le_sup_right (oTwoUpper_le _) _) ?_
  exact sup_le (inf_le_left.trans (Y153_le Mc M)) (inf_le_left.trans c.hyp.T_le)

theorem centralizer_le_of_isUniqueM (c : Ctx153 G T Mc M V₁ V₂ t) {W : Subgroup G}
    (hWV : W ≤ VZ T M) (hW : W ≠ ⊥) (hS : Sgp153 T V₁ ≤ Subgroup.normalizer (W : Set G))
    (hU : IsUniqueM ((Y153 Mc M ⊓ Subgroup.centralizer (W : Set G)) ⊔ Sgp153 T V₁) M) :
    Subgroup.centralizer ((W ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) : Subgroup G) : Set G) ≤
      M := by
  set A : Subgroup G := W ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) with hA
  have hAV : A ≤ VZ T M := inf_le_left.trans hWV
  have hApg : IsPGroup 2 A := (B2F.isPGroup_of_isElemAbelian c.hyp.elemAbelian).to_le hAV
  have hA1 : A ≠ ⊥ := by
    obtain ⟨z, hzW, hz1, hz⟩ := c.hyp.exists_ne_one_mem_centralizer_Sgp153 hWV hW hS
    intro hbot
    have hzA : z ∈ A := ⟨hzW, Subgroup.mem_centralizer_iff.mpr fun y hy => hz y hy⟩
    rw [hbot, Subgroup.mem_bot] at hzA
    exact hz1 hzA
  have hAc : A ≤ Subgroup.centralizer (A : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => by
      exact B2F.isElemAbelian_comm c.hyp.elemAbelian (hAV hb) (hAV ha)
  have hCO : A ≤ pCoreOf 2 (Subgroup.centralizer (A : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 hAc (Subgroup.centralizer_le_normalizer _) hApg
  refine le_of_isUniqueM hU ⟨?_, fun hbot => hA1 (le_bot_iff.mp (hbot ▸ hCO))⟩
  refine sup_le ?_ ?_
  · exact fun x hx => Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Subgroup.mem_centralizer_iff.mp hx.2 a ha.1
  · exact fun x hx => Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (Subgroup.mem_centralizer_iff.mp ha.2 x hx).symm

theorem lemma_15_3_45 (h44 : Stage15344) (h113 : StageLemma14113)
    (c : Ctx153 G T Mc M V₁ V₂ t) : Res15345 T Mc M V₁ V₂ := by
  have hU : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M :=
    h44 G T Mc M V₁ V₂ (Y153 Mc M) t ⟨c.hyp, c.decomp, Or.inl rfl⟩
  have cs : Ctx153 G T Mc M V₂ V₁ t := ⟨c.hyp, c.decomp.swapPlanes⟩
  have hS₂ : Sgp153 T V₂ = Sgp153 T V₁ := c.hyp.Sgp153_eq_inf_normalizer_V₂ c.decomp
  have u₁ := unique_centralizer_Y153 h44 c
  have u₂ : IsUniqueM ((Y153 Mc M ⊓ Subgroup.centralizer (V₂ : Set G)) ⊔ Sgp153 T V₁) M := by
    have := unique_centralizer_Y153 h44 cs
    rwa [hS₂] at this
  have hn := c.hyp.normalizer_V_le h113 c.decomp hU
  have hN₁ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₁ : Set G) := inf_le_right
  have hN₂ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₂ : Set G) :=
    c.hyp.Sgp153_le_normalizer_V₂ c.decomp
  have hV₁ : V₁ ≠ ⊥ := by
    intro hb
    have := c.decomp.card₁
    rw [hb, Subgroup.card_bot] at this
    omega
  have hV₂ : V₂ ≠ ⊥ := by
    intro hb
    have := c.decomp.card₂
    rw [hb, Subgroup.card_bot] at this
    omega
  exact ⟨u₁, u₂, hn.1, hn.2, centralizer_le_of_isUniqueM c c.decomp.le₁ hV₁ hN₁ u₁,
    centralizer_le_of_isUniqueM c c.decomp.le₂ hV₂ hN₂ u₂⟩

end Proof

end CFSG.Quasithin
