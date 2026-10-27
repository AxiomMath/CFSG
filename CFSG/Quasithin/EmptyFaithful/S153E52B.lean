module

public import CFSG.Quasithin.EmptyFaithful.S153E52A
public import CFSG.Quasithin.EmptyFaithful.S153E51A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Transv

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

noncomputable abbrev tildeZS (T M V₁ Mc : Subgroup G) :
    Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
  (tildeOf (quasithinOmegaOneCenter T) (ZS153 T M V₁)).subgroupOf
    (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))

theorem Vstar_comm_mem (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hZS : ZS153 T M V₁ = VZ T M ⊓ UH153 T M V₁ Mc)
    {a : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))}
    (ha : a ∈ autOn (tildeOf (quasithinOmegaOneCenter T) (VZ T M))
      (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))
    (w : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    a w * w⁻¹ ∈ tildeZS T M V₁ Mc := by
  obtain ⟨s, hsV, rfl⟩ := mem_autOn_iff.1 ha
  obtain ⟨x, hxV, hx⟩ := mem_secImg.1 hsV
  obtain ⟨u, huU, hu⟩ := mem_secImg.1 w.2
  rw [Subgroup.mem_subgroupOf]
  have hxu : (x : G) * u * (x : G)⁻¹ * (u : G)⁻¹ ∈ ZS153 T M V₁ := by
    rw [hZS]
    have h1 := four_U cx (Subgroup.commutator_mem_commutator hxV huU)
    simpa [commutatorElement_def] using h1
  have key : (conjAct (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) s w * w⁻¹).val =
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) (quasithinOmegaOneCenter T)
        (x * u * x⁻¹ * u⁻¹) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, conjAct_apply_coe']
    simp only [map_mul, map_inv, hx, hu]
  rw [key]
  exact secMk_mem_secImg (x := x * u * x⁻¹ * u⁻¹) hxu

theorem card_tildeZS (cx : Ctx15350 T Mc M V₁ V₂ t) : Nat.card ↥(tildeZS T M V₁ Mc) = 2 := by
  have hZSU : ZS153 T M V₁ ≤ UH153 T M V₁ Mc := ZS_le_U cx
  have hZSN : ZS153 T M V₁ ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    hZSU.trans ((U_le_T cx).trans ((T_le_Mc cx).trans (Mc_le_normalizer_Z cx)))
  have h1 : Nat.card ↥(tildeZS T M V₁ Mc) = Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (ZS153 T M V₁)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (secImg_mono hZSU)).toEquiv
  have h2 := relIndex_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (B := quasithinOmegaOneCenter T) (T := quasithinOmegaOneCenter T) (H := ZS153 T M V₁) le_rfl
    (Z_le_ZS cx) hZSN
  have h3 : secImg (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_secImg.1 hy
    rw [Subgroup.mem_bot]
    exact secMk_eq_one_iff.2 hx
  rw [h3, Subgroup.relIndex_bot_left] at h2
  have h4 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (ZS153 T M V₁)
  rw [inf_eq_left.2 (Z_le_ZS cx), Decomp153.card_ZS cx.c.hyp cx.c.decomp] at h4
  have hZ2 : Nat.card ↥(quasithinOmegaOneCenter T) = 2 := cx.c.hyp.lemma_15_3_2_two.2
  rw [hZ2] at h4
  have h5 : Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (ZS153 T M V₁)) =
      (quasithinOmegaOneCenter T).relIndex (ZS153 T M V₁) := h2
  rw [h1, h5]
  omega

theorem span_tildeZS (cx : Ctx15350 T Mc M V₁ V₂ t) :
    (⨆ (g : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))
      (_ : g ∈ HStar153 T M V₁ Mc), (tildeZS T M V₁ Mc).map g.toMonoidHom) = ⊤ := by
  set S := ⨆ (g : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))
      (_ : g ∈ HStar153 T M V₁ Mc), (tildeZS T M V₁ Mc).map g.toMonoidHom with hS
  have hZSN : ZS153 T M V₁ ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (ZS_le_U cx).trans ((U_le_T cx).trans ((T_le_Mc cx).trans (Mc_le_normalizer_Z cx)))
  rw [eq_top_iff]
  intro w _
  obtain ⟨u, huU, hu⟩ := mem_secImg.1 w.2
  have key : ∀ x : G, x ∈ UH153 T M V₁ Mc →
      ∃ (hN : x ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (hU : x ∈ UH153 T M V₁ Mc),
        (⟨secMk _ _ ⟨x, hN⟩, secMk_mem_secImg (x := ⟨x, hN⟩) hU⟩ :
          ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) ∈ S := by
    intro x hx
    have hx' : x ∈ Subgroup.closure {y | ∃ k ∈ Mc, ∃ z ∈ ZS153 T M V₁, k * z * k⁻¹ = y} := hx
    clear hx
    induction hx' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, hk, z, hz, rfl⟩ := hy
      have hkN := Mc_le_normalizer_Z cx hk
      have hN : k * z * k⁻¹ ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN (hZSN hz)) (Subgroup.inv_mem _ hkN)
      have hU : k * z * k⁻¹ ∈ UH153 T M V₁ Mc := mem_conjClosure hk hz
      refine ⟨hN, hU, ?_⟩
      have hzt : (⟨secMk _ _ ⟨z, hZSN hz⟩, secMk_mem_secImg (x := ⟨z, hZSN hz⟩) (ZS_le_U cx hz)⟩ :
          ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) ∈ tildeZS T M V₁ Mc :=
        secMk_mem_secImg (x := ⟨z, hZSN hz⟩) hz
      have hg : rhoU cx ⟨k, hk⟩ ∈ HStar153 T M V₁ Mc := by
        rw [← range_rhoU cx]
        exact MonoidHom.mem_range.2 ⟨⟨k, hk⟩, rfl⟩
      have hmap : (⟨secMk _ _ ⟨k * z * k⁻¹, hN⟩, secMk_mem_secImg (x := ⟨k * z * k⁻¹, hN⟩) hU⟩ :
          ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) =
          rhoU cx ⟨k, hk⟩ ⟨secMk _ _ ⟨z, hZSN hz⟩, secMk_mem_secImg (x := ⟨z, hZSN hz⟩)
            (ZS_le_U cx hz)⟩ := by
        apply Subtype.ext
        unfold rhoU
        rw [MonoidHom.comp_apply, Setup.rho_apply_coe]
        have hpi : ((piTilde cx ⟨k, hk⟩ : ↥(tildeOf (quasithinOmegaOneCenter T) Mc)) :
            SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
              (quasithinOmegaOneCenter T)) =
            secMk _ _ ⟨k, hkN⟩ := rfl
        rw [hpi]
        show secMk _ _ ⟨k * z * k⁻¹, hN⟩ =
          secMk _ _ ⟨k, hkN⟩ * secMk _ _ ⟨z, hZSN hz⟩ * (secMk _ _ ⟨k, hkN⟩)⁻¹
        have hprod : (⟨k * z * k⁻¹, hN⟩ : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))) =
            ⟨k, hkN⟩ * ⟨z, hZSN hz⟩ * ⟨k, hkN⟩⁻¹ := Subtype.ext rfl
        rw [hprod, map_mul, map_mul, map_inv]
      rw [hmap]
      have hle : (tildeZS T M V₁ Mc).map (rhoU cx ⟨k, hk⟩).toMonoidHom ≤ S :=
        le_iSup₂_of_le (rhoU cx ⟨k, hk⟩) hg le_rfl
      exact hle (Subgroup.mem_map_of_mem _ hzt)
    | one =>
      refine ⟨Subgroup.one_mem _, Subgroup.one_mem _, ?_⟩
      have : (⟨secMk _ _ ⟨(1 : G), Subgroup.one_mem _⟩, secMk_mem_secImg (x := ⟨1, Subgroup.one_mem _⟩)
          (Subgroup.one_mem _)⟩ : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) = 1 :=
        Subtype.ext (map_one _)
      rw [this]
      exact S.one_mem
    | mul a b _ _ iha ihb =>
      obtain ⟨hNa, hUa, ha⟩ := iha
      obtain ⟨hNb, hUb, hb⟩ := ihb
      refine ⟨Subgroup.mul_mem _ hNa hNb, Subgroup.mul_mem _ hUa hUb, ?_⟩
      have : (⟨secMk _ _ ⟨a * b, Subgroup.mul_mem _ hNa hNb⟩, secMk_mem_secImg
          (x := ⟨a * b, Subgroup.mul_mem _ hNa hNb⟩) (Subgroup.mul_mem _ hUa hUb)⟩ :
          ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) =
          ⟨secMk _ _ ⟨a, hNa⟩, secMk_mem_secImg (x := ⟨a, hNa⟩) hUa⟩ *
            ⟨secMk _ _ ⟨b, hNb⟩, secMk_mem_secImg (x := ⟨b, hNb⟩) hUb⟩ :=
        Subtype.ext (map_mul (secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) (quasithinOmegaOneCenter T)) ⟨a, hNa⟩ ⟨b, hNb⟩)
      rw [this]
      exact S.mul_mem ha hb
    | inv a _ iha =>
      obtain ⟨hNa, hUa, ha⟩ := iha
      refine ⟨Subgroup.inv_mem _ hNa, Subgroup.inv_mem _ hUa, ?_⟩
      have : (⟨secMk _ _ ⟨a⁻¹, Subgroup.inv_mem _ hNa⟩, secMk_mem_secImg
          (x := ⟨a⁻¹, Subgroup.inv_mem _ hNa⟩) (Subgroup.inv_mem _ hUa)⟩ :
          ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) =
          (⟨secMk _ _ ⟨a, hNa⟩, secMk_mem_secImg (x := ⟨a, hNa⟩) hUa⟩ :
            ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))⁻¹ :=
        Subtype.ext (map_inv (secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) (quasithinOmegaOneCenter T)) ⟨a, hNa⟩)
      rw [this]
      exact S.inv_mem ha
  obtain ⟨hN, hU, hmem⟩ := key (u : G) huU
  have hw : w = ⟨secMk _ _ ⟨(u : G), hN⟩, secMk_mem_secImg (x := ⟨(u : G), hN⟩) hU⟩ := by
    apply Subtype.ext
    exact hu.symm
  rw [hw]
  exact hmem

end Transv

end S153E

end CFSG.Quasithin
