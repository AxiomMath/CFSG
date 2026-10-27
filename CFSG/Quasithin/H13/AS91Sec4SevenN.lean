module

public import CFSG.Quasithin.H13.AS91Sec4Six
public import CFSG.Quasithin.H13.AS91Sec4SevenModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem card_sup_mul_card_inf_of_le_normalizer {H N : Subgroup G}
    (hHN : H ≤ normalizer (N : Set G)) :
    Nat.card (H ⊔ N : Subgroup G) * Nat.card (H ⊓ N : Subgroup G) = Nat.card H * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N))
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)
  rw [← Nat.card_congr e.toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv] at h1
  rw [card_subgroupOf_eq H N] at h2
  rw [h1, h2]
  ring

theorem exists_mul_of_mem_sup {N H : Subgroup G} (hHN : H ≤ normalizer (N : Set G)) {x : G}
    (hx : x ∈ N ⊔ H) : ∃ n ∈ N, ∃ y ∈ H, n * y = x := by
  have hx' : x ∈ ((N ⊔ H : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N H hHN, Set.mem_mul] at hx'
  exact hx'

namespace Data41

variable {z : G} {h : HypJ4 G z} (D : Data41 h)

section Image


theorem card_of_image {X : Subgroup G} {Y : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hXE : X ≤ D.E)
    (hE1X : D.E1 ≤ X)
    (hmaps : ∀ x (hx : x ∈ X), D.Φo (h.setting.ρ ⟨x, D.E_le_M (hXE hx)⟩) ∈ Y)
    (honto : ∀ U ∈ Y, ∃ x, ∃ hx : x ∈ X, D.Φo (h.setting.ρ ⟨x, D.E_le_M (hXE hx)⟩) = U) :
    Nat.card X = 2 ^ 7 * Nat.card Y := by
  let f : ↥X →* ↥Y :=
    ((D.Φo.comp h.setting.ρ).comp (Subgroup.inclusion (hXE.trans D.E_le_M))).codRestrict Y
      fun x => hmaps x x.2
  have hsurj : Function.Surjective f := by
    rintro ⟨U, hU⟩
    obtain ⟨x, hx, hxU⟩ := honto U hU
    exact ⟨⟨x, hx⟩, Subtype.ext hxU⟩
  have hker : f.ker = D.E1.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h1
      have h2 : D.Φo (h.setting.ρ (Subgroup.inclusion (hXE.trans D.E_le_M) x)) = D.Φo 1 := by
        rw [map_one]
        exact congrArg Subtype.val h1
      exact D.mem_E1_of_mem_E ((h.setting.ρ_eq_one_iff _).mp (D.Φo_injective h2)) (hXE x.2)
    · intro hx
      apply Subtype.ext
      show D.Φo (h.setting.ρ (Subgroup.inclusion (hXE.trans D.E_le_M) x)) = 1
      rw [(h.setting.ρ_eq_one_iff _).mpr (D.E1_le_QG hx), map_one]
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hker,
    card_subgroupOf_eq, inf_of_le_right hE1X, D.card_E1] at h1
  exact h1.symm

end Image

section Norm

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)

include hOut hTw

theorem E_comm (hHat : HatM22SmallModules) {a b : G} (ha : a ∈ D.E) (hb : b ∈ D.E) :
    a * b = b * a :=
  congrArg Subtype.val ((D.isElemAbelian_E hHat hOut hTw).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem mem_G13_of_normalizer {g : G} (hgM : g ∈ h.setting.M)
    (hg : g ∈ normalizer (D.E : Set G)) : g ∈ D.G13 := by
  have hE1 : ∀ x ∈ D.E1, g * x * g⁻¹ ∈ D.E1 := fun x hx =>
    D.mem_E1_of_mem_E (h.setting.conj_mem_QG hgM hx.1)
      ((mem_normalizer_iff.mp hg x).mp (D.E1_le_E hx))
  have hsub : ⇑(D.Φo (h.setting.ρ ⟨g, hgM⟩)) '' Two.W1 ⊆ Two.W1 := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨y, hyQ, hyv⟩ := h.setting.exists_cl (D.ψV.symm v)
    have hyE : y ∈ D.E1 := ⟨hyQ, by rw [hyv, D.mem_W1q, AddEquiv.apply_symm_apply]; exact hv⟩
    have h2 := (hE1 y hyE).2
    rw [D.mem_W1q] at h2
    rw [← AddEquiv.apply_symm_apply D.ψV v, ← hyv, Φo_apply_ψV, h.setting.ρ_cl _ hyQ]
    exact h2
  have heq : ⇑(D.Φo (h.setting.ρ ⟨g, hgM⟩)) '' Two.W1 = Two.W1 :=
    Set.eq_of_subset_of_ncard_le hsub
      (by rw [Set.ncard_image_of_injective _ (LinearEquiv.injective _)]) (Set.toFinite _)
  exact mem_pre_of_rho ⟨g, hgM⟩ (Two.mem_g13Grp.mpr ⟨D.Φo_mem_nGrp hOut hTw ⟨_, rfl⟩, heq⟩)

theorem mem_normalizer_E_iff {g : G} (hgM : g ∈ h.setting.M) :
    g ∈ normalizer (D.E : Set G) ↔ g ∈ D.G13 :=
  ⟨D.mem_G13_of_normalizer hOut hTw hgM, fun hg =>
    mem_normalizer_fintype fun _ he => D.conj_mem_E hg he⟩

end Norm

section SevenN

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3)
  {s₀ : h.setting.M} (hs₀ : D.Φo (h.setting.ρ s₀) = Two.tE)

include hOut hTw hg₁ hs₀

theorem Zinf_le_E1 : Zinf (h := h) g₁ s₀ ≤ D.E1 := fun x hx => by
  obtain ⟨hxQ, hxZ⟩ := (D.mem_Zinf_iff hOut hTw hg₁ hs₀).mp hx
  exact ⟨hxQ, Two.mem_W1_of_inZ hxZ⟩

theorem E_le_S : D.E ≤ centralizer (Zinf (h := h) g₁ s₀ : Set G) := fun x hx =>
  mem_centralizer_iff.mpr fun y hy => (D.mem_E.mp hx) y (D.Zinf_le_E1 hOut hTw hg₁ hs₀ hy)

omit
  hOut hTw hg₁ hs₀ in
theorem Bgrp_le_T : D.Bgrp g₁ s₀ ≤ D.T :=
  inf_le_right.trans (pre_le_pre (Subgroup.comap_mono Two.p2Grp_le_pGrp))

omit
  hOut hTw hg₁ hs₀ in
theorem Bgrp_le_G13 : D.Bgrp g₁ s₀ ≤ D.G13 := D.Bgrp_le_T.trans D.T_le_G13

theorem conj_mem_E_of_K (hHat : HatM22SmallModules) {k : G} (hk : k ∈ Kgrp (h := h) g₁ s₀)
    {e : G} (he : e ∈ D.E) : k * e * k⁻¹ ∈ D.E := by
  have hAT : D.E.map (MulAut.conj k).toMonoidHom ≤ D.T := by
    rintro _ ⟨e', he', rfl⟩
    have h1 := D.commutator_mem_Bgrp hOut hTw hg₁ hs₀ hk (D.E_le_S hOut hTw hg₁ hs₀ he')
    have e1 : (MulAut.conj k).toMonoidHom e' = (k * e' * k⁻¹ * e'⁻¹) * e' := by
      show k * e' * k⁻¹ = _
      group
    rw [e1]
    exact mul_mem (D.Bgrp_le_T h1) (D.E_le_T hOut hTw he')
  have hAc : ∀ x ∈ D.E.map (MulAut.conj k).toMonoidHom,
      ∀ y ∈ D.E.map (MulAut.conj k).toMonoidHom, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, D.E_comm hOut hTw hHat ha hb]
  have hcard : Nat.card (D.E.map (MulAut.conj k).toMonoidHom) = 2 ^ 11 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, D.card_E hOut hTw]
  have hE1 := (D.card_le_of_comm hOut hTw hAT hAc).2 hcard
  exact D.mem_E.mpr fun y hy => hAc y (hE1 hy) _ ⟨e, he, rfl⟩

theorem K_le_normalizer_E (hHat : HatM22SmallModules) :
    Kgrp (h := h) g₁ s₀ ≤ normalizer (D.E : Set G) := fun _ hk =>
  mem_normalizer_fintype fun _ he => D.conj_mem_E_of_K hOut hTw hg₁ hs₀ hHat hk he

theorem card_E_inf_R : Nat.card (D.E ⊓ D.Bgrp g₁ s₀ : Subgroup G) = 2 ^ 9 := by
  have h1 := D.card_of_image (X := D.E ⊓ D.Bgrp g₁ s₀) (Y := Two.iGrp) inf_le_left
    (fun x hx => ⟨D.E1_le_E hx, D.E_le_S hOut hTw hg₁ hs₀ (D.E1_le_E hx),
      QG_le_pre _ (D.E1_le_QG hx)⟩)
    (fun x hx => by
      rw [← Two.eb_inf_p2]
      exact ⟨D.Φo_mem_eb hOut hTw hx.1 _, rho_mem_of_mem_pre hx.2.2 _⟩)
    (fun U hU => by
      rw [← Two.eb_inf_p2] at hU
      obtain ⟨s, hsE, hsU⟩ := D.exists_mem_E hOut hTw hU.1
      refine ⟨s, ⟨hsE, D.E_le_S hOut hTw hg₁ hs₀ hsE, mem_pre_of_rho s ?_⟩, hsU⟩
      show D.Φo (h.setting.ρ s) ∈ Two.p2Grp
      rw [hsU]
      exact hU.2)
  rw [h1, Two.card_iGrp]
  norm_num

theorem E_le_normalizer_R : D.E ≤ normalizer (D.Bgrp g₁ s₀ : Set G) := fun _ he =>
  mem_normalizer_fintype fun _ hb => D.conj_mem_Bgrp hOut hTw hg₁ hs₀
    (centralizer_le_normalizer _ (D.E_le_S hOut hTw hg₁ hs₀ he)) hb

theorem card_R_sup_E : Nat.card (D.Bgrp g₁ s₀ ⊔ D.E : Subgroup G) = 2 ^ 17 := by
  have h1 := card_sup_mul_card_inf_of_le_normalizer (D.E_le_normalizer_R hOut hTw hg₁ hs₀)
  rw [D.card_E_inf_R hOut hTw hg₁ hs₀, D.card_E hOut hTw, D.card_Bgrp hOut hTw hg₁ hs₀,
    sup_comm] at h1
  have h2 : Nat.card (D.Bgrp g₁ s₀ ⊔ D.E : Subgroup G) * 2 ^ 9 = 2 ^ 17 * 2 ^ 9 := by
    rw [h1]
    norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2

theorem index_G13_S :
    (D.G13.subgroupOf (centralizer (Zinf (h := h) g₁ s₀ : Set G))).index = 5 := by
  obtain ⟨ψ, hψs, hψ⟩ := D.exists_psi hOut hTw hg₁ hs₀
  have hst := D.stabIn_three hOut hTw
  let w1 : ↥Two.w5Action := ⟨Two.W1, ⟨Two.w1Mask (), Two.w1Mask_mem_w5, rfl⟩⟩
  have key : D.G13.subgroupOf (centralizer (Zinf (h := h) g₁ s₀ : Set G)) =
      (MulAction.stabilizer (Equiv.Perm (Fin 5))
        (Finite.equivFinOfCardEq Two.card_w5Action w1)).comap (Two.chi.comp ψ) := by
    ext x
    rw [mem_subgroupOf, mem_comap, MulAction.mem_stabilizer_iff, MonoidHom.comp_apply]
    have h1 : Two.chi (ψ x) • Finite.equivFinOfCardEq Two.card_w5Action w1 =
        Finite.equivFinOfCardEq Two.card_w5Action (ψ x • w1) := by
      show Finite.equivFinOfCardEq Two.card_w5Action
        ((MulAction.toPermHom _ _ (ψ x)) ((Finite.equivFinOfCardEq Two.card_w5Action).symm
          (Finite.equivFinOfCardEq Two.card_w5Action w1))) = _
      rw [Equiv.symm_apply_apply]
      rfl
    rw [h1, (Finite.equivFinOfCardEq Two.card_w5Action).apply_eq_iff_eq]
    constructor
    · intro hx
      apply Subtype.ext
      show ⇑((ψ x : ↥Two.gammaZ) : V12 ≃ₗ[ZMod 2] V12) '' Two.W1 = Two.W1
      rw [hψ x]
      obtain ⟨hxM', hρ⟩ := mem_pre.mp hx
      exact (Two.mem_g13Grp.mp hρ).2
    · intro hx
      have hW : ⇑((ψ x : ↥Two.gammaZ) : V12 ≃ₗ[ZMod 2] V12) '' Two.W1 = Two.W1 :=
        congrArg Subtype.val hx
      rw [hψ x] at hW
      have hρ : h.setting.ρ (Subgroup.inclusion (D.hSM hOut hTw hg₁ hs₀) x) ∈ D.g13bar :=
        Two.mem_g13Grp.mpr ⟨D.Φo_mem_nGrp hOut hTw ⟨_, rfl⟩, hW⟩
      exact mem_pre_of_rho _ hρ
  have hsurj : Function.Surjective (Two.chi.comp ψ) := (Two.chi_surjective hst).comp hψs
  rw [key, Subgroup.index_comap_of_surjective _ hsurj,
    MulAction.index_stabilizer_of_transitive, Nat.card_fin]

theorem exists_mul_of_mem_G12 (hHat : HatM22SmallModules) {g : G}
    (hg : g ∈ normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G)) :
    ∃ k ∈ Kgrp (h := h) g₁ s₀, ∃ s ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ D.G13,
      k * s = g := by
  have hSK : centralizer (Zinf (h := h) g₁ s₀ : Set G) ≤
      normalizer (Kgrp (h := h) g₁ s₀ : Set G) := fun _ hs =>
    mem_normalizer_fintype fun _ hk => conj_mem_Kgrp (h := h) (centralizer_le_normalizer _ hs) hk
  have hgN := hg.1
  rw [(D.K_facts hOut hTw hg₁ hs₀).1] at hgN
  obtain ⟨k, hk, s, hs, rfl⟩ := exists_mul_of_mem_sup hSK hgN
  refine ⟨k, hk, s, ⟨hs, ?_⟩, rfl⟩
  have hsE : s ∈ normalizer (D.E : Set G) := by
    simpa using mul_mem (inv_mem (D.K_le_normalizer_E hOut hTw hg₁ hs₀ hHat hk)) hg.2
  exact (D.mem_normalizer_E_iff hOut hTw (D.hSM hOut hTw hg₁ hs₀ hs)).mp hsE

theorem G12_eq_sup (hHat : HatM22SmallModules) :
    normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G) =
      Kgrp (h := h) g₁ s₀ ⊔ (centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ D.G13) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨k, hk, s, hs, rfl⟩ := D.exists_mul_of_mem_G12 hOut hTw hg₁ hs₀ hHat hg
    exact mul_mem (mem_sup_left hk) (mem_sup_right hs)
  · refine sup_le (le_inf (D.Kgrp_le_normalizer hOut hTw hg₁ hs₀)
      (D.K_le_normalizer_E hOut hTw hg₁ hs₀ hHat)) ?_
    exact le_inf (inf_le_left.trans (centralizer_le_normalizer _)) fun g hg =>
      (D.mem_normalizer_E_iff hOut hTw (pre_le_M _ hg.2)).mpr hg.2

theorem relIndex_G12 (hHat : HatM22SmallModules) :
    (normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G)).relIndex
      (normalizer (Zinf (h := h) g₁ s₀ : Set G)) = 5 := by
  have hSK : centralizer (Zinf (h := h) g₁ s₀ : Set G) ≤
      normalizer (Kgrp (h := h) g₁ s₀ : Set G) := fun _ hs =>
    mem_normalizer_fintype fun _ hk => conj_mem_Kgrp (h := h) (centralizer_le_normalizer _ hs) hk
  have hR : centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ Kgrp (h := h) g₁ s₀ = D.Bgrp g₁ s₀ := by
    rw [inf_comm, D.Kgrp_inf_eq_Bgrp hOut hTw hg₁ hs₀]
  have hR' : centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ D.G13 ⊓ Kgrp (h := h) g₁ s₀ =
      D.Bgrp g₁ s₀ :=
    le_antisymm (by rw [← hR]; exact inf_le_inf_right _ inf_le_left)
      (le_inf (le_inf (D.Bgrp_le_centralizer hOut hTw hg₁ hs₀) D.Bgrp_le_G13)
        (D.Bgrp_le_Kgrp hOut hTw hg₁ hs₀))
  have c1 := card_sup_mul_card_inf_of_le_normalizer hSK
  rw [sup_comm, ← (D.K_facts hOut hTw hg₁ hs₀).1, hR] at c1
  have c2 := card_sup_mul_card_inf_of_le_normalizer
    (inf_le_left.trans hSK : centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ D.G13 ≤ _)
  rw [sup_comm, ← D.G12_eq_sup hOut hTw hg₁ hs₀ hHat, hR'] at c2
  have c3 := Subgroup.card_mul_index
    (D.G13.subgroupOf (centralizer (Zinf (h := h) g₁ s₀ : Set G)))
  rw [D.index_G13_S hOut hTw hg₁ hs₀, card_subgroupOf_eq] at c3
  have hc := Subgroup.relIndex_mul_card
    (normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ normalizer (D.E : Set G))
    (normalizer (Zinf (h := h) g₁ s₀ : Set G))
  rw [inf_of_le_left inf_le_left] at hc
  have hRpos : 0 < Nat.card (D.Bgrp g₁ s₀) := Nat.card_pos
  have hGpos : 0 < Nat.card ↥(normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓
      normalizer (D.E : Set G)) := Nat.card_pos
  generalize Nat.card ↥(normalizer (Zinf (h := h) g₁ s₀ : Set G)) = n at c1 hc
  generalize Nat.card ↥(normalizer (Zinf (h := h) g₁ s₀ : Set G) ⊓
    normalizer (D.E : Set G)) = g at c2 hc hGpos
  generalize Nat.card (D.Bgrp g₁ s₀) = r at c1 c2 hRpos
  generalize Nat.card ↥(Kgrp (h := h) g₁ s₀) = k at c1 c2
  generalize Nat.card ↥(centralizer (Zinf (h := h) g₁ s₀ : Set G)) = s at c1 c3
  generalize Nat.card ↥(centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ D.G13) = t at c2 c3
  have hn : n = 5 * g := by
    apply Nat.eq_of_mul_eq_mul_right hRpos
    calc n * r = s * k := c1
      _ = 5 * (t * k) := by rw [← c3]; ring
      _ = 5 * g * r := by rw [← c2]; ring
  rw [hn] at hc
  exact Nat.eq_of_mul_eq_mul_right hGpos hc

end SevenN

end Data41

end CFSG.Quasithin.H13.AS91
