module

public import CFSG.Quasithin.Vol2.Ch11SecBHBMain

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

theorem solvableRadical_quotient_eq_bot_of_le {A : Type*} [Group A] [Finite A] (N : Subgroup A)
    [N.Normal] (hNs : Group.IsSolvable ↥N) (hRN : CFSG.solvableRadical A ≤ N) :
    CFSG.solvableRadical (A ⧸ N) = ⊥ := by
  set R' := CFSG.solvableRadical (A ⧸ N) with hR'
  have hR's : Group.IsSolvable R' := A3.solvableRadical_isSolvable
  let Φ : A →* A ⧸ N := QuotientGroup.mk' N
  let P : Subgroup A := R'.comap Φ
  have hNP : N ≤ P := fun x hx => by
    have h1 : (x : A ⧸ N) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    show (x : A ⧸ N) ∈ R'
    rw [h1]
    exact R'.one_mem
  have hPnormal : P.Normal := Subgroup.Normal.comap inferInstance _
  have hPs : Group.IsSolvable P := by
    let g : ↥P →* ↥R' := (Φ.comp P.subtype).codRestrict R' (fun p => p.2)
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNP) g (fun p hp => ?_)
    have h1 : Φ p = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hp)
      exact this
    have h2 : (p : A) ∈ N := (QuotientGroup.eq_one_iff (p : A)).mp h1
    exact ⟨⟨p, h2⟩, rfl⟩
  have hPN : P ≤ N := (A3.le_solvableRadical hPnormal hPs).trans hRN
  have h3 : R' = P.map Φ :=
    (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) R').symm
  have h4 : P.map Φ ≤ ⊥ := by
    have := Subgroup.map_mono (f := Φ) hPN
    rwa [QuotientGroup.map_mk'_self] at this
  exact le_bot_iff.mp (h3 ▸ h4)

variable {G : Type} [Group G] [Finite G]

theorem isComponent_star {H X L : Subgroup G} (hXH : X ≤ H)
    (hJs : Group.IsSolvable ↥(kerIn X H))
    (hRJ : solvRad H ≤ kerIn X H) (hL : L ∈ cComp H) : CFSG.IsComponent (E2.star X H L) := by
  have hJs' : Group.IsSolvable ↥((kerIn X H).subgroupOf H) := by
    have hle : kerIn X H ≤ H := kerIn_le.trans hXH
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).injective
  have hR : CFSG.solvableRadical ↥H ≤ (kerIn X H).subgroupOf H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hRJ ((solvRad_eq_map_solvableRadical H).symm ▸ ⟨x, hx, rfl⟩)
  have hker : (QuotientGroup.mk' ((kerIn X H).subgroupOf H)).ker = (kerIn X H).subgroupOf H :=
    QuotientGroup.ker_mk' _
  have h3 := map_mem_cComp_top (QuotientGroup.mk' ((kerIn X H).subgroupOf H))
    (QuotientGroup.mk'_surjective _) (by rw [hker]; exact hJs') (subgroupOf_mem_cComp hL)
  exact isComponent_of_mem_cComp_top
    (solvableRadical_quotient_eq_bot_of_le _ hJs' hR) h3

omit [Finite G] in
theorem star_cjSub {H X L : Subgroup G} {s : G} (hs : s ∈ H) :
    E2.star X H (cjSub s L) = (E2.star X H L).map
      (MulAut.conj (QuotientGroup.mk' ((kerIn X H).subgroupOf H) ⟨s, hs⟩)).toMonoidHom := by
  set π := QuotientGroup.mk' ((kerIn X H).subgroupOf H) with hπ
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : s⁻¹ * (y : G) * s ∈ L := mem_cjSub.mp (Subgroup.mem_subgroupOf.mp hy)
    have hz : s⁻¹ * (y : G) * s ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hs) y.2) hs
    have hmem : π ⟨_, hz⟩ ∈ E2.star X H L := ⟨⟨_, hz⟩, Subgroup.mem_subgroupOf.mpr hy', rfl⟩
    refine ⟨π ⟨_, hz⟩, hmem, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_mul, ← map_inv]
    congr 1
    apply Subtype.ext
    simp [mul_assoc]
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hy' : (y : G) ∈ L := Subgroup.mem_subgroupOf.mp hy
    have hz : s * (y : G) * s⁻¹ ∈ H := H.mul_mem (H.mul_mem hs y.2) (H.inv_mem hs)
    have hz' : s * (y : G) * s⁻¹ ∈ cjSub s L := by
      rw [mem_cjSub]
      simpa [mul_assoc] using hy'
    refine ⟨⟨_, hz⟩, Subgroup.mem_subgroupOf.mpr hz', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv]
    congr 1

omit [Finite G] in
theorem le_sup_of_star_le {H X L₁ L₂ : Subgroup G} (hL₁ : L₁ ≤ H)
    (h : E2.star X H L₁ ≤ E2.star X H L₂) : L₁ ≤ L₂ ⊔ kerIn X H := by
  intro x hx
  have hmem : QuotientGroup.mk' ((kerIn X H).subgroupOf H) ⟨x, hL₁ hx⟩ ∈ E2.star X H L₁ :=
    ⟨⟨x, hL₁ hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := h hmem
  have hy' : (y : G) ∈ L₂ := Subgroup.mem_subgroupOf.mp hy
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hyx
  have : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hy' (by simpa using hyx)

theorem eq_of_star_eq {H X L₁ L₂ : Subgroup G} (hXH : X ≤ H)
    (hJs : Group.IsSolvable ↥(kerIn X H)) (hL₁ : L₁ ∈ cComp H) (hL₂ : L₂ ∈ cComp H)
    (h : E2.star X H L₁ = E2.star X H L₂) : L₁ = L₂ := by
  have hJH : kerIn X H ≤ H := kerIn_le.trans hXH
  have key : ∀ {A B : Subgroup G}, A ∈ cComp H → B ∈ cComp H →
      E2.star X H A ≤ E2.star X H B → A ≤ B := by
    intro A B hA hB hAB
    have h1 := le_sup_of_star_le (le_of_mem_cComp hA) hAB
    have h2 : perfectCore (B ⊔ kerIn X H) = B := (cComp_commutator_perfectCore hB hJH hJs
      ((le_of_mem_cComp hB).trans (le_normalizer_kerIn X H))).2
    calc A = perfectCore A := (perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hA)).symm
      _ ≤ perfectCore (B ⊔ kerIn X H) := perfectCore_mono h1
      _ = B := h2
  exact le_antisymm (key hL₁ hL₂ h.le) (key hL₂ hL₁ h.ge)

theorem le_normalizer_sup_of_star {H X L K : Subgroup G} (hXH : X ≤ H)
    (hJs : Group.IsSolvable ↥(kerIn X H)) (hL : L ∈ cComp H) (hK : K ∈ cComp H)
    (h : E2.star X H L = E2.star X H K ∨ ⁅E2.star X H L, E2.star X H K⁆ = ⊥) :
    L ≤ Subgroup.normalizer ((K ⊔ kerIn X H : Subgroup G) : Set G) := by
  have hHJ : H ≤ Subgroup.normalizer (kerIn X H : Set G) := le_normalizer_kerIn X H
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hKH : K ≤ H := le_of_mem_cComp hK
  rcases h with h | h
  · rw [eq_of_star_eq hXH hJs hL hK h]
    exact fun x hx => mem_normalizer_sup_of_mem (Subgroup.le_normalizer hx) (hHJ (hKH hx))
  have hle : ∀ x ∈ L, (K ⊔ kerIn X H).map (MulAut.conj x).toMonoidHom ≤ K ⊔ kerIn X H := by
    intro x hx
    rw [Subgroup.map_sup, map_conj_eq_self_of_mem_normalizer (hHJ (hLH hx))]
    refine sup_le ?_ le_sup_right
    rintro _ ⟨k, hk, rfl⟩
    have hxs : QuotientGroup.mk' ((kerIn X H).subgroupOf H) ⟨x, hLH hx⟩ ∈ E2.star X H L :=
      ⟨⟨x, hLH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hks : QuotientGroup.mk' ((kerIn X H).subgroupOf H) ⟨k, hKH hk⟩ ∈ E2.star X H K :=
      ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have hc : ⁅(⟨x, hLH hx⟩ : ↥H), (⟨k, hKH hk⟩ : ↥H)⁆ ∈ (kerIn X H).subgroupOf H := by
      rw [← QuotientGroup.ker_mk' ((kerIn X H).subgroupOf H), MonoidHom.mem_ker,
        map_commutatorElement]
      have := Subgroup.commutator_mem_commutator hxs hks
      rwa [h, Subgroup.mem_bot] at this
    have hc' : ⁅x, k⁆ ∈ kerIn X H := by
      have := Subgroup.mem_subgroupOf.mp hc
      simpa [commutatorElement_def] using this
    have he : (MulAut.conj x).toMonoidHom k = ⁅x, k⁆ * k := by
      simp [commutatorElement_def, mul_assoc]
    rw [he, sup_comm]
    exact Subgroup.mul_mem_sup hc' hk
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hle x hx ⟨y, hy, rfl⟩
  · intro hy
    have := hle x⁻¹ (L.inv_mem hx) ⟨_, hy, rfl⟩
    simpa [mul_assoc] using this

end CFSG.Quasithin.Vol2.Ch11.SecB
