module

public import CFSG.Quasithin.EmptyFaithful.S14612EC
public import CFSG.Quasithin.EmptyFaithful.Gap6Dec12Sec
public import CFSG.Quasithin.Background.C1PackS14612One

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
open scoped commutatorElement

section HL

variable {G : Type} [Group G] {H : Subgroup G} {V' : Type*} [Group V']

@[expose] def HLb (β : ↥H →* MulAut V') (L : Subgroup (MulAut V')) : Subgroup G :=
  (L.comap β).map H.subtype

variable {β : ↥H →* MulAut V'} {L L' : Subgroup (MulAut V')}

theorem mem_HLb {g : G} : g ∈ HLb β L ↔ ∃ h : ↥H, β h ∈ L ∧ (h : G) = g := by
  unfold HLb
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.subtype_apply]

theorem HLb_le (L : Subgroup (MulAut V')) : HLb β L ≤ H := by
  intro g hg
  obtain ⟨h, -, rfl⟩ := mem_HLb.1 hg
  exact h.2

theorem mem_HLb_iff {g : G} (hg : g ∈ H) : g ∈ HLb β L ↔ β ⟨g, hg⟩ ∈ L := by
  constructor
  · intro h
    obtain ⟨h', hL, rfl⟩ := mem_HLb.1 h
    exact hL
  · intro h
    exact mem_HLb.2 ⟨⟨g, hg⟩, h, rfl⟩

theorem mem_HLb_of_mem {h : ↥H} (hh : β h ∈ L) : (h : G) ∈ HLb β L := mem_HLb.2 ⟨h, hh, rfl⟩

theorem HLb_mono (h : L ≤ L') : HLb β L ≤ HLb β L' := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := mem_HLb.1 hg
  exact mem_HLb_of_mem (h hx)

theorem HLb_inf (L L' : Subgroup (MulAut V')) : HLb β (L ⊓ L') = HLb β L ⊓ HLb β L' := by
  ext g
  constructor
  · intro hg
    exact ⟨HLb_mono inf_le_left hg, HLb_mono inf_le_right hg⟩
  · rintro ⟨h1, h2⟩
    have hgH : g ∈ H := HLb_le L h1
    exact (mem_HLb_iff hgH).2 ⟨(mem_HLb_iff hgH).1 h1, (mem_HLb_iff hgH).1 h2⟩

theorem HLb_bot : HLb β (⊥ : Subgroup (MulAut V')) = β.ker.map H.subtype := by
  ext g
  constructor
  · intro hg
    obtain ⟨x, hx, rfl⟩ := mem_HLb.1 hg
    exact ⟨x, MonoidHom.mem_ker.2 (Subgroup.mem_bot.1 hx), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact mem_HLb_of_mem (Subgroup.mem_bot.2 (MonoidHom.mem_ker.1 hx))

theorem HLb_sup (hL : L ≤ β.range) (hL' : L' ≤ β.range) :
    HLb β (L ⊔ L') = HLb β L ⊔ HLb β L' := by
  unfold HLb
  rw [← Subgroup.map_sup, Subgroup.comap_sup_eq_of_le_range _ hL hL']

theorem HLb_le_of_le (hL : L ≤ β.range) (h : HLb β L ≤ HLb β L') : L ≤ L' := by
  intro l hl
  obtain ⟨x, rfl⟩ := hL hl
  exact (mem_HLb_iff x.2).1 (h (mem_HLb_of_mem hl))

theorem HLb_injective (hL : L ≤ β.range) (hL' : L' ≤ β.range) (h : HLb β L = HLb β L') : L = L' :=
  le_antisymm (HLb_le_of_le hL h.le) (HLb_le_of_le hL' h.ge)

theorem conjSub_HLb {t : G} (ht : t ∈ H)
    (hLL' : ∀ x, x ∈ L' ↔ (β ⟨t, ht⟩)⁻¹ * x * β ⟨t, ht⟩ ∈ L) :
    conjSub t (HLb β L) = HLb β L' := by
  ext g
  rw [mem_conjSub]
  constructor
  · intro hg
    have hgH' : t⁻¹ * g * t ∈ H := HLb_le L hg
    have hgH : g ∈ H := by
      have := H.mul_mem (H.mul_mem ht hgH') (H.inv_mem ht)
      simpa [mul_assoc] using this
    refine (mem_HLb_iff hgH).2 ?_
    rw [hLL']
    have h1 := (mem_HLb_iff hgH').1 hg
    have e : (⟨t, ht⟩⁻¹ * ⟨g, hgH⟩ * ⟨t, ht⟩ : ↥H) = ⟨t⁻¹ * g * t, hgH'⟩ := Subtype.ext rfl
    rw [← map_inv, ← map_mul, ← map_mul, e]
    exact h1
  · intro hg
    have hgH : g ∈ H := HLb_le _ hg
    have hgH' : t⁻¹ * g * t ∈ H := H.mul_mem (H.mul_mem (H.inv_mem ht) hgH) ht
    refine (mem_HLb_iff hgH').2 ?_
    have h1 := (mem_HLb_iff hgH).1 hg
    rw [hLL'] at h1
    have e : (⟨t, ht⟩⁻¹ * ⟨g, hgH⟩ * ⟨t, ht⟩ : ↥H) = ⟨t⁻¹ * g * t, hgH'⟩ := Subtype.ext rfl
    rw [← map_inv, ← map_mul, ← map_mul, e] at h1
    exact h1

theorem secIso_HLb {Q : Subgroup G} (hQ : β.ker.map H.subtype = Q) (hL : L ≤ β.range)
    {D : Type*} [Group D] (e : ↥L ≃* D) : SecIso (HLb β L) Q D := by
  let f : ↥(HLb β L) →* ↥L := ((β).comp (Subgroup.inclusion (HLb_le L))).codRestrict L
    (fun x => (mem_HLb_iff (HLb_le L x.2)).1 x.2)
  have hker : f.ker = Q.subgroupOf (HLb β L) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hQ]
    have : f x = 1 ↔ β (Subgroup.inclusion (HLb_le L) x) = 1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [this]
    constructor
    · intro h
      exact ⟨Subgroup.inclusion (HLb_le L) x, MonoidHom.mem_ker.2 h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : Subgroup.inclusion (HLb_le L) x = y := Subtype.ext hyx.symm
      rw [this]
      exact MonoidHom.mem_ker.1 hy
  have hsurj : Function.Surjective f := by
    intro l
    obtain ⟨h, hh⟩ := hL l.2
    have hmem : (h : G) ∈ HLb β L := mem_HLb_of_mem (by rw [hh]; exact l.2)
    exact ⟨⟨h, hmem⟩, Subtype.ext hh⟩
  have hnorm : (Q.subgroupOf (HLb β L)).Normal := hker ▸ f.normal_ker
  refine ⟨hnorm, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    ((QuotientGroup.quotientKerEquivOfSurjective f hsurj).trans e)

end HL

section Dict

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

abbrev UMod (h : HypF91 T V L V₁ Vp H) : Type :=
  IntMod (tildeOf V₁ (conjClosure Vp H)) h.isElemAbelian_tilde

@[expose] def valW (h : HypF91 T V L V₁ Vp H) : UMod h →* SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁ :=
  ⟨⟨IntMod.val, rfl⟩, IntMod.val_mul⟩

theorem valW_injective (h : HypF91 T V L V₁ Vp H) : Function.Injective (valW h) := IntMod.val_injective

@[expose] noncomputable def valK (h : HypF91 T V L V₁ Vp H) :
    ↥(kOf (rhoH h)) →* SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁ :=
  (valW h).comp (kOf (rhoH h)).subtype

theorem valK_injective (h : HypF91 T V L V₁ Vp H) : Function.Injective (valK h) :=
  (valW_injective h).comp Subtype.val_injective

theorem rhoH_val (h : HypF91 T V L V₁ Vp H) (x : ↥H) (w : UMod h) :
    (rhoH h x w).val = secMk (Subgroup.normalizer (V₁ : Set G)) V₁
        (Subgroup.inclusion h.H_normalizes_V₁ x) * w.val *
      (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (Subgroup.inclusion h.H_normalizes_V₁ x))⁻¹ := by
  unfold rhoH
  rw [MonoidHom.comp_apply, convHom_apply, convI_apply_val]
  rfl

theorem U_le_normalizer (h : HypF91 T V L V₁ Vp H) :
    conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
  h.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans h.H_normalizes_V₁)

theorem valK_comm_gen (h : HypF91 T V L V₁ Vp H) (hh : ↥H) (v : ↥(kOf (rhoH h))) :
    valK h (resBeta (rhoH h) hh v * v⁻¹) =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (Subgroup.inclusion h.H_normalizes_V₁ hh) *
        valK h v *
        (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (Subgroup.inclusion h.H_normalizes_V₁ hh))⁻¹ *
        (valK h v)⁻¹ := by
  have e2 := rhoH_val h hh (v : UMod h)
  have h1 : (((resBeta (rhoH h) hh v * v⁻¹ : ↥(kOf (rhoH h)))) : UMod h) =
      rhoH h hh (v : UMod h) * (v : UMod h)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, resBeta_apply]
  calc valK h (resBeta (rhoH h) hh v * v⁻¹) = valW h (rhoH h hh (v : UMod h) * (v : UMod h)⁻¹) :=
        congrArg (valW h) h1
    _ = (rhoH h hh (v : UMod h)).val * ((v : UMod h).val)⁻¹ := by rw [map_mul, map_inv]; rfl
    _ = _ := by rw [e2]; rfl

theorem rho_mul_inv_eq (h : HypF91 T V L V₁ Vp H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    (hh : ↥H) (w : UMod h) :
    ∃ a : ↥(kOf (rhoH h)),
      rhoH h hh w * w⁻¹ = ((resBeta (rhoH h) hh a * a⁻¹ : ↥(kOf (rhoH h))) : UMod h) := by
  obtain ⟨a, ha, c, hc, hac⟩ := hsplit w
  refine ⟨⟨a, ha⟩, ?_⟩
  have hcfix : rhoH h hh c = c := hc (rhoH h hh) ⟨hh, rfl⟩
  rw [hac, map_mul, hcfix]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, resBeta_apply]
  rw [mul_inv_rev]
  calc rhoH h hh a * c * (c⁻¹ * a⁻¹) = rhoH h hh a * (c * c⁻¹) * a⁻¹ := by simp only [mul_assoc]
    _ = rhoH h hh a * a⁻¹ := by simp

theorem tildeOf_comm_HLb (h : HypF91 T V L V₁ Vp H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Lb : Subgroup (MulAut ↥(kOf (rhoH h)))} (hLb : Lb ≤ (resBeta (rhoH h)).range) :
    tildeOf V₁ (⁅conjClosure Vp H, HLb (resBeta (rhoH h)) Lb⁆ ⊔ V₁) = (commV Lb).map (valK h) := by
  have hHU : H ≤ Subgroup.normalizer (conjClosure Vp H : Set G) := le_normalizer_conjClosure _ _
  have hUN := U_le_normalizer h
  have hHLN : HLb (resBeta (rhoH h)) Lb ≤ Subgroup.normalizer (V₁ : Set G) :=
    (HLb_le Lb).trans h.H_normalizes_V₁
  have hcomm : ⁅conjClosure Vp H, HLb (resBeta (rhoH h)) Lb⁆ ≤ Subgroup.normalizer (V₁ : Set G) :=
    (S145.commutator_le_of_le_normalizer ((HLb_le Lb).trans hHU)).trans hUN
  rw [tildeOf_sup_self hcomm]
  have e0 : tildeOf V₁ ⁅conjClosure Vp H, HLb (resBeta (rhoH h)) Lb⁆ =
      ⁅tildeOf V₁ (conjClosure Vp H), tildeOf V₁ (HLb (resBeta (rhoH h)) Lb)⁆ :=
    Gap6.secImg_commutator hUN hHLN
  rw [e0]
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro m hm x hx
    obtain ⟨xN, hxN, rfl⟩ := mem_secImg.1 hx
    have hxH : (xN : G) ∈ H := HLb_le _ hxN
    have hhL : resBeta (rhoH h) ⟨xN, hxH⟩ ∈ Lb := (mem_HLb_iff hxH).1 hxN
    obtain ⟨a, ha⟩ := rho_mul_inv_eq h hsplit ⟨xN, hxH⟩ (IntMod.mk h.isElemAbelian_tilde ⟨m, hm⟩)
    have hmemc : (resBeta (rhoH h) ⟨xN, hxH⟩ a * a⁻¹ : ↥(kOf (rhoH h))) ∈ commV Lb :=
      Subgroup.subset_closure ⟨resBeta (rhoH h) ⟨xN, hxH⟩, hhL, a, rfl⟩
    have hval : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ xN * m *
        (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ xN)⁻¹ * m⁻¹ =
        valK h (resBeta (rhoH h) ⟨xN, hxH⟩ a * a⁻¹) := by
      have h2 := congrArg (valW h) ha
      rw [map_mul, map_inv] at h2
      have e2 := rhoH_val h ⟨xN, hxH⟩ (IntMod.mk h.isElemAbelian_tilde ⟨m, hm⟩)
      have e3 : (Subgroup.inclusion h.H_normalizes_V₁ ⟨xN, hxH⟩) = xN := Subtype.ext rfl
      rw [e3] at e2
      exact (by rw [← e2] at *; exact h2 : _)
    have e : ⁅m, secMk (Subgroup.normalizer (V₁ : Set G)) V₁ xN⁆ =
        (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ xN * m *
          (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ xN)⁻¹ * m⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, hval, ← map_inv]
    exact ⟨_, (commV Lb).inv_mem hmemc, rfl⟩
  · rintro y ⟨k, hk, rfl⟩
    induction hk using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨l, hl, v, rfl⟩ := hw
      obtain ⟨hh, hhl⟩ := hLb hl
      subst hhl
      have hhmem : (hh : G) ∈ HLb (resBeta (rhoH h)) Lb := mem_HLb_of_mem hl
      have hx : secMk (Subgroup.normalizer (V₁ : Set G)) V₁
          (Subgroup.inclusion h.H_normalizes_V₁ hh) ∈ tildeOf V₁ (HLb (resBeta (rhoH h)) Lb) :=
        secMk_mem_secImg hhmem
      have hv : valK h v ∈ tildeOf V₁ (conjClosure Vp H) := (v : UMod h).val_mem
      have hcm := Subgroup.commutator_mem_commutator hx hv
      rw [Subgroup.commutator_comm] at hcm
      rw [valK_comm_gen h hh v]
      convert hcm using 1
    | one => simp
    | mul a b _ _ iha ihb =>
      rw [map_mul]
      exact Subgroup.mul_mem _ iha ihb
    | inv a _ iha =>
      rw [map_inv]
      exact Subgroup.inv_mem _ iha

end Dict

end CFSG.Quasithin
