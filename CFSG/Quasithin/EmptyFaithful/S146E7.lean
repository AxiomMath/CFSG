module

public import CFSG.Quasithin.EmptyFaithful.S146E6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section Decomp

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s u : G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem FCtx.cComp_eq (c : FCtx T M K U₁ U₂ s u) {L : Subgroup G} (hL : L ∈ cComp (mcOf T)) :
    L = K := by
  have h1 : L ≤ perfectCore (mcOf T) := by
    have := perfectCore_mono (le_of_mem_cComp hL)
    rwa [perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hL)] at this
  exact eq_of_le_cComp c.hKc hL (c.hKeq ▸ h1)

theorem FCtx.exists_decomp (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {x : G}
    (hx : x ∈ uOfL22 T M) : ∃ y ∈ U₁, ∃ r ∈ uxOf T M U₂, x = y * r := by
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) :=
    S.conjClosure_le_normalizer_Z S.isHTM_mcOf
  have h3 := c.hc23.2.2.1
  have hle1 : (⨆ K' ∈ cComp (mcOf T), tildeOf Zz ⁅uOfL22 T M, K'⁆) ≤ tildeOf Zz (U₁ ⊔ U₂) := by
    refine iSup₂_le fun K' hK' => ?_
    rw [c.cComp_eq hK']
    refine secImg_mono ?_
    calc ⁅uOfL22 T M, K⁆ ≤ ⁅uOfL22 T M, K⁆ ⊔ Zz := le_sup_left
      _ = U₁ ⊔ U₂ := c.hsup
  have hU12 : U₁ ⊔ U₂ ≤ Subgroup.normalizer (Zz : Set G) := (sup_le c.hU₁U c.hU₂U).trans hUN
  have hcuN : cuOf T M ≤ Subgroup.normalizer (Zz : Set G) := (cuOf_le T M).trans hUN
  have h4 : tildeOf Zz (uOfL22 T M) ≤ tildeOf Zz ((U₁ ⊔ U₂) ⊔ cuOf T M) := by
    rw [tildeOf_sup hU12 hcuN, h3]
    exact sup_le_sup_right hle1 _
  have hxN : x ∈ Subgroup.normalizer (Zz : Set G) := hUN hx
  have hZ12 : Zz ≤ (U₁ ⊔ U₂) ⊔ cuOf T M := c.hSec.le.trans (le_sup_left.trans le_sup_left)
  have h5 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨x, hxN⟩ ∈
      tildeOf Zz ((U₁ ⊔ U₂) ⊔ cuOf T M) := h4 (secMk_mem_secImg (x := ⟨x, hxN⟩) hx)
  have h6 : x ∈ (U₁ ⊔ U₂) ⊔ cuOf T M := (secMk_mem_secImg_iff (x := ⟨x, hxN⟩) hZ12).mp h5
  have hcomm12 : ∀ a ∈ U₁ ⊔ U₂, ∀ b ∈ cuOf T M, a * b = b * a := fun a ha b hb =>
    S.comm_of_mem_conjClosure (sup_le c.hU₁U c.hU₂U ha) (cuOf_le T M hb)
  have hN12 : U₁ ⊔ U₂ ≤ Subgroup.normalizer ((cuOf T M : Subgroup G) : Set G) :=
    le_normalizer_of_forall_commute hcomm12
  have h7 : x ∈ (((U₁ ⊔ U₂) ⊔ cuOf T M : Subgroup G) : Set G) := h6
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN12] at h7
  obtain ⟨a, ha, d, hd, rfl⟩ := h7
  have hN₁₂ : U₁ ≤ Subgroup.normalizer (U₂ : Set G) :=
    le_normalizer_of_forall_commute fun x hx y hy =>
      S.comm_of_mem_conjClosure (c.hU₁U hx) (c.hU₂U hy)
  have ha' : a ∈ ((U₁ ⊔ U₂ : Subgroup G) : Set G) := ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN₁₂] at ha'
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := ha'
  refine ⟨y₁, hy₁, y₂ * d, ?_, by group⟩
  exact (uxOf T M U₂).mul_mem (Subgroup.mem_sup_left hy₂) (Subgroup.mem_sup_right hd)

theorem FCtx.uOfL22_le_uxOf_of_mem (S : Setting146 G T M) (c : FCtx T M K U₁ U₂ s u) {v : G}
    (hv : v ∈ VZ T M) (hvZ : v ∉ Zz) (hvX : v ∈ uxOf T M U₂) :
    uOfL22 T M ≤ uxOf T M U₂ := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hG.1.1
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hVcard : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hZcard : Nat.card Zz = 2 := S.card_Z
  have hZV : Zz ≤ VZ T M := le_conjClosure _ _
  have hZX : Zz ≤ uxOf T M U₂ := c.hZU₂.trans le_sup_left
  have hKH : K ≤ mcOf T := le_of_mem_cComp c.hKc
  have hPN : T ≤ Subgroup.normalizer (K : Set G) := fun t ht => c.hKn (hTH ht)
  have hcent : ∀ h ∈ mcOf T, ∀ z ∈ Zz, h * z * h⁻¹ = z := fun h hh z hz => by
    have := S146T.comm_Z hh hz
    calc h * z * h⁻¹ = (h * z) * h⁻¹ := rfl
      _ = (z * h) * h⁻¹ := by rw [← this]
      _ = z := by group
  refine conjClosure_le fun h hh w hw => ?_
  have hh' : h ∈ ((K ⊔ T : Subgroup G) : Set G) := c.hHKT ▸ hh
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hPN] at hh'
  obtain ⟨k, hk, t, ht, rfl⟩ := hh'
  by_cases hwZ : w ∈ Zz
  · have : k * t * w * (k * t)⁻¹ = w := by
      have e : k * t * w * (k * t)⁻¹ = k * (t * w * t⁻¹) * k⁻¹ := by group
      rw [e, hcent t (hTH ht) w hwZ, hcent k (hKH hk) w hwZ]
    rw [this]
    exact hZX hwZ
  · have hz : v⁻¹ * w ∈ Zz := inv_mul_mem_of_card_four hZV hVcard hZcard hv hw hvZ hwZ
    have hwv : w = v * (v⁻¹ * w) := by group
    set z := v⁻¹ * w with hzdef
    have hz₁ : t * v * t⁻¹ * v⁻¹ ∈ Zz := S.commutator_VZ_mem (hTM ht) (hTH ht) hv
    set z₁ := t * v * t⁻¹ * v⁻¹ with hz₁def
    have e1 : t * v * t⁻¹ = z₁ * v := by rw [hz₁def]; group
    have e2 : k * t * w * (k * t)⁻¹ = (k * z₁ * k⁻¹) * (k * v * k⁻¹) * (k * z * k⁻¹) := by
      calc k * t * w * (k * t)⁻¹ = k * ((t * v * t⁻¹) * (t * z * t⁻¹)) * k⁻¹ := by
            rw [hwv]; group
        _ = k * ((z₁ * v) * (t * z * t⁻¹)) * k⁻¹ := by rw [e1]
        _ = (k * z₁ * k⁻¹) * (k * v * k⁻¹) * (k * (t * z * t⁻¹) * k⁻¹) := by group
        _ = (k * z₁ * k⁻¹) * (k * v * k⁻¹) * (k * z * k⁻¹) := by
            rw [hcent t (hTH ht) z hz]
    rw [e2, hcent k (hKH hk) z₁ hz₁, hcent k (hKH hk) z hz]
    have hkv : k * v * k⁻¹ ∈ uxOf T M U₂ := (Subgroup.mem_normalizer_iff.mp
      (c.le_normalizer_uxOf S hk) v).mp hvX
    exact (uxOf T M U₂).mul_mem ((uxOf T M U₂).mul_mem (hZX hz₁) hkv) (hZX hz)

end Decomp

end CFSG.Quasithin
