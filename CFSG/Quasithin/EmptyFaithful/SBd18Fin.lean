module

public import CFSG.Quasithin.EmptyFaithful.SBd18Nf
public import CFSG.Quasithin.EmptyFaithful.SBd18Cs
public import CFSG.Quasithin.EmptyFaithful.SBd18Z
public import CFSG.Quasithin.EmptyFaithful.SBd18V
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourConjugacy

public section

namespace CFSG.Quasithin.SBd18

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_conj_involutions {K : Type} [Field K] [CharP K 2] {x y : projectiveSL 3 K}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ p : projectiveSL 3 K, p * x * p⁻¹ = y := by
  obtain ⟨g₁, h₁⟩ := LinearFieldFour.exists_conj_eq_wP_one x hx2 hx1
  obtain ⟨g₂, h₂⟩ := LinearFieldFour.exists_conj_eq_wP_one y hy2 hy1
  refine ⟨(proj 3 K g₂)⁻¹ * proj 3 K g₁, ?_⟩
  calc (proj 3 K g₂)⁻¹ * proj 3 K g₁ * x * ((proj 3 K g₂)⁻¹ * proj 3 K g₁)⁻¹
      = (proj 3 K g₂)⁻¹ * (proj 3 K g₁ * x * (proj 3 K g₁)⁻¹) * proj 3 K g₂ := by group
    _ = (proj 3 K g₂)⁻¹ * (proj 3 K g₂ * y * (proj 3 K g₂)⁻¹) * proj 3 K g₂ := by rw [h₁, h₂]
    _ = y := by group

end CFSG.Quasithin.SBd18

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.exists_conj_into_V (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    {x : G} (hxL : x ∈ L) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ l ∈ L, l * x * l⁻¹ ∈ VZ T M ∧ l * x * l⁻¹ ≠ 1 := by
  classical
  obtain ⟨K, _, _, _, ρ, φ, Φ, hK4, hmod, hker, hφ, hΦ, hinn⟩ := r.exists_outer_action h113
  have D0 := r.ctx.hyp.decomp
  have hV₁ : V₁ = centerOf L := r.V₁_eq_center h113
  have hmemV₁ : ∀ y : ↥L, ρ y = 1 → (y : G) ∈ V₁ := by
    intro y hy
    rw [hV₁]
    have : y ∈ ρ.ker := hy
    rw [hker] at this
    exact SBd9.mem_centerOf_iff.mpr this
  by_cases hρx : ρ ⟨x, hxL⟩ = 1
  · refine ⟨1, L.one_mem, ?_, ?_⟩
    · rw [one_mul, inv_one, mul_one]
      exact D0.le₁ (hmemV₁ ⟨x, hxL⟩ hρx)
    · simpa using hx1
  · obtain ⟨v₂, hv₂, hv₂1⟩ : ∃ v₂ ∈ V₂, v₂ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : V₂ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
      have h4 := D0.card₂
      rw [this, Subgroup.card_bot] at h4
      omega
    have hv₂L : v₂ ∈ L := (r.V₂_le_Q hv₂).2
    have hρv₂ : ρ ⟨v₂, hv₂L⟩ ≠ 1 := by
      intro h
      have h1 : v₂ ∈ V₁ := hmemV₁ ⟨v₂, hv₂L⟩ h
      have : v₂ ∈ V₁ ⊓ V₂ := ⟨h1, hv₂⟩
      rw [D0.inf, Subgroup.mem_bot] at this
      exact hv₂1 this
    have hρx2 : ρ ⟨x, hxL⟩ * ρ ⟨x, hxL⟩ = 1 := by
      rw [← map_mul]
      have : (⟨x, hxL⟩ : ↥L) * ⟨x, hxL⟩ = 1 := Subtype.ext hx2
      rw [this, map_one]
    have hρv₂2 : ρ ⟨v₂, hv₂L⟩ * ρ ⟨v₂, hv₂L⟩ = 1 := by
      rw [← map_mul]
      have : (⟨v₂, hv₂L⟩ : ↥L) * ⟨v₂, hv₂L⟩ = 1 :=
        Subtype.ext (r.V_sq v₂ (D0.le₂ hv₂))
      rw [this, map_one]
    obtain ⟨p, hp⟩ := SBd18.exists_conj_involutions hρx2 hρv₂2 hρx hρv₂
    obtain ⟨l₀, rfl⟩ := hmod.surj p
    have hl : ρ (l₀ * ⟨x, hxL⟩ * l₀⁻¹) = ρ ⟨v₂, hv₂L⟩ := by
      rw [map_mul, map_mul, map_inv]
      exact hp
    have hw : ρ ((⟨v₂, hv₂L⟩ : ↥L)⁻¹ * (l₀ * ⟨x, hxL⟩ * l₀⁻¹)) = 1 := by
      rw [map_mul, map_inv, hl, inv_mul_cancel]
    have hwV₁ := hmemV₁ _ hw
    refine ⟨(l₀ : G), l₀.2, ?_, ?_⟩
    · have e : (l₀ : G) * x * (l₀ : G)⁻¹ = v₂ * (((⟨v₂, hv₂L⟩ : ↥L)⁻¹ * (l₀ * ⟨x, hxL⟩ * l₀⁻¹) : ↥L) : G) := by
        simp [mul_assoc]
      rw [e, ← D0.sup]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hv₂) (Subgroup.mem_sup_left hwV₁)
    · intro h1
      apply hx1
      have : x = (l₀ : G)⁻¹ * ((l₀ : G) * x * (l₀ : G)⁻¹) * (l₀ : G) := by group
      rw [this, h1]
      group

theorem RestHyp.noFusion_of_notconj_f (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    (hOut : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 → SBd18.OutFacts K)
    (hI : I = Subgroup.normalizer (V₁ : Set G))
    (hK1 : ∀ v ∈ V₁, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ I)
    (hTI : ∀ (g x : G), x ∈ V₁ → x ≠ 1 → g⁻¹ * x * g ∈ V₁ → g ∈ Subgroup.normalizer (V₁ : Set G))
    {τ f t₀ : G} (hτS : τ ∈ Sgp153 T V₁) (hfS : f ∈ Sgp153 T V₁) (hττ : τ * τ = 1)
    (hff : f * f = 1) (hτf : τ * f = f * τ) (hcent : ∀ v ∈ V₁, (τ * f) * v = v * (τ * f))
    (hmove : ∃ v ∈ V₁, τ * v ≠ v * τ) (hσL : τ * f ∉ L)
    (hcl : Subgroup.centralizer (V₁ : Set G) = L ⊔ Subgroup.zpowers (τ * f))
    (ht₀ : t₀ * τ * t₀⁻¹ = τ * f) (hf : ∀ g : G, g⁻¹ * τ * g ≠ f) :
    ∀ g : G, g⁻¹ * τ * g ∉ Sgp153 T V₁ ⊓ L ∧ f⁻¹ * (g⁻¹ * τ * g) ∉ Sgp153 T V₁ ⊓ L := by
  classical
  intro g
  have D0 := r.ctx.hyp.decomp
  have hNV := r.not_conj_V₁_of_swap h113 hOut hI hK1 hTI hτS hfS hττ hff hτf hcent hmove hσL hcl ht₀
  obtain ⟨z, hzV, hz1, hz2, hzT, hzcl⟩ := r.V_classes
  have hNz := r.not_conj_z h113 hOut hK1 hτS hfS hττ hff hτf hcent hmove hσL hzT hz1 hz2
  obtain ⟨x, hx⟩ : ∃ x : G, x = g⁻¹ * τ * g := ⟨_, rfl⟩
  have hx2 : x * x = 1 := by
    calc x * x = g⁻¹ * (τ * τ) * g := by rw [hx]; group
      _ = 1 := by rw [hττ]; group
  have hτ1 : τ ≠ 1 := by
    obtain ⟨v, hv, hne⟩ := hmove
    intro h
    exact hne (by rw [h]; simp)
  have hx1 : x ≠ 1 := by
    intro h
    apply hτ1
    calc τ = g * (g⁻¹ * τ * g) * g⁻¹ := by group
      _ = 1 := by rw [← hx, h]; group
  rw [← hx]
  constructor
  · intro hxQ
    have hxL : x ∈ L := hxQ.2
    obtain ⟨l, hlL, hlV, hl1⟩ := r.exists_conj_into_V h113 hxL hx2 hx1
    rcases hzcl _ hlV hl1 with ⟨m, hmM, hm⟩ | ⟨v, hvV, hv1, m, hmM, hm⟩
    · apply hNz (g * l⁻¹ * m⁻¹)
      calc (g * l⁻¹ * m⁻¹)⁻¹ * τ * (g * l⁻¹ * m⁻¹) = m * (l * (g⁻¹ * τ * g) * l⁻¹) * m⁻¹ := by
            group
        _ = m * (l * x * l⁻¹) * m⁻¹ := by rw [hx]
        _ = z := hm
    · apply hNV (g * l⁻¹ * m⁻¹)
      have e : (g * l⁻¹ * m⁻¹)⁻¹ * τ * (g * l⁻¹ * m⁻¹) = v := by
        calc (g * l⁻¹ * m⁻¹)⁻¹ * τ * (g * l⁻¹ * m⁻¹) = m * (l * (g⁻¹ * τ * g) * l⁻¹) * m⁻¹ := by
              group
          _ = m * (l * x * l⁻¹) * m⁻¹ := by rw [hx]
          _ = v := hm
      rw [e]
      exact hvV
  · intro hqQ
    have hq : f⁻¹ * x ∈ L := hqQ.2
    obtain ⟨l, hlL, hl⟩ := r.exists_conj_of_coset h113 hOut hτS hfS hττ hff hτf hcent hmove hσL hx2 hq
    apply hf (g * l)
    calc (g * l)⁻¹ * τ * (g * l) = l⁻¹ * (g⁻¹ * τ * g) * l := by group
      _ = l⁻¹ * x * l := by rw [hx]
      _ = l⁻¹ * (l * f * l⁻¹) * l := by rw [hl]
      _ = f := by group

end CFSG.Quasithin.SBd14
