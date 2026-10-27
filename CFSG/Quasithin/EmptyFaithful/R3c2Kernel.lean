module

public import CFSG.Quasithin.EmptyFaithful.R3c2Star
public import CFSG.Quasithin.EmptyFaithful.R3c2Theta

public section

namespace CFSG.Quasithin.R3c2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G}

omit [Finite G] in
theorem exists_starSurj (T I L : Subgroup G) (hLI : L ≤ I) :
    ∃ ψ : ↥L →* ↥(Star153 T I L), Function.Surjective ψ ∧
      ∀ x : ↥L, ψ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (UI153 T I : Set G) := by
  have hr := range_actL T I L hLI
  set a := actL T I L hLI with ha
  refine ⟨(MulEquiv.subgroupCongr hr).toMonoidHom.comp a.rangeRestrict, ?_, fun x => ?_⟩
  · exact (MulEquiv.subgroupCongr hr).surjective.comp a.rangeRestrict_surjective
  · rw [← actL_eq_one_iff T I L hLI x, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      ← (MulEquiv.subgroupCongr hr).map_one, (MulEquiv.subgroupCongr hr).injective.eq_iff,
      ← Subtype.coe_inj]
    simp
    exact Iff.rfl

omit [Finite G] in
theorem conj_mem_centralizer_UI (T I : Subgroup G) {g : G} (hg : g ∈ I) {h : G}
    (hh : h ∈ Subgroup.centralizer (UI153 T I : Set G)) :
    g * h * g⁻¹ ∈ Subgroup.centralizer (UI153 T I : Set G) := by
  have hUN := le_normalizer_UI153 T I
  rw [Subgroup.mem_centralizer_iff] at hh ⊢
  intro u hu
  have hu' : g⁻¹ * u * g ∈ (UI153 T I : Set G) := by
    have := Subgroup.mem_normalizer_iff.1 (hUN (I.inv_mem hg)) u
    simpa using this.1 hu
  have h1 := hh _ hu'
  calc u * (g * h * g⁻¹) = g * ((g⁻¹ * u * g) * h) * g⁻¹ := by group
    _ = g * (h * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
    _ = g * h * g⁻¹ * u := by group

theorem mem_pPrimeCore_of_mem_centralizer_UI (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (hF : Facts15325 T Mc M V₁ V₂ Yp I) (hLI : L ≤ I)
    (hnorm : I ≤ Subgroup.normalizer (L : Set G)) {x : G} (hxL : x ∈ L)
    (hxC : x ∈ Subgroup.centralizer (UI153 T I : Set G)) :
    (⟨x, hLI hxL⟩ : ↥I) ∈ CFSG.pPrimeCore 3 ↥I := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := L ⊓ Subgroup.centralizer (UI153 T I : Set G) with hN
  have hNI : N ≤ I := inf_le_left.trans hLI
  have hINN : I ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hL := Subgroup.mem_normalizer_iff.1 (hnorm hg) h
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hL.1 h1, conj_mem_centralizer_UI T I hg h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨hL.2 h1, ?_⟩
      have := conj_mem_centralizer_UI T I (I.inv_mem hg) h2
      simpa [mul_assoc] using this
  have hNn : (N.subgroupOf I).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNI).2 hINN
  have h3 : ¬ 3 ∣ Nat.card N := by
    intro h3
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 h3
    refine orderOf_ne_three_of_mem_centralizer_UI hI hF (hNI z.2) z.2.2 ?_
    rw [Subgroup.orderOf_coe z]
    exact hz
  have hcop : Nat.Coprime 3 (Nat.card (N.subgroupOf I)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNI).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  exact le_sSup (show N.subgroupOf I ∈ {K : Subgroup ↥I | K.Normal ∧ Nat.Coprime 3 (Nat.card K)} from
    ⟨hNn, hcop⟩) ((Subgroup.mem_subgroupOf).2 ⟨hxL, hxC⟩)

theorem exists_surjection_star_starImage (hI : IsHPlus Yp (Sgp153 T V₁) M I)
    (hF : Facts15325 T Mc M V₁ V₂ Yp I) (hLI : L ≤ I)
    (hnorm : I ≤ Subgroup.normalizer (L : Set G)) :
    ∃ π : ↥(Star153 T I L) →* ↥(starImage 3 (L.subgroupOf I)), Function.Surjective π := by
  obtain ⟨ψ, hψ, hψ1⟩ := exists_starSurj T I L hLI
  exact exists_surjection_starImage hLI ψ hψ fun x hx =>
    mem_pPrimeCore_of_mem_centralizer_UI hI hF hLI hnorm x.2 ((hψ1 x).1 hx)

end CFSG.Quasithin.R3c2
