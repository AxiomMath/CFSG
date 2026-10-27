module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem mem_centralizer_of_commute (k : Sec7Core4 G) (h75 : Step75 k) {H : Subgroup G}
    (hH : Config k H)
    (hF : AbelianPSubgroupLeFStar k.p
      (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))))
    {X : Subgroup G} (hXK : X ≤ (CFSG.pPrimeCore k.p ↥H).map H.subtype) {A : Subgroup G}
    (hAHM : A ≤ H ⊓ k.M) (hA : CFSG.Open.IsElemAbelian k.p A) (hAc : Nat.card A = k.p ^ 2)
    (hAX : A ≤ Subgroup.centralizer (X : Set G)) {u : G} (huHM : u ∈ H ⊓ k.M)
    (hup : IsPGroup k.p (Subgroup.zpowers u)) (huA : ∀ a ∈ A, a * u = u * a) :
    u ∈ Subgroup.centralizer (X : Set G) := by
  by_contra huC
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let π : ↥H →* (↥H ⧸ K₀) := QuotientGroup.mk' K₀
  let Nbar : Subgroup (↥H ⧸ K₀) := ((H ⊓ k.M).subgroupOf H).map π
  let J : Subgroup G := layerLift k.p H
  let KG : Subgroup G := K₀.map H.subtype
  have hKcop : Nat.Coprime k.p (Nat.card K₀) := CFSG.pPrimeCore_coprime_card
  let B : Subgroup G := A ⊔ Subgroup.zpowers u
  have huB : u ∈ B := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hBHM : B ≤ H ⊓ k.M := sup_le hAHM (Subgroup.zpowers_le.mpr huHM)
  have hBH : B ≤ H := fun b hb => (hBHM hb).1
  have huCA : u ∈ Subgroup.centralizer (A : Set G) := Subgroup.mem_centralizer_iff.mpr huA
  have huCu : u ∈ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((Commute.refl u).zpow_left n).eq
  have hBA : B ≤ Subgroup.centralizer (A : Set G) :=
    sup_le (Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1)
      (Subgroup.zpowers_le.mpr huCA)
  have hBu : B ≤ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr huCA))
      (Subgroup.zpowers_le.mpr huCu)
  have hBB : B ≤ Subgroup.centralizer (B : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.mp hBA) (Subgroup.le_centralizer_iff.mp hBu)
  have hBp : IsPGroup k.p B := hA.isPGroup.to_sup_of_normal_left' hup
    ((Subgroup.zpowers_le.mpr huCA).trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨b, hb⟩ := hBp.exists_card_eq
  have hb3 : 3 ≤ b := by
    have hdvd : k.p ^ 2 ∣ k.p ^ b := by
      rw [← hAc, ← hb]
      exact Subgroup.card_dvd_of_le le_sup_left
    have h2 : 2 ≤ b := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
    by_contra h
    have hb2 : b = 2 := by omega
    have hAB : A = B := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hb, hAc, hb2])
    exact huC (hAX (hAB ▸ huB))
  let B' : Subgroup ↥H := B.subgroupOf H
  let Bbar : Subgroup (↥H ⧸ K₀) := B'.map π
  have hB'c : Nat.card B' = k.p ^ b := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv, hb]
  have hB'K : B' ⊓ π.ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    exact Subgroup.inf_eq_bot_of_coprime (by rw [hB'c]; exact hKcop.pow_left b)
  have hBbarc : Nat.card Bbar = k.p ^ b := by
    have hinj : Function.Injective (π.comp B'.subtype) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have hmem : (a : ↥H) ∈ B' ⊓ π.ker := ⟨a.2, ha⟩
      rw [hB'K, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hr : Bbar = (π.comp B'.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hr, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, hB'c]
  have hBN : Bbar ≤ Nbar := Subgroup.map_mono fun a ha =>
    Subgroup.mem_subgroupOf.mpr (hBHM (Subgroup.mem_subgroupOf.mp ha))
  have hBbarab : ∀ a ∈ Bbar, ∀ c ∈ Bbar, a * c = c * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
    have h : a * c = c * a := Subtype.ext ((Subgroup.mem_centralizer_iff.mp
      (hBB (Subgroup.mem_subgroupOf.mp hc))) _ (Subgroup.mem_subgroupOf.mp ha))
    rw [← map_mul, ← map_mul, h]
  have hFB := hF Bbar hBN (IsPGroup.of_card hBbarc) hBbarab
    (by rw [hBbarc]; exact Nat.pow_le_pow_right hp.pos hb3)
  have hsimple := k.isSimpleGroup_generalizedFitting_quotient hH
  haveI : IsSimpleGroup ↥(CFSG.generalizedFitting (↥H ⧸ K₀)) := hsimple.1
  have hLbarperf : ⁅CFSG.generalizedFitting (↥H ⧸ K₀), CFSG.generalizedFitting (↥H ⧸ K₀)⁆ =
      CFSG.generalizedFitting (↥H ⧸ K₀) :=
    Subgroup.isPerfect_iff.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hsimple.2.1).1.1
  have hmap : (J.subgroupOf H).map π = CFSG.generalizedFitting (↥H ⧸ K₀) :=
    map_layerLift_eq k.p H hLbarperf
  let uH : ↥H := ⟨u, huHM.1⟩
  have huL : π uH ∈ (J.subgroupOf H).map π := by
    rw [hmap]
    exact hFB (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr huB))
  obtain ⟨h, hh, hπh⟩ := Subgroup.mem_map.mp huL
  have hk1 : π (h⁻¹ * uH) = 1 := by rw [map_mul, map_inv, hπh, inv_mul_cancel]
  have hk : h⁻¹ * uH ∈ K₀ := by
    rw [← QuotientGroup.ker_mk' K₀]
    exact MonoidHom.mem_ker.mpr hk1
  have hhJ : (h : G) ∈ J := Subgroup.mem_subgroupOf.mp hh
  have hkKG : (h : G)⁻¹ * u ∈ KG := Subgroup.mem_map_of_mem H.subtype hk
  have hcentJK : J ≤ Subgroup.centralizer (KG : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := J) (H₂ := KG)).mp (h75 H hH)
  have hhX : (h : G) ∈ Subgroup.centralizer (X : Set G) :=
    Subgroup.centralizer_le hXK (hcentJK hhJ)
  have hcomm : Commute (h : G) ((h : G)⁻¹ * u) :=
    (Subgroup.mem_centralizer_iff.mp (hcentJK hhJ) _ hkKG).symm
  have hum : u ^ orderOf ((h : G)⁻¹ * u) = (h : G) ^ orderOf ((h : G)⁻¹ * u) := by
    calc u ^ orderOf ((h : G)⁻¹ * u)
        = ((h : G) * ((h : G)⁻¹ * u)) ^ orderOf ((h : G)⁻¹ * u) := by group
      _ = (h : G) ^ orderOf ((h : G)⁻¹ * u) := by
        rw [hcomm.mul_pow, pow_orderOf_eq_one, mul_one]
  have hKGcop : Nat.Coprime k.p (Nat.card KG) := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hKcop
  obtain ⟨a, ha⟩ := hup.exists_card_eq
  have hcop : Nat.Coprime (orderOf ((h : G)⁻¹ * u)) (orderOf u) := by
    rw [← Nat.card_zpowers u, ha]
    exact (Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard KG hkKG)
      hKGcop.symm).pow_right a
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  apply huC
  rw [← ht, hum]
  exact pow_mem (pow_mem hhX _) t

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
