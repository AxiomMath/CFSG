module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZ
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
import CFSG.GroupTheory.PrimeField.SteinbergBNPowerComparison

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem exists_layer_commute_of_involution (k : Sec7Core4 G) (h75 : Step75 k) {H : Subgroup G}
    (hH : Config k H)
    (hC2 : InvolutionCentralizerHasPElementOutside k.p
      (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))))
    {A : Subgroup G} (hAHM : A ≤ H ⊓ k.M) (hA : CFSG.Open.IsElemAbelian k.p A)
    (hAc : Nat.card A = k.p ^ 2) {t : G} (htHM : t ∈ H ⊓ k.M) (ht2 : orderOf t = 2)
    (htA : ∀ a ∈ A, a * t = t * a) (htK : t ∉ (CFSG.pPrimeCore k.p ↥H).map H.subtype) :
    ∃ j ∈ layerLift k.p H, j ∉ k.M ∧ j * t = t * j := by
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let π : ↥H →* (↥H ⧸ K₀) := QuotientGroup.mk' K₀
  let Nbar : Subgroup (↥H ⧸ K₀) := ((H ⊓ k.M).subgroupOf H).map π
  let Lbar : Subgroup (↥H ⧸ K₀) := CFSG.generalizedFitting (↥H ⧸ K₀)
  let J : Subgroup G := layerLift k.p H
  let KG : Subgroup G := K₀.map H.subtype
  let A' : Subgroup ↥H := A.subgroupOf H
  let Abar : Subgroup (↥H ⧸ K₀) := A'.map π
  let th : ↥H := ⟨t, htHM.1⟩
  let tbar : ↥H ⧸ K₀ := π th
  have hKcop : Nat.Coprime k.p (Nat.card K₀) := CFSG.pPrimeCore_coprime_card
  have hAH : A ≤ H := fun a ha => (hAHM ha).1
  have hAN : Abar ≤ Nbar := Subgroup.map_mono fun a ha =>
    Subgroup.mem_subgroupOf.mpr (hAHM (Subgroup.mem_subgroupOf.mp ha))
  have hAbar : CFSG.Open.IsElemAbelian k.p Abar := (hA.subgroupOf H).map π
  have hA'c : Nat.card A' = k.p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hAc]
  have hA'K : A' ⊓ π.ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    exact Subgroup.inf_eq_bot_of_coprime (by rw [hA'c]; exact (hKcop.pow_left 2))
  have hAbarc : Nat.card Abar = k.p ^ 2 := by
    have hinj : Function.Injective (π.comp A'.subtype) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have hmem : (a : ↥H) ∈ A' ⊓ π.ker := ⟨a.2, ha⟩
      rw [hA'K, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hr : Abar = (π.comp A'.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hr, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, hA'c]
  have htN : tbar ∈ Nbar := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr htHM)
  have ht1 : tbar ≠ 1 := by
    intro h
    have hker : th ∈ π.ker := MonoidHom.mem_ker.mpr h
    rw [QuotientGroup.ker_mk'] at hker
    exact htK (Subgroup.mem_map_of_mem H.subtype hker)
  have ht2bar : orderOf tbar = 2 := by
    have hdvd : orderOf tbar ∣ 2 := by
      have h1 : orderOf tbar ∣ orderOf th := orderOf_map_dvd π th
      rwa [← Subgroup.orderOf_coe th, ht2] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht1
    · exact h
  have htAbar : ∀ a ∈ Abar, a * tbar = tbar * a := by
    rintro _ ⟨a, ha, rfl⟩
    have h : a * th = th * a := Subtype.ext (htA _ (Subgroup.mem_subgroupOf.mp ha))
    rw [← map_mul, ← map_mul, h]
  obtain ⟨cc, hccL, hcct, hccp, hccN⟩ := hC2 Abar hAN hAbar hAbarc tbar htN ht2bar htAbar
  have hsimple := k.isSimpleGroup_generalizedFitting_quotient hH
  haveI : IsSimpleGroup ↥Lbar := hsimple.1
  have hLbarperf : ⁅Lbar, Lbar⁆ = Lbar :=
    Subgroup.isPerfect_iff.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hsimple.2.1).1.1
  have hmap : (J.subgroupOf H).map π = Lbar := map_layerLift_eq k.p H hLbarperf
  have hccL' : cc ∈ (J.subgroupOf H).map π := by rw [hmap]; exact hccL
  obtain ⟨h, hh, hπh⟩ := Subgroup.mem_map.mp hccL'
  have hhJ : (h : G) ∈ J := Subgroup.mem_subgroupOf.mp hh
  let ι : ↥J →* ↥H := Subgroup.inclusion (layerLift_le k.p H)
  let ψ : ↥J →* (↥H ⧸ K₀) := π.comp ι
  let xj : ↥J := ⟨(h : G), hhJ⟩
  have hψxj : ψ xj = cc := by
    have hι : ι xj = h := Subtype.ext rfl
    show π (ι xj) = cc
    rw [hι]
    exact hπh
  obtain ⟨n, e, hpn, hfix⟩ := CFSG.AGLEmbedding.exists_pPart_pow hp xj
  let jJ : ↥J := xj ^ n
  let j : G := (jJ : G)
  have hccorder : cc ^ orderOf xj = 1 := by
    have hdvd : orderOf cc ∣ orderOf xj := by
      have h := orderOf_map_dvd ψ xj
      rwa [hψxj] at h
    exact (orderOf_dvd_iff_pow_eq_one).mp hdvd
  have hccpow : ∃ m : ℕ, cc ^ k.p ^ m = 1 := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hccp
    have hcord : orderOf cc = k.p ^ m := by rw [← Nat.card_zpowers, hm]
    exact ⟨m, by rw [← hcord]; exact pow_orderOf_eq_one cc⟩
  have hψj : ψ jJ = cc := by
    calc ψ jJ = ψ (xj ^ n) := rfl
      _ = (ψ xj) ^ n := map_pow ψ xj n
      _ = cc ^ n := by rw [hψxj]
      _ = cc := hfix cc hccorder hccpow
  have hjJ : j ∈ J := jJ.2
  have hjH : j ∈ H := layerLift_le k.p H hjJ
  have hjpow : j ^ k.p ^ e = 1 := by
    have h := congrArg J.subtype hpn
    rw [map_pow, map_one] at h
    exact h
  have hπι : π (ι jJ) = cc := hψj
  have hπj : π (⟨j, hjH⟩ : ↥H) = cc := by
    rwa [show ι jJ = ⟨j, hjH⟩ from Subtype.ext rfl] at hπι
  have hjM : j ∉ k.M := by
    intro hjM
    have hmemN : π (⟨j, hjH⟩ : ↥H) ∈ Nbar :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ⟨hjH, hjM⟩)
    rw [hπj] at hmemN
    exact hccN hmemN
  have hcommut : j * t * j⁻¹ * t⁻¹ ∈ KG := by
    have hmemH : j * t * j⁻¹ * t⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem hjH htHM.1) (H.inv_mem hjH)) (H.inv_mem htHM.1)
    have hπcomm : π (⟨j * t * j⁻¹ * t⁻¹, hmemH⟩ : ↥H) = 1 := by
      have hmul : (⟨j * t * j⁻¹ * t⁻¹, hmemH⟩ : ↥H) =
          ι jJ * th * (ι jJ)⁻¹ * th⁻¹ := Subtype.ext rfl
      rw [hmul, map_mul, map_mul, map_inv, map_mul, map_inv, hπι, show π th = tbar from rfl,
        hcct]
      group
    exact Subgroup.mem_map_of_mem H.subtype
      (show (⟨j * t * j⁻¹ * t⁻¹, hmemH⟩ : ↥H) ∈ K₀ from by
        rw [← QuotientGroup.ker_mk' K₀]
        exact MonoidHom.mem_ker.mpr hπcomm)
  have hKGcop : Nat.Coprime k.p (Nat.card KG) := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hKcop
  have hcommJK : ⁅J, KG⁆ = ⊥ := h75 H hH
  have hcentJK : J ≤ Subgroup.centralizer (KG : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := J) (H₂ := KG)).mp hcommJK
  let c' : G := ⁅j, t⁆
  have hcK : c' ∈ KG := by
    rw [show c' = j * t * j⁻¹ * t⁻¹ by simp [c', commutatorElement_def]]
    exact hcommut
  have hcj : Commute c' j := Subgroup.mem_centralizer_iff.mp (hcentJK hjJ) c' hcK
  have hcpow : c' ^ (k.p ^ e) = 1 := by
    have h := CFSG.commutator_pow_eq_one_of_pow_eq_one_of_commute
      (x := j) (g := t) (p := k.p ^ e) (by simpa [c'] using hcj) hjpow
    simpa [c'] using h
  have hc1 : c' = 1 := CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime hcK
    (Nat.Coprime.pow_left e hKGcop).symm hcpow
  have hpc : j * t * j⁻¹ * t⁻¹ = 1 := by simpa [c', commutatorElement_def] using hc1
  refine ⟨j, hjJ, hjM, ?_⟩
  calc j * t = (j * t * j⁻¹ * t⁻¹) * (t * j) := by group
    _ = t * j := by rw [hpc, one_mul]

theorem false_of_involution (k : Sec7Core4 G) (h75 : Step75 k) {H : Subgroup G}
    (hH : Config k H)
    (hC2 : InvolutionCentralizerHasPElementOutside k.p
      (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))))
    {A : Subgroup G} (hAHM : A ≤ H ⊓ k.M) (hA : CFSG.Open.IsElemAbelian k.p A)
    (hAc : Nat.card A = k.p ^ 2) {t : G} (htHM : t ∈ H ⊓ k.M) (ht2 : orderOf t = 2)
    (htA : ∀ a ∈ A, a * t = t * a) : False := by
  have hp : k.p.Prime := k.prime
  have htK : t ∉ (CFSG.pPrimeCore k.p ↥H).map H.subtype := by
    intro htK
    have hodd := k.odd_card_pPrimeCore_of_not_le hH.not_le hH.two_le_pRank
    have hdvd : 2 ∣ Nat.card ((CFSG.pPrimeCore k.p ↥H).map H.subtype) := by
      rw [← ht2]
      exact Subgroup.orderOf_dvd_natCard _ htK
    rw [Subgroup.card_map_of_injective H.subtype_injective] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  obtain ⟨j, -, hjM, hjt⟩ :=
    k.exists_layer_commute_of_involution h75 hH hC2 hAHM hA hAc htHM ht2 htA htK
  have hD : Subgroup.zpowers t ≠ ⊥ := by
    intro h
    rw [Subgroup.zpowers_eq_bot] at h
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hD2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have hmem : ∀ g : G, g * t = t * g →
      g ∈ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
    exact hg
  have hCN := Subgroup.centralizer_le_normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)
  have hrank : 2 ≤ CFSG.Open.pRank k.p
      (Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) ⊓ k.M) :=
    CFSG.SectionRank.le_pRank hp.one_lt
      (le_inf (fun a ha => hCN (hmem a (htA a ha))) fun a ha => (hAHM ha).2) hA hAc
  exact hjM (k.huniq _ hD hD2 hrank (hCN (hmem j hjt)))

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
