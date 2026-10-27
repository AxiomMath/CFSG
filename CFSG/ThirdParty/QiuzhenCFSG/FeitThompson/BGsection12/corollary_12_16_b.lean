module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_16_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-!
# corollary_12_16_b
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_card_ambientDerived_eq_derived_local (H : Subgroup G) :
    Nat.card (ambientDerivedSubgroup H) = Nat.card (derivedSubgroup H) := by
  let e : derivedSubgroup H ≃* ambientDerivedSubgroup H :=
    Subgroup.equivMapOfInjective (f := H.subtype) (derivedSubgroup H)
      H.subtype_injective
  exact (Nat.card_congr e.toEquiv).symm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_prime_mem_derivedSubgroup_of_mem_ambientDerived_local
    {H : Subgroup G} {p : Nat.Primes}
    (hp : p ∈ subgroupPrimeSet (ambientDerivedSubgroup H)) :
    p ∈ subgroupPrimeSet (derivedSubgroup H) := by
  simpa [subgroupPrimeSet, section12_card_ambientDerived_eq_derived_local (G := G) H] using hp

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_derived_card_conjBy_local
    (H : Subgroup G) (g : G) :
    Nat.card (derivedSubgroup (H.conjBy g)) = Nat.card (derivedSubgroup H) := by
  let e : H ≃* H.conjBy g := (MulAut.conj g).subgroupMap H
  have hmap :
      (derivedSubgroup H).map e.toMonoidHom = derivedSubgroup (H.conjBy g) := by
    change (derivedSeries H 1).map e.toMonoidHom = derivedSeries (H.conjBy g) 1
    exact map_derivedSeries_eq (f := e.toMonoidHom) e.surjective 1
  calc
    Nat.card (derivedSubgroup (H.conjBy g)) =
        Nat.card ((derivedSubgroup H).map e.toMonoidHom) := by
          rw [← hmap]
    _ = Nat.card (derivedSubgroup H) :=
      Subgroup.card_map_of_injective e.injective

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_ambientDerived_card_conjBy_local
    (H : Subgroup G) (g : G) :
    Nat.card (ambientDerivedSubgroup (H.conjBy g)) =
      Nat.card (ambientDerivedSubgroup H) := by
  calc
    Nat.card (ambientDerivedSubgroup (H.conjBy g)) =
        Nat.card (derivedSubgroup (H.conjBy g)) :=
      section12_card_ambientDerived_eq_derived_local (G := G) (H.conjBy g)
    _ = Nat.card (derivedSubgroup H) :=
      section12_derived_card_conjBy_local (G := G) H g
    _ = Nat.card (ambientDerivedSubgroup H) :=
      (section12_card_ambientDerived_eq_derived_local (G := G) H).symm

omit [IsMinCE G] in
private theorem CFSG.section12_tau1_not_mem_ambientDerived_of_le
    {M U : Subgroup G} {p : Nat.Primes}
    (hUM : U ≤ M) (hpτ1 : p ∈ section12Tau1Primes M) :
    p ∉ subgroupPrimeSet (ambientDerivedSubgroup U) := by
  intro hpUder
  have hpMambient : p ∈ subgroupPrimeSet (ambientDerivedSubgroup M) :=
    section8_subgroupPrimeSet_mono
      (section12_ambientDerivedSubgroup_mono (G := G) hUM) hpUder
  have hpMder : p ∈ subgroupPrimeSet (derivedSubgroup M) :=
    section12_prime_mem_derivedSubgroup_of_mem_ambientDerived_local
      (G := G) (H := M) hpMambient
  exact hpτ1.2.1 hpMder

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_derived_le_sup_commutator_local
    {K U : Subgroup G} [K.Normal] (hKU : K ⊔ U = ⊤) :
    derivedSubgroup G ≤ K ⊔ ⁅U, U⁆ := by
  change ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ K ⊔ ⁅U, U⁆
  rw [Subgroup.commutator_le]
  intro p hp q hq
  have hp_sup : p ∈ K ⊔ U := by simp [hKU]
  rcases (Subgroup.mem_sup_of_normal_left (s := K) (t := U) (x := p)).1 hp_sup with
    ⟨k₁, hk₁K, u₁, hu₁U, hk₁u₁⟩
  have hq_sup : q ∈ K ⊔ U := by simp [hKU]
  rcases (Subgroup.mem_sup_of_normal_left (s := K) (t := U) (x := q)).1 hq_sup with
    ⟨k₂, hk₂K, u₂, hu₂U, hk₂u₂⟩
  let c : G := ⁅u₁, u₂⁆
  have hcUU : c ∈ ⁅U, U⁆ :=
    by
      exact Subgroup.commutator_mem_commutator (H₁ := U) (H₂ := U) hu₁U hu₂U
  have hk₁eq : (((k₁ * u₁ : G) : G) : G ⧸ K) = (u₁ : G ⧸ K) := by
    rw [QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv, mul_assoc] using hk₁K
  have hk₂eq : (((k₂ * u₂ : G) : G) : G ⧸ K) = (u₂ : G ⧸ K) := by
    rw [QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv, mul_assoc] using hk₂K
  have hmap_eq : QuotientGroup.mk' K ⁅p, q⁆ = QuotientGroup.mk' K c := by
    calc
      QuotientGroup.mk' K ⁅p, q⁆
          = ⁅((p : G) : G ⧸ K), ((q : G) : G ⧸ K)⁆ := by
              exact
                (map_commutatorElement (f := QuotientGroup.mk' K) (g₁ := p) (g₂ := q))
      _ = ⁅(((k₁ * u₁ : G) : G) : G ⧸ K), (((k₂ * u₂ : G) : G) : G ⧸ K)⁆ := by
            rw [← hk₁u₁, ← hk₂u₂]
      _ = ⁅(u₁ : G ⧸ K), (u₂ : G ⧸ K)⁆ := by rw [hk₁eq, hk₂eq]
      _ = QuotientGroup.mk' K c := by
            exact
              (map_commutatorElement (f := QuotientGroup.mk' K) (g₁ := u₁) (g₂ := u₂)).symm
  let k₀ : G := ⁅p, q⁆ * c⁻¹
  have hk₀K : k₀ ∈ K := by
    apply (QuotientGroup.eq_one_iff (N := K) (x := k₀)).mp
    calc
      QuotientGroup.mk' K k₀ = QuotientGroup.mk' K ⁅p, q⁆ * (QuotientGroup.mk' K c)⁻¹ := by
        simp only [k₀, map_mul, map_inv]
      _ = QuotientGroup.mk' K c * (QuotientGroup.mk' K c)⁻¹ := by rw [hmap_eq]
      _ = 1 := by simp
  have hrepr : ⁅p, q⁆ = k₀ * c := by
    dsimp [k₀]
    simp [mul_assoc]
  rw [hrepr]
  exact (K ⊔ ⁅U, U⁆).mul_mem (Subgroup.mem_sup_left hk₀K) (Subgroup.mem_sup_right hcUU)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_isPiSubgroup_sup_of_normal_right_local
    {π : Set Nat.Primes} {H K : Subgroup G}
    (hH : IsPiSubgroup (G := G) π H) (hK : IsPiSubgroup (G := G) π K)
    [K.Normal] :
    IsPiSubgroup (G := G) π (H ⊔ K) := by
  intro p hpSup
  have hmul : (↑(H ⊔ K) : Set G) = (H : Set G) * (K : Set G) := by
    simpa using (Subgroup.mul_normal H K)
  have hcard_sup_set :
      Nat.card (↑(H ⊔ K) : Set G) =
        Nat.card ((H : Set G) * (K : Set G) : Set G) :=
    Nat.card_congr (Set.equivOfEq hmul)
  have hcard_sup :
      Nat.card (↥(H ⊔ K)) = Nat.card ((H : Set G) * (K : Set G) : Set G) := by
    simpa using hcard_sup_set
  have hcard_mul :
      Nat.card ((H : Set G) * (K : Set G) : Set G) =
        Nat.card K * Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) := by
    simpa using
      (Subgroup.card_mul_eq_card_subgroup_mul_card_quotient (s := K) (t := (H : Set G)))
  have hset_image :
      ((H : Set G).image (↑) : Set (G ⧸ K)) =
        (H.map (QuotientGroup.mk' K) : Set (G ⧸ K)) := by
    simp [Subgroup.coe_map]
  have hcard_image_set :
      Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) =
        Nat.card (H.map (QuotientGroup.mk' K) : Set (G ⧸ K)) :=
    Nat.card_congr (Set.equivOfEq hset_image)
  have hcard_image_subgroup :
      Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) =
        Nat.card (H.map (QuotientGroup.mk' K)) := by
    exact hcard_image_set
  have hp_mul :
      p.val ∣ Nat.card K * Nat.card ((H : Set G).image (↑) : Set (G ⧸ K)) := by
    rw [← hcard_mul, ← hcard_sup]
    exact hpSup
  rcases p.2.dvd_mul.mp hp_mul with hpK | hpImg
  · exact hK p hpK
  · have hpMap : p.val ∣ Nat.card (H.map (QuotientGroup.mk' K)) := by
      rwa [hcard_image_subgroup] at hpImg
    exact hH p (hpMap.trans (Subgroup.card_map_dvd (H := H) (QuotientGroup.mk' K)))

omit [IsMinCE G] in
private theorem CFSG.section12_not_mem_ambientDerived_of_product_pprime
    {H K U : Subgroup G} {p : Nat.Primes}
    (hKH : K ≤ H) (hUH : U ≤ H)
    [hKnorm : (K.subgroupOf H).Normal]
    (hKU : K.subgroupOf H ⊔ U.subgroupOf H = ⊤)
    (hpK : p ∉ subgroupPrimeSet K)
    (hpUder : p ∉ subgroupPrimeSet (ambientDerivedSubgroup U)) :
    p ∉ subgroupPrimeSet (ambientDerivedSubgroup H) := by
  classical
  intro hpHder
  let Usub : Subgroup H := U.subgroupOf H
  let Ksub : Subgroup H := K.subgroupOf H
  have hpHder_local : p ∈ subgroupPrimeSet (derivedSubgroup H) :=
    section12_prime_mem_derivedSubgroup_of_mem_ambientDerived_local
      (G := G) (H := H) hpHder
  have hD_le : derivedSubgroup H ≤ Ksub ⊔ ⁅Usub, Usub⁆ := by
    simpa [Ksub, Usub] using
      (section12_derived_le_sup_commutator_local
        (G := H) (K := K.subgroupOf H) (U := U.subgroupOf H) hKU)
  have hpSup : p ∈ subgroupPrimeSet (Ksub ⊔ ⁅Usub, Usub⁆) :=
    section8_subgroupPrimeSet_mono (G := H) hD_le hpHder_local
  have hKπ : IsPiSubgroup (G := H) ({p}ᶜ : Set Nat.Primes) Ksub := by
    intro q hqK
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hqp
    subst q
    have hpKsub : p ∈ subgroupPrimeSet K := by
      simpa [Ksub, subgroupPrimeSet, section12_card_subgroupOf_eq hKH] using hqK
    exact hpK hpKsub
  have hcommπ : IsPiSubgroup (G := H) ({p}ᶜ : Set Nat.Primes) ⁅Usub, Usub⁆ := by
    intro q hqComm
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hqp
    subst q
    have hcard_map :
        Nat.card ((⁅Usub, Usub⁆).map H.subtype) =
          Nat.card (↥(⁅Usub, Usub⁆ : Subgroup H)) :=
      Subgroup.card_map_of_injective
        (K := ⁅Usub, Usub⁆) (f := H.subtype) H.subtype_injective
    have hpCommMap : p ∈ subgroupPrimeSet ((⁅Usub, Usub⁆).map H.subtype) := by
      change p.val ∣ Nat.card (↥((⁅Usub, Usub⁆).map H.subtype))
      rw [hcard_map]
      exact hqComm
    have hmap_eq :
        (⁅Usub, Usub⁆).map H.subtype = ambientDerivedSubgroup U := by
      calc
        (⁅Usub, Usub⁆).map H.subtype = ⁅U, U⁆ := by
          simpa [Usub] using
            (commutator_subgroupOf_map_eq (S := H) (H := U) (R := U) hUH hUH)
        _ = ambientDerivedSubgroup U := by
          rw [section12_ambientDerivedSubgroup_eq_commutator]
    exact hpUder (by simpa [hmap_eq] using hpCommMap)
  have hsupπ :
      IsPiSubgroup (G := H) ({p}ᶜ : Set Nat.Primes) (⁅Usub, Usub⁆ ⊔ Ksub) :=
    section12_isPiSubgroup_sup_of_normal_right_local hcommπ hKπ
  have hpSup' : p ∈ subgroupPrimeSet (⁅Usub, Usub⁆ ⊔ Ksub) := by
    simpa [sup_comm] using hpSup
  exact (by simpa using hsupπ p hpSup')

private theorem CFSG.section12_corollary_12_16_derived_exclusion_of_le_msigma
    {M E E₁₂ E₁ E₂ E₃ Y H : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hYne : Y ≠ ⊥) (hYσ : IsPiSubgroup (section10SigmaPrimes M) Y)
    (hYleσ : Y ≤ section10Msigma M)
    (hpE : p ∈ subgroupPrimeSet E) (hpβ : p ∉ section12BetaPrimesOfGroup G)
    (hH : H ∈ section9MaximalSubgroupsContaining Y)
    (hpτ1 : p ∈ section12Tau1Primes M) :
    p ∉ subgroupPrimeSet (ambientDerivedSubgroup (subgroupNormalizerIn H (Y : Set G))) := by
  classical
  have hYne_top : Y ≠ ⊤ := by
    intro hYtop
    exact hH.1.1 (top_le_iff.mp (hYtop ▸ hH.2))
  rcases section12_exists_characteristic_pSubgroup_of_nontrivial
      (G := G) (Y := Y) hYne hYne_top with
    ⟨q, X, hXleY, hXne, hXq, hNormY_le_NormX⟩
  haveI : Fact q.val.Prime := ⟨q.property⟩
  have hXσ : X ≤ section10Msigma M := hXleY.trans hYleσ
  have hX_le_M : X ≤ M := hXσ.trans (section12_Msigma_le M)
  have hqY : q ∈ subgroupPrimeSet Y := by
    have hXnontrivial : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).2 hXne
    exact
      section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
        (A := Y) (B := X.subgroupOf Y)
        (hBp := hXq.of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := X) (K := Y) hXleY).symm)
        (hB_ne_bot := by
          intro hbot
          exact hXne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hXleY))
  have hqσ : q ∈ section10SigmaPrimes M := hYσ q hqY
  let N : Subgroup G := subgroupNormalizerIn H (Y : Set G)
  by_cases hNXM : Subgroup.normalizer (X : Set G) ≤ M
  · have hN_le_M : N ≤ M := by
      intro x hx
      exact hNXM (hNormY_le_NormX (mem_subgroupNormalizerIn.mp hx).1)
    exact section12_tau1_not_mem_ambientDerived_of_le
      (G := G) (M := M) (U := N) hN_le_M hpτ1
  · have hNXne_top : Subgroup.normalizer (X : Set G) ≠ ⊤ := by
      intro hNtop
      have hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
      letI : IsSimpleGroup G := IsMinCE.simple
      rcases hXnormal.eq_bot_or_eq_top with hXbot | hXtop
      · exact hXne hXbot
      · have hYtop : Y = ⊤ := by
          have htop_le_Y : (⊤ : Subgroup G) ≤ Y := by
            simpa [hXtop] using hXleY
          exact top_le_iff.mp htop_le_Y
        exact hYne_top hYtop
    obtain ⟨Mstar, hMstar⟩ :=
      section9_exists_maximalSubgroupsContaining_of_ne_top
        (G := G) (H := Subgroup.normalizer (X : Set G)) hNXne_top
    have hMstar_ne_M : Mstar ≠ M := by
      intro hEq
      exact hNXM (hEq ▸ hMstar.2)
    have hX_le_Mstar : X ≤ Mstar := Subgroup.le_normalizer.trans hMstar.2
    have hXinf : X ≤ M ⊓ Mstar := le_inf hX_le_M hX_le_Mstar
    obtain ⟨S, hXS⟩ :=
      IsPGroup.exists_le_sylow (G := (M ⊓ Mstar : Subgroup G)) (p := q.val)
        (hXq.of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := X) (K := M ⊓ Mstar) hXinf).symm)
    have hX_leS :
        X ≤ section10AmbientSylowSubgroup (M ⊓ Mstar) S := by
      intro x hx
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hXinf hx⟩, hXS (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
    have hnotconj_star : section12NotConjugate Mstar M :=
      proposition_12_15_a
        (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q) (S := S)
        hM hqσ hX_le_M hXne hXq hMstar hMstar_ne_M hX_leS
    have hN_le_Mstar : N ≤ Mstar := by
      intro x hx
      exact hMstar.2 (hNormY_le_NormX (mem_subgroupNormalizerIn.mp hx).1)
    let U : Subgroup G := M ⊓ Mstar
    have hU_le_M : U ≤ M := inf_le_left
    have hU_le_Mstar : U ≤ Mstar := inf_le_right
    have hpUder : p ∉ subgroupPrimeSet (ambientDerivedSubgroup U) :=
      section12_tau1_not_mem_ambientDerived_of_le
        (G := G) (M := M) (U := U) hU_le_M hpτ1
    have hpM : p ∈ subgroupPrimeSet M :=
      section8_subgroupPrimeSet_mono hE.1.2.1 hpE
    have hpMstar_der : p ∉ subgroupPrimeSet (ambientDerivedSubgroup Mstar) := by
      by_cases hqσstar : q ∈ section10SigmaPrimes Mstar
      · rcases proposition_12_15_d
            (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q) (S := S)
            hM hqσ hX_le_M hXne hXq hMstar hMstar_ne_M hX_leS hqσstar with
          ⟨hjoin, _hτ1, _hβα, _hβne⟩
        haveI : ((section10Mbeta Mstar).subgroupOf Mstar).Normal := by
          rw [section12Mbeta_subgroupOf_eq]
          infer_instance
        have hβHall :
            IsHallSubgroup (section10BetaPrimes Mstar)
              ((section10Mbeta Mstar).subgroupOf Mstar) := by
          simpa [section12Mbeta_subgroupOf_eq] using
            (lemma_10_8_a (G := G) hMstar.1).2
        have hpβstar : p ∉ section10BetaPrimes Mstar :=
          section12_not_beta_of_not_betaG (G := G) (M := Mstar) hpβ
        have hpK : p ∉ subgroupPrimeSet (section10Mbeta Mstar) := by
          intro hpK
          have hcard :
              Nat.card ((section10Mbeta Mstar).subgroupOf Mstar) =
                Nat.card (section10Mbeta Mstar) :=
            section12_card_subgroupOf_eq (section12_Mbeta_le Mstar)
          exact hpβstar
            (hβHall.p_in_pi_of_p_dvd_card p
              (by simpa [subgroupPrimeSet, hcard] using hpK))
        have hKU :
            (section10Mbeta Mstar).subgroupOf Mstar ⊔ U.subgroupOf Mstar = ⊤ := by
          have hsup : section10Mbeta Mstar ⊔ U = Mstar := by
            simpa [U, sup_comm] using hjoin.symm
          exact
            section12_local_sup_eq_top_of_sup_eq
              (G := G) (H := Mstar) (A := section10Mbeta Mstar) (B := U)
              (section12_Mbeta_le Mstar) hU_le_Mstar hsup
        exact
          section12_not_mem_ambientDerived_of_product_pprime
            (G := G) (H := Mstar) (K := section10Mbeta Mstar) (U := U)
            (section12_Mbeta_le Mstar) hU_le_Mstar hKU hpK hpUder
      · rcases proposition_12_15_e
            (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q) (S := S)
            hM hqσ hX_le_M hXne hXq hMstar hMstar_ne_M hX_leS hqσstar with
          ⟨_hqτ2star, hbeta_subset, hcomp⟩
        haveI : ((section10Msigma Mstar).subgroupOf Mstar).Normal := by
          rw [section12Msigma_subgroupOf_eq]
          infer_instance
        have hσHall :
            IsHallSubgroup (section10SigmaPrimes Mstar)
              ((section10Msigma Mstar).subgroupOf Mstar) := by
          simpa [section12Msigma_subgroupOf_eq] using
            (theorem_10_2_b (G := G) hMstar.1).2
        have hpσstar : p ∉ section10SigmaPrimes Mstar := by
          intro hpσ
          exact (section12_not_beta_of_not_betaG (G := G) (M := Mstar) hpβ)
            (hbeta_subset ⟨hpM, hpσ⟩)
        have hpK : p ∉ subgroupPrimeSet (section10Msigma Mstar) := by
          intro hpK
          have hcard :
              Nat.card ((section10Msigma Mstar).subgroupOf Mstar) =
                Nat.card (section10Msigma Mstar) :=
            section12_card_subgroupOf_eq (section12_Msigma_le Mstar)
          exact hpσstar
            (hσHall.p_in_pi_of_p_dvd_card p
              (by simpa [subgroupPrimeSet, hcard] using hpK))
        have hKU :
            (section10Msigma Mstar).subgroupOf Mstar ⊔ U.subgroupOf Mstar = ⊤ := by
          have hsup : section10Msigma Mstar ⊔ U = Mstar := by
            simpa [U] using hcomp.2.2.1.symm
          exact
            section12_local_sup_eq_top_of_sup_eq
              (G := G) (H := Mstar) (A := section10Msigma Mstar) (B := U)
              (section12_Msigma_le Mstar) hU_le_Mstar hsup
        exact
          section12_not_mem_ambientDerived_of_product_pprime
            (G := G) (H := Mstar) (K := section10Msigma Mstar) (U := U)
            (section12_Msigma_le Mstar) hU_le_Mstar hKU hpK hpUder
    intro hpNder
    exact hpMstar_der
      (section8_subgroupPrimeSet_mono
        (section12_ambientDerivedSubgroup_mono (G := G) hN_le_Mstar) hpNder)

private theorem CFSG.section12_corollary_12_16_derived_exclusion
    {M E E₁₂ E₁ E₂ E₃ Y H : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hYne : Y ≠ ⊥) (hYσ : IsPiSubgroup (section10SigmaPrimes M) Y)
    (hpE : p ∈ subgroupPrimeSet E) (hpβ : p ∉ section12BetaPrimesOfGroup G)
    (hH : H ∈ section9MaximalSubgroupsContaining Y)
    (hpτ1 : p ∈ section12Tau1Primes M) :
    p ∉ subgroupPrimeSet (ambientDerivedSubgroup (subgroupNormalizerIn H (Y : Set G))) := by
  classical
  have hYne_top : Y ≠ ⊤ := by
    intro hYtop
    exact hH.1.1 (top_le_iff.mp (hYtop ▸ hH.2))
  obtain ⟨g, hYg_leσ⟩ :=
    section12_corollary_12_16_exists_conjugating_element
      (G := G) (M := M) (Y := Y) hM hYne hYσ hYne_top
  let Yg : Subgroup G := Y.conjBy g
  let Hg : Subgroup G := H.conjBy g
  have hYg_ne : Yg ≠ ⊥ := by
    simpa [Yg] using section12_conjBy_ne_bot (G := G) hYne g
  have hYgσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Yg := by
    intro r hrYg
    have hrY : r ∈ subgroupPrimeSet Y := by
      simpa [Yg, subgroupPrimeSet, section12_card_conjBy_local (G := G) Y g] using hrYg
    exact hYσ r hrY
  have hHg_cont : Hg ∈ section9MaximalSubgroupsContaining Yg := by
    refine ⟨section12_maximal_conjBy_local (G := G) hH.1 g, ?_⟩
    change Y.map ((MulAut.conj g).toMonoidHom) ≤
      H.map ((MulAut.conj g).toMonoidHom)
    exact Subgroup.map_mono hH.2
  have hcore :
      p ∉ subgroupPrimeSet
        (ambientDerivedSubgroup (subgroupNormalizerIn Hg (Yg : Set G))) :=
    section12_corollary_12_16_derived_exclusion_of_le_msigma
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (Y := Yg) (H := Hg) (p := p)
      hM hE hYg_ne hYgσ hYg_leσ hpE hpβ hHg_cont hpτ1
  have hnorm_eq :
      subgroupNormalizerIn Hg (Yg : Set G) =
        (subgroupNormalizerIn H (Y : Set G)).conjBy g := by
    simpa [Yg, Hg] using section12_subgroupNormalizerIn_conjBy_eq_local
      (G := G) H Y g
  intro hpN
  have hpNconj :
      p ∈ subgroupPrimeSet
        (ambientDerivedSubgroup ((subgroupNormalizerIn H (Y : Set G)).conjBy g)) := by
    simpa [subgroupPrimeSet,
      section12_ambientDerived_card_conjBy_local
        (G := G) (subgroupNormalizerIn H (Y : Set G)) g] using hpN
  exact hcore (by simpa [hnorm_eq] using hpNconj)

/-- Corollary 12.16(b). -/
public theorem CFSG.corollary_12_16_b
    {M E E₁₂ E₁ E₂ E₃ Y H : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hYne : Y ≠ ⊥) (hYσ : IsPiSubgroup (section10SigmaPrimes M) Y)
    (hpE : p ∈ subgroupPrimeSet E) (hpβ : p ∉ section12BetaPrimesOfGroup G)
    (hH : H ∈ section9MaximalSubgroupsContaining Y)
    (hHnot : section12NotConjugate H M)
    (hpτ1 : p ∈ section12Tau1Primes M) :
    (∃ g : G, Y.conjBy g ≤ section10Msigma M) ∧
      p ∉ subgroupPrimeSet (ambientDerivedSubgroup (subgroupNormalizerIn H (Y : Set G))) := by
  exact ⟨
    (corollary_12_16_a
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (Y := Y) (H := H) (p := p)
      hM hE hYne hYσ hpE hpβ hH hHnot).1,
    section12_corollary_12_16_derived_exclusion
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (Y := Y) (H := H) (p := p)
      hM hE hYne hYσ hpE hpβ hH hpτ1⟩

end Section12
