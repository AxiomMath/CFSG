module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection13.corollary_13_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Data.Finset.NatDivisors
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Corollary 13 3 from BG Section 13 -/

section Section13

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
/-- Corollary 13.3(a): every nontrivial cyclic Sylow subgroup of `E`
acts in a prime manner on `M_σ`. -/
public theorem CFSG.corollary_13_3_a
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    ∀ p : Nat.Primes, ∀ P : Sylow p.val E,
      (P : Subgroup E) ≠ ⊥ → IsCyclic (P : Subgroup E) →
        section13ActsPrimeManner
          (section10AmbientSylowSubgroup E P) (section10Msigma M) := by
  classical
  intro p P hPne hPcyc
  let A : Subgroup G := section10AmbientSylowSubgroup E P
  have hA_le_E : A ≤ E := section13_ambient_sylow_le_base (G := G) E P
  have hE_le_M : E ≤ M := hE.1.2.1
  have hA_le_M : A ≤ M := hA_le_E.trans hE_le_M
  have hAp : IsPGroup p.val A := by
    change IsPGroup p.val ((P : Subgroup E).map E.subtype)
    exact IsPGroup.map (p := p.val) (H := (P : Subgroup E))
      P.isPGroup' E.subtype
  have hAcyc : IsCyclic A := by
    simpa [A] using section13_ambient_sylow_is_cyclic (G := G) P hPcyc
  have hpτ13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M :=
    section13_prime_mem_tau13_of_cyclic_sylow_E
      (G := G) hM hE P hPne hPcyc
  refine ⟨?_, ?_⟩
  · exact hA_le_M.trans section13_le_normalizer_msigma
  · intro X hX
    rcases (by simpa [section12PrimeOrderSubgroups, A] using hX) with ⟨hXA, hXcard⟩
    rcases hXcard with ⟨q, hXcard⟩
    have hXp : IsPGroup p.val X :=
      section13_isPGroup_of_le_pSubgroup (G := G) hAp hXA
    have hXne : X ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hXcard
    have hXM : X ≤ M := hXA.trans hA_le_M
    have hnormX_ne_top : Subgroup.normalizer (X : Set G) ≠ ⊤ :=
      section13_normalizer_ne_top_of_ne_bot_le_maximal hM hXM hXne
    rcases section9_exists_maximalSubgroupsContaining_of_ne_top
        (G := G) hnormX_ne_top with
      ⟨Mstar, hMstar⟩
    have hA_le_normX : A ≤ Subgroup.normalizer (X : Set G) :=
      section13_ambient_sylow_le_normalizer_of_le_cyclic
        (G := G) hXA hAcyc
    have hA_le_Mstar : A ≤ Mstar := hA_le_normX.trans hMstar.2
    have hA_le_inf : A ≤ M ⊓ Mstar := le_inf hA_le_M hA_le_Mstar
    have hA_cent :
        A ≤ Subgroup.centralizer (section10Msigma M ⊓ Mstar : Set G) :=
      corollary_13_2_a (G := G) hM hE hpτ13 hXp hXne hXM hMstar
        A hA_le_inf hAp
    intro y hy
    refine ⟨hy.1, ?_⟩
    have hyMstar : y ∈ Mstar :=
      hMstar.2 ((centralizer_le_normalizer X) hy.2)
    change y ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact ((Subgroup.mem_centralizer_iff.mp (hA_cent ha)) y ⟨hy.1, hyMstar⟩).symm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_ambientDerivedSubgroup_le_of_le
    {H K : Subgroup G} (hHK : H ≤ K) :
    ambientDerivedSubgroup H ≤ ambientDerivedSubgroup K := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  let f : H →* K := H.subtype.codRestrict K (fun h => hHK h.property)
  have hyK : f y ∈ derivedSubgroup K := by
    exact (map_derivedSeries_le_derivedSeries f 1) (Subgroup.mem_map_of_mem f hy)
  change ((y : H) : G) ∈ ambientDerivedSubgroup K
  exact Subgroup.mem_map_of_mem K.subtype hyK

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_prime_mem_derivedSubgroup_of_mem_ambientDerived
    {M : Subgroup G} {p : Nat.Primes}
    (hp : p ∈ subgroupPrimeSet (ambientDerivedSubgroup M)) :
    p ∈ subgroupPrimeSet (derivedSubgroup M) := by
  let e : derivedSubgroup M ≃* ambientDerivedSubgroup M :=
    Subgroup.equivMapOfInjective (f := M.subtype) (derivedSubgroup M) M.subtype_injective
  have hcard : Nat.card (ambientDerivedSubgroup M) = Nat.card (derivedSubgroup M) :=
    (Nat.card_congr e.toEquiv).symm
  simpa [subgroupPrimeSet, hcard] using hp

omit [IsMinCE G] in
private theorem CFSG.section13_isPiSubgroup_tau1_compl_of_le_ambientDerived
    {M X : Subgroup G}
    (hXD : X ≤ ambientDerivedSubgroup M) :
    IsPiSubgroup (G := G) (section12Tau1Primes M)ᶜ X := by
  intro p hpX
  rw [Set.mem_compl_iff]
  intro hpτ1
  have hpDambient : p ∈ subgroupPrimeSet (ambientDerivedSubgroup M) :=
    section8_subgroupPrimeSet_mono hXD (by simpa [subgroupPrimeSet] using hpX)
  have hpD : p ∈ subgroupPrimeSet (derivedSubgroup M) :=
    section13_prime_mem_derivedSubgroup_of_mem_ambientDerived
      (G := G) (M := M) hpDambient
  rcases (by simpa [section12Tau1Primes] using hpτ1) with
    ⟨_hp_not_sigma, hp_notD, _hrank⟩
  exact hp_notD hpD

omit [IsMinCE G] in
public theorem CFSG.section13_le_normalizer_of_le_cyclic_normal
    {E E₃ X : Subgroup G}
    (hXE₃ : X ≤ E₃) (hE₃cyc : IsCyclic E₃)
    (hE₃norm : section10NormalIn E₃ E) :
    E ≤ Subgroup.normalizer (X : Set G) := by
  classical
  haveI : IsCyclic E₃ := hE₃cyc
  have hXchar : (X.subgroupOf E₃).Characteristic :=
    section12_subgroup_characteristic_of_cyclic (X.subgroupOf E₃)
  haveI : (X.subgroupOf E₃).Characteristic := hXchar
  have hnormE₃_le_normX :
      Subgroup.normalizer (E₃ : Set G) ≤
        Subgroup.normalizer ((X.subgroupOf E₃).map E₃.subtype : Set G) :=
    section8_normalizer_map_subtype_le_of_characteristic
      (H := E₃) (K := X.subgroupOf E₃)
  have hXmap : (X.subgroupOf E₃).map E₃.subtype = X :=
    Subgroup.map_subgroupOf_eq_of_le hXE₃
  have hE_le_normE₃ : E ≤ Subgroup.normalizer (E₃ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE₃norm.1).1 hE₃norm.2
  simpa [hXmap] using hE_le_normE₃.trans hnormE₃_le_normX

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_tau3_of_prime_order_le_E3
    {M E E₃ X : Subgroup G} {q : Nat.Primes}
    (hE₃Hall : section12HallSubgroupIn (section12Tau3Primes M) E₃ E)
    (hXE₃ : X ≤ E₃) (hXcard : Nat.card X = q.val) :
    q ∈ section12Tau3Primes M := by
  rcases hE₃Hall with ⟨hE₃E, hHallE₃⟩
  have hqX : q.val ∣ Nat.card X := by rw [hXcard]
  have hqE₃ : q.val ∣ Nat.card E₃ :=
    hqX.trans (Subgroup.card_dvd_of_le hXE₃)
  have hcardE₃sub : Nat.card (E₃.subgroupOf E) = Nat.card E₃ :=
    natCard_subgroupOf_eq E₃ E hE₃E
  exact hHallE₃.p_in_pi_of_p_dvd_card q (by simpa [hcardE₃sub] using hqE₃)

/-- Corollary 13.3(b): `E₃` acts in a prime manner on `M_σ`. -/
public theorem CFSG.corollary_13_3_b
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    section13ActsPrimeManner E₃ (section10Msigma M) := by
  classical
  rcases hE with ⟨hcomp, hE₁₂, hE₁, hE₂, hE₃Hall⟩
  rcases hE₃Hall with ⟨hE₃E, hHallE₃⟩
  have hEdata : section12EData M E E₁₂ E₁ E₂ E₃ :=
    ⟨hcomp, hE₁₂, hE₁, hE₂, ⟨hE₃E, hHallE₃⟩⟩
  have hE_le_M : E ≤ M := hcomp.2.1
  have hE₃_le_M : E₃ ≤ M := hE₃E.trans hE_le_M
  have hE₃cyc : IsCyclic E₃ := (lemma_12_1_d hM hEdata).2
  have hE₃derived : E₃ ≤ ambientDerivedSubgroup E := (lemma_12_1_b hM hEdata).1
  have hE₃norm : section10NormalIn E₃ E := (lemma_12_1_b hM hEdata).2
  refine ⟨?_, ?_⟩
  · exact hE₃_le_M.trans section13_le_normalizer_msigma
  · intro X hX
    rcases (by simpa [section12PrimeOrderSubgroups] using hX) with ⟨hXE₃, hXcard⟩
    rcases hXcard with ⟨q, hXcard⟩
    have hXq : IsPGroup q.val X := by
      refine IsPGroup.of_card (p := q.val) (G := X) (n := 1) ?_
      simpa [pow_one] using hXcard
    have hXne : X ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hXcard
    have hXM : X ≤ M := hXE₃.trans hE₃_le_M
    have hqτ3 : q ∈ section12Tau3Primes M :=
      section13_tau3_of_prime_order_le_E3
        (G := G) (M := M) (E := E) (E₃ := E₃) (X := X) (q := q)
        ⟨hE₃E, hHallE₃⟩ hXE₃ hXcard
    have hnormX_ne_top : Subgroup.normalizer (X : Set G) ≠ ⊤ :=
      section13_normalizer_ne_top_of_ne_bot_le_maximal hM hXM hXne
    rcases section9_exists_maximalSubgroupsContaining_of_ne_top
        (G := G) hnormX_ne_top with
      ⟨Mstar, hMstar⟩
    have hE_le_normX : E ≤ Subgroup.normalizer (X : Set G) :=
      section13_le_normalizer_of_le_cyclic_normal
        (G := G) hXE₃ hE₃cyc hE₃norm
    have hE_le_Mstar : E ≤ Mstar := hE_le_normX.trans hMstar.2
    have hE₃_le_Mstar : E₃ ≤ Mstar := hE₃E.trans hE_le_Mstar
    have hE₃_le_inf : E₃ ≤ E ⊓ Mstar := le_inf hE₃E hE₃_le_Mstar
    have hE₃_le_derived_star : E₃ ≤ ambientDerivedSubgroup Mstar :=
      hE₃derived.trans (section13_ambientDerivedSubgroup_le_of_le hE_le_Mstar)
    have hE₃πc : IsPiSubgroup (G := G) (section12Tau1Primes Mstar)ᶜ E₃ :=
      section13_isPiSubgroup_tau1_compl_of_le_ambientDerived
        (G := G) (M := Mstar) (X := E₃) hE₃_le_derived_star
    have hE₃_cent :
        E₃ ≤ Subgroup.centralizer (section10Msigma M ⊓ Mstar : Set G) :=
      corollary_13_2_b (G := G) hM hEdata (Or.inr hqτ3)
        hXq hXne hXM hMstar E₃ hE₃_le_inf hE₃πc
    intro y hy
    refine ⟨hy.1, ?_⟩
    have hyMstar : y ∈ Mstar :=
      hMstar.2 ((centralizer_le_normalizer X) hy.2)
    change y ∈ Subgroup.centralizer (E₃ : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.mp (hE₃_cent he)) y ⟨hy.1, hyMstar⟩).symm

end Section13
