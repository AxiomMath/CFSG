module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Steps
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.SignalizerFunctorTheorem.Inheritance.Pullback

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7


variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem step74_of_pPrimeCore_eq_bot (k : Sec7Core4 G)
    (h1 : ∀ H : Subgroup G, Config k H →
      CFSG.pPrimeCore k.p
        ↥(((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) = ⊥) :
    Step74 k := by
  intro H hH
  classical
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 k.M
  let R : Subgroup G := Q ⊓ H
  let K : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  haveI : K.Normal := CFSG.pPrimeCore_normal
  let q : ↥H →* ↥H ⧸ K := QuotientGroup.mk' K
  let B : Subgroup ↥H := (H ⊓ k.M).subgroupOf H
  let A : Subgroup ↥H := R.subgroupOf H
  let Nbar : Subgroup (↥H ⧸ K) := B.map q
  let Rbar : Subgroup (↥H ⧸ K) := A.map q
  have hRleM : R ≤ k.M := by
    intro x hx
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 k.M hx.1
  have hRleH : R ≤ H := inf_le_right
  have hRleB : R ≤ H ⊓ k.M := le_inf hRleH hRleM
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 k.M
  have hR2 : IsPGroup 2 R := hQ2.to_le inf_le_left
  have hB0N : H ⊓ k.M ≤ Subgroup.normalizer (R : Set G) := by
    have hHn : H ≤ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer
    have hQn : k.M ≤ Subgroup.normalizer (Q : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 k.M
    have hle : H ⊓ k.M ≤
        Subgroup.normalizer (Q : Set G) ⊓ Subgroup.normalizer (H : Set G) :=
      le_inf (inf_le_right.trans hQn) (inf_le_left.trans hHn)
    simpa [R] using hle.trans (Subgroup.inf_normalizer_le_normalizer_inf (H := Q) (K := H))
  have hAB : A ≤ B := Subgroup.subgroupOf_mono H hRleB
  have hAnorm : (A.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAB]
    intro h b hh hk
    have hhR : (h : G) ∈ R := Subgroup.mem_subgroupOf.mp hh
    have hkB : (b : G) ∈ H ⊓ k.M := Subgroup.mem_subgroupOf.mp hk
    have hmem : (b : G) * (h : G) * (b : G)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hB0N hkB) (h : G)).mp hhR
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hmem)
  have hRbar_le_Nbar : Rbar ≤ Nbar :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H hRleB)
  haveI : (A.subgroupOf B).Normal := hAnorm
  have hRbarSubNorm : (Rbar.subgroupOf Nbar).Normal :=
    CFSG.SignalizerFunctorTheorem.normal_map_subgroupOf q hAB
  have hR2sub : IsPGroup 2 ↥(R.subgroupOf H) :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRleH).symm
  have hRbar2 : IsPGroup 2 Rbar := hR2sub.map q
  obtain ⟨n, hn⟩ := hRbar2.exists_card_eq
  have hpne2 : k.p ≠ 2 := k.odd
  have hcopRbar : Nat.Coprime k.p (Nat.card Rbar) := by
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).mpr hpne2)
  have hcardSub : Nat.card (Rbar.subgroupOf Nbar) = Nat.card Rbar :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRbar_le_Nbar).toEquiv
  have hcop : Nat.Coprime k.p (Nat.card (Rbar.subgroupOf Nbar)) := hcardSub ▸ hcopRbar
  have hNbar_bot : CFSG.pPrimeCore k.p ↥Nbar = ⊥ := h1 H hH
  have hRbarSubBot : Rbar.subgroupOf Nbar = ⊥ := by
    have hle : Rbar.subgroupOf Nbar ≤ CFSG.pPrimeCore k.p ↥Nbar :=
      CFSG.le_pPrimeCore_of_normal_coprime hRbarSubNorm hcop
    rw [hNbar_bot] at hle
    exact le_bot_iff.mp hle
  have hRbar_bot : Rbar = ⊥ :=
    (Subgroup.subgroupOf_eq_bot.mp hRbarSubBot).eq_bot_of_le hRbar_le_Nbar
  have hAleK : A ≤ K := by
    have h : A ≤ q.ker :=
      (Subgroup.map_eq_bot_iff A (f := q)).mp (by simpa [Rbar] using hRbar_bot)
    rwa [QuotientGroup.ker_mk'] at h
  have hRleK : R ≤ K.map H.subtype := by
    intro x hx
    have hxA : (⟨x, hx.2⟩ : ↥H) ∈ A := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_map_of_mem H.subtype (hAleK hxA)
  have hoddK : Odd (Nat.card (K.map H.subtype)) := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact k.odd_card_pPrimeCore_of_not_le hH.not_le hH.two_le_pRank
  have hRodd : Odd (Nat.card R) := hoddK.of_dvd_nat (Subgroup.card_dvd_of_le hRleK)
  rcases hR2.card_eq_or_dvd with h1 | h2
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    exact (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr h2)

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
