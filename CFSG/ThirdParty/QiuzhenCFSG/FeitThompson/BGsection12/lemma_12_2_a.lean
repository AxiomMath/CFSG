module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_1_g
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# lemma_12_2_a
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Group G] [Finite G] [IsMinCE G] in
public theorem CFSG.section12_subgroup_characteristic_of_cyclic
    {H : Type*} [Group H] [Finite H] [IsCyclic H] (K : Subgroup H) :
    K.Characteristic := by
  classical
  rw [Subgroup.characteristic_iff_map_le]
  intro φ x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hyK, rfl⟩
  have hxpow : (φ y) ^ Nat.card K = 1 := by
    let yK : K := ⟨y, hyK⟩
    have hyKpow : yK ^ Nat.card K = 1 := @pow_card_eq_one' K _ yK
    have hypow : y ^ Nat.card K = 1 :=
      congrArg Subtype.val hyKpow
    calc
      (φ y) ^ Nat.card K = φ (y ^ Nat.card K) := by simp
      _ = φ 1 := by rw [hypow]
      _ = 1 := by simp
  have hset_le : {y : H | y ^ Nat.card K = 1} ⊆ K := by
    intro y hy
    have hKcard_pos : 0 < Nat.card K := Nat.card_pos
    have hcard_roots : Nat.card {y : H | y ^ Nat.card K = 1} ≤ Nat.card K := by
      letI : Fintype H := Fintype.ofFinite H
      have hle := IsCyclic.card_pow_eq_one_le (α := H) (n := Nat.card K) hKcard_pos
      rw [Nat.card_eq_fintype_card]
      simpa [Fintype.card_subtype] using hle
    have hK_subset : (K : Set H) ⊆ {y : H | y ^ Nat.card K = 1} := by
      intro z hz
      let zK : K := ⟨z, hz⟩
      have hzKpow : zK ^ Nat.card K = 1 := @pow_card_eq_one' K _ zK
      exact congrArg Subtype.val hzKpow
    have hsets_eq : (K : Set H) = {y : H | y ^ Nat.card K = 1} := by
      exact Set.Finite.eq_of_subset_of_card_le
        (Set.toFinite ({y : H | y ^ Nat.card K = 1} : Set H)) hK_subset hcard_roots
    exact hsets_eq.symm ▸ hy
  exact hset_le (by simpa using hxpow)

private theorem CFSG.section12_lemma_10_5_nontrivial_pSubgroup_rank
    {M X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpσ : p ∉ section10SigmaPrimes M)
    (hpX : IsPGroup p.val X) (hXne : X ≠ ⊥) (hXM : X ≤ M)
    (hNX : Subgroup.normalizer (X : Set G) ≤ M) :
    primeRank p.val M = 2 := by
  classical
  have hXsub_p : IsPGroup p.val (X.subgroupOf M) :=
    hpX.of_equiv (Subgroup.subgroupOfEquivOfLe hXM).symm
  have hXsub_ne : X.subgroupOf M ≠ ⊥ := by
    intro hbot
    apply hXne
    ext x
    constructor
    · intro hx
      have hxsub : (⟨x, hXM hx⟩ : M) ∈ X.subgroupOf M := by
        simpa [Subgroup.mem_subgroupOf] using hx
      have : (⟨x, hXM hx⟩ : M) = 1 := by
        simpa [hbot] using hxsub
      simpa using congrArg Subtype.val this
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact X.one_mem
  have hpM : p ∈ subgroupPrimeSet M :=
    section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
      (A := M) (B := X.subgroupOf M) hXsub_p hXsub_ne
  have hpos : 1 ≤ primeRank p.val M :=
    section12_primeRank_pos_of_mem_subgroupPrimeSet (R := M) hpM
  have hle_two : primeRank p.val M ≤ 2 := by
    by_contra hnot
    have hgt : 2 < primeRank p.val M := by omega
    exact hpσ (section12_sigmaPrimes_mem_of_alphaPrimes_mem hM ⟨hpM, hgt⟩)
  by_contra hne
  have hrank1 : primeRank p.val M = 1 := by omega
  obtain ⟨P, hXsub_le_P⟩ := IsPGroup.exists_le_sylow (G := M) (p := p.val) hXsub_p
  have hPcyc : IsCyclic (P : Subgroup M) := by
    have hpG : p.val ∣ Nat.card G := hpM.trans (Subgroup.card_subgroup_dvd_card M)
    have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG
    exact section12_sylow_cyclic_of_primeRank_le_one hpodd (by simp [hrank1]) P
  let XG : Subgroup G := X
  have hXG_eq : XG = X := rfl
  have hXG_le_Pamb : XG ≤ section10AmbientSylowSubgroup M P := by
    intro x hx
    have hxsub : (⟨x, hXM hx⟩ : M) ∈ X.subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hXM hx⟩, hXsub_le_P hxsub, rfl⟩
  have hPamb_cyc : IsCyclic (section10AmbientSylowSubgroup M P) := by
    let e : (P : Subgroup M) ≃* section10AmbientSylowSubgroup M P :=
      Subgroup.equivMapOfInjective (f := M.subtype) (P : Subgroup M) M.subtype_injective
    exact e.isCyclic.mp hPcyc
  haveI : IsCyclic (section10AmbientSylowSubgroup M P) := hPamb_cyc
  have hXGsub_char :
      (XG.subgroupOf (section10AmbientSylowSubgroup M P)).Characteristic :=
    section12_subgroup_characteristic_of_cyclic
      (XG.subgroupOf (section10AmbientSylowSubgroup M P))
  have hnormP_le_normX :
      Subgroup.normalizer (section10AmbientSylowSubgroup M P : Set G) ≤
        Subgroup.normalizer (X : Set G) := by
    have hnormP_le_normXp :
        Subgroup.normalizer (section10AmbientSylowSubgroup M P : Set G) ≤
          Subgroup.normalizer
            ((XG.subgroupOf (section10AmbientSylowSubgroup M P)).map
              (section10AmbientSylowSubgroup M P).subtype : Set G) := by
      simpa [section10AmbientSylowSubgroup, XG] using
        (section8_normalizer_map_subtype_le_of_characteristic
          (H := section10AmbientSylowSubgroup M P)
          (K := XG.subgroupOf (section10AmbientSylowSubgroup M P)))
    have hXGsub_map_eq :
        (XG.subgroupOf (section10AmbientSylowSubgroup M P)).map
            (section10AmbientSylowSubgroup M P).subtype = X := by
      simpa [hXG_eq] using Subgroup.map_subgroupOf_eq_of_le hXG_le_Pamb
    simpa [hXGsub_map_eq] using hnormP_le_normXp
  have hpσ_mem : p ∈ section10SigmaPrimes M := by
    refine ⟨hpM, P, ?_⟩
    exact hnormP_le_normX.trans hNX
  exact hpσ hpσ_mem

/-- Lemma 12.2(a). -/
public theorem CFSG.lemma_12_2_a
    {M Mstar X : Subgroup G} {p : Nat.Primes}
    (_hM : M ∈ section9MaximalSubgroups G)
    (hpX : IsPGroup p.val X) (hXne : X ≠ ⊥) (_hXM : X ≤ M)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    p ∈ section10SigmaPrimes Mstar ∪ section12Tau2Primes Mstar := by
  by_cases hpσstar : p ∈ section10SigmaPrimes Mstar
  · exact Or.inl hpσstar
  · right
    have hX_Mstar : X ≤ Mstar := by
      exact Subgroup.le_normalizer.trans hMstar.2
    have hprank : primeRank p.val Mstar = 2 :=
      section12_lemma_10_5_nontrivial_pSubgroup_rank
        (M := Mstar) (X := X) (p := p) hMstar.1 hpσstar hpX hXne hX_Mstar hMstar.2
    simpa [section12Tau2Primes] using ⟨hpσstar, hprank⟩

end Section12
