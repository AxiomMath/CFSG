module

public import CFSG.RankThree.PartOne.K128.G2Syl
public import CFSG.RankThree.PartOne.K133H.TorusImage

public section

namespace CFSG.RankThree.PartOne.K133H

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K128 CFSG.Timmesfeld.ExceptionalOrders

set_option linter.unusedSectionVars false

theorem card_weylGroup_G2 : Nat.card (WeylGroup .G2) = 12 := by
  classical
  have : Fintype (WeylGroup .G2) := Fintype.ofFinite _
  have h := sum_length_G2 1
  simp only [one_pow, Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, h]
  simp [geomSum]

theorem card_torusImage_torusTorsion_dvd {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1) :
    Nat.card ↥(torusImage (torusTorsion K p) (adjointGroup .G2 K)) ∣ 12 := by
  classical
  have : Finite (ModGL .G2 K) := finite_modGL
  obtain ⟨-, -, hC, hex, huniq, hmem, -, -⟩ :=
    G2_toral_prime_plane_centralizer_and_scalar_normalizers (k := K) hp hp3 hpq
  refine card_torusImage_dvd_of_card (H := torusGroup .G2 K) torusGroup_le_adjointGroup' ?_ ?_
  · intro h hh
    rw [← hC] at hh
    exact hh.2
  · let f : ↥(torusGroup .G2 K) × WeylGroup .G2 →
        ↥(adjointGroup .G2 K ⊓ Subgroup.normalizer (torusTorsion K p : Set (ModGL .G2 K))) :=
      fun hw => ⟨hw.1 * canonicalRep (coxeterSystem .G2) K hw.2, hmem _ hw.1.2 _⟩
    have hf : Function.Bijective f := by
      refine ⟨fun a b hab => ?_, fun ⟨g, hg⟩ => ?_⟩
      · obtain ⟨h1, h2⟩ := huniq _ a.1.2 _ b.1.2 _ _ (congrArg Subtype.val hab)
        exact Prod.ext (Subtype.ext h1) h2
      · obtain ⟨h, hh, w, rfl⟩ := hex g hg
        exact ⟨(⟨h, hh⟩, w), rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, card_weylGroup_G2, mul_comm]

theorem exists_conj_eq_torusTorsion {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) (hpq : p ∣ Nat.card K - 1)
    {A : Subgroup (ModGL .G2 K)} (hAC : A ≤ adjointGroup .G2 K) (hpow : ∀ x ∈ A, x ^ p = 1)
    (hcard : Nat.card A = p ^ 2) :
    ∃ g ∈ adjointGroup .G2 K, A.map (MulAut.conj g).toMonoidHom = torusTorsion K p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (ModGL .G2 K) := finite_modGL
  have hQ : 2 ≤ Nat.card K := Finite.one_lt_card
  have hdQ : p ∣ Nat.card K ^ 2 - 1 := by
    rw [sq_sub_one_eq _ (by omega)]
    exact hpq.mul_right _
  have hnQ1 : ¬ p ∣ Nat.card K + 1 := by
    intro h
    have h1 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub h hpq
    have h2 : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [h2] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hvp : (Nat.card K ^ 2 - 1).factorization p = (Nat.card K - 1).factorization p := by
    rw [sq_sub_one_eq _ (by omega), Nat.factorization_mul (by omega) (by omega),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnQ1, add_zero]
  have hvC : (Nat.card ↥(adjointGroup .G2 K)).factorization p =
      (Nat.card ↥(torusGroup .G2 K)).factorization p := by
    rw [card_adjointGroup_G2, card_torusGroup_G2, factorization_ordG2 hp hp5 hQ hpK hdQ, hvp,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hTC : torusGroup .G2 K ≤ adjointGroup .G2 K := torusGroup_le_adjointGroup'
  obtain ⟨S₁⟩ : Nonempty (Sylow p ↥(torusGroup .G2 K)) := inferInstance
  let P₀ : Subgroup ↥(adjointGroup .G2 K) :=
    (S₁ : Subgroup ↥(torusGroup .G2 K)).map (Subgroup.inclusion hTC)
  have hP₀ : Nat.card ↥P₀ = p ^ (Nat.card ↥(adjointGroup .G2 K)).factorization p := by
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hTC),
      Sylow.card_eq_multiplicity, hvC]
  let S₀ : Sylow p ↥(adjointGroup .G2 K) := Sylow.ofCard P₀ hP₀
  have hA'p : IsPGroup p ↥(A.subgroupOf (adjointGroup .G2 K)) := fun x => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hpow x.1.1 (Subgroup.mem_subgroupOf.1 x.2)⟩
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hA'p
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(adjointGroup .G2 K) P S₀
  refine ⟨(g : ModGL .G2 K), g.2, ?_⟩
  have hle : A.map (MulAut.conj (g : ModGL .G2 K)).toMonoidHom ≤ torusTorsion K p := by
    rintro _ ⟨x, hxA, rfl⟩
    have hxP : (⟨x, hAC hxA⟩ : ↥(adjointGroup .G2 K)) ∈ P := hP (Subgroup.mem_subgroupOf.2 hxA)
    have h1 : (MulAut.conj g) • (⟨x, hAC hxA⟩ : ↥(adjointGroup .G2 K)) ∈ (g • P : Sylow p _) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hxP
    rw [hg] at h1
    obtain ⟨s, -, hs⟩ := Subgroup.mem_map.1 (show _ ∈ P₀ from h1)
    refine mem_torusTorsion_iff.2 ⟨?_, ?_⟩
    · have := congrArg (fun z : ↥(adjointGroup .G2 K) => (z : ModGL .G2 K)) hs
      simp only [Subgroup.coe_inclusion] at this
      show (g : ModGL .G2 K) * x * (g : ModGL .G2 K)⁻¹ ∈ torusGroup .G2 K
      rw [show (g : ModGL .G2 K) * x * (g : ModGL .G2 K)⁻¹ = (s : ModGL .G2 K) from
        this.symm.trans (by rfl)]
      exact s.2
    · show ((MulAut.conj (g : ModGL .G2 K)) x) ^ p = 1
      rw [← map_pow, hpow x hxA, map_one]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [natCard_torusTorsion hpq, Subgroup.card_map_of_injective (MulAut.conj _).injective, hcard]

end CFSG.RankThree.PartOne.K133H
