module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight73Y
public import CFSG.Adapters.LieModelL3U3Sylow
public import CFSG.Adapters.LieModelL3U3Torus
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjSetCard
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63General
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S213L3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeSylow
import CFSG.GroupTheory.SylowNormalElements
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 BarInf calC)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_two_mul_gcd_three_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ 2 * 1 * Nat.gcd 3 (p ^ 1 - 1) := by
  intro hd
  have h2g : 2 * 1 * Nat.gcd 3 (p ^ 1 - 1) = 2 * Nat.gcd 3 (p ^ 1 - 1) := by ring
  rw [h2g] at hd
  have hpdvd6 : p ∣ 6 :=
    hd.trans (Nat.mul_dvd_mul_left 2 (Nat.gcd_dvd_left 3 (p ^ 1 - 1)))
  have hpdvd23 : p ∣ 2 * 3 := by simpa using hpdvd6
  rcases hp.dvd_mul.mp hpdvd23 with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    rw [hp3] at hd
    norm_num at hd

theorem not_dvd_two_mul_gcd_three_add_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ 2 * 1 * Nat.gcd 3 (p ^ 1 + 1) := by
  intro hd
  have h2g : 2 * 1 * Nat.gcd 3 (p ^ 1 + 1) = 2 * Nat.gcd 3 (p ^ 1 + 1) := by ring
  rw [h2g] at hd
  have hpdvd6 : p ∣ 6 :=
    hd.trans (Nat.mul_dvd_mul_left 2 (Nat.gcd_dvd_left 3 (p ^ 1 + 1)))
  have hpdvd23 : p ∣ 2 * 3 := by simpa using hpdvd6
  rcases hp.dvd_mul.mp hpdvd23 with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    rw [hp3] at hd
    norm_num at hd

theorem isStronglyPEmbedded_of_eight73Y_of_pRank (hK35w : UCK.K35w)
    (hKZ : StronglyEmbeddedCentralFree) {D : Data G} (h63 : UC6.R6_3 D) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {L Q : Subgroup G} (hL : L ∈ calC D.M)
    (hZ : ¬ p ∣ Nat.card (center (Bar2 L))) (hout : ¬ p ∣ Nat.card (Outer (BarInf L)))
    (hM3 : CFSG.Open.pRank p D.M ≤ 3) (hQ : IsSylowOf p Q L) (hQexp : ∀ x ∈ Q, x ^ p = 1)
    (hQcard : p ^ 3 ∣ Nat.card Q) (hΓ : rankThreeGamma 1 p Q ≤ D.M) :
    IsStronglyPEmbedded p D.M := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hQp : IsPGroup p ↥Q := hQ.isPGroup
  have hQ2 : 2 ≤ CFSG.Open.pRank p Q := by
    have hncyc : ¬ IsCyclic ↥Q := by
      intro hcyc
      obtain ⟨g, hg⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := ↥Q)).mp hcyc
      have hgen : orderOf g = Nat.card ↥Q := orderOf_eq_card_of_zpowers_eq_top hg
      have hgpow : g ^ p = 1 := by
        apply Subtype.ext
        simpa using hQexp (g : G) g.2
      have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgpow
      have hcarddvd : Nat.card ↥Q ∣ p := hgen ▸ hdvd
      have hle : Nat.card ↥Q ≤ p := Nat.le_of_dvd hp.pos hcarddvd
      have hge : p ^ 3 ≤ Nat.card ↥Q := Nat.le_of_dvd Nat.card_pos hQcard
      have hlt : p < p ^ 3 := by
        simpa using (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 1 < 3))
      omega
    haveI : Fact (IsPGroup p ↥Q) := ⟨hQp⟩
    obtain ⟨S, -, hScard, hSelem⟩ := CFSG.lemma_4_5_a (R := ↥Q) (p := p) hp2 hncyc
    let E : Subgroup G := S.map Q.subtype
    have hEcard : Nat.card E = p ^ 2 := by
      rw [Subgroup.card_map_of_injective Q.subtype_injective, hScard]
    have hEel : IsElemAbelian p E :=
      CFSG.SectionRank.isElemAbelian_map
        ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p S).1 hSelem) Q.subtype
    exact CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.map_subtype_le S) hEel
      (by rw [hEcard])
  have h2L : 2 ≤ CFSG.Open.pRank p L := hQ2.trans (CFSG.SectionRank.pRank_mono hp.one_lt hQ.le)
  have hMN : D.M ≤ normalizer (L : Set G) := by
    by_contra hnot
    have hex : ∃ g ∈ D.M, g ∉ normalizer (L : Set G) := by
      by_contra h
      exact hnot fun g hg => by
        by_contra hgn
        exact h ⟨g, hg, hgn⟩
    obtain ⟨g, hgM, hgN⟩ := hex
    have hne : L ≠ L.map (MulAut.conj g).toMonoidHom := fun he =>
      hgN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
    have h4 := UC22.uc22s213_four_le_pRank_of_two_conj hL (mem_conjSetOf_self D.M L)
      ⟨g, hgM, rfl⟩ hne hp hp2 h2L hZ
    omega
  obtain ⟨P, hP, hPL⟩ :=
    CFSG.GroupTheory.exists_isSylowOf_inf_eq_of_le (p := p) hLM hQ
  have hQL : Q ≤ L := hQ.le
  have hQP : Q ≤ P := by rw [← hPL]; exact inf_le_left
  have hP3 : CFSG.Open.pRank p P ≤ 3 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt hP.le).trans hM3
  have hPN : P ≤ normalizer (L : Set G) := hP.le.trans hMN
  have hPQL : P ≤ normalizer ((P ⊓ L : Subgroup G) : Set G) :=
    (le_inf le_normalizer hPN).trans inf_normalizer_le_normalizer_inf
  have hout2 : ¬ p ∣ Nat.card (Outer (Bar2 L)) :=
    UC22.uc22s213_not_dvd_card_outer_bar2 hL.2.2 hout
  have hQ' : IsSylowOf p (P ⊓ L) L := hPL ▸ hQ
  have hPQ : P ≤ Q ⊔ centralizerBar P L := by
    have hdec : P ≤ (P ⊓ L) ⊔ centralizerBar P L :=
      le_sup_centralizerBar_of_inner_prime inf_le_left inf_le_right rfl
        (normal_subgroupOf_of_le_normalizer hPQL) hQ' hP.isPGroup hPN le_rfl fun y hy =>
          exists_conj_of_not_dvd_outer y (hPN hy)
            (hP.isPGroup.to_le (zpowers_le.mpr hy)) hout2
    simpa [hPL] using hdec
  have hcyc : IsCyclic (centralizerBar P L) :=
    isCyclic_centralizerBar_of_pRank_le_three hp hp2 hQL hQP hP.isPGroup hQ2 hP3 hZ
  exact isStronglyPEmbedded_of_eight73Y hK35w hKZ h63 hp hp2 hL hMN hZ hP hQL hQP hQexp hQcard
    hPQ hcyc hΓ

theorem isStronglyPEmbedded_of_eight73Y_lieModel (hGA : GriessAllModelsStatement)
    (hK35w : UCK.K35w) (hKZ : StronglyEmbeddedCentralFree) {D : Data G} (h63 : UC6.R6_3 D)
    {p : ℕ} (hp2 : p ≠ 2) {L Q : Subgroup G} (hL : L ∈ calC D.M)
    (hX : LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1)
    (hM3 : CFSG.Open.pRank p D.M ≤ 3) (hQ : IsSylowOf p Q L)
    (hΓ : rankThreeGamma 1 p Q ≤ D.M) : IsStronglyPEmbedded p D.M := by
  classical
  have hp : p.Prime := by
    rcases hX with hX | hX
    · exact hX.admissible.1
    · exact hX.admissible.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : ¬ p ∣ Nat.card (center (Bar2 L)) := by
    rcases hX with hX | hX
    · exact UC22.uc22s213_not_dvd_card_center_of_rank_three_odd hGA hL (.inl rfl) hp2 hX
    · exact UC22.uc22s213_not_dvd_card_center_of_rank_three_odd hGA hL (.inr rfl) hp2 hX
  have hout : ¬ p ∣ Nat.card (Outer (BarInf L)) := by
    rcases hX with hX | hX
    · exact fun hd =>
        not_dvd_two_mul_gcd_three_sub_one hp hp2 (hd.trans hX.card_outer_psl3_dvd)
    · rw [hX.card_outer_psu3]
      exact not_dvd_two_mul_gcd_three_add_one hp hp2
  have hRnot : ¬ p ∣ Nat.card (CFSG.solvableRadical ↥L) :=
    UC22.not_dvd_card_solvableRadical hL.2.2 hp hp2 hZ
  have hfactBar : (Nat.card (BarInf L)).factorization p = 3 := by
    rcases hX with hX | hX
    · simpa using hX.factorization_card_psl3 (f := 1)
    · simpa using hX.factorization_card_psu3 (f := 1)
  have hcardL : Nat.card ↥L = Nat.card (BarInf L) * Nat.card (CFSG.solvableRadical ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.solvableRadical ↥L)
  have hfactL : (Nat.card ↥L).factorization p = 3 := by
    rw [hcardL, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hRnot, add_zero, hfactBar]
  have hQcard : p ^ 3 ∣ Nat.card Q := by
    have hQcard' : Nat.card Q = p ^ 3 := by rw [hQ.card_eq, hfactL]
    rw [hQcard']
  have hQpL : IsPGroup p (Q.subgroupOf L) := hQ.isPGroup.comap_subtype (K := L)
  have hQR : Q.subgroupOf L ⊓ CFSG.solvableRadical ↥L = ⊥ := by
    rw [← disjoint_iff]
    refine Subgroup.disjoint_of_coprime_natCard ?_
    obtain ⟨k, hk⟩ := hQpL.exists_card_eq
    rw [hk]
    exact (hp.coprime_iff_not_dvd.mpr hRnot).pow_left k
  have hQexp : ∀ x ∈ Q, x ^ p = 1 := by
    intro x hx
    let x' : ↥L := ⟨x, hQ.le hx⟩
    have hx'Q : x' ∈ Q.subgroupOf L := hx
    obtain ⟨k, hk⟩ := hQpL ⟨x', hx'Q⟩
    have hkx : x' ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have himg : ∃ k : ℕ,
        ((QuotientGroup.mk' (CFSG.solvableRadical ↥L)) x') ^ p ^ k = 1 := by
      refine ⟨k, ?_⟩
      rw [← map_pow, hkx, map_one]
    have hpow : ((QuotientGroup.mk' (CFSG.solvableRadical ↥L)) x') ^ p = 1 := by
      rcases hX with hX | hX
      · exact hX.pow_eq_one_of_psl3 hp2 himg
      · exact hX.pow_eq_one_of_psu3 hp2 himg
    have hmemR : x' ^ p ∈ CFSG.solvableRadical ↥L := by
      have h1 : (QuotientGroup.mk' (CFSG.solvableRadical ↥L)) (x' ^ p) = 1 := by
        rw [map_pow, hpow]
      exact (QuotientGroup.eq_one_iff (x' ^ p)).mp h1
    have hmemQ : x' ^ p ∈ Q.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      simpa using Q.pow_mem hx p
    have hbot : x' ^ p = 1 := by
      have hmem : x' ^ p ∈ Q.subgroupOf L ⊓ CFSG.solvableRadical ↥L := ⟨hmemQ, hmemR⟩
      rwa [hQR, Subgroup.mem_bot] at hmem
    simpa using congrArg Subtype.val hbot
  exact isStronglyPEmbedded_of_eight73Y_of_pRank hK35w hKZ h63 hp hp2 hL hZ hout hM3 hQ hQexp
    hQcard hΓ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
