module

public import CFSG.RankThree.GroupTheory.SteinbergBKComponentOrbitLocalRank
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG CFSG.Assembly.RankThreeEven

variable {G : Type*} [Group G]

theorem large_prime_elements_normalize_components [Finite G] (he : twoLocalOddRank G ≤ 3)
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) {x : G} (hx : ∃ k : ℕ, orderOf x = r ^ k)
    {L : Subgroup G} (hL : IsComponent L) : x ∈ normalizer (L : Set G) := by
  by_contra hxL
  have hmove : L.map (MulAut.conj x).toMonoidHom ≠ L := fun h' =>
    hxL (mem_normalizer_iff_map_conj_eq.mpr h')
  obtain ⟨-, hsimple, hnonab⟩ := hL.1
  have : IsSimpleGroup (L ⧸ center L) := hsimple
  obtain ⟨heven, -⟩ := CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnonab
  obtain ⟨q, hq, hq3, hqS⟩ : ∃ q : ℕ, q.Prime ∧ 3 < q ∧ q ∣ Nat.card (L ⧸ center L) := by
    by_contra hno
    push Not at hno
    have hsub : (Nat.card (L ⧸ center L)).primeFactors ⊆ {2, 3} := by
      intro t ht
      have htp := Nat.prime_of_mem_primeFactors ht
      have htle : t ≤ 3 := by
        by_contra h
        exact hno t htp (by omega) (Nat.dvd_of_mem_primeFactors ht)
      have h2t := htp.two_le
      interval_cases t <;> simp
    have hcard : (Nat.card (L ⧸ center L)).primeFactors.card ≤ 2 :=
      (Finset.card_le_card hsub).trans (Finset.card_le_two)
    have hsolv := CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two hcard
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolv a b)
  have h2q : 2 * q ∣ Nat.card (L ⧸ center L) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)) (even_iff_two_dvd.mp heven) hqS
  obtain ⟨-, -, -, -, -, -, -, -, hdl, hrd⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBK.component_orbit_ambient_local_rank_witness hr hx hL
      hmove hq h2q rfl
  have hqG : q ∣ Nat.card G := by
    refine hqS.trans ?_
    refine (card_quotient_dvd_card (center L)).trans ?_
    exact card_subgroup_dvd_card L
  have hloc := CFSG.RankThree.Theta.localRank_le_twoLocalOddRank hq (by omega) hqG
  have hr4 : r - 1 ≤ 3 := hrd.trans (hdl.trans (hloc.trans he))
  have hr4' : r = 4 := by omega
  rw [hr4'] at hr
  exact absurd hr (by norm_num)

end CFSG.RankThree.GroupTheory.SteinbergBM
