module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic
import CFSG.RankThree.GroupTheory.SteinbergBKComponentOrbitLocalRank
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBK

open Subgroup CFSG CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (localRank)

theorem pElement_normalizes_component_of_localRank_le_three {H : Type*} [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hrank : localRank p H ≤ 3) {L : Subgroup H}
    (hL : IsComponent L) (hpL : 2 * p ∣ Nat.card (L ⧸ center L)) {x : H}
    (hx : ∃ k : ℕ, orderOf x = p ^ k) : x ∈ normalizer (L : Set H) := by
  by_contra h
  have hmove : L.map (MulAut.conj x).toMonoidHom ≠ L := fun h' =>
    h (mem_normalizer_iff_map_conj_eq.mpr h')
  obtain ⟨-, -, -, -, -, -, -, -, hdl, hrd⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBK.component_orbit_ambient_local_rank_witness hp hx hL
      hmove hp hpL rfl
  have h4 : p = 4 := by omega
  exact absurd hp (h4 ▸ by norm_num)

theorem selected_prime_elements_fix_prime_divisible_quotient_components {G : Type*} [Group G]
    [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup G) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) (hrank : localRank p G ≤ 3) {L : Subgroup (G ⧸ N)}
    (hL : IsComponent L) (hpL : p ∣ Nat.card (L ⧸ center L)) :
    (∀ x : G, (∃ k : ℕ, orderOf x = p ^ k) → (x : G ⧸ N) ∈ normalizer (L : Set (G ⧸ N))) ∧
      ∀ P : Subgroup G, IsPGroup p P → ∀ x ∈ P, (x : G ⧸ N) ∈ normalizer (L : Set (G ⧸ N)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hQrank : localRank p (G ⧸ N) ≤ 3 :=
    (CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 N hN).trans hrank
  have : IsSimpleGroup (L ⧸ center L) := hL.1.2.1
  have h2L : 2 ∣ Nat.card (L ⧸ center L) := by
    obtain ⟨a, b, hab⟩ := hL.1.2.2
    exact (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even
      ⟨a, b, hab⟩).1.two_dvd
  have h2pL : 2 * p ∣ Nat.card (L ⧸ center L) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm) h2L hpL
  have hmain : ∀ x : G, (∃ k : ℕ, orderOf x = p ^ k) →
      (x : G ⧸ N) ∈ normalizer (L : Set (G ⧸ N)) := by
    intro x ⟨k, hk⟩
    have hdvd : orderOf (x : G ⧸ N) ∣ p ^ k := hk ▸ orderOf_map_dvd (QuotientGroup.mk' N) x
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    exact pElement_normalizes_component_of_localRank_le_three hp hp3 hQrank hL h2pL ⟨j, hj⟩
  refine ⟨hmain, fun P hP x hx => hmain x ?_⟩
  obtain ⟨n, hn⟩ := hP.exists_orderOf_eq_pow ⟨x, hx⟩
  exact ⟨n, (Subgroup.orderOf_coe (⟨x, hx⟩ : P)).trans hn⟩

end CFSG.RankThree.GroupTheory.SteinbergBK
