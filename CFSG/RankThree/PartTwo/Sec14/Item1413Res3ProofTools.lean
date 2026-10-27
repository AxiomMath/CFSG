module

import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.RankThree.PartTwo.Sec6.Item68
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413Res3

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_normalizer_of_mem_lA {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) {La : Subgroup G} (hLa : La ∈ lA A a)
    (h3 : 3 ∣ Nat.card La) :
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (La : Set G) := by
  intro x hxa
  refine mem_normalizer_of_map_conj_eq
    ((h.chosen136.2 a ha La hLa).2 _ (Sec6.map_conj_mem_thetaComponentsAt hxa hLa.1) ?_)
  rwa [Subgroup.card_map_of_injective (MulAut.conj x).injective]

theorem mem_scriptQ_of_le_normalizer (h142 : Concl142S14) {A L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) {c' : G} (hc' : Subgroup.zpowers c' ∈ omegaA A) {Q : Subgroup G}
    (hQN : Q ≤ Subgroup.normalizer (Subgroup.zpowers c' : Set G))
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (hQ3 : ¬ 3 ∣ Nat.card Q) :
    Q ∈ scriptQ A (lB A) := by
  have hQinv : Q ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c' : Set G)) A
      (piCompl 3) := ⟨hQN, (isPiSubgroup_piCompl_iff Nat.prime_three Q).mpr hQ3, hAQ⟩
  obtain ⟨Q', hQQ', hQ'⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c' : Set G)) A
      (piCompl 3))) hQinv
  exact mem_scriptQ_of_le (h142 G A c L hS c' hc' Q' hQ').1 hQQ' hAQ

theorem not_three_dvd_of_isPGroup_two {Q : Subgroup G} (hQ : IsPGroup 2 Q) :
    ¬ 3 ∣ Nat.card Q := by
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  rw [hk]
  intro h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem eq_bot_of_isPGroup_two_of_le {Q X : Subgroup G} (hQ : IsPGroup 2 Q) (hQX : Q ≤ X)
    (hX : ¬ 2 ∣ Nat.card X) : Q = ⊥ := by
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  rcases k with _ | k
  · exact Subgroup.eq_bot_of_card_eq Q (by simpa using hk)
  · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans
      (hk ▸ Subgroup.card_dvd_of_le hQX)) hX

theorem le_of_commutator_mem {A Q N : Subgroup G} (hA : IsPGroup 3 A) (hNQ : N ≤ Q)
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hN3 : ¬ 3 ∣ Nat.card N)
    (hcomm : ∀ q ∈ Q, ∀ a ∈ A, q * a * q⁻¹ * a⁻¹ ∈ N)
    (hC : Q ⊓ Subgroup.centralizer (A : Set G) = ⊥) : Q ≤ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro g hg
  let α : ↥A →* MulAut G := MulAut.conj.comp A.subtype
  have hα : ∀ (a : ↥A) (x : G), α a x = (a : G) * x * (a : G)⁻¹ := fun _ _ => rfl
  obtain ⟨c, hc, hfix⟩ :=
    (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hA α N hN3 g).2 (by
      intro a x hx
      have h1 : g⁻¹ * (a : G) * g⁻¹⁻¹ * (a : G)⁻¹ ∈ N := hcomm g⁻¹ (inv_mem hg) a a.2
      have h2 : (a : G) * (g⁻¹ * x) * (a : G)⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hAN a.2) _).mp hx
      have h3 : g⁻¹ * α a x =
          (g⁻¹ * (a : G) * g⁻¹⁻¹ * (a : G)⁻¹) * ((a : G) * (g⁻¹ * x) * (a : G)⁻¹) := by
        rw [hα]
        group
      rw [h3]
      exact mul_mem h1 h2)
  have hcQ : c ∈ Q := by
    have h1 := mul_mem hg (hNQ hc)
    rwa [mul_inv_cancel_left] at h1
  have hcA : c ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : (a : G) * c * (a : G)⁻¹ = c := by
      rw [← hα ⟨a, ha⟩]
      exact hfix ⟨a, ha⟩
    calc a * c = a * c * a⁻¹ * a := by group
      _ = c * a := by rw [h1]
  have hc1 : c = 1 := by
    have h1 : c ∈ Q ⊓ Subgroup.centralizer (A : Set G) := ⟨hcQ, hcA⟩
    rw [hC] at h1
    exact h1
  rw [hc1, mul_one] at hc
  have h1 := inv_mem hc
  rwa [inv_inv] at h1

theorem mem_thetaQuotCentralizer_of_mem {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) : c ∈ Sec4.thetaQuotCentralizer L := by
  have hLc := Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc hy))
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hcN, fun l hl => ?_⟩
  rw [← Subgroup.mem_centralizer_singleton_iff.mp (hLc hl), mul_inv_cancel_right, inv_mul_cancel]
  exact Subgroup.one_mem _

end Proof1413Res3

end CFSG.RankThree.PartTwo.Sec14
