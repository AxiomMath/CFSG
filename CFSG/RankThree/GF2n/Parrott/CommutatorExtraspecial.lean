module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Parrott.Setup

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

private lemma mem_normalizer_of_pow_three_eq_one {K : Subgroup G} {g : G}
    (hg : g ^ 3 = 1) (h : ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · exact h k
  · intro hk
    have h2 : g * (g * k * g⁻¹) * g⁻¹ ∈ K := h _ hk
    have h3 : g * (g * (g * k * g⁻¹) * g⁻¹) * g⁻¹ ∈ K := h _ h2
    have hggg : g * g * g = 1 := by
      rw [← pow_three']
      exact hg
    have h3' : (g * g * g) * k * (g * g * g)⁻¹ ∈ K := by
      convert h3 using 1
      group
    rw [hggg] at h3'
    simpa using h3'

private lemma commute_of_commutator_mem_center {g k c : G}
    (hg : g ^ 3 = 1) (hc : c = ⁅g, k⁆) (hgc : Commute g c) (hc2 : c * c = 1) :
    Commute g k := by
  have hgk : g * k * g⁻¹ = c * k := by
    rw [hc, commutatorElement_def]
    group
  have hgc' : g * c * g⁻¹ = c := by
    rw [hgc.eq]
    group
  have hggg : g * g * g = 1 := by
    rw [← pow_three']
    exact hg
  have h2 : (g * g) * k * (g * g)⁻¹ = k := by
    calc
      (g * g) * k * (g * g)⁻¹ = g * (g * k * g⁻¹) * g⁻¹ := by group
      _ = g * (c * k) * g⁻¹ := by rw [hgk]
      _ = (g * c * g⁻¹) * (g * k * g⁻¹) := by group
      _ = c * (c * k) := by rw [hgc', hgk]
      _ = k := by rw [← mul_assoc, hc2, one_mul]
  have h1 : g * k * g⁻¹ = k := by
    calc
      g * k * g⁻¹ = g * ((g * g) * k * (g * g)⁻¹) * g⁻¹ := by rw [h2]
      _ = (g * g * g) * k * (g * g * g)⁻¹ := by group
      _ = k := by rw [hggg]; group
  calc
    g * k = (g * k * g⁻¹) * g := by group
    _ = k * g := by rw [h1]

private lemma mul_self_eq_one_of_mem_zpowers_of_order_two {c : G}
    (h : c ∈ Subgroup.zpowers z) (hz : orderOf z = 2) : c * c = 1 := by
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, hz]
  have hdvd : orderOf c ∣ 2 := by
    have h' := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers z) h
    rwa [hcard] at h'
  have hpow : c ^ 2 = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · have hc1 : c = 1 := orderOf_eq_one_iff.mp h1
      rw [hc1]
      simp
    · rw [← h1]
      exact pow_orderOf_eq_one c
  simpa [pow_two] using hpow

end CFSG.RankThree.GF2n.Parrott
