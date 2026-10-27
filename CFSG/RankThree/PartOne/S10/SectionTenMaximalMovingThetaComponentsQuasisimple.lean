module

public import CFSG.RankThree.PartOne.S10.ThetaContract

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

theorem not_isCyclic_of_relIndex_eq_prime {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {A E : Subgroup G} (hA : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 3) (hEA : E ≤ A) (hrel : E.relIndex A = p) :
    ¬ IsCyclic E := by
  intro hcyc
  have hcard : Nat.card E = p ^ 2 := by
    have h1 := (E.subgroupOf A).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv, hAcard] at h1
    change E.relIndex A * Nat.card E = p ^ 3 at h1
    rw [hrel] at h1
    have h2 : p * (p ^ 2) = p * Nat.card E := by rw [h1]; ring
    exact (Nat.eq_of_mul_eq_mul_left hp.pos h2).symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have hgord : orderOf (g : G) = p ^ 2 := by
    rw [Subgroup.orderOf_coe, hg, hcard]
  have hgp : (g : G) ^ p = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (A := A) (g : G) (hEA g.2)
  have hdvd : p ^ 2 ∣ p := hgord ▸ orderOf_dvd_of_pow_eq_one hgp
  have := Nat.le_of_dvd hp.pos hdvd
  nlinarith [hp.two_le]

theorem section_ten_maximal_moving_theta_components_quasisimple_of
    (hF4 : NonquasisimpleMovingThetaComponentScalarKernelHyperplane)
    (hE8 : SectionTenMaximalComponentQuotientActorKernelCyclic) :
    SectionTenMaximalMovingThetaComponentsQuasisimple := by
  intro hS hT G _ _ p A hS10 L hL
  by_contra hnq
  obtain ⟨-, hrel, -⟩ := hF4 hT G p A hS10 L hL.1 hnq
  obtain ⟨-, hcyc⟩ := hE8 hS G p A hS10 L hL.2
  obtain ⟨-, -, -, -, -, -, hAe, hAcard, -, -⟩ := id hS10
  exact not_isCyclic_of_relIndex_eq_prime (sectionTenSetup_prime hS10) hAe hAcard inf_le_left hrel
    hcyc

end CFSG.RankThree.PartOne
