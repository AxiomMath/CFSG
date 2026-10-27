module

public import CFSG.RankThree.PartOne.S11c.Sec66TFamily
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw
public import CFSG.Sporadic.Schreier.TitsOuterTwo

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint
open CFSG.Sporadic.Schreier.Tits (CTI_Tits_model_outer_two_part_bound)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem mem_innerAut_of_card_outer_two {T : Type} [Group T]
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) = 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {α : MulAut T} (hαp : α ^ p = 1) : α ∈ innerAut T := by
  let π : MulAut T →* CFSG.ComponentClassification.OuterAutomorphisms.Outer T :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)
  have h1 : orderOf (π α) ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hαp, map_one])
  have h2 : orderOf (π α) ∣ 2 := hout ▸ orderOf_dvd_natCard _
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have h3 : orderOf (π α) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : π α = 1 := orderOf_eq_one_iff.mp h3
  have hxi : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner T :=
    (QuotientGroup.eq_one_iff α).mp h4
  exact hxi

theorem sec66T_K1_Tits :
    Sec66T_K1 .Tits := by
  intro T _ _ p hp hp5 hmodel _ α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU _hmv _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  have hR : ReeTitsModel T .Tits 2 f := (lieModel_Tits_iff.mp hM).2
  obtain ⟨-, -, hout, -⟩ := CTI_Tits_model_outer_two_part_bound T 2 f hR
  have hαp : α ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one α
  exact absurd (mem_innerAut_of_card_outer_two hout hp (by omega) hαp) hαinn

theorem sec66T_K2_Tits :
    Sec66T_K2 .Tits := by
  intro T _ _ p hp hp5 hmodel _ E hE hcard hEinn _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  have hR : ReeTitsModel T .Tits 2 f := (lieModel_Tits_iff.mp hM).2
  obtain ⟨-, -, hout, -⟩ := CTI_Tits_model_outer_two_part_bound T 2 f hR
  have : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) :=
    Nat.finite_of_card_ne_zero (by rw [hout]; norm_num)
  have : Fact (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T)).Prime := by
    rw [hout]; exact ⟨Nat.prime_two⟩
  have : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) :=
    isCyclic_of_prime_card rfl
  let π : MulAut T →* CFSG.ComponentClassification.OuterAutomorphisms.Outer T :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)
  refine no_plane_of_cyclic_quotient hp π ?_ E hE hcard hEinn
  intro x hx _
  have hxi : x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner T :=
    (QuotientGroup.eq_one_iff x).mp hx
  exact hxi

end CFSG.RankThree.PartOne.Sec66T
