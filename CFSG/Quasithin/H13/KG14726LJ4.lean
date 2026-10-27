module

public import CFSG.Quasithin.H13.KG14726LSylow
public import CFSG.Quasithin.H13.KG14726J4

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup CFSG.Blueprint

theorem kg115J4Input_holds :
    KG115J4Input := by
  show KG115Excluded NativeSporadic.J4
  have : Finite NativeSporadic.J4 := CFSG.Sporadic.J4.fam_j4_simplicity.1
  obtain ⟨hsimple, -, hZ2, -, htype⟩ := J4.concreteJ4_typeJ4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcent : ∀ (S : Sylow 2 NativeSporadic.J4) (l : NativeSporadic.J4),
      l ∈ (S : Subgroup NativeSporadic.J4) → (∀ s ∈ (S : Subgroup NativeSporadic.J4),
        s * l = l * s) → l ≠ 1 →
      Nat.card (centralizer ({l} : Set NativeSporadic.J4)) = 21799895040 := by
    intro S l hl hlc hl1
    have hlZ : (⟨l, hl⟩ : ↥(S : Subgroup NativeSporadic.J4)) ∈
        center ↥(S : Subgroup NativeSporadic.J4) :=
      mem_center_iff.mpr fun g => Subtype.ext (hlc g g.2)
    have hord : orderOf l = 2 := by
      have h1 := orderOf_dvd_natCard
        (⟨⟨l, hl⟩, hlZ⟩ : ↥(center ↥(S : Subgroup NativeSporadic.J4)))
      rw [hZ2 S, Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h1
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hl1
      · exact h
    exact (htype l hord ⟨S, ⟨⟨l, hl⟩, hlZ, rfl⟩⟩).1
  have h4 : 4 ∣ Nat.card NativeSporadic.J4 := by
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 NativeSporadic.J4))
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(center ↥(S : Subgroup NativeSporadic.J4))) 2 (by rw [hZ2 S])
    have hz1 : (((z : ↥(S : Subgroup NativeSporadic.J4)) : NativeSporadic.J4)) ≠ 1 := by
      intro h1
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, h1, orderOf_one] at hz
      exact absurd hz (by norm_num)
    have hzc : ∀ s ∈ (S : Subgroup NativeSporadic.J4),
        s * ((z : ↥(S : Subgroup NativeSporadic.J4)) : NativeSporadic.J4) =
          ((z : ↥(S : Subgroup NativeSporadic.J4)) : NativeSporadic.J4) * s := by
      intro s hs
      have h1 := congrArg Subtype.val (mem_center_iff.mp z.2 ⟨s, hs⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
      exact h1
    have hC := hcent S _ (z : ↥(S : Subgroup NativeSporadic.J4)).2 hzc hz1
    refine (show (4 : ℕ) ∣ 21799895040 by norm_num).trans ?_
    rw [← hC]
    exact card_subgroup_dvd_card _
  refine kg115Excluded_of_simple fun hc => kg115Excluded_of_at hc
    (sylowTwoNoThree_of_twoCentral
      (kg14726SporadicInput_J4 : TwoCentralConstrained NativeSporadic.J4) h4) ?_
  intro S hS hSi l hl hlc hl1
  refine kg115At_of_prime ?_
  have hC := hcent (hS.toSylow hSi) l hl hlc hl1
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hc5⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(centralizer ({l} : Set NativeSporadic.J4))) 5 (by rw [hC]; norm_num)
  exact ⟨c, mem_centralizer_singleton_iff.mp c.2, 5, by norm_num, le_rfl,
    by rw [Subgroup.orderOf_coe, hc5]⟩

end CFSG.Quasithin.H13.KG14726

end
