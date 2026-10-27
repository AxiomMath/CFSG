module

public import CFSG.Quasithin.Background.S1549CBasic
public import CFSG.Quasithin.Background.S1549CA0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

namespace S1549C

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem claim_b (h11 : StageLemma14111) (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    {H : Subgroup G} (hH : Adm T Mc M H) : Y0 T Mc M = thetaOf (M ⊓ H) := by
  have hHMc : H ≤ Mc := C1Pack153.le_mc_of_isHTM153 h11 h hH.hH
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hxK : x ∈ Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) := hx.1
    have hx3 : x ^ 3 = 1 := pow_three_eq_one_of_odd h113 h hxK.1 hx.2
    have hxH : x ∈ H := inf_le_of_adm h113 h hH hxK
    by_cases hx1 : x = 1
    · rw [hx1]; exact Subgroup.one_mem _
    · refine Subgroup.subset_closure ⟨⟨Y153_le Mc M hxK.1, hxH⟩, ?_⟩
      have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h' | h'
      · exact absurd (orderOf_eq_one_iff.mp h') hx1
      · exact h'
  · refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hodd : Odd (orderOf x) := hx.2 ▸ (by decide : Odd 3)
    have hxC := C1Pack153.mem_centralizer_of_odd_of_mem_inf h ⟨hHMc hx.1.2, hx.1.1⟩ hodd
    have hxY := mem_Y153_of_orderOf_three h113 h hx.1.1 hxC hx.2
    exact mem_oTwoUpper_of_odd ⟨hxY, hxC⟩ hodd

end S1549C

end CFSG.Quasithin
