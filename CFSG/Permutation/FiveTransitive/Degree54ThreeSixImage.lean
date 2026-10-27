module

public import CFSG.Permutation.FiveTransitive.SimpleGoursat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG

namespace FiveTransitive.Degree54ThreeSixImage

theorem exists_five_in_kernel
    {G F E : Type} [Group G] [Finite G] [Fintype F] [DecidableEq F] [Finite E]
    (hF : Nat.card F = 6) (hE : Nat.card E = 5)
    (rho : G →* Equiv.Perm F) (sigma : G →* Equiv.Perm E)
    (hrho : rho.range = ⊤) : ∃ g : G, orderOf g = 5 ∧ sigma g = 1 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsSimpleGroup (alternatingGroup F) := alternatingGroup.isSimpleGroup (by omega)
  have hA : Nat.card (alternatingGroup F) = 360 := by
    rw [nat_card_alternatingGroup,hF]
    norm_num [Nat.factorial]
  have hsmall : Nat.card sigma.range < Nat.card (alternatingGroup F) := by
    have hb := Nat.card_le_card_of_injective sigma.range.subtype Subtype.val_injective
    change Nat.card sigma.range ≤ Nat.card (Equiv.Perm E) at hb
    rw [Nat.card_perm,hE] at hb
    rw [hA]
    exact lt_of_le_of_lt hb (by norm_num [Nat.factorial])
  let K := sigma.ker
  let f : K →* Equiv.Perm F := rho.comp K.subtype
  have hAlt : alternatingGroup F ≤ f.range := by
    intro q hq
    obtain ⟨g,hg,hgs⟩ := SimpleGoursat.exists_lift_with_aux_eq_one
      G (Equiv.Perm F) (Equiv.Perm E) rho sigma (alternatingGroup F)
      (by rw [hrho]; exact le_top) hsmall q hq
    exact ⟨⟨g,hgs⟩,hg⟩
  have hd : 5 ∣ Nat.card K :=
    (show 5 ∣ Nat.card (alternatingGroup F) by rw [hA]; norm_num).trans
      ((Subgroup.card_dvd_of_le hAlt).trans (Subgroup.card_range_dvd f))
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 hd
  exact ⟨g.val,(Subgroup.orderOf_coe g).trans hg,g.property⟩

end FiveTransitive.Degree54ThreeSixImage

end CFSG
