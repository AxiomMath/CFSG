module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.Adapters.LieModelOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint Subgroup

theorem uc22p21l_j1NotSp4SU3 : J1NotSp4SU3 := by
  intro X _ hX
  obtain ⟨e⟩ := hX
  have hcard : Nat.card X = 175560 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J1.card_J1
  haveI : IsSimpleGroup X := by
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J1) :=
      CFSG.Sporadic.J1.isSimpleGroup_J1
    exact e.isSimpleGroup
  have hc : Subgroup.center X = ⊥ := by
    rcases (inferInstance : (Subgroup.center X).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hcomm : ∀ a b : X, a * b = b * a := fun a b =>
        (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm
      letI : CommGroup X := { ‹Group X› with mul_comm := hcomm }
      haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
      have hp : (Nat.card X).Prime := IsSimpleGroup.prime_card
      rw [hcard] at hp
      exact absurd hp (by norm_num)
  refine ⟨hc, fun n hn => ?_, fun n hn => ?_⟩
  · have h1 : Nat.card X = ordBC 2 (2 ^ n) := hn.card_eq_lieOrd (by norm_num)
    obtain ⟨r, hr, hm⟩ := (CFSG.Timmesfeld.Orders.profile_ordBC (n := 2) hn.admissible.2.1).two
    have h2 : 2 ^ (n * (2 * 2)) * r = 2 ^ 3 * 21945 := by
      rw [← hm, ← h1, hcard]
      norm_num
    have := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr (by decide : Odd 21945) h2
    omega
  · obtain ⟨-, hU⟩ := hn
    have h1 : Nat.card X = ordTwistedA 2 (2 ^ n) :=
      (uc22p21k_card_quot_center hc).symm.trans (hU.card_eq_lieOrd (by norm_num))
    obtain ⟨-, hf, -, hne⟩ := hU.admissible
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have hn1 : n = 1 := by omega
      subst hn1
      exact hne (by simp)
    obtain ⟨r, hr, hm⟩ := (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) (by norm_num)
      hf).two
    have h2 : 2 ^ (n * (2 * (2 + 1) / 2)) * r = 2 ^ 3 * 21945 := by
      rw [← hm, ← h1, hcard]
      norm_num
    have := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr (by decide : Odd 21945) h2
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
