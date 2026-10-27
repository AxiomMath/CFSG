module

public import CFSG.Permutation.FiveTransitive.LargePrimeCyclePrimitive
public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.PCycleJordan
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.NormNum.NatFactorial

public section

namespace CFSG

namespace FiveTransitive.A9TenQuotientTransitive
open MulAction

private theorem excluded_of_alternating_le
    {F E : Type*} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E = 10)
    (B : Subgroup (Equiv.Perm E)) (tau : B →* alternatingGroup F)
    (htau : Function.Surjective tau) (hAlt : alternatingGroup E ≤ B) : False := by
  classical
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsSimpleGroup (alternatingGroup E) := alternatingGroup.isSimpleGroup (by omega)
  have hA : Nat.card (alternatingGroup F) = 181440 := by
    rw [nat_card_alternatingGroup,hF]; norm_num [Nat.factorial]
  have hAE : Nat.card (alternatingGroup E) = 1814400 := by
    rw [nat_card_alternatingGroup,hE]; norm_num [Nat.factorial]
  let f := tau.comp (Subgroup.inclusion hAlt)
  have htriv (g : alternatingGroup E) : f g = 1 := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
    · have hi := (MonoidHom.ker_eq_bot_iff f).mp h
      have hb := Nat.card_le_card_of_injective f hi
      rw [hA,hAE] at hb
      omega
    · have hg : g ∈ f.ker := by rw [h]; trivial
      exact hg
  let K := tau.ker.map B.subtype
  have hAK : alternatingGroup E ≤ K := by
    intro g hg
    exact ⟨⟨g,hAlt hg⟩,htriv ⟨g,hg⟩,rfl⟩
  have hl := Nat.le_of_dvd (Nat.card_pos (α := K)) (Subgroup.card_dvd_of_le hAK)
  rw [hAE,Subgroup.card_map_of_injective B.subtype_injective] at hl
  have hp := tau.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr htau,Subgroup.card_top,hA] at hp
  have hb := Nat.card_le_card_of_injective B.subtype B.subtype_injective
  rw [Nat.card_perm,hE] at hb
  norm_num [Nat.factorial] at hb
  rw [← Nat.card_eq_fintype_card] at hb
  omega

theorem excluded
    {F E : Type*} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E = 10)
    (B : Subgroup (Equiv.Perm E)) [IsPretransitive B E]
    (tau : B →* alternatingGroup F) (htau : Function.Surjective tau) : False := by
  classical
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hdA : 7 ∣ Nat.card (alternatingGroup F) := by
    rw [nat_card_alternatingGroup,hF]; norm_num [Nat.factorial]
  have hd := hdA.trans (Subgroup.card_dvd_of_surjective htau)
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := B) 7 hd
  have hg : orderOf (u : Equiv.Perm E) = 7 := (Subgroup.orderOf_coe u).trans hu
  have hc : (u : Equiv.Perm E).IsCycle := Equiv.Perm.isCycle_of_prime_order
    (by rw [hg]; decide) (by
      have hs := Finset.card_le_univ (u : Equiv.Perm E).support
      rw [← Nat.card_eq_fintype_card,hE] at hs
      rw [hg]
      omega)
  have hs : (u : Equiv.Perm E).support.card = 7 := hc.orderOf.symm.trans hg
  have hp := LargePrimeCyclePrimitive.isPreprimitive B u.property hc
    (by rw [hs]; decide) (by rw [hs,hE]; decide)
  have halt := OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
    hp (by decide : Nat.Prime 7) (by omega) hc hs u.property
  exact excluded_of_alternating_le hF hE B tau htau halt

end FiveTransitive.A9TenQuotientTransitive

end CFSG
