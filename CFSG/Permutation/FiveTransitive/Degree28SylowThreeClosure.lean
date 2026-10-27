module

public import CFSG.Permutation.FiveTransitive.Degree28WitnessClosure

public section

namespace CFSG

namespace FiveTransitive.Degree28SylowThreeClosure

open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hScard : Nat.card S = 3) :
    alternatingGroup X ≤ P := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hdiv : 3 ∣ Nat.card S := by rw [hScard]
  obtain ⟨q,hq⟩ := exists_prime_orderOf_dvd_card' 3 hdiv
  let r : P := q.val.val
  have hrH : orderOf q.val = 3 := (Subgroup.orderOf_coe q).trans hq
  have hr : orderOf r = 3 := (Subgroup.orderOf_coe q.val).trans hrH
  have hg : orderOf r.val = 3 := (Subgroup.orderOf_coe r).trans hr
  have hZle : Subgroup.zpowers q.val ≤ (S : Subgroup (fixingSubgroup P s)) :=
    Subgroup.zpowers_le.mpr q.property
  have hZcard : Nat.card (Subgroup.zpowers q.val) = 3 := by rw [Nat.card_zpowers,hrH]
  have hZe : Subgroup.zpowers q.val = (S : Subgroup (fixingSubgroup P s)) :=
    Subgroup.eq_of_le_of_card_ge hZle (by rw [hZcard,hScard])
  have hRSP : PrimeCyclicFixedAction.cyclicSubgroup P r = Degree24.sylowImage X P s S := by
    change Subgroup.zpowers r = (S : Subgroup (fixingSubgroup P s)).map (fixingSubgroup P s).subtype
    rw [← hZe,MonoidHom.map_zpowers]
    rfl
  have hfix : s ⊆ Function.fixedPoints r.val := by
    intro x hx
    exact (mem_fixingSubgroup_iff P).mp q.val.property x hx
  have hfive : 5 ≤ Fintype.card (Function.fixedPoints r.val) := by
    have hh := Set.ncard_le_ncard hfix
    rw [hs,← Nat.card_coe_set_eq,Nat.card_eq_fintype_card] at hh
    exact hh
  have hprime : Nat.Prime (orderOf r.val) := by rw [hg]; norm_num
  obtain ⟨m,hm⟩ := Equiv.Perm.cycleType_prime_order hprime
  have hsupport : r.val.support.card = 3 * r.val.cycleType.card := by
    rw [← r.val.sum_cycleType,hm,hg]
    simp [Nat.mul_comm]
    omega
  have hfixed : Fintype.card (Function.fixedPoints r.val) = 28 - r.val.support.card := by
    rw [Equiv.Perm.card_fixedPoints,r.val.sum_cycleType,hcard]
  have hsle := Finset.card_le_univ r.val.support
  rw [hcard] at hsle
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  by_cases hsmall : r.val.support.card ≤ 18
  · exact Degree28WitnessClosure.alternatingGroup_le_of_order_three_support_le_eighteen
      hcard P hexp s hs S hScard r.val r.property hg hsmall
  · have hf : Fintype.card (Function.fixedPoints r.val) = 7 := by omega
    have hc : r.val.cycleType.card = 7 := by omega
    rcases Degree28BlockEscape.alternating_or_exists_order_three_support_le_eighteen
      hcard P hexp s hs S hScard r hRSP hg hf hc with hAlt | ⟨g,hgP,hgo,hgs⟩
    · exact hAlt
    · exact Degree28WitnessClosure.alternatingGroup_le_of_order_three_support_le_eighteen
        hcard P hexp s hs S hScard g hgP hgo hgs

end FiveTransitive.Degree28SylowThreeClosure

end CFSG
