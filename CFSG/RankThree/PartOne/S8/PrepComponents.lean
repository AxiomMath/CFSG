module

public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic
import CFSG.RankThree.GroupTheory.SteinbergBKPrimeElementsFixQuotientComponents
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.PartOne.S8.QuotientTransfer
import CFSG.RankThree.PartOne.S10.SelectedPrimeFixCoprimeQuotientComponents

public section

namespace CFSG.RankThree.PartOne.S8

open CFSG
open CFSG.RankThree.GroupTheory.SteinbergBK
  (selected_prime_elements_fix_prime_divisible_quotient_components)
open scoped commutatorElement

theorem plane_normalizes_quotient_component {X : Type} [Group X] [Finite X]
    (hX : CFSG.Assembly.evenRank X ≤ 3) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (N : Subgroup X) [N.Normal] (hN : ¬ p ∣ Nat.card N) {E : Subgroup (X ⧸ N)}
    (hE : IsPGroup p E) {L : Subgroup (X ⧸ N)} (hL : IsComponent L) :
    E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) := by
  have : Fact p.Prime := ⟨hp⟩
  intro e he
  obtain ⟨n, hn⟩ := hE.exists_orderOf_eq_pow ⟨e, he⟩
  have hord : ∃ k : ℕ, orderOf e = p ^ k :=
    ⟨n, (Subgroup.orderOf_coe (⟨e, he⟩ : E)).trans hn⟩
  obtain ⟨x, rfl, hx⟩ := exists_lift_orderOf_pow hp N hord
  by_cases hpL : p ∣ Nat.card (L ⧸ Subgroup.center L)
  · have hp2 : p ≠ 2 := by omega
    have hrank : CFSG.Assembly.RankThreeEven.localRank p X ≤ 3 :=
      (CFSG.RankThree.OddKernel.localRank_le_evenRank hp hp2).trans hX
    exact (selected_prime_elements_fix_prime_divisible_quotient_components hp hp3 N hN hrank hL
      hpL).1 x hx
  · exact selected_prime_elements_fix_coprime_quotient_components X hX p hp hp3 N hN x hx L hL
      hpL

theorem commutator_normalizes_component {Q : Type*} [Group Q] {U E : Subgroup Q}
    (hE : ∀ L : Subgroup Q, IsComponent L → E ≤ Subgroup.normalizer (L : Set Q))
    {L : Subgroup Q} (hL : IsComponent L) : ⁅U, E⁆ ≤ Subgroup.normalizer (L : Set Q) := by
  rw [Subgroup.commutator_le]
  intro u _ e he
  have h1 : u * e * u⁻¹ ∈ Subgroup.normalizer (L : Set Q) := by
    have h := hE _ (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj u⁻¹) hL) he
    rw [← Subgroup.map_equiv_normalizer_eq] at h
    obtain ⟨z, hz, hze⟩ := h
    have hzu : u * e * u⁻¹ = z := by
      rw [← hze]
      simp [mul_assoc]
    rw [hzu]
    exact hz
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem (hE L hL he))

end CFSG.RankThree.PartOne.S8
