module

public import CFSG.RankThree.PartOne.S11.CatalogLeaves
public import CFSG.RankThree.PartOne.SPOR.PlanesGeneric
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG
open scoped commutatorElement

theorem isElementaryAbelian_of_le {X : Type*} [Group X] {p : ℕ} {E K : Subgroup X}
    [IsElementaryAbelian p E] (hKE : K ≤ E) : IsElementaryAbelian p K :=
  CFSG.IsElementaryAbelian.of_le inferInstance hKE

theorem exists_plane_containing {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {E : Subgroup X} [IsElementaryAbelian p E] (hcard : p ^ 2 ≤ Nat.card E) {x : X} (hx : x ∈ E)
    (hx1 : x ≠ 1) :
    ∃ E0 : Subgroup X, E0 ≤ E ∧ x ∈ E0 ∧ Nat.card E0 = p ^ 2 ∧ IsElementaryAbelian p E0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hEp
  have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hk ▸ hcard)
  have hdvd : p ^ 2 ∣ Nat.card E := by
    rw [hk]
    exact pow_dvd_pow p hk2
  have hox : orderOf x = p :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hx1
  have hzp : Nat.card (Subgroup.zpowers x) ∣ p ^ 2 := by
    rw [Nat.card_zpowers, hox]
    exact dvd_pow_self p two_ne_zero
  have hzE : Subgroup.zpowers x ≤ E := Subgroup.zpowers_le.2 hx
  obtain ⟨K, hKc, hzK, hKE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp hzp hdvd hzE
  exact ⟨K, hKE, hzK (Subgroup.mem_zpowers x), hKc, isElementaryAbelian_of_le hKE⟩

theorem nonabelian_of_plane {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] {p : ℕ}
    (hp : p.Prime) {E : Subgroup X} [IsElementaryAbelian p E] (hcard : p ^ 2 ≤ Nat.card E) :
    ∃ a b : X, a * b ≠ b * a := by
  apply not_commutative_of_simple_of_not_prime
  intro hq
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (IsElementaryAbelian.isPGroup p E)
  have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hk ▸ hcard)
  have hpX : p ∣ Nat.card X :=
    ((dvd_pow_self p (by omega : k ≠ 0)).trans (hk ▸ Subgroup.card_subgroup_dvd_card E))
  have hpq : p = Nat.card X := (Nat.prime_dvd_prime_iff_eq hp hq).1 hpX
  have hle : Nat.card E ≤ Nat.card X := Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card E)
  have hp2 : p < p ^ 2 := by nlinarith [hp.two_le]
  omega

theorem item613_false_of_planes {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpl : (∃ a b : X, a * b ≠ b * a) → ∀ (E' : Subgroup (MulAut X)) (U : Subgroup X),
      PlaneOn p E' U → PlaneCentralizes E' U)
    {E : Subgroup X} [IsElementaryAbelian p E] (hcard : p ^ 2 ≤ Nat.card E) {S : Subgroup X}
    (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S) (hEN : E ≤ Subgroup.normalizer (S : Set X))
    (hSE : ⁅S, E⁆ = S) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hnab := nonabelian_of_plane hp hcard
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    conj_injective_of_trivial_center (trivial_center_of_simple hnab)
  have hcent : ∀ x ∈ E, ∀ u ∈ S, x * u * x⁻¹ = u := by
    intro x hx u hu
    by_cases hx1 : x = 1
    · simp [hx1]
    obtain ⟨E0, hE0E, hxE0, hE0card, hE0el⟩ := exists_plane_containing hp hcard hx hx1
    have hplane : PlaneOn p (E0.map (MulAut.conj : X →* MulAut X)) S :=
      { prime := hp
        three_lt := by omega
        elementary := IsElementaryAbelian.map _
        card := by rw [Subgroup.card_map_of_injective hinj, hE0card]
        two_group := hS2
        normalized := by
          intro e he v hv
          obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 he
          have h := (Subgroup.mem_normalizer_iff.1 (hEN (hE0E ht)) v).1 hv
          simpa [MulAut.conj_apply] using h }
    have h := hpl hnab _ S hplane (MulAut.conj x) (Subgroup.mem_map_of_mem _ hxE0) u hu
    simpa [MulAut.conj_apply] using h
  have hEc : E ≤ Subgroup.centralizer (S : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h := hcent x hx u hu
    calc u * x = (x * u * x⁻¹) * x := by rw [h]
      _ = x * u := by group
  have hcomm : ⁅E, S⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hEc
  apply hS1
  rw [← hSE, Subgroup.commutator_comm]
  exact hcomm

end CFSG.RankThree.PartOne.SPOR
