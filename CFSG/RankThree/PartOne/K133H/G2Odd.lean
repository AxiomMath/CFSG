module

public import CFSG.RankThree.PartOne.K133H.G2Core
public import CFSG.RankThree.PartOne.K133.G2Odd
public import CFSG.RankThree.PartOne.K133.G2Char
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
import CFSG.RankThree.PartOne.Q1327T.ItemBasic

public section

namespace CFSG.RankThree.PartOne.K133H

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133 CFSG.RankThree.PartOne.Q1327T
  CFSG.RankThree.PartOne.K133B CFSG.Timmesfeld.ExceptionalOrders
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem simple_nonabelian_of_model {K : Type} [Group K] {g : ℕ}
    (hm : StatedClassicalModel K .PSL 2 2 g) :
    IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a :=
  CFSG.RankThree.PartOne.Q1327T.simple_nonab_of_model hm

theorem mem_normalizer_of_commutes {G : Type} [Group G] {U : Subgroup G} {k : G}
    (hcomm : ∀ x ∈ U, x * k = k * x) : k ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have e : k * x * k⁻¹ = x := by rw [← hcomm x hx, mul_inv_cancel_right]
    rw [e]
    exact hx
  · intro hx
    have h : k * x * k⁻¹ * k = k * (k * x * k⁻¹) := hcomm _ hx
    have h1 : k * x = k * (k * x * k⁻¹) := by rw [← h]; group
    have e : x = k * x * k⁻¹ := mul_left_cancel h1
    rw [e]
    exact hx

set_option linter.unusedSectionVars false

theorem row8OddAt_leaf4_zero : Row8OddAt (K133.leaf4 0) := by
  intro Q _ _ p g Ē hp11 hZ hX h
  obtain ⟨q, hq2, hq1, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have := h.elem
  have hmodel : ChevalleyExceptionalModel (Q ⧸ Subgroup.center Q) .G2 q.p q.exponent :=
    CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e0
      (CFSG.RankThree.PartTwo.Sec4.Census.chevalleyExceptionalModel_G2_of_odd q hv hq2)
  obtain ⟨K, _, _, hK, ⟨θ⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hmodel.2
  have hKc : Nat.card K = q.p := by rw [hK, hq1, pow_one]
  have hchar : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      q.exponent_pos hK
  have hK2 : (2 : K) ≠ 0 := by
    intro h0
    have h1 := (CharP.cast_eq_zero_iff K q.p 2).1 (by exact_mod_cast h0)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1)
  have hKodd : Odd (Nat.card K) := by rw [hKc]; exact q.prime_p.odd_of_ne_two hq2
  let ce : Q ≃* Q ⧸ Subgroup.center Q :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let eQ : Q ≃* adjointGroup .G2 K := ce.trans θ
  have hEel : IsElementaryAbelian p (Ē.map eQ.toMonoidHom) := IsElementaryAbelian.map _
  have hEcard : Nat.card (Ē.map eQ.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective eQ.injective, h.card]
  by_cases hpr : p = q.p
  ·
    exfalso
    obtain ⟨c, hcE, hc1, Kb, x, hKbc, -, hKbm, -, -, -⟩ := h.conf
    obtain ⟨hKbs, hKbn⟩ := simple_nonabelian_of_model hKbm
    have hcp : c ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := Ē) c hcE
    let Kb' : Subgroup (adjointGroup .G2 K) := Kb.map eQ.toMonoidHom
    let ε : Kb ≃* Kb' := Subgroup.equivMapOfInjective Kb eQ.toMonoidHom eQ.injective
    have : IsSimpleGroup Kb' := ε.symm.isSimpleGroup
    have hKn' : ∃ a b : Kb', a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hKbn
      exact ⟨ε a, ε b, fun h' => hab (ε.injective (by rw [map_mul, map_mul]; exact h'))⟩
    have hec : eQ c ≠ 1 := fun h1 => hc1 (eQ.injective (by rw [h1, map_one]))
    have hecp : eQ c ^ p = 1 := by rw [← map_pow, hcp, map_one]
    have hUc : Nat.card (Subgroup.zpowers (eQ c)) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hecp hec]
    have hUp : IsPGroup q.p (Subgroup.zpowers (eQ c)) := by
      rw [← hpr]
      exact IsPGroup.of_card (n := 1) (by rw [hUc, pow_one])
    have hU : Subgroup.zpowers (eQ c) ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]
      exact hec
    refine g2_no_simple_normalizing_pSubgroup K hK2 (U := Subgroup.zpowers (eQ c)) (Kb := Kb')
      hKn' hU hUp ?_
    intro k hk
    obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.1 hk
    apply mem_normalizer_of_commutes
    intro u hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    have hk₀c : k₀ * c = c * k₀ := by
      have := Subgroup.mem_centralizer_iff.1 (hKbc hk₀) c (Set.mem_singleton c)
      exact this.symm
    have hcomm : Commute (eQ c) (eQ k₀) := by
      show eQ c * eQ k₀ = eQ k₀ * eQ c
      rw [← map_mul, ← map_mul, hk₀c.symm]
    exact (hcomm.zpow_left n).eq
  · have hpK : ¬ p ∣ Nat.card K := by
      rw [hKc]
      intro hd
      exact hpr ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 hd)
    by_cases hd : p ∣ Nat.card K ^ 2 - 1
    · exact row8OddConcl_of_G2 (ℓ := q.p) h eQ hpK hd
    · exfalso
      have hdvd : p ∣ Nat.card (adjointGroup .G2 K) := by
        have h1 := Subgroup.card_subgroup_dvd_card (Ē.map eQ.toMonoidHom)
        rw [hEcard] at h1
        exact (dvd_pow_self p two_ne_zero).trans h1
      have hcyc := cyclic_pSubgroups_G2_odd K hKodd hp hp5 hpK hdvd hd (Ē.map eQ.toMonoidHom)
        (IsElementaryAbelian.isPGroup p _)
      have hexp : Monoid.exponent ↥(Ē.map eQ.toMonoidHom) ∣ p :=
        IsElementaryAbelian.exponent_dvd_p p _
      rw [IsCyclic.exponent_eq_card] at hexp
      have hle := Nat.le_of_dvd hp.pos hexp
      rw [hEcard] at hle
      have h2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      rw [pow_one] at h2
      omega

end CFSG.RankThree.PartOne.K133H
