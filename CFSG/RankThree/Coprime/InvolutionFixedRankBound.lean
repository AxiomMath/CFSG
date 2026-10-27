module

public import CFSG.Foundations.Basic
public import CFSG.RankThree.Coprime.DihedralProductWitness

public section

namespace CFSG.RankThree.Coprime

open Subgroup
open scoped IsMulCommutative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem le_pRank_of_isElementaryAbelian {p : ℕ} (hp : 1 < p) {H : Type*} [Group H] [Finite H]
    {E : Subgroup H} (hE : IsElementaryAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ pRank p H := by
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card H := Subgroup.card_le_card_group B

theorem mem_fixedPointSubgroup_zpowers {A P : Type*} [Group A] [Group P]
    [MulDistribMulAction A P] {a : A} {x : P} (h : a • x = x) :
    x ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers a) P := by
  rintro ⟨g, hg⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have ha : a ∈ MulAction.stabilizer A x := h
  exact (MulAction.stabilizer A x).zpow_mem ha m

theorem class_two_involution_fixed_rank_bound {p : ℕ} [hpF : Fact p.Prime] (hodd : Odd p)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P) (hexp : Monoid.exponent P ∣ p)
    (hclass : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥)
    {A : Type*} [CommGroup A] [Finite A] [Module (ZMod 2) (Additive A)] (n m : ℕ)
    (hA : Nat.card A = 2 ^ n) [MulDistribMulAction A P] [FaithfulSMul A P]
    (hm : ∀ a : A, a ≠ 1 → pRank p (CFSG.fixedPointSubgroup (Subgroup.zpowers a) P) ≤ m) :
    n ≤ m + 1 ∧
      (1 ≤ n → ∃ a : A, a ≠ 1 ∧
        n - 1 ≤ pRank p (CFSG.fixedPointSubgroup (Subgroup.zpowers a) P)) := by
  classical
  have key : 1 ≤ n → ∃ a : A, a ≠ 1 ∧
      n - 1 ≤ pRank p (CFSG.fixedPointSubgroup (Subgroup.zpowers a) P) := by
    intro hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨U, hU, hUinv, -, aB, uB, hrel, -⟩ :=
      class_two_dihedral_product_witness hodd hP hexp hclass (k + 1) hA
    set a : A := Additive.toMul (aB (Fin.last k)) with ha_def
    have ha1 : a ≠ 1 := by
      intro h
      apply aB.ne_zero (Fin.last k)
      rw [← ofMul_toMul (aB (Fin.last k)), ← ha_def, h, ofMul_one]
    have hfix : ∀ j : Fin k,
        invariantSubgroupRep p U hUinv a (uB (Fin.castSucc j)) = uB (Fin.castSucc j) := by
      intro j
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [coe_toMul_invariantSubgroupRep, hrel]
      simp [(Fin.castSucc_lt_last j).ne']
    let ν : Multiplicative (Fin k → ZMod p) →* P := U.subtype.comp
      (AddMonoidHom.toMultiplicativeLeft
        (Fintype.linearCombination (ZMod p) (uB ∘ Fin.castSucc)).toAddMonoidHom)
    have hν : ∀ c, ν (Multiplicative.ofAdd c) =
        ((Additive.toMul (∑ j, c j • uB (Fin.castSucc j)) : U) : P) := fun c => rfl
    have hνfix : ∀ c, ν c ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers a) P := by
      intro c
      apply mem_fixedPointSubgroup_zpowers
      have h1 : invariantSubgroupRep p U hUinv a
          (∑ j, (Multiplicative.toAdd c) j • uB (Fin.castSucc j)) =
          ∑ j, (Multiplicative.toAdd c) j • uB (Fin.castSucc j) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, hfix]
      rw [← ofAdd_toAdd c, hν, ← coe_toMul_invariantSubgroupRep p U hUinv, h1]
    let ν' := ν.codRestrict (CFSG.fixedPointSubgroup (Subgroup.zpowers a) P) hνfix
    have hνinj : Function.Injective ν' := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : ν x = 1 := congrArg Subtype.val hx
      rw [← ofAdd_toAdd x, hν] at hx'
      have h0 : ∑ j, (Multiplicative.toAdd x) j • uB (Fin.castSucc j) = 0 := by
        have h1 : Additive.toMul (∑ j, (Multiplicative.toAdd x) j • uB (Fin.castSucc j)) = 1 :=
          Subtype.ext hx'
        exact h1
      have hli := uB.linearIndependent.comp _ (Fin.castSucc_injective k)
      have h2 := Fintype.linearIndependent_iff.mp hli _ h0
      rw [← ofAdd_toAdd x]
      have h3 : Multiplicative.toAdd x = 0 := funext h2
      rw [h3, ofAdd_zero]
    have hEexp : Monoid.exponent ν'.range ∣ p := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      rintro ⟨_, c, rfl⟩
      apply Subtype.ext
      have hc : c ^ p = 1 := by
        have h := ZModModule.char_nsmul_eq_zero p (Multiplicative.toAdd c)
        rw [← ofAdd_toAdd c, ← ofAdd_nsmul, h, ofAdd_zero]
      change ν' c ^ p = 1
      rw [← map_pow, hc, map_one]
    have hEcard : Nat.card ν'.range = p ^ k := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hνinj).toEquiv,
        Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    refine ⟨a, ha1, ?_⟩
    rw [Nat.add_sub_cancel]
    exact le_pRank_of_isElementaryAbelian hpF.out.one_lt ⟨hEexp⟩ hEcard
  refine ⟨?_, key⟩
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · omega
  · obtain ⟨a, ha1, ha⟩ := key hpos
    have := hm a ha1
    omega

end CFSG.RankThree.Coprime
