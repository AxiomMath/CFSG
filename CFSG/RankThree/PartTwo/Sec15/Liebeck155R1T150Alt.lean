module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150LieChev
import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Alt
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Core

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open Equiv Equiv.Perm
open CFSG.Quasithin.SteinbergCB (conjPerm conjPerm_apply)
open CFSG.RankThree.PartTwo.Sec4.Ronan148R (le_range_ofSubtype_of_card_cycleType_le)
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (not_three_dvd_outer_alternatingGroup
  range_ofSubtype_le_autFix)

theorem k150_goodAll_of_le_simple {J : Type} [Group J] [Nontrivial J] {S : Type} [Group S]
    {C E : Subgroup S} (hEC : E ≤ C) [hEs : IsSimpleGroup E] (hEJ : IsEmpty (E ≃* J))
    (hle : ∀ K : Subgroup S, K ≤ C → Group.IsPerfect K → K ≤ E) : GoodAllFor J C := by
  intro P hPC hPs hPp N hN
  refine ⟨fun e => ?_⟩
  have hPE : P ≤ E := hle P hPC hPp
  have hsE : (P.subgroupOf E).IsSubnormal := by
    have h1 := hPs.comap (Subgroup.inclusion hEC)
    have h2 : (P.subgroupOf C).comap (Subgroup.inclusion hEC) = P.subgroupOf E := by
      ext a
      simp [Subgroup.mem_subgroupOf]
    rwa [h2] at h1
  rcases hsE.eq_bot_or_top_of_isSimpleGroup hEs with hbot | htop
  · rw [Subgroup.subgroupOf_eq_bot] at hbot
    have hP0 : P = ⊥ := by
      rw [eq_bot_iff]
      intro k hk
      exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hbot hk (hPE hk))
    subst hP0
    have : Subsingleton (↥(⊥ : Subgroup S) ⧸ N) := inferInstance
    have : Subsingleton J := e.symm.injective.subsingleton
    exact not_subsingleton J ‹_›
  · have hPeq : P = E := le_antisymm hPE (Subgroup.subgroupOf_eq_top.mp htop)
    subst hPeq
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN0 | hN1
    · subst hN0
      exact hEJ.false ((QuotientGroup.quotientBot (G := ↥P)).symm.trans e)
    · subst hN1
      have : Subsingleton (↥P ⧸ (⊤ : Subgroup ↥P)) := QuotientGroup.subsingleton_quotient_top
      have : Subsingleton J := e.symm.injective.subsingleton
      exact not_subsingleton J ‹_›

section Fixed

variable {n : ℕ} {τ : Perm (Fin n)}

theorem k150_goodAll_alternating_of_card_gt {J : Type} [Group J] {m : ℕ}
    (hk : Multiset.card τ.cycleType ≤ 4) (hΩ : Fintype.card ↥(τ.supportᶜ) ≤ m)
    (hJ : m.factorial < Nat.card J) : GoodAllFor J (autFix (conjPerm n τ)) := by
  let ψ : alternatingGroup ↥(τ.supportᶜ) ≃* (alternatingGroup.ofSubtype τ.supportᶜ).range :=
    MonoidHom.ofInjective alternatingGroup.ofSubtype_injective
  refine k150_goodAll_of_perfect_le (E := (alternatingGroup.ofSubtype τ.supportᶜ).range)
    (fun K hK hKp => have := hKp; le_range_ofSubtype_of_card_cycleType_le hk hK) fun hdvd => ?_
  have hle : Nat.card (alternatingGroup.ofSubtype τ.supportᶜ).range ≤ m.factorial := by
    rw [← Nat.card_congr ψ.toEquiv]
    calc Nat.card (alternatingGroup ↥(τ.supportᶜ)) ≤ Nat.card (Perm ↥(τ.supportᶜ)) :=
          Subgroup.card_le_card_group _
      _ = (Fintype.card ↥(τ.supportᶜ)).factorial := by
          rw [Nat.card_perm, Nat.card_eq_fintype_card]
      _ ≤ m.factorial := Nat.factorial_le hΩ
  have hpos : 0 < Nat.card (alternatingGroup.ofSubtype τ.supportᶜ).range := Nat.card_pos
  have hge := Nat.le_of_dvd hpos hdvd
  omega

theorem k150_goodAll_alternating_a7 (hk : Multiset.card τ.cycleType ≤ 4)
    (hΩ : Fintype.card ↥(τ.supportᶜ) ≤ 9) (h7 : Fintype.card ↥(τ.supportᶜ) ≠ 7) :
    GoodAllFor (alternatingGroup (Fin 7)) (autFix (conjPerm n τ)) := by
  by_cases h6 : Fintype.card ↥(τ.supportᶜ) ≤ 6
  · refine k150_goodAll_alternating_of_card_gt (m := 6) hk h6 ?_
    rw [k150_card_alternating_seven]
    decide
  · have h8 : 8 ≤ Fintype.card ↥(τ.supportᶜ) := by omega
    let ψ : alternatingGroup ↥(τ.supportᶜ) ≃* (alternatingGroup.ofSubtype τ.supportᶜ).range :=
      MonoidHom.ofInjective alternatingGroup.ofSubtype_injective
    have : IsSimpleGroup (alternatingGroup ↥(τ.supportᶜ)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card]; omega)
    have : IsSimpleGroup (alternatingGroup.ofSubtype τ.supportᶜ).range := ψ.symm.isSimpleGroup
    refine k150_goodAll_of_le_simple (range_ofSubtype_le_autFix τ) ⟨fun e => ?_⟩
      (fun K hK hKp => have := hKp; le_range_ofSubtype_of_card_cycleType_le hk hK)
    have : Nontrivial ↥(τ.supportᶜ) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hc : Nat.card (alternatingGroup ↥(τ.supportᶜ)) = 2520 := by
      rw [Nat.card_congr (ψ.toEquiv.trans e.toEquiv), k150_card_alternating_seven]
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card] at hc
    have h40320 : (8 : ℕ).factorial ≤ (Fintype.card ↥(τ.supportᶜ)).factorial :=
      Nat.factorial_le h8
    have : (8 : ℕ).factorial = 40320 := rfl
    omega

end Fixed

private theorem k150_alt_order_three {n : ℕ} (hn : n ≤ 12) (s : alternatingGroup (Fin n))
    (hs : orderOf s = 3) :
    ∃ τ : Perm (Fin n), MulAut.conj s = conjPerm n τ ∧ Multiset.card τ.cycleType ≤ 4 ∧
      ∃ k : ℕ, 1 ≤ k ∧ 3 * k ≤ n ∧ Fintype.card ↥(τ.supportᶜ) = n - 3 * k := by
  have hconj : MulAut.conj s = conjPerm n (s : Perm (Fin n)) := by
    ext x
    rw [conjPerm_apply]
    rfl
  set τ : Perm (Fin n) := (s : Perm (Fin n)) with hτ
  have hτ3 : τ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs] at h
    have := congrArg Subtype.val h
    simpa [hτ] using this
  have hτ1 : τ ≠ 1 := by
    intro h
    have : s = 1 := Subtype.ext h
    rw [this, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hord : orderOf τ ∣ 3 := orderOf_dvd_of_pow_eq_one hτ3
  have hmem : ∀ m ∈ τ.cycleType, m = 3 := fun m hm => by
    have h2 := two_le_of_mem_cycleType hm
    have hd := (dvd_of_mem_cycleType hm).trans hord
    have : m ≤ 3 := Nat.le_of_dvd (by norm_num) hd
    interval_cases m
    · norm_num at hd
    · rfl
  set k := Multiset.card τ.cycleType with hk
  have hrep : τ.cycleType = Multiset.replicate k 3 := Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hsupp : τ.support.card = 3 * k := by
    rw [← sum_cycleType, hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hsum : 3 * k ≤ n := by
    have := τ.support.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr fun h0 =>
    hτ1 (card_cycleType_eq_zero.mp (by rw [← hk]; exact h0))
  have hΩ : Fintype.card ↥(τ.supportᶜ) = n - 3 * k := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hsupp]
  exact ⟨τ, hconj, by omega, k, hk1, hsum, hΩ⟩

theorem k150_rowAll_alternating_of_card_gt {J : Type} [Group J] (hJ : 362880 < Nat.card J)
    {n : ℕ} (hn5 : 5 ≤ n) (hn : n ≤ 12) : RowAllOfK150 J (alternatingGroup (Fin n)) := by
  refine k150_rowAll_of_inner_model (not_three_dvd_outer_alternatingGroup hn5) fun s hs => ?_
  obtain ⟨τ, hconj, hk, k, hk1, hsum, hΩ⟩ := k150_alt_order_three hn s hs
  rw [← RonanK429H.autFix_conj, hconj]
  exact k150_goodAll_alternating_of_card_gt (m := 9) hk (by rw [hΩ]; omega) hJ

theorem k150_rowAll_alternating_a7 {n : ℕ} (hn5 : 5 ≤ n) (hn : n ≤ 12) (hn10 : n ≠ 10) :
    RowAllOfK150 (alternatingGroup (Fin 7)) (alternatingGroup (Fin n)) := by
  refine k150_rowAll_of_inner_model (not_three_dvd_outer_alternatingGroup hn5) fun s hs => ?_
  obtain ⟨τ, hconj, hk, k, hk1, hsum, hΩ⟩ := k150_alt_order_three hn s hs
  rw [← RonanK429H.autFix_conj, hconj]
  exact k150_goodAll_alternating_a7 hk (by rw [hΩ]; omega) (by rw [hΩ]; omega)

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
