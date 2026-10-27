module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Core
public import CFSG.Quasithin.SteinbergCBAlternatingAut
import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Alt

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open Equiv Equiv.Perm
open CFSG.Quasithin.SteinbergCB (conjPerm conjPerm_apply)
open CFSG.RankThree.PartTwo.Sec4.Ronan148R (le_range_ofSubtype_of_card_cycleType_le)
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (not_three_dvd_outer_alternatingGroup)

theorem goodJ2_alternating {n : ℕ} {τ : Equiv.Perm (Fin n)}
    (hk : Multiset.card τ.cycleType ≤ 4) (hΩ : Fintype.card ↥(τ.supportᶜ) ≤ 9) :
    GoodJ2 (autFix (conjPerm n τ)) := by
  let ψ : alternatingGroup ↥(τ.supportᶜ) ≃* (alternatingGroup.ofSubtype τ.supportᶜ).range :=
    MonoidHom.ofInjective alternatingGroup.ofSubtype_injective
  refine goodJ2_of_perfect_le (E := (alternatingGroup.ofSubtype τ.supportᶜ).range)
    (fun K hK _ => le_range_ofSubtype_of_card_cycleType_le hk hK) fun hdvd => ?_
  have hle : Nat.card (alternatingGroup.ofSubtype τ.supportᶜ).range ≤ (9 : ℕ).factorial := by
    rw [← Nat.card_congr ψ.toEquiv]
    calc Nat.card (alternatingGroup ↥(τ.supportᶜ)) ≤ Nat.card (Perm ↥(τ.supportᶜ)) :=
          Subgroup.card_le_card_group _
      _ = (Fintype.card ↥(τ.supportᶜ)).factorial := by
          rw [Nat.card_perm, Nat.card_eq_fintype_card]
      _ ≤ (9 : ℕ).factorial := Nat.factorial_le hΩ
  have hpos : 0 < Nat.card (alternatingGroup.ofSubtype τ.supportᶜ).range := Nat.card_pos
  have h9 : (9 : ℕ).factorial = 362880 := rfl
  have hge := Nat.le_of_dvd hpos hdvd
  omega

private theorem goodJ2_alternating_centralizer {n : ℕ} (hn : n ≤ 12)
    (s : alternatingGroup (Fin n)) (hs : orderOf s = 3) :
    GoodJ2 (Subgroup.centralizer ({s} : Set (alternatingGroup (Fin n)))) := by
  have hconj : MulAut.conj s = conjPerm n (s : Perm (Fin n)) := by
    ext x
    rw [conjPerm_apply]
    rfl
  rw [← RonanK429H.autFix_conj, hconj]
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
  exact goodJ2_alternating (by omega) (by rw [hΩ]; omega)

theorem rowOfK9_alternating {n : ℕ} (hn5 : 5 ≤ n) (hn : n ≤ 12) :
    RowOfK9 (alternatingGroup (Fin n)) := by
  intro S _ _ hs hna ⟨e⟩
  haveI := hs
  exact noCfgJ2_of_model e (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (RonanK429H.not_three_dvd_outer_of_mulEquiv e (not_three_dvd_outer_alternatingGroup hn5))
    fun y hy => goodJ2_alternating_centralizer hn y hy

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
