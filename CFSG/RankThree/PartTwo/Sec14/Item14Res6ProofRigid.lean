module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesHJ
public import CFSG.RankThree.PartTwo.Sec17.Item17Res8ProofJ2
public import CFSG.RankThree.PartTwo.KFacts.ONanKS17J2CentralizerNine

public section

namespace CFSG.RankThree.PartTwo.Sec14

namespace Res6Rigid

variable {X : Type} [Group X]

theorem pow_apply_eq_of_forall {E : Subgroup X} {τ : MulAut X} (hτ : ∀ e ∈ E, τ e = e)
    (k : ℕ) : ∀ e ∈ E, (τ ^ k) e = e := by
  intro e he
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, MulAut.mul_apply, hτ e he, ih]

theorem mem_centralizer_of_conj_fix {E : Subgroup X} {x : X}
    (h : ∀ e ∈ E, MulAut.conj x e = e) : x ∈ Subgroup.centralizer (E : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h1 : x * e * x⁻¹ = e := h e he
  calc e * x = x * e * x⁻¹ * x := by rw [h1]
    _ = x * e := by group

end Res6Rigid

open Res6Rigid in
theorem ks142J2Rigid :
    KS142J2Rigid := by
  intro X _ _ hX E hE9 τ hτE n hn hτn
  classical
  have hfin : Finite (MulAut X) :=
    Finite.of_injective (fun σ : MulAut X => (σ : X → X)) DFunLike.coe_injective
  by_contra hτ1
  have hord : orderOf τ ∣ n := orderOf_dvd_of_pow_eq_one hτn
  have hord1 : orderOf τ ≠ 1 := fun h => hτ1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hord1
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hn (hpd.trans hord)
  set σ := τ ^ (orderOf τ / p) with hσ
  have hσord : orderOf σ = p := orderOf_pow_orderOf_div (orderOf_pos τ).ne' hpd
  have hσE : ∀ e ∈ E, σ e = e := pow_apply_eq_of_forall hτE _
  have hσp : σ ^ p = 1 := by
    rw [← hσord]
    exact pow_orderOf_eq_one σ
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have h1 := KFacts.ks152J2InvolNine X hX E hE9 σ hσp hσE
    rw [h1, orderOf_one] at hσord
    omega
  · have hidx := Sec17.Proof17Res8.index_inner_of_j2 hX
    obtain ⟨x, hx⟩ := Sec17.Proof17Res8.mem_inner_of_odd_pow hidx σ hodd
      (by rw [hσp]; exact one_mem _)
    have hxC : x ∈ Subgroup.centralizer (E : Set X) :=
      mem_centralizer_of_conj_fix fun e he => by rw [hx]; exact hσE e he
    have hxE : x ∈ E := KFacts.ks17J2CentralizerNine X hX E hE9 hxC
    have hx9 : x ^ 9 = 1 := by
      have h := pow_card_eq_one' (G := E) (x := ⟨x, hxE⟩)
      rw [hE9] at h
      exact congrArg Subtype.val h
    have hσ9 : σ ^ 9 = 1 := by
      rw [← hx, ← map_pow, hx9, map_one]
    have hp9 : p ∣ 3 ^ 2 := by
      rw [← hσord]
      exact orderOf_dvd_of_pow_eq_one (by norm_num; exact hσ9)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hp9))

end CFSG.RankThree.PartTwo.Sec14
