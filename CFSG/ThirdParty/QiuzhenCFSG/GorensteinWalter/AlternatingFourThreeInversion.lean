module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AlternatingFourThreeSubgroupNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# No involution inverts an order-three subgroup of `A₄`

Every subgroup of order three in `A₄` is self-normalizing, so an involution
cannot invert such a subgroup without lying in it.  This is the endpoint
used to eliminate the `|K| = 3` linear branch in the first case.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- No involution of a group isomorphic to `A₄` inverts a nontrivial
`3`-subgroup. -/
public theorem no_involution_inverts_three_subgroup_of_mulEquiv_alternatingGroup_four
    {G : Type u} [Group G] [Finite G]
    (e : Nonempty (G ≃* alternatingGroup (Fin 4)))
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup G) (hPp : IsPGroup p P) (hPne : P ≠ ⊥)
    (t : G) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (htinv : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹) :
    False := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let eG : G ≃* alternatingGroup (Fin 4) := e.some
  let P' : Subgroup (alternatingGroup (Fin 4)) := P.map eG.toMonoidHom
  have hP'p : IsPGroup p P' := IsPGroup.map hPp eG.toMonoidHom
  have hP'ne : P' ≠ ⊥ := by
    intro hbot
    apply hPne
    apply le_bot_iff.mp
    intro x hx
    have hx' : eG x ∈ P' := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hbot] at hx'
    have hx1' : eG x = 1 := Subgroup.mem_bot.mp hx'
    exact eG.injective (by simpa using hx1')
  have hp3 : p = 3 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP'p
    have hdiv : Nat.card P' ∣ Nat.card (alternatingGroup (Fin 4)) := by
      simpa only [Subgroup.card_top] using
        (Subgroup.card_dvd_of_le (H := P') (K := (⊤ : Subgroup (alternatingGroup (Fin 4))))
          le_top)
    have h12 : Nat.card (alternatingGroup (Fin 4)) = 12 :=
      alternatingGroup.card_of_card_eq_four (by simp)
    rw [h12] at hdiv
    have hn0 : n ≠ 0 := by
      intro hn0'
      have hcard1 : Nat.card P' = 1 := by
        rw [hn, hn0']
        norm_num
      apply hP'ne
      exact Subgroup.eq_bot_of_card_eq (H := P') hcard1
    have hpdvd : p ∣ 12 := by
      have h : p ∣ Nat.card P' := by
        rw [hn]
        exact dvd_pow_self p (Nat.ne_of_gt (Nat.pos_of_ne_zero hn0))
      exact h.trans hdiv
    have hp_coprime_four : Nat.Coprime p 4 := by
      have hpne2 : p ≠ 2 := by
        intro hp2
        exact hpodd.not_two_dvd_nat (by simp [hp2])
      have hcop2 : Nat.Coprime p 2 :=
        (hp.odd_of_ne_two hpne2).coprime_two_left.symm
      simpa using hcop2.pow_right 2
    have hp_dvd_three : p ∣ 3 := by
      apply hp_coprime_four.dvd_of_dvd_mul_left
      simpa [pow_two] using hpdvd
    rcases (Nat.dvd_prime (p := 3) (m := p) Nat.prime_three).mp hp_dvd_three with
      hp1 | hp3
    · exact False.elim (hp.ne_one hp1)
    · exact hp3
  subst p
  have hP'card : Nat.card P' = 3 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP'p
    have hdiv : Nat.card P' ∣ Nat.card (alternatingGroup (Fin 4)) := by
      simpa only [Subgroup.card_top] using
        (Subgroup.card_dvd_of_le (H := P') (K := (⊤ : Subgroup (alternatingGroup (Fin 4))))
          le_top)
    have h12 : Nat.card (alternatingGroup (Fin 4)) = 12 :=
      alternatingGroup.card_of_card_eq_four (by simp)
    rw [h12] at hdiv
    have hpos : 0 < Nat.card P' := Nat.card_pos
    have hn0 : n ≠ 0 := by
      intro hn0'
      have hcard1 : Nat.card P' = 1 := by
        rw [hn, hn0']
        norm_num
      apply hP'ne
      exact Subgroup.eq_bot_of_card_eq (H := P') hcard1
    have hnpos : 1 ≤ n := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hn0)
    have hnle : n ≤ 1 := by
      by_contra h
      have hn2 : 2 ≤ n := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge h)
      have h9 : 9 ∣ 3 ^ n := pow_dvd_pow 3 hn2
      have hpowdiv : 3 ^ n ∣ 12 := by
        rw [← hn]
        exact hdiv
      have h9div12 : 9 ∣ 12 := h9.trans hpowdiv
      norm_num at h9div12
    have hn1 : n = 1 := by omega
    rw [hn, hn1]
    norm_num
  let t' : alternatingGroup (Fin 4) := eG t
  have ht'1 : t' ≠ 1 := by
    intro h
    exact ht1 (eG.injective (by simpa [t'] using h))
  have ht'2 : t' ^ 2 = 1 := by
    simpa [t'] using congrArg eG ht2
  have ht'_inv : t'⁻¹ = t' := by
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht'2)
  have hconj_of_mem : ∀ z ∈ P', t' * z * t'⁻¹ ∈ P' := by
    intro z hz
    rcases (Subgroup.mem_map.mp hz) with ⟨y, hyP, hz'⟩
    have hEq : eG y⁻¹ = t' * z * t'⁻¹ := by
      have hmain := congrArg eG (htinv y hyP)
      rw [← hz']
      simpa [t', map_mul, MonoidHom.map_inv] using hmain.symm
    exact Subgroup.mem_map.mpr ⟨y⁻¹, P.inv_mem hyP, hEq⟩
  have hnorm : t' ∈ Subgroup.normalizer (P' : Set (alternatingGroup (Fin 4))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj_of_mem x hx
    · intro hx
      have hx' := hconj_of_mem (t' * x * t'⁻¹) hx
      have hEq : t' * (t' * x * t'⁻¹) * t'⁻¹ = x := by
        rw [ht'_inv]
        calc
          t' * (t' * x * t') * t' = (t' * t') * x * (t' * t') := by group
          _ = x := by
            have hsq : t' * t' = 1 := by simpa [pow_two] using ht'2
            rw [hsq]
            simp
      simpa [hEq] using hx'
  have ht'P : t' ∈ P' := by
    rw [normalizer_eq_self_of_card_eq_three_of_mulEquiv_alternatingGroup_four
      P' hP'card ⟨MulEquiv.refl (alternatingGroup (Fin 4))⟩] at hnorm
    exact hnorm
  have hdiv3 : orderOf t' ∣ 3 := by
    exact (Subgroup.orderOf_dvd_natCard P' ht'P).trans (by rw [hP'card])
  have horder2 : orderOf t' = 2 := by
    exact (orderOf_eq_prime_iff (x := t') (p := 2)).2 ⟨ht'2, ht'1⟩
  have h23 : 2 ∣ 3 := by
    rw [horder2] at hdiv3
    exact hdiv3
  norm_num at h23

end CFSG.GorensteinWalter
