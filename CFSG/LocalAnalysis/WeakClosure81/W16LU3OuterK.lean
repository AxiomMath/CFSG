module

public import CFSG.GH74.Uniqueness.Bender.UnitaryAut
public import CFSG.GH74.Uniqueness.Bender.Aut
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.WeakClosure81.W16LU3Dih

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.GH74.Uniqueness.Bender
open Subgroup

variable {K : Type} [Group K] [Finite K] {n e : ℕ}

private theorem w16l_odd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n + 1) := by
  rw [← Nat.not_even_iff_odd, Nat.even_add_one]
  intro h
  exact h (Nat.even_pow.mpr ⟨even_two, by omega⟩)

private theorem w16l_unitary_index_odd_and_gt_one (h : BenderType K n 3 e) :
    Odd e ∧ 1 < e := by
  rcases h.cases' with ⟨h31, he, hn⟩ | ⟨h32, he, hn⟩ | ⟨-, he, hn⟩
  · omega
  · omega
  · subst he
    have hg : Nat.gcd 3 (2 ^ n + 1) ∣ 2 ^ n + 1 := Nat.gcd_dvd_right 3 (2 ^ n + 1)
    refine ⟨(w16l_odd_two_pow_add_one (by omega)).of_dvd_nat (Nat.div_dvd_of_dvd hg), ?_⟩
    have hgdvd : Nat.gcd 3 (2 ^ n + 1) ∣ 2 ^ n + 1 := hg
    have hgle : Nat.gcd 3 (2 ^ n + 1) ≤ 3 :=
      Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (2 ^ n + 1))
    have h5 : 5 ≤ 2 ^ n + 1 := by
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (n := 2) (by norm_num) (i := 2) (j := n) hn
      omega
    by_contra hle
    have hle' : (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) ≤ 1 := by omega
    have hmul : (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) * Nat.gcd 3 (2 ^ n + 1) ≤ 1 * 3 :=
      Nat.mul_le_mul hle' hgle
    rw [Nat.div_mul_cancel hgdvd] at hmul
    omega

section Certified


theorem BenderType.unitary_involution_dichotomy (h : BenderType K n 3 e) (Q : Sylow 2 K)
    (α : MulAut K) (hα : α * α = 1) (hfix : ∀ z ∈ rootCenter (Q : Subgroup K), α z = z) :
    (∃ r ∈ rootCenter (Q : Subgroup K), α = MulAut.conj r) ∨
      (∀ x ∈ Subgroup.centralizer (rootCenter (Q : Subgroup K) : Set K), Odd (orderOf x) →
        α x * x ∈ (Q : Subgroup K)) := by
  classical
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
    CFSG.mulAutConj_injective_of_center_eq_bot h.center_eq_bot
  obtain ⟨D, hND, hsup, hNDnorm, -, ⟨eD⟩⟩ := h.lemma_3_6_c_unitary Q
  have hαA : α ∈ autCentralizer (rootCenter (Q : Subgroup K)) :=
    mem_autCentralizer_iff.mpr hfix
  have hmOdd : Odd (2 ^ n + 1) := w16l_odd_two_pow_add_one (by have := h.two_le.2; omega)
  by_cases hαN : α ∈ Subgroup.map (MulAut.conj : K →* MulAut K) (Q : Subgroup K)
  · left
    obtain ⟨r, hrQ, hrα⟩ := Subgroup.mem_map.mp hαN
    refine ⟨r, ?_, hrα.symm⟩
    obtain ⟨t, hc⟩ := h.exists_benderCore Q
    have hrr : r * r = 1 := by
      apply hinj
      rw [map_mul, map_one, hrα]
      exact hα
    exact hc.mem_rootCenter_of_mul_self hrQ hrr
  · right
    intro x hx hodd
    have hxconjA : MulAut.conj x ∈ autCentralizer (rootCenter (Q : Subgroup K)) := by
      rw [mem_autCentralizer_iff]
      intro z hz
      have hzx : z * x = x * z := Subgroup.mem_centralizer_iff.mp hx z hz
      calc MulAut.conj x z = x * z * x⁻¹ := MulAut.conj_apply x z
        _ = z * x * x⁻¹ := by rw [← hzx]
        _ = z := by simp
    have hHcard : Nat.card (Subgroup.zpowers (MulAut.conj x)) = orderOf x := by
      rw [Nat.card_zpowers, orderOf_injective (MulAut.conj) hinj x]
    have hHodd : Odd (Nat.card (Subgroup.zpowers (MulAut.conj x))) := by
      simpa [hHcard] using hodd
    have hprod : ∀ h ∈ Subgroup.zpowers (MulAut.conj x),
        α * h * α⁻¹ * h ∈ Subgroup.map (MulAut.conj : K →* MulAut K) (Q : Subgroup K) :=
      w16l_inverts_of_dihedral_complement (G := MulAut K)
        (A := autCentralizer (rootCenter (Q : Subgroup K)))
        (N := Subgroup.map (MulAut.conj : K →* MulAut K) (Q : Subgroup K)) (D := D)
        (H := Subgroup.zpowers (MulAut.conj x)) (m := 2 ^ n + 1) (a := α)
        hmOdd hND hsup hNDnorm eD (Subgroup.zpowers_le.mpr hxconjA) hHodd hαA hα hαN
    have hmem : MulAut.conj (α x * x) ∈
        Subgroup.map (MulAut.conj : K →* MulAut K) (Q : Subgroup K) := by
      have h1 : α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
        ext v
        simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]
      rw [map_mul, ← h1]
      exact hprod (MulAut.conj x) (Subgroup.mem_zpowers _)
    obtain ⟨q, hqQ, hqeq⟩ := Subgroup.mem_map.mp hmem
    have hqx : q = α x * x := hinj hqeq
    rw [← hqx]
    exact hqQ

theorem BenderType.exists_odd_ne_one_centralizer_rootCenter (h : BenderType K n 3 e)
    (Q : Sylow 2 K) :
    ∃ x ∈ Subgroup.centralizer (rootCenter (Q : Subgroup K) : Set K), Odd (orderOf x) ∧
      x ≠ 1 := by
  obtain ⟨hoddE, hgtE⟩ := w16l_unitary_index_odd_and_gt_one h
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hcard : Nat.card (fixCartan (Q : Subgroup K) t) = e := hc.card_fixCartan
  have hgt : 1 < Nat.card (fixCartan (Q : Subgroup K) t) := by rw [hcard]; exact hgtE
  have hne : fixCartan (Q : Subgroup K) t ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (fixCartan (Q : Subgroup K) t) = 1 := by
      rw [hbot, Subgroup.card_bot]
    omega
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨(y : K), ?_, ?_, ?_⟩
  · rw [hc.centralizer_rootCenter_eq]
    exact Subgroup.mem_sup_right y.2
  · have hdvd : orderOf (y : K) ∣ Nat.card (fixCartan (Q : Subgroup K) t) :=
      Subgroup.orderOf_dvd_natCard _ y.2
    rw [hcard] at hdvd
    exact hoddE.of_dvd_nat hdvd
  · intro hy
    exact hy1 (Subtype.ext hy)

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
