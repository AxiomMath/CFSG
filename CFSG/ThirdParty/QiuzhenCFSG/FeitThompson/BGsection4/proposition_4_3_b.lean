module

import Mathlib.Data.Nat.Choose.Dvd
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Infrastructure
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_3_a

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

section Main

private theorem CFSG.pth_mul_eq_mul_pows_of_derived_le_omega₁
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) [Fact (IsPGroup p R)]
    (hclass : NilpotencyClassLe 2 R ∨ (3 < p ∧ NilpotencyClassLe 3 R))
    (hder : derivedSubgroup R ≤ omega₁ (G := R) (p := p)) {u v : R} :
    (u * v) ^ p = u ^ p * v ^ p := by
  have hΩpow : ∀ x : omega₁ (G := R) (p := p), x ^ p = 1 := by
    have hexp_dvd : Monoid.exponent ↥(omega₁ (G := R) (p := p)) ∣ p := by
      rcases proposition_4_3_a (R := R) (p := p) hpodd hclass with h1 | hp
      · rw [h1]
        exact one_dvd p
      · rw [hp]
    exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hexp_dvd)
  have hder_pow : ∀ {x : R}, x ∈ derivedSubgroup R → x ^ p = 1 := by
    intro x hx
    have hxΩ : x ∈ omega₁ (G := R) (p := p) := hder hx
    simpa using congrArg Subtype.val (hΩpow ⟨x, hxΩ⟩)
  cases hclass with
  | inl hclass2 =>
      have hp1 : 1 < p := (show Nat.Prime p from Fact.out).one_lt
      have hcomm_le :
          ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ ≤ Subgroup.center R :=
        commutator_le_center_of_le_upperCentralSeries_two (G := R) (⊤ : Subgroup R)
          (by simpa [hclass2])
      have hcomm_mem : ⁅v, u⁆ ∈ Subgroup.center R := by
        exact hcomm_le (Subgroup.commutator_mem_commutator (by simp) (by simp))
      have hcomm_mem' : ⁅u, v⁆ ∈ Subgroup.center R := by
        simpa [commutatorElement_inv] using (Subgroup.center R).inv_mem hcomm_mem
      have hc_der : ⁅v, u⁆ ∈ derivedSubgroup R := by
        change ⁅v, u⁆ ∈ ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆
        exact Subgroup.commutator_mem_commutator (by simp) (by simp)
      have hc_choose : ⁅v, u⁆ ^ Nat.choose p 2 = 1 := by
        exact choose_two_pow_eq_one (p := p) hpodd (hder_pow hc_der)
      calc
        (u * v) ^ p = u ^ p * v ^ p * ⁅v, u⁆ ^ Nat.choose p 2 := by
          simpa using lemma_4_2_b (G := R) (x := u) (y := v) (n := p) hp1 hcomm_mem'
        _ = u ^ p * v ^ p := by simp [hc_choose]
  | inr hclass3 =>
      let c : R := ⁅v, u⁆
      let du : R := ⁅c, u⁆
      let dv : R := ⁅c, v⁆
      have hL2 : (⊤ : Subgroup R).lowerCentralSeries 2 ≤ Subgroup.center R :=
        lowerCentralSeries_two_le_center_of_class3 (R := R) hclass3.2
      have hdu_mem_l2 : du ∈ (⊤ : Subgroup R).lowerCentralSeries 2 := by
        simpa [c, du] using
          (triple_commutator_mem_lowerCentralSeries_two (R := R) v u u)
      have hdv_mem_l2 : dv ∈ (⊤ : Subgroup R).lowerCentralSeries 2 := by
        simpa [c, dv] using
          (triple_commutator_mem_lowerCentralSeries_two (R := R) v u v)
      have hdu_cent : du ∈ Subgroup.center R := hL2 hdu_mem_l2
      have hdv_cent : dv ∈ Subgroup.center R := hL2 hdv_mem_l2
      have hc_der : c ∈ derivedSubgroup R := by
        change ⁅v, u⁆ ∈ ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆
        exact Subgroup.commutator_mem_commutator (by simp) (by simp)
      have hdu_der : du ∈ derivedSubgroup R := by
        have hcomm_le : ⁅derivedSubgroup R, (⊤ : Subgroup R)⁆ ≤ derivedSubgroup R :=
          Subgroup.commutator_le_left (H₁ := derivedSubgroup R) (H₂ := (⊤ : Subgroup R))
        apply hcomm_le
        simpa [c, du] using
          (Subgroup.commutator_mem_commutator (H₁ := derivedSubgroup R) (H₂ := (⊤ : Subgroup R))
            hc_der (by simp))
      have hdv_der : dv ∈ derivedSubgroup R := by
        have hcomm_le : ⁅derivedSubgroup R, (⊤ : Subgroup R)⁆ ≤ derivedSubgroup R :=
          Subgroup.commutator_le_left (H₁ := derivedSubgroup R) (H₂ := (⊤ : Subgroup R))
        apply hcomm_le
        simpa [c, dv] using
          (Subgroup.commutator_mem_commutator (H₁ := derivedSubgroup R) (H₂ := (⊤ : Subgroup R))
            hc_der (by simp))
      have hc_choose : c ^ Nat.choose p 2 = 1 := by
        exact choose_two_pow_eq_one (p := p) hpodd (hder_pow hc_der)
      have hpdvd_choose3 : p ∣ Nat.choose p 3 := by
        have hpprime : Nat.Prime p := Fact.out
        exact Nat.Prime.dvd_choose_self hpprime (k := 3) (by decide) hclass3.1
      have hpdvd_chooseSucc3 : p ∣ Nat.choose (p + 1) 3 := by
        have hpascal : Nat.choose (p + 1) 3 = Nat.choose p 2 + Nat.choose p 3 := by
          simpa [Nat.add_comm] using Nat.choose_succ_succ p 2
        rw [hpascal]
        exact dvd_add (prime_dvd_choose_two (p := p) hpodd) hpdvd_choose3
      have hdu_choose : du ^ Nat.choose (p + 1) 3 = 1 := by
        rcases hpdvd_chooseSucc3 with ⟨k, hk⟩
        calc
          du ^ Nat.choose (p + 1) 3 = du ^ (p * k) := by simp [hk]
          _ = (du ^ p) ^ k := by rw [pow_mul]
          _ = 1 := by simp [hder_pow hdu_der]
      have hdv_choose : dv ^ Nat.choose p 3 = 1 := by
        rcases hpdvd_choose3 with ⟨k, hk⟩
        calc
          dv ^ Nat.choose p 3 = dv ^ (p * k) := by simp [hk]
          _ = (dv ^ p) ^ k := by rw [pow_mul]
          _ = 1 := by simp [hder_pow hdv_der]
      calc
        (u * v) ^ p
            = du ^ Nat.choose (p + 1) 3 * (dv ^ Nat.choose p 3)⁻¹ * u ^ p * c ^ Nat.choose p 2 * v ^ p := by
                simpa [c, du, dv] using (mul_pow_formula_front (u := u) (v := v) hdu_cent hdv_cent p)
        _ = u ^ p * v ^ p := by simp [hdu_choose, hdv_choose, hc_choose]

public theorem CFSG.proposition_4_3_b {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) [Fact (IsPGroup p R)]
    (hclass : NilpotencyClassLe 2 R ∨ (3 < p ∧ NilpotencyClassLe 3 R))
    (hder : derivedSubgroup R ≤ omega₁ (G := R) (p := p)) :
    ∃ φ : R →* R, ∀ x : R, φ x = x ^ p := by
  refine ⟨
    { toFun := fun x => x ^ p
      map_one' := by simp
      map_mul' := by
        intro x y
        exact pth_mul_eq_mul_pows_of_derived_le_omega₁
          (R := R) (p := p) hpodd hclass hder (u := x) (v := y) },
    fun x => rfl⟩


end Main
