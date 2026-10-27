module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_5_a

namespace CFSG
end CFSG
open CFSG

/-! # Theorem 5.5(b) from BG Section 5 -/

public theorem CFSG.theorem_5_5_b
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R) (hR : 3 ≤ groupRank R)
    {A : Subgroup (MulAut R)} [Group.IsSolvable A] (hoddA : Odd (Nat.card A))
    (a : MulAut R) (ha : a ∈ A) (hcop : Nat.Coprime p (orderOf a)) :
    orderOf a ∣ p - 1 := by
  classical
  let : Fact (IsPGroup p R) := ⟨hnarrow.1⟩
  have hR_nontrivial : Nontrivial R := by
    refine not_subsingleton_iff_nontrivial.mp ?_
    intro hsub
    let : Subsingleton R := hsub
    have hcyc : IsCyclic R := inferInstance
    have hRank_le_one : groupRank R ≤ 1 := groupRank_le_one_of_isCyclic R
    exact (by decide : ¬ 3 ≤ (1 : ℕ)) (le_trans hR hRank_le_one)
  let : Nontrivial R := hR_nontrivial
  obtain ⟨H, hHchar, hHcomm, hHnil, hHexp, hAfix_p⟩ :=
    theorem_1_13 (G := R) (p := p) hpodd
  let Afix : Subgroup (MulAut R) :=
    fixingSubgroup (M := MulAut R) (α := R) (H : Set R)
  let aA : A := ⟨a, ha⟩
  have hcopA : Nat.Coprime p (orderOf aA) := by
    simpa [aA, Subgroup.orderOf_coe] using hcop
  have hfix : ((aA ^ (p - 1) : A) : MulAut R) ∈ Afix := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    exact
      theorem_5_5_b_high_rank_pow_pred_fixes_H_core
        (p := p) hpodd (R := R) hnarrow hR (A := A) hoddA
        hHchar hHcomm hHnil hHexp aA hcopA x hx
  let b : Afix := ⟨(aA ^ (p - 1) : A), hfix⟩
  have hborder_dvd_p_pow : ∃ n, orderOf b = p ^ n := by
    exact (IsPGroup.iff_orderOf (p := p)).mp hAfix_p b
  have hborder_dvd_p : orderOf b = 1 ∨ p ∣ orderOf b := by
    rcases hborder_dvd_p_pow with ⟨n, hn⟩
    cases n with
    | zero =>
        left
        simpa using hn
    | succ n =>
        right
        rw [hn]
        rw [pow_succ']
        exact dvd_mul_right p (p ^ n)
  have hborder_dvd_a : orderOf b ∣ orderOf aA := by
    rw [← Subgroup.orderOf_coe (a := b)]
    have h1 : orderOf ((b : Afix) : MulAut R) ∣ orderOf (aA ^ (p - 1) : A) := by
      change orderOf (((aA ^ (p - 1) : A) : MulAut R)) ∣ orderOf (aA ^ (p - 1) : A)
      rw [Subgroup.orderOf_coe]
    exact h1.trans (orderOf_pow_dvd (x := aA) (p - 1))
  have hborder_coprime : Nat.Coprime p (orderOf b) :=
    Nat.Coprime.of_dvd_right hborder_dvd_a hcopA
  have hborder_one : orderOf b = 1 := by
    cases hborder_dvd_p with
    | inl h => exact h
    | inr hp_dvd =>
        exact False.elim ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hborder_coprime hp_dvd)
  have hb_one : b = 1 := orderOf_eq_one_iff.mp hborder_one
  have hpow_one_A : aA ^ (p - 1) = 1 := by
    have hval := congrArg (fun y : Afix => ((y : Afix) : MulAut R)) hb_one
    have hone : ((1 : Afix) : MulAut R) = 1 := rfl
    have hval' : ((aA ^ (p - 1) : A) : MulAut R) = 1 := by
      simpa [b, hone] using hval
    exact Subtype.ext hval'
  have hpow_one : a ^ (p - 1) = 1 := by
    simpa [aA] using congrArg (fun y : A => (y : MulAut R)) hpow_one_A
  exact orderOf_dvd_of_pow_eq_one hpow_one
