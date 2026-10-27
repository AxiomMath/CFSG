module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6OddTr

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

variable {V : Type*} [CommGroup V]

theorem fixes_of_commV_inf {a w : MulAut V} (ha : a * a = 1)
    (hw : w * (a * w * a) = (a * w * a) * w) {k : ℕ}
    (hdisj : commV (zpowers a) ⊓ commV (zpowers (w ^ k * a * (w ^ k)⁻¹)) = ⊥)
    {v : V} (hv : ((a * (w * a * w⁻¹)) ^ k) v = v) : (a * (w * a * w⁻¹)) v = v := by
  set c : MulAut V := a * (w * a * w⁻¹) with hcdef
  have hc : c = (a * w * a) * w⁻¹ := by
    rw [hcdef]
    group
  have hcomm : Commute (a * w * a) w := hw.symm
  have hcu : ∀ j : ℕ, c ^ j = (a * w * a) ^ j * (w⁻¹) ^ j := by
    intro j
    rw [hc, hcomm.inv_right.mul_pow]
  have hau : ∀ j : ℕ, a * (a * w * a) ^ j = w ^ j * a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← mul_assoc, ih]
      calc w ^ j * a * (a * w * a) = w ^ j * (a * a) * w * a := by group
        _ = w ^ j * w * a := by rw [ha, mul_one]
        _ = w ^ (j + 1) * a := by rw [pow_succ]
  have hac : ∀ j : ℕ, a * c ^ j = w ^ j * a * (w ^ j)⁻¹ := by
    intro j
    rw [hcu j, ← mul_assoc, hau j, inv_pow]
  have hdisj' : commV (zpowers a) ⊓ commV (zpowers (a * c ^ k)) = ⊥ := by
    rw [hac k]
    exact hdisj
  have hav : a v = v := fixes_of_inf_commV_eq_bot hdisj' hv
  have ha1 : w * a * w⁻¹ = a * c := by
    calc w * a * w⁻¹ = (a * a) * (w * a * w⁻¹) := by rw [ha, one_mul]
      _ = a * (a * (w * a * w⁻¹)) := by group
      _ = a * c := by rw [← hcdef]
  have ha1c : ∀ j : ℕ, (w * a * w⁻¹) * c ^ j =
      w ^ (j + 1) * a * (w ^ (j + 1))⁻¹ := by
    intro j
    calc (w * a * w⁻¹) * c ^ j = (a * c) * c ^ j := by rw [ha1]
      _ = a * c ^ (j + 1) := by rw [mul_assoc, ← pow_succ']
      _ = w ^ (j + 1) * a * (w ^ (j + 1))⁻¹ := hac (j + 1)
  have hdisj_conj : commV (zpowers (w * a * w⁻¹)) ⊓
      commV (zpowers (w ^ (k + 1) * a * (w ^ (k + 1))⁻¹)) = ⊥ := by
    have hmap := congrArg (fun S : Subgroup V => S.map w.toMonoidHom) hdisj
    rw [Subgroup.map_inf_eq _ _ w.toMonoidHom w.injective, Subgroup.map_bot] at hmap
    rw [← commV_zpowers_conj_eq a w,
      ← commV_zpowers_conj_eq (w ^ k * a * (w ^ k)⁻¹) w] at hmap
    convert hmap using 2
    group
  have hdisj₁ : commV (zpowers (w * a * w⁻¹)) ⊓
      commV (zpowers ((w * a * w⁻¹) * c ^ k)) = ⊥ := by
    rw [ha1c k]
    exact hdisj_conj
  have ha1v : (w * a * w⁻¹) v = v := fixes_of_inf_commV_eq_bot hdisj₁ hv
  calc (a * (w * a * w⁻¹)) v = a ((w * a * w⁻¹) v) := MulAut.mul_apply ..
    _ = a v := by rw [ha1v]
    _ = v := hav

theorem eq_one_of_fixes_sq [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {r : MulAut V} {n : ℕ}
    (hr : r ^ 2 ^ n = 1) (h : ∀ v : V, (r ^ 2) v = v → r v = v) : r = 1 := by
  have hdvd : orderOf r ∣ 2 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hr
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hC : {v : V | r v = v} = {v : V | (r ^ 2) v = v} := by
    ext v
    change r v = v ↔ (r ^ 2) v = v
    constructor
    · intro hv
      rw [pow_two, MulAut.mul_apply, hv, hv]
    · intro hv
      exact h v hv
  have hbot :=
    CFSG.HardMathSupport.Aschbacher.SymplecticType.actionCommutator_eq_bot_of_fixed_points_eq
      V hV r ⟨k, hk⟩ hC
  ext v
  have hmem : v⁻¹ * r v ∈
      CFSG.HardMathSupport.Aschbacher.SymplecticType.actionCommutator V {r} :=
    Subgroup.subset_closure ⟨r, by simp, v, rfl⟩
  rw [hbot] at hmem
  have h1 : v⁻¹ * r v = 1 := Subgroup.mem_bot.1 hmem
  simpa using (inv_mul_eq_one.1 h1).symm

theorem eq_one_of_fixes_of_odd [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {s t : MulAut V} {n : ℕ}
    (hst : s * t = t * s) (hs : s ^ 2 ^ n = 1) (ht : Odd (orderOf t))
    (h : ∀ v : V, s v = v → t v = v) : t = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp : IsPGroup 2 V := fun v => ⟨1, by rw [pow_one, hV v]⟩
  have hsP : IsPGroup 2 (Subgroup.zpowers s) := by
    refine IsPGroup.of_card_dvd_pow (n := n) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr hs
  have hcomm : ∀ a ∈ Subgroup.zpowers s, a * t = t * a := by
    intro a ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left hst i).eq
  have hfix : ∀ v : V, (∀ a ∈ Subgroup.zpowers s, a v = v) → t v = v := by
    intro v hv
    exact h v (hv s (Subgroup.mem_zpowers s))
  exact CFSG.GroupTheory.eq_one_of_forall_fixed_of_coprime hVp hsP
    (Nat.coprime_two_right.mpr ht) hcomm hfix

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
