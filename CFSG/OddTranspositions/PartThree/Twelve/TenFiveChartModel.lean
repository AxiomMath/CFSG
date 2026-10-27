module

public import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
public import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Five
public import CFSG.RankThree.GF2n.Tim79aSec2

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix
open CFSG.OddTranspositions.PartFour.TableE1Five

namespace FiveChartModel

variable {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}

theorem five_mul_eq_zero {a c : ZMod 5} (h : a * c = 0) : a = 0 ∨ c = 0 := by
  revert a c; decide

theorem five_smul_eq_zero {a : ZMod 5} {v : Fin n → ZMod 5} (h : a • v = 0) :
    a = 0 ∨ v = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · refine Or.inr (funext fun i => ?_)
    have hi := congrFun h i
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi
    exact (five_mul_eq_zero hi).resolve_left ha

theorem commute_subtype_iff {X : Type*} [Group X] {H : Subgroup X} {a b : H} :
    Commute (a : X) (b : X) ↔ Commute a b :=
  ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem fiveReflections_eq_reflSet (k : ℕ) (ε π : Bool) :
    fiveReflections k ε π = reflSet (fiveBilin k ε π) :=
  (fischerTransvections_fiveBilin k ε π).symm

theorem mem_fiveReflections_iff {k : ℕ} {ε π : Bool} {g : GL (Fin (k + 1)) (ZMod 5)} :
    g ∈ fiveReflections k ε π ↔
      ∃ v, fiveBilin k ε π v v = 1 ∧ refl (fiveBilin k ε π) v = g := by
  rw [fiveReflections_eq_reflSet]
  exact mem_reflSet_iff

theorem refl_mem_fiveReflections {k : ℕ} {ε π : Bool} {v : Fin (k + 1) → ZMod 5}
    (hv : fiveBilin k ε π v v = 1) : refl (fiveBilin k ε π) v ∈ fiveReflections k ε π := by
  rw [fiveReflections_eq_reflSet]
  exact refl_mem_reflSet hv

theorem norm_act_refl (hsym : ∀ x y, b x y = b y x) {v w : Fin n → ZMod 5}
    (hv : b v v = 1) (hw : b w w = 1) : b (act (refl b v) w) (act (refl b v) w) = 1 := by
  rw [act_refl hv]
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hv, hw]
  rw [hsym w v]
  ring

theorem norm_act_refl_mul (hsym : ∀ x y, b x y = b y x) {v w : Fin n → ZMod 5}
    (hv : b v v = 1) (hw : b w w = 1) :
    b (act (refl b v * refl b w) v) (act (refl b v * refl b w) v) = 1 := by
  rw [act_mul, act_refl hw, act_refl hv]
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hv, hw]
  rw [hsym w v]
  ring

theorem norm_act_refl_mul' (hsym : ∀ x y, b x y = b y x) {v w : Fin n → ZMod 5}
    (hv : b v v = 1) (hw : b w w = 1) :
    b (act (refl b w * refl b v) w) (act (refl b w * refl b v) w) = 1 := by
  rw [act_mul, act_refl hv, act_refl hw]
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hv, hw]
  rw [hsym w v]
  ring

theorem refl_braid_three (hsym : ∀ x y, b x y = b y x) {v w : Fin n → ZMod 5}
    (hv : b v v = 1) (hw : b w w = 1) (ht : b v w = 2 ∨ b v w = -2) :
    refl b v * refl b w * refl b v = refl b w * refl b v * refl b w := by
  have hiv := refl_mem_isomGroup hsym v
  have hiw := refl_mem_isomGroup hsym w
  have e1 : refl b v * refl b w * refl b v = refl b (act (refl b v) w) := by
    rw [← conj_refl hiv, refl_inv]
  have e2 : refl b w * refl b v * refl b w = refl b (act (refl b w) v) := by
    rw [← conj_refl hiw, refl_inv]
  rw [e1, e2]
  have hn1 := norm_act_refl hsym hv hw
  have hn2 := norm_act_refl hsym hw hv
  have h5 : (5 : ZMod 5) = 0 := by decide
  rcases ht with ht | ht
  · refine (refl_eq_refl_iff hn1 hn2).mpr (Or.inl ?_)
    rw [act_refl hw, act_refl hv, hsym w v, ht]
    linear_combination (norm := module) h5 • (v - w)
  · refine (refl_eq_refl_iff hn1 hn2).mpr (Or.inr ?_)
    rw [act_refl hw, act_refl hv, hsym w v, ht]
    linear_combination (norm := module) h5 • (v + w)

theorem refl_braid_five (hsym : ∀ x y, b x y = b y x) {v w : Fin n → ZMod 5}
    (hv : b v v = 1) (hw : b w w = 1) (ht : b v w = 1 ∨ b v w = -1) :
    refl b v * refl b w * refl b v * refl b w * refl b v =
      refl b w * refl b v * refl b w * refl b v * refl b w := by
  have hiv := refl_mem_isomGroup hsym v
  have hiw := refl_mem_isomGroup hsym w
  have hivw : refl b v * refl b w ∈ isomGroup b := (isomGroup b).mul_mem hiv hiw
  have hiwv : refl b w * refl b v ∈ isomGroup b := (isomGroup b).mul_mem hiw hiv
  have e1 : refl b v * refl b w * refl b v * refl b w * refl b v =
      refl b (act (refl b v * refl b w) v) := by
    rw [← conj_refl hivw, _root_.mul_inv_rev, refl_inv, refl_inv]
    group
  have e2 : refl b w * refl b v * refl b w * refl b v * refl b w =
      refl b (act (refl b w * refl b v) w) := by
    rw [← conj_refl hiwv, _root_.mul_inv_rev, refl_inv, refl_inv]
    group
  rw [e1, e2]
  have hn1 := norm_act_refl_mul hsym hv hw
  have hn2 := norm_act_refl_mul' hsym hv hw
  have h5 : (5 : ZMod 5) = 0 := by decide
  rcases ht with ht | ht
  · refine (refl_eq_refl_iff hn1 hn2).mpr (Or.inl ?_)
    rw [act_mul, act_mul, act_refl hw, act_refl hv, act_refl hv, act_refl hw]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hv, hw]
    rw [hsym w v, ht]
    linear_combination (norm := module) h5 • (w - v)
  · refine (refl_eq_refl_iff hn1 hn2).mpr (Or.inr ?_)
    rw [act_mul, act_mul, act_refl hw, act_refl hv, act_refl hv, act_refl hw]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hv, hw]
    rw [hsym w v, ht]
    linear_combination (norm := module) h5 • (v + w)

private theorem pow_three_of_braid {H : Type*} [Group H] {a c : H} (ha : a * a = 1)
    (hc : c * c = 1) (h : a * c * a = c * a * c) : (a * c) ^ 3 = 1 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  calc (a * c) ^ 3 = (a * c * a) * (c * a * c) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (c * a * c) * (c⁻¹ * a⁻¹ * c⁻¹) := by rw [h, ha', hc']
    _ = 1 := by group

private theorem pow_five_of_braid {H : Type*} [Group H] {a c : H} (ha : a * a = 1)
    (hc : c * c = 1) (h : a * c * a * c * a = c * a * c * a * c) : (a * c) ^ 5 = 1 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  calc (a * c) ^ 5 = (a * c * a * c * a) * (c * a * c * a * c) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (c * a * c * a * c) * (c⁻¹ * a⁻¹ * c⁻¹ * a⁻¹ * c⁻¹) := by rw [h, ha', hc']
    _ = 1 := by group

theorem refl_mul_refl_pow_five (hsym : ∀ x y, b x y = b y x) {v w : Fin n → ZMod 5}
    (hv : b v v = 1) (hw : b w w = 1) (ht : (b v w) ^ 2 = 1) :
    (refl b v * refl b w) ^ 5 = 1 := by
  have ht' : b v w = 1 ∨ b v w = -1 := by
    revert ht; generalize b v w = t; revert t; decide
  exact pow_five_of_braid (refl_mul_self v) (refl_mul_self w) (refl_braid_five hsym hv hw ht')

theorem refl_mul_refl_pow_three (hsym : ∀ x y, b x y = b y x) {v w : Fin n → ZMod 5}
    (hv : b v v = 1) (hw : b w w = 1) (ht : b v w ≠ 0) (ht2 : (b v w) ^ 2 ≠ 1) :
    (refl b v * refl b w) ^ 3 = 1 := by
  have ht' : b v w = 2 ∨ b v w = -2 := by
    revert ht2 ht; generalize b v w = t; revert t; decide
  exact pow_three_of_braid (refl_mul_self v) (refl_mul_self w) (refl_braid_three hsym hv hw ht')

theorem refl_commute_iff (hsym : ∀ x y, b x y = b y x) {v w : Fin n → ZMod 5}
    (hv : b v v = 1) (hw : b w w = 1) :
    Commute (refl b v) (refl b w) ↔ b v w = 0 ∨ w = v ∨ w = -v := by
  constructor
  · intro h
    have h1 : refl b v * refl b w * (refl b v)⁻¹ = refl b w := by
      rw [h.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [conj_refl (refl_mem_isomGroup hsym v),
      refl_eq_refl_iff (by rw [isom_norm (refl_mem_isomGroup hsym v), hw]) hw,
      act_refl hv] at h1
    rcases h1 with h1 | h1
    · left
      have h2 : (-2 * b w v) • v = 0 := by
        have h : w + (-2 * b w v) • v = w + 0 := by
          rw [add_zero]; exact h1.symm
        exact add_left_cancel h
      have hv0 : v ≠ 0 := ne_zero_of_norm_ne_zero (by rw [hv]; decide)
      have h3 : -2 * b w v = 0 := (five_smul_eq_zero h2).resolve_right hv0
      have h4 : b w v = 0 := (five_mul_eq_zero h3).resolve_left (by decide)
      rwa [hsym w v] at h4
    · right
      have h2 : w = (b w v) • v := by
        have h3 : (2 : ZMod 5) • (w - (b w v) • v) = 0 := by
          linear_combination (norm := module) h1
        rcases five_smul_eq_zero h3 with h4 | h4
        · exact absurd h4 (by decide)
        · exact sub_eq_zero.mp h4
      have hc : b w v * b w v = 1 := by
        have hw' := hw
        rw [h2, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hv,
          mul_one] at hw'
        exact hw'
      have hc' : b w v = 1 ∨ b w v = -1 := by
        revert hc; generalize b w v = c; revert c; decide
      rcases hc' with hc' | hc'
      · left; rw [h2, hc', one_smul]
      · right; rw [h2, hc', neg_one_smul (ZMod 5) v]
  · rintro (h | rfl | rfl)
    · exact refl_comm_of_perp hsym h
    · rfl
    · simpa [refl_neg] using Commute.refl (refl b v)

theorem refl_commute_iff_of_ne (hsym : ∀ x y, b x y = b y x) {v w : Fin n → ZMod 5}
    (hv : b v v = 1) (hw : b w w = 1) (hne1 : w ≠ v) (hne2 : w ≠ -v) :
    Commute (refl b v) (refl b w) ↔ b v w = 0 := by
  rw [refl_commute_iff hsym hv hw]
  constructor
  · rintro (h | h | h)
    · exact h
    · exact absurd h hne1
    · exact absurd h hne2
  · exact Or.inl

theorem refl_mul_refl_order (hsym : ∀ x y, b x y = b y x) {v w : Fin n → ZMod 5}
    (hv : b v v = 1) (hw : b w w = 1) (hne1 : w ≠ v) (hne2 : w ≠ -v)
    (ht : b v w ≠ 0) :
    orderOf (refl b v * refl b w) = if (b v w) ^ 2 = 1 then 5 else 3 := by
  have hne : refl b v * refl b w ≠ 1 := by
    intro h
    have h1 : refl b v = refl b w := by
      have h2 := congrArg (fun z => z * refl b w) h
      simpa [mul_assoc, refl_mul_self] using h2
    rcases (refl_eq_refl_iff hv hw).mp h1 with h2 | h2
    · exact hne1 h2
    · exact hne2 h2
  by_cases ht2 : (b v w) ^ 2 = 1
  · rw [if_pos ht2]
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime (refl_mul_refl_pow_five hsym hv hw ht2) hne
  · rw [if_neg ht2]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (refl_mul_refl_pow_three hsym hv hw ht ht2) hne

end FiveChartModel

end CFSG.OddTranspositions.PartThree

end
