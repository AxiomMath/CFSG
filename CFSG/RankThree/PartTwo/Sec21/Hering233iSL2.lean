module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

private theorem sq_eq_one_aux {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (a b c d : F)
    (h00 : a * a + b * c = 1) (h01 : a * b + b * d = 0) (h10 : c * a + d * c = 0)
    (hdet : a * d - b * c = 1) : b = 0 ∧ c = 0 ∧ d = a ∧ (a = 1 ∨ a = -1) := by
  by_cases had : a + d = 0
  · exfalso
    apply h2
    have hd : d = -a := by linear_combination had
    rw [hd] at hdet
    linear_combination (-1 : F) * h00 + (-1 : F) * hdet
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination h01
      exact (mul_eq_zero.1 this).resolve_right had
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination h10
      exact (mul_eq_zero.1 this).resolve_right had
    subst hb hc
    have ha : a * a = 1 := by linear_combination h00
    have hda : a * d = 1 := by linear_combination hdet
    have hd : d = a := by
      have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one ha
      apply mul_left_cancel₀ ha0
      rw [hda, ha]
    exact ⟨rfl, rfl, hd, mul_self_eq_one_iff.1 ha⟩

theorem sl2_eq_one_or_neg_one_of_mul_self {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {g : Matrix.SpecialLinearGroup (Fin 2) F} (hg : g * g = 1) : g = 1 ∨ g = -1 := by
  have hm := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F)) hg
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h10 := congrFun (congrFun hm 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨hb, hc, hd, h1⟩ := sq_eq_one_aux h2 _ _ _ _ h00 h01 h10 hdet
  rcases h1 with h1 | h1
  · left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, hd, hb, hc]
  · right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, hd, hb, hc]

theorem false_of_sl2_quotient {Y : Type*} [Group Y] {N : Subgroup Y} [N.Normal] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (e : Y ⧸ N ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    {S : Subgroup Y} (hSN : S ⊓ N = ⊥) {u v : Y} (hu : u ∈ S) (hv : v ∈ S) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huv : u ≠ v) (hu2 : u * u = 1) (hv2 : v * v = 1) : False := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h'
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := hp.two_le
    exact hp2 (by omega)
  have hsq : ∀ w : Y, w * w = 1 → e (w : Y ⧸ N) * e (w : Y ⧸ N) = 1 := by
    intro w hw
    rw [← map_mul e, ← QuotientGroup.mk_mul, hw, QuotientGroup.mk_one, map_one]
  have hnot : ∀ w : Y, w ∈ S → w ≠ 1 → e (w : Y ⧸ N) ≠ 1 := by
    intro w hw hw1 h
    have hwN : w ∈ N := (QuotientGroup.eq_one_iff w).1 (e.injective (h.trans (map_one e).symm))
    have hmem : w ∈ S ⊓ N := ⟨hw, hwN⟩
    rw [hSN, Subgroup.mem_bot] at hmem
    exact hw1 hmem
  have hu_neg : e (u : Y ⧸ N) = -1 :=
    (sl2_eq_one_or_neg_one_of_mul_self h2 (hsq u hu2)).resolve_left (hnot u hu hu1)
  have hv_neg : e (v : Y ⧸ N) = -1 :=
    (sl2_eq_one_or_neg_one_of_mul_self h2 (hsq v hv2)).resolve_left (hnot v hv hv1)
  have hmk : (u : Y ⧸ N) = (v : Y ⧸ N) := e.injective (hu_neg.trans hv_neg.symm)
  have hinv : ((u⁻¹ * v : Y) : Y ⧸ N) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk, inv_mul_cancel]
  have hmem : u⁻¹ * v ∈ S ⊓ N :=
    ⟨S.mul_mem (S.inv_mem hu) hv, (QuotientGroup.eq_one_iff _).1 hinv⟩
  rw [hSN, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact huv hmem

end CFSG.RankThree.PartTwo.Sec21.Hering233i
