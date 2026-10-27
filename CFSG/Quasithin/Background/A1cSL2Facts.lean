module

public import CFSG.Quasithin.Background.A1cA130
public import CFSG.Quasithin.Background.A1cA133
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.Quasithin

open Matrix
open scoped MatrixGroups commutatorElement

namespace A1c

section Explicit

variable (p : ℕ)

@[expose] def sl2Diag (a b : ZMod p) (h : a * b = 1) : SL(2, ZMod p) :=
  ⟨!![a, 0; 0, b], by simp [Matrix.det_fin_two, h]⟩

variable {p}

theorem sl2Diag_mul_sl2U (a b : ZMod p) (h : a * b = 1) (n : ℕ) (hn : a = (n : ZMod p) * b) :
    sl2Diag p a b h * sl2U p = sl2U p ^ n * sl2Diag p a b h := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, sl2U_pow]
  simp only [sl2Diag, sl2U]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hn]

theorem sl2W_ne_one [Fact (1 < p)] : sl2W p ≠ 1 := by
  intro h
  have := congrArg (fun g : SL(2, ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) h
  simp [sl2W] at this

theorem sl2W_ne_negOne [Fact (1 < p)] : sl2W p ≠ sl2NegOne p := by
  intro h
  have := congrArg (fun g : SL(2, ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) h
  simp [sl2W, sl2NegOne] at this

theorem sl2U_mul_sl2W_ne [Fact (1 < p)] : sl2U p * sl2W p ≠ sl2W p * sl2U p := by
  intro h
  have h' := congrArg (fun g : SL(2, ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h'
  simp [sl2U, sl2W, Matrix.mul_apply, Fin.sum_univ_two] at h'

theorem sl2U_mul_sl2W_ne' [Fact (1 < p)] :
    sl2U p * sl2W p ≠ sl2NegOne p * (sl2W p * sl2U p) := by
  intro h
  have h' := congrArg (fun g : SL(2, ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h'
  simp [sl2U, sl2W, sl2NegOne, Matrix.mul_apply, Fin.sum_univ_two] at h'

theorem sl2U_ne_one [Fact (1 < p)] : sl2U p ≠ 1 := by
  intro h
  have := congrArg (fun g : SL(2, ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) h
  simp [sl2U] at this

theorem sl2U_ne_negOne [Fact (1 < p)] : sl2U p ≠ sl2NegOne p := by
  intro h
  have := congrArg (fun g : SL(2, ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) h
  simp [sl2U, sl2NegOne] at this

end Explicit

section Facts

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_finset_card_four (hp5 : 5 ≤ p) : ∃ s : Finset (ZMod p), s.card = 4 := by
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (ZMod p)))
    (n := 4) (by rw [Finset.card_univ, ZMod.card]; omega)
  exact ⟨t, ht⟩

theorem sl2_isPerfect (hp5 : 5 ≤ p) : Group.IsPerfect (SL(2, ZMod p)) :=
  CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four hp5)

theorem normal_le_center_or_eq_top (hp5 : 5 ≤ p) (N : Subgroup (SL(2, ZMod p))) [N.Normal] :
    N ≤ Subgroup.center (SL(2, ZMod p)) ∨ N = ⊤ := by
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := ZMod p) (n := 2)
    le_rfl (Or.inr (exists_finset_card_four hp5))
  have hq : Function.Surjective (QuotientGroup.mk' (Subgroup.center (SL(2, ZMod p)))) :=
    QuotientGroup.mk'_surjective _
  have hNm : (N.map (QuotientGroup.mk' (Subgroup.center (SL(2, ZMod p))))).Normal :=
    Subgroup.Normal.map ‹N.Normal› _ hq
  rcases hsimple.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center (SL(2, ZMod p))))) with h | h
  · left
    intro g hg
    have h1 : QuotientGroup.mk' (Subgroup.center (SL(2, ZMod p))) g ∈
        N.map (QuotientGroup.mk' (Subgroup.center (SL(2, ZMod p)))) := ⟨g, hg, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff g).1 h1
  · right
    have hperf := sl2_isPerfect hp5
    have hdecomp : ∀ x : SL(2, ZMod p), ∃ n ∈ N, ∃ z ∈ Subgroup.center (SL(2, ZMod p)), x = n * z := by
      intro x
      have h1 : QuotientGroup.mk' (Subgroup.center (SL(2, ZMod p))) x ∈
          N.map (QuotientGroup.mk' (Subgroup.center (SL(2, ZMod p)))) := by rw [h]; trivial
      obtain ⟨n, hn, hnx⟩ := h1
      refine ⟨n, hn, n⁻¹ * x, ?_, by group⟩
      rw [← QuotientGroup.ker_mk' (Subgroup.center (SL(2, ZMod p))), MonoidHom.mem_ker, map_mul,
        map_inv, hnx, inv_mul_cancel]
    have hcomm : ∀ x y : SL(2, ZMod p), ⁅x, y⁆ ∈ N := by
      intro x y
      obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hdecomp x
      obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hdecomp y
      have c1 : Commute z₁ (n₂ * z₂) := (Subgroup.mem_center_iff.1 hz₁ _).symm
      have c2 : Commute z₂ n₁ := (Subgroup.mem_center_iff.1 hz₂ _).symm
      rw [commutatorElement_mul_of_commute_right c1, commutatorElement_mul_of_commute_left c2]
      rw [commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)
    rw [eq_top_iff]
    have : commutator (SL(2, ZMod p)) ≤ N := by
      rw [commutator_def, Subgroup.commutator_le]
      exact fun x _ y _ => hcomm x y
    rwa [hperf.commutator_eq_top] at this

theorem eq_one_or_eq_sl2NegOne_of_mem_center {g : SL(2, ZMod p)}
    (hg : g ∈ Subgroup.center (SL(2, ZMod p))) : g = 1 ∨ g = sl2NegOne p := by
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
  have hr2 : (r - 1) * (r + 1) = 0 := by
    have : r ^ 2 = 1 := by simpa using hr
    linear_combination this
  rcases mul_eq_zero.1 hr2 with h | h
  · left
    have hr1 : r = 1 := by linear_combination h
    apply Subtype.ext
    rw [← hrg, hr1]
    simp
  · right
    have hr1 : r = -1 := eq_neg_of_add_eq_zero_left h
    apply Subtype.ext
    rw [← hrg, hr1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2NegOne, Matrix.scalar_apply] <;> rfl

theorem sl2NegOne_mem_center : sl2NegOne p ∈ Subgroup.center (SL(2, ZMod p)) := by
  refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨-1, ?_, ?_⟩
  · rw [Fintype.card_fin]; exact neg_one_sq
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2NegOne, Matrix.scalar_apply] <;> rfl

theorem sl2NegOne_comm (g : SL(2, ZMod p)) : g * sl2NegOne p = sl2NegOne p * g :=
  Subgroup.mem_center_iff.1 sl2NegOne_mem_center g

theorem orderOf_sl2NegOne (hp2 : p ≠ 2) : orderOf (sl2NegOne p) = 2 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  orderOf_eq_prime (by rw [pow_two]; exact sl2NegOne_mul_self) (sl2NegOne_ne_one hp2)

end Facts

end A1c

end CFSG.Quasithin
