module

public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRP

open Matrix

section Matrix

variable {F : Type} [Field F]

theorem mul_apply_two (m n : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    (m * n) i j = m i 0 * n 0 j + m i 1 * n 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_comm_of_commute_nonscalar {a b y : Matrix (Fin 2) (Fin 2) F}
    (hy : y 0 1 ≠ 0 ∨ y 1 0 ≠ 0 ∨ y 0 0 ≠ y 1 1) (ha : a * y = y * a) (hb : b * y = y * b) :
    a * b = b * a := by
  have a1 := congrFun (congrFun ha 0) 0
  have a2 := congrFun (congrFun ha 0) 1
  have a3 := congrFun (congrFun ha 1) 0
  have b1 := congrFun (congrFun hb 0) 0
  have b2 := congrFun (congrFun hb 0) 1
  have b3 := congrFun (congrFun hb 1) 0
  simp only [mul_apply_two] at a1 a2 a3 b1 b2 b3
  refine Matrix.ext fun i j => ?_
  revert i j
  simp only [Fin.forall_fin_two, mul_apply_two]
  by_cases h01 : y 0 1 = 0
  · by_cases h10 : y 1 0 = 0
    · have hd : y 0 0 - y 1 1 ≠ 0 := by
        rcases hy with h | h | h
        · exact absurd h01 h
        · exact absurd h10 h
        · exact sub_ne_zero.mpr h
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> apply mul_left_cancel₀ hd
      · linear_combination (-(b 1 0)) * a2 + a 1 0 * b2 + (b 1 0 * (a 0 0 - a 1 1) -
          a 1 0 * (b 0 0 - b 1 1)) * h01
      · linear_combination (b 0 0 - b 1 1) * a2 - (a 0 0 - a 1 1) * b2
      · linear_combination (b 0 0 - b 1 1) * a3 - (a 0 0 - a 1 1) * b3
      · linear_combination b 1 0 * a2 - a 1 0 * b2 - (b 1 0 * (a 0 0 - a 1 1) -
          a 1 0 * (b 0 0 - b 1 1)) * h01
    · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> apply mul_left_cancel₀ h10
      · linear_combination b 1 0 * a1 - a 1 0 * b1
      · linear_combination (a 0 0 - a 1 1) * b1 - (b 0 0 - b 1 1) * a1 +
          ((a 0 0 - a 1 1) * b 1 0 - (b 0 0 - b 1 1) * a 1 0) * h01
      · linear_combination b 1 0 * a3 - a 1 0 * b3
      · linear_combination a 1 0 * b1 - b 1 0 * a1
  · have h2 : y 0 1 * y 0 1 ≠ 0 := mul_ne_zero h01 h01
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · apply mul_left_cancel₀ h01
      linear_combination b 0 1 * a1 - a 0 1 * b1
    · apply mul_left_cancel₀ h01
      linear_combination b 0 1 * a2 - a 0 1 * b2
    · apply mul_left_cancel₀ h2
      linear_combination (-(y 1 0)) * b 0 1 * a2 + y 1 0 * a 0 1 * b2 -
        y 0 1 * (b 0 0 - b 1 1) * a1 + y 0 1 * (a 0 0 - a 1 1) * b1
    · apply mul_left_cancel₀ h01
      linear_combination a 0 1 * b1 - b 0 1 * a1

end Matrix

section SL

variable {F : Type} [Field F]

theorem commute_of_forall_commute {X : Subgroup (SpecialLinearGroup (Fin 2) F)}
    {x₁ x₂ : SpecialLinearGroup (Fin 2) F} (h₁ : x₁ ∈ X) (h₂ : x₂ ∈ X) (hne : x₁ * x₂ ≠ x₂ * x₁)
    {u v : SpecialLinearGroup (Fin 2) F} (hu : ∀ x ∈ X, u * x = x * u) : u * v = v * u := by
  by_cases hs : (u : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (u : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (u : Matrix (Fin 2) (Fin 2) F) 0 0 = (u : Matrix (Fin 2) (Fin 2) F) 1 1
  · obtain ⟨h01, h10, hd⟩ := hs
    apply Subtype.ext
    show (u : Matrix (Fin 2) (Fin 2) F) * v = (v : Matrix (Fin 2) (Fin 2) F) * u
    refine Matrix.ext fun i j => ?_
    revert i j
    simp only [Fin.forall_fin_two, mul_apply_two, h01, h10, hd]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring
  · exfalso
    apply hne
    have hy : (u : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 ∨ (u : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 ∨
        (u : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ (u : Matrix (Fin 2) (Fin 2) F) 1 1 := by
      tauto
    have c₁ : (u : Matrix (Fin 2) (Fin 2) F) * x₁ = (x₁ : Matrix (Fin 2) (Fin 2) F) * u :=
      congrArg Subtype.val (hu x₁ h₁)
    have c₂ : (u : Matrix (Fin 2) (Fin 2) F) * x₂ = (x₂ : Matrix (Fin 2) (Fin 2) F) * u :=
      congrArg Subtype.val (hu x₂ h₂)
    exact Subtype.ext (mul_comm_of_commute_nonscalar hy c₁.symm c₂.symm)

end SL

section PSL

variable {p : ℕ} [Fact p.Prime]

@[expose] def tm : Matrix (Fin 2) (Fin 2) (ZMod p) := !![1, 1; 0, 1]

theorem tm_pow (m : ℕ) :
    (tm : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ m = !![1, (m : ZMod p); 0, 1] := by
  induction m with
  | zero => rw [pow_zero, Matrix.one_fin_two]; simp
  | succ m ih =>
    rw [pow_succ, ih, tm, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]

@[expose] def tr : SpecialLinearGroup (Fin 2) (ZMod p) :=
  ⟨tm, by simp [tm, Matrix.det_fin_two]⟩

theorem tr_pow_apply (m : ℕ) :
    ((tr ^ m : SpecialLinearGroup (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = m := by
  show (tm ^ m) 0 1 = (m : ZMod p)
  rw [tm_pow]
  simp

theorem le_center_of_isPGroup_two (hp : 5 ≤ p)
    {N : Subgroup (SpecialLinearGroup (Fin 2) (ZMod p))} (hN : N.Normal) (h2 : IsPGroup 2 N) :
    N ≤ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)) := by
  have hF : 4 ≤ Nat.card (ZMod p) := by rw [Nat.card_zmod]; omega
  have hsimple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  set π := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)))
  have hNπ : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  rcases (haveI := hNπ; hsimple.eq_bot_or_eq_top_of_normal (N.map π)) with h | h
  · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · exfalso
    have h2π : IsPGroup 2 (N.map π) := h2.map π
    obtain ⟨k, hk⟩ := h2π ⟨π tr, by rw [h]; exact Subgroup.mem_top _⟩
    have hk' : π tr ^ (2 ^ k) = 1 := by
      have h' := congrArg Subtype.val hk
      simpa only [SubmonoidClass.coe_pow, OneMemClass.coe_one] using h'
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hk'
    obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hk'
    have h01 : (Matrix.scalar (Fin 2) c) 0 1 = ((2 ^ k : ℕ) : ZMod p) := by
      rw [hc]
      exact tr_pow_apply (2 ^ k)
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (show (0 : Fin 2) ≠ 1 by decide)]
      at h01
    have hdvd : p ∣ 2 ^ k := (ZMod.natCast_eq_zero_iff (2 ^ k) p).mp h01.symm
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hdvd)
    omega

end PSL

section Perfect

variable {G : Type*} [Group G]

theorem eq_bot_of_perfect_of_le {H N : Subgroup G} [Group.IsSolvable ↥N] (hHN : H ≤ N)
    (hH : ⁅H, H⁆ = H) : H = ⊥ := by
  have hmap : (H.subgroupOf N).map N.subtype = H := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hHN]
  have hperf : ⁅H.subgroupOf N, H.subgroupOf N⁆ = H.subgroupOf N :=
    Subgroup.map_injective N.subtype_injective (by rw [Subgroup.map_commutator, hmap, hH])
  by_contra hne
  have hne' : H.subgroupOf N ≠ ⊥ := fun h => hne (by rw [← hmap, h, Subgroup.map_bot])
  exact (Group.IsSolvable.commutator_lt_of_ne_bot hne').ne hperf

end Perfect

end CFSG.Quasithin.Vol2.Ch10.SecB.KRP
