module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.Quasithin.H13.NQCat.T513.L35

open Matrix

abbrev G35 := Matrix.SpecialLinearGroup (Fin 3) (ZMod 5)

theorem card_G35 : Nat.card G35 = 372000 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  change Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 5)) = 372000
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
  decide

@[expose] def IsMon (M : Matrix (Fin 3) (Fin 3) (ZMod 5)) : Prop :=
  M 0 2 = 0 ∧ M 1 2 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 2 2 ≠ 0 ∧
    ((M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 ≠ 0 ∧ M 1 1 ≠ 0) ∨
      (M 0 0 = 0 ∧ M 1 1 = 0 ∧ M 0 1 ≠ 0 ∧ M 1 0 ≠ 0))

theorem isMon_mul {M N : Matrix (Fin 3) (Fin 3) (ZMod 5)} (hM : IsMon M) (hN : IsMon N) :
    IsMon (M * N) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨m02, m12, m20, m21, m22, hm⟩ := hM
  obtain ⟨n02, n12, n20, n21, n22, hn⟩ := hN
  simp only [IsMon, Matrix.mul_apply, Fin.sum_univ_three, m02, m12, m20, m21, n02, n12, n20, n21,
    mul_zero, zero_mul, add_zero, zero_add]
  refine ⟨trivial, trivial, trivial, trivial, mul_ne_zero m22 n22, ?_⟩
  rcases hm with ⟨m01, m10, m00, m11⟩ | ⟨m00, m11, m01, m10⟩ <;>
    rcases hn with ⟨n01, n10, n00, n11⟩ | ⟨n00, n11, n01, n10⟩ <;>
    simp only [m01, m10, m00, m11, n01, n10, n00, n11, mul_zero, zero_mul, add_zero, zero_add,
      true_and, ne_eq, mul_eq_zero, or_self, not_false_eq_true, and_true, and_self, true_or,
      or_true, false_or]
  all_goals first
    | exact Or.inl ⟨by simp [*], by simp [*]⟩
    | exact Or.inr ⟨by simp [*], by simp [*]⟩
    | simp [*]

@[expose] noncomputable def T0 : Subgroup G35 :=
  Subgroup.closure {g : G35 | IsMon (g : Matrix (Fin 3) (Fin 3) (ZMod 5))}

theorem isMon_one : IsMon ((1 : G35) : Matrix (Fin 3) (Fin 3) (ZMod 5)) := by
  simp only [IsMon, Matrix.SpecialLinearGroup.coe_one]
  decide

theorem mem_T0_iff {g : G35} : g ∈ T0 ↔ IsMon (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) := by
  have hmul : ∀ x y : G35, IsMon (x : Matrix (Fin 3) (Fin 3) (ZMod 5)) →
      IsMon (y : Matrix (Fin 3) (Fin 3) (ZMod 5)) →
      IsMon ((x * y : G35) : Matrix (Fin 3) (Fin 3) (ZMod 5)) := by
    intro x y hx hy
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact isMon_mul hx hy
  have hpow : ∀ (x : G35) (n : ℕ), IsMon (x : Matrix (Fin 3) (Fin 3) (ZMod 5)) →
      IsMon ((x ^ n : G35) : Matrix (Fin 3) (Fin 3) (ZMod 5)) := by
    intro x n hx
    induction n with
    | zero => rw [pow_zero]; exact isMon_one
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih hx
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact isMon_one
    | mul x y _ _ hx hy => exact hmul x y hx hy
    | inv x _ hx =>
      have h1 : x⁻¹ = x ^ (orderOf x - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
          Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
      rw [h1]
      exact hpow x _ hx
  · intro hg
    exact Subgroup.subset_closure hg

@[expose] def monMat (e : Bool) (a b : ZMod 5) : Matrix (Fin 3) (Fin 3) (ZMod 5) :=
  if e then !![0, a, 0; b, 0, 0; 0, 0, -(a * b)⁻¹] else !![a, 0, 0; 0, b, 0; 0, 0, (a * b)⁻¹]

theorem det_monMat (e : Bool) {a b : ZMod 5} (ha : a ≠ 0) (hb : b ≠ 0) :
    (monMat e a b).det = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  cases e <;> simp [monMat, Matrix.det_fin_three] <;> field_simp

theorem isMon_monMat (e : Bool) {a b : ZMod 5} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsMon (monMat e a b) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  cases e <;> simp [IsMon, monMat, ha, hb, hab]

theorem card_monPar : Nat.card {p : Bool × ZMod 5 × ZMod 5 // p.2.1 ≠ 0 ∧ p.2.2 ≠ 0} = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_T0 : Nat.card T0 = 32 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let S := {p : Bool × ZMod 5 × ZMod 5 // p.2.1 ≠ 0 ∧ p.2.2 ≠ 0}
  let f : S → T0 := fun p => ⟨⟨monMat p.1.1 p.1.2.1 p.1.2.2, det_monMat _ p.2.1 p.2.2⟩,
    mem_T0_iff.mpr (isMon_monMat _ p.2.1 p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨e, a, b⟩, ha, hb⟩ ⟨⟨e', a', b'⟩, ha', hb'⟩ h
      have h1 := congrArg (fun x : T0 => ((x : G35) : Matrix (Fin 3) (Fin 3) (ZMod 5))) h
      simp only [f] at h1
      have h00 := congrFun (congrFun h1 0) 0
      have h01 := congrFun (congrFun h1 0) 1
      have h10 := congrFun (congrFun h1 1) 0
      have h11 := congrFun (congrFun h1 1) 1
      simp only at ha hb ha' hb'
      cases e <;> cases e' <;> simp [monMat] at h00 h01 h10 h11
      all_goals first
        | exact absurd h00 ha
        | exact absurd h00.symm ha'
        | exact absurd h01 ha
        | exact absurd h01.symm ha'
        | (subst h00; subst h11; rfl)
        | (subst h01; subst h10; rfl)
    · rintro ⟨g, hg⟩
      obtain ⟨m02, m12, m20, m21, m22, hm⟩ := mem_T0_iff.mp hg
      have hdet := g.2
      rw [Matrix.det_fin_three] at hdet
      rcases hm with ⟨m01, m10, m00, m11⟩ | ⟨m00, m11, m01, m10⟩
      · refine ⟨⟨⟨false, g 0 0, g 1 1⟩, m00, m11⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        simp only [m02, m12, m20, m21, m01, m10, mul_zero, zero_mul, sub_zero, add_zero] at hdet
        have h22 : (g 0 0 * g 1 1)⁻¹ = g 2 2 :=
          (eq_inv_of_mul_eq_one_left (by linear_combination hdet)).symm
        ext i j
        fin_cases i <;> fin_cases j <;> simp [f, monMat, m02, m12, m20, m21, m01, m10, h22]
      · refine ⟨⟨⟨true, g 0 1, g 1 0⟩, m01, m10⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        simp only [m02, m12, m20, m21, m00, m11, mul_zero, zero_mul, sub_zero, add_zero,
          zero_sub] at hdet
        have h22 : -(g 0 1 * g 1 0)⁻¹ = g 2 2 := by
          rw [← inv_neg]
          exact (eq_inv_of_mul_eq_one_left (by linear_combination hdet)).symm
        have h22' : -((g 1 0)⁻¹ * (g 0 1)⁻¹) = g 2 2 := by rw [← _root_.mul_inv_rev]; exact h22
        ext i j
        fin_cases i <;> fin_cases j <;> simp [f, monMat, m02, m12, m20, m21, m00, m11, h22, h22']
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  exact card_monPar

@[expose] noncomputable def T0Sylow : Sylow 2 G35 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard T0 (by
    rw [card_T0, card_G35, show (372000 : ℕ) = 2 ^ 5 * 11625 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simp)

theorem coe_T0Sylow : ((T0Sylow : Sylow 2 G35) : Subgroup G35) = T0 := rfl

end CFSG.Quasithin.H13.NQCat.T513.L35

end
