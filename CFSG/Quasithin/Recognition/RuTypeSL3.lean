module

public import CFSG.Quasithin.Recognition.RuTypeDefs

public section

namespace CFSG.Quasithin.RuType.SL3

open scoped MatrixGroups

abbrev mat (g : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) := g

theorem eq_one_of_fix_all {g : SL(3, ZMod 2)} (h : ∀ v, natAct3 g v = v) : g = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [natAct3, Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem natAct3_mul (g h : SL(3, ZMod 2)) (v : Fin 3 → ZMod 2) :
    natAct3 (g * h) v = natAct3 g (natAct3 h v) := by
  simp [natAct3, Matrix.mulVec_mulVec]

theorem natAct3_one (v : Fin 3 → ZMod 2) : natAct3 1 v = v := by
  simp [natAct3]

@[expose] def P0 : Subgroup SL(3, ZMod 2) where
  carrier := {g | mat g 1 0 = 0 ∧ mat g 2 0 = 0 ∧ mat g 2 1 = 0}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_three]
    simp [ha1, ha2, ha3, hb1, hb2, hb3]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
    simp [ha1, ha2, ha3]

instance : DecidablePred (· ∈ P0) := fun g =>
  inferInstanceAs (Decidable (mat g 1 0 = 0 ∧ mat g 2 0 = 0 ∧ mat g 2 1 = 0))

theorem card_P0 : Nat.card P0 = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_SL3 : Nat.card SL(3, ZMod 2) = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three]

@[expose] noncomputable def sylowP0 : Sylow 2 SL(3, ZMod 2) :=
  Sylow.ofCard P0 (by
    rw [card_P0, card_SL3]
    have : (168 : ℕ).factorization 2 = 3 := by
      rw [show (168 : ℕ) = 2 ^ 3 * 21 by norm_num, Nat.factorization_mul (by norm_num)
        (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
      simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 21 by norm_num)]
    rw [this]
    norm_num)

theorem exists_conj_eq_P0 {P : Subgroup SL(3, ZMod 2)} (hP : Nat.card P = 8) :
    ∃ g : SL(3, ZMod 2), P = P0.map (MulAut.conj g).toMonoidHom := by
  have hfact : (Nat.card SL(3, ZMod 2)).factorization 2 = 3 := by
    rw [card_SL3, show (168 : ℕ) = 2 ^ 3 * 21 by norm_num, Nat.factorization_mul (by norm_num)
      (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 21 by norm_num)]
  let SP : Sylow 2 SL(3, ZMod 2) := Sylow.ofCard P (by rw [hP, hfact]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(3, ZMod 2) sylowP0 SP
  refine ⟨g, ?_⟩
  have := congrArg (fun Q : Sylow 2 SL(3, ZMod 2) => (Q : Subgroup SL(3, ZMod 2))) hg
  simp only [Sylow.coe_subgroup_smul, SP, Sylow.coe_ofCard] at this
  rw [← this]
  rfl

theorem fix_P0 (v : Fin 3 → ZMod 2) :
    (∀ g ∈ P0, natAct3 g v = v) ↔ v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · intro h
    have hx : (⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩ : SL(3, ZMod 2)) ∈ P0 :=
      ⟨by decide, by decide, by decide⟩
    have hy : (⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩ : SL(3, ZMod 2)) ∈ P0 :=
      ⟨by decide, by decide, by decide⟩
    have h1 := congrFun (h _ hx) 0
    have h2 := congrFun (h _ hy) 1
    simp [natAct3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ g ⟨hg1, hg2, hg3⟩
    have hdet : (mat g).det = 1 := g.2
    rw [Matrix.det_fin_three] at hdet
    simp only [hg1, hg2, hg3, mul_zero, zero_mul, add_zero] at hdet
    have hd : mat g 0 0 = 1 ∧ mat g 1 1 = 1 ∧ mat g 2 2 = 1 := by
      have key : ∀ a b c : ZMod 2, a * b * c - 0 - 0 - 0 = 1 → a = 1 ∧ b = 1 ∧ c = 1 := by
        decide
      exact key _ _ _ hdet
    funext i
    fin_cases i <;>
      simp [natAct3, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2, hg1, hg2, hg3,
        hd.1, hd.2.1, hd.2.2]

theorem card_fix_of_card_eq_eight {P : Subgroup SL(3, ZMod 2)} (hP : Nat.card P = 8) :
    Nat.card {v : Fin 3 → ZMod 2 // ∀ g ∈ P, natAct3 g v = v} = 2 := by
  obtain ⟨g, rfl⟩ := exists_conj_eq_P0 hP
  have hc : ∀ (h : SL(3, ZMod 2)) (v : Fin 3 → ZMod 2),
      natAct3 (g * h * g⁻¹) v = v ↔ natAct3 h (natAct3 g⁻¹ v) = natAct3 g⁻¹ v := by
    intro h v
    rw [natAct3_mul, natAct3_mul]
    constructor
    · intro e
      have e' := congrArg (natAct3 g⁻¹) e
      rwa [← natAct3_mul g⁻¹ g, inv_mul_cancel, natAct3_one] at e'
    · intro e
      rw [e, ← natAct3_mul, mul_inv_cancel, natAct3_one]
  have key : ∀ v : Fin 3 → ZMod 2, (∀ h ∈ P0.map (MulAut.conj g).toMonoidHom,
      natAct3 h v = v) ↔ (∀ h ∈ P0, natAct3 h (natAct3 g⁻¹ v) = natAct3 g⁻¹ v) := by
    intro v
    constructor
    · intro hv h hh
      have := hv _ (Subgroup.mem_map_of_mem _ hh)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      exact (hc h v).mp this
    · rintro hv _ ⟨h, hh, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (hc h v).mpr (hv h hh)
  have e : {v : Fin 3 → ZMod 2 // ∀ h ∈ P0.map (MulAut.conj g).toMonoidHom, natAct3 h v = v} ≃
      {v : Fin 3 → ZMod 2 // v 1 = 0 ∧ v 2 = 0} :=
    { toFun := fun v => ⟨natAct3 g⁻¹ v.1, (fix_P0 _).mp ((key v.1).mp v.2)⟩
      invFun := fun w => ⟨natAct3 g w.1, (key _).mpr (by
          rw [← natAct3_mul, inv_mul_cancel, natAct3_one]
          exact (fix_P0 _).mpr w.2)⟩
      left_inv := fun v => Subtype.ext (by
        simp only
        rw [← natAct3_mul, mul_inv_cancel, natAct3_one])
      right_inv := fun w => Subtype.ext (by
        simp only
        rw [← natAct3_mul, inv_mul_cancel, natAct3_one]) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

@[expose] def natEquiv (g : SL(3, ZMod 2)) :
    Multiplicative (Fin 3 → ZMod 2) ≃* Multiplicative (Fin 3 → ZMod 2) where
  toFun x := Multiplicative.ofAdd (natAct3 g (Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd (natAct3 g⁻¹ (Multiplicative.toAdd x))
  left_inv x := by
    simp only [toAdd_ofAdd]
    rw [← natAct3_mul, inv_mul_cancel, natAct3_one]
    rfl
  right_inv x := by
    simp only [toAdd_ofAdd]
    rw [← natAct3_mul, mul_inv_cancel, natAct3_one]
    rfl
  map_mul' x y := by
    simp [natAct3, Matrix.mulVec_add, toAdd_mul]

theorem natEquiv_apply (g : SL(3, ZMod 2)) (x : Multiplicative (Fin 3 → ZMod 2)) :
    Multiplicative.toAdd (natEquiv g x) = natAct3 g (Multiplicative.toAdd x) := rfl

theorem stAct_mul (g h : SL(3, ZMod 2)) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    stAct (g * h) A = stAct g (stAct h A) := by
  simp [stAct, Matrix.mul_assoc]

theorem stAct_one (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : stAct 1 A = A := by
  simp [stAct]

theorem stAct_add (g : SL(3, ZMod 2)) (A B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    stAct g (A + B) = stAct g A + stAct g B := by
  simp [stAct, Matrix.mul_add, Matrix.add_mul]

theorem trace_stAct (g : SL(3, ZMod 2)) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (stAct g A).trace = A.trace := by
  unfold stAct
  rw [Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

@[expose] def stHom (g : SL(3, ZMod 2)) :
    Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)) →*
      Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)) where
  toFun x := Multiplicative.ofAdd (stAct g (Multiplicative.toAdd x))
  map_one' := by simp [stAct]
  map_mul' x y := by simp [toAdd_mul, stAct_add]

theorem stHom_apply (g : SL(3, ZMod 2)) (x : Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) :
    Multiplicative.toAdd (stHom g x) = stAct g (Multiplicative.toAdd x) := rfl

theorem stHom_injective (g : SL(3, ZMod 2)) : Function.Injective (stHom g) := by
  intro x y h
  have e := congrArg (fun z => stAct g⁻¹ (Multiplicative.toAdd z)) h
  simp only [stHom_apply, ← stAct_mul, inv_mul_cancel, stAct_one] at e
  exact e

theorem exists_fixed_ne {P : Type*} [Group P] (hP : IsPGroup 2 P) {α : Type*}
    (act : P → α → α) (h1 : ∀ a, act 1 a = a) (hmul : ∀ g h a, act (g * h) a = act g (act h a))
    (X : Set α) [Finite X] (hX : ∀ g, ∀ a ∈ X, act g a ∈ X) (h2 : 2 ∣ Nat.card X)
    {a₀ : α} (ha₀ : a₀ ∈ X) (hfix : ∀ g, act g a₀ = a₀) :
    ∃ b ∈ X, b ≠ a₀ ∧ ∀ g, act g b = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction P X :=
    { smul := fun g a => ⟨act g a, hX g a a.2⟩
      one_smul := fun a => Subtype.ext (h1 a)
      mul_smul := fun g h a => Subtype.ext (hmul g h a) }
  obtain ⟨⟨b, hb⟩, hbfix, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point X h2
    (a := ⟨a₀, ha₀⟩) (fun g => Subtype.ext (hfix g))
  refine ⟨b, hb, fun e => hne (Subtype.ext e.symm), fun g => ?_⟩
  have := hbfix g
  exact congrArg Subtype.val this

abbrev e0 : Fin 3 → ZMod 2 := ![1, 0, 0]

@[expose] def Stab0 : Subgroup SL(3, ZMod 2) where
  carrier := {g | natAct3 g e0 = e0}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [natAct3_mul, hb, ha]
  one_mem' := natAct3_one e0
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← natAct3_mul, inv_mul_cancel, natAct3_one]

theorem mem_Stab0 {g : SL(3, ZMod 2)} : g ∈ Stab0 ↔ natAct3 g e0 = e0 := Iff.rfl

instance : DecidablePred (· ∈ Stab0) := fun g =>
  inferInstanceAs (Decidable (natAct3 g e0 = e0))

theorem card_Stab0 : Nat.card Stab0 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] def R0 : Subgroup SL(3, ZMod 2) where
  carrier := {g | mat g 0 0 = 1 ∧ mat g 1 0 = 0 ∧ mat g 2 0 = 0 ∧ mat g 1 1 = 1 ∧
    mat g 1 2 = 0 ∧ mat g 2 1 = 0 ∧ mat g 2 2 = 1}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_three]
    simp [ha1, ha2, ha3, ha4, ha5, ha6, ha7, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
    simp [ha1, ha2, ha3, ha4, ha5, ha6, ha7]

instance : DecidablePred (· ∈ R0) := fun g =>
  inferInstanceAs (Decidable (mat g 0 0 = 1 ∧ mat g 1 0 = 0 ∧ mat g 2 0 = 0 ∧ mat g 1 1 = 1 ∧
    mat g 1 2 = 0 ∧ mat g 2 1 = 0 ∧ mat g 2 2 = 1))

theorem card_R0 : Nat.card R0 = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem R0_le_Stab0 : R0 ≤ Stab0 := by
  intro g hg
  revert g
  decide +kernel

theorem R0_le_P0 : R0 ≤ P0 := by
  intro g hg
  revert g
  decide +kernel

theorem conj_mem_R0 : ∀ g ∈ Stab0, ∀ x ∈ R0, g * x * g⁻¹ ∈ R0 := by
  decide +kernel

theorem conj_R0_transitive : ∀ x ∈ R0, x ≠ 1 → ∀ y ∈ R0, y ≠ 1 →
    ∃ g ∈ Stab0, g * x * g⁻¹ = y := by
  decide +kernel

theorem natAct3_R0 : ∀ g ∈ R0, ∀ v : Fin 3 → ZMod 2,
    natAct3 g v + v = 0 ∨ natAct3 g v + v = e0 := by
  decide +kernel

theorem exists_R0_move : ∃ g ∈ R0, natAct3 g ![0, 1, 0] ≠ ![0, 1, 0] := by
  decide +kernel

theorem Stab0_transitive : ∀ v w : Fin 3 → ZMod 2, v ≠ 0 → v ≠ e0 → w ≠ 0 → w ≠ e0 →
    ∃ g ∈ Stab0, natAct3 g v = w := by
  decide +kernel

theorem SL3_transitive : ∀ v w : Fin 3 → ZMod 2, v ≠ 0 → w ≠ 0 →
    ∃ g : SL(3, ZMod 2), natAct3 g v = w := by
  decide +kernel

theorem P0_le_Stab0 : P0 ≤ Stab0 := by
  intro g hg
  revert g
  decide +kernel

theorem pow_four_of_pow_eight : ∀ x : SL(3, ZMod 2), x ^ 8 = 1 → x ^ 4 = 1 := by
  decide +kernel

theorem exists_comm_order_three : ∀ x ∈ Stab0, x ∉ R0 → x ^ 4 = 1 →
    ∃ g ∈ Stab0, x * g * x⁻¹ * g⁻¹ ≠ 1 ∧ (x * g * x⁻¹ * g⁻¹) ^ 3 = 1 := by
  decide +kernel

abbrev stA0 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 0, 0, 0; 0, 0, 0]

theorem fix_P0_st : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 →
    (∀ g ∈ P0, stAct g A = A) → A = 0 ∨ A = stA0 := by
  intro A hA h
  have hx : (⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩ : SL(3, ZMod 2)) ∈ P0 :=
    ⟨by decide, by decide, by decide⟩
  have hy : (⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩ : SL(3, ZMod 2)) ∈ P0 :=
    ⟨by decide, by decide, by decide⟩
  have key : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 →
      (stAct ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩ A = A ∧
       stAct ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩ A = A) → A = 0 ∨ A = stA0 := by
    decide +kernel
  exact key A hA ⟨h _ hx, h _ hy⟩

theorem stA0_fix : ∀ g ∈ P0, stAct g stA0 = stA0 := by
  decide +kernel

@[expose] def stGens : Fin 8 → SL(3, ZMod 2) :=
  ![⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide⟩, ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩,
    ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide⟩, ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩,
    ⟨!![0, 1, 0; 1, 0, 0; 1, 0, 1], by decide⟩, ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide⟩,
    ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], by decide⟩, ⟨!![1, 0, 0; 0, 1, 0; 1, 0, 1], by decide⟩]

@[expose] def stBasis (i : Fin 8) : Matrix (Fin 3) (Fin 3) (ZMod 2) := stAct (stGens i) stA0

@[expose] def stComb (c : Fin 8 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ∑ i, c i • stBasis i

theorem stComb_trace (c : Fin 8 → ZMod 2) : (stComb c).trace = 0 := by
  revert c
  decide +kernel

theorem stComb_eq_zero : ∀ c : Fin 8 → ZMod 2, stComb c = 0 → c = 0 := by
  decide +kernel

theorem stComb_add (c d : Fin 8 → ZMod 2) : stComb (c + d) = stComb c + stComb d := by
  simp [stComb, add_smul, Finset.sum_add_distrib]

theorem stComb_injective : Function.Injective stComb := by
  intro c d h
  have : stComb (c - d) = 0 := by
    have e : c - d = c + d := by
      funext i
      have : ∀ x y : ZMod 2, x - y = x + y := by decide
      exact this _ _
    rw [e, stComb_add, h]
    have : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M + M = 0 := fun M => by
      ext i j
      have : ∀ x : ZMod 2, x + x = 0 := by decide
      exact this _
    exact this _
  exact sub_eq_zero.mp (stComb_eq_zero _ this)

theorem card_traceZero :
    Fintype.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // A.trace = 0} = 256 := by
  let f : Matrix (Fin 3) (Fin 3) (ZMod 2) →+ ZMod 2 := Matrix.traceAddMonoidHom (Fin 3) (ZMod 2)
  have hf : Function.Surjective f := fun c =>
    ⟨Matrix.diagonal (fun i => if i = 0 then c else 0), by simp [f, Matrix.trace]⟩
  have h := AddSubgroup.card_ker_mul_card_of_surjective hf
  have hM : Nat.card (Matrix (Fin 3) (Fin 3) (ZMod 2)) = 512 := by
    rw [Nat.card_eq_fintype_card]
    show Fintype.card (Fin 3 → Fin 3 → ZMod 2) = 512
    rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hk : Nat.card f.ker =
      Fintype.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // A.trace = 0} := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun A => by simp [f, AddMonoidHom.mem_ker])
  rw [h2, hM, hk] at h
  omega

@[expose] def stCombTZ (c : Fin 8 → ZMod 2) :
    {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // A.trace = 0} :=
  ⟨stComb c, stComb_trace c⟩

theorem stCombTZ_injective : Function.Injective stCombTZ := by
  intro c d h
  apply stComb_injective
  have := Subtype.ext_iff.mp h
  simpa only [stCombTZ] using this

theorem exists_stComb {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : A.trace = 0) :
    ∃ c, stComb c = A := by
  have hcard : Fintype.card (Fin 8 → ZMod 2) =
      Fintype.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // A.trace = 0} := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, card_traceZero]
    norm_num
  obtain ⟨c, hc⟩ := ((Fintype.bijective_iff_injective_and_card stCombTZ).mpr
    ⟨stCombTZ_injective, hcard⟩).2 ⟨A, hA⟩
  refine ⟨c, ?_⟩
  have := Subtype.ext_iff.mp hc
  simpa only [stCombTZ] using this

theorem st_irreducible (X : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hX : ∀ A ∈ X, A.trace = 0) (hinv : ∀ g : SL(3, ZMod 2), ∀ A ∈ X, stAct g A ∈ X)
    (hne : X ≠ ⊥) {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : A.trace = 0) : A ∈ X := by
  have hP : IsPGroup 2 P0 := by
    rw [IsPGroup.iff_card, card_P0]
    exact ⟨3, rfl⟩
  have h2 : 2 ∣ Nat.card (X : Set (Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
    have hdvd : Nat.card X ∣ 2 ^ 9 := by
      have := AddSubgroup.card_addSubgroup_dvd_card X
      rwa [Nat.card_eq_fintype_card (α := Matrix (Fin 3) (Fin 3) (ZMod 2)),
        show Fintype.card (Matrix (Fin 3) (Fin 3) (ZMod 2)) = 2 ^ 9 by
          show Fintype.card (Fin 3 → Fin 3 → ZMod 2) = 2 ^ 9
          rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin]
          norm_num] at this
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hne
      rw [pow_zero] at hk'
      exact AddSubgroup.eq_bot_of_card_eq X hk'
    show 2 ∣ Nat.card X
    rw [hk']
    exact dvd_pow_self 2 hk0
  obtain ⟨B, hB, hB0, hBfix⟩ := exists_fixed_ne hP (fun g A => stAct (g : SL(3, ZMod 2)) A)
    (fun A => stAct_one A) (fun g h A => stAct_mul g h A) (X : Set _)
    (fun g A hA => hinv g A hA) h2 X.zero_mem (fun g => by simp [stAct])
  have hBeq : B = stA0 := by
    rcases fix_P0_st B (hX B hB) (fun g hg => hBfix ⟨g, hg⟩) with h | h
    · exact absurd h hB0
    · exact h
  rw [hBeq] at hB
  obtain ⟨c, rfl⟩ := exists_stComb hA
  unfold stComb
  refine AddSubgroup.sum_mem X fun i _ => ?_
  have hMi : stBasis i ∈ X := hinv (stGens i) stA0 hB
  have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hc (c i) with h | h
  · rw [h, zero_smul]
    exact X.zero_mem
  · rw [h, one_smul]
    exact hMi

end CFSG.Quasithin.RuType.SL3
