module

public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130Res5Proof

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem pow_three_eq_zero_of_isNilpotent {N : Matrix (Fin 3) (Fin 3) K} (hN : IsNilpotent N) :
    N ^ 3 = 0 := by
  have h1 := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
  have h2 : N.charpoly = Polynomial.X ^ 3 := by
    have := IsReduced.eq_zero _ h1
    simpa [sub_eq_zero] using this
  have h3 := Matrix.aeval_self_charpoly N
  rw [h2] at h3
  simpa using h3

theorem exists_eq_of_commute_of_sq_ne {N A : Matrix (Fin 3) (Fin 3) K} (hN3 : N ^ 3 = 0)
    {v : Fin 3 → K} (hv : (N ^ 2) *ᵥ v ≠ 0) (hAN : A * N = N * A) :
    ∃ α β γ : K, A = α • (1 : Matrix (Fin 3) (Fin 3) K) + β • N + γ • N ^ 2 := by
  set b : Fin 3 → (Fin 3 → K) := ![v, N *ᵥ v, (N ^ 2) *ᵥ v] with hb
  have hN4 : N ^ 4 = 0 := by rw [pow_succ, hN3, zero_mul]
  have hli : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, hb, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
    have e2 := congrArg (fun w => (N ^ 2) *ᵥ w) hg
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_zero]
      at e2
    rw [← pow_succ, ← pow_add, show 2 + 2 = 4 from rfl, hN4, show 2 + 1 = 3 from rfl, hN3]
      at e2
    simp only [Matrix.zero_mulVec, smul_zero, add_zero] at e2
    have hg0 : g 0 = 0 := (smul_eq_zero.mp e2).resolve_right hv
    rw [hg0, zero_smul, zero_add] at hg
    have e1 := congrArg (fun w => N *ᵥ w) hg
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_zero]
      at e1
    rw [← sq, ← pow_succ', hN3] at e1
    simp only [Matrix.zero_mulVec, smul_zero, add_zero] at e1
    have hg1 : g 1 = 0 := (smul_eq_zero.mp e1).resolve_right hv
    rw [hg1, zero_smul, zero_add] at hg
    have hg2 : g 2 = 0 := (smul_eq_zero.mp hg).resolve_right hv
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  have hspan : Submodule.span K (Set.range b) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hAv : A *ᵥ v ∈ Submodule.span K (Set.range b) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hAv
  refine ⟨c 0, c 1, c 2, ?_⟩
  set B := c 0 • (1 : Matrix (Fin 3) (Fin 3) K) + c 1 • N + c 2 • N ^ 2 with hB
  have hBv : B *ᵥ v = A *ᵥ v := by
    rw [← hc]
    simp only [Fin.sum_univ_three, hb, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hB, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hBN : B * N = N * B := by
    rw [hB]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, ← pow_succ, ← pow_succ']
  have hcomm : ∀ (X : Matrix (Fin 3) (Fin 3) K), X * N = N * X → ∀ k : ℕ,
      X * N ^ k = N ^ k * X := by
    intro X hX k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hX, Matrix.mul_assoc]
  apply Matrix.toLin'.injective
  refine LinearMap.ext_on_range hspan fun i => ?_
  have key : ∀ k : ℕ, A *ᵥ ((N ^ k) *ᵥ v) = B *ᵥ ((N ^ k) *ᵥ v) := by
    intro k
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm A hAN k, hcomm B hBN k,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBv]
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  have hb0 : b 0 = (N ^ 0) *ᵥ v := by simp [hb]
  have hb1 : b 1 = (N ^ 1) *ᵥ v := by simp [hb]
  have hb2 : b 2 = (N ^ 2) *ᵥ v := by simp [hb]
  fin_cases i
  · change A *ᵥ b 0 = B *ᵥ b 0
    rw [hb0]
    exact key 0
  · change A *ᵥ b 1 = B *ᵥ b 1
    rw [hb1]
    exact key 1
  · change A *ᵥ b 2 = B *ᵥ b 2
    rw [hb2]
    exact key 2

section CharTwo

variable [CharP K 2]

theorem pow_four_eq_smul_one {N : Matrix (Fin 3) (Fin 3) K} (hN3 : N ^ 3 = 0) (α β γ : K) :
    (α • (1 : Matrix (Fin 3) (Fin 3) K) + β • N + γ • N ^ 2) ^ 4 = α ^ 4 • 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Matrix (Fin 3) (Fin 3) K := β • 1 + γ • N with hC
  have hM : β • N + γ • N ^ 2 = N * C := by
    rw [hC, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, ← sq]
  have hNC : Commute N C := by
    rw [hC]
    exact (Commute.add_right ((Commute.one_right N).smul_right β)
      ((Commute.refl N).smul_right γ))
  rw [add_assoc, hM]
  have hcomm : Commute (α • (1 : Matrix (Fin 3) (Fin 3) K)) (N * C) :=
    (Commute.one_left _).smul_left α
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4, add_pow_char_pow_of_commute (p := 2) (n := 2) (h := hcomm), hNC.mul_pow, ← h4,
    show N ^ 4 = N ^ 3 * N by rw [pow_succ], hN3, zero_mul, zero_mul, add_zero, smul_pow,
    one_pow]

theorem exists_pow_four_eq_smul_one {A g : GL (Fin 3) K} (hAg : A * g = g * A) {k : ℕ}
    (hg : g ^ 2 ^ k = 1) (hg2 : g ^ 2 ≠ 1) :
    ∃ α : K, ((A : Matrix (Fin 3) (Fin 3) K)) ^ 4 = α • 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K) - 1 with hN
  have hcomm1 : Commute (g : Matrix (Fin 3) (Fin 3) K) 1 := Commute.one_right _
  have hNk : N ^ 2 ^ k = 0 := by
    rw [hN, sub_pow_char_pow_of_commute (p := 2) (n := k) (h := hcomm1), one_pow,
      ← Units.val_pow_eq_pow_val, hg, Units.val_one, sub_self]
  have hN3 : N ^ 3 = 0 := pow_three_eq_zero_of_isNilpotent ⟨_, hNk⟩
  have hN2 : N ^ 2 ≠ 0 := by
    intro h0
    apply hg2
    have h1 : N ^ 2 ^ 1 = 0 := by rw [pow_one]; exact h0
    rw [hN, sub_pow_char_pow_of_commute (p := 2) (n := 1) (h := hcomm1), one_pow, pow_one,
      sub_eq_zero] at h1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, h1, Units.val_one]
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → K, (N ^ 2) *ᵥ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hN2
    rw [Matrix.ext_iff_mulVec]
    intro w
    rw [hcon w, Matrix.zero_mulVec]
  have hAN : (A : Matrix (Fin 3) (Fin 3) K) * N = N * A := by
    have h1 : (A : Matrix (Fin 3) (Fin 3) K) * g = g * A := by
      rw [← Units.val_mul, hAg, Units.val_mul]
    rw [hN, Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_one, Matrix.one_mul]
  obtain ⟨α, β, γ, hA⟩ := exists_eq_of_commute_of_sq_ne hN3 hv hAN
  exact ⟨α ^ 4, by rw [hA, pow_four_eq_smul_one hN3]⟩

noncomputable abbrev uSL : Matrix (Fin 3) (Fin 3) K := !![1, 1, 0; 0, 1, 1; 0, 0, 1]

omit [CharP K 2] in
theorem det_uSL : (uSL : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [uSL, Matrix.det_fin_three]

theorem uSL_sq : (uSL : Matrix (Fin 3) (Fin 3) K) ^ 2 = !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, sq, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem uSL_pow_four : (uSL : Matrix (Fin 3) (Fin 3) K) ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, uSL_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_three]; grind

theorem exists_statedSL : ∃ x : StatedSL 3 K, x ^ 2 ≠ 1 ∧ x ^ 4 = 1 := by
  set u : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero uSL
    (by rw [det_uSL]; exact one_ne_zero) with hu
  have hmem : u ∈ StatedSL 3 K := Subgroup.subset_closure
    (show (u : Matrix (Fin 3) (Fin 3) K).det = 1 from det_uSL)
  refine ⟨⟨u, hmem⟩, fun h => ?_, ?_⟩
  · have h1 := congrArg (fun z : StatedSL 3 K => ((z : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) h
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] at h1
    have h2 : (u : Matrix (Fin 3) (Fin 3) K) = uSL := rfl
    rw [h2, uSL_sq] at h1
    have h3 := congrFun (congrFun h1 0) 2
    simp at h3
  · apply Subtype.ext
    apply Units.ext
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one]
    exact uSL_pow_four

noncomputable abbrev uSU (ω : K) : Matrix (Fin 3) (Fin 3) K :=
  !![ω ^ 2, ω, 1; ω, ω ^ 2, 1; 1, 1, 1]

theorem det_uSU {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : (uSU ω).det = 1 := by
  rw [uSU, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const]
  grind

theorem uSU_sq {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (uSU ω) ^ 2 = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSU, sq, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem uSU_pow_four {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : (uSU ω) ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, uSU_sq hω]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_three]

theorem uSU_unitary {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {q : ℕ} (hq : q % 3 = 2) :
    ((uSU ω).map (· ^ q))ᵀ * uSU ω = 1 := by
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hq' : ω ^ q = ω ^ 2 := by
    rw [← Nat.div_add_mod q 3, hq, pow_add, pow_mul, h3, one_pow, one_mul]
  have hq'' : (ω ^ 2) ^ q = ω := by
    rw [← pow_mul, mul_comm, pow_mul, hq', ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, h3,
      one_mul, pow_one]
  have hmap : (uSU ω).map (· ^ q) = !![ω, ω ^ 2, 1; ω ^ 2, ω, 1; 1, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uSU, hq', hq'']
  rw [hmap]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSU, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem exists_statedSU {q : ℕ} (hq : q % 3 = 2) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ x : StatedSU 3 q K, x ^ 2 ≠ 1 ∧ x ^ 4 = 1 := by
  set u : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (uSU ω)
    (by rw [det_uSU hω]; exact one_ne_zero) with hu
  have h2 : (u : Matrix (Fin 3) (Fin 3) K) = uSU ω := rfl
  have hmem : u ∈ StatedSU 3 q K := Subgroup.subset_closure
    (show (u : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
        ((u : Matrix (Fin 3) (Fin 3) K).map (· ^ q))ᵀ * (u : Matrix (Fin 3) (Fin 3) K) = 1 by
      rw [h2]; exact ⟨det_uSU hω, uSU_unitary hω hq⟩)
  refine ⟨⟨u, hmem⟩, fun h => ?_, ?_⟩
  · have h1 := congrArg (fun z : StatedSU 3 q K => ((z : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) h
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] at h1
    rw [h2, uSU_sq hω] at h1
    have h3 := congrFun (congrFun h1 0) 0
    simp at h3
  · apply Subtype.ext
    apply Units.ext
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one]
    rw [h2]
    exact uSU_pow_four hω

end CharTwo

theorem exists_sq_ne_one_of_isSLThreePiAt {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (hX : Sec4.IsSLThreePiAt X (2 ^ m)) : ∃ x : X, x ^ 2 ≠ 1 ∧ x ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, ⟨hF, -, ⟨e⟩⟩ | ⟨hF, hq, ⟨e⟩⟩⟩ := hX
  · have : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hF])
    obtain ⟨x, hx2, hx4⟩ := exists_statedSL (K := F)
    refine ⟨e.symm x, fun h => hx2 ?_, ?_⟩
    · rw [← map_pow, MulEquiv.map_eq_one_iff] at h
      exact h
    · rw [← map_pow, hx4, map_one]
  · have : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := 2 * m)
      (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
    have hK : Sec4.PiField false 2 m F := ⟨Nat.prime_two, hm, hF⟩
    obtain ⟨τ, hτ3, hτ1⟩ := Sec4.exists_tau hK hq
    have hω : τ ^ 2 + τ + 1 = 0 := by
      have h1 : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ3
      exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hτ1)
    obtain ⟨x, hx2, hx4⟩ := exists_statedSU (K := F) hq hω
    refine ⟨e.symm x, fun h => hx2 ?_, ?_⟩
    · rw [← map_pow, MulEquiv.map_eq_one_iff] at h
      exact h
    · rw [← map_pow, hx4, map_one]

theorem card_of_isSLThreePiAt_two_pow {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (hX : Sec4.IsSLThreePiAt X (2 ^ m)) :
    (2 ^ m % 3 = 1 ∧ Nat.card X = (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ∨
      (2 ^ m % 3 = 2 ∧ Nat.card X = (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) := by
  obtain ⟨F, _, _, ⟨hF, hq, ⟨e⟩⟩ | ⟨hF, hq, ⟨e⟩⟩⟩ := hX
  · have : Fintype F := Fintype.ofFinite F
    left
    refine ⟨hq, ?_⟩
    rw [Nat.card_congr (e.trans (Sec4.slPiTrueEquiv (2 ^ m) F)).toEquiv,
      KFacts.card_SL_three, ← Nat.card_eq_fintype_card, hF]
  · right
    refine ⟨hq, ?_⟩
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m F :=
      ⟨Nat.prime_two, hm, by rw [hF, ← pow_mul, mul_comm]⟩
    rw [Nat.card_congr (e.trans (Sec4.slPiFalseEquiv 2 m F)).toEquiv,
      KFacts.card_unitarySU_three hU]

end CFSG.RankThree.PartTwo.Sec21.Item2130Res5Proof
