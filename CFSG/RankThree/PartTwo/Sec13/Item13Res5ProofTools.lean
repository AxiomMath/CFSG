module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Matrix
open CFSG.Assembly.RankThreeEven (projImage projSL projSU projSp)

namespace Res5Proof

section Proj

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

theorem three_dvd_card_projImage_of_mem {H : Subgroup (GL ι K)} {g : GL ι K} (hg : g ∈ H)
    (hg3 : g ^ 3 = 1) (hgc : g ∉ Subgroup.center (GL ι K)) : 3 ∣ Nat.card (projImage H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let x : projImage H := ⟨ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩
  have hx1 : x ≠ 1 := fun hx => hgc (ProjGenLinGroup.mk_eq_one.mp (congrArg Subtype.val hx))
  have hx3 : x ^ 3 = 1 := Subtype.ext (by
    change ProjGenLinGroup.mk g ^ 3 = 1
    rw [← map_pow, hg3, map_one])
  have h := orderOf_dvd_natCard x
  rwa [orderOf_eq_prime hx3 hx1] at h

@[expose] def permGL (σ : Equiv.Perm ι) : GL ι K :=
  ⟨σ.permMatrix K, σ⁻¹.permMatrix K,
    by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one],
    by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩

theorem coe_permGL (σ : Equiv.Perm ι) :
    ((permGL σ : GL ι K) : Matrix ι ι K) = σ.permMatrix K :=
  rfl

theorem permMatrix_pow (σ : Equiv.Perm ι) (k : ℕ) :
    (σ.permMatrix K) ^ k = (σ ^ k).permMatrix K := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', ih, pow_succ, Matrix.permMatrix_mul]

theorem permGL_pow_three {σ : Equiv.Perm ι} (hσ : σ ^ 3 = 1) :
    (permGL σ : GL ι K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_permGL, permMatrix_pow, hσ, Matrix.permMatrix_one,
    Units.val_one]

theorem permGL_not_mem_center {σ : Equiv.Perm ι} (hσ : σ ≠ 1) :
    (permGL σ : GL ι K) ∉ Subgroup.center (GL ι K) := by
  rw [GeneralLinearGroup.center_eq_range_scalar]
  rintro ⟨c, hc⟩
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra h
    push Not at h
    exact hσ (Equiv.ext h)
  have h := congrArg (fun g : GL ι K => (g : Matrix ι ι K) i (σ i)) hc
  simp [coe_permGL, PEquiv.toMatrix_apply, GeneralLinearGroup.coe_scalar, hi.symm] at h

theorem det_permGL (σ : Equiv.Perm ι) :
    ((permGL σ : GL ι K) : Matrix ι ι K).det = Equiv.Perm.sign σ := by
  rw [coe_permGL, Matrix.det_permutation]

omit [Fintype ι] in
theorem map_permMatrix_pow {q : ℕ} (hq : q ≠ 0) (σ : Equiv.Perm ι) :
    (σ.permMatrix K).map (· ^ q) = σ.permMatrix K := by
  ext i j
  simp only [Matrix.map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp [zero_pow hq]

theorem unitary_permGL {q : ℕ} (hq : q ≠ 0) (σ : Equiv.Perm ι) :
    (((permGL σ : GL ι K) : Matrix ι ι K).map (· ^ q))ᵀ * ((permGL σ : GL ι K) : Matrix ι ι K) =
      1 := by
  rw [coe_permGL, map_permMatrix_pow hq, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul,
    mul_inv_cancel, Matrix.permMatrix_one]

end Proj

section Small

variable {K : Type*} [Field K]

@[expose] def slTwoThree (K : Type*) [Field K] : GL (Fin 2) K :=
  ⟨!![0, -1; 1, -1], !![-1, 1; -1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_slTwoThree : ((slTwoThree K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![0, -1; 1, -1] :=
  rfl

theorem slTwoThree_pow_three : slTwoThree K ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_slTwoThree, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_slTwoThree :
    ((slTwoThree K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  rw [coe_slTwoThree, Matrix.det_fin_two_of]
  ring

theorem slTwoThree_not_mem_center : slTwoThree K ∉ Subgroup.center (GL (Fin 2) K) := by
  rw [GeneralLinearGroup.center_eq_range_scalar]
  rintro ⟨c, hc⟩
  have h := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) hc
  simp [coe_slTwoThree, GeneralLinearGroup.coe_scalar] at h

@[expose] def spFourThree (K : Type*) [Field K] : GL (Fin 2 ⊕ Fin 2) K :=
  ⟨Matrix.fromBlocks !![0, -1; 1, -1] 0 0 !![-1, -1; 1, 0],
    Matrix.fromBlocks !![-1, 1; -1, 0] 0 0 !![0, 1; -1, -1],
    by
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      rw [← Matrix.fromBlocks_one]
      congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two],
    by
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      rw [← Matrix.fromBlocks_one]
      congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_spFourThree : ((spFourThree K : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.fromBlocks !![0, -1; 1, -1] 0 0 !![-1, -1; 1, 0] :=
  rfl

theorem spFourThree_pow_three : spFourThree K ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_spFourThree, Units.val_one, pow_succ, pow_succ, pow_one,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [← Matrix.fromBlocks_one]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem spFourThree_symp :
    ((spFourThree K : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      Matrix.fromBlocks 0 1 (-1) 0 *
      ((spFourThree K : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [coe_spFourThree, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.transpose_zero,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem spFourThree_not_mem_center :
    spFourThree K ∉ Subgroup.center (GL (Fin 2 ⊕ Fin 2) K) := by
  rw [GeneralLinearGroup.center_eq_range_scalar]
  rintro ⟨c, hc⟩
  have h := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inl 1)) hc
  simp [coe_spFourThree, GeneralLinearGroup.coe_scalar] at h

end Small

section Card

variable {X : Type*} [Group X]

theorem three_dvd_card_of_mulEquiv {Y : Type*} [Group Y] (e : X ≃* Y) (h : 3 ∣ Nat.card Y) :
    3 ∣ Nat.card X := by
  rwa [Nat.card_congr e.toEquiv]

theorem three_dvd_card_of_mem {G : Type*} [Group G] {H : Subgroup G} {g : G} (hg : g ∈ H)
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) : 3 ∣ Nat.card H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := orderOf_dvd_natCard (⟨g, hg⟩ : H)
  rwa [orderOf_eq_prime (Subtype.ext (by simpa using hg3)) (fun h => hg1 (congrArg Subtype.val h))]
    at h

theorem three_dvd_card_projSL_two (K : Type*) [Field K] : 3 ∣ Nat.card (projSL 2 K) := by
  refine three_dvd_card_projImage_of_mem ?_ slTwoThree_pow_three slTwoThree_not_mem_center
  rw [MonoidHom.mem_ker]
  ext
  rw [GeneralLinearGroup.val_det_apply, det_slTwoThree, Units.val_one]

theorem three_dvd_card_projSL_of_perm {n : ℕ} (K : Type*) [Field K] {σ : Equiv.Perm (Fin n)}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hσs : Equiv.Perm.sign σ = 1) :
    3 ∣ Nat.card (projSL n K) := by
  refine three_dvd_card_projImage_of_mem ?_ (permGL_pow_three hσ3) (permGL_not_mem_center hσ1)
  rw [MonoidHom.mem_ker]
  ext
  rw [GeneralLinearGroup.val_det_apply, det_permGL, hσs, Units.val_one]
  simp

theorem three_dvd_card_projSU_of_perm {n p f : ℕ} [Fact p.Prime] {σ : Equiv.Perm (Fin n)}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hσs : Equiv.Perm.sign σ = 1) :
    3 ∣ Nat.card (projSU n p f) := by
  refine three_dvd_card_projImage_of_mem (Subgroup.subset_closure ⟨?_, ?_⟩)
    (permGL_pow_three hσ3) (permGL_not_mem_center hσ1)
  · ext
    rw [GeneralLinearGroup.val_det_apply, det_permGL, hσs, Units.val_one]
    simp
  · exact unitary_permGL (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) σ

theorem three_dvd_card_projSp_two (K : Type*) [Field K] : 3 ∣ Nat.card (projSp 2 K) :=
  three_dvd_card_projImage_of_mem (Subgroup.subset_closure spFourThree_symp)
    spFourThree_pow_three spFourThree_not_mem_center

theorem cycle_four :
    (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) ^ 3 = 1 ∧
      (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) ≠ 1 ∧
      Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem cycle_five :
    (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ^ 3 = 1 ∧
      (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ≠ 1 ∧
      Equiv.Perm.sign (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem three_dvd_card_projSL_four (K : Type*) [Field K] : 3 ∣ Nat.card (projSL 4 K) :=
  three_dvd_card_projSL_of_perm K cycle_four.1 cycle_four.2.1 cycle_four.2.2

theorem three_dvd_card_projSL_five (K : Type*) [Field K] : 3 ∣ Nat.card (projSL 5 K) :=
  three_dvd_card_projSL_of_perm K cycle_five.1 cycle_five.2.1 cycle_five.2.2

theorem three_dvd_card_projSU_four (p f : ℕ) [Fact p.Prime] : 3 ∣ Nat.card (projSU 4 p f) :=
  three_dvd_card_projSU_of_perm cycle_four.1 cycle_four.2.1 cycle_four.2.2

theorem three_dvd_card_projSU_five (p f : ℕ) [Fact p.Prime] : 3 ∣ Nat.card (projSU 5 p f) :=
  three_dvd_card_projSU_of_perm cycle_five.1 cycle_five.2.1 cycle_five.2.2

theorem cycThree_ne_one {K : Type} [Field K] : (Sec4.cycThree : GL (Fin 3) K) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp [Sec4.coe_cycThree] at h1

theorem cycThree_pow_three {K : Type} [Field K] : (Sec4.cycThree : GL (Fin 3) K) ^ 3 = 1 := by
  ext i j
  rw [Units.val_pow_eq_pow_val, Sec4.coe_cycThree, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem three_dvd_card_of_isSLThreeEpsAt {X : Type} [Group X] {p e : ℕ} (hp : p.Prime)
    (he : 1 ≤ e) (h : Sec4.IsSLThreeEpsAt X (p ^ e)) : 3 ∣ Nat.card X := by
  obtain ⟨K, _, _, ⟨-, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩⟩ := h
  · refine three_dvd_card_of_mulEquiv φ (three_dvd_card_of_mem ?_ cycThree_pow_three
      cycThree_ne_one)
    exact Sec4.cycThree_mem_slPi (π := true) (p := p) (f := e) (fun h => absurd h (by decide))
  · have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p e K :=
      ⟨hp, he, by rw [hK, ← pow_mul, mul_comm]⟩
    refine three_dvd_card_of_mulEquiv φ (three_dvd_card_of_mem ?_ cycThree_pow_three
      cycThree_ne_one)
    exact Sec4.cycThree_mem_slPi (π := false) (fun _ => hU)

theorem three_dvd_card_of_isExtOf {Y : Type*} [Group Y]
    (h : Sec4.IsExtOf X Y (Multiplicative (ZMod 3))) : 3 ∣ Nat.card X := by
  obtain ⟨N, -, ⟨eN⟩, -⟩ := h
  have h3 : Nat.card N = 3 := by
    rw [Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  rw [← h3]
  exact Subgroup.card_subgroup_dvd_card N

theorem three_dvd_mul_sq_sub_one (q : ℕ) : 3 ∣ q * (q ^ 2 - 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have hq3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases hq3 with h | h | h
  · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _
  all_goals
    refine Dvd.dvd.mul_left ?_ _
    apply Nat.dvd_of_mod_eq_zero
    have hq2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
    omega

theorem three_dvd_ordG2 (q : ℕ) : 3 ∣ CFSG.Open.ordG2 q := by
  unfold CFSG.Open.ordG2
  refine (three_dvd_mul_sq_sub_one q).trans ?_
  have h : q * (q ^ 2 - 1) ∣ q ^ 6 * (q ^ 2 - 1) :=
    mul_dvd_mul (dvd_pow_self q (by norm_num)) dvd_rfl
  refine h.trans ?_
  exact ⟨q ^ 6 - 1, by ring⟩

theorem three_dvd_ordTrialityD4 (q : ℕ) : 3 ∣ CFSG.Open.ordTrialityD4 q := by
  unfold CFSG.Open.ordTrialityD4
  refine (three_dvd_mul_sq_sub_one q).trans ?_
  have h : q * (q ^ 2 - 1) ∣ q ^ 12 * (q ^ 2 - 1) :=
    mul_dvd_mul (dvd_pow_self q (by norm_num)) dvd_rfl
  refine h.trans ?_
  exact ⟨(q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1), by ring⟩

theorem three_dvd_ordTwistedF4 (q : ℕ) : 3 ∣ CFSG.Open.ordTwistedF4 q := by
  unfold CFSG.Open.ordTwistedF4
  refine (three_dvd_mul_sq_sub_one q).trans ?_
  have h4 : q ^ 2 - 1 ∣ q ^ 4 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (q ^ 2) 1 2
    rwa [one_pow, ← pow_mul] at this
  have h : q * (q ^ 2 - 1) ∣ q ^ 12 * (q ^ 4 - 1) :=
    mul_dvd_mul (dvd_pow_self q (by norm_num)) h4
  refine h.trans ?_
  exact ⟨(q ^ 6 + 1) * (q ^ 3 + 1) * (q - 1), by ring⟩

end Card

end Res5Proof

end CFSG.RankThree.PartTwo.Sec13
