module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofPerm
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Insp2Proof

open Matrix
open CFSG.RankThree.PartTwo.Sec4.Res417Frame (permGL det_permGL)

variable {K : Type} [Field K]

@[expose] def mkSL (M : Matrix (Fin 3) (Fin 3) K) (h : M.det = 1) :
    Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨M, h⟩

theorem coe_mkSL (M : Matrix (Fin 3) (Fin 3) K) (h : M.det = 1) :
    ((mkSL M h : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = M :=
  rfl

theorem ext_of_coe {a b : Matrix.SpecialLinearGroup (Fin 3) K}
    (h : (a : Matrix (Fin 3) (Fin 3) K) = b) : a = b :=
  Matrix.SpecialLinearGroup.ext a b fun i j => congrFun (congrFun h i) j

theorem isDiag_mul {A B : Matrix (Fin 3) (Fin 3) K} (hA : A.IsDiag) (hB : B.IsDiag) :
    (A * B).IsDiag := by
  rw [← hA.diagonal_diag, ← hB.diagonal_diag, diagonal_mul_diagonal]
  exact isDiag_diagonal _

theorem isDiag_inv {M : SpecialLinearGroup (Fin 3) K}
    (h : (M : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    ((M⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
  rw [Matrix.SpecialLinearGroup.coe_inv, ← h.diagonal_diag, adjugate_diagonal]
  exact isDiag_diagonal _

theorem mul_comm_of_isDiag {A B : Matrix (Fin 3) (Fin 3) K} (hA : A.IsDiag) (hB : B.IsDiag) :
    A * B = B * A := by
  rw [← hA.diagonal_diag, ← hB.diagonal_diag, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem mul_comm_of_isDiag_SL {a b : SpecialLinearGroup (Fin 3) K}
    (ha : (a : Matrix (Fin 3) (Fin 3) K).IsDiag) (hb : (b : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    a * b = b * a :=
  ext_of_coe (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact mul_comm_of_isDiag ha hb)

theorem pow_three_apply_of_isDiag {A : Matrix (Fin 3) (Fin 3) K} (hA : A.IsDiag) (i : Fin 3) :
    (A ^ 3) i i = A i i ^ 3 := by
  conv_lhs => rw [← hA.diagonal_diag]
  rw [diagonal_pow, diagonal_apply_eq, Pi.pow_apply, diag_apply]

theorem det_of_isDiag {A : Matrix (Fin 3) (Fin 3) K} (hA : A.IsDiag) :
    A.det = A 0 0 * A 1 1 * A 2 2 := by
  conv_lhs => rw [← hA.diagonal_diag]
  rw [det_diagonal, Fin.prod_univ_three]
  rfl

@[expose] def diagSL (K : Type) [Field K] : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {M | (M : Matrix (Fin 3) (Fin 3) K).IsDiag}
  mul_mem' := fun {a b} ha hb => by
    show ((a * b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact isDiag_mul ha hb
  one_mem' := by
    show ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact isDiag_one
  inv_mem' := fun h => isDiag_inv h

@[expose] def tZero (K : Type) [Field K] : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {M | (M : Matrix (Fin 3) (Fin 3) K).IsDiag ∧ M ^ 3 = 1}
  mul_mem' := fun {a b} ha hb => by
    refine ⟨?_, ?_⟩
    · show ((a * b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag
      rw [Matrix.SpecialLinearGroup.coe_mul]
      exact isDiag_mul ha.1 hb.1
    · have hc : Commute a b := mul_comm_of_isDiag_SL ha.1 hb.1
      rw [hc.mul_pow, ha.2, hb.2, one_mul]
  one_mem' := by
    refine ⟨?_, one_pow 3⟩
    show ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact isDiag_one
  inv_mem' := fun {a} ha => ⟨isDiag_inv ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem apply_self_pow_three_of_mem_tZero {M : SpecialLinearGroup (Fin 3) K}
    (hM : M ∈ tZero K) (i : Fin 3) : (M : Matrix (Fin 3) (Fin 3) K) i i ^ 3 = 1 := by
  have h := congrArg (fun N : SpecialLinearGroup (Fin 3) K => (N : Matrix (Fin 3) (Fin 3) K) i i)
    hM.2
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at h
  rw [pow_three_apply_of_isDiag hM.1, one_apply_eq] at h
  exact h

theorem card_tZero_le [Finite K] : Nat.card (tZero K) ≤ 9 := by
  have hne : ∀ (M : tZero K) (i : Fin 3),
      ((M : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
    intro M i h0
    have h := apply_self_pow_three_of_mem_tZero M.2 i
    rw [h0] at h
    norm_num at h
  have hroot : ∀ (M : tZero K) (i : Fin 3), Units.mk0 _ (hne M i) ∈ rootsOfUnity 3 K := by
    intro M i
    rw [mem_rootsOfUnity]
    exact Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      exact apply_self_pow_three_of_mem_tZero M.2 i)
  let f : tZero K → rootsOfUnity 3 K × rootsOfUnity 3 K := fun M =>
    (⟨_, hroot M 0⟩, ⟨_, hroot M 1⟩)
  have hf : Function.Injective f := by
    intro M N h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
    have h0 := congrArg Units.val h.1
    have h1 := congrArg Units.val h.2
    simp only [Units.val_mk0] at h0 h1
    have hdM := det_of_isDiag M.2.1
    have hdN := det_of_isDiag N.2.1
    rw [(M : SpecialLinearGroup (Fin 3) K).2] at hdM
    rw [(N : SpecialLinearGroup (Fin 3) K).2] at hdN
    have h2 : ((M : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 =
        ((N : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 := by
      rw [h0, h1] at hdM
      have hmul := mul_ne_zero (hne N 0) (hne N 1)
      exact mul_left_cancel₀ hmul (hdM.symm.trans hdN)
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    by_cases hij : i = j
    · rw [← hij]
      fin_cases i
      exacts [h0, h1, h2]
    · rw [M.2.1 hij, N.2.1 hij]
  calc Nat.card (tZero K) ≤ Nat.card (rootsOfUnity 3 K × rootsOfUnity 3 K) :=
        Nat.card_le_card_of_injective f hf
    _ = Nat.card (rootsOfUnity 3 K) * Nat.card (rootsOfUnity 3 K) := Nat.card_prod _ _
    _ ≤ 3 * 3 := Nat.mul_le_mul (card_rootsOfUnity K 3) (card_rootsOfUnity K 3)

theorem eq_scalar_of_mem_tZero {M : SpecialLinearGroup (Fin 3) K} (hM : M ∈ tZero K)
    {i j : Fin 3} (hij : i ≠ j)
    (h : (M : Matrix (Fin 3) (Fin 3) K) i i = (M : Matrix (Fin 3) (Fin 3) K) j j) :
    (M : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) ((M : Matrix (Fin 3) (Fin 3) K) 0 0) := by
  have hd := det_of_isDiag hM.1
  rw [M.2] at hd
  have h0 := apply_self_pow_three_of_mem_tZero hM 0
  have h1 := apply_self_pow_three_of_mem_tZero hM 1
  have h2 := apply_self_pow_three_of_mem_tZero hM 2
  have hcases : (M : Matrix (Fin 3) (Fin 3) K) 0 0 = (M : Matrix (Fin 3) (Fin 3) K) 1 1 ∨
      (M : Matrix (Fin 3) (Fin 3) K) 0 0 = (M : Matrix (Fin 3) (Fin 3) K) 2 2 ∨
      (M : Matrix (Fin 3) (Fin 3) K) 1 1 = (M : Matrix (Fin 3) (Fin 3) K) 2 2 := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact Or.inl h
      | exact Or.inl h.symm
      | exact Or.inr (Or.inl h)
      | exact Or.inr (Or.inl h.symm)
      | exact Or.inr (Or.inr h)
      | exact Or.inr (Or.inr h.symm)
  have key : (M : Matrix (Fin 3) (Fin 3) K) 1 1 = (M : Matrix (Fin 3) (Fin 3) K) 0 0 ∧
      (M : Matrix (Fin 3) (Fin 3) K) 2 2 = (M : Matrix (Fin 3) (Fin 3) K) 0 0 := by
    generalize (M : Matrix (Fin 3) (Fin 3) K) 0 0 = a at hcases h0 hd ⊢
    generalize (M : Matrix (Fin 3) (Fin 3) K) 1 1 = b at hcases h1 hd ⊢
    generalize (M : Matrix (Fin 3) (Fin 3) K) 2 2 = c at hcases h2 hd ⊢
    rcases hcases with h | h | h
    · exact ⟨h.symm, by linear_combination (-c) * h0 + (-a) * hd + (a ^ 2 * c) * h⟩
    · exact ⟨by linear_combination (-b) * h0 + (-a) * hd + (a ^ 2 * b) * h, h.symm⟩
    · have hba : b = a := by linear_combination a * h1 + b * hd + (-(a * b ^ 2)) * h
      exact ⟨hba, h.symm.trans hba⟩
  ext r s
  by_cases hrs : r = s
  · rw [← hrs, scalar_apply, diagonal_apply_eq]
    fin_cases r
    · rfl
    · exact key.1
    · exact key.2
  · rw [hM.1 hrs, scalar_apply, diagonal_apply_ne _ hrs]

section Omega

variable {ω : K} (hω : IsPrimitiveRoot ω 3)
include hω

theorem injective_omega : Function.Injective (![1, ω, ω ^ 2] : Fin 3 → K) := by
  have h3 := hω.pow_eq_one
  have h1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have h0 : ω ≠ 0 := by
    rintro rfl
    norm_num at h3
  have h2 : ω ^ 2 ≠ 1 := by
    intro h
    apply h1
    calc ω = ω * ω ^ 2 := by rw [h, mul_one]
      _ = ω ^ 3 := by ring
      _ = 1 := h3
  have h12 : ω ≠ ω ^ 2 := by
    intro h
    apply h1
    have : ω * ω = ω * 1 := by rw [← sq, ← h, mul_one]
    exact mul_left_cancel₀ h0 this
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd hij.symm h1
    | exact absurd hij h1
    | exact absurd hij.symm h2
    | exact absurd hij h2
    | exact absurd hij h12
    | exact absurd hij.symm h12

theorem det_regMat : (diagonal ![1, ω, ω ^ 2] : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [det_diagonal, Fin.prod_univ_three]
  change (1 : K) * ω * ω ^ 2 = 1
  linear_combination hω.pow_eq_one

theorem det_scalMat : (diagonal ![ω, ω, ω] : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [det_diagonal, Fin.prod_univ_three]
  change ω * ω * ω = 1
  linear_combination hω.pow_eq_one

@[expose] def regSL : SpecialLinearGroup (Fin 3) K :=
  mkSL (diagonal ![1, ω, ω ^ 2]) (det_regMat hω)

@[expose] def scalSL : SpecialLinearGroup (Fin 3) K :=
  mkSL (diagonal ![ω, ω, ω]) (det_scalMat hω)

theorem coe_regSL :
    ((regSL hω : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![1, ω, ω ^ 2] :=
  rfl

theorem coe_scalSL :
    ((scalSL hω : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![ω, ω, ω] :=
  rfl

theorem regSL_mem_tZero : regSL hω ∈ tZero K := by
  have h3 := hω.pow_eq_one
  have h6 : (ω ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, h3, one_pow]
  refine ⟨isDiag_diagonal _, ext_of_coe ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_regSL, diagonal_pow,
    Matrix.SpecialLinearGroup.coe_one, ← diagonal_one]
  congr 1
  funext i
  fin_cases i
  · change (1 : K) ^ 3 = 1
    exact one_pow 3
  · exact h3
  · exact h6

theorem scalSL_mem_tZero : scalSL hω ∈ tZero K := by
  have h3 := hω.pow_eq_one
  refine ⟨isDiag_diagonal _, ext_of_coe ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_scalSL, diagonal_pow,
    Matrix.SpecialLinearGroup.coe_one, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> exact h3

theorem isDiag_of_commute_regSL {M : Matrix (Fin 3) (Fin 3) K}
    (h : M * diagonal ![1, ω, ω ^ 2] = diagonal ![1, ω, ω ^ 2] * M) : M.IsDiag :=
  CFSG.RankThree.PartTwo.Sec4.Res417Frame.isDiag_of_commute_diagonal (injective_omega hω) h

end Omega

@[expose] noncomputable def permSL (h2 : (2 : K) = 0) :
    Equiv.Perm (Fin 3) →* SpecialLinearGroup (Fin 3) K where
  toFun σ := mkSL ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (det_permGL h2 σ)
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_one]
    change ((permGL 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = _
    rw [map_one, Units.val_one]
  map_mul' σ τ := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change ((permGL (σ * τ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      (((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((permGL τ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) i j
    rw [map_mul, Units.val_mul]

theorem coe_permSL (h2 : (2 : K) = 0) (σ : Equiv.Perm (Fin 3)) :
    ((permSL h2 σ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  rfl

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation) in
theorem mem_range_scalar_of_slConjugation_eq_one {g : GL (Fin 3) K}
    (h : slConjugation 3 K g = 1) :
    (g : Matrix (Fin 3) (Fin 3) K) ∈ Set.range (scalar (Fin 3)) := by
  rw [mem_range_scalar_iff_commute_transvectionStruct]
  intro t
  have h1 := congrArg (fun φ : MulAut (SpecialLinearGroup (Fin 3) K) =>
    ((φ t.toSpecialLinearGroup : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
  simp only [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation,
    MulAut.one_apply, TransvectionStruct.toSpecialLinearGroup_coe] at h1
  have hg : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  show t.toMatrix * (g : Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) K) * t.toMatrix
  calc t.toMatrix * (g : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K) * t.toMatrix *
        ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) := by
        rw [h1]
    _ = (g : Matrix (Fin 3) (Fin 3) K) * t.toMatrix := by
        rw [Matrix.mul_assoc, hg, Matrix.mul_one]

theorem block_of_commute_diagonal {d : Fin 3 → K} {k : Fin 3} (hk : ∀ l, l ≠ k → d l ≠ d k)
    {M : Matrix (Fin 3) (Fin 3) K} (h : M * diagonal d = diagonal d * M) :
    ∀ l, l ≠ k → M k l = 0 ∧ M l k = 0 := by
  intro l hl
  have h1 := congrFun (congrFun h k) l
  have h2 := congrFun (congrFun h l) k
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1 h2
  have h1' : M k l * (d l - d k) = 0 := by linear_combination h1
  have h2' : M l k * (d k - d l) = 0 := by linear_combination h2
  exact ⟨(mul_eq_zero.mp h1').resolve_right (sub_ne_zero.mpr (hk l hl)),
    (mul_eq_zero.mp h2').resolve_right (sub_ne_zero.mpr (hk l hl).symm)⟩

theorem mul_apply_kk {k : Fin 3} {M N : Matrix (Fin 3) (Fin 3) K}
    (hM : ∀ l, l ≠ k → M k l = 0 ∧ M l k = 0) : (M * N) k k = M k k * N k k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · intro l _ hl
    rw [(hM l hl).1, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem mul_apply_kl {k l : Fin 3} (hl : l ≠ k) {M N : Matrix (Fin 3) (Fin 3) K}
    (hM : ∀ l, l ≠ k → M k l = 0 ∧ M l k = 0) (hN : ∀ l, l ≠ k → N k l = 0 ∧ N l k = 0) :
    (M * N) k l = 0 ∧ (M * N) l k = 0 := by
  constructor
  · rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · rw [(hN l hl).1, mul_zero]
    · intro r _ hr
      rw [(hM r hr).1, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ k) h
  · rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · rw [(hM l hl).2, zero_mul]
    · intro r _ hr
      rw [(hN r hr).2, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h

@[expose] def rootSL (k : Fin 3) : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {M | (M : Matrix (Fin 3) (Fin 3) K) k k = 1 ∧
    ∀ l, l ≠ k → (M : Matrix (Fin 3) (Fin 3) K) k l = 0 ∧ (M : Matrix (Fin 3) (Fin 3) K) l k = 0}
  mul_mem' := fun {a b} ha hb => by
    refine ⟨?_, fun l hl => ?_⟩
    · show ((a * b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k k = 1
      rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply_kk ha.2, ha.1, hb.1, one_mul]
    · show ((a * b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k l = 0 ∧
        ((a * b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) l k = 0
      rw [Matrix.SpecialLinearGroup.coe_mul]
      exact mul_apply_kl hl ha.2 hb.2
  one_mem' := by
    refine ⟨?_, fun l hl => ?_⟩
    · show ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k k = 1
      rw [Matrix.SpecialLinearGroup.coe_one, one_apply_eq]
    · show ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k l = 0 ∧
        ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) l k = 0
      rw [Matrix.SpecialLinearGroup.coe_one, one_apply_ne (Ne.symm hl), one_apply_ne hl]
      exact ⟨rfl, rfl⟩
  inv_mem' := fun {a} ha => by
    have h1 : ((a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (a : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : (a : Matrix (Fin 3) (Fin 3) K) *
        ((a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hcol : ∀ l, ((a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) l k =
        (1 : Matrix (Fin 3) (Fin 3) K) l k := by
      intro l
      have h := congrFun (congrFun h1 l) k
      rw [Matrix.mul_apply, Finset.sum_eq_single k (fun r _ hr => by rw [(ha.2 r hr).2, mul_zero])
        (fun h => absurd (Finset.mem_univ k) h), ha.1, mul_one] at h
      exact h
    have hrow : ∀ l, ((a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k l =
        (1 : Matrix (Fin 3) (Fin 3) K) k l := by
      intro l
      have h := congrFun (congrFun h2 k) l
      rw [Matrix.mul_apply, Finset.sum_eq_single k (fun r _ hr => by rw [(ha.2 r hr).1, zero_mul])
        (fun h => absurd (Finset.mem_univ k) h), ha.1, one_mul] at h
      exact h
    refine ⟨by rw [hcol, one_apply_eq], fun l hl => ⟨?_, ?_⟩⟩
    · rw [hrow, one_apply_ne (Ne.symm hl)]
    · rw [hcol, one_apply_ne hl]

theorem mem_rootSL {k : Fin 3} {M : SpecialLinearGroup (Fin 3) K} :
    M ∈ rootSL k ↔ (M : Matrix (Fin 3) (Fin 3) K) k k = 1 ∧
      ∀ l, l ≠ k → (M : Matrix (Fin 3) (Fin 3) K) k l = 0 ∧
        (M : Matrix (Fin 3) (Fin 3) K) l k = 0 :=
  Iff.rfl

theorem det_eq_det_submatrix {k : Fin 3} {M : Matrix (Fin 3) (Fin 3) K} (hkk : M k k = 1)
    (hM : ∀ l, l ≠ k → M k l = 0 ∧ M l k = 0) :
    M.det = (M.submatrix k.succAbove k.succAbove).det := by
  rw [det_succ_row M k, Finset.sum_eq_single k]
  · rw [hkk, mul_one, Even.neg_one_pow ⟨(k : ℕ), rfl⟩, one_mul]
  · intro l _ hl
    rw [(hM l hl).1, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem card_rootSL_le [Finite K] (k : Fin 3) :
    Nat.card (rootSL (K := K) k) ≤ Nat.card (SpecialLinearGroup (Fin 2) K) := by
  let f : rootSL (K := K) k → SpecialLinearGroup (Fin 2) K := fun M =>
    ⟨((M : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).submatrix k.succAbove
      k.succAbove, by
      rw [← det_eq_det_submatrix (mem_rootSL.mp M.2).1 (mem_rootSL.mp M.2).2]
      exact (M : SpecialLinearGroup (Fin 3) K).2⟩
  have hf : Function.Injective f := by
    intro M N h
    have h' := congrArg (fun A : SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K)) h
    simp only [f] at h'
    have hM := mem_rootSL.mp M.2
    have hN := mem_rootSL.mp N.2
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    by_cases hi : i = k
    · by_cases hj : j = k
      · rw [hi, hj, hM.1, hN.1]
      · rw [hi, (hM.2 j hj).1, (hN.2 j hj).1]
    · by_cases hj : j = k
      · rw [hj, (hM.2 i hi).2, (hN.2 i hi).2]
      · obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hi
        obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        exact congrFun (congrFun h' i') j'
  exact Nat.card_le_card_of_injective f hf

theorem transvection_mem_rootSL {k i j : Fin 3} (hi : i ≠ k) (hj : j ≠ k) (hij : i ≠ j) (c : K) :
    Matrix.SpecialLinearGroup.transvection hij c ∈ rootSL k := by
  rw [mem_rootSL, Matrix.SpecialLinearGroup.transvection_coe]
  refine ⟨?_, fun l hl => ⟨?_, ?_⟩⟩
  · rw [Matrix.add_apply, one_apply_eq, single_apply_of_row_ne hi, add_zero]
  · rw [Matrix.add_apply, one_apply_ne (Ne.symm hl), single_apply_of_row_ne hi, add_zero]
  · rw [Matrix.add_apply, one_apply_ne hl, single_apply_of_col_ne _ _ hj, add_zero]

theorem transvection_eq_commutator {i j l : Fin 3} (hij : i ≠ j) (hil : i ≠ l) (hlj : l ≠ j)
    (c : K) :
    Matrix.SpecialLinearGroup.transvection hij c =
      Matrix.SpecialLinearGroup.transvection hil c *
        Matrix.SpecialLinearGroup.transvection hlj 1 *
          Matrix.SpecialLinearGroup.transvection hil (-c) *
            Matrix.SpecialLinearGroup.transvection hlj (-1) := by
  apply ext_of_coe
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp at hij hil hlj <;>
    ext r s <;> fin_cases r <;> fin_cases s <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem toSpecialLinearGroup_eq_transvection (t : TransvectionStruct (Fin 3) K) :
    t.toSpecialLinearGroup = Matrix.SpecialLinearGroup.transvection t.hij t.c := by
  apply ext_of_coe
  rw [TransvectionStruct.toSpecialLinearGroup_coe, Matrix.SpecialLinearGroup.transvection_coe]
  rfl

theorem transvection_mem_sup {k₁ k₂ : Fin 3} (hk : k₁ ≠ k₂) (t : TransvectionStruct (Fin 3) K) :
    t.toSpecialLinearGroup ∈ rootSL (K := K) k₁ ⊔ rootSL k₂ := by
  rw [toSpecialLinearGroup_eq_transvection]
  obtain ⟨i, j, hij, c⟩ := t
  by_cases h1 : i ≠ k₁ ∧ j ≠ k₁
  · exact Subgroup.mem_sup_left (transvection_mem_rootSL h1.1 h1.2 hij c)
  by_cases h2 : i ≠ k₂ ∧ j ≠ k₂
  · exact Subgroup.mem_sup_right (transvection_mem_rootSL h2.1 h2.2 hij c)
  obtain ⟨l, hli, hlj⟩ : ∃ l : Fin 3, l ≠ i ∧ l ≠ j := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact ⟨0, by decide, by decide⟩
      | exact ⟨1, by decide, by decide⟩
      | exact ⟨2, by decide, by decide⟩
  have hij' : (i = k₁ ∧ j = k₂) ∨ (i = k₂ ∧ j = k₁) := by
    push Not at h1 h2
    by_cases hi1 : i = k₁
    · have hj2 : j = k₂ := h2 (fun h => hk (hi1.symm.trans h))
      exact Or.inl ⟨hi1, hj2⟩
    · have hj1 : j = k₁ := h1 hi1
      have hi2 : i = k₂ := by
        by_contra hi2
        exact hk (hj1.symm.trans (h2 hi2))
      exact Or.inr ⟨hi2, hj1⟩
  rw [transvection_eq_commutator hij (Ne.symm hli) hlj c]
  have hA : Matrix.SpecialLinearGroup.transvection (Ne.symm hli) c ∈ rootSL (K := K) j :=
    transvection_mem_rootSL hij hlj (Ne.symm hli) c
  have hA' : Matrix.SpecialLinearGroup.transvection (Ne.symm hli) (-c) ∈ rootSL (K := K) j :=
    transvection_mem_rootSL hij hlj (Ne.symm hli) (-c)
  have hB : Matrix.SpecialLinearGroup.transvection hlj 1 ∈ rootSL (K := K) i :=
    transvection_mem_rootSL hli (Ne.symm hij) hlj 1
  have hB' : Matrix.SpecialLinearGroup.transvection hlj (-1) ∈ rootSL (K := K) i :=
    transvection_mem_rootSL hli (Ne.symm hij) hlj (-1)
  rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_right hA) (Subgroup.mem_sup_left hB)) (Subgroup.mem_sup_right hA'))
      (Subgroup.mem_sup_left hB')
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left hA) (Subgroup.mem_sup_right hB)) (Subgroup.mem_sup_left hA'))
      (Subgroup.mem_sup_right hB')

theorem diag_mem_rootSL {k : Fin 3} {D : Fin 3 → K} (hD : (diagonal D).det = 1) (hk : D k = 1) :
    mkSL (diagonal D) hD ∈ rootSL k := by
  refine ⟨?_, fun l hl => ⟨?_, ?_⟩⟩
  · show (diagonal D) k k = 1
    rw [diagonal_apply_eq, hk]
  · show (diagonal D) k l = 0
    rw [diagonal_apply_ne _ (Ne.symm hl)]
  · show (diagonal D) l k = 0
    rw [diagonal_apply_ne _ hl]

theorem diag_mem_sup {k₁ k₂ : Fin 3} (hk : k₁ ≠ k₂) {D : Fin 3 → K}
    (hD : (diagonal D).det = 1) : mkSL (diagonal D) hD ∈ rootSL (K := K) k₁ ⊔ rootSL k₂ := by
  have hD' : D 0 * D 1 * D 2 = 1 := by
    rw [det_diagonal, Fin.prod_univ_three] at hD
    exact hD
  have h0 : D 0 ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hD')
  have h1 : D 1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul_eq_one hD')
  have h2 : D 2 ≠ 0 := right_ne_zero_of_mul_eq_one hD'
  have key : ∀ E₁ E₂ : Fin 3 → K, (∀ i, E₁ i * E₂ i = D i) → E₁ k₁ = 1 → E₂ k₂ = 1 →
      ∀ (hd₁ : (diagonal E₁).det = 1) (hd₂ : (diagonal E₂).det = 1),
      mkSL (diagonal D) hD ∈ rootSL (K := K) k₁ ⊔ rootSL k₂ := by
    intro E₁ E₂ hE hE₁ hE₂ hd₁ hd₂
    have hprod : mkSL (diagonal D) hD = mkSL (diagonal E₁) hd₁ * mkSL (diagonal E₂) hd₂ := by
      apply ext_of_coe
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_mkSL, coe_mkSL, coe_mkSL, diagonal_mul_diagonal]
      congr 1
      funext i
      exact (hE i).symm
    rw [hprod]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (diag_mem_rootSL hd₁ hE₁))
      (Subgroup.mem_sup_right (diag_mem_rootSL hd₂ hE₂))
  have hdet : ∀ a b c : K, (diagonal ![a, b, c]).det = a * b * c := fun a b c => by
    rw [det_diagonal, Fin.prod_univ_three]
    rfl
  fin_cases k₁ <;> fin_cases k₂
  · exact absurd rfl hk
  ·
    refine key ![1, D 1, (D 1)⁻¹] ![D 0, 1, D 1 * D 2] (fun i => ?_) rfl rfl
      (by rw [hdet]; field_simp) (by rw [hdet]; linear_combination hD')
    fin_cases i
    · exact one_mul _
    · exact mul_one _
    · change (D 1)⁻¹ * (D 1 * D 2) = D 2
      field_simp
  ·
    refine key ![1, (D 2)⁻¹, D 2] ![D 0, D 1 * D 2, 1] (fun i => ?_) rfl rfl
      (by rw [hdet]; field_simp) (by rw [hdet]; linear_combination hD')
    fin_cases i
    · exact one_mul _
    · change (D 2)⁻¹ * (D 1 * D 2) = D 1
      field_simp
    · exact mul_one _
  ·
    refine key ![D 0, 1, (D 0)⁻¹] ![1, D 1, D 0 * D 2] (fun i => ?_) rfl rfl
      (by rw [hdet]; field_simp) (by rw [hdet]; linear_combination hD')
    fin_cases i
    · exact mul_one _
    · exact one_mul _
    · change (D 0)⁻¹ * (D 0 * D 2) = D 2
      field_simp
  · exact absurd rfl hk
  ·
    refine key ![(D 2)⁻¹, 1, D 2] ![D 0 * D 2, D 1, 1] (fun i => ?_) rfl rfl
      (by rw [hdet]; field_simp) (by rw [hdet]; linear_combination hD')
    fin_cases i
    · change (D 2)⁻¹ * (D 0 * D 2) = D 0
      field_simp
    · exact one_mul _
    · exact mul_one _
  ·
    refine key ![D 0, (D 0)⁻¹, 1] ![1, D 0 * D 1, D 2] (fun i => ?_) rfl rfl
      (by rw [hdet]; field_simp) (by rw [hdet]; linear_combination hD')
    fin_cases i
    · exact mul_one _
    · change (D 0)⁻¹ * (D 0 * D 1) = D 1
      field_simp
    · exact one_mul _
  ·
    refine key ![(D 1)⁻¹, D 1, 1] ![D 0 * D 1, 1, D 2] (fun i => ?_) rfl rfl
      (by rw [hdet]; field_simp) (by rw [hdet]; linear_combination hD')
    fin_cases i
    · change (D 1)⁻¹ * (D 0 * D 1) = D 0
      field_simp
    · exact mul_one _
    · exact one_mul _
  · exact absurd rfl hk

theorem sup_rootSL_eq_top {k₁ k₂ : Fin 3} (hk : k₁ ≠ k₂) :
    rootSL (K := K) k₁ ⊔ rootSL k₂ = ⊤ := by
  set H := rootSL (K := K) k₁ ⊔ rootSL k₂ with hH
  have hlist : ∀ L : List (TransvectionStruct (Fin 3) K),
      (L.map TransvectionStruct.toSpecialLinearGroup).prod ∈ H := by
    intro L
    induction L with
    | nil => exact H.one_mem
    | cons t L ih =>
      rw [List.map_cons, List.prod_cons]
      exact H.mul_mem (transvection_mem_sup hk t) ih
  rw [eq_top_iff]
  intro M _
  obtain ⟨L, L', D, hD, hM⟩ :=
    Matrix.SpecialLinearGroup.exists_list_transvec_mul_diagonal_mul_list_transvec M
  rw [hM]
  exact H.mul_mem (H.mul_mem (hlist L) (diag_mem_sup hk hD)) (hlist L')

theorem le_rootSL_of_isPerfect {P : Subgroup (SpecialLinearGroup (Fin 3) K)}
    [Group.IsPerfect P] {k : Fin 3}
    (hP : ∀ M ∈ P, ∀ l, l ≠ k → (M : Matrix (Fin 3) (Fin 3) K) k l = 0 ∧
      (M : Matrix (Fin 3) (Fin 3) K) l k = 0) : P ≤ rootSL k := by
  let f : P →* K :=
    { toFun := fun M => ((M : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k k
      map_one' := by
        show ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k k = 1
        rw [Matrix.SpecialLinearGroup.coe_one, one_apply_eq]
      map_mul' := fun M N => by
        show ((M * N : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k k = _
        rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply_kk (hP _ M.2)] }
  have hker : commutator P ≤ f.toHomUnits.ker := Abelianization.commutator_subset_ker _
  rw [Group.IsPerfect.commutator_eq_top] at hker
  intro M hM
  refine ⟨?_, hP M hM⟩
  have h := hker (Subgroup.mem_top ⟨M, hM⟩)
  rw [MonoidHom.mem_ker] at h
  have h' := congrArg Units.val h
  rw [MonoidHom.coe_toHomUnits, Units.val_one] at h'
  exact h'

theorem subsingleton_of_isPerfect_of_comm {P : Type*} [Group P] [Group.IsPerfect P]
    (h : ∀ a b : P, a * b = b * a) : Subsingleton P := by
  have hc : commutator P = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro b _
    exact h b a
  rw [Group.IsPerfect.commutator_eq_top] at hc
  constructor
  intro a b
  have ha : a ∈ (⊤ : Subgroup P) := Subgroup.mem_top a
  have hb : b ∈ (⊤ : Subgroup P) := Subgroup.mem_top b
  rw [hc, Subgroup.mem_bot] at ha hb
  rw [ha, hb]

end CFSG.RankThree.PartTwo.Sec21.Item228Insp2Proof
