module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalPlane
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalSpan
public import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open Matrix CFSG.Open CFSG.LieType.BorelTits CFSG.Theory.Representation
open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
open scoped commutatorElement

@[expose] def spPlaneOrder : Fin 2 ⊕ Fin 2 ≃ Fin 2 ⊕ Fin 2 :=
  Equiv.swap (.inl 1) (.inr 0)

theorem spPlaneOrder_inl_zero : spPlaneOrder (.inl 0) = .inl 0 := by decide
theorem spPlaneOrder_inl_one : spPlaneOrder (.inl 1) = .inr 0 := by decide
theorem spPlaneOrder_inr_zero : spPlaneOrder (.inr 0) = .inl 1 := by decide
theorem spPlaneOrder_inr_one : spPlaneOrder (.inr 1) = .inr 1 := by decide

variable {K : Type} [Field K]

@[expose] def spPlaneGram : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks !![0, 1; -1, 0] 0 0 !![0, 1; -1, 0]

theorem spGram_submatrix_spPlaneOrder :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).submatrix spPlaneOrder
      spPlaneOrder = spPlaneGram := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [spPlaneGram, spPlaneOrder_inl_zero, spPlaneOrder_inl_one, spPlaneOrder_inr_zero,
      spPlaneOrder_inr_one, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.submatrix_apply]

theorem reindexGL_spPlaneOrder_mem_statedSp_iff (g : GL (Fin 2 ⊕ Fin 2) K) :
    spPlaneOrder.reindexGL K g ∈ StatedSp 2 K ↔
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * spPlaneGram *
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = spPlaneGram := by
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff, Equiv.coe_reindexGL]
  have hJ : (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      spPlaneGram.submatrix spPlaneOrder.symm spPlaneOrder.symm := by
    rw [show spPlaneGram = (fromBlocks 0 1 (-1) 0).submatrix spPlaneOrder spPlaneOrder from
      spGram_submatrix_spPlaneOrder.symm, Matrix.submatrix_submatrix]
    simp
  have hmul : ∀ A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K,
      A.submatrix spPlaneOrder.symm spPlaneOrder.symm *
          B.submatrix spPlaneOrder.symm spPlaneOrder.symm =
        (A * B).submatrix spPlaneOrder.symm spPlaneOrder.symm :=
    fun A B => Matrix.submatrix_mul_equiv A B (⇑spPlaneOrder.symm) spPlaneOrder.symm
      (⇑spPlaneOrder.symm)
  rw [Matrix.transpose_submatrix, hJ, hmul, hmul]
  constructor
  · intro h
    have := congrArg (fun M => M.submatrix spPlaneOrder spPlaneOrder) h
    simpa [Matrix.submatrix_submatrix] using this
  · intro h
    rw [h]

@[expose] noncomputable def spP0 {a b : K} (h : a ^ 2 + b ^ 2 = -1) :
    Subgroup (GL (Fin 2 ⊕ Fin 2) K) :=
  (planeP0 h).map (spPlaneOrder.reindexGL K).toMonoidHom

private theorem sl2_transpose_quatI_mul (X : SpecialLinearGroup (Fin 2) K) :
    (X : Matrix (Fin 2) (Fin 2) K)ᵀ * !![0, 1; -1, 0] * (X : Matrix (Fin 2) (Fin 2) K) =
      !![0, 1; -1, 0] := by
  have hdet : (X : Matrix (Fin 2) (Fin 2) K).det = 1 := Matrix.SpecialLinearGroup.det_coe X
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination hdet | linear_combination -hdet | ring

private theorem sl2_blocks_mem (X Y : SpecialLinearGroup (Fin 2) K) :
    (fromBlocks (X : Matrix (Fin 2) (Fin 2) K) 0 0 (Y : Matrix (Fin 2) (Fin 2) K))ᵀ *
      spPlaneGram *
        fromBlocks (X : Matrix (Fin 2) (Fin 2) K) 0 0 (Y : Matrix (Fin 2) (Fin 2) K) =
      spPlaneGram := by
  rw [spPlaneGram, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, zero_mul, mul_zero, add_zero, zero_add]
  rw [sl2_transpose_quatI_mul X, sl2_transpose_quatI_mul Y]

private theorem swap_blocks_mem :
    (fromBlocks 0 1 1 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * spPlaneGram *
      fromBlocks 0 1 1 0 = spPlaneGram := by
  rw [spPlaneGram, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp

theorem spP0_le_statedSp {a b : K} (h : a ^ 2 + b ^ 2 = -1) : spP0 h ≤ StatedSp 2 K := by
  rw [spP0, Subgroup.map_le_iff_le_comap, planeP0, sup_le_iff]
  constructor
  · rintro g ⟨x, rfl⟩
    rw [Subgroup.mem_comap]
    change spPlaneOrder.reindexGL K (planeQuat h x) ∈ StatedSp 2 K
    rw [reindexGL_spPlaneOrder_mem_statedSp_iff, coe_planeQuat]
    exact sl2_blocks_mem (quatHom h x.1) (quatHom h x.2)
  · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
    change spPlaneOrder.reindexGL K planeSwap ∈ StatedSp 2 K
    rw [reindexGL_spPlaneOrder_mem_statedSp_iff, coe_planeSwap]
    exact swap_blocks_mem

theorem isPGroup_spP0 {a b : K} (h : a ^ 2 + b ^ 2 = -1) : IsPGroup 2 (spP0 h) :=
  (isPGroup_planeP0 h).map (spPlaneOrder.reindexGL K).toMonoidHom

theorem adjoin_spP0_eq_top (hK : ringChar K ≠ 2) {a b : K} (h : a ^ 2 + b ^ 2 = -1) :
    Algebra.adjoin K ((fun g : GL (Fin 2 ⊕ Fin 2) K =>
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) '' (spP0 h : Set (GL (Fin 2 ⊕ Fin 2) K))) =
      ⊤ := by
  have hcoe : ∀ g : GL (Fin 2 ⊕ Fin 2) K,
      ((spPlaneOrder.reindexGL K g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2)
        (Fin 2 ⊕ Fin 2) K) =
        Matrix.reindexAlgEquiv K K spPlaneOrder (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    intro g
    rw [Equiv.coe_reindexGL, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  have hset : ((fun g : GL (Fin 2 ⊕ Fin 2) K =>
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) '' (spP0 h : Set (GL (Fin 2 ⊕ Fin 2) K))) =
      (Matrix.reindexAlgEquiv K K spPlaneOrder) ''
        ((fun g : GL (Fin 2 ⊕ Fin 2) K =>
          (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ''
          (planeP0 h : Set (GL (Fin 2 ⊕ Fin 2) K))) := by
    rw [spP0, Subgroup.coe_map, Set.image_image, Set.image_image]
    exact Set.image_congr fun g _ => hcoe g
  rw [hset]
  change Algebra.adjoin K ((Matrix.reindexAlgEquiv K K spPlaneOrder).toAlgHom ''
    ((fun g : GL (Fin 2 ⊕ Fin 2) K =>
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ''
      (planeP0 h : Set (GL (Fin 2 ⊕ Fin 2) K)))) = ⊤
  rw [Algebra.adjoin_image, adjoin_planeP0_eq_top hK h, Algebra.map_top]
  exact (AlgHom.range_eq_top _).mpr (AlgEquiv.surjective _)

theorem sp4_adjoin_eq_top [Finite K] (hK : ringChar K ≠ 2) (P : Sylow 2 (StatedSp 2 K))
    (H : Subgroup (StatedSp 2 K)) (hPH : (P : Subgroup (StatedSp 2 K)) ≤ H) :
    Algebra.adjoin K (Set.range fun h : H => (((h : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = ⊤ := by
  obtain ⟨a, b, h⟩ := (odd_field_two_dimensional_quaternion_matrices hK).1
  exact adjoin_eq_top_of_sylow_le (spP0_le_statedSp h) (isPGroup_spP0 h)
    (adjoin_spP0_eq_top hK h) P hPH

theorem sp4_eq_bot_of_normal_of_charP [Finite K] (hK : ringChar K ≠ 2) {p : ℕ} [Fact p.Prime]
    [CharP K p] (P : Sylow 2 (StatedSp 2 K)) (H : Subgroup (StatedSp 2 K))
    (hPH : (P : Subgroup (StatedSp 2 K)) ≤ H) {A : Subgroup H} [A.Normal] (hA : IsPGroup p A) :
    A = ⊥ :=
  eq_bot_of_normal_of_charP (sp4_adjoin_eq_top hK P H hPH) hA

private theorem charP_of_card_eq_prime {K : Type} [Field K] {q : ℕ} (hq : Nat.Prime q)
    (hK : Nat.card K = q) : CharP K q := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq.ne_zero)
  let hF : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hcard : Fintype.card K = q := by rw [← Nat.card_eq_fintype_card, hK]
  have hdvd : ringChar K ∣ q := by
    rw [← hcard, hn]
    exact dvd_pow_self _ n.ne_zero
  exact ringChar.of_eq ((Nat.prime_dvd_prime_iff_eq hp hq).1 hdvd)

theorem card_statedSp_two_of_card_eq_three {K : Type} [Field K] (hK : Nat.card K = 3) :
    Nat.card (StatedSp 2 K) = 51840 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two K, hK]
  norm_num

theorem sp4_three_eq_bot_of_normal_five {K : Type} [Field K] (hK : Nat.card K = 3)
    (P : Sylow 2 (StatedSp 2 K)) (H : Subgroup (StatedSp 2 K))
    (hPH : (P : Subgroup (StatedSp 2 K)) ≤ H) {A : Subgroup H} [A.Normal] (hA : IsPGroup 5 A) :
    A = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let : Fintype K := Fintype.ofFinite K
  have h3 : CharP K 3 := charP_of_card_eq_prime (by norm_num) hK
  have hchar2 : ringChar K ≠ 2 := by
    have : ringChar K = 3 := ringChar.eq_iff.mpr h3
    omega
  obtain ⟨a, b, h⟩ := (odd_field_two_dimensional_quaternion_matrices hchar2).1
  let φ : GL (Fin 2 ⊕ Fin 2) K ≃* GL (Fin 2 ⊕ Fin 2) K := spPlaneOrder.reindexGL K
  have hx1P : φ (planeQuat h (.a 1, 1)) ∈ spP0 h :=
    Subgroup.mem_map_of_mem _ (planeQuat_mem_planeP0 h _)
  have hy1P : φ (planeQuat h (.xa 0, 1)) ∈ spP0 h :=
    Subgroup.mem_map_of_mem _ (planeQuat_mem_planeP0 h _)
  let x₁ : StatedSp 2 K := ⟨φ (planeQuat h (.a 1, 1)), spP0_le_statedSp h hx1P⟩
  let y₁ : StatedSp 2 K := ⟨φ (planeQuat h (.xa 0, 1)), spP0_le_statedSp h hy1P⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow_le (spP0_le_statedSp h) (isPGroup_spP0 h) P hPH
  have hkill : ∀ b : StatedSp 2 K, Commute b ⁅x₁, y₁⁆ →
      Commute b ⁅x₁, y₁⁆ → b ^ 5 = 1 → b = 1 := by
    intro b hbz _ hb5
    have hzeq : ((⁅x₁, y₁⁆ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
        φ (planeQuat h (.a 2, 1)) := by
      have hq : ((⁅x₁, y₁⁆ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
          φ ⁅planeQuat h (.a 1, 1), planeQuat h (.xa 0, 1)⁆ := by
        dsimp only [x₁, y₁]
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [hq, commutatorElement_planeQuat_z]
    have hbz' : Commute (φ.symm (b : GL (Fin 2 ⊕ Fin 2) K))
        (φ.symm ((⁅x₁, y₁⁆ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)) :=
      hbz.map (φ.symm.toMonoidHom.comp (StatedSp 2 K).subtype)
    have hz : Commute (φ.symm (b : GL (Fin 2 ⊕ Fin 2) K)) (planeQuat h (.a 2, 1)) := by
      rw [hzeq] at hbz'
      simpa using hbz'
    have hcop : Nat.Coprime 5 (Nat.card (GL (Fin 2) K)) := by
      have hcardK : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK]
      have hGL : Nat.card (GL (Fin 2) K) = 48 := by
        rw [Matrix.card_GL_field (𝔽 := K) 2, hcardK]
        simp [Fin.prod_univ_two]
      rw [hGL]
      norm_num
    have hc5 : (φ.symm (b : GL (Fin 2 ⊕ Fin 2) K)) ^ 5 = 1 := by
      have hb5' : ((b ^ 5 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) = 1 := by
        rw [hb5, Subgroup.coe_one]
      have := congrArg (fun w : GL (Fin 2 ⊕ Fin 2) K => φ.symm w) hb5'
      simpa [map_pow, Subgroup.coe_pow] using this
    have hc1 : φ.symm (b : GL (Fin 2 ⊕ Fin 2) K) = 1 :=
      eq_one_of_commute_z_of_pow_eq_one (K := K) hchar2 h hcop hz hc5
    have hbval : (b : GL (Fin 2 ⊕ Fin 2) K) = 1 := by
      have h := MulEquiv.apply_symm_apply φ (b : GL (Fin 2 ⊕ Fin 2) K)
      rw [hc1, map_one] at h
      exact h.symm
    exact Subtype.ext hbval
  have hr : ¬ 5 ^ 2 ∣ Nat.card (StatedSp 2 K) := by
    rw [card_statedSp_two_of_card_eq_three hK]
    norm_num
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact eq_bot_of_normal_of_commute_commutator (G := StatedSp 2 K) (r := 5) hr hA g x₁ y₁ x₁ y₁
    (hg _ hx1P) (hg _ hy1P) (hg _ hx1P) (hg _ hy1P) hkill

theorem sp4_five_eq_bot_of_normal_five {K : Type} [Field K] (hK : Nat.card K = 5)
    (P : Sylow 2 (StatedSp 2 K)) (H : Subgroup (StatedSp 2 K))
    (hPH : (P : Subgroup (StatedSp 2 K)) ≤ H) {A : Subgroup H} [A.Normal] (hA : IsPGroup 5 A) :
    A = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have h5 : CharP K 5 := charP_of_card_eq_prime (by norm_num) hK
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h2 : ringChar K ≠ 2 := by
    have : ringChar K = 5 := ringChar.eq_iff.mpr h5
    omega
  exact sp4_eq_bot_of_normal_of_charP (K := K) (p := 5) h2 P H hPH hA

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
