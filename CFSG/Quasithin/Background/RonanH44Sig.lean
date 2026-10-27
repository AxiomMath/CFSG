module

public import CFSG.Quasithin.Background.RonanH44Herm
public import CFSG.Quasithin.Background.HL3NineM

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def sig (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    MulAut (HMod n K) :=
  fldAut (bar n)

theorem sig_apply (X : HMod n K) : mat (sig n K X) = (mat X).map (bar n) := rfl

theorem sig_mul_self (hK : Nat.card K = (2 ^ n) ^ 2) : sig n K * sig n K = 1 := by
  have h : (bar n : K ≃+* K) * bar n = 1 := RingEquiv.ext (bar_bar hK)
  unfold sig
  rw [← fldAut_mul, h, fldAut_one]

theorem mem_fixV_sig (hK : Nat.card K = (2 ^ n) ^ 2) {X : HMod n K} :
    X ∈ fixV (Subgroup.zpowers (sig n K)) ↔ ∀ i j : Fin 3, bar n (mat X i j) = mat X i j := by
  have hfix : sig n K X = X ↔ (mat X).map (bar n) = mat X := by
    rw [← sig_apply]
    exact mat_injective.eq_iff.symm
  rw [mem_fixV_zpowers_iff_apply, hfix]
  constructor
  · intro h i j
    exact congrFun (congrFun h i) j
  · intro h
    ext i j
    exact h i j

theorem mat_symm_of_bar {X : HMod n K} (hF : ∀ i j : Fin 3, bar n (mat X i j) = mat X i j)
    (i j : Fin 3) : mat X j i = mat X i j :=
  (hF j i).symm.trans (herm_apply X i j)

@[expose] noncomputable def sigPsi (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    HMod n K →* HMod n K where
  toFun W := sig n K W * W⁻¹
  map_one' := by simp
  map_mul' W V := by
    simp only [map_mul, mul_inv]
    ac_rfl

theorem sigPsi_apply (W : HMod n K) : sigPsi n K W = sig n K W * W⁻¹ := rfl

theorem mat_sigPsi (W : HMod n K) : mat (sigPsi n K W) = (mat W).map (bar n) + -mat W := rfl

theorem sig_zpow_cases (hK : Nat.card K = (2 ^ n) ^ 2) {x : MulAut (HMod n K)}
    (hx : x ∈ Subgroup.zpowers (sig n K)) : x = 1 ∨ x = sig n K := by
  have h2 : sig n K ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact sig_mul_self hK
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [_root_.zpow_mul, h2, _root_.one_zpow]
  · right
    rw [_root_.zpow_add, _root_.zpow_one, _root_.zpow_mul, h2, _root_.one_zpow, _root_.one_mul]

theorem commV_sig_eq (hK : Nat.card K = (2 ^ n) ^ 2) :
    commV (Subgroup.zpowers (sig n K)) = (sigPsi n K).range := by
  apply le_antisymm
  · unfold commV
    rw [Subgroup.closure_le]
    rintro w ⟨x, hx, v, rfl⟩
    rcases sig_zpow_cases hK hx with rfl | rfl
    · exact MonoidHom.mem_range.2 ⟨1, by simp [sigPsi_apply]⟩
    · exact MonoidHom.mem_range.2 ⟨v, rfl⟩
  · rintro w ⟨V, rfl⟩
    unfold commV
    apply Subgroup.subset_closure
    exact ⟨sig n K, Subgroup.mem_zpowers _, V, rfl⟩

theorem mem_commV_sig (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {X : HMod n K} :
    X ∈ commV (Subgroup.zpowers (sig n K)) ↔
      (∀ i : Fin 3, mat X i i = 0) ∧ ∀ i j : Fin 3, bar n (mat X i j) = mat X i j := by
  rw [commV_sig_eq hK, MonoidHom.mem_range]
  constructor
  · rintro ⟨W, rfl⟩
    simp only [mat_sigPsi, Matrix.add_apply, Matrix.neg_apply, Matrix.map_apply]
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · simp [herm_apply W i i]
    · rw [map_add, map_neg, bar_bar hK, CharTwo.neg_eq, CharTwo.neg_eq, add_comm]
  · rintro ⟨hdiag, hF⟩
    obtain ⟨ω, hω⟩ := exists_trace_one hn hK
    have hsym := mat_symm_of_bar hF
    obtain ⟨U, hUpq⟩ : ∃ U : Matrix (Fin 3) (Fin 3) K,
        ∀ p q, U p q = if p < q then mat X p q else 0 :=
      ⟨Matrix.of fun p q => if p < q then mat X p q else 0, fun p q => rfl⟩
    have hUbar : ∀ p q, bar n (U p q) = U p q := by
      intro p q
      rw [hUpq]
      split_ifs
      · exact hF p q
      · exact map_zero _
    have hUsum : ∀ p q, U p q + U q p = mat X p q := by
      intro p q
      rw [hUpq, hUpq]
      rcases lt_trichotomy p q with h | rfl | h
      · rw [if_pos h, if_neg (not_lt.2 h.le), add_zero]
      · rw [if_neg (lt_irrefl _), hdiag p, add_zero]
      · rw [if_neg (not_lt.2 h.le), if_pos h, zero_add, hsym p q]
    obtain ⟨W, hWpq⟩ : ∃ W : Matrix (Fin 3) (Fin 3) K,
        ∀ p q, W p q = ω * U p q + bar n ω * U q p :=
      ⟨Matrix.of fun p q => ω * U p q + bar n ω * U q p, fun p q => rfl⟩
    have hWherm : (conjM n W)ᵀ = W := by
      ext p q
      show bar n (W q p) = W p q
      rw [hWpq q p, map_add, map_mul, map_mul, bar_bar hK, hUbar, hUbar, hWpq p q]
      ring
    refine ⟨mkH W hWherm, ?_⟩
    apply mat_injective
    rw [mat_sigPsi, mat_mkH]
    ext p q
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.map_apply]
    rw [hWpq p q, CharTwo.neg_eq, map_add, map_mul, map_mul, bar_bar hK, hUbar, hUbar]
    linear_combination (U p q + U q p) * hω + hUsum p q

theorem bar_val_fq (x : Fq n K) : bar n (x : K) = x :=
  CFSG.Quasithin.SteinbergCB.mem_frobFixed.1 x.2

theorem herm_of_fq {Z : Matrix (Fin 3) (Fin 3) (Fq n K)} (hZ : Zᵀ = Z) :
    (conjM n (Z.map Subtype.val))ᵀ = Z.map Subtype.val := by
  ext i j
  have h2 : Z j i = Z i j := congrFun (congrFun hZ i) j
  show bar n ((Z j i : Fq n K) : K) = ((Z i j : Fq n K) : K)
  rw [bar_val_fq, h2]

@[expose] noncomputable def fixVEquivSym (hK : Nat.card K = (2 ^ n) ^ 2) :
    {Z : Matrix (Fin 3) (Fin 3) (Fq n K) // Zᵀ = Z} ≃ ↥(fixV (Subgroup.zpowers (sig n K))) where
  toFun Z := ⟨mkH (Z.1.map Subtype.val) (herm_of_fq Z.2), (mem_fixV_sig hK).2 fun i j => by
    rw [mat_mkH]
    exact bar_val_fq (Z.1 i j)⟩
  invFun X := ⟨Matrix.of fun i j => ⟨mat X.1 i j,
      CFSG.Quasithin.SteinbergCB.mem_frobFixed.2 ((mem_fixV_sig hK).1 X.2 i j)⟩,
    Matrix.ext fun i j => Subtype.ext (mat_symm_of_bar ((mem_fixV_sig hK).1 X.2) i j)⟩
  left_inv Z := Subtype.ext (Matrix.ext fun i j => Subtype.ext rfl)
  right_inv X := Subtype.ext (mat_injective (Matrix.ext fun i j => rfl))

theorem card_fixV_sig (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card ↥(fixV (Subgroup.zpowers (sig n K))) = 2 ^ (6 * n) := by
  rw [← Nat.card_congr (fixVEquivSym hK), card_sym, card_Fq hn hK]
  ring

@[expose] def sigAltMat (p : Fq n K × Fq n K × Fq n K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, (p.1 : K), (p.2.1 : K); (p.1 : K), 0, (p.2.2 : K); (p.2.1 : K), (p.2.2 : K), 0]

theorem sigAltMat_herm (p : Fq n K × Fq n K × Fq n K) :
    (conjM n (sigAltMat p))ᵀ = sigAltMat p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigAltMat, conjM, bar_val_fq]

theorem sigAltMat_mem (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (p : Fq n K × Fq n K × Fq n K) :
    mkH (sigAltMat p) (sigAltMat_herm p) ∈ commV (Subgroup.zpowers (sig n K)) := by
  rw [mem_commV_sig hn hK, mat_mkH]
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · fin_cases i <;> simp [sigAltMat]
  · fin_cases i <;> fin_cases j <;> simp [sigAltMat, bar_val_fq]

@[expose] noncomputable def commVEquiv (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    (Fq n K × Fq n K × Fq n K) ≃ ↥(commV (Subgroup.zpowers (sig n K))) where
  toFun p := ⟨mkH (sigAltMat p) (sigAltMat_herm p), sigAltMat_mem hn hK p⟩
  invFun X := (⟨mat X.1 0 1, CFSG.Quasithin.SteinbergCB.mem_frobFixed.2
      (((mem_commV_sig hn hK).1 X.2).2 0 1)⟩,
    ⟨mat X.1 0 2, CFSG.Quasithin.SteinbergCB.mem_frobFixed.2
      (((mem_commV_sig hn hK).1 X.2).2 0 2)⟩,
    ⟨mat X.1 1 2, CFSG.Quasithin.SteinbergCB.mem_frobFixed.2
      (((mem_commV_sig hn hK).1 X.2).2 1 2)⟩)
  left_inv p := Prod.ext (Subtype.ext rfl) (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl))
  right_inv X := by
    obtain ⟨hdiag, hF⟩ := (mem_commV_sig hn hK).1 X.2
    have h10 := mat_symm_of_bar hF 0 1
    have h20 := mat_symm_of_bar hF 0 2
    have h21 := mat_symm_of_bar hF 1 2
    apply Subtype.ext
    apply mat_injective
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sigAltMat, hdiag, h10, h20, h21, mat_mkH]

theorem rk_fixV_sig (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    rk ↥(fixV (Subgroup.zpowers (sig n K))) = 6 * n := by
  unfold rk
  rw [card_fixV_sig hn hK, padicValNat.prime_pow]

theorem rk_commV_sig (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    rk ↥(commV (Subgroup.zpowers (sig n K))) = 3 * n := by
  unfold rk
  rw [← Nat.card_congr (commVEquiv hn hK), Nat.card_prod, Nat.card_prod, card_Fq hn hK,
    ← pow_add, ← pow_add, padicValNat.prime_pow]
  omega

theorem rkIdx_fixV_sig (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    rkIdx (fixV (Subgroup.zpowers (sig n K))) = 3 * n := by
  have h1 := rk_add_rkIdx (fixV (Subgroup.zpowers (sig n K)))
  have h2 : rk (HMod n K) = 9 * n := by
    unfold rk
    rw [card_HMod hn hK, padicValNat.prime_pow]
  rw [rk_fixV_sig hn hK, h2] at h1
  omega

end CFSG.Quasithin.RonanH44
