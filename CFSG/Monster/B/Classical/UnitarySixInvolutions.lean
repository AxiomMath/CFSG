module

public import CFSG.Monster.B.Classical.UnitarySixForm
import all CFSG.Fischer.F4
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.B.Classical.UnitarySix

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix

theorem neg_eq_self' (a : F4) : -a = a := rfl

theorem matrix_neg_eq (M : Matrix (Fin 6) (Fin 6) F4) : -M = M := by
  ext i j
  exact neg_eq_self' _

theorem matrix_add_self (M : Matrix (Fin 6) (Fin 6) F4) : M + M = 0 := by
  ext i j
  exact add_self_eq_zero' _

theorem matrix_sub_eq_add (M M' : Matrix (Fin 6) (Fin 6) F4) : M - M' = M + M' := by
  rw [sub_eq_add_neg, matrix_neg_eq]

theorem vec_add_self (v : V) : v + v = 0 := by
  funext i
  exact add_self_eq_zero' _

theorem scalarHom_injective : Function.Injective scalarHom := by
  intro a b hab
  have h := congrArg (fun g : SU frobeniusF4 6 =>
    ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) 0 0) hab
  simp only [coe_scalarHom, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h
  exact Units.ext h

theorem units_pow_three (a : F4ˣ) : a ^ 3 = 1 := by
  have h : ∀ c : F4, c ≠ 0 → c ^ 3 = 1 := by decide
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, h _ a.ne_zero, Units.val_one])

theorem units_eq_one_of_sq {a : F4ˣ} (h : a ^ 2 = 1) : a = 1 := by
  have h' : ∀ c : F4, c ≠ 0 → c ^ 2 = 1 → c = 1 := by decide
  exact Units.ext (h' _ a.ne_zero (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]))

theorem mem_scalars_iff {g : SU frobeniusF4 6} : g ∈ scalars ↔ ∃ a : F4ˣ, scalarHom a = g :=
  Iff.rfl

theorem exists_unique_involution_lift (x : ProjSU) (hx : x ^ 2 = 1) (_hx1 : x ≠ 1) :
    ∃! A : SU frobeniusF4 6, (A : ProjSU) = x ∧ A ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hg : g ^ 2 ∈ scalars := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hx
  obtain ⟨b, hb⟩ := mem_scalars_iff.mp hg
  have hbmem : scalarHom b ∈ scalars := ⟨b, rfl⟩
  have hcomm : ∀ z ∈ scalars, ∀ h : SU frobeniusF4 6, z * h = h * z :=
    fun z hz h => scalars_commute hz h
  have hbc : Commute (scalarHom b) g := hcomm _ hbmem g
  have hA2 : (scalarHom b * g) ^ 2 = 1 := by
    rw [hbc.mul_pow, ← hb, ← map_pow, ← map_mul, ← pow_succ, units_pow_three, map_one]
  refine ⟨scalarHom b * g, ⟨?_, hA2⟩, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hbmem, one_mul]
  · rintro B ⟨hB, hB2⟩
    have hBg : (scalarHom b * g)⁻¹ * B ∈ scalars := by
      rw [← QuotientGroup.eq, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hbmem,
        one_mul, hB]
    obtain ⟨c, hc⟩ := mem_scalars_iff.mp hBg
    have hB' : B = (scalarHom b * g) * scalarHom c := by
      rw [hc, mul_inv_cancel_left]
    have hcm : scalarHom c ∈ scalars := ⟨c, rfl⟩
    have hcs : Commute (scalarHom b * g) (scalarHom c) := (hcomm _ hcm _).symm
    have hc2 : scalarHom (c ^ 2) = 1 := by
      have h' : B ^ 2 = (scalarHom b * g) ^ 2 * scalarHom c ^ 2 := by rw [hB', hcs.mul_pow]
      rw [hA2, one_mul, hB2] at h'
      rw [map_pow, ← h']
    have : c = 1 := units_eq_one_of_sq (scalarHom_injective (by rw [hc2, map_one]))
    rw [hB', this, map_one, mul_one]

@[expose] noncomputable def invRank (A : SU frobeniusF4 6) : ℕ :=
  (((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) - 1).rank

@[expose] def IsSelfAdj (N : Matrix (Fin 6) (Fin 6) F4) : Prop :=
  ∀ x y, herm (N *ᵥ x) y = herm x (N *ᵥ y)

theorem coe_SU_sq (A : SU frobeniusF4 6) :
    (((A ^ 2 : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
        ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
  rw [pow_two, coe_SU_mul]

theorem mat_sq_of_sq {A : SU frobeniusF4 6} (hA : A ^ 2 = 1) :
    ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
      ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = 1 := by
  rw [← coe_SU_sq, hA, coe_SU_one]

theorem invRank_eq (A : SU frobeniusF4 6) :
    invRank A = (((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) + 1).rank := by
  rw [invRank, matrix_sub_eq_add]

theorem sq_zero_of_involution {A : Matrix (Fin 6) (Fin 6) F4} (hA : A * A = 1) :
    (A + 1) * (A + 1) = 0 := by
  rw [add_mul, mul_add, mul_add, hA, mul_one, one_mul, mul_one, add_assoc, ← add_assoc A,
    matrix_add_self, zero_add, matrix_add_self]

theorem isSelfAdj_of_involution {A : Matrix (Fin 6) (Fin 6) F4} (hA : A * A = 1)
    (hAi : IsIsometry A) : IsSelfAdj (A + 1) := by
  intro x y
  have h1 : herm (A *ᵥ x) y = herm x (A *ᵥ y) := by
    conv_lhs => rw [← one_mulVec y, ← hA, ← mulVec_mulVec, hAi]
  rw [add_mulVec, add_mulVec, one_mulVec, one_mulVec, herm_add_left, herm_add_right, h1]

theorem eq_zero_of_rank_eq_zero {N : Matrix (Fin 6) (Fin 6) F4} (h : N.rank = 0) : N = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  refine Matrix.ext_of_mulVec_single fun j => ?_
  have := LinearMap.congr_fun h (Pi.single j 1)
  rw [Matrix.mulVecLin_apply, LinearMap.zero_apply] at this
  rw [this, zero_mulVec]

theorem rank_pos_of_ne_zero {N : Matrix (Fin 6) (Fin 6) F4} (h : N ≠ 0) : 0 < N.rank :=
  Nat.pos_of_ne_zero fun h0 => h (eq_zero_of_rank_eq_zero h0)

theorem invRank_eq_one_or_two_or_three (A : SU frobeniusF4 6) (hA : A ^ 2 = 1) (hA1 : A ≠ 1) :
    invRank A = 1 ∨ invRank A = 2 ∨ invRank A = 3 := by
  have hN := sq_zero_of_involution (mat_sq_of_sq hA)
  have hle := Matrix.rank_add_rank_le_card_of_mul_eq_zero hN
  rw [Fintype.card_fin] at hle
  have hne : ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) + 1 ≠ 0 := by
    intro h0
    apply hA1
    refine SU_ext ?_
    rw [coe_SU_one, ← sub_eq_zero, matrix_sub_eq_add, h0]
  have hpos := rank_pos_of_ne_zero hne
  rw [invRank_eq]
  omega

@[expose] def rkOne (v : V) : Matrix (Fin 6) (Fin 6) F4 := vecMulVec v fun j => bar (v (Fin.rev j))

theorem rkOne_mulVec (v x : V) : rkOne v *ᵥ x = herm x v • v := by
  have : (fun j => bar (v (Fin.rev j))) ⬝ᵥ x = herm x v := by
    simp only [dotProduct, herm]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [rkOne, Matrix.vecMulVec_mulVec, this, op_smul_eq_smul]

theorem transvecMat_eq (v : V) : transvecMat v = 1 + rkOne v := rfl

theorem isSelfAdj_rkOne (v : V) : IsSelfAdj (rkOne v) := by
  intro x y
  rw [rkOne_mulVec, rkOne_mulVec, herm_smul_left, herm_smul_right, ← herm_swap, mul_comm]

theorem IsSelfAdj.add {N M : Matrix (Fin 6) (Fin 6) F4} (hN : IsSelfAdj N) (hM : IsSelfAdj M) :
    IsSelfAdj (N + M) := fun x y => by
  rw [add_mulVec, add_mulVec, herm_add_left, herm_add_right, hN, hM]

theorem mul_rkOne {P : Matrix (Fin 6) (Fin 6) F4} (hP : IsIsometry P) (v : V) :
    P * rkOne v = rkOne (P *ᵥ v) * P := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, rkOne_mulVec, rkOne_mulVec, mulVec_smul, hP]

theorem rkOne_mul_rkOne {v w : V} (h : herm w v = 0) : rkOne v * rkOne w = 0 := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← mulVec_mulVec, rkOne_mulVec, rkOne_mulVec, herm_smul_left, h, mul_zero, zero_smul,
    zero_mulVec]

theorem eq_zero_of_forall_herm_self {N : Matrix (Fin 6) (Fin 6) F4} (hsa : IsSelfAdj N)
    (h : ∀ y, herm (N *ᵥ y) y = 0) : N = 0 := by
  have hconj : ∀ a b, herm (N *ᵥ b) a = bar (herm (N *ᵥ a) b) := fun a b => by
    rw [hsa, ← herm_swap]
  have key : ∀ x z, herm (N *ᵥ x) z = 0 := by
    intro x z
    have h1 := h (x + z)
    have h2 := h (F4.ω • x + z)
    rw [mulVec_add, herm_add_left, herm_add_right, herm_add_right, h x, h z, hconj x z] at h1
    rw [mulVec_add, herm_add_left, herm_add_right, herm_add_right, h (F4.ω • x), h z,
      hconj (F4.ω • x) z, mulVec_smul, herm_smul_left] at h2
    have hF : ∀ t : F4, 0 + t + (bar t + 0) = 0 →
        0 + F4.ω * t + (bar (F4.ω * t) + 0) = 0 → t = 0 := by decide
    exact hF _ h1 h2
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [zero_mulVec]
  exact eq_zero_of_herm_eq_zero (key _)

theorem peel {N : Matrix (Fin 6) (Fin 6) F4} (hsa : IsSelfAdj N) (hN : N * N = 0) (h0 : N ≠ 0) :
    ∃ v : V, v ≠ 0 ∧ herm v v = 0 ∧ v ∈ LinearMap.range N.mulVecLin ∧
      IsSelfAdj (N + rkOne v) ∧ (N + rkOne v) * (N + rkOne v) = 0 ∧
      (N + rkOne v).rank + 1 = N.rank ∧ (∀ x, herm ((N + rkOne v) *ᵥ x) v = 0) ∧
      LinearMap.range (N + rkOne v).mulVecLin ≤ LinearMap.range N.mulVecLin := by
  have hNN : ∀ x, N *ᵥ (N *ᵥ x) = 0 := fun x => by rw [mulVec_mulVec, hN, zero_mulVec]
  obtain ⟨y, hy⟩ : ∃ y, herm (N *ᵥ y) y ≠ 0 := by
    by_contra! hall
    exact h0 (eq_zero_of_forall_herm_self hsa hall)
  have hy1 : herm (N *ᵥ y) y = 1 := by
    refine eq_one_of_bar_eq ?_ hy
    rw [← herm_swap, ← hsa]
  set v := N *ᵥ y with hv
  have hvv : herm v v = 0 := by rw [hv, hsa, hNN, herm_zero_right]
  have hv0 : v ≠ 0 := fun h => by rw [h, herm_zero_left] at hy1; exact zero_ne_one hy1
  have hNv : N *ᵥ v = 0 := hNN y
  have hyv : herm y v = 1 := by rw [herm_swap, hy1, bar_one]
  set M := N + rkOne v with hM
  have hMx : ∀ x, M *ᵥ x = N *ᵥ x + herm x v • v := fun x => by
    rw [hM, add_mulVec, rkOne_mulVec]
  have hMv : ∀ x, herm (M *ᵥ x) v = 0 := fun x => by
    rw [hMx, herm_add_left, herm_smul_left, hvv, mul_zero, add_zero, hsa, hNv,
      herm_zero_right]
  have hMsa : IsSelfAdj M := hsa.add (isSelfAdj_rkOne v)
  have hMM : M * M = 0 := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [← mulVec_mulVec, hMx, hMx (Pi.single j 1), mulVec_add, mulVec_smul, hNv, smul_zero,
      add_zero, hNN, zero_add, herm_add_left, herm_smul_left, hvv, mul_zero, add_zero, hsa,
      hNv, herm_zero_right, zero_smul, zero_mulVec]
  have hrange : LinearMap.range M.mulVecLin ≤ LinearMap.range N.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    refine ⟨x + herm x v • y, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, mulVec_add, mulVec_smul, ← hv, hMx]
  have hker : LinearMap.ker N.mulVecLin < LinearMap.ker M.mulVecLin := by
    refine lt_of_le_of_ne (fun x hx => ?_) fun heq => ?_
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
      have hxv : herm x v = 0 := by rw [hv, ← hsa, hx, herm_zero_left]
      rw [hMx, hx, hxv, zero_smul, add_zero]
    · have hyM : y ∈ LinearMap.ker M.mulVecLin := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hMx, ← hv, hyv, one_smul, vec_add_self]
      rw [← heq, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hyM
      exact hv0 hyM
  have hlt := Submodule.finrank_lt_finrank_of_lt hker
  have hrn1 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  have hrn2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hsup : LinearMap.range N.mulVecLin ≤ LinearMap.range M.mulVecLin ⊔ (F4 ∙ v) := by
    rintro _ ⟨x, rfl⟩
    have : N *ᵥ x = M *ᵥ x + herm x v • v := by
      rw [hMx, add_assoc, ← add_smul, add_self_eq_zero', zero_smul, add_zero]
    rw [Matrix.mulVecLin_apply, this]
    exact Submodule.add_mem_sup ⟨x, rfl⟩
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  have hle := (Submodule.finrank_mono hsup).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  rw [finrank_span_singleton hv0] at hle
  refine ⟨v, hv0, hvv, ⟨y, rfl⟩, hMsa, hMM, ?_, hMv, hrange⟩
  rw [← hM, Matrix.rank, Matrix.rank]
  omega

theorem exists_decomposition : ∀ (k : ℕ) (N : Matrix (Fin 6) (Fin 6) F4), IsSelfAdj N →
    N * N = 0 → N.rank = k → ∃ v : Fin k → V, (∀ i j, herm (v i) (v j) = 0) ∧
      N = ∑ i, rkOne (v i) ∧ ∀ i, v i ∈ LinearMap.range N.mulVecLin := by
  intro k
  induction k with
  | zero =>
    intro N _ _ hk
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, by rw [eq_zero_of_rank_eq_zero hk]; simp,
      fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro N hsa hN hk
    have h0 : N ≠ 0 := by
      rintro rfl
      rw [Matrix.rank_zero] at hk
      exact Nat.succ_ne_zero k hk.symm
    obtain ⟨v, -, hvv, hvN, hMsa, hMM, hMrank, hMv, hrange⟩ := peel hsa hN h0
    obtain ⟨w, hw, hMw, hwM⟩ := ih (N + rkOne v) hMsa hMM (by omega)
    have hwv : ∀ i, herm (w i) v = 0 := fun i => by
      obtain ⟨x, hx⟩ := hwM i
      rw [← hx, Matrix.mulVecLin_apply, hMv]
    refine ⟨Fin.cons v w, fun i j => ?_, ?_, fun i => ?_⟩
    · cases i using Fin.cases <;> cases j using Fin.cases <;>
        simp only [Fin.cons_zero, Fin.cons_succ, hvv, hw, hwv, herm_eq_zero_comm (hwv _)]
    · rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [← hMw, add_comm, add_assoc, matrix_add_self, add_zero]
    · cases i using Fin.cases
      · exact hvN
      · exact hrange (hwM _)

theorem linearIndependent_of_decomposition {k : ℕ} {N : Matrix (Fin 6) (Fin 6) F4}
    (hk : N.rank = k) {v : Fin k → V} (hN : N = ∑ i, rkOne (v i)) : LinearIndependent F4 v := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
  refine le_antisymm ?_ ((finrank_range_le_card (R := F4) v).trans_eq (Fintype.card_fin k))
  refine hk.symm.le.trans ?_
  rw [Matrix.rank]
  refine Submodule.finrank_mono ?_
  rintro _ ⟨x, rfl⟩
  rw [Matrix.mulVecLin_apply, hN, Matrix.sum_mulVec]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [rkOne_mulVec]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem isIsometry_one_add {N : Matrix (Fin 6) (Fin 6) F4} (hsa : IsSelfAdj N)
    (hN : N * N = 0) : IsIsometry (1 + N) := by
  intro x y
  rw [add_mulVec, add_mulVec, one_mulVec, one_mulVec, herm_add_left, herm_add_right,
    herm_add_right, hsa x y, hsa x (N *ᵥ y), mulVec_mulVec, hN, zero_mulVec, herm_zero_right,
    add_zero, add_assoc, add_self_eq_zero', add_zero]

theorem det_eq_one_of_mul_self {A : Matrix (Fin 6) (Fin 6) F4} (hA : A * A = 1) : A.det = 1 := by
  have h := congrArg Matrix.det hA
  rw [det_mul, det_one] at h
  have hF : ∀ c : F4, c * c = 1 → c = 1 := by decide
  exact hF _ h

theorem one_add_mul_self {N : Matrix (Fin 6) (Fin 6) F4} (hN : N * N = 0) :
    (1 + N) * (1 + N) = 1 := by
  rw [add_mul, mul_add, mul_add, hN, one_mul, mul_one, one_mul, add_zero, add_assoc,
    matrix_add_self, add_zero]

@[expose] noncomputable def invOf (N : Matrix (Fin 6) (Fin 6) F4) (hsa : IsSelfAdj N)
    (hN : N * N = 0) : SU frobeniusF4 6 :=
  mkSU (1 + N) (det_eq_one_of_mul_self (one_add_mul_self hN)) (isIsometry_one_add hsa hN)

@[simp] theorem coe_invOf (N : Matrix (Fin 6) (Fin 6) F4) (hsa : IsSelfAdj N)
    (hN : N * N = 0) :
    (((invOf N hsa hN : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      1 + N :=
  rfl

theorem invOf_sq (N : Matrix (Fin 6) (Fin 6) F4) (hsa : IsSelfAdj N) (hN : N * N = 0) :
    invOf N hsa hN ^ 2 = 1 :=
  SU_ext (by rw [coe_SU_sq, coe_invOf, one_add_mul_self hN, coe_SU_one])

@[expose] noncomputable def mkInv (A : Matrix (Fin 6) (Fin 6) F4) (hA : A * A = 1)
    (hAi : IsIsometry A) : SU frobeniusF4 6 :=
  mkSU A (det_eq_one_of_mul_self hA) hAi

@[expose] def stdSet (k : ℕ) : Finset (Fin 6) := Finset.univ.filter fun i => (i : ℕ) < k

@[expose] noncomputable def stdN (k : ℕ) : Matrix (Fin 6) (Fin 6) F4 :=
  ∑ i ∈ stdSet k, rkOne (Pi.single i 1)

theorem isSelfAdj_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin 6) (Fin 6) F4)
    (hf : ∀ i ∈ s, IsSelfAdj (f i)) : IsSelfAdj (∑ i ∈ s, f i) := by
  intro x y
  rw [Matrix.sum_mulVec, Matrix.sum_mulVec, herm_sum_left, herm_sum_right]
  exact Finset.sum_congr rfl fun i hi => hf i hi x y

theorem isSelfAdj_stdN (k : ℕ) : IsSelfAdj (stdN k) :=
  isSelfAdj_sum _ _ fun _ _ => isSelfAdj_rkOne _

theorem herm_single_single (i j : Fin 6) :
    herm (Pi.single i 1 : V) (Pi.single j 1) = if j = Fin.rev i then 1 else 0 :=
  isFrame_single i j

theorem stdN_mul_self {k : ℕ} (hk : k ≤ 3) : stdN k * stdN k = 0 := by
  rw [stdN, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  refine rkOne_mul_rkOne ?_
  simp only [stdSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  rw [herm_single_single]
  have : ∀ i j : Fin 6, (i : ℕ) < 3 → (j : ℕ) < 3 → i ≠ Fin.rev j := by decide
  simp [this i j (by omega) (by omega)]

@[expose] noncomputable def normalForm (k : ℕ) (hk : k ≤ 3) : SU frobeniusF4 6 :=
  invOf (stdN k) (isSelfAdj_stdN k) (stdN_mul_self hk)

theorem diagCorr_mul_rkOne (d : F4) (i : Fin 6) (hi : (i : ℕ) < 3) :
    diagCorr d * rkOne (Pi.single i 1) = rkOne (Pi.single i 1) * diagCorr d := by
  revert d i; decide +kernel

theorem exists_SU_conj_of_frame {e : Fin 6 → V} (he : IsFrame e) :
    ∃ g : SU frobeniusF4 6, ∀ S : Finset (Fin 6), (∀ i ∈ S, (i : ℕ) < 3) →
      ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * (1 + ∑ i ∈ S, rkOne (Pi.single i 1)) =
        (1 + ∑ i ∈ S, rkOne (e i)) * ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
  obtain ⟨d, -, g, hg⟩ := exists_SU_of_frame he
  refine ⟨g, fun S hS => ?_⟩
  rw [hg, mul_add, add_mul, mul_one, one_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_assoc, diagCorr_mul_rkOne d i (hS i hi), ← mul_assoc, mul_rkOne he.isIsometry,
    frameMat_mulVec_single, mul_assoc]

theorem stdSet_one : stdSet 1 = {0} := by decide

theorem stdSet_two : stdSet 2 = {0, 1} := by decide

theorem stdSet_three : stdSet 3 = {0, 1, 2} := by decide

theorem isConj_normalForm (A : SU frobeniusF4 6) (hA : A ^ 2 = 1) (hA1 : A ≠ 1)
    (hk : invRank A ≤ 3) : IsConj (normalForm (invRank A) hk) A := by
  set M := ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) with hM
  have hsq := mat_sq_of_sq hA
  have hsa := isSelfAdj_of_involution hsq (isIsometry_of_mem A)
  have hN := sq_zero_of_involution hsq
  have hrank : (M + 1).rank = invRank A := (invRank_eq A).symm
  have hAN : M = 1 + (M + 1) := by
    rw [add_comm M 1, ← add_assoc, matrix_add_self, zero_add]
  have key : ∀ e : Fin 6 → V, IsFrame e → (∑ i ∈ stdSet (invRank A), rkOne (e i)) = M + 1 →
      IsConj (normalForm (invRank A) hk) A := by
    intro e he hsum
    obtain ⟨g, hg⟩ := exists_SU_conj_of_frame he
    have hS : ∀ i ∈ stdSet (invRank A), (i : ℕ) < 3 := fun i hi => by
      simp only [stdSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      omega
    have h := hg _ hS
    rw [hsum, ← hAN] at h
    refine isConj_iff.mpr ⟨g, ?_⟩
    refine SU_ext ?_
    rw [coe_SU_mul, coe_SU_mul, normalForm, coe_invOf, stdN, h, mul_assoc, coe_SU_mul_inv,
      mul_one]
  rcases invRank_eq_one_or_two_or_three A hA hA1 with h1 | h2 | h3
  · obtain ⟨v, hv, hdec, -⟩ := exists_decomposition 1 (M + 1) hsa hN (by rw [hrank, h1])
    have hli := linearIndependent_of_decomposition (by rw [hrank, h1]) hdec
    obtain ⟨e, he, he0⟩ := exists_frame_of_isotropic (hli.ne_zero 0) (hv 0 0)
    refine key e he ?_
    rw [h1, stdSet_one, Finset.sum_singleton, he0, hdec, Fin.sum_univ_one]
  · obtain ⟨v, hv, hdec, -⟩ := exists_decomposition 2 (M + 1) hsa hN (by rw [hrank, h2])
    have hli := linearIndependent_of_decomposition (by rw [hrank, h2]) hdec
    have hli' : LinearIndependent F4 ![v 0, v 1] := by
      convert hli using 1
      funext i; fin_cases i <;> rfl
    obtain ⟨e, he, he0, he1⟩ := exists_frame_of_pair hli' (hv 0 0) (hv 1 1) (hv 0 1)
    refine key e he ?_
    rw [h2, stdSet_two, Finset.sum_pair (by decide), he0, he1, hdec, Fin.sum_univ_two]
  · obtain ⟨v, hv, hdec, -⟩ := exists_decomposition 3 (M + 1) hsa hN (by rw [hrank, h3])
    have hli := linearIndependent_of_decomposition (by rw [hrank, h3]) hdec
    have hli' : LinearIndependent F4 ![v 0, v 1, v 2] := by
      convert hli using 1
      funext i; fin_cases i <;> rfl
    obtain ⟨e, he, he0, he1, he2⟩ := exists_frame_of_triple hli' (hv 0 0) (hv 0 1) (hv 0 2)
      (hv 1 1) (hv 1 2) (hv 2 2)
    refine key e he ?_
    rw [h3, stdSet_three, Finset.sum_insert (by decide), Finset.sum_pair (by decide), he0, he1,
      he2, hdec, Fin.sum_univ_three, add_assoc]

theorem invRank_le_three (A : SU frobeniusF4 6) (hA : A ^ 2 = 1) (hA1 : A ≠ 1) :
    invRank A ≤ 3 := by
  rcases invRank_eq_one_or_two_or_three A hA hA1 with h | h | h <;> omega

theorem invRank_conj (g A : SU frobeniusF4 6) : invRank (g * A * g⁻¹) = invRank A := by
  have hdet : IsUnit ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).det := by
    rw [det_of_mem]; exact isUnit_one
  have hdet' : IsUnit (((g⁻¹ : SU frobeniusF4 6) : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4).det := by
    rw [det_of_mem]; exact isUnit_one
  have e : (((g * A * g⁻¹ : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) - 1 =
      ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
        (((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) - 1) *
          ((g⁻¹ : SU frobeniusF4 6) : GL (Fin 6) F4) := by
    rw [coe_SU_mul, coe_SU_mul, mul_sub, sub_mul, mul_one, coe_SU_mul_inv]
  rw [invRank, e, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet, invRank]

theorem isConj_iff_invRank_eq (A B : SU frobeniusF4 6) (hA : A ^ 2 = 1) (hA1 : A ≠ 1)
    (hB : B ^ 2 = 1) (hB1 : B ≠ 1) : IsConj A B ↔ invRank A = invRank B := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := isConj_iff.mp h
    exact (invRank_conj g A).symm
  · intro h
    have hA' := isConj_normalForm A hA hA1 (invRank_le_three A hA hA1)
    have hB' := isConj_normalForm B hB hB1 (invRank_le_three B hB hB1)
    have e : normalForm (invRank A) (invRank_le_three A hA hA1) =
        normalForm (invRank B) (invRank_le_three B hB hB1) := by
      simp only [h]
    rw [e] at hA'
    exact hA'.symm.trans hB'

@[expose] def repMat₁ : Matrix (Fin 6) (Fin 6) F4 := 1 + single 2 3 1

@[expose] def repMat₂ : Matrix (Fin 6) (Fin 6) F4 := 1 + single 0 1 1 + single 4 5 1

@[expose] def repMat₃ : Matrix (Fin 6) (Fin 6) F4 :=
  1 + single 0 1 1 + single 2 3 1 + single 4 5 1

theorem repMat₁_mul_self : repMat₁ * repMat₁ = 1 := by decide +kernel

theorem repMat₂_mul_self : repMat₂ * repMat₂ = 1 := by decide +kernel

theorem repMat₃_mul_self : repMat₃ * repMat₃ = 1 := by decide +kernel

theorem repMat₁_isIsometry : IsIsometry repMat₁ := by
  rw [isIsometry_iff_map_bar]; decide +kernel

theorem repMat₂_isIsometry : IsIsometry repMat₂ := by
  rw [isIsometry_iff_map_bar]; decide +kernel

theorem repMat₃_isIsometry : IsIsometry repMat₃ := by
  rw [isIsometry_iff_map_bar]; decide +kernel

@[expose] noncomputable def rep₁ : SU frobeniusF4 6 :=
  mkInv repMat₁ repMat₁_mul_self repMat₁_isIsometry

@[expose] noncomputable def rep₂ : SU frobeniusF4 6 :=
  mkInv repMat₂ repMat₂_mul_self repMat₂_isIsometry

@[expose] noncomputable def rep₃ : SU frobeniusF4 6 :=
  mkInv repMat₃ repMat₃_mul_self repMat₃_isIsometry

theorem coe_rep₁ :
    (((rep₁ : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      1 + single 2 3 1 :=
  rfl

theorem coe_rep₂ :
    (((rep₂ : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      1 + single 0 1 1 + single 4 5 1 :=
  rfl

theorem coe_rep₃ :
    (((rep₃ : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      1 + single 0 1 1 + single 2 3 1 + single 4 5 1 :=
  rfl

theorem mkInv_sq (A : Matrix (Fin 6) (Fin 6) F4) (hA : A * A = 1) (hAi : IsIsometry A) :
    mkInv A hA hAi ^ 2 = 1 :=
  SU_ext (by rw [coe_SU_sq]; exact hA)

theorem rep₁_sq : rep₁ ^ 2 = 1 := mkInv_sq _ _ _

theorem rep₂_sq : rep₂ ^ 2 = 1 := mkInv_sq _ _ _

theorem rep₃_sq : rep₃ ^ 2 = 1 := mkInv_sq _ _ _

theorem rank_rkOne {v : V} (hv : v ≠ 0) : (rkOne v).rank = 1 := by
  refine le_antisymm (Matrix.rank_vecMulVec_le _ _) (rank_pos_of_ne_zero ?_)
  intro h0
  obtain ⟨x, hx⟩ := exists_herm_eq_one hv
  have := congrArg (· *ᵥ x) h0
  simp only [rkOne_mulVec, hx, one_smul, zero_mulVec] at this
  exact hv this

theorem rank_mul_diagonal {Q : Matrix (Fin 6) (Fin 6) F4} (hQ : Q * Q = 1) (w : Fin 6 → F4) :
    (Q * diagonal w).rank = Fintype.card {i // w i ≠ 0} := by
  have hdet : IsUnit Q.det := by
    refine IsUnit.of_mul_eq_one Q.det ?_
    rw [← det_mul, hQ, det_one]
  rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet, Matrix.rank_diagonal]

theorem invRank_rep₁ : invRank rep₁ = 1 := by
  rw [invRank, coe_rep₁, add_sub_cancel_left]
  have : (single 2 3 1 : Matrix (Fin 6) (Fin 6) F4) = rkOne (Pi.single 2 1) := by decide +kernel
  rw [this, rank_rkOne (by decide)]

private def permQ₂ : Matrix (Fin 6) (Fin 6) F4 :=
  !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0]

private def permQ₃ : Matrix (Fin 6) (Fin 6) F4 :=
  !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 1, 0]

theorem invRank_rep₂ : invRank rep₂ = 2 := by
  rw [invRank, coe_rep₂, add_assoc, add_sub_cancel_left]
  have h : (single 0 1 1 + single 4 5 1 : Matrix (Fin 6) (Fin 6) F4) =
      permQ₂ * diagonal ![0, 1, 0, 0, 0, 1] := by decide +kernel
  rw [h, rank_mul_diagonal (by decide +kernel)]
  decide

theorem invRank_rep₃ : invRank rep₃ = 3 := by
  rw [invRank, coe_rep₃, add_assoc, add_assoc, add_sub_cancel_left]
  have h : (single 0 1 1 + (single 2 3 1 + single 4 5 1) : Matrix (Fin 6) (Fin 6) F4) =
      permQ₃ * diagonal ![0, 1, 0, 1, 0, 1] := by decide +kernel
  rw [h, rank_mul_diagonal (by decide +kernel)]
  decide

@[expose] noncomputable def involutionRep : ℕ → SU frobeniusF4 6
  | 1 => rep₁
  | 2 => rep₂
  | _ => rep₃

theorem isConj_involutionRep (A : SU frobeniusF4 6) (hA : A ^ 2 = 1) (hA1 : A ≠ 1) :
    IsConj A (involutionRep (invRank A)) := by
  have hrep : ∀ k, k = 1 ∨ k = 2 ∨ k = 3 → involutionRep k ^ 2 = 1 ∧ involutionRep k ≠ 1 ∧
      invRank (involutionRep k) = k := by
    have hne : ∀ B : SU frobeniusF4 6, invRank B ≠ 0 → B ≠ 1 := by
      rintro B hB rfl
      rw [invRank, coe_SU_one, sub_self, Matrix.rank_zero] at hB
      exact hB rfl
    rintro k (rfl | rfl | rfl)
    · exact ⟨rep₁_sq, hne rep₁ (by rw [invRank_rep₁]; omega), invRank_rep₁⟩
    · exact ⟨rep₂_sq, hne rep₂ (by rw [invRank_rep₂]; omega), invRank_rep₂⟩
    · exact ⟨rep₃_sq, hne rep₃ (by rw [invRank_rep₃]; omega), invRank_rep₃⟩
  obtain ⟨h2, h1, hk⟩ := hrep _ (invRank_eq_one_or_two_or_three A hA hA1)
  exact (isConj_iff_invRank_eq A _ hA hA1 h2 h1).mpr hk.symm

theorem herm_single_self (i : Fin 6) : herm (Pi.single i 1 : V) (Pi.single i 1) = 0 := by
  rw [herm_single_single]
  revert i; decide

theorem invRank_eq_one_iff (A : SU frobeniusF4 6) (hA : A ^ 2 = 1) :
    invRank A = 1 ↔ ∃ (v : V) (hv : herm v v = 0), v ≠ 0 ∧ A = transvec v hv := by
  constructor
  · intro h1
    set M := ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) with hM
    have hsq := mat_sq_of_sq hA
    have hsa := isSelfAdj_of_involution hsq (isIsometry_of_mem A)
    have hN := sq_zero_of_involution hsq
    have hrank : (M + 1).rank = 1 := by rw [← invRank_eq]; exact h1
    obtain ⟨v, hv, hdec, -⟩ := exists_decomposition 1 (M + 1) hsa hN hrank
    have hli := linearIndependent_of_decomposition hrank hdec
    refine ⟨v 0, hv 0 0, hli.ne_zero 0, SU_ext ?_⟩
    rw [coe_transvec, transvecMat_eq, ← Fin.sum_univ_one (fun i => rkOne (v i)), ← hdec,
      add_comm M 1, ← add_assoc, matrix_add_self, zero_add]
  · rintro ⟨v, hv, hv0, rfl⟩
    rw [invRank, coe_transvec, transvecMat_eq, add_sub_cancel_left, rank_rkOne hv0]

theorem transvec_sq (v : V) (hv : herm v v = 0) : transvec v hv ^ 2 = 1 := by
  rw [pow_two, transvec_mul_self]

theorem transvec_eq_transvec_iff {v w : V} (hv : herm v v = 0) (hw : herm w w = 0)
    (hw0 : w ≠ 0) : transvec v hv = transvec w hw ↔ (F4 ∙ v) = (F4 ∙ w) := by
  constructor
  · intro h
    have hmat : transvecMat v = transvecMat w := by
      rw [← coe_transvec v hv, ← coe_transvec w hw, h]
    obtain ⟨x, hx⟩ := exists_herm_eq_one hw0
    have h1 := congrArg (· *ᵥ x) hmat
    simp only [transvecMat_mulVec, hx, one_smul, add_right_inj] at h1
    have hc : herm x v ≠ 0 := fun h0 => hw0 (by rw [← h1, h0, zero_smul])
    rw [← h1, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc)]
  · intro h
    obtain ⟨z, rfl⟩ := (Submodule.span_singleton_eq_span_singleton).mp h
    refine SU_ext ?_
    rw [coe_transvec, coe_transvec, Units.smul_def, transvecMat_smul z.ne_zero]

theorem conj_transvec (g : SU frobeniusF4 6) (v : V) (hv : herm v v = 0) :
    ∃ hv' : herm (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v)
      (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v) = 0,
      g * transvec v hv * g⁻¹ = transvec _ hv' := by
  refine ⟨by rw [isIsometry_of_mem g, hv], SU_ext ?_⟩
  rw [coe_SU_mul, coe_SU_mul, coe_transvec, coe_transvec, mul_transvecMat (isIsometry_of_mem g),
    mul_assoc, coe_SU_mul_inv, mul_one]

theorem isConj_transvec_single {v : V} (hv0 : v ≠ 0) (hv : herm v v = 0) :
    IsConj (transvec (Pi.single 0 1) (herm_single_self 0)) (transvec v hv) := by
  obtain ⟨e, he, he0⟩ := exists_frame_of_isotropic hv0 hv
  obtain ⟨d, hd0, g, hg⟩ := exists_SU_of_frame he
  refine isConj_iff.mpr ⟨g, SU_ext ?_⟩
  have hgu : ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ Pi.single 0 1 = d • v := by
    rw [hg, ← mulVec_mulVec, diagCorr_mulVec_single, mulVec_smul, frameMat_mulVec_single, he0]
    rfl
  rw [coe_SU_mul, coe_SU_mul, coe_transvec, coe_transvec, mul_transvecMat (isIsometry_of_mem g),
    hgu, transvecMat_smul hd0, mul_assoc, coe_SU_mul_inv, mul_one]

theorem isConj_transvec {v w : V} (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hv : herm v v = 0)
    (hw : herm w w = 0) : IsConj (transvec v hv) (transvec w hw) :=
  (isConj_transvec_single hv0 hv).symm.trans (isConj_transvec_single hw0 hw)

theorem unitary_six_involution_rank_normal_forms :
    (∀ x : ProjSU, x ^ 2 = 1 → x ≠ 1 →
      ∃! A : SU frobeniusF4 6, (A : ProjSU) = x ∧ A ^ 2 = 1) ∧
    (∀ A : SU frobeniusF4 6, A ^ 2 = 1 → A ≠ 1 →
      invRank A = 1 ∨ invRank A = 2 ∨ invRank A = 3) ∧
    (∀ A B : SU frobeniusF4 6, A ^ 2 = 1 → A ≠ 1 → B ^ 2 = 1 → B ≠ 1 →
      (IsConj A B ↔ invRank A = invRank B)) ∧
    ((((rep₁ : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        1 + single 2 3 1 ∧ rep₁ ^ 2 = 1 ∧ invRank rep₁ = 1) ∧
    ((((rep₂ : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        1 + single 0 1 1 + single 4 5 1 ∧ rep₂ ^ 2 = 1 ∧ invRank rep₂ = 2) ∧
    ((((rep₃ : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        1 + single 0 1 1 + single 2 3 1 + single 4 5 1 ∧ rep₃ ^ 2 = 1 ∧ invRank rep₃ = 3) ∧
    (∀ A : SU frobeniusF4 6, A ^ 2 = 1 → A ≠ 1 → IsConj A (involutionRep (invRank A))) ∧
    (∀ A : SU frobeniusF4 6, A ^ 2 = 1 →
      (invRank A = 1 ↔ ∃ (v : V) (hv : herm v v = 0), v ≠ 0 ∧ A = transvec v hv)) ∧
    (∀ (v : V) (hv : herm v v = 0), transvec v hv ^ 2 = 1) ∧
    (∀ (v w : V) (hv : herm v v = 0) (hw : herm w w = 0), v ≠ 0 → w ≠ 0 →
      (transvec v hv = transvec w hw ↔ (F4 ∙ v) = (F4 ∙ w))) ∧
    (∀ (v w : V) (hv : herm v v = 0) (hw : herm w w = 0), v ≠ 0 → w ≠ 0 →
      IsConj (transvec v hv) (transvec w hw)) ∧
    (∀ (g : SU frobeniusF4 6) (v : V) (hv : herm v v = 0),
      ∃ hv' : herm (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v)
        (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v) = 0,
        g * transvec v hv * g⁻¹ = transvec _ hv') :=
  ⟨exists_unique_involution_lift, invRank_eq_one_or_two_or_three, isConj_iff_invRank_eq,
    ⟨coe_rep₁, rep₁_sq, invRank_rep₁⟩, ⟨coe_rep₂, rep₂_sq, invRank_rep₂⟩,
    ⟨coe_rep₃, rep₃_sq, invRank_rep₃⟩, isConj_involutionRep, invRank_eq_one_iff, transvec_sq,
    fun _ _ hv hw _ hw0 => transvec_eq_transvec_iff hv hw hw0,
    fun _ _ hv hw hv0 hw0 => isConj_transvec hv0 hw0 hv hw, conj_transvec⟩

end CFSG.Monster.B.Classical.UnitarySix
