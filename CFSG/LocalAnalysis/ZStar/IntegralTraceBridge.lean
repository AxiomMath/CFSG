module

public import CFSG.LocalAnalysis.ZStar.CharacterContradiction
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG

namespace ZStar.IntegralTraceBridge

noncomputable section

universe u v w

private theorem rank_map_le_rank_map
    {R : Type u} {k : Type v} {K : Type w}
    [CommRing R] [Field k] [Field K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (q : R →+* k) (hq : Function.Surjective q)
    (j : R →+* K) (hj : Function.Injective j)
    (A : Matrix n n R) :
    (A.map q).rank ≤ (A.map j).rank := by
  classical
  let B : Matrix n n k := A.map q
  obtain ⟨V, U, e, _hV, _hU, hnormal⟩ :=
    Matrix.exists_rank_normal_form B
  let liftEntry : k → R := fun x ↦ Classical.choose (hq x)
  have q_liftEntry (x : k) : q (liftEntry x) = x :=
    Classical.choose_spec (hq x)
  let liftMatrix : Matrix n n k → Matrix n n R :=
    fun M i l ↦ liftEntry (M i l)
  have map_liftMatrix (M : Matrix n n k) :
      (liftMatrix M).map q = M := by
    ext i l
    exact q_liftEntry (M i l)
  let C : Matrix n n R := liftMatrix V * A * liftMatrix U
  have hC : C.map q =
      (Matrix.fromBlocks 1 0 0 0).submatrix e e := by
    calc
      C.map q = (liftMatrix V).map q * A.map q *
          (liftMatrix U).map q := by
        simp only [C, Matrix.map_mul]
      _ = V * B * U := by
        rw [map_liftMatrix, map_liftMatrix]
      _ = (Matrix.fromBlocks 1 0 0 0).submatrix e e := hnormal
  let first : Fin B.rank → n := fun i ↦ e.symm (Sum.inl i)
  let C₀ : Matrix (Fin B.rank) (Fin B.rank) R :=
    C.submatrix first first
  have hC₀ : C₀.map q = 1 := by
    ext i l
    have h := congrFun (congrFun hC (first i)) (first l)
    simpa [C₀, first] using h
  have hdetC₀q : q C₀.det = 1 := by
    calc
      q C₀.det = (q.mapMatrix C₀).det := q.map_det C₀
      _ = (C₀.map q).det := rfl
      _ = 1 := by rw [hC₀, Matrix.det_one]
  have hdetC₀ : C₀.det ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hdetC₀q
    exact zero_ne_one hdetC₀q
  have hdetC₀K : (C₀.map j).det ≠ 0 := by
    have hjdet : j C₀.det ≠ 0 := by
      intro hzero
      apply hdetC₀
      apply hj
      simpa using hzero
    intro hzero
    apply hjdet
    calc
      j C₀.det = (j.mapMatrix C₀).det := j.map_det C₀
      _ = (C₀.map j).det := rfl
      _ = 0 := hzero
  have hrankC₀K : (C₀.map j).rank = B.rank := by
    simpa using Matrix.rank_of_det_ne_zero hdetC₀K
  have hsubmatrix : C₀.map j = (C.map j).submatrix first first := by
    ext i l
    rfl
  calc
    (A.map q).rank = B.rank := rfl
    _ = (C₀.map j).rank := hrankC₀K.symm
    _ = ((C.map j).submatrix first first).rank := by rw [hsubmatrix]
    _ ≤ (C.map j).rank := Matrix.rank_submatrix_le _ _ _
    _ = ((liftMatrix V).map j * A.map j *
        (liftMatrix U).map j).rank := by
      simp only [C, Matrix.map_mul]
    _ ≤ ((liftMatrix V).map j * A.map j).rank :=
      Matrix.rank_mul_le_left _ _
    _ ≤ (A.map j).rank := Matrix.rank_mul_le_right _ _

private theorem rank_eq_finrank_range_toLin'
    {K : Type u} [Field K]
    {n : Type v} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) :
    A.rank = Module.finrank K (Matrix.toLin' A).range := by
  calc
    A.rank = Module.finrank K
        ((Matrix.toLin (Pi.basisFun K n) (Pi.basisFun K n)) A).range :=
      Matrix.rank_eq_finrank_range_toLin A
        (Pi.basisFun K n) (Pi.basisFun K n)
    _ = Module.finrank K (Matrix.toLin' A).range := by
      rw [Matrix.toLin_eq_toLin']

private theorem rank_add_eq_of_orthogonal_idempotents
    {K : Type u} [Field K]
    {n : Type v} [Fintype n] [DecidableEq n]
    (A B : Matrix n n K)
    (hA : A * A = A) (hB : B * B = B)
    (hAB : A * B = 0) (hBA : B * A = 0) :
    (A + B).rank = A.rank + B.rank := by
  let f : (n → K) →ₗ[K] (n → K) := Matrix.toLin' A
  let g : (n → K) →ₗ[K] (n → K) := Matrix.toLin' B
  have hf : IsIdempotentElem f := by
    rw [isIdempotentElem_iff]
    change f ∘ₗ f = f
    simpa only [f, ← Matrix.toLin'_mul] using congrArg Matrix.toLin' hA
  have hg : IsIdempotentElem g := by
    rw [isIdempotentElem_iff]
    change g ∘ₗ g = g
    simpa only [g, ← Matrix.toLin'_mul] using congrArg Matrix.toLin' hB
  have hfg : f ∘ₗ g = 0 := by
    simpa only [f, g, ← Matrix.toLin'_mul, map_zero] using
      congrArg Matrix.toLin' hAB
  have hgf : g ∘ₗ f = 0 := by
    simpa only [f, g, ← Matrix.toLin'_mul, map_zero] using
      congrArg Matrix.toLin' hBA
  have hdisjoint : Disjoint f.range g.range := by
    apply (LinearMap.IsIdempotentElem.isCompl hf).disjoint.mono_right
    intro x hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    change f (g y) = 0
    have := LinearMap.congr_fun hfg y
    simpa using this
  have hrange : (f + g).range = f.range ⊔ g.range := by
    apply le_antisymm
    · exact LinearMap.range_add_le f g
    · apply sup_le
      · intro x hx
        rw [LinearMap.mem_range] at hx ⊢
        obtain ⟨y, rfl⟩ := hx
        refine ⟨f y, ?_⟩
        change f (f y) + g (f y) = f y
        have hff : f (f y) = f y := LinearMap.congr_fun
          (show f ∘ₗ f = f by exact (isIdempotentElem_iff.mp hf)) y
        have hgf' : g (f y) = 0 := LinearMap.congr_fun hgf y
        rw [hff, hgf', add_zero]
      · intro x hx
        rw [LinearMap.mem_range] at hx ⊢
        obtain ⟨y, rfl⟩ := hx
        refine ⟨g y, ?_⟩
        change f (g y) + g (g y) = g y
        have hgg : g (g y) = g y := LinearMap.congr_fun
          (show g ∘ₗ g = g by exact (isIdempotentElem_iff.mp hg)) y
        have hfg' : f (g y) = 0 := LinearMap.congr_fun hfg y
        rw [hgg, hfg', zero_add]
  have htoadd : Matrix.toLin' (A + B) = f + g := by
    simp only [map_add, f, g]
  rw [rank_eq_finrank_range_toLin', rank_eq_finrank_range_toLin',
    rank_eq_finrank_range_toLin']
  rw [htoadd]
  change Module.finrank K (f + g).range =
    Module.finrank K f.range + Module.finrank K g.range
  rw [hrange, ← Submodule.finrank_sup_add_finrank_inf_eq]
  rw [hdisjoint.eq_bot]
  simp

private theorem rank_eq_add_of_scaled_orthogonal
    {K : Type u} [Field K]
    {n : Type v} [Fintype n] [DecidableEq n]
    (E A B : Matrix n n K) (c d : K)
    (hc : c ≠ 0) (hd : d ≠ 0)
    (hA : A * A = c • A) (hB : B * B = d • B)
    (hAB : A * B = 0) (hBA : B * A = 0)
    (hsum : c⁻¹ • A + d⁻¹ • B = E) :
    E.rank = A.rank + B.rank := by
  have hAi : (c⁻¹ • A) * (c⁻¹ • A) = c⁻¹ • A := by
    calc
      (c⁻¹ • A) * (c⁻¹ • A) = (c⁻¹ * c⁻¹) • (A * A) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = (c⁻¹ * c⁻¹) • (c • A) := by rw [hA]
      _ = c⁻¹ • A := by simp [smul_smul, hc]
  have hBi : (d⁻¹ • B) * (d⁻¹ • B) = d⁻¹ • B := by
    calc
      (d⁻¹ • B) * (d⁻¹ • B) = (d⁻¹ * d⁻¹) • (B * B) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = (d⁻¹ * d⁻¹) • (d • B) := by rw [hB]
      _ = d⁻¹ • B := by simp [smul_smul, hd]
  have hAiBi : (c⁻¹ • A) * (d⁻¹ • B) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAB, smul_zero]
  have hBiAi : (d⁻¹ • B) * (c⁻¹ • A) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hBA, smul_zero]
  have hrankA : (c⁻¹ • A).rank = A.rank :=
    Matrix.rank_smul_of_mem_nonZeroDivisors A (by simp [hc])
  have hrankB : (d⁻¹ • B).rank = B.rank :=
    Matrix.rank_smul_of_mem_nonZeroDivisors B (by simp [hd])
  calc
    E.rank = (c⁻¹ • A + d⁻¹ • B).rank :=
      congrArg (fun M : Matrix n n K ↦ M.rank) hsum.symm
    _ = (c⁻¹ • A).rank + (d⁻¹ • B).rank :=
      rank_add_eq_of_orthogonal_idempotents _ _ hAi hBi hAiBi hBiAi
    _ = A.rank + B.rank := by rw [hrankA, hrankB]

private theorem rank_idempotent_map_eq
    {R : Type u} {k : Type v} {K : Type w}
    [CommRing R] [Field k] [Field K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (q : R →+* k) (hq : Function.Surjective q)
    (j : R →+* K) (hj : Function.Injective j)
    (E : Matrix n n R) (hE : E * E = E) :
    (E.map q).rank = (E.map j).rank := by
  have hEq : E.map q * E.map q = E.map q := by
    simpa only [Matrix.map_mul] using congrArg (fun M ↦ M.map q) hE
  have hEj : E.map j * E.map j = E.map j := by
    simpa only [Matrix.map_mul] using congrArg (fun M ↦ M.map j) hE
  have hCq : (1 - E.map q) * (1 - E.map q) = 1 - E.map q := by
    calc
      (1 - E.map q) * (1 - E.map q) =
          1 - E.map q - E.map q + E.map q * E.map q := by noncomm_ring
      _ = 1 - E.map q := by rw [hEq]; abel
  have hCj : (1 - E.map j) * (1 - E.map j) = 1 - E.map j := by
    calc
      (1 - E.map j) * (1 - E.map j) =
          1 - E.map j - E.map j + E.map j * E.map j := by noncomm_ring
      _ = 1 - E.map j := by rw [hEj]; abel
  have hsumq := rank_add_eq_of_orthogonal_idempotents
    (E.map q) (1 - E.map q) hEq hCq
      (by calc
        E.map q * (1 - E.map q) = E.map q - E.map q * E.map q := by noncomm_ring
        _ = 0 := by rw [hEq]; abel)
      (by calc
        (1 - E.map q) * E.map q = E.map q - E.map q * E.map q := by noncomm_ring
        _ = 0 := by rw [hEq]; abel)
  have hsumj := rank_add_eq_of_orthogonal_idempotents
    (E.map j) (1 - E.map j) hEj hCj
      (by calc
        E.map j * (1 - E.map j) = E.map j - E.map j * E.map j := by noncomm_ring
        _ = 0 := by rw [hEj]; abel)
      (by calc
        (1 - E.map j) * E.map j = E.map j - E.map j * E.map j := by noncomm_ring
        _ = 0 := by rw [hEj]; abel)
  have hcompq : E.map q + (1 - E.map q) = 1 := by abel
  have hcompj : E.map j + (1 - E.map j) = 1 := by abel
  have hsumq' : Fintype.card n =
      (E.map q).rank + (1 - E.map q).rank := by
    calc
      Fintype.card n = (1 : Matrix n n k).rank := Matrix.rank_one.symm
      _ = (E.map q + (1 - E.map q)).rank :=
        congrArg (fun A : Matrix n n k ↦ A.rank) hcompq.symm
      _ = (E.map q).rank + (1 - E.map q).rank := hsumq
  have hsumj' : Fintype.card n =
      (E.map j).rank + (1 - E.map j).rank := by
    calc
      Fintype.card n = (1 : Matrix n n K).rank := Matrix.rank_one.symm
      _ = (E.map j + (1 - E.map j)).rank :=
        congrArg (fun A : Matrix n n K ↦ A.rank) hcompj.symm
      _ = (E.map j).rank + (1 - E.map j).rank := hsumj
  have hmapCq : (1 - E).map q = 1 - E.map q := by
    ext i l
    by_cases h : i = l
    · subst l
      simp
    · simp [h]
  have hmapCj : (1 - E).map j = 1 - E.map j := by
    ext i l
    by_cases h : i = l
    · subst l
      simp
    · simp [h]
  have hqsum : (E.map q).rank + ((1 - E).map q).rank = Fintype.card n := by
    rw [hmapCq]
    exact hsumq'.symm
  have hjsum : (E.map j).rank + ((1 - E).map j).rank = Fintype.card n := by
    rw [hmapCj]
    exact hsumj'.symm
  have hEle := rank_map_le_rank_map q hq j hj E
  have hCle := rank_map_le_rank_map q hq j hj (1 - E)
  omega

private theorem ranks_eq_of_modular_half_rank
    {R : Type u} {k : Type v} {K : Type w}
    [CommRing R] [Field k] [Field K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (q : R →+* k) (hq : Function.Surjective q)
    (j : R →+* K) (hj : Function.Injective j)
    (E A B : Matrix n n R) (hE : E * E = E)
    (hsame : (A.map q).rank = (B.map q).rank)
    (hhalf : (E.map q).rank ≤ 2 * (A.map q).rank)
    (hfit : (A.map j).rank + (B.map j).rank ≤ (E.map j).rank) :
    (A.map j).rank = (B.map j).rank := by
  have hErank := rank_idempotent_map_eq q hq j hj E hE
  have hAle := rank_map_le_rank_map q hq j hj A
  have hBle := rank_map_le_rank_map q hq j hj B
  omega

private theorem rank_involution_sectors_add
    {K : Type u} [Field K] [CharZero K]
    {n : Type v} [Fintype n] [DecidableEq n]
    (E P : Matrix n n K)
    (hE : E * E = E) (hP : P * P = 1)
    (hEP : E * P = P * E) :
    E.rank = (E * (P - 1)).rank + (E * (P + 1)).rank := by
  let A : Matrix n n K := E * (P - 1)
  let B : Matrix n n K := E * (P + 1)
  have hminus_comm : (P - 1) * E = E * (P - 1) := by
    calc
      (P - 1) * E = P * E - E := by noncomm_ring
      _ = E * P - E := by rw [← hEP]
      _ = E * (P - 1) := by noncomm_ring
  have hplus_comm : (P + 1) * E = E * (P + 1) := by
    calc
      (P + 1) * E = P * E + E := by noncomm_ring
      _ = E * P + E := by rw [← hEP]
      _ = E * (P + 1) := by noncomm_ring
  have hminus_sq : (P - 1) * (P - 1) =
      -((P - 1) + (P - 1)) := by
    calc
      (P - 1) * (P - 1) = P * P - P - P + 1 := by noncomm_ring
      _ = 1 - P - P + 1 := by rw [hP]
      _ = -((P - 1) + (P - 1)) := by noncomm_ring
  have hplus_sq : (P + 1) * (P + 1) =
      (P + 1) + (P + 1) := by
    calc
      (P + 1) * (P + 1) = P * P + P + P + 1 := by noncomm_ring
      _ = 1 + P + P + 1 := by rw [hP]
      _ = (P + 1) + (P + 1) := by abel
  have hA0 : A * A = -(A + A) := by
    calc
      A * A = E * ((P - 1) * E) * (P - 1) := by
        simp only [A, mul_assoc]
      _ = E * (E * (P - 1)) * (P - 1) := by rw [hminus_comm]
      _ = (E * E) * ((P - 1) * (P - 1)) := by
        simp only [mul_assoc]
      _ = E * ((P - 1) * (P - 1)) := by rw [hE]
      _ = E * (-((P - 1) + (P - 1))) := by rw [hminus_sq]
      _ = -(A + A) := by simp only [A]; noncomm_ring
  have hB0 : B * B = B + B := by
    calc
      B * B = E * ((P + 1) * E) * (P + 1) := by
        simp only [B, mul_assoc]
      _ = E * (E * (P + 1)) * (P + 1) := by rw [hplus_comm]
      _ = (E * E) * ((P + 1) * (P + 1)) := by
        simp only [mul_assoc]
      _ = E * ((P + 1) * (P + 1)) := by rw [hE]
      _ = E * ((P + 1) + (P + 1)) := by rw [hplus_sq]
      _ = B + B := by simp only [B]; noncomm_ring
  have hA : A * A = (-2 : K) • A := by
    rw [hA0]
    ext i l
    simp
    ring
  have hB : B * B = (2 : K) • B := by
    rw [hB0]
    ext i l
    simp
    ring
  have hminus_plus : (P - 1) * (P + 1) = 0 := by
    calc
      (P - 1) * (P + 1) = P * P - 1 := by noncomm_ring
      _ = 0 := by rw [hP]; abel
  have hplus_minus : (P + 1) * (P - 1) = 0 := by
    calc
      (P + 1) * (P - 1) = P * P - 1 := by noncomm_ring
      _ = 0 := by rw [hP]; abel
  have hAB : A * B = 0 := by
    calc
      A * B = E * ((P - 1) * E) * (P + 1) := by
        simp only [A, B, mul_assoc]
      _ = (E * E) * ((P - 1) * (P + 1)) := by
        rw [hminus_comm]
        simp only [mul_assoc]
      _ = 0 := by rw [hE, hminus_plus, mul_zero]
  have hBA : B * A = 0 := by
    calc
      B * A = E * ((P + 1) * E) * (P - 1) := by
        simp only [A, B, mul_assoc]
      _ = (E * E) * ((P + 1) * (P - 1)) := by
        rw [hplus_comm]
        simp only [mul_assoc]
      _ = 0 := by rw [hE, hplus_minus, mul_zero]
  have hAexpand : A = E * P - E := by
    simp only [A]
    noncomm_ring
  have hBexpand : B = E * P + E := by
    simp only [B]
    noncomm_ring
  have hsum : (-2 : K)⁻¹ • A + (2 : K)⁻¹ • B = E := by
    rw [hAexpand, hBexpand]
    ext i l
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
    field_simp
    ring
  simpa only [A, B] using rank_eq_add_of_scaled_orthogonal
    E A B (-2 : K) (2 : K) (by norm_num) (by norm_num)
      hA hB hAB hBA hsum

private theorem rank_involution_sectors_eq_of_modular_half
    {R : Type u} {k : Type v} {K : Type w}
    [CommRing R] [Field k] [CharP k 2] [Field K] [CharZero K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (q : R →+* k) (hq : Function.Surjective q)
    (j : R →+* K) (hj : Function.Injective j)
    (E P : Matrix n n R)
    (hE : E * E = E) (hP : P * P = 1)
    (hEP : E * P = P * E)
    (hhalf : (E.map q).rank ≤
      2 * ((E * (P - 1)).map q).rank) :
    ((E * (P - 1)).map j).rank =
      ((E * (P + 1)).map j).rank := by
  have hmap_one_q : (1 : Matrix n n R).map q = (1 : Matrix n n k) := by
    ext i l
    by_cases h : i = l
    · subst l
      simp
    · simp [h]
  have hmap_one_j : (1 : Matrix n n R).map j = (1 : Matrix n n K) := by
    ext i l
    by_cases h : i = l
    · subst l
      simp
    · simp [h]
  have hminus_q : (E * (P - 1)).map q =
      E.map q * (P.map q - 1) := by
    rw [Matrix.map_mul]
    congr 1
    ext i l
    change q (P i l - (1 : Matrix n n R) i l) =
      P.map q i l - (1 : Matrix n n k) i l
    rw [map_sub]
    exact congrArg (fun z ↦ P.map q i l - z)
      (congrFun (congrFun hmap_one_q i) l)
  have hplus_q : (E * (P + 1)).map q =
      E.map q * (P.map q + 1) := by
    rw [Matrix.map_mul]
    congr 1
    ext i l
    change q (P i l + (1 : Matrix n n R) i l) =
      P.map q i l + (1 : Matrix n n k) i l
    rw [map_add]
    exact congrArg (fun z ↦ P.map q i l + z)
      (congrFun (congrFun hmap_one_q i) l)
  have hsame : ((E * (P - 1)).map q).rank =
      ((E * (P + 1)).map q).rank := by
    have hsign : P.map q - 1 = P.map q + 1 := by
      ext i l
      exact CharTwo.sub_eq_add _ _
    rw [hminus_q, hplus_q, hsign]
  have hminus_j : (E * (P - 1)).map j =
      E.map j * (P.map j - 1) := by
    rw [Matrix.map_mul]
    congr 1
    ext i l
    change j (P i l - (1 : Matrix n n R) i l) =
      P.map j i l - (1 : Matrix n n K) i l
    rw [map_sub]
    exact congrArg (fun z ↦ P.map j i l - z)
      (congrFun (congrFun hmap_one_j i) l)
  have hplus_j : (E * (P + 1)).map j =
      E.map j * (P.map j + 1) := by
    rw [Matrix.map_mul]
    congr 1
    ext i l
    change j (P i l + (1 : Matrix n n R) i l) =
      P.map j i l + (1 : Matrix n n K) i l
    rw [map_add]
    exact congrArg (fun z ↦ P.map j i l + z)
      (congrFun (congrFun hmap_one_j i) l)
  have hEj : E.map j * E.map j = E.map j := by
    simpa only [Matrix.map_mul] using congrArg (fun M ↦ M.map j) hE
  have hPj : P.map j * P.map j = 1 := by
    have hpmap := congrArg (fun M ↦ M.map j) hP
    simpa only [Matrix.map_mul, hmap_one_j] using hpmap
  have hEPj : E.map j * P.map j = P.map j * E.map j := by
    simpa only [Matrix.map_mul] using congrArg (fun M ↦ M.map j) hEP
  have hsum := rank_involution_sectors_add
    (E.map j) (P.map j) hEj hPj hEPj
  rw [← hminus_j, ← hplus_j] at hsum
  apply ranks_eq_of_modular_half_rank q hq j hj
    E (E * (P - 1)) (E * (P + 1)) hE hsame hhalf
  exact le_of_eq hsum.symm

private theorem trace_eq_rank_of_idempotent
    {K : Type u} [Field K] [CharZero K]
    {n : Type v} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (hA : A * A = A) :
    A.trace = (A.rank : K) := by
  let f : (n → K) →ₗ[K] (n → K) := Matrix.toLin' A
  have hf : IsIdempotentElem f := by
    rw [isIdempotentElem_iff]
    change f ∘ₗ f = f
    simpa only [f, ← Matrix.toLin'_mul] using congrArg Matrix.toLin' hA
  calc
    A.trace = (LinearMap.trace K (n → K)) f :=
      (Matrix.trace_toLin'_eq A).symm
    _ = (Module.finrank K f.range : K) :=
      (LinearMap.IsIdempotentElem.isProj_range f hf).trace
    _ = (A.rank : K) := by rw [rank_eq_finrank_range_toLin' A]

private theorem trace_eq_mul_rank_of_scaled_idempotent
    {K : Type u} [Field K] [CharZero K]
    {n : Type v} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (c : K) (hc : c ≠ 0)
    (hA : A * A = c • A) :
    A.trace = c * (A.rank : K) := by
  have hAi : (c⁻¹ • A) * (c⁻¹ • A) = c⁻¹ • A := by
    calc
      (c⁻¹ • A) * (c⁻¹ • A) = (c⁻¹ * c⁻¹) • (A * A) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = (c⁻¹ * c⁻¹) • (c • A) := by rw [hA]
      _ = c⁻¹ • A := by simp [smul_smul, hc]
  have hrank : (c⁻¹ • A).rank = A.rank :=
    Matrix.rank_smul_of_mem_nonZeroDivisors A (by simp [hc])
  calc
    A.trace = c * (c⁻¹ • A).trace := by
      rw [Matrix.trace_smul]
      simp [smul_eq_mul, hc]
    _ = c * ((c⁻¹ • A).rank : K) := by
      rw [trace_eq_rank_of_idempotent _ hAi]
    _ = c * (A.rank : K) := by rw [hrank]

private theorem involution_minus_sector_sq
    {K : Type u} [Field K] [CharZero K]
    {n : Type v} [Fintype n] [DecidableEq n]
    (E P : Matrix n n K)
    (hE : E * E = E) (hP : P * P = 1)
    (hEP : E * P = P * E) :
    (E * (P - 1)) * (E * (P - 1)) =
      (-2 : K) • (E * (P - 1)) := by
  have hcomm : (P - 1) * E = E * (P - 1) := by
    calc
      (P - 1) * E = P * E - E := by noncomm_ring
      _ = E * P - E := by rw [← hEP]
      _ = E * (P - 1) := by noncomm_ring
  have hsquare : (P - 1) * (P - 1) =
      -((P - 1) + (P - 1)) := by
    calc
      (P - 1) * (P - 1) = P * P - P - P + 1 := by noncomm_ring
      _ = 1 - P - P + 1 := by rw [hP]
      _ = -((P - 1) + (P - 1)) := by noncomm_ring
  have hraw : (E * (P - 1)) * (E * (P - 1)) =
      -((E * (P - 1)) + (E * (P - 1))) := by
    calc
      (E * (P - 1)) * (E * (P - 1)) =
          E * ((P - 1) * E) * (P - 1) := by simp only [mul_assoc]
      _ = E * (E * (P - 1)) * (P - 1) := by rw [hcomm]
      _ = (E * E) * ((P - 1) * (P - 1)) := by simp only [mul_assoc]
      _ = E * ((P - 1) * (P - 1)) := by rw [hE]
      _ = E * (-((P - 1) + (P - 1))) := by rw [hsquare]
      _ = -((E * (P - 1)) + (E * (P - 1))) := by noncomm_ring
  rw [hraw]
  ext i l
  simp
  ring

private theorem involution_plus_sector_sq
    {K : Type u} [Field K] [CharZero K]
    {n : Type v} [Fintype n] [DecidableEq n]
    (E P : Matrix n n K)
    (hE : E * E = E) (hP : P * P = 1)
    (hEP : E * P = P * E) :
    (E * (P + 1)) * (E * (P + 1)) =
      (2 : K) • (E * (P + 1)) := by
  have hcomm : (P + 1) * E = E * (P + 1) := by
    calc
      (P + 1) * E = P * E + E := by noncomm_ring
      _ = E * P + E := by rw [← hEP]
      _ = E * (P + 1) := by noncomm_ring
  have hsquare : (P + 1) * (P + 1) =
      (P + 1) + (P + 1) := by
    calc
      (P + 1) * (P + 1) = P * P + P + P + 1 := by noncomm_ring
      _ = 1 + P + P + 1 := by rw [hP]
      _ = (P + 1) + (P + 1) := by abel
  have hraw : (E * (P + 1)) * (E * (P + 1)) =
      (E * (P + 1)) + (E * (P + 1)) := by
    calc
      (E * (P + 1)) * (E * (P + 1)) =
          E * ((P + 1) * E) * (P + 1) := by simp only [mul_assoc]
      _ = E * (E * (P + 1)) * (P + 1) := by rw [hcomm]
      _ = (E * E) * ((P + 1) * (P + 1)) := by simp only [mul_assoc]
      _ = E * ((P + 1) * (P + 1)) := by rw [hE]
      _ = E * ((P + 1) + (P + 1)) := by rw [hsquare]
      _ = (E * (P + 1)) + (E * (P + 1)) := by noncomm_ring
  rw [hraw]
  ext i l
  simp
  ring

private theorem trace_mul_eq_zero_of_involution_sector_ranks_eq
    {K : Type u} [Field K] [CharZero K]
    {n : Type v} [Fintype n] [DecidableEq n]
    (E P : Matrix n n K)
    (hE : E * E = E) (hP : P * P = 1)
    (hEP : E * P = P * E)
    (hrank : (E * (P - 1)).rank = (E * (P + 1)).rank) :
    (E * P).trace = 0 := by
  let A : Matrix n n K := E * (P - 1)
  let B : Matrix n n K := E * (P + 1)
  have hA : A * A = (-2 : K) • A := by
    simpa only [A] using involution_minus_sector_sq E P hE hP hEP
  have hB : B * B = (2 : K) • B := by
    simpa only [B] using involution_plus_sector_sq E P hE hP hEP
  have htA : A.trace = (-2 : K) * (A.rank : K) :=
    trace_eq_mul_rank_of_scaled_idempotent A (-2 : K) (by norm_num) hA
  have htB : B.trace = (2 : K) * (B.rank : K) :=
    trace_eq_mul_rank_of_scaled_idempotent B (2 : K) (by norm_num) hB
  have htrace : (A + B).trace = 0 := by
    rw [Matrix.trace_add, htA, htB]
    have hrank' : A.rank = B.rank := by simpa only [A, B] using hrank
    rw [hrank']
    ring
  have hsum : A + B = (2 : K) • (E * P) := by
    simp only [A, B]
    ext i l
    simp only [Matrix.add_apply, Matrix.smul_apply]
    change (E * (P - 1)) i l + (E * (P + 1)) i l =
      2 * (E * P) i l
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply,
      Finset.mul_sum, mul_sub, mul_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have htwo_trace : (2 : K) * (E * P).trace = 0 := by
    calc
      (2 : K) * (E * P).trace = ((2 : K) • (E * P)).trace := by
        rw [Matrix.trace_smul]
        rfl
      _ = (A + B).trace := congrArg Matrix.trace hsum.symm
      _ = 0 := htrace
  exact (mul_eq_zero.mp htwo_trace).resolve_left (by norm_num)

private theorem trace_involution_projector_eq_zero_of_modular_half
    {R : Type u} {k : Type v} {K : Type w}
    [CommRing R] [Field k] [CharP k 2] [Field K] [CharZero K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (q : R →+* k) (hq : Function.Surjective q)
    (j : R →+* K) (hj : Function.Injective j)
    (E P : Matrix n n R)
    (hE : E * E = E) (hP : P * P = 1)
    (hEP : E * P = P * E)
    (hhalf : (E.map q).rank ≤
      2 * ((E * (P - 1)).map q).rank) :
    (E.map j * P.map j).trace = 0 := by
  have hrank := rank_involution_sectors_eq_of_modular_half
    q hq j hj E P hE hP hEP hhalf
  have hmap_one_j : (1 : Matrix n n R).map j = (1 : Matrix n n K) := by
    ext i l
    by_cases h : i = l
    · subst l
      simp
    · simp [h]
  have hminus_j : (E * (P - 1)).map j =
      E.map j * (P.map j - 1) := by
    rw [Matrix.map_mul]
    congr 1
    ext i l
    change j (P i l - (1 : Matrix n n R) i l) =
      P.map j i l - (1 : Matrix n n K) i l
    rw [map_sub]
    exact congrArg (fun z ↦ P.map j i l - z)
      (congrFun (congrFun hmap_one_j i) l)
  have hplus_j : (E * (P + 1)).map j =
      E.map j * (P.map j + 1) := by
    rw [Matrix.map_mul]
    congr 1
    ext i l
    change j (P i l + (1 : Matrix n n R) i l) =
      P.map j i l + (1 : Matrix n n K) i l
    rw [map_add]
    exact congrArg (fun z ↦ P.map j i l + z)
      (congrFun (congrFun hmap_one_j i) l)
  have hEj : E.map j * E.map j = E.map j := by
    simpa only [Matrix.map_mul] using congrArg (fun M ↦ M.map j) hE
  have hPj : P.map j * P.map j = 1 := by
    have hpmap := congrArg (fun M ↦ M.map j) hP
    simpa only [Matrix.map_mul, hmap_one_j] using hpmap
  have hEPj : E.map j * P.map j = P.map j * E.map j := by
    simpa only [Matrix.map_mul] using congrArg (fun M ↦ M.map j) hEP
  have hrank' : (E.map j * (P.map j - 1)).rank =
      (E.map j * (P.map j + 1)).rank := by
    rw [← hminus_j, ← hplus_j]
    exact hrank
  exact trace_mul_eq_zero_of_involution_sector_ranks_eq
    (E.map j) (P.map j) hEj hPj hEPj hrank'

private theorem finrank_le_two_mul_finrank_range_of_exact_on_subspace
    {k : Type u} [Field k]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : Submodule k V) (d : V →ₗ[k] V)
    (hexact : d.ker ⊓ F ≤ d.range) :
    Module.finrank k F ≤ 2 * Module.finrank k d.range := by
  let dr : F →ₗ[k] V := d.domRestrict F
  have hrange_le : dr.range ≤ d.range := by
    intro x hx
    rw [LinearMap.mem_range] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨(y : V), rfl⟩
  have hrange : Module.finrank k dr.range ≤ Module.finrank k d.range :=
    Submodule.finrank_mono hrange_le
  let kerToRange : dr.ker →ₗ[k] d.range :=
    { toFun := fun x ↦ ⟨x.1.1, by
        apply hexact
        constructor
        · exact x.property
        · exact x.1.property⟩
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl }
  have hkerinj : Function.Injective kerToRange := by
    intro x y hxy
    have hv : (x.1.1 : V) = y.1.1 :=
      congrArg (fun z : d.range ↦ (z : V)) hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hv
  have hker : Module.finrank k dr.ker ≤ Module.finrank k d.range :=
    LinearMap.finrank_le_finrank_of_injective hkerinj
  have hranknull := LinearMap.finrank_range_add_finrank_ker dr
  omega

private theorem rank_projector_le_two_minus_sector_of_exact
    {k : Type u} [Field k]
    {n : Type v} [Fintype n] [DecidableEq n]
    (E P : Matrix n n k)
    (hE : E * E = E) (hEP : E * P = P * E)
    (hexact :
      (Matrix.toLin' (P - 1)).ker ⊓ (Matrix.toLin' E).range ≤
        (Matrix.toLin' (P - 1)).range) :
    E.rank ≤ 2 * (E * (P - 1)).rank := by
  let e : (n → k) →ₗ[k] (n → k) := Matrix.toLin' E
  let s : (n → k) →ₗ[k] (n → k) := Matrix.toLin' (P - 1)
  let d : (n → k) →ₗ[k] (n → k) := Matrix.toLin' (E * (P - 1))
  have he : IsIdempotentElem e := by
    rw [isIdempotentElem_iff]
    change e ∘ₗ e = e
    simpa only [e, ← Matrix.toLin'_mul] using congrArg Matrix.toLin' hE
  have hcomm_matrix : E * (P - 1) = (P - 1) * E := by
    calc
      E * (P - 1) = E * P - E := by noncomm_ring
      _ = P * E - E := by rw [hEP]
      _ = (P - 1) * E := by noncomm_ring
  have hd : d = e ∘ₗ s := by
    simp only [d, e, s, Matrix.toLin'_mul]
  have hcomm : e ∘ₗ s = s ∘ₗ e := by
    simpa only [e, s, ← Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hcomm_matrix
  have hdexact : d.ker ⊓ e.range ≤ d.range := by
    intro x hx
    have hxker : d x = 0 := hx.1
    have hxrange : x ∈ e.range := hx.2
    have hefix : e x = x :=
      (LinearMap.IsIdempotentElem.mem_range_iff he).mp hxrange
    have hdx : d x = s x := by
      calc
        d x = e (s x) := LinearMap.congr_fun hd x
        _ = s (e x) := LinearMap.congr_fun hcomm x
        _ = s x := by rw [hefix]
    have hsx : s x = 0 := by rw [← hdx]; exact hxker
    have hsrange : x ∈ s.range := by
      apply hexact
      exact ⟨hsx, hxrange⟩
    rw [LinearMap.mem_range] at hsrange ⊢
    obtain ⟨y, hy⟩ := hsrange
    refine ⟨y, ?_⟩
    calc
      d y = e (s y) := LinearMap.congr_fun hd y
      _ = e x := by rw [hy]
      _ = x := hefix
  have hdim := finrank_le_two_mul_finrank_range_of_exact_on_subspace
    e.range d hdexact
  dsimp only [e, d] at hdim
  rw [← rank_eq_finrank_range_toLin' E,
    ← rank_eq_finrank_range_toLin' (E * (P - 1))] at hdim
  exact hdim

private theorem trace_involution_projector_eq_zero_of_modular_exact
    {R : Type u} {k : Type v} {K : Type w}
    [CommRing R] [Field k] [CharP k 2] [Field K] [CharZero K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (q : R →+* k) (hq : Function.Surjective q)
    (j : R →+* K) (hj : Function.Injective j)
    (E P : Matrix n n R)
    (hE : E * E = E) (hP : P * P = 1)
    (hEP : E * P = P * E)
    (hexact :
      (Matrix.toLin' (P.map q - 1)).ker ⊓
          (Matrix.toLin' (E.map q)).range ≤
        (Matrix.toLin' (P.map q - 1)).range) :
    (E.map j * P.map j).trace = 0 := by
  have hmap_one_q : (1 : Matrix n n R).map q = (1 : Matrix n n k) := by
    ext i l
    by_cases h : i = l
    · subst l
      simp
    · simp [h]
  have hminus_q : (E * (P - 1)).map q =
      E.map q * (P.map q - 1) := by
    rw [Matrix.map_mul]
    congr 1
    ext i l
    change q (P i l - (1 : Matrix n n R) i l) =
      P.map q i l - (1 : Matrix n n k) i l
    rw [map_sub]
    exact congrArg (fun z ↦ P.map q i l - z)
      (congrFun (congrFun hmap_one_q i) l)
  have hEq : E.map q * E.map q = E.map q := by
    simpa only [Matrix.map_mul] using congrArg (fun M ↦ M.map q) hE
  have hEPq : E.map q * P.map q = P.map q * E.map q := by
    simpa only [Matrix.map_mul] using congrArg (fun M ↦ M.map q) hEP
  have hhalf' := rank_projector_le_two_minus_sector_of_exact
    (E.map q) (P.map q) hEq hEPq hexact
  have hhalf : (E.map q).rank ≤
      2 * ((E * (P - 1)).map q).rank := by
    rw [hminus_q]
    exact hhalf'
  exact trace_involution_projector_eq_zero_of_modular_half
    q hq j hj E P hE hP hEP hhalf

theorem trace_mul_eq_trace_of_exact_projector_decomposition
    {R : Type u} {k : Type v} {K : Type w}
    [CommRing R] [Field k] [CharP k 2] [Field K] [CharZero K]
    {n : Type*} [Fintype n] [DecidableEq n]
    {I : Type*} [Fintype I]
    (q : R →+* k) (hq : Function.Surjective q)
    (j : R →+* K) (hj : Function.Injective j)
    (P Q : Matrix n n R) (E : I → Matrix n n R) (c : I → K)
    (hP : P * P = 1)
    (hE : ∀ i, E i * E i = E i)
    (hEP : ∀ i, E i * P = P * E i)
    (hexact : ∀ i,
      (Matrix.toLin' (P.map q - 1)).ker ⊓
          (Matrix.toLin' ((E i).map q)).range ≤
        (Matrix.toLin' (P.map q - 1)).range)
    (hdecomp : P.map j * (Q.map j - 1) =
      ∑ i, c i • ((E i).map j * P.map j)) :
    (P.map j * Q.map j).trace = (P.map j).trace := by
  have hsector (i : I) : ((E i).map j * P.map j).trace = 0 :=
    trace_involution_projector_eq_zero_of_modular_exact
      q hq j hj (E i) P (hE i) hP (hEP i) (hexact i)
  have hsumtrace :
      (∑ i, c i • ((E i).map j * P.map j)).trace = 0 := by
    rw [Matrix.trace_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Matrix.trace_smul, hsector i]
    simp
  have hzero : (P.map j * (Q.map j - 1)).trace = 0 := by
    rw [hdecomp]
    exact hsumtrace
  have hdiff : P.map j * Q.map j - P.map j =
      P.map j * (Q.map j - 1) := by noncomm_ring
  apply sub_eq_zero.mp
  rw [← Matrix.trace_sub, hdiff]
  exact hzero

end

end ZStar.IntegralTraceBridge

end CFSG
