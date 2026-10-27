module

public import CFSG.LocalAnalysis.StandardType.GGA11FrameDefs
public import CFSG.LocalAnalysis.StandardType.GGA11GraphAut
public import CFSG.LocalAnalysis.StandardType.GGA8NbrGlue
public import CFSG.LocalAnalysis.StandardType.GGA8NbrPlumb
public import CFSG.LocalAnalysis.StandardType.GGA8NbrTorusNorm
public import Certificates.Certificate476001

public section

set_option synthInstance.maxSize 512

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.A8Coord CFSG.StandardType.A11
  CFSG.StandardType.A8NbrInf Matrix
open Certificates.A8Nbr476

namespace CFSG.StandardType.A11
private lemma a11ge_zmod_smul_eq_nsmul (c : ZMod 7) (v : Fin 4 → ZMod 7) :
    c • v = c.val • v := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 7), ZMod.natCast_zmod_val]

private lemma a11ge_two_ne_zero : (2 : ZMod 7) ≠ 0 := by decide

private lemma a11ge_single_vecMul (A : M4) (i : Fin 4) :
    vecMul (Pi.single i 1) A = A i := by
  funext j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ]

private lemma a11ge_matrix_eq_of_rows {A B : M4}
    (h : ∀ i, vecMul (Pi.single i (1 : ZMod 7)) A =
      vecMul (Pi.single i (1 : ZMod 7)) B) : A = B := by
  ext i j
  have hh := congrFun (h i) j
  simpa [Matrix.vecMul, dotProduct, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ] using hh

private lemma a11ge_vecMul_a8Dscal (a u : ZMod 7) (hu : u ≠ 0) :
    vecMul ![a, u, u, u] (a8Dscal u⁻¹) = ![a, 1, 1, 1] := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  funext j
  fin_cases j <;> simp [a8Dscal, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.diagonal]
  all_goals exact mul_inv_cancel₀ hu

private lemma a11ge_det_ne_zero_of_mul_eq_one {A B : M4} (h : A * B = 1) : A.det ≠ 0 := by
  intro h0
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at hd
  exact (by decide : (0 : ZMod 7) ≠ 1) hd

private lemma a11ge_mul_comm_of_mul_eq_one {A B : M4} (h : A * B = 1) : B * A = 1 := by
  have hdet : Invertible A.det := Matrix.detInvertibleOfRightInverse (A := A) (B := B) h
  letI : Invertible A := Matrix.invertibleOfDetInvertible (A := A)
  rw [← Matrix.inv_eq_right_inv h, Matrix.inv_mul_of_invertible]

private def a11ge_matAddEquiv (m m' : M4) (hm : m * m' = 1) :
    (Fin 4 → ZMod 7) ≃+ (Fin 4 → ZMod 7) where
  toFun v := vecMul v m
  invFun v := vecMul v m'
  left_inv v := by
    change vecMul (vecMul v m) m' = v
    rw [Matrix.vecMul_vecMul, hm, Matrix.vecMul_one]
  right_inv v := by
    have hm' : m' * m = 1 := a11ge_mul_comm_of_mul_eq_one hm
    change vecMul (vecMul v m') m = v
    rw [Matrix.vecMul_vecMul, hm', Matrix.vecMul_one]
  map_add' v w := by
    change vecMul (v + w) m = vecMul v m + vecMul w m
    rw [Matrix.add_vecMul]

private noncomputable def a11ge_matAut {G : Type} [Group G] {Bs : Subgroup G}
    (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)) (m m' : M4) (hm : m * m' = 1) : MulAut ↥Bs :=
  Additive.toMul (AddAutAdditive ↥Bs (ι.trans ((a11ge_matAddEquiv m m' hm).trans ι.symm)))

private lemma a11ge_addAutAdditive_apply {G : Type} [Group G] {Bs : Subgroup G}
    (A : Additive ↥Bs ≃+ Additive ↥Bs) (b : ↥Bs) :
    Additive.toMul (AddAutAdditive ↥Bs A) b = Additive.toMul (A (Additive.ofMul b)) := by
  rw [← AddAutAdditive_apply_apply]
  rfl

private lemma a11ge_matAut_apply {G : Type} [Group G] {Bs : Subgroup G}
    (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)) (m m' : M4) (hm : m * m' = 1) (b : ↥Bs) :
    ι (Additive.ofMul (a11ge_matAut ι m m' hm b)) = vecMul (ι (Additive.ofMul b)) m := by
  rw [a11ge_matAut, a11ge_addAutAdditive_apply]
  simp [a11ge_matAddEquiv]

private lemma a11ge_decomp {G : Type} [Group G] {Bs : Subgroup G}
    (e f : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)) :
    ∀ b : Additive ↥Bs, f b =
      vecMul (e b) (Matrix.of fun i j => f (e.symm (Pi.single i 1)) j) := by
  letI : AddCommMonoid (Additive ↥Bs) :=
    { (inferInstance : AddMonoid (Additive ↥Bs)) with
      add_comm := fun x y => e.injective (by rw [map_add, map_add, add_comm]) }
  intro b
  let v : Fin 4 → ZMod 7 := e b
  let P : M4 := Matrix.of fun i j => f (e.symm (Pi.single i 1)) j
  have hb : b = ∑ i : Fin 4, (v i).val • e.symm (Pi.single i (1 : ZMod 7)) := by
    apply e.injective
    rw [map_sum]
    simp only [map_nsmul, AddEquiv.apply_symm_apply]
    change v = ∑ i : Fin 4, (v i).val • (Pi.single i (1 : ZMod 7) : Fin 4 → ZMod 7)
    trans ∑ i : Fin 4, (v i) • (Pi.single i (1 : ZMod 7) : Fin 4 → ZMod 7)
    · exact (by
        funext j
        simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ])
    · apply Finset.sum_congr rfl
      intro i _
      rw [a11ge_zmod_smul_eq_nsmul]
  calc f b = f (∑ i : Fin 4, (v i).val • e.symm (Pi.single i (1 : ZMod 7))) := by rw [hb]
    _ = ∑ i : Fin 4, (v i).val • f (e.symm (Pi.single i (1 : ZMod 7))) := by
        rw [map_sum]
        simp only [map_nsmul]
    _ = ∑ i : Fin 4, (v i) • f (e.symm (Pi.single i (1 : ZMod 7))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [a11ge_zmod_smul_eq_nsmul]
    _ = vecMul v P := by
        funext j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, P, Matrix.vecMul, dotProduct,
          Matrix.of_apply]

private lemma a11ge_exists_frame {G : Type} [Group G] {Bs : Subgroup G}
    (ιK ιL : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)) :
    ∃ P Q : M4, (∀ b, ιL b = vecMul (ιK b) P) ∧ P * Q = 1 ∧ Q * P = 1 := by
  let P : M4 := Matrix.of fun i j => ιL (ιK.symm (Pi.single i 1)) j
  let Q : M4 := Matrix.of fun i j => ιK (ιL.symm (Pi.single i 1)) j
  have hP : ∀ b, ιL b = vecMul (ιK b) P := a11ge_decomp ιK ιL
  have hQ : ∀ b, ιK b = vecMul (ιL b) Q := a11ge_decomp ιL ιK
  have hPQ : P * Q = 1 := by
    apply a11ge_matrix_eq_of_rows
    intro i
    rw [← Matrix.vecMul_vecMul, a11ge_single_vecMul]
    let b : Additive ↥Bs := ιK.symm (Pi.single i 1)
    have hPb : P i = ιL b := by
      rw [← a11ge_single_vecMul P i, hP b, AddEquiv.apply_symm_apply]
    have hQb : vecMul (ιL b) Q = ιK b := (hQ b).symm
    rw [hPb, hQb, AddEquiv.apply_symm_apply, Matrix.vecMul_one]
  have hQP : Q * P = 1 := by
    apply a11ge_matrix_eq_of_rows
    intro i
    rw [← Matrix.vecMul_vecMul, a11ge_single_vecMul]
    let b : Additive ↥Bs := ιL.symm (Pi.single i 1)
    have hQb : Q i = ιK b := by
      rw [← a11ge_single_vecMul Q i, hQ b, AddEquiv.apply_symm_apply]
    have hPb : vecMul (ιK b) P = ιL b := (hP b).symm
    rw [hQb, hPb, AddEquiv.apply_symm_apply, Matrix.vecMul_one]
  exact ⟨P, Q, hP, hPQ, hQP⟩

private lemma a11ge_old_of_new {G : Type} [Group G] {Bs : Subgroup G}
    {ι ιK : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)} {T T' : M4}
    (hTT' : T * T' = 1) (hι : ∀ b, ι b = vecMul (ιK b) T) (b : Additive ↥Bs) :
    ιK b = vecMul (ι b) T' := by
  rw [hι b, Matrix.vecMul_vecMul, hTT', Matrix.vecMul_one]

private lemma a11ge_matAut_mem_of_frame {G : Type} [Group G] {Bs K : Subgroup G}
    {ιK : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)}
    (hK : ∀ φ : MulAut ↥Bs, φ ∈ ggAutomizer K Bs ↔
      ∃ (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3), ∀ b : ↥Bs,
        ιK (Additive.ofMul (φ b)) = vecMul (ιK (Additive.ofMul b)) (a8MonK π k))
    {ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)} {T T' : M4} (hTT' : T * T' = 1)
    (hι : ∀ b, ι b = vecMul (ιK b) T)
    {m m' : M4} (hm : m * m' = 1) (hmK : ∃ π k, T * m * T' = a8MonK π k) :
    a11ge_matAut ι m m' hm ∈ ggAutomizer K Bs := by
  rw [hK]
  obtain ⟨π, k, hπk⟩ := hmK
  refine ⟨π, k, fun b => ?_⟩
  calc ιK (Additive.ofMul (a11ge_matAut ι m m' hm b))
      = vecMul (ι (Additive.ofMul (a11ge_matAut ι m m' hm b))) T' :=
        a11ge_old_of_new hTT' hι (Additive.ofMul (a11ge_matAut ι m m' hm b))
    _ = vecMul (vecMul (ι (Additive.ofMul b)) m) T' := by rw [a11ge_matAut_apply]
    _ = vecMul (ι (Additive.ofMul b)) (m * T') := by rw [Matrix.vecMul_vecMul]
    _ = vecMul (vecMul (ιK (Additive.ofMul b)) T) (m * T') := by rw [← hι]
    _ = vecMul (ιK (Additive.ofMul b)) (T * m * T') := by
        rw [Matrix.vecMul_vecMul]
        simp only [mul_assoc]
    _ = vecMul (ιK (Additive.ofMul b)) (a8MonK π k) := by rw [hπk]

private lemma a11ge_rel_of_aut {G : Type} [Group G] {Bs : Subgroup G}
    {ιK ιL : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)} {P : M4}
    (hP : ∀ b, ιL b = vecMul (ιK b) P)
    {ψ : MulAut ↥Bs} {g : M4}
    (hg : ∀ b : ↥Bs, ιK (Additive.ofMul (ψ b)) = vecMul (ιK (Additive.ofMul b)) g)
    {S : M4} (hS : ∀ b : ↥Bs, ιL (Additive.ofMul (ψ b)) = vecMul (ιL (Additive.ofMul b)) S) :
    g * P = P * S := by
  apply a11ge_matrix_eq_of_rows
  intro j
  let b : Additive ↥Bs := ιK.symm (Pi.single j 1)
  have hb : ιK b = Pi.single j 1 := AddEquiv.apply_symm_apply ιK _
  have hL : vecMul (Pi.single j 1) (g * P) = ιL (Additive.ofMul (ψ (Additive.toMul b))) := by
    rw [← Matrix.vecMul_vecMul, ← hb]
    change vecMul (vecMul (ιK (Additive.ofMul (Additive.toMul b))) g) P = _
    rw [← hg (Additive.toMul b), ← hP (Additive.ofMul (ψ (Additive.toMul b)))]
  have hR : vecMul (Pi.single j 1) (P * S) = ιL (Additive.ofMul (ψ (Additive.toMul b))) := by
    rw [← Matrix.vecMul_vecMul, ← hb]
    change vecMul (vecMul (ιK b) P) S = _
    rw [← hP b]
    exact (hS (Additive.toMul b)).symm
  rw [hL, hR]

private lemma a11ge_fix_of_aut {G : Type} [Group G] {Bs : Subgroup G}
    {ιK : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)}
    {ψ : MulAut ↥Bs} {g : M4} {xb : ↥Bs}
    (hg : ∀ b : ↥Bs, ιK (Additive.ofMul (ψ b)) = vecMul (ιK (Additive.ofMul b)) g)
    (hfix : ψ xb = xb) : vecMul (ιK (Additive.ofMul xb)) g = ιK (Additive.ofMul xb) := by
  rw [← hg xb, hfix]

private lemma a11ge_sq_eq_one {g P Q S : M4} (hPQ : P * Q = 1) (hrel : g * P = P * S)
    (hS : S * S = 1) : g * g = 1 := by
  calc g * g = (g * g) * (P * Q) := by rw [hPQ, mul_one]
    _ = ((g * g) * P) * Q := by simp only [mul_assoc]
    _ = (g * (g * P)) * Q := by simp only [mul_assoc]
    _ = (g * (P * S)) * Q := by rw [hrel]
    _ = ((g * P) * S) * Q := by simp only [mul_assoc]
    _ = ((P * S) * S) * Q := by rw [hrel]
    _ = (P * (S * S)) * Q := by simp only [mul_assoc]
    _ = (P * 1) * Q := by rw [hS]
    _ = 1 := by rw [mul_one, hPQ]

private lemma a11ge_pow_mul {g P S : M4} (hrel : g * P = P * S) (n : ℕ) :
    g ^ n * P = P * S ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc g ^ (n + 1) * P = (g ^ n * g) * P := by rw [pow_succ]
        _ = g ^ n * (g * P) := by simp only [mul_assoc]
        _ = g ^ n * (P * S) := by rw [hrel]
        _ = (g ^ n * P) * S := by simp only [mul_assoc]
        _ = (P * S ^ n) * S := by rw [ih]
        _ = P * S ^ (n + 1) := by rw [mul_assoc, pow_succ]

private lemma a11ge_pow_three_eq_one {g h P Q S T : M4} (hPQ : P * Q = 1)
    (hrelg : g * P = P * S) (hrelh : h * P = P * T) (hST : (S * T) ^ 3 = 1) :
    (g * h) ^ 3 = 1 := by
  have hrel : (g * h) * P = P * (S * T) := by
    rw [mul_assoc, hrelh, ← mul_assoc, hrelg, mul_assoc]
  have hp := a11ge_pow_mul hrel 3
  rw [hST, mul_one] at hp
  have hcancel : ((g * h) ^ 3 * P) * Q = (g * h) ^ 3 := by
    rw [mul_assoc, hPQ, mul_one]
  rw [← hcancel, hp, hPQ]

private lemma a11ge_ne_one {g h P Q S T : M4} (hPQ : P * Q = 1)
    (hrelg : g * P = P * S) (hrelh : h * P = P * T) (hST : S * T ≠ 1) :
    g * h ≠ 1 := by
  have hQP : Q * P = 1 := a11ge_mul_comm_of_mul_eq_one hPQ
  intro hgh
  have hrel : (g * h) * P = P * (S * T) := by
    rw [mul_assoc, hrelh, ← mul_assoc, hrelg, mul_assoc]
  have hP : P = P * (S * T) := by
    rw [← hrel, hgh, one_mul]
  have hT : S * T = 1 := by
    calc S * T = 1 * (S * T) := by rw [one_mul]
      _ = (Q * P) * (S * T) := by rw [hQP]
      _ = Q * (P * (S * T)) := by rw [mul_assoc]
      _ = Q * P := by rw [← hP]
      _ = 1 := hQP
  exact hST hT

private lemma a11ge_genK_rel {C C' g Dp P S : M4} (hC'C : C' * C = 1)
    (hDcommC : Dp * C = C * Dp) (hDcommC' : Dp * C' = C' * Dp) (hDcommg : Dp * g = g * Dp)
    (hrel : g * P = P * S) :
    (C * g * C') * (Dp * C * P) = (Dp * C * P) * S := by
  calc (C * g * C') * (Dp * C * P)
      = C * g * (C' * Dp) * (C * P) := by noncomm_ring
    _ = C * g * (Dp * C') * (C * P) := by rw [hDcommC']
    _ = C * g * Dp * (C' * C) * P := by noncomm_ring
    _ = C * g * Dp * P := by rw [hC'C, mul_one]
    _ = C * (Dp * g) * P := by rw [hDcommg]; noncomm_ring
    _ = Dp * C * g * P := by rw [hDcommC]; noncomm_ring
    _ = Dp * C * (g * P) := by noncomm_ring
    _ = Dp * C * (P * S) := by rw [hrel]
    _ = (Dp * C * P) * S := by noncomm_ring

private def a11ge_pi : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide
  right_inv := by decide

private lemma a11ge_zmod7_ne_zero_cases : ∀ a : ZMod 7,
    a ≠ 0 → a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by
  decide +kernel

private lemma a11ge_fBasis_mul_inv (a : ZMod 7) (ha : a ≠ 0) :
    fBasis a * fBasisInv a = 1 := by
  rcases a11ge_zmod7_ne_zero_cases a ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

private lemma a11ge_fBasis_inv_mul (a : ZMod 7) (ha : a ≠ 0) :
    fBasisInv a * fBasis a = 1 := by
  rcases a11ge_zmod7_ne_zero_cases a ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

private lemma a11ge_a8PermMat_permMatrix (σ : Equiv.Perm (Fin 4)) :
    a8PermMat σ = σ.permMatrix (ZMod 7) := by
  ext i j; simp [a8PermMat, Equiv.Perm.permMatrix, eq_comm]

private lemma a11ge_a8PermMat_mul (σ τ : Equiv.Perm (Fin 4)) :
    a8PermMat (σ * τ) = a8PermMat τ * a8PermMat σ := by
  rw [a11ge_a8PermMat_permMatrix, a11ge_a8PermMat_permMatrix, a11ge_a8PermMat_permMatrix,
    Matrix.permMatrix_mul]

private lemma a11ge_fPerm_mul (a : ZMod 7) (ha : a ≠ 0) (σ τ : Equiv.Perm (Fin 4)) :
    fPerm a (σ * τ) = fPerm a τ * fPerm a σ := by
  have hb : fBasis a * fBasisInv a = 1 := a11ge_fBasis_mul_inv a ha
  rw [fPerm, fPerm, fPerm, a11ge_a8PermMat_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (fBasis a) (fBasisInv a) (a8PermMat σ * fBasis a), hb, one_mul]

private lemma a11ge_smul_a8MonK3 :
    ∀ (e : ZMod 3) (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3),
      (2 : ZMod 7) ^ e.val • a8MonK3 π k = a8MonK3 π (fun i => k i + e) := by
  decide +kernel

private lemma a11ge_vecMul_smul (c : ZMod 7) (v : Fin 3 → ZMod 7) (M : M3) :
    vecMul v (c • M) = c • vecMul v M :=
  Matrix.vecMul_smul v c M

private lemma a11ge_exists_alpha_mono (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3) :
    ∃ α : MulAut GLV, ∀ f : Fin 3 → ZMod 7,
      α (tC f) = tC (vecMul f (a8MonK3 π k)) := by
  obtain ⟨n, hn⟩ := ggSL9_exists_monomial π k
  exact ⟨MulAut.conj n, fun f => by simpa [tC, MulAut.conj_apply] using hn f⟩

private lemma a11ge_exists_alpha_neg (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3) :
    ∃ α : MulAut GLV, ∀ f : Fin 3 → ZMod 7,
      α (tC f) = tC (-(vecMul f (a8MonK3 π k))) := by
  obtain ⟨γ, hγ⟩ := a11GraphAutInput_holds
  obtain ⟨n, hn⟩ := ggSL9_exists_monomial π k
  refine ⟨(MulAut.conj n).trans γ, fun f => ?_⟩
  rw [MulEquiv.trans_apply]
  have h1 : (MulAut.conj n) (tC f) = tC (vecMul f (a8MonK3 π k)) := by
    simpa [tC, MulAut.conj_apply] using hn f
  rw [h1, hγ]

private lemma a11ge_exists_alpha (u : ZMod 7) (hu : u ≠ 0)
    (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3) :
    ∃ α : MulAut GLV, ∀ f : Fin 3 → ZMod 7,
      α (tC f) = tC (u⁻¹ • vecMul f (a8MonK3 π k)) := by
  rcases a11ge_zmod7_ne_zero_cases u hu with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨α, hα⟩ := a11ge_exists_alpha_mono π k
    refine ⟨α, fun f => ?_⟩
    rw [hα f]
    congr 1
    simp
  · obtain ⟨α, hα⟩ := a11ge_exists_alpha_mono π (fun i => k i + (2 : ZMod 3))
    refine ⟨α, fun f => ?_⟩
    rw [hα f]
    congr 1
    rw [ZMod.inv_eq_of_mul_eq_one 7 2 4 (by decide)]
    rw [← a11ge_smul_a8MonK3 (2 : ZMod 3) π k, a11ge_vecMul_smul,
      show (2 : ZMod 7) ^ (2 : ZMod 3).val = (4 : ZMod 7) from by decide]
  · obtain ⟨α, hα⟩ := a11ge_exists_alpha_neg π (fun i => k i + (1 : ZMod 3))
    refine ⟨α, fun f => ?_⟩
    rw [hα f]
    congr 1
    rw [ZMod.inv_eq_of_mul_eq_one 7 3 5 (by decide)]
    rw [← a11ge_smul_a8MonK3 (1 : ZMod 3) π k, a11ge_vecMul_smul,
      show (2 : ZMod 7) ^ (1 : ZMod 3).val = (2 : ZMod 7) from by decide]
    rw [show -((2 : ZMod 7) • vecMul f (a8MonK3 π k)) = (5 : ZMod 7) • vecMul f (a8MonK3 π k) from by
      rw [show (5 : ZMod 7) = -2 from by decide]
      exact (neg_smul (2 : ZMod 7) (vecMul f (a8MonK3 π k))).symm]
  · obtain ⟨α, hα⟩ := a11ge_exists_alpha_mono π (fun i => k i + (1 : ZMod 3))
    refine ⟨α, fun f => ?_⟩
    rw [hα f]
    congr 1
    rw [ZMod.inv_eq_of_mul_eq_one 7 4 2 (by decide)]
    rw [← a11ge_smul_a8MonK3 (1 : ZMod 3) π k, a11ge_vecMul_smul,
      show (2 : ZMod 7) ^ (1 : ZMod 3).val = (2 : ZMod 7) from by decide]
  · obtain ⟨α, hα⟩ := a11ge_exists_alpha_neg π (fun i => k i + (2 : ZMod 3))
    refine ⟨α, fun f => ?_⟩
    rw [hα f]
    congr 1
    rw [ZMod.inv_eq_of_mul_eq_one 7 5 3 (by decide)]
    rw [← a11ge_smul_a8MonK3 (2 : ZMod 3) π k, a11ge_vecMul_smul,
      show (2 : ZMod 7) ^ (2 : ZMod 3).val = (4 : ZMod 7) from by decide]
    rw [show -((4 : ZMod 7) • vecMul f (a8MonK3 π k)) = (3 : ZMod 7) • vecMul f (a8MonK3 π k) from by
      rw [show (3 : ZMod 7) = -4 from by decide]
      exact (neg_smul (4 : ZMod 7) (vecMul f (a8MonK3 π k))).symm]
  · obtain ⟨α, hα⟩ := a11ge_exists_alpha_neg π k
    refine ⟨α, fun f => ?_⟩
    rw [hα f]
    congr 1
    rw [ZMod.inv_eq_of_mul_eq_one 7 6 6 (by decide)]
    rw [show (-(vecMul f (a8MonK3 π k))) = (6 : ZMod 7) • vecMul f (a8MonK3 π k) from by
      rw [show (6 : ZMod 7) = -1 from by decide]
      simpa using (neg_smul (1 : ZMod 7) (vecMul f (a8MonK3 π k))).symm]

private lemma a11ge_blk_zero_zero (M : M3) : Certificates.A8Nbr476.blk M 0 0 = 1 := by
  simp [Certificates.A8Nbr476.blk]

private lemma a11ge_blk_zero_succ (M : M3) (j : Fin 3) :
    Certificates.A8Nbr476.blk M 0 j.succ = 0 := by
  simp [Certificates.A8Nbr476.blk]

private lemma a11ge_blk_succ_zero (M : M3) (i : Fin 3) :
    Certificates.A8Nbr476.blk M i.succ 0 = 0 := by
  simp [Certificates.A8Nbr476.blk]

private lemma a11ge_blk_succ_succ (M : M3) (i j : Fin 3) :
    Certificates.A8Nbr476.blk M i.succ j.succ = M i j := by
  simp [Certificates.A8Nbr476.blk, Fin.pred_succ]

private lemma a11ge_blk_mul (A B : M3) :
    Certificates.A8Nbr476.blk A * Certificates.A8Nbr476.blk B =
      Certificates.A8Nbr476.blk (A * B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Certificates.A8Nbr476.blk, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]

private lemma a11ge_vecMul_blk_zero (v : Fin 4 → ZMod 7) (M : M3) :
    vecMul v (Certificates.A8Nbr476.blk M) 0 = v 0 := by
  rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]
  simp [a11ge_blk_zero_zero, a11ge_blk_succ_zero]

private lemma a11ge_vecMul_blk_succ (v : Fin 4 → ZMod 7) (M : M3) (i : Fin 3) :
    vecMul v (Certificates.A8Nbr476.blk M) i.succ =
      vecMul (fun j => v j.succ) M i := by
  rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]
  simp only [a11ge_blk_zero_succ, a11ge_blk_succ_succ]
  rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_three]
  ring

private lemma a11ge_vecMul_a8MonK_succ (v : Fin 4 → ZMod 7) (π : Equiv.Perm (Fin 3))
    (k : Fin 3 → ZMod 3) (i : Fin 3) :
    vecMul v (a8MonK π k) (π i).succ = v i.succ * (2 : ZMod 7) ^ (k i).val := by
  rw [show a8MonK π k = Certificates.A8Nbr476.blk (a8MonK3 π k) from rfl,
    a11ge_vecMul_blk_succ v (a8MonK3 π k) (π i)]
  rw [Matrix.vecMul_apply_eq_sum]
  simp only [a8MonK3, Matrix.of_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have h : π b ≠ π i := fun hh => hb (Equiv.injective π hh)
    simp [h]
  · intro hnot; exact absurd (Finset.mem_univ i) hnot

private lemma a11ge_vecMul_single_blk (M : M3) :
    vecMul (Pi.single (0 : Fin 4) 1) (Certificates.A8Nbr476.blk M) = Pi.single 0 1 := by
  funext j
  fin_cases j <;> simp [a11ge_single_vecMul, Certificates.A8Nbr476.blk]

private lemma a11ge_T_eq_blk (u : ZMod 7) (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3) :
    a8MonK π k * a8Dscal u⁻¹ = Certificates.A8Nbr476.blk (u⁻¹ • a8MonK3 π k) := by
  rw [show a8MonK π k = Certificates.A8Nbr476.blk (a8MonK3 π k) from rfl]
  rw [show a8Dscal u⁻¹ = Certificates.A8Nbr476.blk (u⁻¹ • (1 : M3)) from by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [a8Dscal, Certificates.A8Nbr476.blk, Matrix.diagonal]]
  rw [a11ge_blk_mul (a8MonK3 π k) (u⁻¹ • (1 : M3)), Matrix.mul_smul, Matrix.mul_one]

private lemma a11ge_genL_fPerm {c : Case} (hc : c ∈ excCases) :
    genL c 0 = fPerm c.2.1 (Equiv.swap 0 1) ∧
    genL c 1 = fPerm c.2.1 (Equiv.swap 1 2) ∧
    genL c 2 = fPerm c.2.1 (Equiv.swap 0 3) := by
  simp only [excCases, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private lemma a11ge_key {a : ZMod 7} (ha : a ≠ 0) {P' Q' : M4} (hP'Q' : P' * Q' = 1)
    (h1 : P' * a8PermMat (Equiv.swap 0 1) * Q' = fPerm a (Equiv.swap 0 3))
    (h2 : P' * a8PermMat (Equiv.swap 1 2) * Q' = fPerm a (Equiv.swap 0 1))
    (h3 : P' * a8PermMat (Equiv.swap 2 3) * Q' = fPerm a (Equiv.swap 1 2)) :
    ∀ σ : Equiv.Perm (Fin 4),
      P' * a8PermMat (a11ge_pi⁻¹ * σ * a11ge_pi) * Q' = fPerm a σ := by
  have hQ'P : Q' * P' = 1 := a11ge_mul_comm_of_mul_eq_one hP'Q'
  let F : Equiv.Perm (Fin 4) → M4 := fun σ => P' * a8PermMat σ * Q'
  let G : Equiv.Perm (Fin 4) → M4 := fun σ => fPerm a (a11ge_pi * σ * a11ge_pi⁻¹)
  have hFmul : ∀ σ τ : Equiv.Perm (Fin 4), F (σ * τ) = F τ * F σ := by
    intro σ τ
    calc F (σ * τ) = P' * (a8PermMat τ * a8PermMat σ) * Q' := by
          simp only [F, a11ge_a8PermMat_mul]
      _ = P' * a8PermMat τ * Q' * (P' * a8PermMat σ * Q') := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Q' P' (a8PermMat σ * Q'), hQ'P, one_mul]
      _ = F τ * F σ := by simp only [F]
  have hGmul : ∀ σ τ : Equiv.Perm (Fin 4), G (σ * τ) = G τ * G σ := by
    intro σ τ
    change fPerm a (a11ge_pi * (σ * τ) * a11ge_pi⁻¹) =
      fPerm a (a11ge_pi * τ * a11ge_pi⁻¹) * fPerm a (a11ge_pi * σ * a11ge_pi⁻¹)
    rw [show a11ge_pi * (σ * τ) * a11ge_pi⁻¹ =
        (a11ge_pi * σ * a11ge_pi⁻¹) * (a11ge_pi * τ * a11ge_pi⁻¹) from by group]
    rw [a11ge_fPerm_mul a ha]
  have hFone : F 1 = G 1 := by
    have h1 : a8PermMat (1 : Equiv.Perm (Fin 4)) = 1 := by decide +kernel
    have h2 : a11ge_pi * 1 * a11ge_pi⁻¹ = 1 := by group
    simp only [F, G, fPerm, h1, h2, Matrix.mul_one]
    rw [hP'Q', a11ge_fBasis_inv_mul a ha]
  let S : Submonoid (Equiv.Perm (Fin 4)) :=
    { carrier := {σ | F σ = G σ}
      one_mem' := hFone
      mul_mem' := by
        intro σ τ hσ hτ
        show F (σ * τ) = G (σ * τ)
        rw [hFmul, hGmul, hσ, hτ] }
  have hgen : ∀ i : Fin 3, F (Equiv.swap i.castSucc i.succ) = G (Equiv.swap i.castSucc i.succ) := by
    intro i
    fin_cases i
    · simpa [F, G, show ((Equiv.swap (0 : Fin 3).castSucc (0 : Fin 3).succ) : Equiv.Perm (Fin 4)) =
          Equiv.swap (0 : Fin 4) 1 from by decide,
        show a11ge_pi * Equiv.swap (0 : Fin 4) 1 * a11ge_pi⁻¹ = Equiv.swap 0 3 from by decide]
        using h1
    · simpa [F, G, show ((Equiv.swap (1 : Fin 3).castSucc (1 : Fin 3).succ) : Equiv.Perm (Fin 4)) =
          Equiv.swap (1 : Fin 4) 2 from by decide,
        show a11ge_pi * Equiv.swap (1 : Fin 4) 2 * a11ge_pi⁻¹ = Equiv.swap 0 1 from by decide]
        using h2
    · simpa [F, G, show ((Equiv.swap (2 : Fin 3).castSucc (2 : Fin 3).succ) : Equiv.Perm (Fin 4)) =
          Equiv.swap (2 : Fin 4) 3 from by decide,
        show a11ge_pi * Equiv.swap (2 : Fin 4) 3 * a11ge_pi⁻¹ = Equiv.swap 1 2 from by decide]
        using h3
  have hle : Submonoid.closure (Set.range fun i : Fin 3 => Equiv.swap i.castSucc i.succ) ≤ S :=
    Submonoid.closure_le.mpr (by rintro σ ⟨i, rfl⟩; exact hgen i)
  have htop : (⊤ : Submonoid (Equiv.Perm (Fin 4))) ≤ S := by
    rw [← Equiv.Perm.mclosure_swap_castSucc_succ 3]
    exact hle
  intro σ
  have h := htop (Submonoid.mem_top (a11ge_pi⁻¹ * σ * a11ge_pi))
  change F (a11ge_pi⁻¹ * σ * a11ge_pi) = G (a11ge_pi⁻¹ * σ * a11ge_pi) at h
  have hp : a11ge_pi * (a11ge_pi⁻¹ * σ * a11ge_pi) * a11ge_pi⁻¹ = σ := by group
  simpa only [F, G, hp] using h

private lemma a11ge_excCases_a_ne_zero {c : Case} (hc : c ∈ excCases) : c.2.1 ≠ 0 := by
  simp only [excCases, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem a11GlueExtInput_holds : A11GlueExtInput := by
  intro G _ Bs L K J hNT hJK xb y hy hJx ρ ιK ιL hF hK hV hLx hL hLJ
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P, Q, hP, hPQ, hQP⟩ := a11ge_exists_frame ιK ιL
  have hdetP : P.det ≠ 0 := a11ge_det_ne_zero_of_mul_eq_one hPQ
  obtain ⟨ψ1, hψ1J, hψ1L⟩ := hLJ (Equiv.swap 1 2) (by decide)
  obtain ⟨ψ2, hψ2J, hψ2L⟩ := hLJ (Equiv.swap 2 3) (by decide)
  have hψ1K : ψ1 ∈ ggAutomizer K Bs := ggAutomizer_mono Bs hJK hψ1J
  have hψ2K : ψ2 ∈ ggAutomizer K Bs := ggAutomizer_mono Bs hJK hψ2J
  obtain ⟨π1, k1, hπ1⟩ := (hK ψ1).mp hψ1K
  obtain ⟨π2, k2, hπ2⟩ := (hK ψ2).mp hψ2K
  let g1 : M4 := a8MonK π1 k1
  let g2 : M4 := a8MonK π2 k2
  have hrel1 : g1 * P = P * a8PermMat (Equiv.swap 1 2) := a11ge_rel_of_aut hP hπ1 hψ1L
  have hrel2 : g2 * P = P * a8PermMat (Equiv.swap 2 3) := a11ge_rel_of_aut hP hπ2 hψ2L
  obtain ⟨hS11, hS22, hS3, hSne⟩ := a8PermMat_relations
  have hg1 : g1 * g1 = 1 := a11ge_sq_eq_one hPQ hrel1 hS11
  have hg2 : g2 * g2 = 1 := a11ge_sq_eq_one hPQ hrel2 hS22
  have hgh : (g1 * g2) ^ 3 = 1 := a11ge_pow_three_eq_one hPQ hrel1 hrel2 hS3
  have hne : g1 * g2 ≠ 1 := a11ge_ne_one hPQ hrel1 hrel2 hSne
  have hvg1 : vecMul (ιK (Additive.ofMul xb)) g1 = ιK (Additive.ofMul xb) :=
    a11ge_fix_of_aut hπ1 (hJx ψ1 hψ1J)
  have hvg2 : vecMul (ιK (Additive.ofMul xb)) g2 = ιK (Additive.ofMul xb) :=
    a11ge_fix_of_aut hπ2 (hJx ψ2 hψ2J)
  obtain ⟨π, π', k, k', hCC', hCg1, hCg2⟩ :=
    a8_standardize (π₁ := π1) (π₂ := π2) (k₁ := k1) (k₂ := k2)
      (v := ιK (Additive.ofMul xb)) hg1 hg2 hgh hne hV hvg1 hvg2
  let C : M4 := a8MonK π k
  let C' : M4 := a8MonK π' k'
  have hC'C : C' * C = 1 := a11ge_mul_comm_of_mul_eq_one hCC'
  let vK : Fin 4 → ZMod 7 := ιK (Additive.ofMul xb)
  let vK1 : Fin 4 → ZMod 7 := vecMul vK C'
  have hvK1_fix0 : vecMul vK1 (genK 0) = vK1 := by
    change vecMul (vecMul vK C') (genK 0) = vecMul vK C'
    rw [← hCg1, Matrix.vecMul_vecMul]
    have hm : C' * (C * g1 * C') = g1 * C' := by
      rw [← mul_assoc C' (C * g1) C', ← mul_assoc C' C g1, hC'C, one_mul]
    rw [hm, ← Matrix.vecMul_vecMul, hvg1]
  have hvK1_fix1 : vecMul vK1 (genK 1) = vK1 := by
    change vecMul (vecMul vK C') (genK 1) = vecMul vK C'
    rw [← hCg2, Matrix.vecMul_vecMul]
    have hm : C' * (C * g2 * C') = g2 * C' := by
      rw [← mul_assoc C' (C * g2) C', ← mul_assoc C' C g2, hC'C, one_mul]
    rw [hm, ← Matrix.vecMul_vecMul, hvg2]
  have hfix01 := a8_fixed_genK hvK1_fix0 hvK1_fix1
  let u : ZMod 7 := vK1 1
  let a0 : ZMod 7 := vK1 0
  have hu : u ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, π' i = 0 := ⟨π'.symm 0, by simp⟩
    have hcoord := a11ge_vecMul_a8MonK_succ vK π' k' i
    have h1 : (1 : Fin 4) = (0 : Fin 3).succ := rfl
    change vecMul vK C' 1 ≠ 0
    rw [h1, ← hi, hcoord]
    exact mul_ne_zero (hV i) (pow_ne_zero _ a11ge_two_ne_zero)
  have hvK1vec : vK1 = ![a0, u, u, u] := by
    funext j
    fin_cases j <;> simp [a0, u, hfix01.1, hfix01.2]
  let Dm : M4 := a8Dscal u⁻¹
  let Dp : M4 := a8Dscal u
  have hDpDm : Dp * Dm = 1 := a8Dscal_mul_inv hu
  have hDmDp : Dm * Dp = 1 := a11ge_mul_comm_of_mul_eq_one hDpDm
  let T : M4 := C' * Dm
  let T' : M4 := Dp * C
  have hTT' : T * T' = 1 := by
    change (C' * Dm) * (Dp * C) = 1
    rw [mul_assoc, ← mul_assoc Dm Dp C, hDmDp, one_mul, hC'C]
  let ιK2 : Additive ↥Bs ≃+ (Fin 4 → ZMod 7) := ιK.trans (a11ge_matAddEquiv T T' hTT')
  have hιK2 : ∀ b, ιK2 b = vecMul (ιK b) T := fun b => rfl
  let vK2 : Fin 4 → ZMod 7 := ιK2 (Additive.ofMul xb)
  have hvK2 : vK2 = ![a0, 1, 1, 1] := by
    have h1 : vK2 = vecMul vK1 Dm := by
      change vecMul (ιK (Additive.ofMul xb)) (C' * Dm) = vecMul vK1 Dm
      rw [Matrix.vecMul_vecMul]
    rw [h1, hvK1vec]
    exact a11ge_vecMul_a8Dscal a0 u hu
  let P' : M4 := Dp * C * P
  have hP' : ∀ b, ιL b = vecMul (ιK2 b) P' := by
    intro b
    rw [hP b]
    change vecMul (ιK b) P = vecMul (vecMul (ιK b) T) (Dp * C * P)
    rw [Matrix.vecMul_vecMul]
    have hTP : T * (Dp * C * P) = P := by
      rw [← mul_assoc T (Dp * C) P, hTT', one_mul]
    rw [hTP]
  have hmD0 : Dm * genK 0 * Dp = genK 0 := by
    rw [genK_eq_a8MonK.1, a8Dscal_comm u⁻¹ (Equiv.swap 0 1) 0, mul_assoc, hDmDp, mul_one]
  have hmD1 : Dm * genK 1 * Dp = genK 1 := by
    rw [genK_eq_a8MonK.2.1, a8Dscal_comm u⁻¹ (Equiv.swap 1 2) 0, mul_assoc, hDmDp, mul_one]
  have hmD2 : Dm * genK 2 * Dp = genK 2 := by
    rw [genK_eq_a8MonK.2.2, a8Dscal_comm u⁻¹ 1 ![1, 0, 0], mul_assoc, hDmDp, mul_one]
  have hT0 : T * genK 0 * T' = a8MonK π1 k1 := by
    change C' * Dm * genK 0 * (Dp * C) = a8MonK π1 k1
    calc C' * Dm * genK 0 * (Dp * C)
        = C' * (Dm * genK 0 * Dp) * C := by simp only [mul_assoc]
      _ = C' * genK 0 * C := by rw [hmD0]
      _ = g1 := by
          rw [← hCg1]
          calc C' * (C * g1 * C') * C = (C' * C) * g1 * (C' * C) := by simp only [mul_assoc]
            _ = g1 := by rw [hC'C, one_mul, mul_one]
  have hT1 : T * genK 1 * T' = a8MonK π2 k2 := by
    change C' * Dm * genK 1 * (Dp * C) = a8MonK π2 k2
    calc C' * Dm * genK 1 * (Dp * C)
        = C' * (Dm * genK 1 * Dp) * C := by simp only [mul_assoc]
      _ = C' * genK 1 * C := by rw [hmD1]
      _ = g2 := by
          rw [← hCg2]
          calc C' * (C * g2 * C') * C = (C' * C) * g2 * (C' * C) := by simp only [mul_assoc]
            _ = g2 := by rw [hC'C, one_mul, mul_one]
  have hT2 : ∃ πT kT, T * genK 2 * T' = a8MonK πT kT := by
    obtain ⟨πa, ka, ha⟩ := a8MonK_mul π' 1 k' ![1, 0, 0]
    obtain ⟨πb, kb, hb⟩ := a8MonK_mul πa π ka k
    refine ⟨πb, kb, ?_⟩
    change C' * Dm * genK 2 * (Dp * C) = a8MonK πb kb
    calc C' * Dm * genK 2 * (Dp * C)
        = C' * (Dm * genK 2 * Dp) * C := by simp only [mul_assoc]
      _ = C' * genK 2 * C := by rw [hmD2]
      _ = (a8MonK π' k' * a8MonK 1 ![1, 0, 0]) * a8MonK π k := by
          change a8MonK π' k' * genK 2 * a8MonK π k = _
          rw [genK_eq_a8MonK.2.2]
      _ = a8MonK πb kb := by rw [ha, hb]
  have hgenK : ∀ j : Fin 3, ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs,
      ∀ b : ↥Bs, ιK2 (Additive.ofMul (φ b)) = vecMul (ιK2 (Additive.ofMul b)) (genK j) := by
    intro j
    fin_cases j
    · obtain ⟨π0', k0', hinv0⟩ := a8MonK_inv (Equiv.swap 0 1) (0 : Fin 3 → ZMod 3)
      have hm0 : genK 0 * a8MonK π0' k0' = 1 := by
        rw [genK_eq_a8MonK.1]; exact hinv0
      have hmem0 : a11ge_matAut ιK2 (genK 0) (a8MonK π0' k0') hm0 ∈ ggAutomizer K Bs :=
        a11ge_matAut_mem_of_frame hK hTT' (fun b => rfl) hm0 ⟨π1, k1, hT0⟩
      exact ⟨a11ge_matAut ιK2 (genK 0) (a8MonK π0' k0') hm0, Subgroup.mem_sup_right hmem0,
        fun b => a11ge_matAut_apply ιK2 _ _ hm0 b⟩
    · obtain ⟨π1', k1', hinv1⟩ := a8MonK_inv (Equiv.swap 1 2) (0 : Fin 3 → ZMod 3)
      have hm1 : genK 1 * a8MonK π1' k1' = 1 := by
        rw [genK_eq_a8MonK.2.1]; exact hinv1
      have hmem1 : a11ge_matAut ιK2 (genK 1) (a8MonK π1' k1') hm1 ∈ ggAutomizer K Bs :=
        a11ge_matAut_mem_of_frame hK hTT' (fun b => rfl) hm1 ⟨π2, k2, hT1⟩
      exact ⟨a11ge_matAut ιK2 (genK 1) (a8MonK π1' k1') hm1, Subgroup.mem_sup_right hmem1,
        fun b => a11ge_matAut_apply ιK2 _ _ hm1 b⟩
    · obtain ⟨π2', k2', hinv2⟩ := a8MonK_inv 1 ![1, 0, 0]
      have hm2 : genK 2 * a8MonK π2' k2' = 1 := by
        rw [genK_eq_a8MonK.2.2]; exact hinv2
      obtain ⟨πT, kT, hT2eq⟩ := hT2
      have hmem2 : a11ge_matAut ιK2 (genK 2) (a8MonK π2' k2') hm2 ∈ ggAutomizer K Bs :=
        a11ge_matAut_mem_of_frame hK hTT' (fun b => rfl) hm2 ⟨πT, kT, hT2eq⟩
      exact ⟨a11ge_matAut ιK2 (genK 2) (a8MonK π2' k2') hm2, Subgroup.mem_sup_right hmem2,
        fun b => a11ge_matAut_apply ιK2 _ _ hm2 b⟩
  let Q' : M4 := Q * C' * Dm
  have hP'Q' : P' * Q' = 1 := by
    change Dp * C * P * (Q * C' * Dm) = 1
    calc Dp * C * P * (Q * C' * Dm)
        = Dp * C * (P * Q) * C' * Dm := by simp only [mul_assoc]
      _ = Dp * C * C' * Dm := by rw [hPQ, mul_one]
      _ = Dp * (C * C') * Dm := by simp only [mul_assoc]
      _ = 1 := by rw [hCC', mul_one, hDpDm]
  have hgenK_rel0 : genK 0 * P' = P' * a8PermMat (Equiv.swap 1 2) := by
    rw [← hCg1]
    exact a11ge_genK_rel hC'C (a8Dscal_comm u π k) (a8Dscal_comm u π' k')
      (a8Dscal_comm u π1 k1) hrel1
  have hgenK_rel1 : genK 1 * P' = P' * a8PermMat (Equiv.swap 2 3) := by
    rw [← hCg2]
    exact a11ge_genK_rel hC'C (a8Dscal_comm u π k) (a8Dscal_comm u π' k')
      (a8Dscal_comm u π2 k2) hrel2
  have hP'mat : P' = a8P (P' 0 0) (P' 0 1) (P' 1 0) (P' 1 1) (P' 1 2) :=
    a8_intertwiner hgenK_rel0 hgenK_rel1
  have hxP' : vecMul ![a0, 1, 1, 1]
      (a8P (P' 0 0) (P' 0 1) (P' 1 0) (P' 1 1) (P' 1 2)) = fun _ => 1 := by
    rw [← hP'mat, ← hvK2]
    have hv : vK2 = ιK2 (Additive.ofMul xb) := rfl
    rw [hv, ← hP' (Additive.ofMul xb)]
    exact hLx
  have hdetP' : (a8P (P' 0 0) (P' 0 1) (P' 1 0) (P' 1 1) (P' 1 2)).det ≠ 0 := by
    rw [← hP'mat]
    change (Dp * C * P).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero
      (mul_ne_zero (a11ge_det_ne_zero_of_mul_eq_one hDpDm) (a11ge_det_ne_zero_of_mul_eq_one hCC'))
      hdetP
  obtain ⟨ψL, hψLL, hψLmat⟩ := hL (Equiv.swap 0 1)
  rcases a8_match hxP' hdetP' with ⟨β, μ, hμ, hab, hmat⟩ | ⟨μ, hμ, ha, hmat⟩
  · rw [← hP'mat] at hmat
    have hgenAll : ∀ k : Fin 6, ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
        ιK2 (Additive.ofMul (φ b)) = vecMul (ιK2 (Additive.ofMul b)) (gens (true, a0, β, μ) k) := by
      intro k
      fin_cases k
      · have hz := (a8_genL_zero_one (a := a0) (β := β) (μ := μ) hμ hab).1
        obtain ⟨φ, hφ, hφmat⟩ := hgenK 0
        refine ⟨φ, hφ, fun b => ?_⟩
        change ιK2 (Additive.ofMul (φ b)) = ιK2 (Additive.ofMul b) ᵥ* gens ((true, a0, β, μ) : Case) 0
        simpa [gens, hz] using hφmat b
      · have hz := (a8_genL_zero_one (a := a0) (β := β) (μ := μ) hμ hab).2
        obtain ⟨φ, hφ, hφmat⟩ := hgenK 1
        refine ⟨φ, hφ, fun b => ?_⟩
        change ιK2 (Additive.ofMul (φ b)) = ιK2 (Additive.ofMul b) ᵥ* gens ((true, a0, β, μ) : Case) 1
        simpa [gens, hz] using hφmat b
      · have hgl_eq : genL (true, a0, β, μ) 2 = P' * a8PermMat (Equiv.swap 0 1) * Q' := by
          rw [← hmat]
          rw [mul_assoc, hP'Q', mul_one]
        refine ⟨ψL, Subgroup.mem_sup_left hψLL, fun b => ?_⟩
        have hmat1 : vecMul (ιK2 (Additive.ofMul (ψL b))) P' =
            vecMul (ιK2 (Additive.ofMul b)) (P' * a8PermMat (Equiv.swap 0 1)) := by
          rw [← hP' (Additive.ofMul (ψL b)), hψLmat, hP' (Additive.ofMul b), Matrix.vecMul_vecMul]
        change ιK2 (Additive.ofMul (ψL b)) = ιK2 (Additive.ofMul b) ᵥ* gens ((true, a0, β, μ) : Case) 2
        have hcalc : ιK2 (Additive.ofMul (ψL b)) =
            vecMul (ιK2 (Additive.ofMul b)) (genL (true, a0, β, μ) 2) := by
          calc ιK2 (Additive.ofMul (ψL b))
              = vecMul (ιK2 (Additive.ofMul (ψL b))) (P' * Q') := by
                rw [hP'Q', Matrix.vecMul_one]
            _ = vecMul (vecMul (ιK2 (Additive.ofMul (ψL b))) P') Q' := by
                rw [Matrix.vecMul_vecMul]
            _ = vecMul (vecMul (ιK2 (Additive.ofMul b))
                  (P' * a8PermMat (Equiv.swap 0 1))) Q' := by rw [hmat1]
            _ = vecMul (ιK2 (Additive.ofMul b))
                  (P' * a8PermMat (Equiv.swap 0 1) * Q') := by rw [Matrix.vecMul_vecMul]
            _ = vecMul (ιK2 (Additive.ofMul b)) (genL (true, a0, β, μ) 2) := by rw [← hgl_eq]
        simpa [gens] using hcalc
      · obtain ⟨φ, hφ, hφmat⟩ := hgenK 0
        refine ⟨φ, hφ, fun b => ?_⟩
        change ιK2 (Additive.ofMul (φ b)) = ιK2 (Additive.ofMul b) ᵥ* gens ((true, a0, β, μ) : Case) 3
        simpa [gens] using hφmat b
      · obtain ⟨φ, hφ, hφmat⟩ := hgenK 1
        refine ⟨φ, hφ, fun b => ?_⟩
        change ιK2 (Additive.ofMul (φ b)) = ιK2 (Additive.ofMul b) ᵥ* gens ((true, a0, β, μ) : Case) 4
        simpa [gens] using hφmat b
      · obtain ⟨φ, hφ, hφmat⟩ := hgenK 2
        refine ⟨φ, hφ, fun b => ?_⟩
        change ιK2 (Additive.ofMul (φ b)) = ιK2 (Additive.ofMul b) ᵥ* gens ((true, a0, β, μ) : Case) 5
        simpa [gens] using hφmat b
    have hcAll : ((true, a0, β, μ) : Case) ∈ allCases := a8_mem_allCases hμ hab
    have hcExc : ((true, a0, β, μ) : Case) ∈ excCases := by
      by_contra hx
      exact ggA8Nbr_false_of_coord L K hNT ιK2 hcAll hx hgenAll
    have ha0 : a0 ≠ 0 := a11ge_excCases_a_ne_zero hcExc
    have hgf := a11ge_genL_fPerm hcExc
    have hgl2 : genL (true, a0, β, μ) 2 = P' * a8PermMat (Equiv.swap 0 1) * Q' := by
      rw [← hmat]
      rw [mul_assoc, hP'Q', mul_one]
    have h1 : P' * a8PermMat (Equiv.swap 0 1) * Q' = fPerm a0 (Equiv.swap 0 3) := by
      rw [← hgl2]; exact hgf.2.2
    have hz01 := a8_genL_zero_one (a := a0) (β := β) (μ := μ) hμ hab
    have h2 : P' * a8PermMat (Equiv.swap 1 2) * Q' = fPerm a0 (Equiv.swap 0 1) := by
      have h : genK 0 = P' * a8PermMat (Equiv.swap 1 2) * Q' := by
        rw [← hgenK_rel0]
        rw [mul_assoc, hP'Q', mul_one]
      rw [← h, ← hz01.1, hgf.1]
    have h3 : P' * a8PermMat (Equiv.swap 2 3) * Q' = fPerm a0 (Equiv.swap 1 2) := by
      have h : genK 1 = P' * a8PermMat (Equiv.swap 2 3) * Q' := by
        rw [← hgenK_rel1]
        rw [mul_assoc, hP'Q', mul_one]
      rw [← h, ← hz01.2, hgf.2.1]
    have hkey := a11ge_key ha0 hP'Q' h1 h2 h3
    obtain ⟨α, hα⟩ := a11ge_exists_alpha u hu π' k'
    let ρ' : ↥K ≃* GLV := ρ.trans α
    have hTblk : T = Certificates.A8Nbr476.blk (u⁻¹ • a8MonK3 π' k') := a11ge_T_eq_blk u π' k'
    refine ⟨ρ', ιK2, a0, ha0, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · change ιK2 (Additive.ofMul ⟨y, hy⟩) = Pi.single 0 1
        rw [hιK2, hF.1, hTblk]
        exact a11ge_vecMul_single_blk _
      · intro b
        rw [hιK2, hTblk, a11ge_vecMul_blk_zero]
        exact hF.2.1 b
      · intro b hb
        change α (ρ ⟨b, hb⟩) = tC (fun i => ιK2 (Additive.ofMul b) i.succ)
        rw [hF.2.2 b hb, hα]
        congr 1
        funext i
        rw [hιK2, hTblk, a11ge_vecMul_blk_succ, a11ge_vecMul_smul]
    · exact hvK2
    · intro σ
      obtain ⟨ψ, hψL, hψ⟩ := hL (a11ge_pi⁻¹ * σ * a11ge_pi)
      refine ⟨ψ, hψL, fun b => ?_⟩
      have hcalc : ιK2 (Additive.ofMul (ψ b)) =
          vecMul (ιK2 (Additive.ofMul b)) (fPerm a0 σ) := by
        calc ιK2 (Additive.ofMul (ψ b))
            = vecMul (ιL (Additive.ofMul (ψ b))) Q' := a11ge_old_of_new hP'Q' hP' _
          _ = vecMul (ιL (Additive.ofMul b))
                (a8PermMat (a11ge_pi⁻¹ * σ * a11ge_pi) * Q') := by
                rw [hψ b, Matrix.vecMul_vecMul]
          _ = vecMul (vecMul (ιK2 (Additive.ofMul b)) P')
                (a8PermMat (a11ge_pi⁻¹ * σ * a11ge_pi) * Q') := by
                rw [← hP' (Additive.ofMul b)]
          _ = vecMul (ιK2 (Additive.ofMul b))
                (P' * a8PermMat (a11ge_pi⁻¹ * σ * a11ge_pi) * Q') := by
                rw [Matrix.vecMul_vecMul]
                simp only [Matrix.mul_assoc]
          _ = vecMul (ιK2 (Additive.ofMul b)) (fPerm a0 σ) := by rw [hkey σ]
      exact hcalc
    · intro σ hσ3
      have hfix : (a11ge_pi⁻¹ * σ * a11ge_pi) 0 = 0 := by
        simp only [Equiv.Perm.coe_mul, Function.comp_apply]
        rw [show a11ge_pi (0 : Fin 4) = 3 from by decide, hσ3,
          show a11ge_pi⁻¹ (3 : Fin 4) = 0 from by decide]
      obtain ⟨ψ, hψJ, hψ⟩ := hLJ (a11ge_pi⁻¹ * σ * a11ge_pi) hfix
      refine ⟨ψ, hψJ, fun b => ?_⟩
      have hcalc : ιK2 (Additive.ofMul (ψ b)) =
          vecMul (ιK2 (Additive.ofMul b)) (fPerm a0 σ) := by
        calc ιK2 (Additive.ofMul (ψ b))
            = vecMul (ιL (Additive.ofMul (ψ b))) Q' := a11ge_old_of_new hP'Q' hP' _
          _ = vecMul (ιL (Additive.ofMul b))
                (a8PermMat (a11ge_pi⁻¹ * σ * a11ge_pi) * Q') := by
                rw [hψ b, Matrix.vecMul_vecMul]
          _ = vecMul (vecMul (ιK2 (Additive.ofMul b)) P')
                (a8PermMat (a11ge_pi⁻¹ * σ * a11ge_pi) * Q') := by
                rw [← hP' (Additive.ofMul b)]
          _ = vecMul (ιK2 (Additive.ofMul b))
                (P' * a8PermMat (a11ge_pi⁻¹ * σ * a11ge_pi) * Q') := by
                rw [Matrix.vecMul_vecMul]
                simp only [Matrix.mul_assoc]
          _ = vecMul (ιK2 (Additive.ofMul b)) (fPerm a0 σ) := by rw [hkey σ]
      exact hcalc

  · rw [← hP'mat] at hmat
    exfalso
    have hgenLInf_eq : genLInf a0 μ 2 = P' * a8PermMat (Equiv.swap 0 1) * Q' := by
      rw [← hmat]
      rw [mul_assoc, hP'Q', mul_one]
    have hgenInf : ∀ k : Fin 6, ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
        ιK2 (Additive.ofMul (φ b)) = vecMul (ιK2 (Additive.ofMul b)) (gensInf a0 μ k) := by
      intro k
      fin_cases k
      · have hz := (a8_genLInf_zero_one (a := a0) (μ := μ) ha hμ).1
        obtain ⟨φ, hφ, hφmat⟩ := hgenK 0
        refine ⟨φ, hφ, fun b => ?_⟩
        change ιK2 (Additive.ofMul (φ b)) = ιK2 (Additive.ofMul b) ᵥ* gensInf a0 μ 0
        simpa [gensInf, hz] using hφmat b
      · have hz := (a8_genLInf_zero_one (a := a0) (μ := μ) ha hμ).2
        obtain ⟨φ, hφ, hφmat⟩ := hgenK 1
        refine ⟨φ, hφ, fun b => ?_⟩
        change ιK2 (Additive.ofMul (φ b)) = ιK2 (Additive.ofMul b) ᵥ* gensInf a0 μ 1
        simpa [gensInf, hz] using hφmat b
      · refine ⟨ψL, Subgroup.mem_sup_left hψLL, fun b => ?_⟩
        have h1 : vecMul (ιK2 (Additive.ofMul (ψL b))) P' =
            vecMul (ιK2 (Additive.ofMul b)) (P' * a8PermMat (Equiv.swap 0 1)) := by
          rw [← hP' (Additive.ofMul (ψL b)), hψLmat, hP' (Additive.ofMul b),
            Matrix.vecMul_vecMul]
        change ιK2 (Additive.ofMul (ψL b)) = ιK2 (Additive.ofMul b) ᵥ* gensInf a0 μ 2
        have hcalc : ιK2 (Additive.ofMul (ψL b)) =
            vecMul (ιK2 (Additive.ofMul b)) (genLInf a0 μ 2) := by
          calc ιK2 (Additive.ofMul (ψL b))
              = vecMul (ιK2 (Additive.ofMul (ψL b))) (P' * Q') := by
                rw [hP'Q', Matrix.vecMul_one]
            _ = vecMul (vecMul (ιK2 (Additive.ofMul (ψL b))) P') Q' := by
                rw [Matrix.vecMul_vecMul]
            _ = vecMul (vecMul (ιK2 (Additive.ofMul b))
                  (P' * a8PermMat (Equiv.swap 0 1))) Q' := by rw [h1]
            _ = vecMul (ιK2 (Additive.ofMul b))
                  (P' * a8PermMat (Equiv.swap 0 1) * Q') := by rw [Matrix.vecMul_vecMul]
            _ = vecMul (ιK2 (Additive.ofMul b)) (genLInf a0 μ 2) := by rw [← hgenLInf_eq]
        simpa [gensInf] using hcalc
      · obtain ⟨φ, hφ, hφmat⟩ := hgenK 0
        refine ⟨φ, hφ, fun b => ?_⟩
        change ιK2 (Additive.ofMul (φ b)) = ιK2 (Additive.ofMul b) ᵥ* gensInf a0 μ 3
        simpa [gensInf] using hφmat b
      · obtain ⟨φ, hφ, hφmat⟩ := hgenK 1
        refine ⟨φ, hφ, fun b => ?_⟩
        change ιK2 (Additive.ofMul (φ b)) = ιK2 (Additive.ofMul b) ᵥ* gensInf a0 μ 4
        simpa [gensInf] using hφmat b
      · obtain ⟨φ, hφ, hφmat⟩ := hgenK 2
        refine ⟨φ, hφ, fun b => ?_⟩
        change ιK2 (Additive.ofMul (φ b)) = ιK2 (Additive.ofMul b) ᵥ* gensInf a0 μ 5
        simpa [gensInf] using hφmat b
    exact CFSG.StandardType.ggA8NbrInf_false_of_coord L K hNT ιK2 ha hμ hgenInf

end CFSG.StandardType.A11

end
