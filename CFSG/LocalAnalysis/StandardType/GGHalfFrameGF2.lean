module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLFrame
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockTorus
public import Mathlib.Tactic.ComputeDegree

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

@[expose] noncomputable def rhoM : Matrix (Fin 2) (Fin 2) F2 := !![0, 1; 1, 1]

private theorem f2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  let φ : F2 ≃+* ZMod 2 := (GaloisField.equivZmodP 2).toRingEquiv
  have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases h (φ x) with h0 | h1
  · left
    calc x = φ.symm (φ x) := (φ.symm_apply_apply x).symm
      _ = φ.symm 0 := by rw [h0]
      _ = 0 := map_zero φ.symm
  · right
    calc x = φ.symm (φ x) := (φ.symm_apply_apply x).symm
      _ = φ.symm 1 := by rw [h1]
      _ = 1 := map_one φ.symm

private theorem submatrix_pow_equiv {F : Type} [Semiring F] {d d' : ℕ}
    (C : Matrix (Fin d) (Fin d) F) (e : Fin d ≃ Fin d') (m : ℕ) :
    (C.submatrix e.symm e.symm) ^ m = (C ^ m).submatrix e.symm e.symm := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Matrix.submatrix_one_equiv e.symm]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ,
      Matrix.submatrix_mul_equiv (C ^ m) C e.symm e.symm e.symm]

private theorem nsCore_submatrix_reindex {F : Type} [Field F] {d d' s r : ℕ}
    (C : Matrix (Fin d) (Fin d) F) (e : Fin d ≃ Fin d') (k : Fin s → ℕ) :
    (SLNS.nsCore (C.submatrix e.symm e.symm) (r := r) k).submatrix
        (Equiv.sumCongr (Equiv.prodCongr e (Equiv.refl (Fin s))) (Equiv.refl (Fin r)))
        (Equiv.sumCongr (Equiv.prodCongr e (Equiv.refl (Fin s))) (Equiv.refl (Fin r))) =
      SLNS.nsCore C k := by
  ext a b
  rcases a with ⟨a, j⟩ | a
  · rcases b with ⟨b, j'⟩ | b
    · simp only [SLNS.nsCore, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
        Equiv.sumCongr_apply, Sum.map_inl, Equiv.prodCongr_apply, Prod.map_apply,
        Equiv.refl_apply, Matrix.blockDiagonal_apply]
      by_cases h : j = j'
      · subst h
        rw [if_pos rfl, if_pos rfl]
        rw [submatrix_pow_equiv (C := C) (e := e) (m := k j)]
        simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
      · rw [if_neg h, if_neg h]
    · simp only [SLNS.nsCore, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂,
        Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.prodCongr_apply, Prod.map_apply,
        Equiv.refl_apply, Matrix.zero_apply]
  · rcases b with ⟨b, j'⟩ | b
    · simp only [SLNS.nsCore, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁,
        Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.prodCongr_apply, Prod.map_apply,
        Equiv.refl_apply, Matrix.zero_apply]
    · simp only [SLNS.nsCore, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂,
        Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply, Matrix.one_apply]

private theorem nsMat_submatrix_reindex {F : Type} [Field F] {n d d' s r : ℕ}
    (C : Matrix (Fin d) (Fin d) F) (ε : Fin n ≃ (Fin d × Fin s) ⊕ Fin r)
    (e : Fin d ≃ Fin d') (k : Fin s → ℕ) :
    SLNS.nsMat ε C k =
      SLNS.nsMat (ε.trans (Equiv.sumCongr (Equiv.prodCongr e (Equiv.refl (Fin s)))
        (Equiv.refl (Fin r)))) (C.submatrix e.symm e.symm) k := by
  rw [SLNS.nsMat, SLNS.nsMat]
  ext a b
  have h := congrFun (congrFun (nsCore_submatrix_reindex C e k) (ε a)) (ε b)
  simp only [Matrix.submatrix_apply] at h
  simp only [Matrix.submatrix_apply, Equiv.trans_apply]
  exact h.symm

theorem exists_frame_gf2 {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) F2))
    (hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y) (hS3 : ∀ x ∈ S, x ^ 3 = 1) :
    ∃ (s r : ℕ) (ε : Fin n ≃ (Fin 2 × Fin s) ⊕ Fin r) (A₀ : SpecialLinearGroup (Fin n) F2),
      ∀ x ∈ S, ∃ k : Fin s → ℕ, x * (A₀ : Matrix (Fin n) (Fin n) F2) =
        (A₀ : Matrix (Fin n) (Fin n) F2) * SLNS.nsMat ε rhoM k := by
  classical
  let g : Polynomial F2 := Polynomial.X ^ 2 + Polynomial.X + 1
  have h11 : (1 : F2) + 1 = 0 := by
    have h : (2 : F2) = 1 + 1 := by norm_num
    rw [← h, gf2_two]
  have hneg1 : (-(1 : F2)) = 1 := by
    calc (-(1 : F2)) = -(1 : F2) + (1 + 1) := by rw [h11, add_zero]
      _ = 1 := by rw [← add_assoc, neg_add_cancel, zero_add]
  have h3 : (3 : F2) ≠ 0 := by
    have h : (3 : F2) = 1 := by
      have h31 : (3 : F2) = 2 + 1 := by norm_num
      rw [h31, gf2_two, zero_add]
    rw [h]; exact one_ne_zero
  have hmon : g.Monic := by
    change (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2).Monic
    rw [← Polynomial.cyclotomic_three]
    exact Polynomial.cyclotomic.monic 3 F2
  have hirr : Irreducible g := by
    change Irreducible (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2)
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2).natDegree = 2 := by
        compute_degree!
      rw [hdeg]; decide
    · intro x hx
      rw [Polynomial.IsRoot.def] at hx
      rcases f2_eq_zero_or_one x with rfl | rfl
      · have h1 : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2).eval 0 = 1 := by simp
        rw [h1] at hx; exact one_ne_zero hx
      · have h1 : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2).eval 1 = 1 := by
          simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_one, one_pow]
          rw [h11, zero_add]
        rw [h1] at hx; exact one_ne_zero hx
  haveI : Fact (Irreducible g) := ⟨hirr⟩
  have hgd : g ∣ Polynomial.cyclotomic 3 F2 := by
    rw [Polynomial.cyclotomic_three]
  have hdim : (CoordSL.rootPB g).dim = 2 := by
    rw [CoordSL.rootPB, AdjoinRoot.powerBasis_dim]
    change (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2).natDegree = 2
    compute_degree!
  have hcoeff0 : g.coeff 0 = 1 := by
    change (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2).coeff 0 = 1
    simp
  have hcoeff1 : g.coeff 1 = 1 := by
    change (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial F2).coeff 1 = 1
    simp [Polynomial.coeff_one]
  have hmin : (CoordSL.rootPB g).minpolyGen = g := by
    rw [CoordSL.rootPB, PowerBasis.minpolyGen_eq, AdjoinRoot.powerBasis_gen,
      AdjoinRoot.minpoly_root hirr.ne_zero, hmon.leadingCoeff, inv_one, Polynomial.C_1, mul_one]
  have hformula : CoordSL.rootMat g = Matrix.of (fun i j : Fin (CoordSL.rootPB g).dim =>
      if (j : ℕ) + 1 = (CoordSL.rootPB g).dim then
        -((CoordSL.rootPB g).minpolyGen.coeff (i : ℕ))
      else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) := by
    have hgen : (CoordSL.rootPB g).gen = AdjoinRoot.root g := AdjoinRoot.powerBasis_gen _
    rw [CoordSL.rootMat, ← hgen]
    exact PowerBasis.leftMulMatrix (CoordSL.rootPB g)
  have hrho : (CoordSL.rootMat g).submatrix (finCongr hdim).symm (finCongr hdim).symm = rhoM := by
    ext i j
    rw [Matrix.submatrix_apply, hformula, hmin]
    simp only [Matrix.of_apply]
    rw [finCongr_symm_apply_coe hdim i, finCongr_symm_apply_coe hdim j, hdim]
    fin_cases i <;> fin_cases j <;>
      simp [rhoM, hcoeff0, hcoeff1, hneg1]
  obtain ⟨s, r, ε₀, A₀, hA₀⟩ :=
    CoordSL.exists_frame (K := F2) g Nat.prime_three h3 hgd S hSc hS3
  refine ⟨s, r, ε₀.trans (Equiv.sumCongr (Equiv.prodCongr (finCongr hdim) (Equiv.refl (Fin s)))
    (Equiv.refl (Fin r))), A₀, ?_⟩
  intro x hx
  obtain ⟨k, hk⟩ := hA₀ x hx
  refine ⟨k, ?_⟩
  rw [hk, nsMat_submatrix_reindex (ε := ε₀) (C := CoordSL.rootMat g) (e := finCongr hdim) (k := k),
    hrho]

end CFSG.StandardType.GGHalf

end
