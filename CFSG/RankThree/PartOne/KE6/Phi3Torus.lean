module

public import CFSG.RankThree.PartOne.KE6.Phi6Torus
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThree

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
open scoped Matrix

@[expose] def e6T3Matrix6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, -1; 1, 0, 0, 0, -1, 0; 1, 1, 0, -1, 0, -1; 1, 1, 1, -1, -1, -1;
    1, 1, 0, 0, -1, -1; 1, 0, 0, 0, 0, -1]

@[expose] def e6T3Matrix : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ := e6T3Matrix6

theorem weylMatrix_e6T3W_eq : weylMatrix e6T3W = e6T3Matrix := by
  rw [weylMatrix_e6T3W]
  show toMat 6 e6T3MList = e6T3Matrix6
  decide +kernel

abbrev phi3N (L : Type) [Field L] :
    ModGL Tag.E6 L :=
  canonicalRep (coxeterSystem Tag.E6) L e6T3W

@[expose] def phi3Matrix (q : ℕ) : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  e6T3Matrix - Matrix.scalar (Fin Tag.E6.rank) (q : ℤ)

theorem det_scalar_sub_e6T3Matrix : ∀ n : Fin 7,
    detLaplace 6 ((Matrix.of fun i j : Fin 6 => if i = j then ((n : ℕ) : ℤ) else 0) -
      e6T3Matrix6) = (((n : ℕ) : ℤ) ^ 2 + (n : ℕ) + 1) ^ 3 := by
  decide +kernel

theorem natDegree_e6T3Charpoly :
    ((Polynomial.X ^ 2 + Polynomial.X + 1) ^ 3 : Polynomial ℤ).natDegree ≤ 6 := by
  compute_degree

theorem charpoly_e6T3Matrix :
    e6T3Matrix.charpoly = (Polynomial.X ^ 2 + Polynomial.X + 1) ^ 3 := by
  refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq
    ((Finset.range 7).image (fun n : ℕ => (n : ℤ))) ?_ ?_ ?_
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range,
      Matrix.charpoly_degree_eq_dim]
    change ((6 : ℕ) : WithBot ℕ) < ((7 : ℕ) : WithBot ℕ)
    exact WithBot.coe_lt_coe.2 (by norm_num)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le natDegree_e6T3Charpoly)
      (WithBot.coe_lt_coe.2 (by norm_num))
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
    rw [Matrix.eval_charpoly, ← detLaplace_eq_det]
    have h := det_scalar_sub_e6T3Matrix ⟨n, Finset.mem_range.1 hn⟩
    have e : Matrix.scalar (Fin Tag.E6.rank) (n : ℤ) - e6T3Matrix =
        (Matrix.of fun i j : Fin 6 => if i = j then (n : ℤ) else 0) - e6T3Matrix6 := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
      rfl
    rw [e]
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    exact h

theorem det_phi3Matrix (q : ℕ) :
    (phi3Matrix q).det = ((q : ℤ) ^ 2 + q + 1) ^ 3 := by
  have h := congrArg (Polynomial.eval (q : ℤ)) charpoly_e6T3Matrix
  rw [Matrix.eval_charpoly] at h
  have e : phi3Matrix q = -(Matrix.scalar (Fin Tag.E6.rank) (q : ℤ) - e6T3Matrix) := by
    rw [phi3Matrix, neg_sub]
  rw [e, Matrix.det_neg, Fintype.card_fin] at *
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one] at h
  have h6 : ((-1 : ℤ)) ^ Tag.E6.rank = 1 := by decide
  rw [h6, one_mul, h]

section Torus

variable {L : Type} [Field L] {Fr : L →+* L}

theorem rootChar_phi3Matrix_mulVec (q : ℕ)
    (b : Fin Tag.E6.rank → Lˣ) (μ : Fin Tag.E6.rank → ℤ) :
    rootChar b (phi3Matrix q *ᵥ μ) = rootChar b (e6T3W • μ) * (rootChar b μ ^ q)⁻¹ := by
  rw [phi3Matrix, Matrix.sub_mulVec, ← weylMatrix_e6T3W_eq, weylMatrix_mulVec, rootChar_sub]
  congr 2
  have : (Matrix.scalar (Fin Tag.E6.rank) (q : ℤ)) *ᵥ μ = (q : ℤ) • μ := by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [this, rootChar_zsmul, zpow_natCast]

theorem mem_twistedTorus_rootDiagUnit_iff3 [IsAlgClosed L] {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (b : Fin Tag.E6.rank → Lˣ) :
    rootDiagUnit Tag.E6 b ∈ twistedTorus (phi3N L) Fr ↔
      b ∈ (monomialHom (G := Lˣ) (phi3Matrix q)ᵀ).ker := by
  rw [mem_ker_monomialHom_iff_forall, mem_twistedTorus]
  refine (and_iff_right (rootDiagUnit_mem_torusGroup b)).trans ?_
  rw [CFSG.RankThree.Chevalley.entrywise_frob_rootDiagUnit Fr hFr, eq_comm]
  refine (rootDiagUnit_eq_conj_canonicalRep_iff (K := L) b (b ^ q) e6T3W).trans ?_
  constructor
  · intro h μ
    rw [rootChar_phi3Matrix_mulVec, ← CFSG.RankThree.Chevalley.rootChar_pow_tuple, h,
      mul_inv_cancel]
  · intro h v
    have h1 := h v
    rw [rootChar_phi3Matrix_mulVec, mul_inv_eq_one,
      ← CFSG.RankThree.Chevalley.rootChar_pow_tuple] at h1
    exact h1

theorem odd_phi3_order (q : ℕ) : Odd ((q ^ 2 + q + 1) ^ 3) := by
  have h1 : Odd (q ^ 2 + q + 1) := by
    have : q ^ 2 + q = q * (q + 1) := by ring
    rw [this]
    exact (Nat.even_mul_succ_self q).add_one
  exact h1.pow

@[expose] def phi3TorusEquiv [IsAlgClosed L] {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) :
    (monomialHom (G := Lˣ) (phi3Matrix q)ᵀ).ker ≃ twistedTorus (phi3N L) Fr :=
  Equiv.ofBijective
    (fun b => ⟨rootDiagUnit Tag.E6 b.1, (mem_twistedTorus_rootDiagUnit_iff3 hFr b.1).2 b.2⟩)
    ⟨fun b c h => Subtype.ext (rootDiagUnit_injective (congrArg Subtype.val h)), fun x => by
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup x.2.1
      refine ⟨⟨b, (mem_twistedTorus_rootDiagUnit_iff3 hFr b).1 ?_⟩, Subtype.ext hb.symm⟩
      rw [← hb]
      exact x.2⟩

theorem natCard_phi3Torus [IsAlgClosed L] {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (hq : (q : L) = 0) :
    Nat.card (twistedTorus (phi3N L) Fr) = (q ^ 2 + q + 1) ^ 3 ∧
      Odd (Nat.card (twistedTorus (phi3N L) Fr)) := by
  have hdet : ((phi3Matrix q)ᵀ).det = (((q ^ 2 + q + 1) ^ 3 : ℕ) : ℤ) := by
    rw [Matrix.det_transpose, det_phi3Matrix]
    push_cast
    ring
  have hne : (((phi3Matrix q)ᵀ).det : L) ≠ 0 := by
    rw [Matrix.det_transpose, det_phi3Matrix]
    push_cast
    rw [hq]
    norm_num
  have h := natCard_ker_monomialHom (Ω := L) (phi3Matrix q)ᵀ hne
  rw [hdet, Int.natAbs_natCast, Nat.card_congr (phi3TorusEquiv hFr)] at h
  exact ⟨h, h ▸ odd_phi3_order q⟩

end Torus

end CFSG.RankThree.PartOne.KE6
