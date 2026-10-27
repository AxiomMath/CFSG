module

public import CFSG.RankThree.Lattice.SteinbergBIE6QplusData
public import CFSG.RankThree.PartOne.KE6.Phi6Torus

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
open scoped Matrix

abbrev eqpN (L : Type) [Field L] :
    ModGL Tag.E6 L :=
  canonicalRep (coxeterSystem Tag.E6) L e6W0

@[expose] def eqpMatrix (q : ℕ) : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  Matrix.scalar (Fin Tag.E6.rank) (q : ℤ) + rhoMatrix

@[expose] def rhoMatrix6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0;
    1, 0, 0, 0, 0, 0]

theorem rhoMatrix_eq_rhoMatrix6 : rhoMatrix = rhoMatrix6 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem det_scalar_sub_rhoMatrix6 : ∀ n : Fin 7,
    detLaplace 6 ((Matrix.of fun i j : Fin 6 => if i = j then ((n : ℕ) : ℤ) else 0) -
      rhoMatrix6) = (((n : ℕ) : ℤ) - 1) ^ 4 * (((n : ℕ) : ℤ) + 1) ^ 2 := by
  decide +kernel

theorem natDegree_rhoCharpoly :
    ((Polynomial.X - 1) ^ 4 * (Polynomial.X + 1) ^ 2 : Polynomial ℤ).natDegree ≤ 6 := by
  compute_degree

theorem charpoly_rhoMatrix :
    rhoMatrix.charpoly = (Polynomial.X - 1) ^ 4 * (Polynomial.X + 1) ^ 2 := by
  refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq
    ((Finset.range 7).image (fun n : ℕ => (n : ℤ))) ?_ ?_ ?_
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range,
      Matrix.charpoly_degree_eq_dim]
    change ((6 : ℕ) : WithBot ℕ) < ((7 : ℕ) : WithBot ℕ)
    exact WithBot.coe_lt_coe.2 (by norm_num)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le natDegree_rhoCharpoly)
      (WithBot.coe_lt_coe.2 (by norm_num))
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
    rw [Matrix.eval_charpoly, ← detLaplace_eq_det]
    have h := det_scalar_sub_rhoMatrix6 ⟨n, Finset.mem_range.1 hn⟩
    have e : Matrix.scalar (Fin Tag.E6.rank) (n : ℤ) - rhoMatrix =
        (Matrix.of fun i j : Fin 6 => if i = j then (n : ℤ) else 0) - rhoMatrix6 := by
      rw [rhoMatrix_eq_rhoMatrix6]
      ext i j
      simp only [Matrix.scalar_apply]
      rfl
    rw [e]
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_mul]
    exact h

theorem det_eqpMatrix (q : ℕ) :
    (eqpMatrix q).det = ((q : ℤ) + 1) ^ 4 * ((q : ℤ) - 1) ^ 2 := by
  have h := congrArg (Polynomial.eval (-(q : ℤ))) charpoly_rhoMatrix
  rw [Matrix.eval_charpoly] at h
  have e : Matrix.scalar (Fin Tag.E6.rank) (-(q : ℤ)) - rhoMatrix = -(eqpMatrix q) := by
    rw [eqpMatrix, map_neg, neg_add', sub_eq_add_neg]
  rw [e, Matrix.det_neg, Fintype.card_fin] at h
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_mul] at h
  have h6 : ((-1 : ℤ)) ^ Tag.E6.rank = 1 := by decide
  rw [h6, one_mul] at h
  rw [h]
  ring

section Torus

variable {L : Type} [Field L] {Fr : L →+* L}

theorem rootChar_eqpMatrix_mulVec (q : ℕ)
    (b : Fin Tag.E6.rank → Lˣ) (μ : Fin Tag.E6.rank → ℤ) :
    rootChar b (eqpMatrix q *ᵥ μ) = rootChar b (permLattice e6Rho μ) * rootChar b μ ^ q := by
  rw [eqpMatrix, Matrix.add_mulVec, ← permLattice_eq_mulVec, rootChar_add, mul_comm]
  congr 1
  have : (Matrix.scalar (Fin Tag.E6.rank) (q : ℤ)) *ᵥ μ = (q : ℤ) • μ := by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [this, rootChar_zsmul, zpow_natCast]

theorem mem_twistedTorus_rootDiagUnit_iffQp [IsAlgClosed L] {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (b : Fin Tag.E6.rank → Lˣ) :
    rootDiagUnit Tag.E6 b ∈ twistedTorus (eqpN L) Fr ↔
      b ∈ (monomialHom (G := Lˣ) (eqpMatrix q)ᵀ).ker := by
  rw [mem_ker_monomialHom_iff_forall, mem_twistedTorus]
  refine (and_iff_right (rootDiagUnit_mem_torusGroup b)).trans ?_
  rw [CFSG.RankThree.Chevalley.entrywise_frob_rootDiagUnit Fr hFr, eq_comm]
  refine (rootDiagUnit_eq_conj_canonicalRep_iff (K := L) b (b ^ q) e6W0).trans ?_
  constructor
  · intro h μ
    have h1 := h μ
    rw [e6W0_smul, CFSG.RankThree.Classical2.rootChar_neg',
      CFSG.RankThree.Chevalley.rootChar_pow_tuple] at h1
    rw [rootChar_eqpMatrix_mulVec, ← h1, mul_inv_cancel]
  · intro h v
    have h1 := h v
    rw [rootChar_eqpMatrix_mulVec] at h1
    rw [e6W0_smul, CFSG.RankThree.Classical2.rootChar_neg',
      CFSG.RankThree.Chevalley.rootChar_pow_tuple, inv_eq_iff_mul_eq_one]
    exact h1

theorem odd_eqp_order {q : ℕ} (hq : Even q) (hq1 : 1 ≤ q) : Odd ((q + 1) ^ 4 * (q - 1) ^ 2) := by
  have h1 : Odd (q + 1) := hq.add_one
  have h2 : Odd (q - 1) := by
    obtain ⟨k, hk⟩ := hq
    exact ⟨k - 1, by omega⟩
  exact (h1.pow).mul (h2.pow)

@[expose] def eqpTorusEquiv [IsAlgClosed L] {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) :
    (monomialHom (G := Lˣ) (eqpMatrix q)ᵀ).ker ≃ twistedTorus (eqpN L) Fr :=
  Equiv.ofBijective
    (fun b => ⟨rootDiagUnit Tag.E6 b.1, (mem_twistedTorus_rootDiagUnit_iffQp hFr b.1).2 b.2⟩)
    ⟨fun b c h => Subtype.ext (rootDiagUnit_injective (congrArg Subtype.val h)), fun x => by
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup x.2.1
      refine ⟨⟨b, (mem_twistedTorus_rootDiagUnit_iffQp hFr b).1 ?_⟩, Subtype.ext hb.symm⟩
      rw [← hb]
      exact x.2⟩

theorem natCard_eqpTorus [IsAlgClosed L] {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (hq : (q : L) = 0) (hq1 : 1 ≤ q) :
    Nat.card (twistedTorus (eqpN L) Fr) = (q + 1) ^ 4 * (q - 1) ^ 2 := by
  have hdet : ((eqpMatrix q)ᵀ).det = (((q + 1) ^ 4 * (q - 1) ^ 2 : ℕ) : ℤ) := by
    rw [Matrix.det_transpose, det_eqpMatrix]
    push_cast [Nat.cast_sub hq1]
    ring
  have hne : (((eqpMatrix q)ᵀ).det : L) ≠ 0 := by
    rw [Matrix.det_transpose, det_eqpMatrix]
    push_cast
    rw [hq]
    norm_num
  have h := natCard_ker_monomialHom (Ω := L) (eqpMatrix q)ᵀ hne
  rw [hdet, Int.natAbs_natCast, Nat.card_congr (eqpTorusEquiv hFr)] at h
  exact h

end Torus

end CFSG.RankThree.PartOne.KE6
