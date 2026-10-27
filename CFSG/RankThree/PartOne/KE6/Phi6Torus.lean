module

public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.RankThree.Classical2.TwistedE6Phi3Torus

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
open scoped Matrix

abbrev phi6N (L : Type) [Field L] : ModGL Tag.E6 L :=
  canonicalRep (coxeterSystem Tag.E6) L e6CoxeterSq

@[expose] def phi6Matrix (q : ℕ) : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  coxeterSqMatrix - Matrix.scalar (Fin Tag.E6.rank) (q : ℤ)

theorem det_phi6Matrix (q : ℕ) :
    (phi6Matrix q).det = ((q : ℤ) ^ 2 - q + 1) ^ 2 * ((q : ℤ) ^ 2 + q + 1) := by
  have h := congrArg (Polynomial.eval (q : ℤ)) charpoly_coxeterSqMatrix
  rw [Matrix.eval_charpoly] at h
  have e : phi6Matrix q = -(Matrix.scalar (Fin Tag.E6.rank) (q : ℤ) - coxeterSqMatrix) := by
    rw [phi6Matrix, neg_sub]
  rw [e, Matrix.det_neg, Fintype.card_fin] at *
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_one] at h
  have h6 : ((-1 : ℤ)) ^ Tag.E6.rank = 1 := by decide
  rw [h6, one_mul, h]

section Torus

variable {L : Type} [Field L] {Fr : L →+* L}

theorem rootChar_phi6Matrix_mulVec (q : ℕ)
    (b : Fin Tag.E6.rank → Lˣ) (μ : Fin Tag.E6.rank → ℤ) :
    rootChar b (phi6Matrix q *ᵥ μ) = rootChar b (e6CoxeterSq • μ) * (rootChar b μ ^ q)⁻¹ := by
  rw [phi6Matrix, Matrix.sub_mulVec, ← weylMatrix_e6CoxeterSq, weylMatrix_mulVec,
    rootChar_sub]
  congr 2
  have : (Matrix.scalar (Fin Tag.E6.rank) (q : ℤ)) *ᵥ μ = (q : ℤ) • μ := by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [this, rootChar_zsmul, zpow_natCast]

theorem mem_ker_monomialHom_iff_forall (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ)
    (b : Fin Tag.E6.rank → Lˣ) :
    b ∈ (monomialHom (G := Lˣ) Nᵀ).ker ↔ ∀ μ, rootChar b (N *ᵥ μ) = 1 := by
  have hcol : ∀ j, rootChar b (N *ᵥ Pi.single j 1) =
      (monomialHom (G := Lˣ) Nᵀ b) j := fun j => by
    rw [monomialHom_apply, rootChar]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Matrix.mulVec_single, Matrix.transpose_apply]
  rw [MonoidHom.mem_ker]
  constructor
  · intro h μ
    have hμ : μ = ∑ j, μ j • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hμ, Matrix.mulVec_sum, rootChar_sum]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Matrix.mulVec_smul, rootChar_zsmul, hcol, h, Pi.one_apply, one_zpow]
  · intro h
    funext j
    rw [← hcol, h, Pi.one_apply]

theorem mem_twistedTorus_rootDiagUnit_iff [IsAlgClosed L] {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (b : Fin Tag.E6.rank → Lˣ) :
    rootDiagUnit Tag.E6 b ∈ twistedTorus (phi6N L) Fr ↔
      b ∈ (monomialHom (G := Lˣ) (phi6Matrix q)ᵀ).ker := by
  rw [mem_ker_monomialHom_iff_forall, mem_twistedTorus]
  refine (and_iff_right (rootDiagUnit_mem_torusGroup b)).trans ?_
  rw [CFSG.RankThree.Chevalley.entrywise_frob_rootDiagUnit Fr hFr, eq_comm]
  refine (rootDiagUnit_eq_conj_canonicalRep_iff (K := L) b (b ^ q) e6CoxeterSq).trans ?_
  constructor
  · intro h μ
    rw [rootChar_phi6Matrix_mulVec, ← CFSG.RankThree.Chevalley.rootChar_pow_tuple, h,
      mul_inv_cancel]
  · intro h v
    have h1 := h v
    rw [rootChar_phi6Matrix_mulVec, mul_inv_eq_one,
      ← CFSG.RankThree.Chevalley.rootChar_pow_tuple] at h1
    exact h1

theorem odd_phi6_order (q : ℕ) : Odd ((q ^ 2 - q + 1) ^ 2 * (q ^ 2 + q + 1)) := by
  have h1 : Odd (q ^ 2 + q + 1) := by
    have : q ^ 2 + q = q * (q + 1) := by ring
    rw [this]
    exact (Nat.even_mul_succ_self q).add_one
  have h2 : Odd (q ^ 2 - q + 1) := by
    have : q ^ 2 - q = q * (q - 1) := by rw [sq, Nat.mul_sub_one]
    rw [this]
    exact (Nat.even_mul_pred_self q).add_one
  exact h2.pow.mul h1

@[expose] def phi6TorusEquiv [IsAlgClosed L] {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) :
    (monomialHom (G := Lˣ) (phi6Matrix q)ᵀ).ker ≃ twistedTorus (phi6N L) Fr :=
  Equiv.ofBijective
    (fun b => ⟨rootDiagUnit Tag.E6 b.1, (mem_twistedTorus_rootDiagUnit_iff hFr b.1).2 b.2⟩)
    ⟨fun b c h => Subtype.ext (rootDiagUnit_injective (congrArg Subtype.val h)), fun x => by
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup x.2.1
      refine ⟨⟨b, (mem_twistedTorus_rootDiagUnit_iff hFr b).1 ?_⟩, Subtype.ext hb.symm⟩
      rw [← hb]
      exact x.2⟩

theorem coe_phi6TorusEquiv [IsAlgClosed L] {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (b : (monomialHom (G := Lˣ) (phi6Matrix q)ᵀ).ker) :
    ((phi6TorusEquiv hFr b : twistedTorus (phi6N L) Fr) : ModGL Tag.E6 L) =
      rootDiagUnit Tag.E6 b.1 :=
  rfl

theorem natCard_phi6Torus [IsAlgClosed L] {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (hq : (q : L) = 0) :
    Nat.card (twistedTorus (phi6N L) Fr) = (q ^ 2 - q + 1) ^ 2 * (q ^ 2 + q + 1) ∧
      Odd (Nat.card (twistedTorus (phi6N L) Fr)) := by
  have hle : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hdet : ((phi6Matrix q)ᵀ).det = (((q ^ 2 - q + 1) ^ 2 * (q ^ 2 + q + 1) : ℕ) : ℤ) := by
    rw [Matrix.det_transpose, det_phi6Matrix]
    push_cast [hle]
    ring
  have hne : (((phi6Matrix q)ᵀ).det : L) ≠ 0 := by
    rw [Matrix.det_transpose, det_phi6Matrix]
    push_cast
    rw [hq]
    norm_num
  have h := natCard_ker_monomialHom (Ω := L) (phi6Matrix q)ᵀ hne
  rw [hdet, Int.natAbs_natCast, Nat.card_congr (phi6TorusEquiv hFr)] at h
  exact ⟨h, h ▸ odd_phi6_order q⟩

end Torus

end CFSG.RankThree.PartOne.KE6
