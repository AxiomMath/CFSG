module

public import CFSG.RankThree.PartOne.KE6.Tw6Transport

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
open scoped Matrix

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

@[expose] def tw6Matrix (q : ℕ) : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  Matrix.scalar (Fin Tag.E6.rank) (q : ℤ) + e6T3Matrix

theorem det_tw6Matrix (q : ℕ) : (tw6Matrix q).det = ((q : ℤ) ^ 2 - q + 1) ^ 3 :=
  det_scalar_add_e6T3Matrix q

theorem rootChar_tw6Matrix_mulVec (q : ℕ) (b : Fin Tag.E6.rank → Ωˣ)
    (μ : Fin Tag.E6.rank → ℤ) :
    rootChar b (tw6Matrix q *ᵥ μ) = rootChar b (e6T3W • μ) * rootChar b μ ^ q := by
  rw [tw6Matrix, Matrix.add_mulVec, ← weylMatrix_e6T3W_eq, weylMatrix_mulVec, rootChar_add,
    mul_comm]
  congr 1
  have : (Matrix.scalar (Fin Tag.E6.rank) (q : ℤ)) *ᵥ μ = (q : ℤ) • μ := by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [this, rootChar_zsmul, zpow_natCast]

theorem mem_twistedTorus_rootDiagUnit_iff6 [IsAlgClosed Ω] {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (b : Fin Tag.E6.rank → Ωˣ) :
    rootDiagUnit Tag.E6 b ∈ twistedTorusOf (tw6N Ω) (twistE6 Ω Fr) ↔
      b ∈ (monomialHom (G := Ωˣ) (tw6Matrix q)ᵀ).ker := by
  have hb' : (fun i => Units.map Fr.toMonoidHom (b (e6Rho.symm i))) =
      (fun i => b (e6Rho.symm i)) ^ q := by
    funext i
    refine Units.ext ?_
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, hFr]
    rfl
  rw [mem_ker_monomialHom_iff_forall, mem_twistedTorusOf]
  refine (and_iff_right (rootDiagUnit_mem_torusGroup b)).trans ?_
  rw [twistE6_rootDiagUnit, hb', eq_comm, rootDiagUnit_eq_conj_canonicalRep_iff]
  have hrr : ∀ x : Fin Tag.E6.rank → ℤ, permLattice e6Rho (permLattice e6Rho x) = x := by
    intro x
    funext i
    simp only [permLattice, Function.comp_apply]
    rw [CFSG.RankThree.Classical2.e6Rho_symm, show e6Rho (e6Rho i) = i by revert i; decide]
  have hchar : ∀ v, rootChar ((fun i => b (e6Rho.symm i)) ^ q) v =
      rootChar b (permLattice e6Rho v) ^ q := by
    intro v
    rw [CFSG.RankThree.Chevalley.rootChar_pow_tuple, ← rootChar_permLattice, CFSG.RankThree.Classical2.e6Rho_symm]
  constructor
  · intro h μ
    have h1 := h (permLattice e6Rho μ)
    rw [tw6W_smul, hrr, hchar, hrr, CFSG.RankThree.Classical2.rootChar_neg'] at h1
    rw [rootChar_tw6Matrix_mulVec, ← h1, mul_inv_cancel]
  · intro h v
    rw [tw6W_smul, hchar, CFSG.RankThree.Classical2.rootChar_neg', inv_eq_iff_mul_eq_one]
    have h1 := h (permLattice e6Rho v)
    rw [rootChar_tw6Matrix_mulVec] at h1
    exact h1

theorem odd_tw6_order (q : ℕ) : Odd ((q ^ 2 - q + 1) ^ 3) := by
  have h2 : Odd (q ^ 2 - q + 1) := by
    have : q ^ 2 - q = q * (q - 1) := by rw [sq, Nat.mul_sub_one]
    rw [this]
    exact (Nat.even_mul_pred_self q).add_one
  exact h2.pow

@[expose] def tw6TorusEquiv [IsAlgClosed Ω] {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) :
    (monomialHom (G := Ωˣ) (tw6Matrix q)ᵀ).ker ≃ twistedTorusOf (tw6N Ω) (twistE6 Ω Fr) :=
  Equiv.ofBijective
    (fun b => ⟨rootDiagUnit Tag.E6 b.1, (mem_twistedTorus_rootDiagUnit_iff6 hFr b.1).2 b.2⟩)
    ⟨fun b c h => Subtype.ext (rootDiagUnit_injective (congrArg Subtype.val h)), fun x => by
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup x.2.1
      refine ⟨⟨b, (mem_twistedTorus_rootDiagUnit_iff6 hFr b).1 ?_⟩, Subtype.ext hb.symm⟩
      rw [← hb]
      exact x.2⟩

theorem natCard_tw6Torus [IsAlgClosed Ω] {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (hq : (q : Ω) = 0) :
    Nat.card (twistedTorusOf (tw6N Ω) (twistE6 Ω Fr)) = (q ^ 2 - q + 1) ^ 3 ∧
      Odd (Nat.card (twistedTorusOf (tw6N Ω) (twistE6 Ω Fr))) := by
  have hle : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hdet : ((tw6Matrix q)ᵀ).det = (((q ^ 2 - q + 1) ^ 3 : ℕ) : ℤ) := by
    rw [Matrix.det_transpose, det_tw6Matrix]
    push_cast [Nat.cast_sub hle]
    ring
  have hne : (((tw6Matrix q)ᵀ).det : Ω) ≠ 0 := by
    rw [Matrix.det_transpose, det_tw6Matrix]
    push_cast
    rw [hq]
    norm_num
  have h := natCard_ker_monomialHom (Ω := Ω) (tw6Matrix q)ᵀ hne
  rw [hdet, Int.natAbs_natCast, Nat.card_congr (tw6TorusEquiv hFr)] at h
  exact ⟨h, h ▸ odd_tw6_order q⟩

end CFSG.RankThree.PartOne.KE6
