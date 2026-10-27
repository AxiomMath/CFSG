module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType.RCKRP

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Universal.Unitary
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

private lemma antidiag_mul_self_aux {K : Type} [Field K] (n : ℕ) :
    (antidiag n : Matrix (Fin n) (Fin n) K) * antidiag n = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev a)]
  · simp only [antidiag, of_apply, ↓reduceIte, one_mul, Fin.rev_rev, Matrix.one_apply]
    by_cases h : b = a
    · simp [h]
    · simp [h, Ne.symm h]
  · intro c _ hc
    simp [antidiag, hc]
  · simp

private lemma antidiag_mul_single_mul_antidiag {K : Type} [Field K] {n : ℕ} (a b : Fin n) (t : K) :
    (antidiag n : Matrix (Fin n) (Fin n) K) * single a b t * antidiag n =
      single (Fin.rev a) (Fin.rev b) t := by
  rw [Matrix.mul_assoc, single_mul_antidiag, antidiag_mul_single]

private lemma coe_inv_of_smul_GL {K : Type} [Field K] {n : ℕ}
    (Q : GL (Fin n) K) (lam : K) (hlam : lam ≠ 0)
    (Qtilde : Matrix.SpecialLinearGroup (Fin n) K)
    (hQtilde : (Qtilde : Matrix (Fin n) (Fin n) K) = lam • (Q : Matrix (Fin n) (Fin n) K)) :
    ((Qtilde⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      lam⁻¹ • ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  let B : Matrix (Fin n) (Fin n) K := lam⁻¹ • ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hB_left : B * (Qtilde : Matrix (Fin n) (Fin n) K) = 1 := by
    calc B * (Qtilde : Matrix (Fin n) (Fin n) K)
        = (lam⁻¹ • ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            (lam • ((Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by dsimp [B]; rw [hQtilde]
      _ = lam • ((lam⁻¹ • ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            ((Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [Matrix.mul_smul]
      _ = lam • (lam⁻¹ • (((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by rw [Matrix.smul_mul]
      _ = (lam * lam⁻¹) • (((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by rw [smul_smul]
      _ = 1 • 1 := by
        rw [one_smul, mul_inv_cancel₀ hlam, one_smul,
          ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
      _ = 1 := by rw [one_smul]
  calc ((Qtilde⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = 1 * ((Qtilde⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [one_mul]
    _ = (B * (Qtilde : Matrix (Fin n) (Fin n) K)) *
          ((Qtilde⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [hB_left]
    _ = B * ((Qtilde : Matrix (Fin n) (Fin n) K) *
          ((Qtilde⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        rw [Matrix.mul_assoc]
    _ = B * 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one]
    _ = B := by rw [Matrix.mul_one]

private lemma conj_transvection_stdUnitary {K : Type} [Field K] {n : ℕ}
    (σ : K ≃+* K) (Q : GL (Fin n) K) (lam : K) (hlam : lam ≠ 0)
    (Qtilde : Matrix.SpecialLinearGroup (Fin n) K)
    (hQtilde : (Qtilde : Matrix (Fin n) (Fin n) K) = lam • (Q : Matrix (Fin n) (Fin n) K))
    (hQ : ((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K))ᵀ *
      (Q : Matrix (Fin n) (Fin n) K) = antidiag n)
    {a b : Fin n} (hab : a ≠ b) (hba : Fin.rev a ≠ Fin.rev b) (t : K) :
    ((stdUnitary (σ : K →+* K) Qtilde * Matrix.SpecialLinearGroup.transvection hab t *
        (stdUnitary (σ : K →+* K) Qtilde)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      ((Qtilde * Matrix.SpecialLinearGroup.transvection hba t *
        Qtilde⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  let c : K := (σ lam)⁻¹
  have hc : c ≠ 0 := by
    dsimp [c]
    exact inv_ne_zero (by simpa using σ.injective.ne hlam)
  have hQtilde_inv := coe_inv_of_smul_GL Q lam hlam Qtilde hQtilde
  have hQmap_inv : ((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K))⁻¹ =
      (((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (σ : K →+* K)) := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one]
    simp [Matrix.map_one, map_zero, map_one]
  have hQinv_transpose : (((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K))⁻¹)ᵀ =
      (Q : Matrix (Fin n) (Fin n) K) * antidiag n := by
    have h1 : ((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K))ᵀ *
        ((Q : Matrix (Fin n) (Fin n) K) * antidiag n) = 1 := by
      rw [← Matrix.mul_assoc, hQ, antidiag_mul_self_aux]
    have h2 : (((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K))ᵀ)⁻¹ =
        (Q : Matrix (Fin n) (Fin n) K) * antidiag n := Matrix.inv_eq_right_inv h1
    have h3 : (((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K))⁻¹)ᵀ =
        (((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K))ᵀ)⁻¹ := by
      have h4 : ((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K))ᵀ *
          (((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K))⁻¹)ᵀ = 1 := by
        rw [← Matrix.transpose_mul]
        have h5 : ((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K))⁻¹ *
            ((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K)) = 1 := by
          rw [hQmap_inv, ← Matrix.map_mul, ← Matrix.GeneralLinearGroup.coe_mul,
            inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
          simp [Matrix.map_one, map_zero, map_one]
        rw [h5, Matrix.transpose_one]
      exact (Matrix.inv_eq_right_inv h4).symm
    rw [h3, h2]
  have hmap_smul : ((lam • (Q : Matrix (Fin n) (Fin n) K)).map (σ : K →+* K)) =
      σ lam • ((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K)) := by
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, map_mul]
  have hstd : ((stdUnitary (σ : K →+* K) Qtilde : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = c • ((Q : Matrix (Fin n) (Fin n) K) * antidiag n) := by
    rw [coe_stdUnitary, hQtilde, hmap_smul]
    have hsmul_inv : (((σ lam) • ((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K)))⁻¹) =
        (σ lam)⁻¹ • (((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K))⁻¹) := by
      apply Matrix.inv_eq_right_inv
      calc (((σ lam) • ((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K))) *
            ((σ lam)⁻¹ • (((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K))⁻¹)))
          = ((σ lam) * (σ lam)⁻¹) •
              (((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K)) *
                (((Q : Matrix (Fin n) (Fin n) K).map (σ : K →+* K))⁻¹)) := by
              rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = 1 • 1 := by
              rw [mul_inv_cancel₀ (by simpa using σ.injective.ne hlam)]
              rw [hQmap_inv, ← Matrix.map_mul, ← Matrix.GeneralLinearGroup.coe_mul,
                mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
              simp [Matrix.map_one, map_zero, map_one]
        _ = 1 := by rw [one_smul]
    rw [hsmul_inv, Matrix.transpose_smul, hQinv_transpose]
  have hstd_inv : (((stdUnitary (σ : K →+* K) Qtilde)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      c⁻¹ • (antidiag n * ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    let B : Matrix (Fin n) (Fin n) K :=
      c⁻¹ • (antidiag n * ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    have hB_left : B * ((stdUnitary (σ : K →+* K) Qtilde : Matrix.SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 := by
      calc B * ((stdUnitary (σ : K →+* K) Qtilde : Matrix.SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K)
          = (c⁻¹ • (antidiag n * ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) *
              (c • ((Q : Matrix (Fin n) (Fin n) K) * antidiag n)) := by dsimp [B]; rw [hstd]
        _ = c • ((c⁻¹ • (antidiag n * ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) *
              ((Q : Matrix (Fin n) (Fin n) K) * antidiag n)) := by rw [Matrix.mul_smul]
        _ = c • (c⁻¹ • ((antidiag n * ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
              ((Q : Matrix (Fin n) (Fin n) K) * antidiag n))) := by rw [Matrix.smul_mul]
        _ = (c * c⁻¹) • ((antidiag n * ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
              ((Q : Matrix (Fin n) (Fin n) K) * antidiag n)) := by rw [smul_smul]
        _ = 1 • 1 := by
              rw [one_smul, mul_inv_cancel₀ hc, one_smul]
              rw [← Matrix.mul_assoc]
              conv_lhs => arg 1; rw [Matrix.mul_assoc]
              rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
                Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one, antidiag_mul_self_aux]
        _ = 1 := by rw [one_smul]
    calc (((stdUnitary (σ : K →+* K) Qtilde)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K)
        = 1 * (((stdUnitary (σ : K →+* K) Qtilde)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) := by rw [one_mul]
      _ = (B * ((stdUnitary (σ : K →+* K) Qtilde : Matrix.SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K)) *
            (((stdUnitary (σ : K →+* K) Qtilde)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
              Matrix (Fin n) (Fin n) K) := by rw [hB_left]
      _ = B * (((stdUnitary (σ : K →+* K) Qtilde : Matrix.SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) *
            (((stdUnitary (σ : K →+* K) Qtilde)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
              Matrix (Fin n) (Fin n) K)) := by rw [Matrix.mul_assoc]
      _ = B * 1 := by
            rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
              Matrix.SpecialLinearGroup.coe_one]
      _ = B := by rw [Matrix.mul_one]
  calc ((stdUnitary (σ : K →+* K) Qtilde * Matrix.SpecialLinearGroup.transvection hab t *
        (stdUnitary (σ : K →+* K) Qtilde)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)
      = ((stdUnitary (σ : K →+* K) Qtilde : Matrix.SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *
        ((Matrix.SpecialLinearGroup.transvection hab t : Matrix.SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *
        (((stdUnitary (σ : K →+* K) Qtilde)⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) := by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    _ = (c • ((Q : Matrix (Fin n) (Fin n) K) * antidiag n)) *
          (1 + single a b t) *
          (c⁻¹ • (antidiag n * ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by
        rw [hstd, hstd_inv, Matrix.SpecialLinearGroup.transvection_coe]
    _ = ((Q : Matrix (Fin n) (Fin n) K) * antidiag n) *
          (1 + single a b t) *
          (antidiag n * ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc,
          one_smul]
    _ = ((Q : Matrix (Fin n) (Fin n) K) *
          (1 + single (Fin.rev a) (Fin.rev b) t) *
          ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        rw [Matrix.mul_add, Matrix.add_mul]
        conv_lhs =>
          arg 1
          rw [show (Q : Matrix (Fin n) (Fin n) K) * antidiag n * 1 *
                (antidiag n * ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
              (Q : Matrix (Fin n) (Fin n) K) * (antidiag n * antidiag n) *
                ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) from by noncomm_ring]
        conv_lhs =>
          arg 2
          rw [show (Q : Matrix (Fin n) (Fin n) K) * antidiag n * single a b t *
                (antidiag n * ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
              (Q : Matrix (Fin n) (Fin n) K) *
                (antidiag n * single a b t * antidiag n) *
                ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) from by noncomm_ring]
        rw [antidiag_mul_self_aux n, antidiag_mul_single_mul_antidiag a b t]
        noncomm_ring
    _ = ((Qtilde * Matrix.SpecialLinearGroup.transvection hba t *
        Qtilde⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          hQtilde, hQtilde_inv, Matrix.SpecialLinearGroup.transvection_coe]
        rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hlam,
          one_smul]

private lemma coe_mul_transvection_mul_inv {K : Type} [Field K] {n : ℕ}
    (Q : GL (Fin n) K) (lam : K) (hlam : lam ≠ 0)
    (Qtilde : Matrix.SpecialLinearGroup (Fin n) K)
    (hQtilde : (Qtilde : Matrix (Fin n) (Fin n) K) = lam • (Q : Matrix (Fin n) (Fin n) K))
    {a b : Fin n} (hab : a ≠ b) (t : K) :
    ((Qtilde * Matrix.SpecialLinearGroup.transvection hab t * Qtilde⁻¹ :
        Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (Q : Matrix (Fin n) (Fin n) K) * (1 + single a b t) *
        ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    hQtilde, coe_inv_of_smul_GL Q lam hlam Qtilde hQtilde,
    Matrix.SpecialLinearGroup.transvection_coe]
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hlam, one_smul]

theorem rckSU_pair_of_witt
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (step : ModGL τ L →* ModGL τ L) {ν : ℕ} (hν : 2 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σf : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σf)
    (σQ : L ≃+* L) {H : Subgroup (ModGL τ L)} {z : ModGL τ L} (hz : z ∈ H) (hψH : ψ.range ≤ H)
    (hconj : ∀ X : SL(ν, L), step (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹)
    (Q : GL (Fin ν) L)
    (hQ : ((Q : Matrix (Fin ν) (Fin ν) L).map σQ)ᵀ * (Q : Matrix (Fin ν) (Fin ν) L) =
      antidiag ν) :
    ∃ y ∈ H,
      ((rootSubgroup τ L (σf ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩))).map
          (MulAut.conj y).toMonoidHom).map step =
        (rootSubgroup τ L (σf ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩))).map
          (MulAut.conj y).toMonoidHom ∧
      ((rootSubgroup τ L (-σf ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩))).map
          (MulAut.conj y).toMonoidHom).map step =
        (rootSubgroup τ L (-σf ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩))).map
          (MulAut.conj y).toMonoidHom ∧
      (∀ g : ModGL τ L,
        g ∈ (rootSubgroup τ L (σf ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩))).map
            (MulAut.conj y).toMonoidHom ⊓ step.eqLocus (MonoidHom.id _) ↔
          ∃ s : L, s + σQ s = 0 ∧ ∃ X : SL(ν, L),
            (X : Matrix (Fin ν) (Fin ν) L) = (Q : Matrix (Fin ν) (Fin ν) L) *
              (1 + single ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩) s) *
                ((Q⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) ∧
            g = z * ψ X * z⁻¹) ∧
      (∀ g : ModGL τ L,
        g ∈ (rootSubgroup τ L (-σf ⟨0, by omega⟩ (Fin.rev ⟨0, by omega⟩))).map
            (MulAut.conj y).toMonoidHom ⊓ step.eqLocus (MonoidHom.id _) ↔
          ∃ s : L, s + σQ s = 0 ∧ ∃ X : SL(ν, L),
            (X : Matrix (Fin ν) (Fin ν) L) = (Q : Matrix (Fin ν) (Fin ν) L) *
              (1 + single (Fin.rev ⟨0, by omega⟩) ⟨0, by omega⟩ s) *
                ((Q⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) ∧
            g = z * ψ X * z⁻¹) := by
  classical
  let e0 : Fin ν := ⟨0, by omega⟩
  let elast : Fin ν := Fin.rev e0
  have h0l : e0 ≠ elast := by
    intro h
    have := congrArg Fin.val h
    simp [e0, elast] at this
    omega
  let γ : Fin τ.rank → ℤ := σf e0 elast
  let γ' : Fin τ.rank → ℤ := σf elast e0
  have hγ' : γ' = -γ := by
    simp [γ, γ', hψ.neg elast e0]
  obtain ⟨ε, hε⟩ := hψ.transv e0 elast h0l
  obtain ⟨ε', hε'⟩ := hψ.transv elast e0 h0l.symm
  have hνpos : 0 < ν := by omega
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq (((Q : Matrix (Fin ν) (Fin ν) L).det)⁻¹) hνpos
  have hdetQ : (Q : Matrix (Fin ν) (Fin ν) L).det ≠ 0 := by
    apply Matrix.det_ne_zero_of_right_inverse
      (B := ((Q⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L))
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hlamne : lam ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_of_gt hνpos)] at hlam
    exact (inv_ne_zero hdetQ) hlam.symm
  have hdetQtilde : (lam • (Q : Matrix (Fin ν) (Fin ν) L)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hlam, inv_mul_cancel₀ hdetQ]
  let Qtilde : SL(ν, L) := ⟨lam • (Q : Matrix (Fin ν) (Fin ν) L), hdetQtilde⟩
  have hQtilde : (Qtilde : Matrix (Fin ν) (Fin ν) L) = lam • (Q : Matrix (Fin ν) (Fin ν) L) := rfl
  let y : ModGL τ L := z * ψ Qtilde
  have hy : y ∈ H :=
    mul_mem hz (hψH ⟨Qtilde, rfl⟩)
  have hkey_high : ∀ s : L,
      stdUnitary σQ.toRingHom (Qtilde * Matrix.SpecialLinearGroup.transvection h0l s *
        Qtilde⁻¹) =
      Qtilde * Matrix.SpecialLinearGroup.transvection h0l (-(σQ s)) * Qtilde⁻¹ := by
    intro s
    have h1 := conj_transvection_stdUnitary σQ Q lam hlamne Qtilde hQtilde hQ h0l.symm
      (Fin.rev_injective.ne h0l.symm) (-(σQ s))
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv, stdUnitary_transvection]
    have htrans : Matrix.SpecialLinearGroup.transvection (Fin.rev_injective.ne h0l.symm) (-(σQ s)) =
        Matrix.SpecialLinearGroup.transvection h0l (-(σQ s)) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
      rw [show elast.rev = e0 from Fin.rev_rev e0, show e0.rev = elast from rfl]
    simpa [htrans] using h1
  have hkey_low : ∀ s : L,
      stdUnitary σQ.toRingHom (Qtilde * Matrix.SpecialLinearGroup.transvection h0l.symm s *
        Qtilde⁻¹) =
      Qtilde * Matrix.SpecialLinearGroup.transvection h0l.symm (-(σQ s)) *
        Qtilde⁻¹ := by
    intro s
    have h1 := conj_transvection_stdUnitary σQ Q lam hlamne Qtilde hQtilde hQ h0l
      (Fin.rev_injective.ne h0l) (-(σQ s))
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv, stdUnitary_transvection]
    have htrans : Matrix.SpecialLinearGroup.transvection (Fin.rev_injective.ne h0l) (-(σQ s)) =
        Matrix.SpecialLinearGroup.transvection h0l.symm (-(σQ s)) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
      rw [show e0.rev = elast from rfl, show elast.rev = e0 from Fin.rev_rev e0]
    simpa [htrans] using h1
  have hy_formula : ∀ s : L, y * pinnedX τ L γ ((ε : L) * s) * y⁻¹ =
      z * ψ (Qtilde * Matrix.SpecialLinearGroup.transvection h0l s * Qtilde⁻¹) * z⁻¹ := by
    intro s
    rw [show y = z * ψ Qtilde from rfl, ← hε s]
    rw [map_mul, map_mul, map_inv]
    group
  have hy_formula_low : ∀ s : L, y * pinnedX τ L γ' ((ε' : L) * s) * y⁻¹ =
      z * ψ (Qtilde * Matrix.SpecialLinearGroup.transvection h0l.symm s * Qtilde⁻¹) * z⁻¹ := by
    intro s
    rw [show y = z * ψ Qtilde from rfl, ← hε' s]
    rw [map_mul, map_mul, map_inv]
    group
  have hstep_high : ∀ s : L, step (y * pinnedX τ L γ ((ε : L) * s) * y⁻¹) =
      y * pinnedX τ L γ ((ε : L) * (-(σQ s))) * y⁻¹ := by
    intro s
    rw [hy_formula s, hconj (Qtilde * Matrix.SpecialLinearGroup.transvection h0l s * Qtilde⁻¹),
      hkey_high s, ← hy_formula (-(σQ s))]
  have hstep_low : ∀ s : L, step (y * pinnedX τ L γ' ((ε' : L) * s) * y⁻¹) =
      y * pinnedX τ L γ' ((ε' : L) * (-(σQ s))) * y⁻¹ := by
    intro s
    rw [hy_formula_low s,
      hconj (Qtilde * Matrix.SpecialLinearGroup.transvection h0l.symm s * Qtilde⁻¹),
      hkey_low s, ← hy_formula_low (-(σQ s))]
  have hstab_high : ((rootSubgroup τ L γ).map (MulAut.conj y).toMonoidHom).map step =
      (rootSubgroup τ L γ).map (MulAut.conj y).toMonoidHom := by
    apply le_antisymm
    · intro g hg
      obtain ⟨u, hu, hgu⟩ := Subgroup.mem_map.1 hg
      obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 hu
      obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hv
      set s' : L := (ε⁻¹ : Lˣ) * s
      have hs' : pinnedX τ L γ ((ε : L) * s') = v := by
        simpa [s'] using hs
      refine Subgroup.mem_map.2 ⟨pinnedX τ L γ ((ε : L) * (-(σQ s'))),
        Subgroup.subset_closure ⟨_, rfl⟩, ?_⟩
      rw [← hgu, ← hvu, ← hs']
      exact (hstep_high s').symm
    · intro g hg
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hg
      obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hu
      set s'' : L := (ε⁻¹ : Lˣ) * s
      have hs'' : pinnedX τ L γ ((ε : L) * s'') = u := by
        simpa [s''] using hs
      set s' : L := σQ.symm (-s'')
      have hneg : -(σQ s') = s'' := by
        simp [s', σQ.apply_symm_apply]
      refine Subgroup.mem_map.2 ⟨(MulAut.conj y) (pinnedX τ L γ ((ε : L) * s')), ?_, ?_⟩
      · exact Subgroup.mem_map.2 ⟨pinnedX τ L γ ((ε : L) * s'),
          Subgroup.subset_closure ⟨_, rfl⟩, rfl⟩
      · change step (y * pinnedX τ L γ ((ε : L) * s') * y⁻¹) = y * u * y⁻¹
        rw [hstep_high s', hneg, hs'']
  have hstab_low : ((rootSubgroup τ L γ').map (MulAut.conj y).toMonoidHom).map step =
      (rootSubgroup τ L γ').map (MulAut.conj y).toMonoidHom := by
    apply le_antisymm
    · intro g hg
      obtain ⟨u, hu, hgu⟩ := Subgroup.mem_map.1 hg
      obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 hu
      obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hv
      set s' : L := ((ε' : Lˣ)⁻¹ : Lˣ) * s
      have hs' : pinnedX τ L γ' ((ε' : L) * s') = v := by
        simpa [s'] using hs
      refine Subgroup.mem_map.2 ⟨pinnedX τ L γ' ((ε' : L) * (-(σQ s'))),
        Subgroup.subset_closure ⟨_, rfl⟩, ?_⟩
      rw [← hgu, ← hvu, ← hs']
      exact (hstep_low s').symm
    · intro g hg
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hg
      obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hu
      set s'' : L := ((ε' : Lˣ)⁻¹ : Lˣ) * s
      have hs'' : pinnedX τ L γ' ((ε' : L) * s'') = u := by
        simpa [s''] using hs
      set s' : L := σQ.symm (-s'')
      have hneg : -(σQ s') = s'' := by
        simp [s', σQ.apply_symm_apply]
      refine Subgroup.mem_map.2 ⟨(MulAut.conj y) (pinnedX τ L γ' ((ε' : L) * s')), ?_, ?_⟩
      · exact Subgroup.mem_map.2 ⟨pinnedX τ L γ' ((ε' : L) * s'),
          Subgroup.subset_closure ⟨_, rfl⟩, rfl⟩
      · change step (y * pinnedX τ L γ' ((ε' : L) * s') * y⁻¹) = y * u * y⁻¹
        rw [hstep_low s', hneg, hs'']
  refine ⟨y, hy, ?_, ?_, ?_, ?_⟩
  ·
    change ((rootSubgroup τ L (σf e0 elast)).map (MulAut.conj y).toMonoidHom).map step =
      (rootSubgroup τ L (σf e0 elast)).map (MulAut.conj y).toMonoidHom
    exact hstab_high
  · change ((rootSubgroup τ L (-σf e0 elast)).map (MulAut.conj y).toMonoidHom).map step =
      (rootSubgroup τ L (-σf e0 elast)).map (MulAut.conj y).toMonoidHom
    rw [← hγ']
    exact hstab_low
  · intro g
    constructor
    · intro hg
      have hgU : g ∈ (rootSubgroup τ L γ).map (MulAut.conj y).toMonoidHom := hg.1
      have hgfix : step g = g := hg.2
      obtain ⟨u, hu, hgu⟩ := Subgroup.mem_map.1 hgU
      obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hu
      set s'' : L := (ε⁻¹ : Lˣ) * s
      have hs'' : pinnedX τ L γ ((ε : L) * s'') = u := by
        simpa [s''] using hs
      have hgu' : g = y * pinnedX τ L γ ((ε : L) * s'') * y⁻¹ := by
        rw [← hgu]
        change (MulAut.conj y) u = y * pinnedX τ L γ ((ε : L) * s'') * y⁻¹
        rw [MulAut.conj_apply, ← hs'']
      have hstepg : step g = y * pinnedX τ L γ ((ε : L) * (-(σQ s''))) * y⁻¹ := by
        rw [hgu', hstep_high s'']
      have heq : pinnedX τ L γ ((ε : L) * (-(σQ s''))) =
          pinnedX τ L γ ((ε : L) * s'') := by
        have h1 : y * pinnedX τ L γ ((ε : L) * (-(σQ s''))) * y⁻¹ =
            y * pinnedX τ L γ ((ε : L) * s'') * y⁻¹ := by
          rw [← hstepg, hgfix, hgu']
        have h2 : y * pinnedX τ L γ ((ε : L) * (-(σQ s''))) =
            y * pinnedX τ L γ ((ε : L) * s'') := mul_right_cancel h1
        exact mul_left_cancel h2
      have hεeq : (ε : L) * (-(σQ s'')) = (ε : L) * s'' := pinnedX_injective τ L γ heq
      have hεne : (ε : L) ≠ 0 := by exact_mod_cast ε.ne_zero
      have hsadd : s'' + σQ s'' = 0 := by
        have hneg : -(σQ s'') = s'' := mul_left_cancel₀ hεne hεeq
        have hσ : σQ s'' = -s'' := by rw [← neg_neg (σQ s''), hneg]
        rw [hσ, add_neg_cancel]
      refine ⟨s'', hsadd, Qtilde * Matrix.SpecialLinearGroup.transvection h0l s'' * Qtilde⁻¹,
        ?_, ?_⟩
      ·
        rw [coe_mul_transvection_mul_inv Q lam hlamne Qtilde hQtilde h0l s'']
      ·
        rw [hgu', hy_formula s'']
    · rintro ⟨s, hsadd, X, hXmat, hgX⟩
      have hX : X = Qtilde * Matrix.SpecialLinearGroup.transvection h0l s * Qtilde⁻¹ := by
        apply Subtype.ext
        rw [hXmat, coe_mul_transvection_mul_inv Q lam hlamne Qtilde hQtilde h0l s]
      have hgU : g ∈ (rootSubgroup τ L γ).map (MulAut.conj y).toMonoidHom := by
        rw [hgX, hX, ← hy_formula s]
        exact Subgroup.mem_map.2 ⟨pinnedX τ L γ ((ε : L) * s),
          Subgroup.subset_closure ⟨_, rfl⟩, rfl⟩
      have hfix : step g = g := by
        have hneg : -σQ s = s := by
          have hσ : σQ s = -s := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hsadd)
          rw [hσ, neg_neg]
        rw [hgX, hX, ← hy_formula s, hstep_high s, hneg]
      exact ⟨hgU, hfix⟩
  · rw [← hγ']
    intro g
    constructor
    · intro hg
      have hgU : g ∈ (rootSubgroup τ L γ').map (MulAut.conj y).toMonoidHom := hg.1
      have hgfix : step g = g := hg.2
      obtain ⟨u, hu, hgu⟩ := Subgroup.mem_map.1 hgU
      obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hu
      set s'' : L := ((ε' : Lˣ)⁻¹ : Lˣ) * s
      have hs'' : pinnedX τ L γ' ((ε' : L) * s'') = u := by
        simpa [s''] using hs
      have hgu' : g = y * pinnedX τ L γ' ((ε' : L) * s'') * y⁻¹ := by
        rw [← hgu]
        change (MulAut.conj y) u = y * pinnedX τ L γ' ((ε' : L) * s'') * y⁻¹
        rw [MulAut.conj_apply, ← hs'']
      have hstepg : step g = y * pinnedX τ L γ' ((ε' : L) * (-(σQ s''))) * y⁻¹ := by
        rw [hgu', hstep_low s'']
      have heq : pinnedX τ L γ' ((ε' : L) * (-(σQ s''))) =
          pinnedX τ L γ' ((ε' : L) * s'') := by
        have h1 : y * pinnedX τ L γ' ((ε' : L) * (-(σQ s''))) * y⁻¹ =
            y * pinnedX τ L γ' ((ε' : L) * s'') * y⁻¹ := by
          rw [← hstepg, hgfix, hgu']
        have h2 : y * pinnedX τ L γ' ((ε' : L) * (-(σQ s''))) =
            y * pinnedX τ L γ' ((ε' : L) * s'') := mul_right_cancel h1
        exact mul_left_cancel h2
      have hεeq : (ε' : L) * (-(σQ s'')) = (ε' : L) * s'' := pinnedX_injective τ L γ' heq
      have hεne : (ε' : L) ≠ 0 := by exact_mod_cast ε'.ne_zero
      have hsadd : s'' + σQ s'' = 0 := by
        have hneg : -(σQ s'') = s'' := mul_left_cancel₀ hεne hεeq
        have hσ : σQ s'' = -s'' := by rw [← neg_neg (σQ s''), hneg]
        rw [hσ, add_neg_cancel]
      refine ⟨s'', hsadd, Qtilde * Matrix.SpecialLinearGroup.transvection h0l.symm s'' * Qtilde⁻¹,
        ?_, ?_⟩
      · rw [coe_mul_transvection_mul_inv Q lam hlamne Qtilde hQtilde h0l.symm s'']
      · rw [hgu', hy_formula_low s'']
    · rintro ⟨s, hsadd, X, hXmat, hgX⟩
      have hX : X = Qtilde * Matrix.SpecialLinearGroup.transvection h0l.symm s * Qtilde⁻¹ := by
        apply Subtype.ext
        rw [hXmat, coe_mul_transvection_mul_inv Q lam hlamne Qtilde hQtilde h0l.symm s]
      have hgU : g ∈ (rootSubgroup τ L γ').map (MulAut.conj y).toMonoidHom := by
        rw [hgX, hX, ← hy_formula_low s]
        exact Subgroup.mem_map.2 ⟨pinnedX τ L γ' ((ε' : L) * s),
          Subgroup.subset_closure ⟨_, rfl⟩, rfl⟩
      have hfix : step g = g := by
        have hneg : -σQ s = s := by
          have hσ : σQ s = -s := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hsadd)
          rw [hσ, neg_neg]
        rw [hgX, hX, ← hy_formula_low s, hstep_low s, hneg]
      exact ⟨hgU, hfix⟩

end CFSG.StandardType.RCKRP
