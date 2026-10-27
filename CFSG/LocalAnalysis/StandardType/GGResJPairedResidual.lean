module

public import CFSG.LocalAnalysis.StandardType.GGResJPairedBlock
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType
namespace ResJPairedBlock
namespace ActualA
namespace RankTwo

open Matrix Polynomial CoordSL Multiplicative CFSG.Assembly

variable {G : Type} [Group G] [Finite G]
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {n : ℕ} {Bs J : Subgroup G}
  {g : K[X]} [Fact (Irreducible g)]
  {r s : ℕ} {ε : Fin n ≃ (Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin r}
  {A₀ : Matrix.SpecialLinearGroup (Fin n) K}

open CoordSL

@[expose] def resBlock : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 1]

theorem resBlock_det : resBlock (K := K).det = 1 := by
  rw [resBlock, Matrix.det_fin_two_of, zero_mul, one_mul, zero_sub]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h : (1 : K) + 1 = 0 := by
    simpa [one_add_one_eq_two] using h2
  exact neg_eq_of_add_eq_zero_left h

theorem resBlock_pow_three : resBlock (K := K) ^ 3 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  rw [pow_three', Matrix.one_fin_two]
  change (!![0, 1; 1, 1] * !![0, 1; 1, 1] * !![0, 1; 1, 1] :
    Matrix (Fin 2) (Fin 2) K) i j = _
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  have h11 : (1 : K) + 1 = 0 := by
    simpa [one_add_one_eq_two] using h2
  fin_cases i <;> fin_cases j <;> simp [h11]

theorem resBlock_apply_zero_one : resBlock (K := K) 0 1 = 1 := rfl

private noncomputable def resFinEquiv (hr : 2 ≤ r) : Fin r ≃ Fin 2 ⊕ Fin (r - 2) :=
  (finCongr (by omega : 2 + (r - 2) = r)).symm.trans finSumFinEquiv.symm

private noncomputable def resMat (hr : 2 ≤ r) : Matrix (Fin r) (Fin r) K :=
  (Matrix.fromBlocks resBlock 0 0 (1 : Matrix (Fin (r - 2)) (Fin (r - 2)) K)).submatrix
    (resFinEquiv hr) (resFinEquiv hr)

private theorem resMat_det (hr : 2 ≤ r) : (resMat (K := K) hr).det = 1 := by
  rw [resMat, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    resBlock_det, Matrix.det_one, mul_one]

private theorem resMat_pow_three (hr : 2 ≤ r) : (resMat (K := K) hr) ^ 3 = 1 := by
  have hM3 : (Matrix.fromBlocks resBlock 0 0
      (1 : Matrix (Fin (r - 2)) (Fin (r - 2)) K)) ^ 3 = 1 := by
    rw [Matrix.fromBlocks_diagonal_pow, resBlock_pow_three]
    simp
  rw [resMat, SLNS.submatrix_pow_equiv, hM3, Matrix.submatrix_one_equiv]

private theorem resMat_offdiag (hr : 2 ≤ r) :
    resMat (K := K) hr ((resFinEquiv hr).symm (Sum.inl 0))
      ((resFinEquiv hr).symm (Sum.inl 1)) = 1 := by
  rw [resMat, Matrix.submatrix_apply]
  simp [Matrix.fromBlocks_apply₁₁, resBlock]

private theorem resD0_comm (hr : 2 ≤ r) (k : Fin s → ℕ) :
    (Matrix.fromBlocks
        (1 : Matrix (Fin (CoordSL.rootPB g).dim × Fin s)
          (Fin (CoordSL.rootPB g).dim × Fin s) K) 0 0 (resMat (K := K) hr)) *
      SLNS.nsCore (CoordSL.rootMat g) k =
    SLNS.nsCore (CoordSL.rootMat g) k *
      (Matrix.fromBlocks
        (1 : Matrix (Fin (CoordSL.rootPB g).dim × Fin s)
          (Fin (CoordSL.rootPB g).dim × Fin s) K) 0 0 (resMat (K := K) hr)) := by
  rw [SLNS.nsCore, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

private theorem resD0_det (hr : 2 ≤ r) :
    (Matrix.fromBlocks
      (1 : Matrix (Fin (CoordSL.rootPB g).dim × Fin s)
        (Fin (CoordSL.rootPB g).dim × Fin s) K) 0 0 (resMat (K := K) hr)).det = 1 := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, resMat_det]

private theorem resD0_pow_three (hr : 2 ≤ r) :
    (Matrix.fromBlocks
      (1 : Matrix (Fin (CoordSL.rootPB g).dim × Fin s)
        (Fin (CoordSL.rootPB g).dim × Fin s) K) 0 0 (resMat (K := K) hr)) ^ 3 = 1 := by
  rw [Matrix.fromBlocks_diagonal_pow, one_pow, resMat_pow_three]
  simp

private theorem frameSL_pow_three
    (hC : (CoordSL.rootMat g).det = 1)
    (hCp : (CoordSL.rootMat g) ^ 3 = 1) (k : Fin s → ℕ) :
    (A₀ * SLNS.nsSL ε hC k * A₀⁻¹) ^ 3 = 1 := by
  have hns : (SLNS.nsSL ε hC k) ^ 3 = 1 := by
    rw [SLNS.nsSL_pow]
    have hcongr := SLNS.nsSL_congr (ε := ε) (C := CoordSL.rootMat g)
      (hC := hC) (hCp := hCp) (k := 3 • k) (k' := 0) (by
        intro i
        have hzero : (k i * 3) % 3 = 0 :=
          Nat.mod_eq_zero_of_dvd (dvd_mul_left 3 (k i))
        simpa [Pi.smul_apply, Nat.mul_comm] using hzero)
    simpa [SLNS.nsSL_zero] using hcongr
  calc (A₀ * SLNS.nsSL ε hC k * A₀⁻¹) ^ 3
      = A₀ * (SLNS.nsSL ε hC k) ^ 3 * A₀⁻¹ := by rw [conj_pow]
    _ = 1 := by rw [hns]; group

theorem residual_le_one
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hSC : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    (hn3 : 3 ≤ n)
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* ↥J)
    (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hpK : ¬ 3 ∣ Nat.card K - 1)
    (hC : (CoordSL.rootMat g).det = 1) (hCp : (CoordSL.rootMat g) ^ 3 = 1)
    (hgd : g ∣ cyclotomic 3 K)
    (hframeA : (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range =
      (ggGamma J hN).range) :
    r ≤ 1 := by
  classical
  by_contra hle
  have hr : 2 ≤ r := by omega
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) := by
    by_cases hs : 2 ≤ s
    · exact isPerfect_SL_of_frame (ε' := ε) hgd hpK hs
    · exact CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := K) hn3
  have hkerPsi : (psi φ).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) :=
    psi_ker_le_center (φ := φ) hφ hker hperf
  have hφc : ∀ x, φ x ∈ Subgroup.center ↥J →
      x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
    intro x hx
    apply hkerPsi
    rw [MonoidHom.mem_ker, psi_apply]
    have hx1 : MulAut.conj (φ x) = 1 := by
      have hxker := hx
      rw [← CFSG.GroupTheory.ker_conj_eq_center] at hxker
      simpa [MonoidHom.mem_ker] using hxker
    exact hx1
  let D0 : Matrix ((Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin r)
      ((Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin r) K :=
    Matrix.fromBlocks
      (1 : Matrix (Fin (CoordSL.rootPB g).dim × Fin s)
        (Fin (CoordSL.rootPB g).dim × Fin s) K) 0 0 (resMat (K := K) hr)
  let D : Matrix (Fin n) (Fin n) K := D0.submatrix ε ε
  have hD0comm : ∀ k : Fin s → ℕ,
      D0 * SLNS.nsCore (CoordSL.rootMat g) k =
        SLNS.nsCore (CoordSL.rootMat g) k * D0 := by
    intro k
    simpa [D0] using resD0_comm (g := g) (s := s) hr k
  have hD0det : D0.det = 1 := by
    simpa [D0] using resD0_det (g := g) (s := s) hr
  have hD0pow : D0 ^ 3 = 1 := by
    simpa [D0] using resD0_pow_three (g := g) (s := s) hr
  have hDdet : D.det = 1 := by
    dsimp [D]
    rw [Matrix.det_submatrix_equiv_self, hD0det]
  have hDpow : D ^ 3 = 1 := by
    dsimp [D]
    rw [SLNS.submatrix_pow_equiv, hD0pow, Matrix.submatrix_one_equiv]
  have hDcomm : ∀ k : Fin s → ℕ,
      D * SLNS.nsMat ε (CoordSL.rootMat g) k =
        SLNS.nsMat ε (CoordSL.rootMat g) k * D := by
    intro k
    dsimp [D]
    rw [SLNS.nsMat, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    exact congrArg (fun M => M.submatrix ε ε) (hD0comm k)
  let dSL : Matrix.SpecialLinearGroup (Fin n) K := ⟨D, hDdet⟩
  let t : Matrix.SpecialLinearGroup (Fin n) K := A₀ * dSL * A₀⁻¹
  have hdSLpow : dSL ^ 3 = 1 := Subtype.ext hDpow
  have htpow : t ^ 3 = 1 := by
    dsimp [t]
    calc (A₀ * dSL * A₀⁻¹) ^ 3 = A₀ * dSL ^ 3 * A₀⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [hdSLpow]; group
  have hdSLcomm : ∀ k : Fin s → ℕ,
      dSL * SLNS.nsSL ε hC k = SLNS.nsSL ε hC k * dSL := by
    intro k
    apply Subtype.ext
    change D * SLNS.nsMat ε (CoordSL.rootMat g) k =
      SLNS.nsMat ε (CoordSL.rootMat g) k * D
    exact hDcomm k
  have htcomm : ∀ k : Fin s → ℕ,
      t * (A₀ * SLNS.nsSL ε hC k * A₀⁻¹) =
        (A₀ * SLNS.nsSL ε hC k * A₀⁻¹) * t := by
    intro k
    dsimp [t]
    calc A₀ * dSL * A₀⁻¹ * (A₀ * SLNS.nsSL ε hC k * A₀⁻¹)
        = A₀ * (dSL * SLNS.nsSL ε hC k) * A₀⁻¹ := by group
      _ = A₀ * (SLNS.nsSL ε hC k * dSL) * A₀⁻¹ := by rw [hdSLcomm k]
      _ = (A₀ * SLNS.nsSL ε hC k * A₀⁻¹) * (A₀ * dSL * A₀⁻¹) := by group

  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  have hsc : GGTorusSelfCent 3 A := by
    simpa [A] using ggTorusSelfCent_ggGamma (p := 3) hN hSC
  have htpowJ : (φ t) ^ 3 = 1 := by
    rw [← map_pow, htpow, map_one]
  have hfix : ∀ a ∈ A, a (φ t) = φ t := by
    intro a ha
    have ha' : a ∈ (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range := by
      rw [hframeA]
      exact ha
    obtain ⟨u, hu⟩ := ha'
    let k : Fin s → ℕ := fun i => (Multiplicative.toAdd u i).val
    let y : Matrix.SpecialLinearGroup (Fin n) K :=
      A₀ * SLNS.nsSL ε hC k * A₀⁻¹
    have hframe : CoordSL.frameHom (psi φ) A₀ ε hC hCp u = MulAut.conj (φ y) := by
      simpa [k, y] using
        (frameHom_psi_apply (φ := φ) (hC := hC) (hCp := hCp)
          (t := Multiplicative.toAdd u))
    have hc' : φ y * φ t = φ t * φ y := by
      rw [← map_mul, ← map_mul, htcomm k]
    rw [← hu, hframe, MulAut.conj_apply, hc', mul_assoc, mul_inv_cancel, mul_one]
  have hmemA : (psi φ) t ∈ A := by
    simpa [psi_apply] using hsc (φ t) hfix htpowJ
  have hmemFrame : (psi φ) t ∈
      (CoordSL.frameHom (psi φ) A₀ ε hC hCp).range := by
    rw [hframeA]
    exact hmemA
  obtain ⟨u, hu⟩ := hmemFrame
  let k : Fin s → ℕ := fun i => (Multiplicative.toAdd u i).val
  let frameSL : Matrix.SpecialLinearGroup (Fin n) K :=
    A₀ * SLNS.nsSL ε hC k * A₀⁻¹
  have hframe : CoordSL.frameHom (psi φ) A₀ ε hC hCp u = (psi φ) frameSL := by
    simpa [k, frameSL, psi_apply] using
      (frameHom_psi_apply (φ := φ) (hC := hC) (hCp := hCp)
        (t := Multiplicative.toAdd u))
  have hpsieq : (psi φ) t = (psi φ) frameSL := by
    rw [← hu, hframe]
  have hframePow : frameSL ^ 3 = 1 := by
    simpa [frameSL] using frameSL_pow_three (g := g) (s := s) (A₀ := A₀)
      (hC := hC) (hCp := hCp) k
  have hconj : MulAut.conj (φ t) = MulAut.conj (φ frameSL) := by
    simpa [psi_apply] using hpsieq
  have ht_eq : t = frameSL :=
    eq_of_conj_phi_eq (φ := φ) hφc hpK htpow hframePow hconj
  have hdSL_eq : dSL = SLNS.nsSL ε hC k := by
    have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin n) K =>
      A₀⁻¹ * x * A₀) ht_eq
    simpa [t, frameSL, mul_assoc] using h
  have hD_eq : D = SLNS.nsMat ε (CoordSL.rootMat g) k := by
    have h := congrArg Subtype.val hdSL_eq
    simpa [dSL, SLNS.nsSL] using h

  let j0 := (resFinEquiv hr).symm (Sum.inl 0)
  let j1 := (resFinEquiv hr).symm (Sum.inl 1)
  have hj : j0 ≠ j1 := by
    intro hh
    have := congrArg (resFinEquiv hr) hh
    simp [j0, j1] at this
  let i0 := ε.symm (Sum.inr j0)
  let i1 := ε.symm (Sum.inr j1)
  have hleft : D i0 i1 = 1 := by
    dsimp [D]
    simp [D0, i0, i1, j0, j1, resMat_offdiag hr]
  have hright : SLNS.nsMat ε (CoordSL.rootMat g) k i0 i1 = 0 := by
    rw [SLNS.nsMat, Matrix.submatrix_apply]
    simp [SLNS.nsCore, Matrix.fromBlocks_apply₂₂, Matrix.one_apply, i0, i1, j0, j1, hj]
  have hone : (1 : K) = 0 := by
    calc (1 : K) = D i0 i1 := hleft.symm
      _ = SLNS.nsMat ε (CoordSL.rootMat g) k i0 i1 := by rw [hD_eq]
      _ = 0 := hright
  exact one_ne_zero hone

end RankTwo
end ActualA
end ResJPairedBlock
end CFSG.StandardType

end
