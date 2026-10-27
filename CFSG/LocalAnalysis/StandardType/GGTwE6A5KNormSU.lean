module

public import CFSG.Open.StatedDefs
import CFSG.HardMathSupport.Foote.ModuleExclusions.PSUAlg
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUCommute
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUBlocks
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.StandardType.SCFourCover

open Matrix
open scoped MatrixGroups

private theorem exists_pow_two_pow_mul_eq_one_ne_one {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    [CharP Ω 2] {f : ℕ} (hf : 1 ≤ f) : ∃ ζ : Ω, ζ ^ 2 ^ f * ζ = 1 ∧ ζ ≠ 1 := by
  have h2 : ((2 ^ f + 1 : ℕ) : Ω) = 1 := by
    push_cast
    rw [CharTwo.two_eq_zero, zero_pow (n := f) (by omega), zero_add]
  haveI : NeZero ((2 ^ f + 1 : ℕ) : Ω) := ⟨by rw [h2]; exact one_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (2 ^ f + 1)
  refine ⟨ζ, by rw [← pow_succ]; exact hζ.pow_eq_one, hζ.ne_one ?_⟩
  have := Nat.two_pow_pos f
  omega

private theorem mul_comm_of_unitary_conj {Ω : Type} [Field Ω] {ν : ℕ} (φ : Ω →+* Ω)
    {M Mi G : Matrix (Fin ν) (Fin ν) Ω} (hMiM : Mi * M = 1)
    (hq1 : (M.map φ)ᵀ * (Mi.map φ)ᵀ = 1) (hG : (G.map φ)ᵀ * G = 1)
    (hWG : ((M * G * Mi).map φ)ᵀ * (M * G * Mi) = 1) :
    (M.map φ)ᵀ * M * G = G * ((M.map φ)ᵀ * M) := by
  have hG' : G * (G.map φ)ᵀ = 1 := mul_eq_one_comm.1 hG
  have hX : (G.map φ)ᵀ * ((M.map φ)ᵀ * M) * G = (M.map φ)ᵀ * M := by
    have h := congrArg (fun X => (M.map φ)ᵀ * X * M) hWG
    simp only [Matrix.map_mul, transpose_mul, Matrix.mul_assoc, Matrix.mul_one,
      Matrix.one_mul] at h
    rw [hMiM, Matrix.mul_one, ← Matrix.mul_assoc (M.map φ)ᵀ, hq1, Matrix.one_mul] at h
    simpa only [Matrix.mul_assoc] using h
  calc (M.map φ)ᵀ * M * G = G * (G.map φ)ᵀ * ((M.map φ)ᵀ * M) * G := by
        rw [hG', Matrix.one_mul]
    _ = G * ((M.map φ)ᵀ * M) := by
        rw [Matrix.mul_assoc G, Matrix.mul_assoc G, hX]

private theorem map_map_eq_of_unitary {Ω : Type} [Field Ω] {ν : ℕ} (φ : Ω →+* Ω)
    {N : Matrix (Fin ν) (Fin ν) Ω} (hN : (N.map φ)ᵀ * N = 1) : (N.map φ).map φ = N := by
  have h1 : N.map φ * Nᵀ = 1 := by
    have h := congrArg transpose (mul_eq_one_comm.1 hN)
    rwa [transpose_mul, transpose_transpose, transpose_one] at h
  have h2 : ((N.map φ).map φ)ᵀ * N.map φ = 1 := by
    have h := congrArg (fun X : Matrix (Fin ν) (Fin ν) Ω => X.map φ) hN
    simp only [Matrix.map_mul, transpose_map] at h
    rw [h, Matrix.map_one _ (map_zero φ) (map_one φ)]
  rw [← transpose_inj]
  calc ((N.map φ).map φ)ᵀ = ((N.map φ).map φ)ᵀ * (N.map φ * Nᵀ) := by rw [h1, Matrix.mul_one]
    _ = Nᵀ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem exists_smul_unitary_of_normalizes_statedSU {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    [CharP Ω 2] {ν f : ℕ} (hν : 2 ≤ ν) (hf : 1 ≤ f) {W : GL (Fin ν) Ω}
    (hW : ∀ g ∈ CFSG.Open.StatedSU ν (2 ^ f) Ω, W * g * W⁻¹ ∈ CFSG.Open.StatedSU ν (2 ^ f) Ω) :
    ∃ c μ : Ω, c ≠ 0 ∧ μ ≠ 0 ∧ μ ^ 2 ^ f = μ ∧
      (c • (W : Matrix (Fin ν) (Fin ν) Ω)).map (· ^ (2 ^ f) ^ 2) =
        c • (W : Matrix (Fin ν) (Fin ν) Ω) ∧
      Matrix.transpose ((c • (W : Matrix (Fin ν) (Fin ν) Ω)).map (· ^ 2 ^ f)) *
          (c • (W : Matrix (Fin ν) (Fin ν) Ω)) = μ • (1 : Matrix (Fin ν) (Fin ν) Ω) := by
  set φ := iterateFrobenius Ω 2 f
  have hφ : ∀ x : Ω, φ x = x ^ 2 ^ f := fun _ => rfl
  obtain ⟨ζ, hζ, hζ1⟩ := exists_pow_two_pow_mul_eq_one_ne_one (Ω := Ω) hf
  have hMiM : ((W⁻¹ : GL (Fin ν) Ω) : Matrix (Fin ν) (Fin ν) Ω) * W = 1 := Units.inv_mul W
  have hq1 : ((W : Matrix (Fin ν) (Fin ν) Ω).map φ)ᵀ *
      (((W⁻¹ : GL (Fin ν) Ω) : Matrix (Fin ν) (Fin ν) Ω).map φ)ᵀ = 1 := by
    rw [← transpose_mul, ← Matrix.map_mul, hMiM, Matrix.map_one _ (map_zero φ) (map_one φ),
      transpose_one]
  have hD := CFSG.ComponentClassification.RankTwoClassical.eq_smul_one_of_commute_statedSU hν
    hζ hζ1 (D := ((W : Matrix (Fin ν) (Fin ν) Ω).map φ)ᵀ * W) fun g =>
      mul_comm_of_unitary_conj φ hMiM hq1
        (CFSG.HardMathSupport.Foote.ModuleExclusions.unitary_of_mem_statedSU φ hφ g.2).1 (by
          have h := (CFSG.HardMathSupport.Foote.ModuleExclusions.unitary_of_mem_statedSU φ hφ
            (hW _ g.2)).1
          rwa [Units.val_mul, Units.val_mul] at h)
  obtain ⟨l, hl⟩ : ∃ l : Ω, ((W : Matrix (Fin ν) (Fin ν) Ω).map φ)ᵀ * W = l • 1 := ⟨_, hD⟩
  have hl0 : l ≠ 0 := by
    intro h0
    have h : ((W : Matrix (Fin ν) (Fin ν) Ω).map φ)ᵀ * W *
        (((W⁻¹ : GL (Fin ν) Ω) : Matrix (Fin ν) (Fin ν) Ω) *
          (((W⁻¹ : GL (Fin ν) Ω) : Matrix (Fin ν) (Fin ν) Ω).map φ)ᵀ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (W : Matrix (Fin ν) (Fin ν) Ω), Units.mul_inv,
        Matrix.one_mul, hq1]
    rw [hl, h0, zero_smul, Matrix.zero_mul] at h
    have h00 := congrFun (congrFun h ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at h00
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq l⁻¹ (n := 2 ^ f + 1) (Nat.succ_pos _)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (n := 2 ^ f + 1) (Nat.succ_ne_zero _)] at hc
    exact inv_ne_zero hl0 hc.symm
  have hN : ((c • (W : Matrix (Fin ν) (Fin ν) Ω)).map φ)ᵀ *
      (c • (W : Matrix (Fin ν) (Fin ν) Ω)) = 1 := by
    have hmap : (c • (W : Matrix (Fin ν) (Fin ν) Ω)).map φ =
        φ c • (W : Matrix (Fin ν) (Fin ν) Ω).map φ := by
      ext i j
      simp [Matrix.map_apply, Matrix.smul_apply, map_mul]
    rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hl, smul_smul, hφ,
      ← pow_succ, hc, inv_mul_cancel₀ hl0, one_smul]
  refine ⟨c, 1, hc0, one_ne_zero, one_pow _, ?_, by rw [one_smul]; exact hN⟩
  have h2 := map_map_eq_of_unitary φ hN
  rw [Matrix.map_map] at h2
  have hfun : (fun x : Ω => x ^ (2 ^ f) ^ 2) = ⇑φ ∘ ⇑φ := by
    funext x
    simp only [Function.comp_apply, hφ, sq, pow_mul]
  rw [hfun]
  exact h2

end CFSG.StandardType.SCFourCover

end
