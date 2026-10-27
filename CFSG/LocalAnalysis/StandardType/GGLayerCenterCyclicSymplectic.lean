module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicLinear
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicMatrix
public import CFSG.LieType.Steinberg.Classical.Symplectic
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix

namespace LayerCC

variable {m : ℕ} {K : Type} [Field K]

theorem sp_conj_gram {M Mi H : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K} {μ : K} (hμ : μ ≠ 0)
    (hMMi : M * Mi = 1) (hM : Mᵀ * fromBlocks 0 1 (-1) 0 * M = μ • fromBlocks 0 1 (-1) 0)
    (hH : Hᵀ * fromBlocks 0 1 (-1) 0 * H = fromBlocks 0 1 (-1) 0) :
    (M * H * Mi)ᵀ * fromBlocks 0 1 (-1) 0 * (M * H * Mi) = fromBlocks 0 1 (-1) 0 := by
  set J : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := fromBlocks 0 1 (-1) 0 with hJ
  have hMiT : Miᵀ * Mᵀ = 1 := by rw [← transpose_mul, hMMi, transpose_one]
  have hMi : Miᵀ * J * Mi = μ⁻¹ • J := by
    have h1 : Miᵀ * (Mᵀ * J * M) * Mi = J := by
      calc Miᵀ * (Mᵀ * J * M) * Mi = (Miᵀ * Mᵀ) * J * (M * Mi) := by
            simp only [Matrix.mul_assoc]
        _ = J := by rw [hMiT, hMMi, Matrix.one_mul, Matrix.mul_one]
    rw [hM, Matrix.mul_smul, Matrix.smul_mul] at h1
    calc Miᵀ * J * Mi = μ⁻¹ • (μ • (Miᵀ * J * Mi)) := by
          rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = μ⁻¹ • J := by rw [h1]
  calc (M * H * Mi)ᵀ * J * (M * H * Mi)
      = Miᵀ * (Hᵀ * (Mᵀ * J * M) * H) * Mi := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = Miᵀ * (μ • (Hᵀ * J * H)) * Mi := by
        rw [hM, Matrix.mul_smul, Matrix.smul_mul]
    _ = μ • (Miᵀ * J * Mi) := by
        rw [hH, Matrix.mul_smul, Matrix.smul_mul]
    _ = J := by rw [hMi, smul_smul, mul_inv_cancel₀ hμ, one_smul]

theorem inv_mem_gspSet {A : GL (Fin m ⊕ Fin m) K} (hA : A ∈ LargeEvenGSpSet K m) :
    A⁻¹ ∈ LargeEvenGSpSet K m := by
  obtain ⟨μ, hμ, hA⟩ := hA
  refine ⟨μ⁻¹, inv_ne_zero hμ, ?_⟩
  set M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := A.val
  set Mi : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := (A⁻¹).val
  have hMMi : M * Mi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiT : Miᵀ * Mᵀ = 1 := by rw [← transpose_mul, hMMi, transpose_one]
  have h1 : Miᵀ * (Mᵀ * LargeEvenSpForm K m * M) * Mi = LargeEvenSpForm K m := by
    calc Miᵀ * (Mᵀ * LargeEvenSpForm K m * M) * Mi
        = (Miᵀ * Mᵀ) * LargeEvenSpForm K m * (M * Mi) := by simp only [Matrix.mul_assoc]
      _ = LargeEvenSpForm K m := by rw [hMiT, hMMi, Matrix.one_mul, Matrix.mul_one]
  rw [hA, Matrix.mul_smul, Matrix.smul_mul] at h1
  calc Miᵀ * LargeEvenSpForm K m * Mi = μ⁻¹ • (μ • (Miᵀ * LargeEvenSpForm K m * Mi)) := by
        rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
    _ = μ⁻¹ • LargeEvenSpForm K m := by rw [h1]

theorem conj_mem_largeEvenSpGroup {A : GL (Fin m ⊕ Fin m) K} (hA : A ∈ LargeEvenGSpSet K m)
    {h : GL (Fin m ⊕ Fin m) K} (hh : h ∈ LargeEvenSpGroup K m) :
    A * h * A⁻¹ ∈ LargeEvenSpGroup K m := by
  obtain ⟨μ, hμ, hAμ⟩ := hA
  have hh' := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp hh
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mpr
  rw [Units.val_mul, Units.val_mul]
  exact sp_conj_gram hμ (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hAμ hh'

end LayerCC

open LayerCC in
theorem LayerCC.gsp_subset_normalizer_sp {m : ℕ} {K : Type} [Field K] {A : GL (Fin m ⊕ Fin m) K}
    (hA : A ∈ LargeEvenGSpSet K m) :
    A ∈ Subgroup.normalizer (LargeEvenSpGroup K m : Set (GL (Fin m ⊕ Fin m) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_largeEvenSpGroup hA hh, fun hh => ?_⟩
  have h1 := conj_mem_largeEvenSpGroup (inv_mem_gspSet hA) hh
  rwa [inv_inv, show A⁻¹ * (A * h * A⁻¹) * A = h by group] at h1

theorem LayerCC.commutator_largeEvenSpGroup {m : ℕ} {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (hm : 2 ≤ m) (hm2 : m = 2 → 2 ≤ n) :
    commutator (LargeEvenSpGroup K m) = ⊤ := by
  refine (CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp m K ?_).commutator_eq_top
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · right
    right
    obtain rfl : n = 1 := by omega
    refine ⟨by rw [hK, pow_one], ?_⟩
    by_contra h3
    exact absurd (hm2 (by omega)) (by omega)
  · left
    have : Fintype K := Fintype.ofFinite K
    have h4 : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
    exact ⟨s, hs⟩

open LayerCC in
theorem ggPSections_sp
    {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGPSections p (LargeEvenSpGroup K m) := by
  intro E _ _ η hη hker hpk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := not_two_dvd_card_of_isPGroup hp hp2 hpk
  obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
    (CFSG.LieType.Universal.Symplectic.rootDatum m K).isFiniteType
    (Dv := (CFSG.LieType.Universal.Symplectic.rootDatum m K).divisible) rfl
  have hE := CFSG.LieType.Steinberg.Sp.chevalleyExtras (F := K) hm O
    CFSG.LieType.Steinberg.Sp.commC (CFSG.LieType.Steinberg.Sp.commutatorFormula O)
  exact (CFSG.LieType.Steinberg.existsUnique_section_of_sl2_lift
    (CFSG.LieType.Universal.Symplectic.isCTGroupDatum m K)
    (CFSG.LieType.Universal.Symplectic.steinbergExtras m K) hE.param hE.rankOne hη hker hC
    fun ρ => by
      obtain ⟨ρ', hρ', -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift hη hker hC ρ
      exact ⟨ρ', fun g => congrArg (· g) hρ'⟩).exists

end CFSG.StandardType

end
