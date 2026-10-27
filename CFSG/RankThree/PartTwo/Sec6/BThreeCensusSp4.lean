module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusLinear
public import CFSG.RankThree.SubgroupLists.SymplecticReducible
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.Open.StatedAPI
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists

local notation "V₄" => Fin 2 ⊕ Fin 2

section Symplectic

variable {K : Type} [Field K]

theorem finrank_le_two_of_isotropic {U : Submodule K (V₄ → K)}
    (hU : ∀ u ∈ U, ∀ v ∈ U, spForm 2 K u v = 0) : Module.finrank K U ≤ 2 := by
  have hle : U ≤ orth U := fun v hv => mem_orth.mpr fun u hu => hU u hu v hv
  have h1 := Submodule.finrank_mono hle
  rw [finrank_orth] at h1
  omega

theorem spForm_smul_smul (a b : K) (u v : V₄ → K) :
    spForm 2 K (a • u) (b • v) = a * b * spForm 2 K u v := by
  rw [LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, mul_assoc]

theorem finrank_range_eigenProj_le_two (h3 : (3 : K) ≠ 0) {g : GL V₄ K} (hgS : g ∈ StatedSp 2 K)
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) {c : K} (hc : c ^ 3 = 1) :
    Module.finrank K (LinearMap.range (Matrix.toLin' (eigenProj (g : Matrix V₄ V₄ K) c))) ≤ 2 := by
  have hgm : (g : Matrix V₄ V₄ K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hg3, Units.val_one]
  have hB : ∀ x y : V₄ → K, spForm 2 K ((g : Matrix V₄ V₄ K) *ᵥ x) ((g : Matrix V₄ V₄ K) *ᵥ y) =
      spForm 2 K x y := spForm_mulVec hgS
  by_cases hc1 : c = 1
  ·
    subst hc1
    set P := eigenProj (g : Matrix V₄ V₄ K) 1 with hP
    set E := LinearMap.range (Matrix.toLin' P) with hE
    set W := LinearMap.ker (Matrix.toLin' P) with hW
    have hgP : (g : Matrix V₄ V₄ K) * P = P := by
      rw [hP, mul_eigenProj hgm (one_pow 3), one_pow, one_smul]
    have hPP : P * P = (3 : K) • P := by
      have hg2P : (g : Matrix V₄ V₄ K) ^ 2 * P = P := by rw [sq, mul_assoc, hgP, hgP]
      calc P * P = P + (g : Matrix V₄ V₄ K) * P + (g : Matrix V₄ V₄ K) ^ 2 * P := by
            simp only [hP, eigenProj, one_smul, one_pow, add_mul, one_mul]
        _ = (3 : K) • P := by
            rw [hgP, hg2P, show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
    have hxW : ∀ x : V₄ → K, x - (3 : K)⁻¹ • (P *ᵥ x) ∈ W := by
      intro x
      change P *ᵥ (x - (3 : K)⁻¹ • (P *ᵥ x)) = 0
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hPP, Matrix.smul_mulVec,
        smul_smul, inv_mul_cancel₀ h3, one_smul, sub_self]
    by_contra hdim
    push Not at hdim
    have hrank := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' P)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hrank
    have hW1 : Module.finrank K W ≤ 1 := by
      change Module.finrank K E + Module.finrank K W = 2 + 2 at hrank
      omega
    have hEW : ∀ u ∈ E, ∀ w ∈ W, spForm 2 K u w = 0 := by
      intro u hu w hw
      have hgu : (g : Matrix V₄ V₄ K) *ᵥ u = u := by
        have := mulVec_eq_of_mem_range_eigenProj hgm (one_pow 3) hu
        rwa [one_pow, one_smul] at this
      have hPw : P *ᵥ w = 0 := hw
      have e1 : spForm 2 K u ((g : Matrix V₄ V₄ K) *ᵥ w) = spForm 2 K u w := by
        rw [← hB u w, hgu]
      have e2 : spForm 2 K u ((g : Matrix V₄ V₄ K) ^ 2 *ᵥ w) = spForm 2 K u w := by
        rw [sq, ← Matrix.mulVec_mulVec]
        calc spForm 2 K u ((g : Matrix V₄ V₄ K) *ᵥ ((g : Matrix V₄ V₄ K) *ᵥ w)) =
            spForm 2 K ((g : Matrix V₄ V₄ K) *ᵥ u)
              ((g : Matrix V₄ V₄ K) *ᵥ ((g : Matrix V₄ V₄ K) *ᵥ w)) := by rw [hgu]
          _ = spForm 2 K u ((g : Matrix V₄ V₄ K) *ᵥ w) := hB u _
          _ = spForm 2 K u w := e1
      have e3 : P *ᵥ w = w + (g : Matrix V₄ V₄ K) *ᵥ w + (g : Matrix V₄ V₄ K) ^ 2 *ᵥ w := by
        simp only [hP, eigenProj, one_smul, one_pow, Matrix.add_mulVec, Matrix.one_mulVec]
      have e4 := congrArg (spForm 2 K u) e3
      rw [hPw, map_zero, map_add, map_add, e1, e2] at e4
      have h3B : (3 : K) * spForm 2 K u w = 0 := by linear_combination -e4
      exact (mul_eq_zero.mp h3B).resolve_left h3
    obtain ⟨w₀, hw₀⟩ := finrank_le_one_iff.mp hW1
    have hWW : ∀ w ∈ W, ∀ w' ∈ W, spForm 2 K w w' = 0 := by
      intro w hw w' hw'
      obtain ⟨a, ha⟩ := hw₀ ⟨w, hw⟩
      obtain ⟨b, hb⟩ := hw₀ ⟨w', hw'⟩
      have ha' : a • (w₀ : V₄ → K) = w := congrArg Subtype.val ha
      have hb' : b • (w₀ : V₄ → K) = w' := congrArg Subtype.val hb
      rw [← ha', ← hb', spForm_smul_smul, spForm_self, mul_zero]
    have hW0 : ∀ w ∈ W, w = 0 := by
      intro w hw
      apply spForm_separatingLeft w
      intro x
      have hx : x = (3 : K)⁻¹ • (P *ᵥ x) + (x - (3 : K)⁻¹ • (P *ᵥ x)) := by abel
      have hPxE : (3 : K)⁻¹ • (P *ᵥ x) ∈ E :=
        ⟨(3 : K)⁻¹ • x, by rw [Matrix.toLin'_apply, Matrix.mulVec_smul]⟩
      rw [hx, map_add, hWW w hw _ (hxW x), add_zero]
      exact spForm_isRefl _ _ (hEW _ hPxE w hw)
    have hP3 : P = (3 : K) • 1 := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro x
      have hx := sub_eq_zero.mp (hW0 _ (hxW x))
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
      calc P *ᵥ x = (3 : K) • ((3 : K)⁻¹ • (P *ᵥ x)) := by
            rw [smul_smul, mul_inv_cancel₀ h3, one_smul]
        _ = (3 : K) • x := by rw [← hx]
    apply hg1
    apply Units.ext
    rw [Units.val_one]
    have h := hgP
    rw [hP3, Matrix.mul_smul, mul_one] at h
    have h' := congrArg (fun M : Matrix V₄ V₄ K => (3 : K)⁻¹ • M) h
    simpa only [smul_smul, inv_mul_cancel₀ h3, one_smul] using h'
  ·
    refine finrank_le_two_of_isotropic fun u hu v hv => ?_
    have hgu := mulVec_eq_of_mem_range_eigenProj hgm hc hu
    have hgv := mulVec_eq_of_mem_range_eigenProj hgm hc hv
    have h := hB u v
    rw [hgu, hgv, spForm_smul_smul] at h
    have hc4 : c ^ 2 * c ^ 2 = c := by
      calc c ^ 2 * c ^ 2 = c ^ 3 * c := by ring
        _ = c := by rw [hc, one_mul]
    rw [hc4] at h
    have h' : (c - 1) * spForm 2 K u v = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hc1
    · exact h0

end Symplectic

section BaseChange

variable {F K : Type} [Field F] [Field K]

theorem map_mem_statedSp_two (φ : F →+* K) {x : GL V₄ F} (hx : x ∈ StatedSp 2 F) :
    Matrix.GeneralLinearGroup.map φ x ∈ StatedSp 2 K :=
  CFSG.Open.StatedAPI.map_mem_statedSp φ hx

end BaseChange

theorem eq_bot_of_commute_of_mem_statedSp {F : Type} [Field F]
    [Finite F] (h3 : (3 : F) ≠ 0) {g : GL V₄ F} (hgS : g ∈ StatedSp 2 F) (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) (Y : Subgroup (GL V₄ F)) (hYg : ∀ y ∈ Y, y * g = g * y)
    (hYp : Group.IsPerfect Y) (hY3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  obtain ⟨K, _, _, φ, ω, hω⟩ := exists_splittingField_cubeRoot F
  have h3K := three_ne_zero_map φ h3
  have hinj := map_gl_injective (n := V₄) φ
  refine eq_bot_of_commute_of_map h3K φ hω (fun c hc => ?_) Y hYg hYp hY3
  exact finrank_range_eigenProj_le_two h3K (map_mem_statedSp_two φ hgS)
    (by rw [← map_pow, hg3, map_one]) (fun h => hg1 (hinj (by rw [h, map_one]))) hc

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
