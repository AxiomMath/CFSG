module

public import CFSG.RankThree.PartOne.SEITZU49.Stmt
public import CFSG.RankThree.PartOne.CTP.SeitzU5Gen

public section

namespace CFSG.RankThree.PartOne.SEITZU49.Gen

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.RankThree.PartOne.CTP.U5Gen (Cset Cset_smul Cset_pair Cset_conj_mem dgTau dgTau_smul
  plane_all_of_point extVec extVec_eq range_blockEmb2_le two_eq_zero ne_zero_of_norm_one)
open CFSG.ClassicalInvolution.Phan (iSup_range_blockEmb2)
open CFSG.RankThree.PartOne.SEITZU49.Frame (shiftZ)
open CFSG.RankThree.PartOne.SEITZU49.Circ (shiftZ_mulVec)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

local notation "σ" => unitaryInvolution K 2 f

theorem herm_mulVec_conjTr {g : Matrix (Fin 5) (Fin 5) K} (hg : conjTr σ g * g = 1)
    (a v : Fin 5 → K) : herm σ (g *ᵥ a) v = herm σ a (conjTr σ g *ᵥ v) := by
  have hv : g *ᵥ (conjTr σ g *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Eich.mul_conjTr_of σ hg, Matrix.one_mulVec]
  conv_lhs => rw [← hv]
  exact Eich.isom_of_conjTr σ hg a _

theorem Cset_conjU (hσ : ∀ c : K, σ (σ c) = c) (M : Subgroup (SUid σ 5))
    {g : Matrix (Fin 5) (Fin 5) K} (hg : conjTr σ g * g = 1)
    (hM : ∀ x ∈ M, Eich.conjU σ g hg x ∈ M) {a : Fin 5 → K} (ha : a ∈ Cset hσ M) :
    g *ᵥ a ∈ Cset hσ M := by
  obtain ⟨ha0, ha⟩ := ha
  have ha' : herm σ (g *ᵥ a) (g *ᵥ a) = 0 := by rw [Eich.isom_of_conjTr σ hg, ha0]
  refine ⟨ha', fun c hc => ?_⟩
  have e : tv hσ ha' hc = Eich.conjU σ g hg (tv hσ ha0 hc) := by
    apply ext_smul
    intro v
    rw [Eich.conjU_smul]
    have h1 : CFSG.RankThree.PartOne.CTP.U5Gen.mat σ (tv hσ ha0 hc) *ᵥ (conjTr σ g *ᵥ v) =
        conjTr σ g *ᵥ v + (c * herm σ a (conjTr σ g *ᵥ v)) • a :=
      tv_smul hσ ha0 hc (conjTr σ g *ᵥ v)
    rw [h1, tv_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Eich.mul_conjTr_of σ hg, Matrix.one_mulVec, herm_mulVec_conjTr hg a v]
  rw [e]
  exact hM _ (ha c hc)

theorem plane_point_Y (hσ : ∀ c : K, σ (σ c) = c) (h2 : (2 : K) = 0) (M : Subgroup (SUid σ 5))
    (hD : ∀ (τ : K) (hτ : σ τ * τ = 1), dgTau τ hτ ∈ M) {w : K} (hwσ : σ w = w)
    (hY : (![0, w, w, 1, 1] : Fin 5 → K) ∈ Cset hσ M) {τ : K} (hτ : σ τ * τ = 1) (hτ1 : τ ≠ 1) :
    (![0, 0, 0, 1 + τ, 1 + τ⁻¹] : Fin 5 → K) ∈ Cset hσ M := by
  have h0 : τ ≠ 0 := ne_zero_of_norm_one σ hτ
  have hστ : σ τ = τ⁻¹ := by field_simp; linear_combination hτ
  have hy' : (![0, w, w, τ, τ⁻¹] : Fin 5 → K) ∈ Cset hσ M := by
    have := Cset_conj_mem hσ M (dgTau τ hτ) (hD τ hτ) hY
    rw [dgTau_smul] at this
    convert this using 1
    ext i
    fin_cases i <;> simp
  have hlam : herm σ (![0, w, w, τ, τ⁻¹] : Fin 5 → K) ![0, w, w, 1, 1] = τ + τ⁻¹ := by
    simp only [herm, Fin.sum_univ_five]
    simp [hστ, hwσ, map_inv₀]
    linear_combination (w * w) * h2
  have hne : τ + τ⁻¹ ≠ 0 := by
    intro h
    have h1 : τ ^ 2 + 1 = 0 := by field_simp at h; linear_combination h
    have h3 : (τ + 1) ^ 2 = 0 := by linear_combination h1 + (τ) * h2
    have h4 : τ + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
    exact hτ1 (by linear_combination h4 - h2)
  have := Cset_pair hσ M h2 hY hy' (by rw [hlam, map_add, map_inv₀, hστ, inv_inv]; ring)
    (by rw [hlam]; exact hne)
  convert this using 1
  ext i
  fin_cases i <;> simp
  all_goals linear_combination (-w) * h2

theorem plane_all_Y (hσ : ∀ c : K, σ (σ c) = c) (hσi : IsUnitaryInvolution σ) (h2 : (2 : K) = 0)
    (M : Subgroup (SUid σ 5)) (hD : ∀ (τ : K) (hτ : σ τ * τ = 1), dgTau τ hτ ∈ M) {w : K}
    (hwσ : σ w = w) (hY : (![0, w, w, 1, 1] : Fin 5 → K) ∈ Cset hσ M) (a₃ a₄ : K)
    (h : σ a₃ * a₃ = σ a₄ * a₄) : (![0, 0, 0, a₃, a₄] : Fin 5 → K) ∈ Cset hσ M := by
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := hσi.exists_norm_one_ne_one
  have hτ0 : τ₀ ≠ 0 := ne_zero_of_norm_one σ hτ₀
  have hu₀ := plane_point_Y hσ h2 M hD hwσ hY hτ₀ hτ₀1
  have hu : 1 + τ₀ ≠ 0 := by
    intro h'
    exact hτ₀1 (by linear_combination h' - h2)
  have hστ : σ τ₀ = τ₀⁻¹ := by field_simp; linear_combination hτ₀
  have hu' : 1 + τ₀⁻¹ ≠ 0 := by
    intro h'
    apply hu
    have : τ₀ * (1 + τ₀⁻¹) = 1 + τ₀ := by field_simp; ring
    rw [← this, h', mul_zero]
  refine plane_all_of_point hσ h2 M hD hu hu' ?_ hu₀ a₃ a₄ h
  rw [map_add, map_add, map_one, map_inv₀, hστ, inv_inv]
  ring

omit [Finite K] [CharP K 2] in
theorem shiftZ_extVec_zero (z : K) (a : Fin 2 → K) : shiftZ z *ᵥ extVec 0 a = extVec 1 a := by
  rw [shiftZ_mulVec]
  ext k
  simp only [extVec_eq]
  fin_cases k <;> simp

omit [Finite K] [CharP K 2] in
theorem shiftZ_extVec_one (z : K) (a : Fin 2 → K) : shiftZ z *ᵥ extVec 1 a = extVec 2 a := by
  rw [shiftZ_mulVec]
  ext k
  simp only [extVec_eq]
  fin_cases k <;> simp

omit [Finite K] [CharP K 2] in
theorem shiftZ_shiftZ_extVec_three (z : K) (a : Fin 2 → K) :
    shiftZ z *ᵥ (shiftZ z *ᵥ extVec 3 a) = z • extVec 0 a := by
  rw [shiftZ_mulVec, shiftZ_mulVec]
  ext k
  simp only [extVec_eq, Pi.smul_apply, smul_eq_mul]
  fin_cases k <;> simp

theorem eq_top_of_ext3_shiftZ (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 2 ^ f ≠ 2)
    {z : K} (hz : σ z * z = 1) (M : Subgroup (SUid σ 5))
    (hext3 : ∀ a : Fin 2 → K, herm σ a a = 0 →
      extVec 3 a ∈ Cset (unitaryInvolution_involutive hK) M)
    (hS : ∀ x ∈ M, Eich.conjU σ (shiftZ z) (Circ.conjTr_shiftZ_mul σ z hz) x ∈ M) : M = ⊤ := by
  have hσ : ∀ c : K, σ (σ c) = c := unitaryInvolution_involutive hK
  have hσi : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution (p := 2) (f := f) hK
  have hz0 : z ≠ 0 := ne_zero_of_norm_one σ hz
  have hshift : ∀ {v : Fin 5 → K}, v ∈ Cset hσ M → shiftZ z *ᵥ v ∈ Cset hσ M :=
    fun hv => Cset_conjU hσ M (Circ.conjTr_shiftZ_mul σ z hz) hS hv
  have hext0 : ∀ a : Fin 2 → K, herm σ a a = 0 → extVec 0 a ∈ Cset hσ M := by
    intro a ha
    have h1 := hshift (hshift (hext3 a ha))
    rw [shiftZ_shiftZ_extVec_three] at h1
    have := Cset_smul hσ M h1 z⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hz0, one_smul] at this
  have hext1 : ∀ a : Fin 2 → K, herm σ a a = 0 → extVec 1 a ∈ Cset hσ M := by
    intro a ha
    rw [← shiftZ_extVec_zero z a]
    exact hshift (hext0 a ha)
  have hext2 : ∀ a : Fin 2 → K, herm σ a a = 0 → extVec 2 a ∈ Cset hσ M := by
    intro a ha
    rw [← shiftZ_extVec_one z a]
    exact hshift (hext1 a ha)
  rw [eq_top_iff, ← iSup_range_blockEmb2 (K := K) (p := 2) (f := f) hK hq 4]
  refine iSup_le fun i => range_blockEmb2_le hσ hσi M i ?_
  fin_cases i
  · exact hext0
  · exact hext1
  · exact hext2
  · exact hext3

theorem eq_top_of_Y_mem_Cset (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 2 ^ f ≠ 2)
    {z : K} (hz : σ z * z = 1) {M : Subgroup (SUid σ 5)} (hM : GenHyp σ z hz M) {w : K}
    (hwσ : σ w = w)
    (hY : (![0, w, w, 1, 1] : Fin 5 → K) ∈ Cset (unitaryInvolution_involutive hK) M) :
    M = ⊤ := by
  have h2 : (2 : K) = 0 := two_eq_zero
  have hσ : ∀ c : K, σ (σ c) = c := unitaryInvolution_involutive hK
  have hσi : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution (p := 2) (f := f) hK
  refine eq_top_of_ext3_shiftZ hK hq hz M (fun a ha => ?_) hM.stab
  have e : extVec 3 a = ![0, 0, 0, a 0, a 1] := by
    ext k
    fin_cases k <;> simp [extVec_eq]
  rw [e]
  refine plane_all_Y hσ hσi h2 M (fun τ hτ => hM.diag _ _ _) hwσ hY (a 0) (a 1) ?_
  simp only [herm, Fin.sum_univ_two] at ha
  linear_combination ha - (σ (a 1) * a 1) * h2

end CFSG.RankThree.PartOne.SEITZU49.Gen
