module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5TorusV
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5TorusDelta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.Om4 Matrix

variable {K : Type} [Field K] [Finite K]

private theorem s16c11_case5_D0_le_normalizer_of_forward
    {A : Subgroup (MulAut (VM K))}
    (h : ∀ μ : Kˣ, ∀ y ∈ A,
      s16c11_case5_D0Hom μ * y * (s16c11_case5_D0Hom μ)⁻¹ ∈ A) :
    s16c11_case5_D0 (K := K) ≤ Subgroup.normalizer (A : Set (MulAut (VM K))) := by
  intro x hx
  change x ∈ s16c11_case5_D0Hom.range at hx
  rw [MonoidHom.mem_range] at hx
  obtain ⟨μ, rfl⟩ := hx
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · exact fun hy => h μ y hy
  · intro hy
    have hy' := h μ⁻¹ (s16c11_case5_D0Hom μ * y * (s16c11_case5_D0Hom μ)⁻¹) hy
    rw [map_inv, inv_inv] at hy'
    have hconj : (s16c11_case5_D0Hom μ)⁻¹ *
        (s16c11_case5_D0Hom μ * y * (s16c11_case5_D0Hom μ)⁻¹) *
        s16c11_case5_D0Hom μ = y := by group
    rwa [hconj] at hy'

theorem s16c11_case5_D0_le_normalizer_Delta :
    s16c11_case5_D0 (K := K) ≤
      Subgroup.normalizer (s16c11_case5_Delta (K := K) : Set (MulAut (VM K))) := by
  refine s16c11_case5_D0_le_normalizer_of_forward ?_
  intro μ y hy
  rw [s16c11_case5_mem_Delta] at hy ⊢
  obtain ⟨a, rfl⟩ := hy
  exact ⟨(μ : K) ^ 2 * a, s16c11_case5_D0_conj_rhoU μ a a⟩

theorem s16c11_case5_D0_le_normalizer_zpowers_sigma :
    s16c11_case5_D0 (K := K) ≤
      Subgroup.normalizer (Subgroup.zpowers (s16c11_case5_sigma (K := K)) :
        Set (MulAut (VM K))) := by
  refine s16c11_case5_D0_le_normalizer_of_forward ?_
  intro μ y hy
  rw [Subgroup.mem_zpowers_iff] at hy
  obtain ⟨n, rfl⟩ := hy
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨n, ?_⟩
  have hcomm : Commute (s16c11_case5_D0Hom μ) (s16c11_case5_sigma (K := K)) :=
    s16c11_case5_D0_comm_sigma μ
  rw [show s16c11_case5_D0Hom μ * s16c11_case5_sigma ^ n *
        (s16c11_case5_D0Hom μ)⁻¹ = s16c11_case5_sigma ^ n by
      rw [(hcomm.zpow_right n).eq, mul_assoc, mul_inv_cancel, mul_one]]

theorem s16c11_case5_D0_le_normalizer_of_kInv {A : Subgroup (MulAut (VM K))}
    (hAV : A ≤ s16c11_case5_V)
    (hinv : ∀ c a b : K, s16c11_case5_rhoU a b ∈ A → s16c11_case5_rhoU (c * a) (c * b) ∈ A) :
    s16c11_case5_D0 (K := K) ≤ Subgroup.normalizer (A : Set (MulAut (VM K))) := by
  refine s16c11_case5_D0_le_normalizer_of_forward ?_
  intro μ y hy
  have hyV : y ∈ s16c11_case5_V := hAV hy
  rw [s16c11_case5_mem_V] at hyV
  obtain ⟨⟨a, b⟩, rfl⟩ := hyV
  rw [s16c11_case5_D0_conj_rhoU]
  exact hinv ((μ : K) ^ 2) a b hy

theorem s16c11_case5_D0_le_normalizer_of_mem_aSet (hK : Nat.card K = 4)
    {A : Subgroup (MulAut (VM K))} (hA : A ∈ E3.aSet 2 (s16c11_case5_S0 (K := K))) :
    s16c11_case5_D0 (K := K) ≤ Subgroup.normalizer (A : Set (MulAut (VM K))) := by
  by_cases hAV : A ≤ s16c11_case5_V
  · exact s16c11_case5_D0_le_normalizer_of_kInv hAV
      (fun c a b hab => s16c11_case5_V_kInv hK hAV hA hab c)
  · rw [s16c11_case5_eq_Delta_sup_sigma hK hA hAV]
    exact (le_inf s16c11_case5_D0_le_normalizer_Delta
      s16c11_case5_D0_le_normalizer_zpowers_sigma).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
