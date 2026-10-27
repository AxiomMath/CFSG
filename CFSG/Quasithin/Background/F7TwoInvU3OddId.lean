module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionEigen
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
public import CFSG.LinearAlgebra.LinearGroups.UnitaryTransitivity

public section

namespace CFSG.Quasithin.F7Two.U3Odd

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem finrank_hypIndex_one : Module.finrank K (HypIndex 1 1 → K) = 3 := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp

theorem exists_hyperbolic_pair_of_plane (h : UnitaryFieldData p f K)
    {W : Submodule K (HypIndex 1 1 → K)} (hW : Module.finrank K W = 2)
    (hnd : ∀ w ∈ W, (∀ w' ∈ W, hypForm h 1 1 w w' = 0) → w = 0) :
    ∃ a ∈ W, ∃ b ∈ W, hypForm h 1 1 a a = 0 ∧ hypForm h 1 1 b b = 0 ∧
      hypForm h 1 1 a b = 1 := by
  have hsymm : ((hypForm h 1 1).domRestrict₁₂ W W).IsSymm := (hypForm_isSymm h).domRestrict _
  have hsep : ((hypForm h 1 1).domRestrict₁₂ W W).SeparatingLeft := fun w hw =>
    Subtype.ext (hnd w w.2 fun w' hw' => hw ⟨w', hw'⟩)
  obtain ⟨a, ha0, haa⟩ := exists_isotropic_of_finrank_two h hsymm hsep hW
  obtain ⟨⟨b, hab, hbb⟩, -⟩ := hermitian_hyperbolic_splitting h hsymm hsep ha0 haa
  exact ⟨a, a.2, b, b.2, haa, hbb, hab⟩

theorem exists_hyperbolic_pair_of_compl_orth (h : UnitaryFieldData p f K)
    {W W' : Submodule K (HypIndex 1 1 → K)} (hc : IsCompl W W') (hW : Module.finrank K W = 2)
    (horth : ∀ v ∈ W, ∀ w ∈ W', hypForm h 1 1 v w = 0) :
    ∃ a ∈ W, ∃ b ∈ W, hypForm h 1 1 a a = 0 ∧ hypForm h 1 1 b b = 0 ∧
      hypForm h 1 1 a b = 1 := by
  refine exists_hyperbolic_pair_of_plane h hW fun w hw hw0 => ?_
  refine hypForm_separatingLeft h w fun x => ?_
  obtain ⟨y, z, hy, hz, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint x
  rw [map_add, hw0 y hy, horth w hw z hz, add_zero]

theorem exists_stable_pair_of_sq (hp2 : p ≠ 2) {A : GL (HypIndex 1 1) K}
    (hA : A ∈ hypUnitary h 1 1) {c : K} (hcN : h.norm c = 1)
    (hAA : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = c • 1)
    (hns : ∀ c' : K, (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) ≠ c' • 1) :
    ∃ (a b : HypIndex 1 1 → K) (l₁ l₃ : K), hypForm h 1 1 a a = 0 ∧ hypForm h 1 1 b b = 0 ∧
      hypForm h 1 1 a b = 1 ∧ (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ a = l₁ • a ∧
        (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ b = l₃ • b := by
  classical
  set AM : Matrix (HypIndex 1 1) (HypIndex 1 1) K := (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K)
    with hAM
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨l, hl0, hl2⟩ := exists_sq_eq_of_norm_eq_one h hp2 hcN
  let T0 : Module.End K (HypIndex 1 1 → K) := Matrix.toLin' AM
  have hT0 : ∀ v, T0 v = AM *ᵥ v := fun v => rfl
  have hAAend : T0 * T0 = (l ^ 2) • 1 := by
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, hT0, hT0, mulVec_mulVec, hAA, LinearMap.smul_apply,
      Module.End.one_apply, hl2, Matrix.smul_mulVec, one_mulVec]
  have hTT := invSMulOp_mul_self hl0 hAAend
  have hcompl := isCompl_ker_sub_one_ker_add_one h2 hTT
  have hns' : ∀ c' : K, T0 ≠ c' • 1 := by
    intro c' hc'
    refine hns c' (Matrix.toLin'.injective ?_)
    rw [map_smul, Matrix.toLin'_one]
    exact hc'
  obtain ⟨hnep, hnem⟩ := eigen_ne_bot h2 hl0 hAAend hns'
  have hiso : ∀ v w, hypForm h 1 1 (AM *ᵥ v) (AM *ᵥ w) = hypForm h 1 1 v w :=
    (gramForm_isometry_iff h _ AM).mpr (mem_hypUnitary.mp hA)
  have hTv : ∀ v, invSMulOp l T0 v = l⁻¹ • (AM *ᵥ v) := fun v => rfl
  have hTB : ∀ v w, hypForm h 1 1 (invSMulOp l T0 v) (invSMulOp l T0 w) =
      (h.norm l)⁻¹ * hypForm h 1 1 v w := by
    intro v w
    rw [hTv, hTv, sesq_smul_smul (B := hypForm h 1 1), hiso]
    congr 1
    simp only [UnitaryFieldData.norm, map_inv₀, mul_inv]
  have hNN : h.norm l * h.norm l = 1 := by
    have h1 : h.norm c = h.norm l * h.norm l := by
      rw [← hl2, sq]
      simp only [UnitaryFieldData.norm, map_mul]
      ring
    rw [← h1, hcN]
  have hdim : Module.finrank K (LinearMap.ker (invSMulOp l T0 - 1)) +
      Module.finrank K (LinearMap.ker (invSMulOp l T0 + 1)) = 3 := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    rwa [finrank_hypIndex_one] at this
  have h1p := Submodule.one_le_finrank_iff.mpr hnep
  have h1m := Submodule.one_le_finrank_iff.mpr hnem
  have hWp : ∀ v ∈ LinearMap.ker (invSMulOp l T0 - 1), AM *ᵥ v = l • v := by
    intro v hv
    have := apply_eq_of_mem_ker_sub_one hv
    rw [hTv] at this
    exact (inv_smul_eq_iff₀ hl0).mp this
  have hWm : ∀ v ∈ LinearMap.ker (invSMulOp l T0 + 1), AM *ᵥ v = (-l) • v := by
    intro v hv
    have := apply_eq_neg_of_mem_ker_add_one hv
    rw [hTv] at this
    rw [neg_smul, ← smul_neg]
    exact (inv_smul_eq_iff₀ hl0).mp this
  rcases mul_self_eq_one_iff.mp hNN with hN1 | hNm1
  ·
    have hT' : ∀ v w, hypForm h 1 1 (invSMulOp l T0 v) (invSMulOp l T0 w) =
        hypForm h 1 1 v w := fun v w => by rw [hTB, hN1, inv_one, one_mul]
    have horth : ∀ v ∈ LinearMap.ker (invSMulOp l T0 - 1),
        ∀ w ∈ LinearMap.ker (invSMulOp l T0 + 1), hypForm h 1 1 v w = 0 :=
      fun v hv w hw => sesq_eq_zero_of_eigen_one h2 hT' hv hw
    by_cases hdp : Module.finrank K (LinearMap.ker (invSMulOp l T0 - 1)) = 2
    · obtain ⟨a, ha, b, hb, haa, hbb, hab⟩ := exists_hyperbolic_pair_of_compl_orth h hcompl hdp
        horth
      exact ⟨a, b, l, l, haa, hbb, hab, hWp a ha, hWp b hb⟩
    · have hdm : Module.finrank K (LinearMap.ker (invSMulOp l T0 + 1)) = 2 := by omega
      have horth' : ∀ v ∈ LinearMap.ker (invSMulOp l T0 + 1),
          ∀ w ∈ LinearMap.ker (invSMulOp l T0 - 1), hypForm h 1 1 v w = 0 := fun v hv w hw => by
        rw [← (hypForm_isSymm h).eq w v, horth w hw v hv, map_zero]
      obtain ⟨a, ha, b, hb, haa, hbb, hab⟩ := exists_hyperbolic_pair_of_compl_orth h hcompl.symm
        hdm horth'
      exact ⟨a, b, -l, -l, haa, hbb, hab, hWm a ha, hWm b hb⟩
  ·
    exfalso
    have hT' : ∀ v w, hypForm h 1 1 (invSMulOp l T0 v) (invSMulOp l T0 w) =
        -hypForm h 1 1 v w := fun v w => by
      rw [hTB, hNm1, inv_neg, inv_one, neg_one_mul]
    have bp := finrank_le_of_isTotIso h (hypForm_isSymm h) (hypForm_separatingLeft h)
      (fun x hx y hy => sesq_eq_zero_of_eigen_neg_plus h2 hT' hx hy)
    have bm := finrank_le_of_isTotIso h (hypForm_isSymm h) (hypForm_separatingLeft h)
      (fun x hx y hy => sesq_eq_zero_of_eigen_neg_minus h2 hT' hx hy)
    rw [finrank_hypIndex_one] at bp bm
    omega

end CFSG.Quasithin.F7Two.U3Odd
