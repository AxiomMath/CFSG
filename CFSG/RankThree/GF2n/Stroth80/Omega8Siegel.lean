module

public import CFSG.RankThree.GF2n.Stroth80.SmithEightHolds
public import CFSG.LieType.D4Small.Om8Datum
public import CFSG.ClassicalGroups.Orthogonal.Lines
public import CFSG.RankThree.GF2n.Smith81.Orth212C5Alg
public import CFSG.ClassicalGroups.SpecialLinear.InvariantForms
public import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.RankThree.GF2n.Smith81.EStmt
public import CFSG.RankThree.GF2n.Smith81.OrthE2Layer
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC
public import CFSG.RankThree.GF2n.Stroth80.Sec1110ModuleDual
public import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.RankThree.GF2n.Stroth80.SpHomTrivial

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem polar_quadPlus_eq (v w : Fin 4 ⊕ Fin 4 → K) :
    polar (quadPlus 4 K) v w =
      StatedQuadPlus 4 K (v + w) - StatedQuadPlus 4 K v - StatedQuadPlus 4 K w := by
  rw [QuadraticMap.polar, coe_quadPlus]

private theorem siegel_decomp {u w v₁ v₂ : Fin 4 ⊕ Fin 4 → K}
    (N : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (hNker : ∀ v, polar (quadPlus 4 K) v u = 0 → polar (quadPlus 4 K) v w = 0 → N v = 0)
    (hv₁u : polar (quadPlus 4 K) v₁ u = 1) (hv₁w : polar (quadPlus 4 K) v₁ w = 0)
    (hv₂u : polar (quadPlus 4 K) v₂ u = 0) (hv₂w : polar (quadPlus 4 K) v₂ w = 1) :
    ∀ v, N v = polar (quadPlus 4 K) v u • N v₁ + polar (quadPlus 4 K) v w • N v₂ := by
  intro v
  have hz : N (v - polar (quadPlus 4 K) v u • v₁ - polar (quadPlus 4 K) v w • v₂) = 0 := by
    apply hNker
    · rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, smul_eq_mul,
        smul_eq_mul, hv₁u, hv₂u]
      ring
    · rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, smul_eq_mul,
        smul_eq_mul, hv₁w, hv₂w]
      ring
  have hlin : N (v - polar (quadPlus 4 K) v u • v₁ - polar (quadPlus 4 K) v w • v₂) =
      N v - polar (quadPlus 4 K) v u • N v₁ - polar (quadPlus 4 K) v w • N v₂ := by
    rw [map_sub, map_sub, map_smul, map_smul]
  rw [hlin] at hz
  have h1 : N v - polar (quadPlus 4 K) v u • N v₁ = polar (quadPlus 4 K) v w • N v₂ :=
    sub_eq_zero.mp hz
  rw [sub_eq_iff_eq_add] at h1
  rw [h1, add_comm]

private theorem siegel_coeff {u w v₁ v₂ : Fin 4 ⊕ Fin 4 → K}
    (N : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (hNmem : ∀ v, N v ∈ Submodule.span K {u, w})
    (hBvNv : ∀ v, polar (quadPlus 4 K) v (N v) = 0)
    (hv₁u : polar (quadPlus 4 K) v₁ u = 1) (hv₁w : polar (quadPlus 4 K) v₁ w = 0)
    (hv₂u : polar (quadPlus 4 K) v₂ u = 0) (hv₂w : polar (quadPlus 4 K) v₂ w = 1)
    (hdec : ∀ v, N v = polar (quadPlus 4 K) v u • N v₁ + polar (quadPlus 4 K) v w • N v₂) :
    ∃ b : K, ∀ v, N v = b • (polar (quadPlus 4 K) v w • u +
      polar (quadPlus 4 K) v u • w) := by
  obtain ⟨m₁₁, m₂₁, hm₁⟩ := Submodule.mem_span_pair.mp (hNmem v₁)
  obtain ⟨m₁₂, m₂₂, hm₂⟩ := Submodule.mem_span_pair.mp (hNmem v₂)
  have hm₁₁ : m₁₁ = 0 := by
    have h := hBvNv v₁
    rw [← hm₁, polar_add_right, polar_smul_right, polar_smul_right, smul_eq_mul,
      smul_eq_mul, hv₁u, hv₁w] at h
    simpa using h
  have hm₂₂ : m₂₂ = 0 := by
    have h := hBvNv v₂
    rw [← hm₂, polar_add_right, polar_smul_right, polar_smul_right, smul_eq_mul,
      smul_eq_mul, hv₂u, hv₂w] at h
    simpa using h
  have hsum : m₁₂ + m₂₁ = 0 := by
    have h12 : polar (quadPlus 4 K) v₁ (N v₂) = m₁₂ := by
      rw [← hm₂, polar_add_right, polar_smul_right, polar_smul_right, smul_eq_mul,
        smul_eq_mul, hv₁u, hv₁w, mul_one, mul_zero, add_zero]
    have h21 : polar (quadPlus 4 K) v₂ (N v₁) = m₂₁ := by
      rw [← hm₁, polar_add_right, polar_smul_right, polar_smul_right, smul_eq_mul,
        smul_eq_mul, hv₂u, hv₂w, mul_zero, mul_one, zero_add]
    have h := hBvNv (v₁ + v₂)
    rw [map_add, polar_add_left, polar_add_right, polar_add_right, hBvNv v₁, h12, h21,
      hBvNv v₂, zero_add, add_zero] at h
    exact h
  have hb : m₁₂ = m₂₁ := by
    have h := hsum
    rw [add_eq_zero_iff_eq_neg] at h
    rwa [CharTwo.neg_eq] at h
  refine ⟨m₂₁, fun v => ?_⟩
  have hNv : N v = m₂₁ • (polar (quadPlus 4 K) v w • u +
      polar (quadPlus 4 K) v u • w) := by
    have hstep : N v = polar (quadPlus 4 K) v u • (m₂₁ • w) +
        polar (quadPlus 4 K) v w • (m₂₁ • u) := by
      rw [hdec, ← hm₁, ← hm₂]
      simp [hm₁₁, hm₂₂, hb]
    rw [hstep, smul_comm (polar (quadPlus 4 K) v u) m₂₁ w,
      smul_comm (polar (quadPlus 4 K) v w) m₂₁ u, ← smul_add, add_comm]
  exact hNv

private theorem siegel_endomorphism (u w : Fin 4 ⊕ Fin 4 → K)
    (hli : LinearIndependent K ![u, w])
    (N : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (hNmem : ∀ v, N v ∈ Submodule.span K {u, w})
    (hNker : ∀ v, polar (quadPlus 4 K) v u = 0 → polar (quadPlus 4 K) v w = 0 → N v = 0)
    (hBvNv : ∀ v, polar (quadPlus 4 K) v (N v) = 0) :
    ∃ b : K, ∀ v, N v = b • (polar (quadPlus 4 K) v w • u +
      polar (quadPlus 4 K) v u • w) := by
  have hnd : ∀ x : Fin 4 ⊕ Fin 4 → K, (∀ v, polar (quadPlus 4 K) x v = 0) → x = 0 := by
    intro x hx
    exact (nondegenerate_polarBilin_quadPlus 4 K).1 x (fun v => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hx v)
  obtain ⟨v₁, v₂, hv₁u, hv₁w, hv₂u, hv₂w⟩ :=
    CFSG.RankThree.GF2n.Smith81.OrthC5.exists_dual hnd hli
  have hv₁u' : polar (quadPlus 4 K) v₁ u = 1 := by rw [polar_comm]; exact hv₁u
  have hv₁w' : polar (quadPlus 4 K) v₁ w = 0 := by rw [polar_comm]; exact hv₁w
  have hv₂u' : polar (quadPlus 4 K) v₂ u = 0 := by rw [polar_comm]; exact hv₂u
  have hv₂w' : polar (quadPlus 4 K) v₂ w = 1 := by rw [polar_comm]; exact hv₂w
  exact siegel_coeff N hNmem hBvNv hv₁u' hv₁w' hv₂u' hv₂w'
    (siegel_decomp N hNker hv₁u' hv₁w' hv₂u' hv₂w')

private theorem siegel_hBvNv {u w : Fin 4 ⊕ Fin 4 → K} (hu : quadPlus 4 K u = 0)
    (hw : quadPlus 4 K w = 0) (hBuw : polar (quadPlus 4 K) u w = 0)
    (g : StatedOmega (StatedQuadPlus 4 K))
    (N : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (hNapply : ∀ v, N v = ((g : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v - v)
    (hNmem : ∀ v, N v ∈ Submodule.span K {u, w}) :
    ∀ v, polar (quadPlus 4 K) v (N v) = 0 := by
  have hQspan : ∀ z ∈ Submodule.span K ({u, w} : Set (Fin 4 ⊕ Fin 4 → K)),
      quadPlus 4 K z = 0 := by
    intro z hz
    rw [Submodule.mem_span_pair] at hz
    obtain ⟨a, b, rfl⟩ := hz
    have hsplit := QuadraticMap.map_add (quadPlus 4 K) (a • u) (b • w)
    rw [hsplit, QuadraticMap.map_smul, QuadraticMap.map_smul, hu, hw]
    simp [polar_smul_left, polar_smul_right, hBuw]
  intro v
  have hQN : quadPlus 4 K (N v) = 0 := hQspan (N v) (hNmem v)
  have hgv : ((g : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v = v + N v := by
    rw [hNapply]; abel
  have hiso : quadPlus 4 K (((g : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v) = quadPlus 4 K v := by
    simpa [coe_quadPlus] using
      CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.isometry_of_mem_statedOmega
        (f := StatedQuadPlus 4 K) g.2 v
  rw [QuadraticMap.polar, ← hgv, hiso, hQN, sub_self, sub_zero]

theorem siegel_form (u w : Fin 4 ⊕ Fin 4 → K) (hli : LinearIndependent K ![u, w])
    (hu : StatedQuadPlus 4 K u = 0) (hw : StatedQuadPlus 4 K w = 0)
    (huw : StatedQuadPlus 4 K (u + w) = 0) (g : StatedOmega (StatedQuadPlus 4 K))
    (hN : ∀ v, ((g : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v - v ∈ Submodule.span K {u, w})
    (hfix : ∀ v, StatedQuadPlus 4 K (v + u) - StatedQuadPlus 4 K v -
        StatedQuadPlus 4 K u = 0 →
      StatedQuadPlus 4 K (v + w) - StatedQuadPlus 4 K v - StatedQuadPlus 4 K w = 0 →
      ((g : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v = v) :
    ∃ b : K, ∀ v, ((g : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v =
      v + b • ((StatedQuadPlus 4 K (v + w) - StatedQuadPlus 4 K v -
          StatedQuadPlus 4 K w) • u +
        (StatedQuadPlus 4 K (v + u) - StatedQuadPlus 4 K v -
          StatedQuadPlus 4 K u) • w) := by
  have hu' : quadPlus 4 K u = 0 := by simpa [coe_quadPlus] using hu
  have hw' : quadPlus 4 K w = 0 := by simpa [coe_quadPlus] using hw
  have hBuw : polar (quadPlus 4 K) u w = 0 := by
    simp [QuadraticMap.polar, coe_quadPlus, huw, hu, hw]
  let N : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
    (toLinEquiv (Fin 4 ⊕ Fin 4) K (g : GL (Fin 4 ⊕ Fin 4) K)).toLinearMap - LinearMap.id
  have hNapply : ∀ v, N v = ((g : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v - v := by
    intro v
    change (toLinEquiv (Fin 4 ⊕ Fin 4) K (g : GL (Fin 4 ⊕ Fin 4) K)) v - v = _
    rw [toLinEquiv_apply]
  have hNmem : ∀ v, N v ∈ Submodule.span K {u, w} := by
    intro v
    rw [hNapply]
    exact hN v
  have hNker : ∀ v, polar (quadPlus 4 K) v u = 0 → polar (quadPlus 4 K) v w = 0 → N v = 0 := by
    intro v hv1 hv2
    rw [hNapply, sub_eq_zero]
    apply hfix
    · simpa [QuadraticMap.polar, coe_quadPlus] using hv1
    · simpa [QuadraticMap.polar, coe_quadPlus] using hv2
  obtain ⟨b, hb⟩ := siegel_endomorphism u w hli N hNmem hNker
    (siegel_hBvNv hu' hw' hBuw g N hNapply hNmem)
  refine ⟨b, fun v => ?_⟩
  have hgv : ((g : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v = v + N v := by
    rw [hNapply]; abel
  rw [hgv, hb v, polar_quadPlus_eq, polar_quadPlus_eq]

theorem exists_statedOmega_line (u w : Fin 4 ⊕ Fin 4 → K) (hli : LinearIndependent K ![u, w])
    (hu : StatedQuadPlus 4 K u = 0) (hw : StatedQuadPlus 4 K w = 0)
    (huw : StatedQuadPlus 4 K (u + w) = 0) :
    ∃ A : StatedOmega (StatedQuadPlus 4 K),
      ((A : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ
        plusVec 4 K 0 true = u ∧
      ((A : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ
        plusVec 4 K 1 true = w := by
  have hu' : quadPlus 4 K u = 0 := by simpa [coe_quadPlus] using hu
  have hw' : quadPlus 4 K w = 0 := by simpa [coe_quadPlus] using hw
  have hBuw : polar (quadPlus 4 K) u w = 0 := by
    simp [QuadraticMap.polar, coe_quadPlus, huw, hu, hw]
  have hnd := nondegenerate_polarBilin_quadPlus 4 K
  have hli' := LinearIndependent.pair_iff.mp hli
  have hu0 : u ≠ 0 := fun h0 =>
    one_ne_zero ((hli' 1 0 (by rw [h0, smul_zero, zero_smul, add_zero])).1)
  have h₁₂ : (plusPair K (0 : Fin 4)).Orth (plusPair K (1 : Fin 4)) := plusPair_orth (by decide)
  have h₁₃ : (plusPair K (0 : Fin 4)).Orth (plusPair K (2 : Fin 4)) := plusPair_orth (by decide)
  have h₂₃ : (plusPair K (1 : Fin 4)).Orth (plusPair K (2 : Fin 4)) := plusPair_orth (by decide)
  obtain ⟨g₁, hg₁, hg₁u⟩ := exists_mem_elementaryGroup_apply_eq (Q := quadPlus 4 K) hnd h₁₂
    hu0 (plusPair K (0 : Fin 4)).e_ne_zero (by rw [hu', (plusPair K (0 : Fin 4)).Q_e])
  have hg₁O := elementaryGroup_le_orthogonalGroup (quadPlus 4 K) hg₁
  have hx : quadPlus 4 K (g₁ w) = 0 := by rw [map_of_mem hg₁O, hw']
  have hex : polar (quadPlus 4 K) (plusPair K (0 : Fin 4)).e (g₁ w) = 0 := by
    rw [← hg₁u, polar_map_of_mem hg₁O, hBuw]
  have hxe : ∀ c : K, g₁ w ≠ c • (plusPair K (0 : Fin 4)).e := by
    intro c hc
    rw [← hg₁u, ← map_smul] at hc
    have h1 := g₁.injective hc
    exact one_ne_zero (hli' (-c) 1 (by rw [h1, neg_smul, one_smul, neg_add_cancel])).2
  obtain ⟨g₂, hg₂, hg₂e, hg₂x⟩ :=
    exists_fix_apply_eq_of_polar_eq_zero h₁₂ h₁₃ h₂₃ hnd hx hex hxe
  have hgu : (g₂ * g₁) u = (plusPair K (0 : Fin 4)).e := by
    rw [LinearEquiv.mul_apply, hg₁u, hg₂e]
  have hgw : (g₂ * g₁) w = (plusPair K (1 : Fin 4)).e := by
    rw [LinearEquiv.mul_apply, hg₂x]
  refine ⟨(statedOmegaPlusEquiv (m := 4) (by norm_num)).symm
    ⟨(g₂ * g₁)⁻¹, inv_mem (mul_mem hg₂ hg₁)⟩, ?_, ?_⟩
  · rw [statedOmegaPlusEquiv_symm_app]
    change (g₂ * g₁)⁻¹ ((plusPair K (0 : Fin 4)).e) = u
    rw [← hgu]
    exact LinearEquiv.symm_apply_apply (g₂ * g₁) u
  · rw [statedOmegaPlusEquiv_symm_app]
    change (g₂ * g₁)⁻¹ ((plusPair K (1 : Fin 4)).e) = w
    rw [← hgw]
    exact LinearEquiv.symm_apply_apply (g₂ * g₁) w

private theorem conjPhi_reindex (A : StatedOmega (StatedQuadPlus 4 K))
    (z : Fin 4 ⊕ Fin 4 → K) :
    conjPhi A (reindexVectorEquiv (plusIndexEquiv 4) z) =
      ((A : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ z := by
  simp only [conjPhi, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, toLinEquiv_apply]

private theorem conjPhi_symm_apply (A : StatedOmega (StatedQuadPlus 4 K))
    (v : Fin 4 ⊕ Fin 4 → K) :
    (conjPhi A).symm v = reindexVectorEquiv (plusIndexEquiv 4)
      ((toLinEquiv (Fin 4 ⊕ Fin 4) K (A : GL (Fin 4 ⊕ Fin 4) K)).symm v) := by
  apply (conjPhi A).injective
  rw [LinearEquiv.apply_symm_apply, conjPhi_reindex, ← toLinEquiv_apply]
  exact (LinearEquiv.apply_symm_apply _ v).symm

private theorem eichlerC_reindex_plus (u w y : Fin 4 ⊕ Fin 4 → K) :
    AutOm.eichlerC (coordinateQuadPlus 4 K) (reindexVectorEquiv (plusIndexEquiv 4) u)
        (reindexVectorEquiv (plusIndexEquiv 4) w) (reindexVectorEquiv (plusIndexEquiv 4) y) =
      reindexVectorEquiv (plusIndexEquiv 4)
        (y + polar (quadPlus 4 K) y u • w - polar (quadPlus 4 K) y w • u -
          (quadPlus 4 K w * polar (quadPlus 4 K) y u) • u) := by
  rw [AutOm.eichlerC, AutOm.polar_reindex_plus, AutOm.polar_reindex_plus, coordinateQuadPlus,
    reindexQuadraticForm_map, map_sub, map_sub, map_add, LinearEquiv.map_smul,
    LinearEquiv.map_smul, LinearEquiv.map_smul]

private theorem map_eichlerC_singular (A : StatedOmega (StatedQuadPlus 4 K)) (c : K)
    (z : Fin 4 ⊕ Fin 4 → K) :
    ((A : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ
        (z + polar (quadPlus 4 K) z (plusVec 4 K 1 true) • (c • plusVec 4 K 0 true) -
          polar (quadPlus 4 K) z (c • plusVec 4 K 0 true) • plusVec 4 K 1 true -
          (quadPlus 4 K (c • plusVec 4 K 0 true) *
            polar (quadPlus 4 K) z (plusVec 4 K 1 true)) • plusVec 4 K 1 true) =
      ((A : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ z +
        c • (polar (quadPlus 4 K) (((A : GL (Fin 4 ⊕ Fin 4) K) :
                Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ z)
              (((A : GL (Fin 4 ⊕ Fin 4) K) :
                Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ plusVec 4 K 1 true) •
            (((A : GL (Fin 4 ⊕ Fin 4) K) :
              Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ plusVec 4 K 0 true) +
          polar (quadPlus 4 K) (((A : GL (Fin 4 ⊕ Fin 4) K) :
                Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ z)
              (((A : GL (Fin 4 ⊕ Fin 4) K) :
                Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ plusVec 4 K 0 true) •
            (((A : GL (Fin 4 ⊕ Fin 4) K) :
              Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ plusVec 4 K 1 true)) := by
  have hiso : ∀ z, quadPlus 4 K (((A : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ z) = quadPlus 4 K z := by
    intro z
    simpa [coe_quadPlus] using
      CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.isometry_of_mem_statedOmega
        (f := StatedQuadPlus 4 K) A.2 z
  have hpol : ∀ p q, polar (quadPlus 4 K) (((A : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ p)
      (((A : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ q) = polar (quadPlus 4 K) p q := by
    intro p q
    rw [QuadraticMap.polar, QuadraticMap.polar, ← Matrix.mulVec_add, hiso, hiso, hiso]
  have hQ0 : quadPlus 4 K (c • plusVec 4 K 0 true) = 0 := by
    rw [QuadraticMap.map_smul, quadPlus_plusVec, smul_zero]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [hQ0, polar_smul_right, smul_eq_mul]
  simp only [smul_zero, zero_mul, zero_smul, add_zero]
  rw [hpol z (plusVec 4 K 1 true), hpol z (plusVec 4 K 0 true), smul_add, smul_smul,
    smul_smul, smul_smul,
    mul_comm c (polar (quadPlus 4 K) z (plusVec 4 K 1 true))]
  have hneg : ∀ x : Fin 4 ⊕ Fin 4 → K, -x = x := by
    intro x
    rw [neg_eq_iff_add_eq_zero, ← two_smul K x,
      show (2 : K) = 0 from CharP.cast_eq_zero K 2, zero_smul]
  simp only [sub_eq_add_neg, hneg, add_zero]
  abel

theorem conjOm8_x_mulVec (A : StatedOmega (StatedQuadPlus 4 K)) (c : K)
    (v : Fin 4 ⊕ Fin 4 → K) :
    ((conjOm8 A ((om8Datum K).x (lv 0 1 true true) c) :
        StatedOmega (StatedQuadPlus 4 K)) : GL (Fin 4 ⊕ Fin 4) K) *ᵥ v =
      v + c • (polar (quadPlus 4 K) v
            (((A : GL (Fin 4 ⊕ Fin 4) K) :
              Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ plusVec 4 K 1 true) •
          (((A : GL (Fin 4 ⊕ Fin 4) K) :
            Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ plusVec 4 K 0 true) +
        polar (quadPlus 4 K) v
            (((A : GL (Fin 4 ⊕ Fin 4) K) :
              Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ plusVec 4 K 0 true) •
          (((A : GL (Fin 4 ⊕ Fin 4) K) :
            Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ plusVec 4 K 1 true)) := by
  set ρ : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin (2 * 4) → K) :=
    reindexVectorEquiv (plusIndexEquiv 4) with hρ
  set a₀ : Fin 4 ⊕ Fin 4 → K :=
    ((A : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ
      plusVec 4 K 0 true with ha₀
  set a₁ : Fin 4 ⊕ Fin 4 → K :=
    ((A : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ
      plusVec 4 K 1 true with ha₁
  set y : Fin 4 ⊕ Fin 4 → K :=
    (toLinEquiv (Fin 4 ⊕ Fin 4) K (A : GL (Fin 4 ⊕ Fin 4) K)).symm v with hy
  have hAy : ((A : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ y = v := by
    rw [hy, ← toLinEquiv_apply]
    exact LinearEquiv.apply_symm_apply _ v
  have hy' : (conjPhi A).symm v = ρ y := by
    rw [conjPhi_symm_apply, ← hy, hρ]
  have hρe₁ : (AutOm.pvec (1 : Fin 4) true : Fin (2 * 4) → K) = ρ (plusVec 4 K 1 true) := rfl
  have hρe₀ : (AutOm.pvec (0 : Fin 4) true : Fin (2 * 4) → K) = ρ (plusVec 4 K 0 true) := rfl
  rw [← LinearEquiv.apply_symm_apply (conjPhi A) v,
    conjOm8_mulVec_conjPhi A _ ((conjPhi A).symm v), LinearEquiv.apply_symm_apply]
  rw [om8Datum_x_mulVec K (by decide) true true c _]
  rw [hρe₁, hρe₀, ← map_smul, hy', eichlerC_reindex_plus, conjPhi_reindex,
    map_eichlerC_singular, hAy, ha₀, ha₁]

theorem exists_conjOm8_siegel (u w : Fin 4 ⊕ Fin 4 → K) (hli : LinearIndependent K ![u, w])
    (hu : StatedQuadPlus 4 K u = 0) (hw : StatedQuadPlus 4 K w = 0)
    (huw : StatedQuadPlus 4 K (u + w) = 0) :
    ∃ A : StatedOmega (StatedQuadPlus 4 K), ∀ g : StatedOmega (StatedQuadPlus 4 K),
      (∀ v, ((g : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v - v ∈ Submodule.span K {u, w}) →
      (∀ v, StatedQuadPlus 4 K (v + u) - StatedQuadPlus 4 K v -
          StatedQuadPlus 4 K u = 0 →
        StatedQuadPlus 4 K (v + w) - StatedQuadPlus 4 K v - StatedQuadPlus 4 K w = 0 →
        ((g : GL (Fin 4 ⊕ Fin 4) K) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v = v) →
      ∃ b : K, g = conjOm8 A ((om8Datum K).x (lv 0 1 true true) b) := by
  obtain ⟨A, hA₀, hA₁⟩ := exists_statedOmega_line u w hli hu hw huw
  refine ⟨A, fun g hN hfix => ?_⟩
  obtain ⟨b, hb⟩ := siegel_form u w hli hu hw huw g hN hfix
  refine ⟨b, ?_⟩
  have hroot := conjOm8_x_mulVec A b
  apply Subtype.ext
  apply (toLinEquiv (Fin 4 ⊕ Fin 4) K).injective
  ext v
  rw [toLinEquiv_apply, toLinEquiv_apply, hb v, hroot v, hA₀, hA₁]
  simp only [QuadraticMap.polar, coe_quadPlus]

end CFSG.RankThree.GF2n.Stroth80
