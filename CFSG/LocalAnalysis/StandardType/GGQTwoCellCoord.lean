module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOrthogonalAbelianization
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasThree
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2xCC1_Q_apply (G : Matrix (Fin 4) (Fin 4) (ZMod 3)) (v : Fin 4 → ZMod 3) :
    (Matrix.toQuadraticForm' G) v = v ⬝ᵥ G.mulVec v := by
  rw [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']

private theorem ggQ2xCC1_Gsymm (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1) :
    G.IsSymm := by
  rcases hG with rfl | rfl <;> decide +kernel

private theorem ggQ2xCC1_polar_eq (G : Matrix (Fin 4) (Fin 4) (ZMod 3)) (hGsym : G.IsSymm)
    (x y : Fin 4 → ZMod 3) :
    QuadraticMap.polar (Matrix.toQuadraticForm' G) x y = 2 * (x ⬝ᵥ G.mulVec y) := by
  rw [Matrix.toQuadraticForm', LinearMap.BilinMap.polar_toQuadraticMap,
    Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply',
    hGsym.dotProduct_mulVec_comm]
  ring

private theorem ggQ2xCC1_ker (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1) :
    ∀ x : Fin 4 → ZMod 3, (∀ y : Fin 4 → ZMod 3, x ⬝ᵥ G.mulVec y = 0) → x = 0 := by
  rcases hG with rfl | rfl <;> decide +kernel

private theorem ggQ2xCC1_nondeg (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1) :
    (QuadraticMap.polarBilin (Matrix.toQuadraticForm' G)).Nondegenerate := by
  have hsym := ggQ2xCC1_Gsymm G hG
  have hpol := ggQ2xCC1_polar_eq G hsym
  have hker := ggQ2xCC1_ker G hG
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  constructor
  · intro x hx
    apply hker x
    intro z
    have h := hx z
    rw [QuadraticMap.polarBilin_apply_apply, hpol x z] at h
    exact (mul_eq_zero.mp h).resolve_left h2
  · intro y hy
    apply hker y
    intro z
    have h := hy z
    rw [QuadraticMap.polarBilin_apply_apply, hpol z y, hsym.dotProduct_mulVec_comm] at h
    exact (mul_eq_zero.mp h).resolve_left h2

private theorem ggQ2xCC1_reflect_isReflLin (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1)
    (z : Fin 4 → ZMod 3) (hz : z ⬝ᵥ G.mulVec z ≠ 0) :
    IsReflLin (CFSG.ClassicalGroups.Orthogonal.reflect (Matrix.toQuadraticForm' G) z) := by
  have hsym := ggQ2xCC1_Gsymm G hG
  have hQz : (Matrix.toQuadraticForm' G) z ≠ 0 := by
    rw [ggQ2xCC1_Q_apply]; exact hz
  let φ : Module.Dual (ZMod 3) (Fin 4 → ZMod 3) :=
    (2 / (Matrix.toQuadraticForm' G) z) • (Matrix.toLinearMap₂' (ZMod 3) G z)
  have hφ : φ z = 2 := by
    simp only [φ, LinearMap.smul_apply, smul_eq_mul]
    rw [Matrix.toLinearMap₂'_apply', ← ggQ2xCC1_Q_apply]
    exact div_mul_cancel₀ 2 hQz
  refine ⟨z, φ, hφ, ?_⟩
  ext w
  rw [Module.reflection_apply, CFSG.ClassicalGroups.Orthogonal.reflect_apply hQz w,
    ggQ2xCC1_polar_eq G hsym z w]
  have hcoef : 2 * (z ⬝ᵥ G.mulVec w) / (Matrix.toQuadraticForm' G) z =
      (2 / (Matrix.toQuadraticForm' G) z) * (z ⬝ᵥ G.mulVec w) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [hcoef]
  simp only [φ, LinearMap.smul_apply, smul_eq_mul, Matrix.toLinearMap₂'_apply']

private theorem ggQ2xCC1_reflect_mem_A (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1)
    (A : Subgroup ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)))
    (hall : ∀ z : Fin 4 → ZMod 3, z ⬝ᵥ G.mulVec z ≠ 0 →
      ∃ g ∈ A, ∀ v, g v = v - (2 * (z ⬝ᵥ G.mulVec v) / (z ⬝ᵥ G.mulVec z)) • z)
    (z : Fin 4 → ZMod 3) (hz : z ⬝ᵥ G.mulVec z ≠ 0) :
    CFSG.ClassicalGroups.Orthogonal.reflect (Matrix.toQuadraticForm' G) z ∈ A := by
  obtain ⟨g, hgA, hgv⟩ := hall z hz
  have hsym := ggQ2xCC1_Gsymm G hG
  have hQz : (Matrix.toQuadraticForm' G) z ≠ 0 := by
    rw [ggQ2xCC1_Q_apply]; exact hz
  have hgeq : g = CFSG.ClassicalGroups.Orthogonal.reflect (Matrix.toQuadraticForm' G) z := by
    ext w
    rw [hgv w, CFSG.ClassicalGroups.Orthogonal.reflect_apply hQz w,
      ggQ2xCC1_polar_eq G hsym z w, ggQ2xCC1_Q_apply G z]
  rwa [hgeq] at hgA

private theorem ggQ2xCC1_reflect_mem_reflGp (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1)
    (A : Subgroup ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)))
    (hall : ∀ z : Fin 4 → ZMod 3, z ⬝ᵥ G.mulVec z ≠ 0 →
      ∃ g ∈ A, ∀ v, g v = v - (2 * (z ⬝ᵥ G.mulVec v) / (z ⬝ᵥ G.mulVec z)) • z)
    (z : Fin 4 → ZMod 3) (hz : z ⬝ᵥ G.mulVec z ≠ 0) :
    CFSG.ClassicalGroups.Orthogonal.reflect (Matrix.toQuadraticForm' G) z ∈ reflGp A :=
  Subgroup.subset_closure
    ⟨ggQ2xCC1_reflect_mem_A G hG A hall z hz,
      ggQ2xCC1_reflect_isReflLin G hG z hz⟩

private theorem ggQ2xCC_orth_le (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1)
    (A : Subgroup ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)))
    (hall : ∀ z : Fin 4 → ZMod 3, z ⬝ᵥ G.mulVec z ≠ 0 →
      ∃ g ∈ A, ∀ v, g v = v - (2 * (z ⬝ᵥ G.mulVec v) / (z ⬝ᵥ G.mulVec z)) • z)
    (g : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3))
    (hg : ∀ v, (g v) ⬝ᵥ G.mulVec (g v) = v ⬝ᵥ G.mulVec v) : g ∈ reflGp A := by
  have hQnd := ggQ2xCC1_nondeg G hG
  have hQapply := ggQ2xCC1_Q_apply G
  have hmem : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Matrix.toQuadraticForm' G) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro m
    rw [hQapply, hQapply]
    exact hg m
  have hK : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
  obtain ⟨l, _hlen, hQl, hprod⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_odd_reflection_generation
      (K := ZMod 3) (V := Fin 4 → ZMod 3) (Q := Matrix.toQuadraticForm' G) hK hQnd hmem
  rw [hprod]
  exact (reflGp A).list_prod_mem fun r hr => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    have hv' : v ⬝ᵥ G.mulVec v ≠ 0 := by
      have := hQl v hv
      rwa [hQapply] at this
    exact ggQ2xCC1_reflect_mem_reflGp G hG A hall v hv'

private theorem ggQ2xCC_trans_noniso (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1)
    (A : Subgroup ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)))
    (hall : ∀ z : Fin 4 → ZMod 3, z ⬝ᵥ G.mulVec z ≠ 0 →
      ∃ g ∈ A, ∀ v, g v = v - (2 * (z ⬝ᵥ G.mulVec v) / (z ⬝ᵥ G.mulVec z)) • z)
    {v w : Fin 4 → ZMod 3} (hvw : v ⬝ᵥ G.mulVec v = w ⬝ᵥ G.mulVec w)
    (hw : w ⬝ᵥ G.mulVec w ≠ 0) : ∃ r ∈ reflGp A, r v = w := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hQapply := ggQ2xCC1_Q_apply G
  have hvw' : (Matrix.toQuadraticForm' G) v = (Matrix.toQuadraticForm' G) w := by
    rw [hQapply, hQapply]; exact hvw
  have hw' : (Matrix.toQuadraticForm' G) w ≠ 0 := by rw [hQapply]; exact hw
  obtain ⟨g, hg, hgv⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_mem_orthogonalGroup_apply_eq
      (Q := Matrix.toQuadraticForm' G) h2 hvw' hw'
  refine ⟨g, ggQ2xCC_orth_le G hG A hall g ?_, hgv⟩
  intro m
  rw [← hQapply, ← hQapply]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg m

private theorem ggQ2xCC_trans_iso (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1)
    (A : Subgroup ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)))
    (hall : ∀ z : Fin 4 → ZMod 3, z ⬝ᵥ G.mulVec z ≠ 0 →
      ∃ g ∈ A, ∀ v, g v = v - (2 * (z ⬝ᵥ G.mulVec v) / (z ⬝ᵥ G.mulVec z)) • z)
    {v w : Fin 4 → ZMod 3} (hv : v ≠ 0) (hw : w ≠ 0) (hv0 : v ⬝ᵥ G.mulVec v = 0)
    (hw0 : w ⬝ᵥ G.mulVec w = 0) : ∃ r ∈ reflGp A, r v = w := by
  have hQnd := ggQ2xCC1_nondeg G hG
  have hQapply := ggQ2xCC1_Q_apply G
  have hv0' : (Matrix.toQuadraticForm' G) v = 0 := by rw [hQapply]; exact hv0
  have hw0' : (Matrix.toQuadraticForm' G) w = 0 := by rw [hQapply]; exact hw0
  obtain ⟨g, hg, hgv⟩ :=
    CFSG.ClassicalInvolution.exists_mem_orthogonalGroup_apply_eq_of_nondegenerate
      (Q := Matrix.toQuadraticForm' G) hQnd hv0' hw0' hv hw
  refine ⟨g, ggQ2xCC_orth_le G hG A hall g ?_, hgv⟩
  intro m
  rw [← hQapply, ← hQapply]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg m

private theorem ggQ2xCC2_F2 (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1) :
    ∀ u : Fin 4 → ZMod 3, ∃ z : Fin 4 → ZMod 3,
      z ⬝ᵥ G.mulVec z ≠ 0 ∧ (u + z) ⬝ᵥ G.mulVec (u + z) ≠ 0 := by
  rcases hG with rfl | rfl <;> decide +kernel

private theorem ggQ2xCC2_F1 (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1) :
    ∀ z z' : Fin 4 → ZMod 3,
      (z ⬝ᵥ G.mulVec z ≠ 0 ∧ z' ⬝ᵥ G.mulVec z' ≠ 0) →
        z ⬝ᵥ G.mulVec z' ≠ 0 ∨ ∃ z'' : Fin 4 → ZMod 3,
          z'' ⬝ᵥ G.mulVec z'' ≠ 0 ∧ z ⬝ᵥ G.mulVec z'' ≠ 0 ∧
            z'' ⬝ᵥ G.mulVec z' ≠ 0 := by
  rcases hG with rfl | rfl <;> decide +kernel

private theorem ggQ2xCC2_symm (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1) :
    ∀ z z' : Fin 4 → ZMod 3,
      z ⬝ᵥ G.mulVec z' = z' ⬝ᵥ G.mulVec z := by
  rcases hG with rfl | rfl <;> decide +kernel

private noncomputable def ggQ2xCC2_dual (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (z : Fin 4 → ZMod 3) (φ : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) :
    Module.Dual (ZMod 3) (Fin 4 → ZMod 3) where
  toFun v := (2 / (z ⬝ᵥ G.mulVec z)) * (z ⬝ᵥ G.mulVec (φ.symm v))
  map_add' x y := by
    simp only [map_add, Matrix.mulVec_add, dotProduct_add, mul_add]
  map_smul' a x := by
    simp only [map_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_smul,
      RingHom.id_apply]
    ring_nf

private theorem ggQ2xCC2_dual_self (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (z : Fin 4 → ZMod 3) (hz : z ⬝ᵥ G.mulVec z ≠ 0)
    (φ : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) :
    ggQ2xCC2_dual G z φ (φ z) = 2 := by
  simp only [ggQ2xCC2_dual, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.symm_apply_apply]
  exact div_mul_cancel₀ 2 hz

private theorem ggQ2xCC2_reflection_mem (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (A : Subgroup ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)))
    (hall : ∀ z : Fin 4 → ZMod 3, z ⬝ᵥ G.mulVec z ≠ 0 →
      ∃ g ∈ A, ∀ v, g v = v - (2 * (z ⬝ᵥ G.mulVec v) / (z ⬝ᵥ G.mulVec z)) • z)
    (φ : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) (hφA : φ ∈ A)
    (z : Fin 4 → ZMod 3) (hz : z ⬝ᵥ G.mulVec z ≠ 0) :
    Module.reflection (ggQ2xCC2_dual_self G z hz φ) ∈ A := by
  obtain ⟨g, hgA, hgv⟩ := hall z hz
  have htA : φ * g * φ⁻¹ ∈ A := A.mul_mem (A.mul_mem hφA hgA) (A.inv_mem hφA)
  have ht : φ * g * φ⁻¹ = Module.reflection (ggQ2xCC2_dual_self G z hz φ) := by
    refine LinearEquiv.ext (fun v => ?_)
    have hgvv := hgv (φ.symm v)
    calc
      (φ * g * φ⁻¹) v = φ (g (φ.symm v)) := by
        simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv]
      _ = φ (φ.symm v -
            (2 * (z ⬝ᵥ G.mulVec (φ.symm v)) / (z ⬝ᵥ G.mulVec z)) • z) := by rw [hgvv]
      _ = v - ((2 / (z ⬝ᵥ G.mulVec z)) * (z ⬝ᵥ G.mulVec (φ.symm v))) • (φ z) := by
        simp only [map_sub, map_smul, LinearEquiv.apply_symm_apply, div_mul_eq_mul_div]
      _ = (Module.reflection (ggQ2xCC2_dual_self G z hz φ)) v := by
        rw [Module.reflection_apply]
        simp only [ggQ2xCC2_dual, LinearMap.coe_mk, AddHom.coe_mk]
  simpa [ht] using htA

private theorem ggQ2xCC2_scalar (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1)
    (A : Subgroup ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)))
    (hS1 : ∀ (c : Fin 4 → ZMod 3) (φ : Module.Dual (ZMod 3) (Fin 4 → ZMod 3)) (h : φ c = 2),
      Module.reflection h ∈ A →
        ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ G.mulVec v))
    (hall : ∀ z : Fin 4 → ZMod 3, z ⬝ᵥ G.mulVec z ≠ 0 →
      ∃ g ∈ A, ∀ v, g v = v - (2 * (z ⬝ᵥ G.mulVec v) / (z ⬝ᵥ G.mulVec z)) • z)
    (φ : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) (hφA : φ ∈ A)
    (z : Fin 4 → ZMod 3) (hz : z ⬝ᵥ G.mulVec z ≠ 0) :
    ∃ κ : ZMod 3, κ ≠ 0 ∧ ∀ w : Fin 4 → ZMod 3,
      (φ z) ⬝ᵥ G.mulVec (φ w) = κ * (z ⬝ᵥ G.mulVec w) := by
  obtain ⟨ε, hεpm, hεeq⟩ := hS1 (φ z) (ggQ2xCC2_dual G z φ)
    (ggQ2xCC2_dual_self G z hz φ)
    (ggQ2xCC2_reflection_mem G A hall φ hφA z hz)
  refine ⟨ε * (2 / (z ⬝ᵥ G.mulVec z)), ?_, fun w => ?_⟩
  · have h2 : (2 : ZMod 3) ≠ 0 := by decide
    have hq : (2 / (z ⬝ᵥ G.mulVec z)) ≠ 0 := div_ne_zero h2 hz
    have hεne : ε ≠ 0 := by
      rcases hεpm with rfl | rfl <;> decide
    exact mul_ne_zero hεne hq
  · have hw := hεeq (φ w)
    have hmain : (2 / (z ⬝ᵥ G.mulVec z)) * (z ⬝ᵥ G.mulVec w)
        = ε * ((φ z) ⬝ᵥ G.mulVec (φ w)) := by
      simpa only [ggQ2xCC2_dual, LinearMap.coe_mk, AddHom.coe_mk,
        LinearEquiv.symm_apply_apply] using hw
    have hε2 : ε * ε = 1 := by
      rcases hεpm with rfl | rfl <;> decide
    calc
      (φ z) ⬝ᵥ G.mulVec (φ w) = (ε * ε) * ((φ z) ⬝ᵥ G.mulVec (φ w)) := by
        rw [hε2, one_mul]
      _ = ε * (ε * ((φ z) ⬝ᵥ G.mulVec (φ w))) := by ring
      _ = ε * ((2 / (z ⬝ᵥ G.mulVec z)) * (z ⬝ᵥ G.mulVec w)) := by rw [← hmain]
      _ = (ε * (2 / (z ⬝ᵥ G.mulVec z))) * (z ⬝ᵥ G.mulVec w) := by ring

private theorem ggQ2xCC2_scalar_eq (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1)
    (φ : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3))
    {z z' : Fin 4 → ZMod 3} (hB : z ⬝ᵥ G.mulVec z' ≠ 0) {κ κ' : ZMod 3}
    (hκ : ∀ w : Fin 4 → ZMod 3,
      (φ z) ⬝ᵥ G.mulVec (φ w) = κ * (z ⬝ᵥ G.mulVec w))
    (hκ' : ∀ w : Fin 4 → ZMod 3,
      (φ z') ⬝ᵥ G.mulVec (φ w) = κ' * (z' ⬝ᵥ G.mulVec w)) :
    κ = κ' := by
  have h1 := hκ z'
  have h2 := hκ' z
  rw [ggQ2xCC2_symm G hG (φ z) (φ z')] at h1
  rw [ggQ2xCC2_symm G hG z' z] at h2
  exact mul_right_cancel₀ hB (h1.symm.trans h2)

private theorem ggQ2xCC2_scalar_all (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1)
    (A : Subgroup ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)))
    (hS1 : ∀ (c : Fin 4 → ZMod 3) (φ : Module.Dual (ZMod 3) (Fin 4 → ZMod 3)) (h : φ c = 2),
      Module.reflection h ∈ A →
        ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ G.mulVec v))
    (hall : ∀ z : Fin 4 → ZMod 3, z ⬝ᵥ G.mulVec z ≠ 0 →
      ∃ g ∈ A, ∀ v, g v = v - (2 * (z ⬝ᵥ G.mulVec v) / (z ⬝ᵥ G.mulVec z)) • z)
    (φ : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) (hφA : φ ∈ A) :
    ∃ κ : ZMod 3, κ ≠ 0 ∧ ∀ z : Fin 4 → ZMod 3, z ⬝ᵥ G.mulVec z ≠ 0 →
      ∀ w : Fin 4 → ZMod 3,
        (φ z) ⬝ᵥ G.mulVec (φ w) = κ * (z ⬝ᵥ G.mulVec w) := by
  obtain ⟨z0, hz0, -⟩ := ggQ2xCC2_F2 G hG 0
  obtain ⟨κ0, hκ0ne, hκ0⟩ := ggQ2xCC2_scalar G hG A hS1 hall φ hφA z0 hz0
  refine ⟨κ0, hκ0ne, fun z hz w => ?_⟩
  obtain ⟨κz, -, hκz⟩ := ggQ2xCC2_scalar G hG A hS1 hall φ hφA z hz
  have heq : κz = κ0 := by
    rcases ggQ2xCC2_F1 G hG z z0 ⟨hz, hz0⟩ with hB | ⟨z'', hz'', hB1, hB2⟩
    · exact ggQ2xCC2_scalar_eq G hG φ hB hκz hκ0
    · obtain ⟨κ'', -, hκ''⟩ := ggQ2xCC2_scalar G hG A hS1 hall φ hφA z'' hz''
      exact (ggQ2xCC2_scalar_eq G hG φ hB1 hκz hκ'').trans
        (ggQ2xCC2_scalar_eq G hG φ hB2 hκ'' hκ0)
  rw [heq] at hκz
  exact hκz w

private theorem ggQ2xCC_sim (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1)
    (A : Subgroup ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)))
    (hS1 : ∀ (c : Fin 4 → ZMod 3) (φ : Module.Dual (ZMod 3) (Fin 4 → ZMod 3)) (h : φ c = 2),
      Module.reflection h ∈ A →
        ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ G.mulVec v))
    (hall : ∀ z : Fin 4 → ZMod 3, z ⬝ᵥ G.mulVec z ≠ 0 →
      ∃ g ∈ A, ∀ v, g v = v - (2 * (z ⬝ᵥ G.mulVec v) / (z ⬝ᵥ G.mulVec z)) • z) :
    ∀ φ ∈ A, ∃ κ : ZMod 3, κ ≠ 0 ∧ ∀ u v : Fin 4 → ZMod 3,
      (φ u) ⬝ᵥ G.mulVec (φ v) = κ * (u ⬝ᵥ G.mulVec v) := by
  intro φ hφA
  obtain ⟨κ, hκne, hκ⟩ := ggQ2xCC2_scalar_all G hG A hS1 hall φ hφA
  refine ⟨κ, hκne, fun u v => ?_⟩
  obtain ⟨z, hz, huz⟩ := ggQ2xCC2_F2 G hG u
  have h1 : (φ (u + z)) ⬝ᵥ G.mulVec (φ v) = κ * ((u + z) ⬝ᵥ G.mulVec v) :=
    hκ (u + z) huz v
  have h2 : (φ z) ⬝ᵥ G.mulVec (φ v) = κ * (z ⬝ᵥ G.mulVec v) := hκ z hz v
  have hsum : (φ u) ⬝ᵥ G.mulVec (φ v) + (φ z) ⬝ᵥ G.mulVec (φ v)
      = κ * (u ⬝ᵥ G.mulVec v) + κ * (z ⬝ᵥ G.mulVec v) := by
    have hadd : (φ (u + z)) ⬝ᵥ G.mulVec (φ v)
        = (φ u) ⬝ᵥ G.mulVec (φ v) + (φ z) ⬝ᵥ G.mulVec (φ v) := by
      rw [map_add, add_dotProduct]
    rw [← hadd, h1, add_dotProduct, mul_add]
  rw [← h2] at hsum
  exact add_right_cancel hsum

theorem ggQ2_cell_coord (G : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hG : G = !![2, 2, 0, 0; 2, 2, 1, 0; 0, 1, 1, 1; 0, 0, 1, 1] ∨ G = 1)
    (A : Subgroup ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)))
    (hS1 : ∀ (c : Fin 4 → ZMod 3) (φ : Module.Dual (ZMod 3) (Fin 4 → ZMod 3)) (h : φ c = 2),
      Module.reflection h ∈ A →
        ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ G.mulVec v))
    (hall : ∀ z : Fin 4 → ZMod 3, z ⬝ᵥ G.mulVec z ≠ 0 →
      ∃ g ∈ A, ∀ v, g v = v - (2 * (z ⬝ᵥ G.mulVec v) / (z ⬝ᵥ G.mulVec z)) • z)
    (x y : Fin 4 → ZMod 3)
    (hdat : (∃ s t : ZMod 3, s • x + t • y ≠ 0 ∧
        (s • x + t • y) ⬝ᵥ G.mulVec (s • x + t • y) = 0) ∨
      ((∀ s t : ZMod 3, s • x + t • y ≠ 0 →
        (s • x + t • y) ⬝ᵥ G.mulVec (s • x + t • y) ≠ 0) ∧
      ∃ s₁ t₁ s₂ t₂ : ZMod 3, (s₁ • x + t₁ • y) ⬝ᵥ G.mulVec (s₁ • x + t₁ • y) = 1 ∧
        (s₂ • x + t₂ • y) ⬝ᵥ G.mulVec (s₂ • x + t₂ • y) = 2)) :
    (∃ u ∈ Submodule.span (ZMod 3) {x, y}, u ≠ 0 ∧ ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ u} = Submodule.span (ZMod 3) {r u}) ∨
    (∀ φ ∈ A, ∀ w ∈ Submodule.span (ZMod 3) {x, y}, w ≠ 0 → ∃ r ∈ reflGp A,
      ∃ w' ∈ Submodule.span (ZMod 3) {x, y}, w' ≠ 0 ∧
        Submodule.span (ZMod 3) {φ w} = Submodule.span (ZMod 3) {r w'}) := by
  classical
  have hsim := ggQ2xCC_sim G hG A hS1 hall
  have hmem : ∀ a b : ZMod 3, a • x + b • y ∈ Submodule.span (ZMod 3) {x, y} := fun a b =>
    Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hspan : ∀ w ∈ Submodule.span (ZMod 3) {x, y}, ∃ a b : ZMod 3, w = a • x + b • y :=
    fun w hw => by
      obtain ⟨a, b, h⟩ := Submodule.mem_span_pair.mp hw
      exact ⟨a, b, h.symm⟩
  rcases hdat with ⟨s, t, hne, hiso⟩ | ⟨hnon, s₁, t₁, s₂, t₂, h1, h2⟩
  · left
    refine ⟨s • x + t • y, hmem s t, hne, fun φ hφ => ?_⟩
    obtain ⟨κ, hκ, hκφ⟩ := hsim φ hφ
    have hφiso : (φ (s • x + t • y)) ⬝ᵥ G.mulVec (φ (s • x + t • y)) = 0 := by
      rw [hκφ, hiso, mul_zero]
    have hφne : φ (s • x + t • y) ≠ 0 := fun h => hne ((map_eq_zero_iff φ φ.injective).mp h)
    obtain ⟨r, hr, hru⟩ := ggQ2xCC_trans_iso G hG A hall hne hφne hiso hφiso
    exact ⟨r, hr, by rw [hru]⟩
  · right
    intro φ hφ w hw hw0
    obtain ⟨κ, hκ, hκφ⟩ := hsim φ hφ
    obtain ⟨a, b, rfl⟩ := hspan w hw
    have hQw : (a • x + b • y) ⬝ᵥ G.mulVec (a • x + b • y) ≠ 0 := hnon a b hw0
    have hQφ : (φ (a • x + b • y)) ⬝ᵥ G.mulVec (φ (a • x + b • y)) ≠ 0 := by
      rw [hκφ]
      exact mul_ne_zero hκ hQw
    have h12 : ∀ q : ZMod 3, q ≠ 0 → q = 1 ∨ q = 2 := by decide
    rcases h12 _ hQφ with h | h
    · have hw'0 : s₁ • x + t₁ • y ≠ 0 := by
        intro h0
        rw [h0, zero_dotProduct] at h1
        exact absurd h1 (by decide)
      obtain ⟨r, hr, hru⟩ := ggQ2xCC_trans_noniso G hG A hall (v := s₁ • x + t₁ • y)
        (w := φ (a • x + b • y)) (by rw [h1, h]) hQφ
      exact ⟨r, hr, s₁ • x + t₁ • y, hmem s₁ t₁, hw'0, by rw [hru]⟩
    · have hw'0 : s₂ • x + t₂ • y ≠ 0 := by
        intro h0
        rw [h0, zero_dotProduct] at h2
        exact absurd h2 (by decide)
      obtain ⟨r, hr, hru⟩ := ggQ2xCC_trans_noniso G hG A hall (v := s₂ • x + t₂ • y)
        (w := φ (a • x + b • y)) (by rw [h2, h]) hQφ
      exact ⟨r, hr, s₂ • x + t₂ • y, hmem s₂ t₂, hw'0, by rw [hru]⟩

end CFSG.StandardType

end
