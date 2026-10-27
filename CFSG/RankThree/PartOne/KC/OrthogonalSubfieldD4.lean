module

public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOneD4
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed

public section

open Matrix QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.Classical2 CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank

namespace CFSG.RankThree.PartOne.KCOrthogonalSubfield

section Std

open CFSG.RankThree.OddD4Centralizer (quadPlus_single_add_single polar_single_add_single)

variable (F : Type) [Field F]

@[expose] noncomputable def stdU : Fin (2 * 4) → F :=
  reindexVectorEquiv (plusIndexEquiv 4) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1)

@[expose] noncomputable def stdV : Fin (2 * 4) → F :=
  reindexVectorEquiv (plusIndexEquiv 4) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)

theorem coordinateQuadPlus_stdU : coordinateQuadPlus 4 F (stdU F) = 1 := by
  have hr : ∀ y, coordinateQuadPlus 4 F (reindexVectorEquiv (plusIndexEquiv 4) y) =
      quadPlus 4 F y := reindexQuadraticForm_map (plusIndexEquiv 4) (quadPlus 4 F)
  rw [stdU, hr]
  exact quadPlus_single_add_single 0

theorem coordinateQuadPlus_stdV : coordinateQuadPlus 4 F (stdV F) = 1 := by
  have hr : ∀ y, coordinateQuadPlus 4 F (reindexVectorEquiv (plusIndexEquiv 4) y) =
      quadPlus 4 F y := reindexQuadraticForm_map (plusIndexEquiv 4) (quadPlus 4 F)
  rw [stdV, hr]
  exact quadPlus_single_add_single 1

theorem polar_stdU_stdV : polar (coordinateQuadPlus 4 F) (stdU F) (stdV F) = 0 := by
  have hr : ∀ y, coordinateQuadPlus 4 F (reindexVectorEquiv (plusIndexEquiv 4) y) =
      quadPlus 4 F y := reindexQuadraticForm_map (plusIndexEquiv 4) (quadPlus 4 F)
  rw [stdU, stdV, CFSG.RankThree.EvenD4Centralizer.polar_map_isometry
    (reindexVectorEquiv (K := F) (plusIndexEquiv 4)) hr, polar_single_add_single]
  simp

theorem stdU_stdV_independent (s t : F) (h : s • stdU F + t • stdV F = 0) : s = 0 ∧ t = 0 := by
  have h1 := congrFun h (plusIndexEquiv 4 (Sum.inl 0))
  have h2 := congrFun h (plusIndexEquiv 4 (Sum.inl 1))
  simp [stdU, stdV, reindexVectorEquiv_apply] at h1 h2
  exact ⟨h1, h2⟩

variable {K : Type} [Field K] (k : Subfield K)

theorem vecIncl_stdU : vecIncl k (stdU k) = stdU K := by
  funext i
  simp [vecIncl, stdU, reindexVectorEquiv_apply, Pi.single_apply]
  split_ifs <;> simp

theorem vecIncl_stdV : vecIncl k (stdV k) = stdV K := by
  funext i
  simp [vecIncl, stdV, reindexVectorEquiv_apply, Pi.single_apply]
  split_ifs <;> simp

end Std


section Compat

variable {K : Type} [Field K] (k : Subfield K) {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem polar_vecIncl (hext : IsExtension k Q₀ Q) (v w : Fin d → k) :
    polar Q (vecIncl k v) (vecIncl k w) = ((polar Q₀ v w : k) : K) := by
  unfold QuadraticMap.polar
  rw [← vecIncl_add, hext, hext, hext]
  push_cast
  rfl

theorem reflect_vecIncl (hext : IsExtension k Q₀ Q) {u : Fin d → k} (hu : Q₀ u ≠ 0)
    (w : Fin d → k) :
    reflect Q (vecIncl k u) (vecIncl k w) = vecIncl k (reflect Q₀ u w) := by
  have hQu : Q (vecIncl k u) ≠ 0 := by
    rw [hext]
    intro h
    exact hu (Subtype.ext (by simpa using h))
  rw [reflect_apply hQu, reflect_apply hu]
  funext i
  simp only [vecIncl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [polar_vecIncl k hext, hext]
  push_cast
  rfl

theorem linearEquiv_ext_vecIncl {f g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (h : ∀ w : Fin d → k, f (vecIncl k w) = g (vecIncl k w)) : f = g := by
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin d)).ext
  intro i
  have := h (Pi.single i 1)
  rw [vecIncl_single] at this
  simpa using this

end Compat


section D4

open CFSG.RankThree.PartOne.KCOrthogonalD4 (reflect_mul_reflect_mem_orthDerived)
open CFSG.RankThree.Classical (orthDerived_eq_and_le_closure)

theorem reflect_std_mem_orthDerived {F : Type} [Field F] [Finite F]
    (hnd : (polarBilin (coordinateQuadPlus 4 F)).Nondegenerate)
    (hT : ∃ U : Submodule F (Fin (2 * 4) → F), Module.finrank F U = 3 ∧
      ∀ u ∈ U, coordinateQuadPlus 4 F u = 0) :
    reflect (coordinateQuadPlus 4 F) (stdU F) * reflect (coordinateQuadPlus 4 F) (stdV F) ∈
      orthDerived (coordinateQuadPlus 4 F) := by
  have hu := coordinateQuadPlus_stdU F
  have hv := coordinateQuadPlus_stdV F
  have huv := polar_stdU_stdV F
  by_cases h2 : (2 : F) = 0
  · have hsing : coordinateQuadPlus 4 F (stdU F + stdV F) = 0 := by
      rw [QuadraticMap.map_add (coordinateQuadPlus 4 F), hu, hv, huv]
      linear_combination h2
    have hua : polar (coordinateQuadPlus 4 F) (stdU F + stdV F) (stdU F) = 0 := by
      rw [polar_add_left, polar_self, hu, polar_comm, huv]
      simp [h2]
    have h1 := eichler_eq_reflect_mul_reflect h2 hsing hua hu
    have h3 : stdU F + (stdU F + stdV F) = stdV F := by
      rw [← add_assoc, ← two_smul F, h2, zero_smul, zero_add]
    rw [h3] at h1
    rw [← h1, (orthDerived_eq_and_le_closure hnd hT).1]
    exact eichler_mem_elementaryGroup _ _ _
  · exact reflect_mul_reflect_mem_orthDerived h2 _ hu hv huv

variable {K : Type} [Field K] [Finite K] (k : Subfield K)

theorem mem_matrixProjectiveImage_plus_four {ℓ f : ℕ} (hK : Nat.card K = ℓ ^ f)
    (h : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus 4 K)) .POmegaPlus 4 ℓ f)
    (e : matrixProjectiveDerived (coordinateQuadPlus 4 K) ≃*
      StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (hext : IsExtension k (coordinateQuadPlus 4 k) (coordinateQuadPlus 4 K))
    (hnd₀ : (polarBilin (coordinateQuadPlus 4 k)).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin (2 * 4) → k), Module.finrank k U = 3 ∧
      ∀ u ∈ U, coordinateQuadPlus 4 k u = 0)
    (β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    (hβ : ∀ t ∈ subfieldDerivedImage k hext, β t = t) :
    β ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
  classical
  have hg₀ := reflect_std_mem_orthDerived hnd₀ hT₀
  obtain ⟨ĝ₀, hĝ₀⟩ := KCOrthogonalAut.exists_matrixDerived (coordinateQuadPlus 4 k) ⟨_, hg₀⟩
  have hu₀ : coordinateQuadPlus 4 k (stdU k) ≠ 0 := by
    rw [coordinateQuadPlus_stdU]
    exact one_ne_zero
  have hv₀ : coordinateQuadPlus 4 k (stdV k) ≠ 0 := by
    rw [coordinateQuadPlus_stdV]
    exact one_ne_zero
  have hgl : matrixLinearEquiv (inclHom k hext ĝ₀).val =
      reflect (coordinateQuadPlus 4 K) (stdU K) * reflect (coordinateQuadPlus 4 K) (stdV K) := by
    apply linearEquiv_ext_vecIncl k
    intro w
    rw [inclHom_val, matrixLinearEquiv_apply, mulVec_vecIncl, LinearEquiv.mul_apply,
      ← vecIncl_stdU k, ← vecIncl_stdV k, reflect_vecIncl k hext hv₀ w,
      reflect_vecIncl k hext hu₀]
    congr 1
    have := congrArg (fun F => F w) hĝ₀
    simpa [KCOrthogonalAut.matrixLinearIso_apply, LinearEquiv.mul_apply] using this.symm
  have hfix : β (matrixProjectiveProjection (coordinateQuadPlus 4 K) (inclHom k hext ĝ₀)) =
      matrixProjectiveProjection (coordinateQuadPlus 4 K) (inclHom k hext ĝ₀) :=
    hβ _ ⟨matrixProjectiveProjection (coordinateQuadPlus 4 k) ĝ₀, rfl⟩
  exact d4_mem_matrixProjectiveImage _ h K hK e β (coordinateQuadPlus_stdU K)
    (coordinateQuadPlus_stdV K) (polar_stdU_stdV K) (stdU_stdV_independent K) _ hgl hfix

end D4

end CFSG.RankThree.PartOne.KCOrthogonalSubfield
