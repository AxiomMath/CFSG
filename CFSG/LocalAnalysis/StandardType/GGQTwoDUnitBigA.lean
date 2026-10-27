module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
public import CFSG.LinearAlgebra.SteinbergBQKernelBlocks
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigAD
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigAA
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigAB
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigAF

public section

namespace CFSG.StandardType.QTwo

open CFSG.LinearAlgebra.SteinbergBQ

theorem qtwoDB41_torus_weights {m : ℕ} (hm : 6 ≤ m) {c : Fin m}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (τ : Multiplicative (DVec m) →* (V ≃ₗ[ZMod 2] V))
    (hτO : τ.range ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hτker : ∀ v : DVec m, τ (Multiplicative.ofAdd v) = 1 ↔ ∀ i, i ≠ c → v i = 0)
    (hW : ∀ w ∈ dEvenStab m (Pi.single c 1), ∃ n ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      ∀ v : DVec m, n * τ (Multiplicative.ofAdd v) * n⁻¹ = τ (Multiplicative.ofAdd (w v)))
    (hdim : Module.finrank (ZMod 2) V = 2 * (m - 1) ∨
      (Module.finrank (ZMod 2) V = 2 * m ∧
        ¬ (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even m))) :
    Module.finrank (ZMod 2) (fixedSub τ.range) + 2 * (m - 1) = Module.finrank (ZMod 2) V ∧
      (∀ x ∈ fixedSub τ.range,
        (∀ y ∈ fixedSub τ.range, QuadraticMap.polar Q x y = 0) → x = 0) ∧
      (∀ v : DVec m, (∀ i, i ≠ c → v i ≠ 0) →
        ∀ x : V, τ (Multiplicative.ofAdd v) x = x → x ∈ fixedSub τ.range) ∧
      (CFSG.GroupTheory.WeirSylow.IsPlusType
          (Q.restrict (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
            (fixedSub τ.range))) ↔
        Even (m - 1)) := by
  obtain ⟨U, hdim_eq, hplane, hfix⟩ := qtwoDB41_blocks hm hQ τ hτO hτker hW hdim
  have hodd := qtwoDB41_odd_card_range τ
  have hnd : ∀ x ∈ fixedSub τ.range,
      (∀ y ∈ fixedSub τ.range, QuadraticMap.polar Q x y = 0) → x = 0 :=
    qtwoDB41_fixedSub_nondegenerate hQ hτO hodd
  set V₀ : Submodule (ZMod 2) V := fixedSub τ.range with hV₀
  set W : Submodule (ZMod 2) V :=
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) V₀ with hWdef
  have hWdef' : W = LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
      (fixedSub τ.range) := by rw [hWdef, hV₀]
  have hdisj : Disjoint V₀ W := by
    rw [Submodule.disjoint_def]
    intro x hx hxW
    exact hnd x (hV₀ ▸ hx) fun y hy => by
      have h0 : (QuadraticMap.polarBilin Q) y x = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp (hWdef ▸ hxW)) y (hV₀ ▸ hy)
      calc QuadraticMap.polar Q x y = QuadraticMap.polar Q y x := QuadraticMap.polar_comm Q x y
        _ = (QuadraticMap.polarBilin Q) y x :=
              (QuadraticMap.polarBilin_apply_apply Q y x).symm
        _ = 0 := h0
  have hcompl : IsCompl V₀ W := by
    rw [hWdef]
    exact (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
      (qtwoDB41_polarBilin_isAlt Q).isRefl).2 (by
      rwa [hWdef] at hdisj)
  have hfin : Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) V₀ + Module.finrank (ZMod 2) W :=
    (Submodule.finrank_add_eq_of_isCompl hcompl).symm
  have hWdim : Module.finrank (ZMod 2) W = 2 * (m - 1) := by
    have hV₀fr : Module.finrank (ZMod 2) V₀ =
        Module.finrank (ZMod 2) (fixedSub τ.range) := by rw [hV₀]
    omega
  have hWfr : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2)
      ↥(LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (fixedSub τ.range)) := by
    rw [hWdef']
  have hWdim' : Module.finrank (ZMod 2)
      ↥(LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (fixedSub τ.range)) =
      2 * (m - 1) := by
    rw [← hWfr]
    exact hWdim
  exact ⟨hdim_eq, hnd, hfix, qtwoDB41_isPlaneSystem_iff hplane hWdim'⟩

end CFSG.StandardType.QTwo

end
