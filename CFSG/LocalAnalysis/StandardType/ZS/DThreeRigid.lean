module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.Fischer.Classification.Orthogonal3.Forms
public import CFSG.Fischer.Classification.Orthogonal3.Model
import CFSG.Fischer.Classification.PartIII.Beta.Forms
import CFSG.Fischer.Classification.PartIII.Beta.Transport
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTransport
import CFSG.LocalAnalysis.StandardType.ZS.DThreeRigidForm
import CFSG.LocalAnalysis.StandardType.ZS.DThreeRigidCount
import CFSG.LocalAnalysis.StandardType.ZS.DThreeRigidOne
import CFSG.LocalAnalysis.StandardType.ZS.DThreeRigidFive
import CFSG.LocalAnalysis.StandardType.ZS.DThreeRigidSix

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

variable {U : Type} [AddCommGroup U] [Module (ZMod 3) U] [Module.Finite (ZMod 3) U]
  {A : Subgroup (U ≃ₗ[ZMod 3] U)}

theorem exists_linearEquiv_of_mulEquiv_R3 (hn : 4 ≤ Module.finrank (ZMod 3) U)
    (hgen : ReflGen 3 A) (hirr : AbsIrred 3 A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl 3 x → IsRefl 3 y → orderOf (x * y) ≤ 3)
    {m : ℕ} (hm : 5 ≤ m) {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 f) (hφ : ∀ g, g ∈ reflImage 3 A ↔ φ g ∈ D3 f) :
    ∃ L : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U, ∀ t : U ≃ₗ[ZMod 3] U,
      (t ∈ A ∧ IsRefl 3 t) ↔ ∃ u, f u u = 1 ∧ ∀ x, t (L x) = L (x + f x u • u) := by
  have hn3 : 3 ≤ Module.finrank (ZMod 3) U := by omega
  obtain ⟨B, hBs, hBnd, hB⟩ := exists_bilinForm_of_orderOf_mul_le_three (by omega) hgen hirr h3
  obtain ⟨δ, e, hδ12, he⟩ := exists_linearEquiv_diagF3 (m := m) (by omega) hf
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_R3_of_isometry (f := f) (f' := diagF3 m δ) e he
  have hφ' : ∀ g, g ∈ reflImage 3 A ↔ (φ.trans ψ) g ∈ D3 (diagF3 m δ) := fun g => by
    rw [hφ g, MulEquiv.trans_apply, mem_iff_of_image_eq ψ hψ]
  obtain ⟨L', hL'⟩ : ∃ L' : (Fin m → ZMod 3) ≃ₗ[ZMod 3] U,
      ∀ x y, B (L' x) (L' y) = diagF3 m δ x y := by
    rcases hδ12 with rfl | rfl
    · exact exists_isometry_of_mulEquiv_R3_diagF3_one hn3 hirr (by omega) _ hφ' hB
    · rcases eq_or_lt_of_le hm with rfl | hm6
      · exact exists_isometry_of_mulEquiv_R3_diagF3_five_two hn3 hirr _ hφ' hBs hBnd hB
      · exact exists_isometry_of_mulEquiv_R3_diagF3_two hn3 hirr (by omega) _ hφ' hBs hBnd hB
  refine ⟨e.trans L', isRefl_iff_of_isometry hn3 hirr (by omega) hf φ hφ hB (e.trans L') ?_⟩
  intro x y
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hL', ← he]

end CFSG.StandardType.ZS
