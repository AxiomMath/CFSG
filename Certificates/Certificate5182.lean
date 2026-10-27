module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2ThreeMaxMain
import Certificates.Kernel.G2Three.PrimFinal

public section

namespace Certificates

open Certificates.G2ThreeMax

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert G2ThreeMax in
theorem certificate5182 : (∀ {G : Type} [Group G] (ρ : G →* Matrix.GeneralLinearGroup (Fin 14) (ZMod 3))
      (ψ : G →* G) (gens : ℕ → G), Subgroup.closure (gens '' {k | k < 8}) = ⊤ →
      (∀ k < 8, ((ρ (gens k) : Matrix.GeneralLinearGroup (Fin 14) (ZMod 3)) : Mat3) =
        M (genArr k)) →
      (∀ k < 8, gens (Certificates.G2ThreeMax.invK k) = (gens k)⁻¹) → ∀ inp ∈ [innerInput, outerInput],
      (∀ k < 8, ψ (gens k) = gens inp.sigma[k]!) →
      IsCoatom (MulAction.stabilizer G (⟨M (wordArr inp.base)⟩ : TwPt ρ ψ))) ∧
    M (wordArr innerInput.base) * M (wordArr innerInput.base) = 1 := by
  refine ⟨fun ρ ψ gens hgen hρ hinv inp hinp hψ => ?_, CFSG.KD.G2Three.inner_invol⟩
  rw [List.mem_cons, List.mem_singleton] at hinp
  rcases hinp with rfl | rfl
  · exact CFSG.KD.G2Three.coatom_inner hgen hρ hinv hψ
  · exact CFSG.KD.G2Three.coatom_outer hgen hρ hinv hψ

end Certificates
