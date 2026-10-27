module

public import CFSG.LocalAnalysis.StandardType.GGExcMaxToral
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxFixedRoot

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.SeitzGeneration CFSG.StandardType.ExcMaxToral CFSG.RankThree.E6
open scoped Matrix

theorem rckExc_weyl_half_class
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (w : WeylGroup τ)
    (hge : p ^ (τ.rank - 1) ≤ Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod p) • z}) :
    (∀ u : Fin τ.rank → ℤ, w • u = -u) ∨
      ∃ β : Fin τ.rank → ℤ, IsRoot τ β ∧ ∀ u : Fin τ.rank → ℤ, w • u = -(rootReflection β • u) := by
  by_cases htop : p ^ τ.rank ≤ Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod p) • z}
  · left
    have hsign := weyl_eq_sign_of_eigenspace_top hp hp2 w (ε := -1) (Or.inr rfl)
      (by simpa using htop)
    intro u
    simpa using hsign u
  · right
    have hlt : Nat.card {z : Fin τ.rank → ZMod p //
        (modMat p (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod p) • z} < p ^ τ.rank :=
      Nat.not_le.mp htop
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have h1 : modMat p (weylMatrix (w * w)) = 1 :=
      ExcFramesHalf.modMat_weylMatrix_mul_self_eq_one hτ hp hp2 w hge
    have hww : w * w = 1 := ExcFramesHalf.eq_one_of_modMat_weylMatrix_eq_one hτ hp3 h1
    have hM : weylMatrix w * weylMatrix w = 1 := by
      rw [← weylMatrix_mul, hww, weylMatrix_one]
    obtain ⟨u, c, hu, hc, hprim, hMx⟩ :=
      ExcFramesHalf.exists_primitive_rank_one_of_involution hp hp2 (weylMatrix w) hM hge hlt
    have hiso : ∀ x y, iform (weylMatrix w *ᵥ x) (weylMatrix w *ᵥ y) = iform x y := by
      intro x y
      rw [weylMatrix_mulVec, weylMatrix_mulVec]
      exact iform_smul w x y
    have hkey := ExcFramesHalf.iform_mul_dotProduct_eq_two_mul (weylMatrix w) hiso hu hc hMx
    have hdvd : ∀ x, iform u u ∣ 2 * iform u x := fun x => ⟨c ⬝ᵥ x, (hkey x).symm⟩
    have hnorm : iform u u = 2 :=
      ExcFramesHalf.iform_self_eq_two_of_primitive_dvd hτ hu hprim hdvd
    have hroot : IsRoot τ u := ExcFramesHalf.isRoot_of_iform_self_eq_two hτ hnorm
    have hcx : ∀ x, c ⬝ᵥ x = iform u x := by
      intro x
      have h := hkey x
      rw [hnorm] at h
      omega
    have hcp : ∀ x, corootPair u x = iform u x := by
      intro x
      have h := corootPair_mul hroot x
      rw [hnorm] at h
      omega
    refine ⟨u, hroot, ?_⟩
    intro x
    rw [← weylMatrix_mulVec w x, hMx x, hcx x, rootReflection_smul hroot x, hcp x]
    abel

end CFSG.StandardType.RCKRP
