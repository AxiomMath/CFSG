module

public import CFSG.LocalAnalysis.ZStar.PadicBlockProperties

public section

namespace CFSG

namespace ZStar.PadicBlockAugmentation

open ZStar.Helpers
open ZStar.PadicBlockLift
open ZStar.PadicBlockProperties

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

noncomputable def augmentationPadic : MonoidAlgebra ℤ_[2] G →ₐ[ℤ_[2]] ℤ_[2] :=
  (MonoidAlgebra.lift ℤ_[2] ℤ_[2] G) (1 : G →* ℤ_[2])

theorem augmentationPadic_apply (x : MonoidAlgebra ℤ_[2] G) :
    augmentationPadic x = ∑ g : G, x.coeff g := by
  classical
  rw [augmentationPadic, MonoidAlgebra.lift_apply]
  calc
    x.coeff.sum (fun a b ↦ b • (1 : G →* ℤ_[2]) a) =
        ∑ a : G, x.coeff a • (1 : G →* ℤ_[2]) a := by
      apply Finsupp.sum_fintype
      intro i
      simp
    _ = ∑ a : G, x.coeff a := by simp

private theorem toZModPow_one_augmentationPadic (x : MonoidAlgebra ℤ_[2] G) :
    PadicInt.toZModPow 1 (augmentationPadic x) =
      augmentationHom G (reducePadic 1 x) := by
  classical
  rw [augmentationPadic_apply, map_sum, augmentationHom_apply, augmentationTwo]
  apply Finset.sum_congr rfl
  intro g hg
  exact reducePadic_coeff 1 x g

theorem principalBlockPadic_augmentation :
    augmentationPadic (principalBlockPadic (G := G)) = 1 := by
  let a := augmentationPadic (principalBlockPadic (G := G))
  have haidem : a * a = a := by
    dsimp [a]
    rw [← map_mul, principalBlockPadic_idempotent]
  have hared : PadicInt.toZModPow 1 a = 1 := by
    dsimp [a]
    rw [toZModPow_one_augmentationPadic, reducePadic_one_principalBlockPadic]
    rw [augmentationHom_apply]
    exact principalBlockCandidate_augmentation G
  have hafactor : a * (a - 1) = 0 := by
    rw [mul_sub, mul_one, haidem, sub_self]
  rcases mul_eq_zero.mp hafactor with ha0 | ha1
  · exfalso
    rw [ha0, map_zero] at hared
    have h01 : (0 : ZMod 2) ≠ 1 := zero_ne_one
    exact h01 (by simpa using hared)
  · exact sub_eq_zero.mp ha1

end

end ZStar.PadicBlockAugmentation

end CFSG
