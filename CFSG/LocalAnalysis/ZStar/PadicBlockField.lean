module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import CFSG.LocalAnalysis.ZStar.PadicBlockAugmentation

public section

namespace CFSG

namespace ZStar.PadicBlockField

open ZStar.PadicBlockLift
open ZStar.PadicBlockProperties
open ZStar.PadicBlockAugmentation

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

abbrev TwoAdicComplex := ℂ_[2]

@[expose] noncomputable def padicIntToComplex : ℤ_[2] →+* TwoAdicComplex :=
  (algebraMap ℚ_[2] TwoAdicComplex).comp (algebraMap ℤ_[2] ℚ_[2])

@[expose] noncomputable def principalBlockTwoAdic : MonoidAlgebra TwoAdicComplex G :=
  MonoidAlgebra.mapRingHom G padicIntToComplex
    (principalBlockPadic (G := G))

theorem principalBlockTwoAdic_idempotent :
    principalBlockTwoAdic (G := G) * principalBlockTwoAdic (G := G) =
      principalBlockTwoAdic (G := G) := by
  rw [principalBlockTwoAdic, ← map_mul, principalBlockPadic_idempotent]

theorem principalBlockTwoAdic_central :
    principalBlockTwoAdic (G := G) ∈
      Submonoid.center (MonoidAlgebra TwoAdicComplex G) := by
  rw [Submonoid.mem_center_iff]
  intro z
  induction z using MonoidAlgebra.induction_on with
  | of g =>
      have hc := (Submonoid.mem_center_iff.mp
        (principalBlockPadic_central (G := G)))
        (MonoidAlgebra.single g 1)
      have hm := congrArg (MonoidAlgebra.mapRingHom G padicIntToComplex) hc
      simpa [principalBlockTwoAdic] using hm
  | add x y hx hy => simp only [add_mul, mul_add, hx, hy]
  | smul r x hx =>
      simpa only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm] using
        congrArg (r • ·) hx

@[expose] noncomputable def augmentationTwoAdic :
    MonoidAlgebra TwoAdicComplex G →ₐ[TwoAdicComplex] TwoAdicComplex :=
  (MonoidAlgebra.lift TwoAdicComplex TwoAdicComplex G)
    (1 : G →* TwoAdicComplex)

theorem augmentationTwoAdic_apply (x : MonoidAlgebra TwoAdicComplex G) :
    augmentationTwoAdic x = ∑ g : G, x.coeff g := by
  classical
  rw [augmentationTwoAdic, MonoidAlgebra.lift_apply]
  calc
    x.coeff.sum (fun a b ↦ b • (1 : G →* TwoAdicComplex) a) =
        ∑ a : G, x.coeff a • (1 : G →* TwoAdicComplex) a := by
      apply Finsupp.sum_fintype
      intro i
      simp
    _ = ∑ a : G, x.coeff a := by simp

theorem principalBlockTwoAdic_augmentation :
    augmentationTwoAdic (principalBlockTwoAdic (G := G)) = 1 := by
  classical
  rw [augmentationTwoAdic_apply, principalBlockTwoAdic]
  calc
    ∑ g : G,
        (MonoidAlgebra.mapRingHom G padicIntToComplex
          (principalBlockPadic (G := G))).coeff g =
        ∑ g : G, padicIntToComplex ((principalBlockPadic (G := G)).coeff g) := by
      apply Finset.sum_congr rfl
      intro g hg
      exact MonoidAlgebra.coeff_mapRingHom _ _ _
    _ = padicIntToComplex
        (∑ g : G, (principalBlockPadic (G := G)).coeff g) := by
      rw [map_sum]
    _ = padicIntToComplex
        (augmentationPadic (principalBlockPadic (G := G))) := by
      rw [augmentationPadic_apply]
    _ = 1 := by rw [principalBlockPadic_augmentation, map_one]

end

end ZStar.PadicBlockField

end CFSG
