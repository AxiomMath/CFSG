module

public import CFSG.LocalAnalysis.ZStar.PadicBlockLift
public import CFSG.LocalAnalysis.ZStar.GroupAlgebraTwistedTrace

public section

namespace CFSG

namespace ZStar.PadicBlockProperties

open ZStar.PadicBlockLift
open ZStar.GroupAlgebraTwistedTrace

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

theorem principalBlockPadic_idempotent :
    principalBlockPadic (G := G) * principalBlockPadic (G := G) =
      principalBlockPadic (G := G) := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  have hred :
      reducePadic n
          (principalBlockPadic (G := G) * principalBlockPadic (G := G)) =
        reducePadic n (principalBlockPadic (G := G)) := by
    rw [map_mul, reducePadic_principalBlockPadic,
      principalBlockMod_idempotent]
  exact congrArg (fun x : ModularGroupAlgebra (G := G) n => x.coeff g) hred

theorem principalBlockPadic_central :
    principalBlockPadic (G := G) ∈
      Submonoid.center (MonoidAlgebra ℤ_[2] G) := by
  rw [Submonoid.mem_center_iff]
  intro z
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  have hcomm :=
    (Submonoid.mem_center_iff.mp (principalBlockMod_central (G := G) n))
      (reducePadic n z)
  have hred :
      reducePadic n (z * principalBlockPadic (G := G)) =
        reducePadic n (principalBlockPadic (G := G) * z) := by
    simpa only [map_mul, reducePadic_principalBlockPadic] using hcomm
  exact congrArg (fun x : ModularGroupAlgebra (G := G) n => x.coeff g) hred

theorem reducePadic_one_principalBlockPadic :
    reducePadic 1 (principalBlockPadic (G := G)) =
      ZStar.Helpers.principalBlockCandidate G := by
  rw [reducePadic_principalBlockPadic]
  rfl

@[simp]
theorem toZModPow_one_principalBlockPadic_coeff (g : G) :
    PadicInt.toZModPow 1 ((principalBlockPadic (G := G)).coeff g) =
      (ZStar.Helpers.principalBlockCandidate G).coeff g := by
  have h := congrArg
    (fun x : ModularGroupAlgebra (G := G) 1 => x.coeff g)
    (reducePadic_one_principalBlockPadic (G := G))
  simpa only [reducePadic_coeff] using h

theorem sum_principalBlockPadic_coeff_twoSidedTwist_eq_zero
    [DecidableEq G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hnconj : ¬IsConj a b) :
    (∑ g : G,
      (principalBlockPadic (G := G)).coeff (g⁻¹ * a * g * b⁻¹)) = 0 := by
  exact sum_coeff_twoSidedTwist_eq_zero a b ha hb hnconj
    (principalBlockPadic (G := G))
    (principalBlockPadic_idempotent (G := G))
    (principalBlockPadic_central (G := G))

theorem sum_principalBlockCandidate_coeff_twoSidedTwist_eq_zero
    [DecidableEq G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hnconj : ¬IsConj a b) :
    (∑ g : G,
      (ZStar.Helpers.principalBlockCandidate G).coeff
        (g⁻¹ * a * g * b⁻¹)) = 0 := by
  have h := congrArg (PadicInt.toZModPow 1)
    (sum_principalBlockPadic_coeff_twoSidedTwist_eq_zero
      (G := G) a b ha hb hnconj)
  simpa only [map_sum, map_zero,
    toZModPow_one_principalBlockPadic_coeff] using h

end

end ZStar.PadicBlockProperties

end CFSG
