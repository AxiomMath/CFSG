module

public import CFSG.RankThree.PartOne.TCX.Tri.Skeleton
public import CFSG.RankThree.PartOne.TCX.Tri.Setup

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Shintani

variable {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L] [CharP L 2]
  [IsAlgClosure K L]

omit [Finite K] in
theorem triShintani {p f₀ : ℕ} (hp3 : p % 3 = 1 ∨ p % 3 = 2) (hf : 1 ≤ p * f₀)
    (hK : Nat.card K = (2 ^ (p * f₀)) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ (p * f₀))
    {α₀ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hα : ∀ y, triF0 L f₀ (triIota L p σ y) = triIota L p σ (α₀ y)) :
    IsShintani p (triIota L p σ) (triF0 L f₀) (triPhi L p f₀) α₀ where
  inj := triIota_injective p σ
  mem := triIota_mem_adjoint p σ
  iter := fun u => triPhi_eq_iterate p f₀ u
  actor := fun y => (hα y).symm
  fix := fun y => triPhi_triIota hp3 σ hσ y
  range := fun _ hu hΦ => triIota_range hp3 hf hK σ hσ hu hΦ

end Shintani

end CFSG.RankThree.PartOne.TCX.Tri
