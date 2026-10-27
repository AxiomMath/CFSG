module

public import CFSG.RankThree.PartOne.SEITZU49.Circ
public import CFSG.RankThree.PartOne.SEITZU49.Eich

public section

namespace CFSG.RankThree.PartOne.SEITZU49

open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (SUid)
open CFSG.RankThree.PartOne.CTP.U5Gen (dgSU mat)
open CFSG.RankThree.PartOne.SEITZU49.Frame (shiftZ)

structure GenHyp {K : Type} [Field K] (σ : K ≃+* K) (z : K) (hz : σ z * z = 1)
    (M : Subgroup (SUid σ 5)) : Prop where
  diag : ∀ (t : Fin 5 → K) (ht : ∀ i, σ (t i) * t i = 1) (hdet : ∏ i, t i = 1),
    dgSU σ t ht hdet ∈ M
  cent : ∀ g : SUid σ 5, mat σ g * shiftZ z = shiftZ z * mat σ g → g ∈ M
  stab : ∀ x ∈ M, Eich.conjU σ (shiftZ z) (Circ.conjTr_shiftZ_mul σ z hz) x ∈ M

@[expose] def Gen49Four : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = (2 ^ 2) ^ 2 →
    ∀ (z : K) (hz : unitaryInvolution K 2 2 z * z = 1),
      (¬ ∃ u : K, unitaryInvolution K 2 2 u * u = 1 ∧ u ^ 5 = z) →
      ∀ M : Subgroup (SUid (unitaryInvolution K 2 2) 5),
        GenHyp (unitaryInvolution K 2 2) z hz M → M = ⊤

@[expose] def Gen49Big : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = (2 ^ f) ^ 2 → 6 ≤ f →
    5 ∣ 2 ^ f + 1 → ∀ (z : K) (hz : unitaryInvolution K 2 f z * z = 1),
      (¬ ∃ u : K, unitaryInvolution K 2 f u * u = 1 ∧ u ^ 5 = z) →
      ∀ M : Subgroup (SUid (unitaryInvolution K 2 f) 5),
        GenHyp (unitaryInvolution K 2 f) z hz M → M = ⊤

end CFSG.RankThree.PartOne.SEITZU49
