module

public import CFSG.RankThree.PartOne.TCX.Ree.Setup
public import CFSG.RankThree.PartOne.TCX.Ree.Closure
public import CFSG.RankThree.PartOne.KLCE.Frob

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.RF4


theorem ree_sector_context {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    {p f₀ a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (hfa : 2 * a + 1 = p * f₀) {σ : K ≃+* K}
    (hσord : orderOf σ = p) (hσ : ∀ c, σ c = c ^ 2 ^ f₀) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : CharP L 2) (_ : IsAlgClosed L)
      (_ : IsAlgClosure K L) (K₀ : Type) (_ : Field K₀) (_ : Finite K₀)
      (_ : CharP K₀ ReeTag.F4.prime) (_ : Algebra K₀ L) (_ : IsAlgClosure K₀ L) (a₀ : ℕ)
      (D₀ : ReeFrameData K₀ L a₀) (D : ReeFrameData K L a),
      Nat.card K₀ = 2 ^ (2 * a₀ + 1) ∧ 2 * a₀ + 1 = f₀ ∧
        IsReeShintani p (thetaGamma L a) D₀.F D.F
          ((ReeTag.F4.reeGammaFieldAut K a σ) ^ ((p + 1) / 2)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hpodd : Odd (p * f₀) := by rw [← hfa]; exact odd_two_mul_add_one a
  obtain ⟨-, hf₀odd⟩ := Nat.odd_mul.1 hpodd
  obtain ⟨a₀, ha₀⟩ := hf₀odd
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hK'' : Nat.card K = 2 ^ (p * f₀) := by rw [hK, hfa]
  obtain ⟨K₀, _, _, _, hK₀⟩ := exists_subfield_of_frobenius hp hf₀ hK'' hσord
  obtain ⟨_, hst, hac⟩ := exists_tower_algebra (K₀ := K₀) (K := K) (L := L)
  have : CharP K₀ ReeTag.F4.prime := ⟨fun x => by
    rw [← (algebraMap K₀ K).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff K 2 x⟩
  have hK₀' : Nat.card K₀ = 2 ^ (2 * a₀ + 1) := by rw [hK₀, ha₀]
  obtain ⟨C⟩ := exists_reeClosure (K := K) (L := L)
  obtain ⟨D, hD⟩ := C.exists_frame hK
  obtain ⟨D₀, hD₀⟩ := C.exists_frame hK₀'
  have hFF : D.F = D₀.F ^ p := by
    rw [hD, hD₀, ← pow_mul, hfa, ha₀, mul_comm]
  have hσ' : ∀ c, σ c = c ^ Nat.card K₀ := fun c => by rw [hσ, hK₀]
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, K₀,
    inferInstance, inferInstance, inferInstance, inferInstance, hac, a₀, D₀, D, hK₀', ha₀.symm,
    reeShintani D₀ D hp (by omega) hFF hσ' hσord⟩

end CFSG.RankThree.PartOne.TCX.Ree
