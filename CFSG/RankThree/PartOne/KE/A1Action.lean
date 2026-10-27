module

public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusCentralizers
public import CFSG.RankThree.PartOne.KE.A1SL2

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.Classical (conjSL conjSL_one)
open scoped MatrixGroups

theorem frobenius_fixed_iff {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (c : L) :
    Fr c = c ↔ c ∈ Set.range (algebraMap K L) := by
  have : Fintype K := Fintype.ofFinite K
  constructor
  · intro h
    exact mem_range_algebraMap_of_pow_card_eq (by rw [← hFr]; exact h)
  · rintro ⟨k, rfl⟩
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem a1_hS1_of_action {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) {n : ModGL τ L}
    {Φ : ModGL τ L →* ModGL τ L} {θ : Fin τ.rank → ℤ} (P : GL (Fin 2) L)
    (hX : ∀ B : SL2 L, n * Φ (rootSL2 τ L θ B) * n⁻¹ =
      rootSL2 τ L θ (conjSL (P * GeneralLinearGroup.map Fr P⁻¹)
        (SpecialLinearGroup.map Fr B))) (B : SL2 L) :
    n * Φ (rootSL2 τ L θ B) * n⁻¹ = rootSL2 τ L θ B ↔
      B ∈ (SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P) := by
  rw [hX B, (rootSL2_injective_of_field θ).eq_iff]
  exact sl2_twistedFixed_iff Fr (frobenius_fixed_iff Fr hFr) P B

theorem a1_typeI_hX {τ : Tag} {L : Type} [Field L] (Fr : L →+* L) {n : ModGL τ L}
    {θ : Fin τ.rank → ℤ}
    (hn : n ∈ Subgroup.centralizer (rootRankOneGroup τ L θ : Set (ModGL τ L))) (B : SL2 L) :
    n * Units.map (entrywiseHom Fr) (rootSL2 τ L θ B) * n⁻¹ =
      rootSL2 τ L θ (conjSL (1 * GeneralLinearGroup.map Fr (1 : GL (Fin 2) L)⁻¹)
        (SpecialLinearGroup.map Fr B)) := by
  rw [entrywise_rootSL2_of_field Fr θ B]
  have h1 := Subgroup.mem_centralizer_iff.1 hn (rootSL2 τ L θ (SpecialLinearGroup.map Fr B))
    ⟨_, rfl⟩
  rw [← h1, mul_inv_cancel_right, inv_one, map_one, one_mul, conjSL_one]

theorem a1_typeII_hX {τ : Tag} {L : Type} [Field L] (Fr : L →+* L) {n : ModGL τ L}
    {θ : Fin τ.rank → ℤ}
    (hn : ∀ B : SL2 L, n * rootSL2 τ L θ B * n⁻¹ = rootSL2 τ L θ (WSL * B * WSL⁻¹))
    (P : GL (Fin 2) L)
    (hP : P * GeneralLinearGroup.map Fr P⁻¹ = SpecialLinearGroup.toGL (WSL : SL2 L))
    (B : SL2 L) :
    n * Units.map (entrywiseHom Fr) (rootSL2 τ L θ B) * n⁻¹ =
      rootSL2 τ L θ (conjSL (P * GeneralLinearGroup.map Fr P⁻¹) (SpecialLinearGroup.map Fr B)) := by
  rw [entrywise_rootSL2_of_field Fr θ B, hn, hP, conjSL_toGL]

theorem a1_typeI_action {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) {n : ModGL τ L}
    {θ : Fin τ.rank → ℤ}
    (hn : n ∈ Subgroup.centralizer (rootRankOneGroup τ L θ : Set (ModGL τ L))) (B : SL2 L) :
    n * Units.map (entrywiseHom Fr) (rootSL2 τ L θ B) * n⁻¹ = rootSL2 τ L θ B ↔
      B ∈ (SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL (1 : GL (Fin 2) L)) :=
  a1_hS1_of_action Fr hFr 1 (a1_typeI_hX Fr hn) B

end CFSG.RankThree.PartOne.KE
