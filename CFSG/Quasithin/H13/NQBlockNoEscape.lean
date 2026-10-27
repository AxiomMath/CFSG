module

public import CFSG.Quasithin.H13.NQBlockOriginalKSingleton
public import CFSG.Quasithin.H13.NQBlockPrimeResidualCenter
public import CFSG.Foundations.HigherElementaryThompson

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

variable {G : Type} [Group G]

@[expose] def nqHigherThompson (R : Subgroup G) (j : ℕ) : Subgroup G :=
  (CFSG.higherElemThompson R j).map R.subtype

@[expose] def nqSourceModule (Y R : Subgroup G) : Subgroup G :=
  sSup {Z | ∃ x ∈ Y ⊔ R, CFSG.conjugate (omegaOneCenterOf 2 R) x = Z}

@[expose] def OriginalRControlledThompson : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ R : Subgroup G, (R : Set G) = nqOriginalCentralizer T L →
      3 ≤ CFSG.pRank 2 R ∧ ∃ j : ℕ, j ≤ 1 ∧ normalizer (nqHigherThompson R j : Set G) ≤ M

@[expose] def ControlledThompsonSourceCommutator : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ R : Subgroup G, (R : Set G) = nqOriginalCentralizer T L →
    ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
    ∀ Y : Subgroup G, Y ≤ H → (Y.subgroupOf H).Normal → ¬ Y ≤ M →
      ⁅nqOriginalK T L, Y⁆ ≤ pCoreOf 2 Y →
      ((∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Monoid.exponent (Y ⧸ CFSG.pCore 2 Y) = p ∧
          Subgroup.upperCentralSeries (Y ⧸ CFSG.pCore 2 Y) 2 = ⊤ ∧
          CFSG.pRank p (Y ⧸ CFSG.pCore 2 Y) ≤ 2) ∨
        Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* GL (Fin 3) (ZMod 2))) →
    ∀ j : ℕ, j ≤ 1 → 3 ≤ CFSG.pRank 2 R → normalizer (nqHigherThompson R j : Set G) ≤ M →
      ∃ A ∈ CFSG.higherElemThompsonFamily R j,
        ⁅⁅nqSourceModule Y R, nqOriginalK T L⁆, ⁅Y, A.map R.subtype⁆⁆ ≠ ⊥

@[expose] def SolvableSourceRankBudget : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ R : Subgroup G, (R : Set G) = nqOriginalCentralizer T L →
    ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
    ∀ Y : Subgroup G, Y ≤ H → (Y.subgroupOf H).Normal → ¬ Y ≤ M →
      ⁅nqOriginalK T L, Y⁆ ≤ pCoreOf 2 Y →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Monoid.exponent (Y ⧸ CFSG.pCore 2 Y) = p ∧
          Subgroup.upperCentralSeries (Y ⧸ CFSG.pCore 2 Y) 2 = ⊤ ∧
          CFSG.pRank p (Y ⧸ CFSG.pCore 2 Y) ≤ 2) →
    ∀ j : ℕ, j ≤ 1 → 3 ≤ CFSG.pRank 2 R → normalizer (nqHigherThompson R j : Set G) ≤ M →
      ∀ A ∈ CFSG.higherElemThompsonFamily R j,
        ⁅⁅nqSourceModule Y R, nqOriginalK T L⁆, ⁅Y, A.map R.subtype⁆⁆ = ⊥

@[expose] def SimpleSourceTensorEquality : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ R : Subgroup G, (R : Set G) = nqOriginalCentralizer T L →
    ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
    ∀ Y : Subgroup G, Y ≤ H → (Y.subgroupOf H).Normal → ¬ Y ≤ M →
      ⁅nqOriginalK T L, Y⁆ ≤ pCoreOf 2 Y →
      (Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* GL (Fin 3) (ZMod 2))) →
    ∀ j : ℕ, j ≤ 1 → 3 ≤ CFSG.pRank 2 R → normalizer (nqHigherThompson R j : Set G) ≤ M →
      ∀ A ∈ CFSG.higherElemThompsonFamily R j,
        ⁅⁅nqSourceModule Y R, nqOriginalK T L⁆, ⁅Y, A.map R.subtype⁆⁆ = ⊥

theorem originalNoNormalSourceYEscapes_of (hRJ : OriginalRControlledThompson)
    (hC : ControlledThompsonSourceCommutator) (hS : SolvableSourceRankBudget)
    (hT : SimpleSourceTensorEquality) : OriginalNoNormalSourceYEscapes := by
  intro G _ _ T L M h H hH hKTH hHM Y hYH hYn hYM hKY hbr
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.t_le.trans h.eq_normalizer.le)
  obtain ⟨hm, j, hj, hJM⟩ := hRJ G T L M h R hR
  obtain ⟨A, hA, hVYA⟩ := hC G T L M h R hR H hH hKTH hHM Y hYH hYn hYM hKY hbr j hj hm hJM
  rcases hbr with hodd | hsimple
  · exact hVYA (hS G T L M h R hR H hH hKTH hHM Y hYH hYn hYM hKY hodd j hj hm hJM A hA)
  · exact hVYA (hT G T L M h R hR H hH hKTH hHM Y hYH hYn hYM hKY hsimple j hj hm hJM A hA)

end CFSG.Quasithin.H13.NQBlock
