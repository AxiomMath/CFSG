module

public import CFSG.Milestones.ASVolI.C137.Stmt

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

@[expose] def burnsideC137_CaseU33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T L P M V : Subgroup G),
    burnsideC137_Hyp G X T L P M V → IsPSU 3 3 1 (↥L ⧸ CFSG.pCore 2 ↥L) →
      burnsideC137_Concl G X T L P V M

@[expose] def burnsideC137_CaseL32Nat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T L P M V : Subgroup G),
    burnsideC137_Hyp G X T L P M V → IsPSL 3 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) →
    ((∃ (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
          (β : ↥⁅V, L⁆ →* Multiplicative (Fin 3 → ZMod 2)),
          Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧ IsNatVia L ⁅V, L⁆ ⊥ α β) ∧
        ∃ u ∈ ⁅V, L⁆, u ≠ 1 ∧ P = X ⊓ Subgroup.centralizer ({u} : Set G)) →
      burnsideC137_Concl G X T L P V M

@[expose] def burnsideC137_CaseL32Sum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T L P M V : Subgroup G),
    burnsideC137_Hyp G X T L P M V → IsPSL 3 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) →
    (∃ (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (U₁ U₂ : Subgroup G)
          (β₁ : ↥U₁ →* Multiplicative (Fin 3 → ZMod 2))
          (β₂ : ↥U₂ →* Multiplicative (Fin 3 → ZMod 2)), SumOfTwoNat L ⁅V, L⁆ α U₁ U₂ β₁ β₂) →
      burnsideC137_Concl G X T L P V M

@[expose] def burnsideC137_CaseA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T L P M V : Subgroup G),
    burnsideC137_Hyp G X T L P M V → IsAlt 6 (↥L ⧸ CFSG.pCore 2 ↥L) →
      burnsideC137_Concl G X T L P V M

@[expose] def burnsideC137_CaseHat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T L P M V : Subgroup G),
    burnsideC137_Hyp G X T L P M V → IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)) →
      burnsideC137_Concl G X T L P V M

theorem burnsideC137_corr_of_cases (hU : burnsideC137_CaseU33) (hN : burnsideC137_CaseL32Nat)
    (hS : burnsideC137_CaseL32Sum) (hA : burnsideC137_CaseA6) (hH : burnsideC137_CaseHat) :
    burnsideC137_C_1_37_corr := by
  intro G _ _ X T L P M V hyp
  obtain ⟨-, -, -, -, htype, -, -, -, -, -, -, -, hL32⟩ := id hyp
  rcases htype with h | h | h | h
  · rcases hL32 h with hs | hn
    · exact hS G X T L P M V hyp h hs
    · exact hN G X T L P M V hyp h hn
  · exact hA G X T L P M V hyp h
  · exact hH G X T L P M V hyp h
  · exact hU G X T L P M V hyp h

end CFSG.ASVolI
