module

public import CFSG.Quasithin.H13.NQSetupDefs

public section

namespace CFSG.Quasithin.H13.NQBlock

open CFSG.Open CFSG.Quasithin.H13

@[expose] def NonquasisimpleMaximalNormalizerSetup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    (∃ K : Subgroup G, quasithinIsFaithfulLocal T K ∧
      ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) →
    ∃ L M : Subgroup G, QTNQ T L M

@[expose] def NonquasisimpleInternalModuleTI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    qtnqU L M ≠ ⊥ ∧ ∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M

@[expose] def NonquasisimpleTITerminalContradiction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ¬ ∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M

theorem stmt13_1_7_of_inputs (hS : NonquasisimpleMaximalNormalizerSetup)
    (hTI : NonquasisimpleInternalModuleTI) (hC : NonquasisimpleTITerminalContradiction) :
    Stmt13_1_7 := by
  intro G _ _ T hs hnab hQ hT hexcl K hK
  by_contra hq
  obtain ⟨L, M, h⟩ := hS G T hs hnab hQ hT hexcl ⟨K, hK, hq⟩
  exact hC G T L M h (hTI G T L M h).2

end CFSG.Quasithin.H13.NQBlock
