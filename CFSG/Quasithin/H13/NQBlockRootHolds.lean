module

public import CFSG.Quasithin.H13.NQBlockRootChainHolds
public import CFSG.Quasithin.H13.NQBlockEvenSymplecticFour
public import CFSG.Quasithin.H13.NQCatOuterDerived
public import CFSG.Quasithin.H13.NQBlockCPUBridge
public import CFSG.Quasithin.H13.NQRigidShort
public import CFSG.Quasithin.H13.NQRigidCPU

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem original_characteristic_witness_singleton_holds
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G}
    (hXR : X ≤ (CFSG.solvableRadical L).map L.subtype) (hXc : (X.subgroupOf L).Characteristic)
    (hX2 : CFSG.pCore 2 X ≠ ⊥) (hXno : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧
      CFSG.Quasithin.SteinbergCC.normalizerFrattiniConj X l ≠ 1)
    (hirr : ∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V,
        CFSG.Quasithin.SteinbergCC.normalizerFrattiniConj X l w ∈ V) → V = ⊥ ∨ V = ⊤) :
    quasithinIsMaxTwoLocal M ∧ X ⊔ T ≤ M ∧
      ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → X ⊔ T ≤ M' → M' = M :=
  original_characteristic_witness_singleton_of_groupCPU
      (originalXTOrbitPlacement_of_outerDerivedCoprime NQCat.stmtOuterDerivedCoprime_holds)
      NQRigid.stmtCPUOffenderSection_holds NQRigid.stmtCPUShortBlock_holds
      (QTESylow.catalog_noncyclic_prime_sylow_product_model_restriction
          QTESylow.he_ru_noncyclic_prime_sylow_product) originalWitnessExcludesEvenSymplecticFour_holds
      h hp hp5 hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr

theorem factWitnessSingleton_holds
    : NQRigid.FactWitnessSingleton := by
  intro G _ _ T L M h p hp hp5 X hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr
  obtain ⟨hM, hle, huniq⟩ := original_characteristic_witness_singleton_holds h hp hp5 hXR hXc hX2
    hXno hXA hexp hrk hW hLW hirr
  exact NQRigid.maximalTwoLocalsContaining_eq_singleton hM hle huniq

end CFSG.Quasithin.H13.NQBlock
