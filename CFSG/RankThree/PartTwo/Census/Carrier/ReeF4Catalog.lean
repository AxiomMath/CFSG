module

public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Index
public import CFSG.LieType.BorelTits.DerivedQuotient
public import CFSG.LocalAnalysis.QuasithinUnique.B1.Interface
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public noncomputable section

namespace CFSG.TauCetiBridge.ReeF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree TauCeti

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem reeFixedGroup_eq_map_fixedSubgroup (m : ℕ) :
    reeFixedGroup .F4 K reeF4Perm (fun i => if i ∈ reeF4Long then 2 ^ m else 2 ^ (m + 1)) =
      (fixedSubgroup (reeF K m)).map (adjointGroup .F4 K).subtype :=
  haveI : CharP K ReeTag.F4.prime := ‹CharP K 2›
  (exceptional_reeFixedGroup_eq .F4 K m).2.2

@[expose] def nativeModelEquiv (m : ℕ) :
    CFSG.Blueprint.DerivedCentralQuotient
        (reeFixedGroup .F4 K reeF4Perm fun i => if i ∈ reeF4Long then 2 ^ m else 2 ^ (m + 1)) ≃*
      FixedPointCandidate (reeF K m) :=
  CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_fixedSubgroup m)).trans
      ((fixedSubgroup (reeF K m)).equivMapOfInjective _ Subtype.val_injective).symm)

end CFSG.TauCetiBridge.ReeF4

namespace CFSG.TauCetiBridge

open TauCeti CFSG.Blueprint CFSG.QuasithinUnique.B1 CFSG.Assembly.LowTwoRank ReeF4

theorem catalogBridgeFor_reeF4 (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid) :
    CatalogBridgeFor (.lie ⟨.reeF4 m, hv⟩) := by
  intro S _ _ _ ⟨e⟩
  have hfin : ∀ d : ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin (ReeF4LieIndex.of m hv)
  have := hchar (ReeF4LieIndex.of m hv)
  have hm : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    SuzukiReeIndex.halfExponent_reeF4 m hv
  obtain ⟨e₁⟩ := nonempty_candidate_equiv_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at e₁
  have hK := card_fixedField_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at hK
  refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl
    ⟨.twistedF4, 2, 2 * m + 1, by decide, ⟨Nat.prime_two, by omega, ?_⟩, m, rfl, ?_⟩)))))
  · exact ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩
  · exact ⟨(ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
      ⟨(e.trans e₁).trans (nativeModelEquiv m).symm⟩⟩

theorem catalogBridgeFor_tits (hv : LieTypeIndex.tits.Valid) :
    CatalogBridgeFor (.lie ⟨.tits, hv⟩) := by
  intro S _ _ _ ⟨e⟩
  have hfin : ∀ d : TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin TitsLieIndex.of
  have := hchar TitsLieIndex.of
  obtain ⟨e₁⟩ := nonempty_candidate_equiv_tits TitsLieIndex.of
  refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl
    ⟨.Tits, 2, 1, by decide, ⟨Nat.prime_two, le_rfl, ?_⟩, 0, rfl, ?_⟩)))))
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨TitsLieIndex.of.1.fixedField, inferInstance, inferInstance,
      (card_fixedField_tits _).trans (pow_one 2).symm,
      ⟨(e.trans e₁).trans (nativeModelEquiv 0).symm⟩⟩

end CFSG.TauCetiBridge
