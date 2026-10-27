module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEToral
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyOrder
import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public noncomputable section

namespace CFSG.StandardType

namespace LayerSixE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE8F
  CFSG.StandardType.LayerExc CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem map_famCentralizer_le_normalizer (F : Set (Fin τ.rank → Kˣ)) :
    (famCentralizer F).map (adjointGroup τ K).subtype ≤ Subgroup.normalizer
      ((torusGroup τ K ⊔ rootSpan τ K (famKernel F) : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) :=
  (map_famCentralizer_le_sup F).trans
    (sup_le Subgroup.le_normalizer (map_famWeylReps_le_normalizer (K := K) F))

section Bridge

open CFSG.HardMathSupport.Timmesfeld.Torality

theorem famKernel_eq_familyKernel (F : Set (Fin τ.rank → Kˣ)) :
    famKernel F = familyKernel (fun a : F => (a : Fin τ.rank → Kˣ)) := by
  ext α
  simp only [famKernel, familyKernel, Set.mem_setOf_eq, Subtype.forall]

theorem famStabilizer_eq_familyStabilizer (F : Set (Fin τ.rank → Kˣ)) :
    famStabilizer F = familyStabilizer (fun a : F => (a : Fin τ.rank → Kˣ)) := by
  ext w
  simp only [famStabilizer, familyStabilizer, Set.mem_setOf_eq, Subtype.forall]

theorem map_famCentralizer_eq_familyCentralizer (F : Set (Fin τ.rank → Kˣ)) :
    (famCentralizer F).map (adjointGroup τ K).subtype =
      familyCentralizer τ K (fun a : F => (a : Fin τ.rank → Kˣ)) := by
  ext x
  rw [mem_familyCentralizer, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, fun i => hg i i.2⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, fun a ha => h ⟨a, ha⟩, rfl⟩

theorem card_famCentralizer [Finite K] (F : Set (Fin τ.rank → Kˣ)) :
    Nat.card (famCentralizer F) = Nat.card (torusGroup τ K) *
      (Nat.card K ^ (famKernel F ∩ {α | IsRoot τ α ∧ 0 < height α}).ncard) *
      ∑ᶠ w : familyStabilizerSubgroup (fun a : F => (a : Fin τ.rank → Kˣ)),
        Nat.card K ^ (famKernel F ∩ inversionSet (w : WeylGroup τ)).ncard := by
  have h := card_familyCentralizer (τ := τ) (K := K) (fun a : F => (a : Fin τ.rank → Kˣ))
  rw [← famKernel_eq_familyKernel, ← map_famCentralizer_eq_familyCentralizer] at h
  rw [← h]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective _ _ (adjointGroup τ K).subtype_injective).toEquiv

end Bridge

end LayerSixE

end CFSG.StandardType
