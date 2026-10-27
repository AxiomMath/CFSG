module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndNode
public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley InndiagE6 RecipeFieldE6
  TableBExc.E6Three

namespace E6ThreeEnd


theorem ggEndNodeAut_hat (K : Type) [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) :
    TableBUD.GGEndNodeAut 3 5 (adjointGroup .E6 K) (Set.range (hatAut .E6 K)) :=
  fun _ hX hXI h5 _ => autEndNode_of_le_hatAut h3 hX (fun φ hφ => hXI φ hφ) h5

@[expose] def E6ThreeEndOn (K : Type) [Field K] (S : (Fin Tag.E6.rank → ℤ) → Prop) : Prop :=
  TableBUD.GGEndNodeAut 3 5 (LargeEvenCenterQuot (MarkChev.chevH Tag.E6.cartan S K false))
    {φ | IsInnDiagOn (MarkChev.chevH Tag.E6.cartan S K false) (markDiagUnit S K) φ}

theorem E6ThreeEndOn.of_eq {K : Type} [Field K] {S S' : (Fin Tag.E6.rank → ℤ) → Prop}
    (hS : S = S') (h : E6ThreeEndOn K S) : E6ThreeEndOn K S' :=
  hS ▸ h

theorem e6ThreeEndOn_isRoot (K : Type) [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) : E6ThreeEndOn K (IsRoot Tag.E6) := by
  unfold E6ThreeEndOn
  rw [markDiagUnit_isRoot]
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot Tag.E6) K), H = adjointGroup Tag.E6 K →
      TableBUD.GGEndNodeAut 3 5 (LargeEvenCenterQuot H)
        {φ | IsInnDiagOn H (rootDiagUnit Tag.E6) φ} from
    key _ (chevH_false_eq_adjointGroup K Tag.E6)
  intro H hH
  subst hH
  have hZ : Subgroup.center (adjointGroup Tag.E6 K) = ⊥ := center_adjointGroup_eq_bot
  have hmk : Function.Injective (LargeEvenCenterMk (adjointGroup Tag.E6 K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, LargeEvenCenterMk, QuotientGroup.ker_mk', hZ]
  refine ggEndNodeAut_of_mulEquiv (centerQuotEquivOfBot hZ) (fun φ hφ => ?_)
    (ggEndNodeAut_hat K h3)
  obtain ⟨g, hg, a, -, -, hφc⟩ := hφ
  refine ⟨⟨g * rootDiagUnit .E6 a, ⟨g, hg, a, rfl⟩⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
  have h1 := hφc.2 h (hφc.1 h h.2)
  rw [congr_centerQuotEquivOfBot_mk hZ φ h] at h1
  have h2 := congrArg Subtype.val (hmk h1)
  rw [coe_hatAut_apply]
  exact h2.symm

theorem ggEndNodeAut_E6_three (K : Type) [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) :
    TableBUD.GGEndNodeAut 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  have h := (e6ThreeEndOn_isRoot K h3).of_eq (largeEvenIsRoot_eq_isRoot Tag.E6).symm
  unfold E6ThreeEndOn at h
  rw [← diagHom_eq_markDiagUnit] at h
  suffices key : ∀ H : Subgroup (LargeEvenChevGL Tag.E6.cartan K),
      H = MarkChev.chevH Tag.E6.cartan (LargeEvenIsRoot Tag.E6.cartan) K false →
      TableBUD.GGEndNodeAut 3 5 (LargeEvenCenterQuot H)
        (LargeEvenChevIDImage Tag.E6.cartan K H) from
    key _ (largeEvenChevH_eq _ K false)
  intro H hH
  subst hH
  intro X hX hXI hr h3'
  exact h X hX (fun φ hφ => mem_chevID_iff_isInnDiagOn.mp (hXI φ hφ)) hr h3'

end E6ThreeEnd


theorem ggE6ThreeEndNodeInput_holds : GGE6ThreeEndNodeInput := fun K _ _ _ h3 =>
  TableBUD.ggEndNode_of_aut (E6ThreeEnd.ggEndNodeAut_E6_three K h3)

theorem ggStdSubPreInputOn_E6_three_of_two (hT : GGE6TwoEndNodeInput) :
    GGStdSubPreInputOn GGTableBE6LabelThree :=
  ggStdSubPreInputOn_E6_three ggE6ThreeEndNodeInput_holds hT

theorem ggStdSubPreInputOn_E6_three_of_twoInputs (hT : E6ThreeEnd.GGE6TwoToralInput)
    (hL : E6ThreeEnd.GGE6TwoLayerInput) : GGStdSubPreInputOn GGTableBE6LabelThree :=
  ggStdSubPreInputOn_E6_three_of_two (E6ThreeEnd.ggE6TwoEndNodeInput_of_inputs hT hL)

end CFSG.StandardType
