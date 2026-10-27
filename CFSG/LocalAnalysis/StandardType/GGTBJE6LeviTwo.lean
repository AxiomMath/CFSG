module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBE6PlusThreeTB
public import CFSG.LocalAnalysis.StandardType.GGTBJF4LeviFrameMap
public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoModel
public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoLang
public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoWitness
public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoClassFacts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e6Two_referenceFrame
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    ∃ D : ExcFrames.E6QPlusThree.E6QPlusThreeFrame K, GGF4LeviFrame 3 D.frame.range := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card K + 1 := by rw [hK]
  obtain ⟨Fr, g0, ζ, hζ, D, hFr, hg0C, hg0, hζo, hFrζ, hsurj, hcoord⟩ :=
    ExcFrames.E6QPlusThree.exists_e6QPlusThreeFrame_with_coordinates h3
  refine ⟨D, ?_⟩
  obtain ⟨S, ι, hq, hι, hrange, hframe, hT, hρ⟩ :=
    e6Two_langSetup D hFr hg0C hg0 hFrζ hcoord
  have hSC := e6Two_frame_selfCentralizing hK D hFr hg0C hg0 hζo hFrζ hcoord
  obtain ⟨nk, wt, hnk, hwn, hwt⟩ := e6Two_torusWitness D hsurj hSC
  refine ⟨AlgebraicClosure K, inferInstance, ζ, hζ, D.frame, nk, 3, wt, hζo, D.frame_injective,
    rfl, hnk, hwn, hwt, fun t ht Y hY => ?_⟩
  obtain ⟨i, hker, hlow⟩ := e6Two_classFacts hK S hq hρ ι hι hrange hζo D.frame hframe hT t ht hY
  exact ⟨i, hker, fun _ _ _ _ c hc => hlow c hc⟩

theorem e6Two_leviFrame
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (E : Subgroup (adjointGroup .E6 K)) (hE : IsElemAbelian 3 E)
    (_hSC : ∀ g : adjointGroup .E6 K, (∀ c ∈ E, g * c = c * g) → g ^ 3 = 1 → g ∈ E)
    (h4 : 3 ^ 4 ≤ Nat.card E) : GGF4LeviFrame 3 E := by
  obtain ⟨D, hD⟩ := e6Two_referenceFrame hK
  obtain ⟨c, hc⟩ := E6PlusThreeTB.exists_conj_map_eq_frame_range D hE h4
  exact GGF4LeviFrame.of_map_eq (MulAut.conj c) hc hD

theorem ggTBJE6LeviL_two
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGHasLabel (⟨.E6, 0, 1⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hp3 : p = 3) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, E, hE, hE4, hEself, hA⟩ := ggE6Two_model_L hRig hH hL hp3
  subst hp3
  exact ggTBJF4LeviL_of_model hH ⟨hN, adjointGroup .E6 Fq, inferInstance,
    center_adjointGroup_eq_bot, e, E, hA, e6Two_leviFrame hFqcard E hE hEself hE4⟩

theorem ggTBJE6LeviK_two
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K)
    (hK : GGHasLabel (⟨.E6, 0, 1⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp3 : p = 3) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  obtain ⟨hN, Fq, _, _, _, hFqcard, e, E, hE, hE4, hEself, hA⟩ := ggE6Two_model_K hRig hH hK hp3
  subst hp3
  exact ggTBJF4LeviK_of_model hH hJK ⟨hN, adjointGroup .E6 Fq, inferInstance,
    center_adjointGroup_eq_bot, e, E, hA, e6Two_leviFrame hFqcard E hE hEself hE4⟩

theorem ggTBJE6LeviL_Q
    (hRig : GGLabelRigidInput) :
    GGTBJETypeLeviL .E6 fun p n labJ => ggTBJE6RowCand p n labJ ∨ ¬ (p = 3 ∧ n = 1) := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ n hΛ hL _ _ _ _ _ hnc
  have hP : p = 3 ∧ n = 1 := by
    by_contra h
    exact hnc (Or.inr h)
  obtain ⟨hp3, rfl⟩ := hP
  exact ggTBJE6LeviL_two hRig hH hL hp3

theorem ggTBJE6LeviK_Q
    (hRig : GGLabelRigidInput) :
    GGTBJETypeLeviK .E6 fun p n labJ => ggTBJE6RowCand p n labJ ∨ ¬ (p = 3 ∧ n = 1) := by
  intro G _ _ p B Bs x L D J y K hH hJK _ _ _ n hΛ hK _ _ _ _ _ hnc
  have hP : p = 3 ∧ n = 1 := by
    by_contra h
    exact hnc (Or.inr h)
  obtain ⟨hp3, rfl⟩ := hP
  exact ggTBJE6LeviK_two hRig hH hJK hK hp3

end CFSG.StandardType

end
