module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusDefs
public import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesMap
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartTwo.Sec21.U4Lines (mapL mapL_le mapL_mono mapL_sup card_mapL
  mapL_inj mapL_le_centralizer mapL_inf_centralizer mapL_perfectResidual_inf mapL_conj
  embedOf embedOf_injective)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes
  (mapL_mapL_symm notationB8103_mapL_iff)

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {L : Subgroup G}
  {L' : Subgroup G'}

omit [Finite G] in
theorem kOf8103_le (L B : Subgroup G) : F08.KOf8103 L B ≤ L := by
  rw [F08.KOf8103]
  exact (Subgroup.map_subtype_le _).trans inf_le_left

theorem mapL_kOf8103 (E : L ≃* L') {B : Subgroup G} (hB : B ≤ L) :
    mapL E (F08.KOf8103 L B) = F08.KOf8103 L' (mapL E B) :=
  mapL_perfectResidual_inf E hB

omit [Finite G] [Finite G'] in
private theorem mapL_symm_mapL (E : L ≃* L') {A : Subgroup G} (hA : A ≤ L) :
    mapL E.symm (mapL E A) = A := by
  simpa using mapL_mapL_symm (E := E.symm) hA

omit [Finite G] [Finite G'] in
private theorem mapL_symm_inf_centralizer (E : L ≃* L') {E₀ : Subgroup G} (hE₀ : E₀ ≤ L) :
    mapL E.symm (L' ⊓ centralizer (mapL E E₀ : Set G')) =
      L ⊓ centralizer (E₀ : Set G) := by
  rw [mapL_inf_centralizer E.symm (mapL_le E E₀), mapL_symm_mapL E hE₀]

private theorem pRank_mapL (E : L ≃* L') {A : Subgroup G} (hA : A ≤ L) (p : ℕ) :
    Open.pRank p (mapL E A) = Open.pRank p A := by
  have h1 : Open.pRank p (mapL E A) = Open.pRank p (A.subgroupOf L) :=
    CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective p
      (embedOf_injective E) _
  have h2 : Open.pRank p A = Open.pRank p (A.subgroupOf L) := by
    have h := CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective p
      L.subtype_injective (A.subgroupOf L)
    rwa [Subgroup.map_subgroupOf_eq_of_le hA] at h
  exact h1.trans h2.symm

private theorem mapL_symm_le_KOf8103 (E : L ≃* L') {B : Subgroup G} (hB : B ≤ L)
    {A' : Subgroup G'} (hA' : A' ≤ F08.KOf8103 L' (mapL E B)) :
    mapL E.symm A' ≤ F08.KOf8103 L B := by
  calc mapL E.symm A' ≤ mapL E.symm (F08.KOf8103 L' (mapL E B)) := mapL_mono E.symm hA'
    _ = F08.KOf8103 L B := by
        rw [mapL_kOf8103 E.symm (mapL_le E B), mapL_symm_mapL E hB]

omit [Finite G] [Finite G'] in
private theorem mapL_symm_le_centralizer_inf (E : L ≃* L') {E₀ : Subgroup G} (hE₀ : E₀ ≤ L)
    {D' : Subgroup G'}
    (hD' : D' ≤ centralizer ((L' ⊓ centralizer (mapL E E₀ : Set G') : Subgroup G') : Set G')) :
    mapL E.symm D' ≤ centralizer ((L ⊓ centralizer (E₀ : Set G) : Subgroup G) : Set G) := by
  have h := mapL_le_centralizer E.symm hD'
  rwa [mapL_symm_inf_centralizer E hE₀] at h

private theorem pRank_mapL_sup_KOf8103 (E : L ≃* L') {B₀ B₁ : Subgroup G} (hB₀ : B₀ ≤ L)
    (hB₁ : B₁ ≤ L) (p : ℕ) :
    Open.pRank p (F08.KOf8103 L B₀ ⊔ F08.KOf8103 L B₁) =
      Open.pRank p (F08.KOf8103 L' (mapL E B₀) ⊔ F08.KOf8103 L' (mapL E B₁)) := by
  have hmap : mapL E (F08.KOf8103 L B₀ ⊔ F08.KOf8103 L B₁) =
      F08.KOf8103 L' (mapL E B₀) ⊔ F08.KOf8103 L' (mapL E B₁) := by
    rw [mapL_sup E (kOf8103_le L B₀) (kOf8103_le L B₁),
      mapL_kOf8103 E hB₀, mapL_kOf8103 E hB₁]
  calc Open.pRank p (F08.KOf8103 L B₀ ⊔ F08.KOf8103 L B₁)
      = Open.pRank p (mapL E (F08.KOf8103 L B₀ ⊔ F08.KOf8103 L B₁)) :=
        (pRank_mapL E (sup_le (kOf8103_le L B₀) (kOf8103_le L B₁)) p).symm
    _ = Open.pRank p (F08.KOf8103 L' (mapL E B₀) ⊔ F08.KOf8103 L' (mapL E B₁)) := by
        rw [hmap]

theorem TorusFacts.of_mapL (E : L ≃* L') {E₀ : Subgroup G} (hE₀ : E₀ ≤ L) {n : ℕ}
    (h : TorusFacts G' L' (mapL E E₀) n) : TorusFacts G L E₀ n := by
  intro B₀ hB₀
  have hB₀L : B₀ ≤ L := hB₀.2.1.trans hE₀
  have hB₀' : F08.NotationB8103 L' (mapL E E₀) n (mapL E B₀) :=
    (notationB8103_mapL_iff E hB₀L).mpr hB₀
  obtain ⟨B₁', hB₁'K, hB₁'not, hB₁'ne, hB₁'uniq, hB₁'p⟩ := h (mapL E B₀) hB₀'
  have hB₁'L' : B₁' ≤ L' := hB₁'K.trans (kOf8103_le L' (mapL E B₀))
  have hB₁K : mapL E.symm B₁' ≤ F08.KOf8103 L B₀ :=
    mapL_symm_le_KOf8103 E hB₀L hB₁'K
  have hB₁L : mapL E.symm B₁' ≤ L := hB₁K.trans (kOf8103_le L B₀)
  have hB₁not : F08.NotationB8103 L E₀ n (mapL E.symm B₁') :=
    (notationB8103_mapL_iff E hB₁L).mp
      (by rw [mapL_mapL_symm E hB₁'L']; exact hB₁'not)
  have hB₁ne : mapL E.symm B₁' ≠ B₀ := by
    intro hEq
    apply hB₁'ne
    rw [← hEq, mapL_mapL_symm E hB₁'L']
  have huniq : ∀ Y : Subgroup G, F08.NotationB8103 L E₀ n Y →
      Y = B₀ ∨ Y = mapL E.symm B₁' := by
    intro Y hY
    have hYL : Y ≤ L := hY.2.1.trans hE₀
    have hY' : F08.NotationB8103 L' (mapL E E₀) n (mapL E Y) :=
      (notationB8103_mapL_iff E hYL).mpr hY
    rcases hB₁'uniq (mapL E Y) hY' with hY₀ | hY₁
    · exact Or.inl (mapL_inj E hYL hB₀L hY₀)
    · exact Or.inr (mapL_inj E hYL (mapL_le E.symm B₁')
        (by rw [mapL_mapL_symm E hB₁'L']; exact hY₁))
  refine ⟨mapL E.symm B₁', hB₁K, hB₁not, hB₁ne, huniq, ?_⟩
  intro p hp hpdvd
  obtain ⟨⟨D₀', hD₀'K, hD₀'card, hD₀'cent⟩, hprank'⟩ := hB₁'p p hp hpdvd
  have hD₀'L' : D₀' ≤ L' := hD₀'K.trans (kOf8103_le L' (mapL E B₀))
  have hprank := pRank_mapL_sup_KOf8103 E hB₀L hB₁L p
  rw [mapL_mapL_symm E hB₁'L'] at hprank
  refine ⟨⟨mapL E.symm D₀', mapL_symm_le_KOf8103 E hB₀L hD₀'K, ?_, ?_⟩, ?_⟩
  · rw [card_mapL E.symm hD₀'L', hD₀'card]
  · exact mapL_symm_le_centralizer_inf E hE₀ hD₀'cent
  · rw [hprank]
    exact hprank'

theorem TorusAt.of_mapL (E : L ≃* L') {n : ℕ} (h : TorusAt G' L' n) : TorusAt G L n := by
  intro E₀ hE₀ hE₀ea hE₀card
  have hE₀' : IsElemAbelian 3 (mapL E E₀) :=
    (hE₀ea.subgroupOf L).map (embedOf E)
  have hE₀card' : Nat.card (mapL E E₀) = 9 := by
    rw [card_mapL E hE₀, hE₀card]
  exact TorusFacts.of_mapL E hE₀ (h (mapL E E₀) (mapL_le E E₀) hE₀' hE₀card')

omit [Finite G'] in
theorem TorusFacts.of_conj {g : G} (hg : g ∈ L) {E₀ : Subgroup G} (hE₀ : E₀ ≤ L) {n : ℕ}
    (h : TorusFacts G L (E₀.map (MulAut.conj g).toMonoidHom) n) : TorusFacts G L E₀ n := by
  have hmap : mapL (MulAut.conj (⟨g, hg⟩ : L)) E₀ =
      E₀.map (MulAut.conj g).toMonoidHom := by
    simpa using mapL_conj (Y := L) (⟨g, hg⟩ : L) hE₀
  rw [← hmap] at h
  exact TorusFacts.of_mapL (MulAut.conj (⟨g, hg⟩ : L)) hE₀ h

omit [Finite G'] [Finite G] in
theorem notationB8103_iff_of_le {n : ℕ} {S E B : Subgroup G} (hES : E ≤ S)
    (hSE : ∀ s ∈ S, s ^ 3 = 1 → s ∈ E) :
    F08.NotationB8103 L S n B ↔ F08.NotationB8103 L E n B := by
  refine ⟨fun ⟨h3, hBS, hL⟩ => ⟨h3, fun b hb => hSE b (hBS hb) ?_, hL⟩,
    fun ⟨h3, hBE, hL⟩ => ⟨h3, hBE.trans hES, hL⟩⟩
  have := congrArg (fun x : B => (x : G)) (pow_card_eq_one' (x := (⟨b, hb⟩ : B)))
  simpa [h3] using this

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
