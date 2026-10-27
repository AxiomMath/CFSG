module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem nineteen_fourteen_reductio (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ}
    {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h18 : R19_18At D V₀ V p L A t B r Y N Dsub H S h)
    (h20 : R19_20At D V₀ V p L A t B r Y N Dsub H S h)
    (h21 : R19_21At D V₀ V p L A t B r Y N Dsub H S h) : False := by
  have h5 : P19_16_5 D Dsub := h20.1
  obtain ⟨d, K, J, hfam, i, hi⟩ := h18.2 h5
  have h191 : P19_19_1 D p L (J i) := h20.2 d K J hfam i hi
  exact h21 d K J i hfam hi h191

theorem exists_mem_muStarSet_of_ne_empty (D : Data G) {B : Subgroup G}
    (h : muSet D B ≠ ∅) : ∃ Y : Subgroup G, Y ∈ muStarSet D B := by
  obtain ⟨Y₀, hY₀⟩ := Set.nonempty_iff_ne_empty.mpr h
  obtain ⟨Y, -, hY⟩ :=
    Set.Finite.exists_le_maximal (s := muSet D B) (Set.toFinite _) hY₀
  exact ⟨Y, hY.1, fun Z hZ hYZ => le_antisymm (hY.2 hZ hYZ) hYZ⟩

theorem exists_calMOf_ne_of_mem_muSet (D : Data G) {B Y : Subgroup G}
    (hY : Y ∈ muSet D B) : ∃ N : Subgroup G, N ∈ calMOf Y ∧ N ≠ D.M := by
  by_contra h
  apply hY.2.2.2
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨⟨D.maxLocal, hY.1⟩, ?_⟩
  intro N hN
  by_contra hNM
  exact h ⟨N, hN, hNM⟩

theorem nineteen_fourteen (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ}
    (h : Ctx19_10 D V₀ V p L A t B r)
    (hglue : ∀ Y N
      (hY : Y ∈ muStarSet D B) (hN : N ∈ calMOf Y ∧ N ≠ D.M),
      R19_glue_5At D V₀ V p L A t B r h Y N hY hN)
    (h18 : ∀ Y N Dsub H S (hctx : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_18At D V₀ V p L A t B r Y N Dsub H S hctx)
    (h20 : (∀ Y N Dsub H S (hctx : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
        R19_20_1At D V₀ V p L A t B r Y N Dsub H S hctx) ∧
      (∀ Y N Dsub H S (hctx : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
        R19_20_2At D V₀ V p L A t B r Y N Dsub H S hctx))
    (h21 : ∀ Y N Dsub H S (hctx : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_21At D V₀ V p L A t B r Y N Dsub H S hctx) :
    R19_14At D V₀ V p L A t B r h := by
  change muSet D B = ∅
  rw [Set.eq_empty_iff_forall_notMem]
  intro Y₀ hY₀
  obtain ⟨Y, hY⟩ :=
    exists_mem_muStarSet_of_ne_empty D (Set.nonempty_iff_ne_empty.mp ⟨Y₀, hY₀⟩)
  obtain ⟨N, hN, hNM⟩ := exists_calMOf_ne_of_mem_muSet D hY.1
  obtain ⟨Dsub, hD, hDle, hO2⟩ :=
    hglue Y N hY ⟨hN, hNM⟩
  have hctx : Ctx19_14 D V₀ V p L A t B r Y N Dsub (Dsub ⊔ Y)
      (pCoreOf 2 ((Dsub ⊔ Y) ⊓ D.M)) :=
    { ctx := h
      hY := hY
      hN := ⟨hN, hNM⟩
      hD := ⟨hD, hDle⟩
      hH := rfl
      hS := rfl
      hO2 := hO2 }
  exact nineteen_fourteen_reductio D hctx
    (h18 Y N Dsub (Dsub ⊔ Y) (pCoreOf 2 ((Dsub ⊔ Y) ⊓ D.M)) hctx)
    ⟨h20.1 Y N Dsub (Dsub ⊔ Y) (pCoreOf 2 ((Dsub ⊔ Y) ⊓ D.M)) hctx,
      h20.2 Y N Dsub (Dsub ⊔ Y) (pCoreOf 2 ((Dsub ⊔ Y) ⊓ D.M)) hctx⟩
    (h21 Y N Dsub (Dsub ⊔ Y) (pCoreOf 2 ((Dsub ⊔ Y) ⊓ D.M)) hctx)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
