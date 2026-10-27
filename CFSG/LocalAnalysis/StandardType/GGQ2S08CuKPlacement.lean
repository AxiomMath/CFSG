module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CuKPlane
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameSplit
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogueU
public import CFSG.LocalAnalysis.StandardType.GGQ2NoTwoNodeExc
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixAux

public section

namespace CFSG.StandardType.GGQ2S08Split

open CFSG CFSG.Assembly CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.PlaneRaw

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

theorem isComponentOf_ggG0_inf_zpowers_of_ggNbr {G : Type} [Group G] [Finite G]
    {B E : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hS : GGQTwoSetting 3 B E x L D J) (hnbr : GGNbr 3 B x D J y K) :
    IsComponentOf K (ggG0 3 B x L D J ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G)) := by
  have hKc : IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hS.1.1.1.2.2.2.2.2.2.2
      (isNeighborOf_of_ggNbr hS.1.1.2.2 hnbr)).1
  have h1 : IsComponentOf K (ggG0 3 B x L D J ⊓ Subgroup.centralizer ({y} : Set G)) :=
    hKc.of_le_of_le (le_inf (le_ggG0_of_ggNbr hnbr) hKc.1) inf_le_right
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem exists_code_rowA (hRig : GGLabelRigidInput) {G : Type} [Group G] {H E K J : Subgroup G}
    {R : RawFrameData} (core : RealizationCore H E R) {y : G} (hyE : y ∈ E)
    (hK : IsComponentOf K (H ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G)))
    {N : ℕ} (hrow : GGQ2S08RowA 3 N K J) (hN : N = 6 ∨ N = 9) :
    ∃ c : R.Code, R.admissible c ∧ K = core.component c ∧ (R.label c).tag = .A ∧
      (R.label c).rank + 1 = N ∧ 2 ≤ (R.label c).n := by
  obtain ⟨c, hc, -, hKc⟩ :=
    (core.occurs_iff (Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hyE) K).mp hK
  obtain ⟨⟨tX, r, f⟩, labJ, hlitX, -, -, htagX, hrankX, hnX, -, hdivN, hNJ⟩ := hrow
  dsimp only at htagX hrankX hnX
  subst htagX
  obtain ⟨labc, hlabc2, hhasc, -, -, -, -, -, hPc⟩ :=
    largeEvenMarking_exists_hasLabel (core.marked c hc)
  rw [hKc] at hlitX
  obtain ⟨labx, hlabx2, hhasx, -, -, -, -, -, hPx⟩ := largeEvenMarking_exists_hasLabel hlitX
  have hPc' : labc = R.label c := hPc
  have hPx' : labx = ⟨.A, r, f⟩ := hPx
  subst hPc' hPx'
  have hr2 : 2 ≤ r := by rcases hN with rfl | rfl <;> omega
  have hlab : R.label c = ⟨.A, r, f⟩ := by
    rcases ggLabelIso_typeA_cases hRig hr2 hlabc2 hlabx2 hhasc hhasx with h | h
    · exact h
    · exact absurd h.1 (by rcases hN with rfl | rfl <;> omega)
  have hf1 : 1 ≤ f := hlabx2.1
  have hf : 2 ≤ f := by
    by_contra hlt
    have hf' : labJ.n = 1 := by omega
    rw [hf'] at hdivN
    norm_num at hdivN
  refine ⟨c, hc, hKc, ?_, ?_, ?_⟩ <;> rw [hlab]
  · show r + 1 = N
    omega
  · exact hf

theorem false_of_core_rowA (hRig : GGLabelRigidInput) {G : Type} [Group G] {H E K J : Subgroup G}
    {R : RawFrameData}
    (hR : ∀ c : R.Code, R.admissible c → (R.label c).tag = .A → 2 ≤ (R.label c).n →
      5 ≤ (R.label c).rank → False)
    (core : RealizationCore H E R) {y : G} (hyE : y ∈ E)
    (hK : IsComponentOf K (H ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G)))
    {N : ℕ} (hrow : GGQ2S08RowA 3 N K J) (hN : N = 6 ∨ N = 9) : False := by
  obtain ⟨c, hc, -, htag, hrank, hn⟩ := exists_code_rowA hRig core hyE hK hrow hN
  exact hR c hc htag hn (by rcases hN with rfl | rfl <;> omega)

theorem planeRaw_label_symplectic_tag_ne {t : ℕ} (c : Code t) :
    (PlaneRaw.label .symplectic c).tag ≠ .A := by
  cases c with
  | zero S =>
      simp only [PlaneRaw.label]
      split_ifs <;> simp
  | extension e => simp [PlaneRaw.label]

theorem planeRaw_label_orthogonal_tag_ne {t : ℕ} (δ : Fin 2) (c : Code t) :
    (PlaneRaw.label (.orthogonal δ) c).tag ≠ .A := by
  cases c with
  | zero S =>
      simp only [PlaneRaw.label]
      split_ifs <;> simp
  | extension e => simp [PlaneRaw.label]

theorem excRaw_label_n_le_or_rank_le (m : Fin 6) (c : Finset (ExcRaw.Root m)) :
    (ExcRaw.label m c).n ≤ 1 ∨ (ExcRaw.label m c).rank ≤ 2 := by
  unfold ExcRaw.label
  split
  · left
    unfold ExcRaw.labelF4
    split <;> simp
  · unfold ExcRaw.labelE6Rel
    split <;> simp
  · left
    unfold ExcRaw.labelSL
    split <;> (try split_ifs) <;> simp

theorem splitPlaneRealization_of_linearCore (hRig : GGLabelRigidInput) {G : Type} [Group G]
    {H E K J : Subgroup G} {t : ℕ} {ε : Fin 2}
    (core : RealizationCore H E (planeEntry (.linear ε) t))
    {y : G} (hyE : y ∈ E)
    (hK : IsComponentOf K (H ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G)))
    {N : ℕ} (hrow : GGQ2S08RowA 3 N K J) (hN : N = 6 ∨ N = 9) :
    Nonempty (SplitPlaneRealization E K N t) := by
  obtain ⟨c, hc, hKc, -, hrank, hn⟩ := exists_code_rowA hRig core hyE hK hrow hN
  cases c with
  | zero S => exact absurd hn (by simp [planeEntry, PlaneRaw.label])
  | extension e =>
      have hadm : PlaneRaw.admissible (.linear ε) (.extension e) := hc.2
      have hsize2 : 2 ≤ (Code.extSupport e).card := hadm.2
      have hrank' : (Code.extSupport e).card - 1 + 1 = N := hrank
      have hsizeN : (Code.extSupport e).card = N := by omega
      refine ⟨⟨core.coord, e, hadm.1, hsizeN, fun b => ?_, fun b => ?_⟩⟩
      · have hcent := core.cent_eq (.extension e) hc
        rw [← hKc] at hcent
        change _ ↔ core.coord (Additive.ofMul b) ∈ (planeEntry (.linear ε) t).cent (.extension e)
        rw [← hcent]
        exact (ofMul_mem_ggLinImage core.coord (Subgroup.centralizer (K : Set G)) b).symm
      · have hin := core.inside_eq (.extension e) hc
        rw [← hKc] at hin
        change _ ↔ core.coord (Additive.ofMul b) ∈ (planeEntry (.linear ε) t).inside (.extension e)
        rw [← hin]
        exact (ofMul_mem_ggLinImage core.coord K b).symm

theorem splitAPlaneInput_of_placement (hRig : GGLabelRigidInput)
    (hplCl : PlacementCoreInputOn ClassicalLabel (catalogueOf classicalCatalogue excCatalogue))
    (hplEx : PlacementCoreInputOn ExceptionalLabel (catalogueOf classicalCatalogue excCatalogue))
    (hplSm : PlacementCoreInputOn SmallLabel (catalogueOf classicalCatalogue excCatalogue)) :
    SplitAPlaneInput := by
  intro G _ _ B E x L D J N y K hS _ hnbr hrow hN
  obtain ⟨lab, hm⟩ := ggQ2_marking_with_label hS.1.2.2.2.2
  have hmark : ∀ P : LargeEvenLabel → Prop, P lab →
      LargeEvenMarking (ggG0 3 B x L D J) (fun l _ _ _ _ _ => P l) := fun P h =>
    largeEvenMarking_mono (fun lab' _ _ _ _ _ hh => by rw [hh]; exact h) hm
  obtain ⟨kind, ⟨core⟩⟩ : ∃ kind : FrameKind, ActualCoreFrame (ggG0 3 B x L D J) E
      (catalogueOf classicalCatalogue excCatalogue kind) := by
    rcases label_cases lab with h | h | h
    · exact hplCl hS rfl (hmark _ h)
    · exact hplEx hS rfl (hmark _ h)
    · exact hplSm hS rfl (hmark _ h)
  have hyE : y ∈ E := hS.1.1.2.1.1 hnbr.1.2.1
  have hK := isComponentOf_ggG0_inf_zpowers_of_ggNbr hS hnbr
  cases kind with
  | lin t ε =>
      rw [catalogueOf_classical _ _ (show IsClassical (FrameKind.lin t ε) from trivial)] at core
      exact ⟨t, splitPlaneRealization_of_linearCore hRig core hyE hK hrow hN⟩
  | symp t =>
      rw [catalogueOf_classical _ _ (show IsClassical (FrameKind.symp t) from trivial)] at core
      exact (false_of_core_rowA hRig (fun c _ h _ _ => planeRaw_label_symplectic_tag_ne c h) core
        hyE hK hrow hN).elim
  | orth t δ =>
      rw [catalogueOf_classical _ _ (show IsClassical (FrameKind.orth t δ) from trivial)] at core
      exact (false_of_core_rowA hRig (fun c _ h _ _ => planeRaw_label_orthogonal_tag_ne δ c h)
        core hyE hK hrow hN).elim
  | unitFull M =>
      rw [catalogueOf_classical _ _ (show IsClassical (FrameKind.unitFull M) from trivial)] at core
      exact (false_of_core_rowA hRig
        (fun c _ h _ _ => by simp [classicalCatalogue, unitFullEntry, UnitRaw.label] at h) core hyE
        hK hrow hN).elim
  | unitHeart M =>
      rw [catalogueOf_classical _ _ (show IsClassical (FrameKind.unitHeart M) from trivial)] at core
      exact (false_of_core_rowA hRig
        (fun c _ h _ _ => by simp [classicalCatalogue, unitHeartEntry, UnitRaw.label] at h) core hyE
        hK hrow hN).elim
  | exceptional m =>
      rw [catalogueOf_exceptional _ _
        (show IsExceptional (FrameKind.exceptional m) from fun h => h)] at core
      exact (false_of_core_rowA hRig (fun c _ _ hn hr => by
          change 2 ≤ (ExcRaw.label m c).n at hn
          change 5 ≤ (ExcRaw.label m c).rank at hr
          rcases excRaw_label_n_le_or_rank_le m c with h | h <;> omega)
        core hyE hK hrow hN).elim

theorem ggQ2s08_cuKA_of_placement (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput)
    (hplCl : PlacementCoreInputOn ClassicalLabel (catalogueOf classicalCatalogue excCatalogue))
    (hplEx : PlacementCoreInputOn ExceptionalLabel (catalogueOf classicalCatalogue excCatalogue))
    (hplSm : PlacementCoreInputOn SmallLabel (catalogueOf classicalCatalogue excCatalogue)) :
    GGQ2S08TNCellK GGQ2S08PosASmall :=
  ggQ2s08_cuKA_of_splitAPlaneInput (splitAPlaneInput_of_placement hRig hplCl hplEx hplSm) hLB hP

end

end CFSG.StandardType.GGQ2S08Split
