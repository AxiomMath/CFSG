module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeGlue
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeTwoTb
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeTwoDesc
import CFSG.LocalAnalysis.StandardType.GGRootGenExcLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.HardMathSupport.Solomon.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTwE6ThreeOddInstOne : Prop :=
  ∀ {K₁ : Type} [Field K₁] [Finite K₁], Nat.card K₁ = (2 ^ 1) ^ 2 →
    ∀ {L₁ : Type} [Group L₁] [Finite L₁] {ψ₁ : L₁ →* TwE6Delta.RecipeR K₁ 1}
      {A₁ : Subgroup (MulAut L₁)}, Odd (Nat.card ψ₁.ker) →
      GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K₁ 1) (TwE6Delta.RecipeI K₁ 1) L₁ ψ₁ A₁ →
      ∃ κ : ↥A₁ →* Multiplicative (Fin Tag.E6.rank → ZMod 3), GGE6ThreeFrameA A₁ κ ∧
        ∀ (y : ↥A₁) (J : Subgroup L₁), y ≠ 1 → IsComponentOf J (fixSubgroup (y : MulAut L₁)) →
          GGE6ThreeClassA A₁ κ y J (∃ m : ℕ, 1 ≤ m ∧
            GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))

@[expose] def GGTwE6ThreeCompInvOne : Prop :=
  ∀ {K₁ : Type} [Field K₁] [Finite K₁], Nat.card K₁ = (2 ^ 1) ^ 2 →
    ∀ {L₁ : Type} [Group L₁] [Finite L₁] {ψ₁ : L₁ →* TwE6Delta.RecipeR K₁ 1}
      {A₁ : Subgroup (MulAut L₁)}, Odd (Nat.card ψ₁.ker) →
      GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K₁ 1) (TwE6Delta.RecipeI K₁ 1) L₁ ψ₁ A₁ →
      ∀ (y : ↥A₁) (J : Subgroup L₁), y ≠ 1 →
        IsComponentOf J (fixSubgroup (y : MulAut L₁)) → ∀ a ∈ A₁, ∀ x ∈ J, a x ∈ J

theorem ggTBJTwE6Levi_threeOne_of_inst
    (hOdd : GGTwE6ThreeOddInstOne) (hNorm : GGTwE6ThreeCompInvOne)
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {Bs J X : Subgroup G} {g : G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ 3 = 1 → a ∈ Bs)
    (hJX : J ≤ X) (hgBs : g ∈ Bs) (hJg : J ≤ Subgroup.centralizer ({g} : Set G))
    (hgX : ∃ l ∈ X, g * l * g⁻¹ ≠ l)
    (hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G)))
    (bX : ↥Bs) (hbX1 : bX ≠ 1) (hbXc : (bX : G) ∈ Subgroup.centralizer (X : Set G))
    (hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 ^ 3)
    (hInn : GGInnerDiagOn Bs X) (hXc : commutator ↥X = ⊤)
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, 1⟩ : LargeEvenLabel))
    (hXl : GGHasLabel (⟨.twE6, 0, 1⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    (hrk : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      3 ^ 5 ≤ Nat.card (ggGamma X hN).range)
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hD4 : ¬ (labJ.tag = .D ∧ labJ.rank = 4)) :
    GGResSideDatum 3 Bs X J ∨ GGResLeviSideDatumLE3 3 Bs X J := by
  obtain ⟨hN, K, _, _, hK, ψ₀, hTB⟩ :=
    ggTwE6Three_tbGroup_of_label_one hRig hBs hSC hInn hXc hΛ hXl hrk
  obtain ⟨κ, hF, hCall⟩ := ggTwE6Three_frameClass_descent_one hOdd hNorm hK hTB
  have hJp : Group.IsPerfect ↥J := ⟨hcomp.2.2.1⟩
  have hC := ggE6ThreeCoordData_mono (ggTwE6Three_label_of_subgroupOf hJX hJp)
    (ggE6Three_coordData_of_frameA hBs hSC hN hgBs hJX hgX hcomp
      (ggTwE6Three_hKer_one hBs hN hK hTB) hF
      (P := fun J' => ∃ m : ℕ, 1 ≤ m ∧
        GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J' ⧸ Subgroup.center ↥J')) hCall)
  have hP : ¬ ∃ m : ℕ, 1 ≤ m ∧
      GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) := by
    rintro ⟨m, hm, hlab⟩
    have hiso : GGLabelIso labJ ⟨.D, 4, m⟩ :=
      hRig labJ ⟨.D, 4, m⟩ _ hΛJ ⟨hm, by norm_num⟩ hJlab hlab
    apply hD4
    obtain ⟨t, r, n'⟩ := labJ
    unfold GGLabelIso at hiso
    rcases hiso with h | h | h | h | h | h | h | h
    · simp only [LargeEvenLabel.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨rfl, rfl⟩
    all_goals simp at h
  exact ggTBJE6Levi_of_threeCoordData hgBs hJX hJg hC hP bX hbX1 hbXc hcardJ

theorem ggTBJTwE6LeviL_threeOne_of_inst
    (hOdd : GGTwE6ThreeOddInstOne) (hNorm : GGTwE6ThreeCompInvOne)
    (hRig : GGLabelRigidInput) (hRL : GGTwE6ThreeBstarRankInput) :
    GGTBJETypeLeviL .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ ¬ (p = 3 ∧ n = 1) := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ n hΛ hL _ labJ hΛJ hJlab _ hnc
  have hP : p = 3 ∧ n = 1 := by
    by_contra h
    exact hnc (Or.inr h)
  obtain ⟨hp3, hn1⟩ := hP
  subst hp3
  subst hn1
  have h3 : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hst : LargeEvenStandardType 3 B x L := hH.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  have heq : labs = (⟨.twE6, 0, 1⟩ : LargeEvenLabel) :=
    eq_of_ggLabelIso_of_excTag (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (hRig ⟨.twE6, 0, 1⟩ labs _ hΛ hlabs hL hhass)
  have hs : LargeEvenSplit 3 (⟨.twE6, 0, 1⟩ : LargeEvenLabel) := heq ▸ hPs.1
  have hD4 : ¬ (labJ.tag = .D ∧ labJ.rank = 4) := fun h =>
    hnc (Or.inl (Or.inl ⟨h.1, h.2, rfl, h3⟩))
  refine ggTBJE6LeviL_of_cellFn hH fun hBs hSC hJX hyBs hJg hgX hcomp bX hbX1 hbXc hcardJ => ?_
  obtain ⟨-, -, -, hperf⟩ := GGConfig.data_L hH.1
  have hInn : GGInnerDiagOn Bs L := hH.2.2.1.1
  have hlabL : GGTableBTwE6ThreeLabel 3 (⟨.twE6, 0, 1⟩ : LargeEvenLabel) := by
    unfold GGTableBTwE6ThreeLabel
    exact ⟨rfl, rfl, h3⟩
  have hM : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L :=
    ggInnerDiagOnLab_of_hasLabel hRig hInn hΛ hL hlabL hs
  exact ggTBJTwE6Levi_threeOne_of_inst hOdd hNorm hRig hBs hSC hJX hyBs hJg hgX hcomp bX hbX1
    hbXc hcardJ hInn hperf hΛ hL (fun hN => hRL G 3 B Bs x L D J hH.1 hM hN) hΛJ hJlab hD4

theorem ggTBJTwE6LeviK_threeOne_of_inst
    (hOdd : GGTwE6ThreeOddInstOne) (hNorm : GGTwE6ThreeCompInvOne)
    (hRig : GGLabelRigidInput) (hRK : GGTwE6ThreeNbrRankInput) :
    GGTBJETypeLeviK .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ ¬ (p = 3 ∧ n = 1) := by
  intro G _ _ p B Bs x L D J y K hH hJK _ _ _ n hΛ hK _ labJ hΛJ hJlab _ hnc
  have hP : p = 3 ∧ n = 1 := by
    by_contra h
    exact hnc (Or.inr h)
  obtain ⟨hp3, hn1⟩ := hP
  subst hp3
  subst hn1
  have h3 : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hD4 : ¬ (labJ.tag = .D ∧ labJ.rank = 4) := fun h =>
    hnc (Or.inl (Or.inl ⟨h.1, h.2, rfl, h3⟩))
  refine ggTBJE6LeviK_of_cellFn hH hJK fun hBs hSC hJK' hxBs hJg hgX hcomp bX hbX1 hbXc hcardJ => ?_
  obtain ⟨-, -, -, hperf⟩ := hH.data_K
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hInn : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  have hbad : GGTwE6BadLabel 3 (⟨.twE6, 0, 1⟩ : LargeEvenLabel) := by
    unfold GGTwE6BadLabel
    exact ⟨rfl, rfl, h3⟩
  have hM : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs K :=
    ggInnerDiagOnLab_of_hasLabel hRig hInn hΛ hK hbad (largeEvenSplit_of_twE6BadLabel hbad)
  exact ggTBJTwE6Levi_threeOne_of_inst hOdd hNorm hRig hBs hSC hJK' hxBs hJg hgX hcomp bX hbX1
    hbXc hcardJ hInn hperf hΛ hK (fun hN => hRK G 3 B Bs x L D J hH.1 rfl y K hnb hM hN
      (ggTorusSelfCent_ggGamma hN hSC)) hΛJ hJlab hD4

end CFSG.StandardType

end
