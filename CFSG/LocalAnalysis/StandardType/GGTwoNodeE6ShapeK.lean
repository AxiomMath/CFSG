module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6ConsumerK
public import CFSG.LocalAnalysis.StandardType.GGDepED4RowSmall
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepLarge
public import CFSG.LocalAnalysis.StandardType.GGE6D4TwoNodeLocalInput
public import CFSG.LocalAnalysis.StandardType.GGTWSmallADefs
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma e6K_row_facts {p : ℕ} {labJ labX : LargeEvenLabel} (h : ggRowTwoNode p labJ labX)
    (htag : labX.tag = .E6 ∨ labX.tag = .twE6) : p = 3 ∧ labJ.tag = .D := by
  rcases h with ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨hJ, hp, -, -⟩ | ⟨hJ, hp, -, -⟩
  · exfalso
    subst hX
    simp at htag
  · exfalso
    subst hX
    simp at htag
  · exact ⟨hp, congrArg LargeEvenLabel.tag hJ⟩
  · exact ⟨hp, congrArg LargeEvenLabel.tag hJ⟩

private lemma e6K_row_of_D {p : ℕ} {labJ labX : LargeEvenLabel} (h : ggRowTwoNode p labJ labX)
    (hD : labJ.tag = .D) : labX.tag = .E6 ∨ labX.tag = .twE6 := by
  rcases h with ⟨hA, -, -, -⟩ | ⟨hA, -, -, -⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · exact absurd (hA ▸ hD) (by decide)
  · exact absurd (hA ▸ hD) (by decide)
  · subst hX
    exact Or.inl rfl
  · subst hX
    exact Or.inr rfl

private lemma e6K_rowJD {G : Type} [Group G] {p : ℕ} {J K : Subgroup G}
    (hrow : GGResRowAt ggRowTwoNodeSmallE6 p J K) : GGResRowAt ggRowTwoNodeSmallJD p J K := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hRowN, hrk⟩, htag⟩ := hrow
  have hJD : labJ.tag = .D := (e6K_row_facts hRowN htag).2
  refine ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨⟨hRowN, ?_⟩, hJD⟩⟩
  split_ifs at hrk <;> omega

private lemma e6K_y_mem {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) : y ∈ Bs := by
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  exact hH.1.2.1.1 (hH.1.2.2.1.1 hyD)

theorem ggE6K_shape
    (hRig : GGLabelRigidInput) (hJ : GGTBJInputR) (hX : GGResXDichotomyInput)
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input) (hLoc : GGE6D4TwoNodeLocalInput)
    (hOrbK : GGResCentBoundNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hrow : GGResRowAt ggRowTwoNodeSmallE6 p J K) :
    (GGReflGenerated p (ggAutomizer L Bs) ∧
      Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤ 3 ^ 7 * (6 * (3 - 1) * 51840)) ∨
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hrowK0 : GGResRowAt ggRowTwoNodeSmallJD p J K := e6K_rowJD hrow
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hRowN, -⟩, htag⟩ := hrow
  have hp3 : p = 3 := (e6K_row_facts hRowN htag).1
  have hy : y ∈ Bs := e6K_y_mem hH
  subst hp3
  obtain ⟨hcard, -, -, hdat, -, -⟩ := hLoc G B Bs x L D J y K hH K y (Or.inr ⟨rfl, rfl⟩) labJ labX
    hJΛ hXΛ hJl hXl hRowN htag
  have hBs : Nat.card ↥Bs ≤ 3 ^ 7 := by
    rcases hcard with h6 | h7
    · rw [h6]
      exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
    · rw [h7]
  obtain ⟨Λ, i1, i2, MK, -, -, -, -, -, -, -, -, e, hMK, -, -, -, -, -, ⟨fK, -⟩, -, -⟩ := hdat
  letI := i1; letI := i2
  have hAK : Nat.card ↥(ggAutomizer K Bs) = 51840 := ggE6K_card_AK e hMK fK
  have hbound := ggE6K_card_join_le hOrbK rfl hH hy hBs hAK
  have hTwo : GGResRowAt ggRowTwoNode 3 J L → GGResTwoNodeSideDatum 3 Bs L J := by
    intro h2
    obtain ⟨labJ', labL', hJΛ', hLΛ', hJl', hLl', hrowJD'⟩ :=
      ggDepED4_row_small_of_row hRig hrowK0 h2
    have hrow2' : ggRowTwoNode 3 labJ' labL' := hrowJD'.1.1
    have hJ'D : labJ'.tag = .D := hrowJD'.2
    exact (hLoc G B Bs x L D J y K hH L x (Or.inl ⟨rfl, rfl⟩) labJ' labL' hJΛ' hLΛ' hJl' hLl'
      hrow2' (e6K_row_of_D hrow2' hJ'D)).2.2.2.2.2
  have hshape : GGResSideDatum 3 Bs L J ∨ GGResLeviSideDatumLE3 3 Bs L J ∨
      (GGResRowAt ggRowTwoNode 3 J L ∧ GGResTwoNodeSideDatum 3 Bs L J) ∨
      GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
    rcases (hX G 3 B Bs x L D J y K hH).1 with hXL | hSL
    · rcases (hJ G 3 B Bs x L D J y K hH).1 hXL with hL | hL3 | hNL
      · exact Or.inl hL
      · exact Or.inr (Or.inl hL3)
      · rcases ggTWSmall_nonLevi_L hTwo h6c h6d h6e h6f h6g hH hF hS hE hNL with htwo | hweyl
        · exact Or.inr (Or.inr (Or.inl htwo))
        · exact Or.inr (Or.inr (Or.inr hweyl))
    · exact Or.inr (Or.inr (Or.inr (h6f G 3 B Bs x L D J y K hH hF hS hE (Or.inl hSL))))
  rcases hshape with hLside | hL3 | ⟨-, hside⟩ | hweyl
  · exact Or.inl ⟨l6a_reflGen_of_side (Or.inl hLside), hbound⟩
  · exact Or.inl ⟨l6a_reflGen_of_side (Or.inr (Or.inr hL3)), hbound⟩
  · exact Or.inl ⟨l6a_reflGen_of_side (Or.inr (Or.inl hside)), hbound⟩
  · exact Or.inr hweyl

theorem ggResTwoNodeIndepE6K
    (hAll : LR6E6All) (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hLoc : GGE6D4TwoNodeLocalInput) (hRig : GGLabelRigidInput)
    (hJ : GGTBJInputR) (hX : GGResXDichotomyInput) (h6c : GGResMaxRankInput)
    (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input) (h6f : GGResSevenInput)
    (h6g : GGResTwA2Input) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hrow : GGResRowAt ggRowTwoNodeSmallE6 p J K) (hyK : y ∈ K) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  rcases ggE6K_shape hRig hJ hX h6c h6d h6e h6f h6g hLoc hOrbK hH hF hS hE hrow with
    ⟨hLrefl, hbound⟩ | hweyl
  · obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hRowN, -⟩, htag⟩ := hrow
    have hp3 : p = 3 := (e6K_row_facts hRowN htag).1
    subst hp3
    obtain ⟨hcard, -, -, hdat, -, -⟩ := hLoc G B Bs x L D J y K hH K y (Or.inr ⟨rfl, rfl⟩) labJ
      labX hJΛ hXΛ hJl hXl hRowN htag
    have hBs : Nat.card ↥Bs ≤ 3 ^ 7 := by
      rcases hcard with h6 | h7
      · rw [h6]
        exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
      · rw [h7]
    obtain ⟨Λ, i1, i2, MK, CK, V, i3, i4, ι, φ, h, α, e, hMK, -, hCK, hφ, -, hpair, -, hAK,
      hind⟩ := hdat
    letI := i1; letI := i2; letI := i3; letI := i4
    exact ggTwoNodeIndepAtK_e6 hAll hFix hFixK rfl hH hBs hLrefl hbound e hMK hCK hφ hpair
      hAK (hind hyK)
  · exact hweyl

end CFSG.StandardType

end
