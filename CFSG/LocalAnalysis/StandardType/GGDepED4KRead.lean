module

public import CFSG.LocalAnalysis.StandardType.GGDepED4ReadDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4L58RowDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4RowSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nRK_row_facts {p : ℕ} {labJ labX : LargeEvenLabel}
    (h : ggRowTwoNode p labJ labX) (hD : labJ.tag = .D) :
    p = 3 ∧ labJ.rank = 4 ∧ (labX.tag = .E6 ∨ labX.tag = .twE6) := by
  rcases h with ⟨hA, -, -, -⟩ | ⟨hA, -, -, -⟩ | ⟨hJ, hp, -, hX⟩ | ⟨hJ, hp, -, hX⟩
  · exact absurd (hA ▸ hD) (by decide)
  · exact absurd (hA ▸ hD) (by decide)
  · subst hX
    exact ⟨hp, by simpa using congrArg LargeEvenLabel.rank hJ, Or.inl rfl⟩
  · subst hX
    exact ⟨hp, by simpa using congrArg LargeEvenLabel.rank hJ, Or.inr rfl⟩

theorem ggDepED4_K
    (hRig : GGLabelRigidInput) (hJ : GGTBJInputR)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input)
    (hLE3 : GGResTwoNodeLE3SmallInput) (hIndep : GGResTwoNodeIndepInput)
    (hLoc : GGE6D4TwoNodeLocalInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    (hPZ : GGPZE6Input) (hLowK : GGDepED4LowCloseK) (h58 : GGDepED4L58RowInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hrow : GGResRowAt ggRowTwoNodeSmallJD p J K) (hyK : y ∉ K)
    (hLread : GGResRowAt ggRowTwoNode p J L → x ∉ L →
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hrowK0 : GGResRowAt ggRowTwoNodeSmallJD p J K := hrow
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hrowJD⟩ := hrow
  have hrowSmall : ggRowTwoNodeSmall p labJ labX := hrowJD.1
  have hrow2 : ggRowTwoNode p labJ labX := hrowJD.1.1
  have hJtagD : labJ.tag = .D := hrowJD.2
  have hrank : labJ.rank = 4 := (l05nRK_row_facts hrow2 hJtagD).2.1
  have htag : labX.tag = .E6 ∨ labX.tag = .twE6 := (l05nRK_row_facts hrow2 hJtagD).2.2
  have hp3 : p = 3 := (l05nRK_row_facts hrow2 hJtagD).1
  subst hp3
  have hLocK := hLoc G B Bs x L D J y K hH K y (Or.inr ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJl hXl
    hrow2 htag
  have hcard : Nat.card ↥Bs = 3 ^ 6 ∨ Nat.card ↥Bs = 3 ^ 7 := hLocK.1
  have hJcard : Nat.card ↥(Bs ⊓ J) = 3 ^ 4 := hLocK.2.1
  have hRG : GGReflGenerated 3 (ggAutomizer J Bs) := hLocK.2.2.1
  have hXK : GGResXDatumE6x 3 Bs K y := hLocK.2.2.2.1
  have hJ192 : Nat.card ↥(ggAutomizer J Bs) = 192 := hLocK.2.2.2.2.1
  have hKd : GGResTwoNodeSideDatum 3 Bs K J := hLocK.2.2.2.2.2
  have hTwo : GGResRowAt ggRowTwoNode 3 J L → GGResTwoNodeSideDatum 3 Bs L J := by
    intro h2
    obtain ⟨labJ', labL', hJΛ', hLΛ', hJl', hLl', hrowJD'⟩ :=
      ggDepED4_row_small_of_row hRig hrowK0 h2
    have hrow2' : ggRowTwoNode 3 labJ' labL' := hrowJD'.1.1
    have hJ'D : labJ'.tag = .D := hrowJD'.2
    exact (hLoc G B Bs x L D J y K hH L x (Or.inl ⟨rfl, rfl⟩) labJ' labL' hJΛ' hLΛ' hJl' hLl'
      hrow2' (l05nRK_row_facts hrow2' hJ'D).2.2).2.2.2.2.2
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
  rcases hshape with hLside | hL3 | ⟨hrowL, _hsideL⟩ | hweyl
  · have hA : GGDepED4Aligned 3 1 Bs K J L :=
      ggDepED4_align_one (by norm_num) hXK hKd hLside hJ192
    have hJcard' : Nat.card ↥(Bs ⊓ J) = 3 ^ labJ.rank := by
      rw [hrank]; exact hJcard
    have h58K : Nat.card ↥Bs = 3 ^ 6 → GGTWHLAt 3 Bs L x ∧
        (Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y → GGTWHLAt 3 Bs K y) :=
      fun h6 => (h58 G 3 1 B Bs x L D J y K hH rfl h6).2 hyK hA hrowK0
    exact ggDepED4_close_K hLowK hFix hFixK hPZ hH hyK rfl hcard hJΛ hXΛ hJl hXl hrowSmall
      htag hJcard' hRG (fun h6 => (h58K h6).2) (fun h6 => (h58K h6).1) hA
  · exact hLE3 G 3 B Bs x L D J y K hH hF hS hE
      (Or.inr ⟨⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hrowSmall⟩, hyK, hL3⟩)
  · by_cases hxL : x ∈ L
    · exact hIndep G 3 B Bs x L D J y K hH hF hS hE (Or.inl ⟨hrowL, hxL⟩)
    · exact hLread hrowL hxL
  · exact hweyl

end CFSG.StandardType

end
