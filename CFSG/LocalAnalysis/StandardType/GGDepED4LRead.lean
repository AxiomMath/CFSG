module

public import CFSG.LocalAnalysis.StandardType.GGDepED4ReadDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4L58RowDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4RowSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nRL_row_D4 {p : ℕ} {labJ labX : LargeEvenLabel}
    (hrow : ggRowTwoNode p labJ labX) (htag : labJ.tag = .D) :
    labJ.rank = 4 ∧ p = 3 ∧ (labX.tag = .E6 ∨ labX.tag = .twE6) := by
  have hcases : (labJ = ⟨.D, 4, labJ.n⟩ ∧ p = 3 ∧ labX = ⟨.E6, 0, labJ.n⟩) ∨
      (labJ = ⟨.D, 4, labJ.n⟩ ∧ p = 3 ∧ labX = ⟨.twE6, 0, labJ.n⟩) := by
    rcases hrow with h | h | h | h
    · rw [h.1] at htag; exact absurd htag (by decide)
    · rw [h.1] at htag; exact absurd htag (by decide)
    · exact Or.inl ⟨h.1, h.2.1, h.2.2.2⟩
    · exact Or.inr ⟨h.1, h.2.1, h.2.2.2⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases hcases with ⟨hJeq, -⟩ | ⟨hJeq, -⟩
    · rw [hJeq]
    · rw [hJeq]
  · rcases hcases with ⟨-, hp, -⟩ | ⟨-, hp, -⟩ <;> exact hp
  · rcases hcases with ⟨-, -, hXeq⟩ | ⟨-, -, hXeq⟩
    · exact Or.inl (by rw [hXeq])
    · exact Or.inr (by rw [hXeq])

theorem ggDepED4_L
    (hRig : GGLabelRigidInput) (hJ : GGTBJInputR)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K))
    (h6c : GGResMaxRankInput) (h6d : GGResTrialityInput) (h6e : GGResTriD4TwE6Input)
    (h6f : GGResSevenInput) (h6g : GGResTwA2Input)
    (hLE3 : GGResTwoNodeLE3SmallInput) (hIndep : GGResTwoNodeIndepInput)
    (hLoc : GGE6D4TwoNodeLocalInput) (hZ : GGDepED4ZKInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hPZ : GGPZE6Input) (hLow : GGDepED4LowClose)
    (h58 : GGDepED4L58RowInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hrow : GGResRowAt ggRowTwoNodeSmallJD p J L) (hxL : x ∉ L) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hrowL : GGResRowAt ggRowTwoNodeSmallJD p J L := hrow
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hrowSmall, htagD⟩ := hrow
  have hrow2 : ggRowTwoNode p labJ labX := hrowSmall.1
  obtain ⟨hlabJrank, hp3, hlabXtag⟩ := l05nRL_row_D4 hrow2 htagD
  subst p
  have hrowSmallAtL : GGResRowAt ggRowTwoNodeSmall 3 J L :=
    ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hrowSmall⟩
  have hLocL := hLoc G B Bs x L D J y K hH L x (Or.inl ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJl hXl
    hrow2 hlabXtag
  obtain ⟨hcard, hJcard, hRG, hXL, hJ192, hLd⟩ := hLocL
  have hLocK : ∀ (h2 : GGResRowAt ggRowTwoNode 3 J K),
      GGResXDatumE6x 3 Bs K y ∧ GGResTwoNodeSideDatum 3 Bs K J := by
    intro h2
    obtain ⟨labJ2, labK2, hJΛ2, hKΛ2, hJl2, hKl2, hrowK2, htagD2⟩ :=
      ggDepED4_row_small_of_row hRig hrowL h2
    obtain ⟨-, -, hKtag⟩ := l05nRL_row_D4 hrowK2.1 htagD2
    have hloc := hLoc G B Bs x L D J y K hH K y (Or.inr ⟨rfl, rfl⟩) labJ2 labK2 hJΛ2 hKΛ2
      hJl2 hKl2 hrowK2.1 hKtag
    exact ⟨hloc.2.2.2.1, hloc.2.2.2.2.2⟩
  have hTwo : GGResRowAt ggRowTwoNode 3 J K → GGResTwoNodeSideDatum 3 Bs K J :=
    fun h2 => (hLocK h2).2
  have hShape : GGResSideDatum 3 Bs K J ∨ GGResLeviSideDatumLE3 3 Bs K J ∨
      (GGResRowAt ggRowTwoNode 3 J K ∧ GGResTwoNodeSideDatum 3 Bs K J) ∨
      GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
    rcases (hX G 3 B Bs x L D J y K hH).2 with hXK | hSK
    · rcases (hJ G 3 B Bs x L D J y K hH).2 hXK with hK | hK3 | hNK
      · exact Or.inl hK
      · exact Or.inr (Or.inl hK3)
      · rcases ggTWSmall_nonLevi_K hTwo h6c h6d h6e h6f h6g hH hF hS hE hNK with htwo | hweyl
        · exact Or.inr (Or.inr (Or.inl htwo))
        · exact Or.inr (Or.inr (Or.inr hweyl))
    · exact Or.inr (Or.inr (Or.inr (h6f G 3 B Bs x L D J y K hH hF hS hE (Or.inr hSK))))
  have hJcard' : Nat.card ↥(Bs ⊓ J) = 3 ^ labJ.rank := by
    rw [hlabJrank]; exact hJcard
  rcases hShape with hK1 | hK3 | htwo | hW
  · have hAligned : GGDepED4Aligned 3 1 Bs L J K :=
      ggDepED4_align_one (by norm_num) hXL hLd hK1 hJ192
    refine ggDepED4_L_of_aligned hLow hFix hFixK hPZ hH hxL (Or.inl rfl) rfl hcard hJΛ hXΛ hJl
      hXl hrowSmall hlabXtag hJcard' hRG ?_ ?_ hAligned
    · intro h6
      exact ((h58 G 3 1 B Bs x L D J y K hH rfl h6).1 hxL
        (hZ G B Bs x L D J y K hH labJ hJΛ hJl htagD hlabJrank h6 hK1) (Or.inl rfl)
        hAligned hrowL (fun h => absurd h (by norm_num))).1
    · intro h6
      exact ((h58 G 3 1 B Bs x L D J y K hH rfl h6).1 hxL
        (hZ G B Bs x L D J y K hH labJ hJΛ hJl htagD hlabJrank h6 hK1) (Or.inl rfl)
        hAligned hrowL (fun h => absurd h (by norm_num))).2
  · exact hLE3 G 3 B Bs x L D J y K hH hF hS hE (Or.inl ⟨hrowSmallAtL, hxL, hK3⟩)
  · obtain ⟨hrowK, hKd⟩ := htwo
    by_cases hyK : y ∈ K
    · exact hIndep G 3 B Bs x L D J y K hH hF hS hE (Or.inr ⟨hrowK, hyK⟩)
    · have hAligned : GGDepED4Aligned 3 2 Bs L J K :=
        ggDepED4_align_two (by norm_num) hXL (hLocK hrowK).1 hLd hKd hJ192
      refine ggDepED4_L_of_aligned hLow hFix hFixK hPZ hH hxL (Or.inr rfl) rfl hcard hJΛ hXΛ
        hJl hXl hrowSmall hlabXtag hJcard' hRG ?_ ?_ hAligned
      · intro h6
        exact ((h58 G 3 2 B Bs x L D J y K hH rfl h6).1 hxL hyK (Or.inr rfl) hAligned hrowL
          (fun _ => hrowK)).1
      · intro h6
        exact ((h58 G 3 2 B Bs x L D J y K hH rfl h6).1 hxL hyK (Or.inr rfl) hAligned hrowL
          (fun _ => hrowK)).2
  · exact hW

end CFSG.StandardType

end
