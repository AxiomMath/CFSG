module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08Ce6Adapt
public import CFSG.LocalAnalysis.StandardType.GGQ2S08Ce6Shape
public import CFSG.LocalAnalysis.StandardType.GGQ2S08Ce6LE3
public import CFSG.LocalAnalysis.StandardType.GGQ2S08Ce6Six
public import CFSG.LocalAnalysis.StandardType.GGDepED4LE3Close
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowTwoClose
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowClose
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowCells
public import CFSG.LocalAnalysis.StandardType.GGDepED4L58RowDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4ReadDefs
public import CFSG.LocalAnalysis.StandardType.GGDepELLowCheck2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure GGQ2S08Ce6In : Prop where
  hRig : GGLabelRigidInput
  hJ : GGTBJInputR
  hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K)
  hLoc : GGE6D4TwoNodeLocalInput
  hZ : GGDepED4ZKInput
  hFix : GGTBFixInput
  hFixK : GGTBFixNbrInput
  hPZ : GGPZE6Input
  hD : GGTBTorD
  hLift : GGTBTorLiftRows
  hQ1 : GGBstarInnerDiagJInput
  h58 : GGDepED4L58RowInput

theorem ggQ2s08_ce6_L (hIn : GGQ2S08Ce6In) {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hI1 : GGQTwoI1 Bs D J)
    (hrowL : GGResRowAt ggRowTwoNodeSmallJD 3 J L) (hxL : x ∉ L) : False := by
  have hcells := ggDepED4LowCells_holds
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hrowL0 := hrowL
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hrowSmall, htagD⟩ := hrowL
  have hrow2 : ggRowTwoNode 3 labJ labX := hrowSmall.1
  obtain ⟨hrank, -, hXtag⟩ := ggQ2s08_ce6_rowD4 hrow2 htagD
  obtain ⟨hcardL, hJcard, hRG, hXL, hJ192, hLd⟩ := hIn.hLoc G B Bs x L D J y K hH L x
    (Or.inl ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJl hXl hrow2 hXtag
  have hle6 := ggQ2s08_ce6_card_le_six hIn.hRig hIn.hD hIn.hLift hIn.hQ1 hH hI1 hJΛ hJl hrow2 hXtag
  have h6 : Nat.card ↥Bs = 3 ^ 6 := by
    rcases hcardL with h | h
    · exact h
    · rw [h] at hle6; norm_num at hle6
  have hJcard' : Nat.card ↥(Bs ⊓ J) = 3 ^ labJ.rank := by rw [hrank]; exact hJcard
  rcases ggQ2s08_ce6_shape hIn.hRig hrowL0 (hIn.hX G 3 B Bs x L D J y K hH).2
      (hIn.hJ G 3 B Bs x L D J y K hH).2 with hK1 | hK3 | hKrow
  · have hA : GGDepED4Aligned 3 1 Bs L J K := ggDepED4_align_one hp2 hXL hLd hK1 hJ192
    have hyK : y ∉ K := hIn.hZ G B Bs x L D J y K hH labJ hJΛ hJl htagD hrank h6 hK1
    have h58 := (hIn.h58 G 3 1 B Bs x L D J y K hH rfl h6).1 hxL hyK (Or.inl rfl) hA hrowL0
      (fun h => absurd h (by norm_num))
    exact ggDepED4LowClose_of_cells hcells hIn.hFix hIn.hFixK hIn.hPZ G 3 1 B Bs x L D J y K hH
      hxL rfl (Or.inl rfl) h6 labJ labX hJΛ hXΛ hJl hXl hrowSmall hXtag hJcard' hRG h58.1 h58.2 hA
  · exact ggDepED4_false_LE3_L hcells hIn.hLoc hIn.hFix hIn.hFixK hIn.hPZ hH hrowL0 hxL hK3
      (by rw [h6]; norm_num)
  · obtain ⟨labJ2, labK2, hJΛ2, hKΛ2, hJl2, hKl2, hrowK2⟩ :=
      ggDepED4_row_small_of_row hIn.hRig hrowL0 hKrow
    obtain ⟨-, -, hKtag⟩ := ggQ2s08_ce6_rowD4 hrowK2.1.1 hrowK2.2
    obtain ⟨-, -, -, hXK, -, hKd⟩ := hIn.hLoc G B Bs x L D J y K hH K y (Or.inr ⟨rfl, rfl⟩)
      labJ2 labK2 hJΛ2 hKΛ2 hJl2 hKl2 hrowK2.1.1 hKtag
    exact ggDepED4_false_two_L hcells hIn.hFix hIn.hFixK hIn.hPZ hH hxL rfl (Or.inl h6) hJΛ hXΛ
      hJl hXl hrowSmall hXtag hJcard' hRG (ggDepED4_align_two hp2 hXL hXK hLd hKd hJ192)

theorem ggQ2s08_ce6_K (hIn : GGQ2S08Ce6In) {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hI1 : GGQTwoI1 Bs D J)
    (hrowK : GGResRowAt ggRowTwoNodeSmallJD 3 J K) (hyK : y ∉ K) : False := by
  have hcells := ggDepED4LowCells_holds
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hrowK0 := hrowK
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hrowSmall, htagD⟩ := hrowK
  have hrow2 : ggRowTwoNode 3 labJ labX := hrowSmall.1
  obtain ⟨hrank, -, hXtag⟩ := ggQ2s08_ce6_rowD4 hrow2 htagD
  obtain ⟨hcardK, hJcard, hRG, hXK, hJ192, hKd⟩ := hIn.hLoc G B Bs x L D J y K hH K y
    (Or.inr ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJl hXl hrow2 hXtag
  have hle6 := ggQ2s08_ce6_card_le_six hIn.hRig hIn.hD hIn.hLift hIn.hQ1 hH hI1 hJΛ hJl hrow2 hXtag
  have h6 : Nat.card ↥Bs = 3 ^ 6 := by
    rcases hcardK with h | h
    · exact h
    · rw [h] at hle6; norm_num at hle6
  have hJcard' : Nat.card ↥(Bs ⊓ J) = 3 ^ labJ.rank := by rw [hrank]; exact hJcard
  rcases ggQ2s08_ce6_shape hIn.hRig hrowK0 (hIn.hX G 3 B Bs x L D J y K hH).1
      (hIn.hJ G 3 B Bs x L D J y K hH).1 with hL1 | hL3 | hLrow
  · have hA : GGDepED4Aligned 3 1 Bs K J L := ggDepED4_align_one hp2 hXK hKd hL1 hJ192
    have h58 := (hIn.h58 G 3 1 B Bs x L D J y K hH rfl h6).2 hyK hA hrowK0
    exact ggDepED4LowCloseK_of_cells hcells hIn.hFix hIn.hFixK hIn.hPZ G 3 B Bs x L D J y K hH
      hyK rfl h6 labJ labX hJΛ hXΛ hJl hXl hrowSmall hXtag hJcard' hRG h58.2 h58.1 hA
  · exact ggDepED4_false_LE3_K hcells hIn.hLoc hIn.hFix hIn.hFixK hIn.hPZ hH hrowK0 hyK hL3
      (by rw [h6]; norm_num)
  · obtain ⟨labJ2, labL2, hJΛ2, hLΛ2, hJl2, hLl2, hrowL2⟩ :=
      ggDepED4_row_small_of_row hIn.hRig hrowK0 hLrow
    obtain ⟨-, -, hLtag⟩ := ggQ2s08_ce6_rowD4 hrowL2.1.1 hrowL2.2
    obtain ⟨-, -, -, hXL, -, hLd⟩ := hIn.hLoc G B Bs x L D J y K hH L x (Or.inl ⟨rfl, rfl⟩)
      labJ2 labL2 hJΛ2 hLΛ2 hJl2 hLl2 hrowL2.1.1 hLtag
    exact ggDepED4_false_two_K hcells hIn.hFix hIn.hFixK hIn.hPZ hH hyK rfl h6 hJΛ hXΛ hJl hXl
      hrowSmall hXtag hJcard' hRG (ggDepED4_align_two hp2 hXK hXL hKd hLd hJ192)

theorem ggQ2s08_ce6_holds (hIn : GGQ2S08Ce6In)
    (hRGK : ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G}
      {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J → ∀ {y : G} {K : Subgroup G},
      GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs)) :
    GGQ2S08NoNbrCell GGQ2S08PosTwE6 := by
  intro G _ _ p _ hp B Bs x L D J hS hI1 y K hnb hrow
  subst hp
  have hH := ggQ2s08_ce6_resHyp hS hnb (hRGK hS hnb)
  rcases hrow with ⟨h, hxL⟩ | ⟨h, hyK⟩
  · exact ggQ2s08_ce6_L hIn hH hI1 (ggQ2s08_ce6_rowAt h).2 hxL
  · exact ggQ2s08_ce6_K hIn hH hI1 (ggQ2s08_ce6_rowAt h).2 hyK

end CFSG.StandardType

end
