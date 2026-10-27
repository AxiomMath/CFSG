module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08Ce6LE3
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowTwoClose
public import CFSG.LocalAnalysis.StandardType.GGE6D4TwoNodeLocalInput

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2s08_ce6_rowD4 {p : ℕ} {labJ labX : LargeEvenLabel}
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

theorem ggDepED4_false_LE3_L (hcells : GGDepED4LowCells) (hLoc : GGE6D4TwoNodeLocalInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hPZ : GGPZE6Input) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrowL : GGResRowAt ggRowTwoNodeSmallJD p J L)
    (hxL : x ∉ L) (hK3 : GGResLeviSideDatumLE3 p Bs K J) (h7 : Nat.card ↥Bs ≠ 3 ^ 7) : False := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hrowSmall, htagD⟩ := hrowL
  have hrow2 : ggRowTwoNode p labJ labX := hrowSmall.1
  obtain ⟨hrank, hp3, hXtag⟩ := ggQ2s08_ce6_rowD4 hrow2 htagD
  subst hp3
  have hy : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  have hy1 : y ≠ 1 := ggRC_y_ne_one hH
  obtain ⟨hcardL, hJcard, hRG, hXL, hJ192, hLd⟩ := hLoc G B Bs x L D J y K hH L x
    (Or.inl ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJl hXl hrow2 hXtag
  have h6 : Nat.card ↥Bs = 3 ^ 6 := hcardL.resolve_right h7
  have hJcard' : Nat.card ↥(Bs ⊓ J) = 3 ^ labJ.rank := by rw [hrank]; exact hJcard
  exact ggDepED4_false_two_L hcells hFix hFixK hPZ hH hxL rfl (Or.inl h6) hJΛ hXΛ hJl hXl
    hrowSmall hXtag hJcard' hRG
    (ggQ2s08_ce6_aligned_of_LE3 hy hKy hy1 h6 hXL.core hLd hJ192 hK3)

theorem ggDepED4_false_LE3_K (hcells : GGDepED4LowCells) (hLoc : GGE6D4TwoNodeLocalInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) (hPZ : GGPZE6Input) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrowK : GGResRowAt ggRowTwoNodeSmallJD p J K)
    (hyK : y ∉ K) (hL3 : GGResLeviSideDatumLE3 p Bs L J) (h7 : Nat.card ↥Bs ≠ 3 ^ 7) : False := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hrowSmall, htagD⟩ := hrowK
  have hrow2 : ggRowTwoNode p labJ labX := hrowSmall.1
  obtain ⟨hrank, hp3, hXtag⟩ := ggQ2s08_ce6_rowD4 hrow2 htagD
  subst hp3
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hx1 : x ≠ 1 := ggTK_x_ne_one hH
  obtain ⟨hcardK, hJcard, hRG, hXK, hJ192, hKd⟩ := hLoc G B Bs x L D J y K hH K y
    (Or.inr ⟨rfl, rfl⟩) labJ labX hJΛ hXΛ hJl hXl hrow2 hXtag
  have h6 : Nat.card ↥Bs = 3 ^ 6 := hcardK.resolve_right h7
  have hJcard' : Nat.card ↥(Bs ⊓ J) = 3 ^ labJ.rank := by rw [hrank]; exact hJcard
  exact ggDepED4_false_two_K hcells hFix hFixK hPZ hH hyK rfl h6 hJΛ hXΛ hJl hXl hrowSmall hXtag
    hJcard' hRG (ggQ2s08_ce6_aligned_of_LE3 hx hLx hx1 h6 hXK.core hKd hJ192 hL3)

end CFSG.StandardType

end
