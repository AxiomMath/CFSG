module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3L4In
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3AStarDefs
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3D
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L2B
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3Norm
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13b
public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnHolds
public import CFSG.RankThree.PartTwo.Sec21.FF79GL33
public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnCenter
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAAssembly
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeSylow
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAFinal

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.S3

open CFSG CFSG.RankThree.PartTwo.Sec21 TLn
open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type} [Group G] [Finite G]

theorem exists_ctx4
    {b : G} {J : Subgroup G} (hyp : FF79Hyp 4 b J)
    (hnc : ¬ ConjInto b J) {B : Subgroup G} (hB : IsSylowOf 3 B (Cen b)) :
    ∃ u v r₁ r₂ w : G, Ctx b J B u v r₁ r₂ w := by
  have D := L13b.Data.of_hyp ff79KTypeLn_holds ff79KTypeLnNorm_holds (Or.inl rfl) hyp hB
  have S := setup14 ff79KTypeLn_holds ff79KCenterJ_holds (Or.inl rfl) hyp hB
  obtain ⟨u, v, r₁, r₂, w, -, -, hr₁, hr₂, hw, hnd, hP, hmono⟩ :=
    exists_normData4 S.hq hyp.model D.hB0syl
  obtain ⟨-, -, -, hcase⟩ := ff79_1_3_of ff79KTypeLn_holds ff79KTypeLnNorm_holds ff79KGL33_holds G 4 (Or.inl rfl) b J hyp B hB
  have horb : ∀ E : Subgroup G, E ≤ B → Nat.card E = 3 →
      ((∃ g ∈ Nor B, conjBy g (Subgroup.zpowers b) = E) ↔ ¬ E ≤ J) := by
    rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hnc
  refine ⟨u, v, r₁, r₂, w, D, hP, hnd, hr₁, hr₂, hw, ?_, horb⟩
  rw [← hP]; exact hmono

theorem exists_sec34Pre4
    (hs : IsSimpleGroup G) (hna : ∃ g h : G, g * h ≠ h * g)
    {b : G} {J : Subgroup G} (hyp : FF79Hyp 4 b J) (hnc : ¬ ConjInto b J) :
    ∃ B A P D : Subgroup G, H4.FF79Sec34Pre4 b J B A P D := by
  obtain ⟨B, hB⟩ := thmA_exists_sylow (Cen b)
  obtain ⟨u, v, r₁, r₂, w, C⟩ := exists_ctx4 hyp hnc hB
  obtain ⟨P, x, y, K⟩ := C.exists_PCtx
  have S := setup14 ff79KTypeLn_holds ff79KCenterJ_holds (Or.inl rfl) hyp hB
  have h3 : ∀ a ∈ Agrp x y u v, a ^ 3 = 1 := fun a ha => K.cube_one_of_simple hs hna ha
  have hr : localRank 3 G ≤ 3 := by
    rw [hyp.rank, pRank_cen_eq_three hB C.D.hE]
  have hoddB := K.odd_cenB h3 hr
  have hX := odd_X S hoddB
  have hsplit := (S.part3 hX ff79KAutCentP_holds).resolve_right (Nat.not_even_iff_odd.mpr hoddB)
  have hJ := J_eq_OUpp S hX hsplit.2
  obtain ⟨D, hD, hDJ, hD8, hDnab, hDz⟩ := K.exists_D hoddB hJ
  refine ⟨B, Agrp x y u v, P, D,
    { hyp := hyp
      sylB := hB
      elemB := C.D.hE
      elemB0 := C.D.hB0
      supB := C.D.hsup
      elemA := K.elemA h3
      B0A := by rw [C.B0]; exact K.R_le_A
      bA := K.b_nor
      commbA := by rw [C.B0]; exact K.comm_bA
      hJ := hJ
      cbSplit := hsplit
      oddX := hX
      oddCB := hoddB
      DJ := hDJ
      DA := hD.1.trans inf_le_right
      D8 := ⟨hD8, hDnab⟩
      sylD := hD
      hP := K.P_eq
      sylP := K.hP
      expP := K.exponent_P h3
      zA := fun z hz hz1 => (hDz z hz hz1).2.2 }⟩

end CFSG.RankThree.PartTwo.Sec21.FF79.S3
