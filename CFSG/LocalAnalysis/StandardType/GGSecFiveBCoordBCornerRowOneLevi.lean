module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerRowOne
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclic
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBQTwoSpSparse
import CFSG.LocalAnalysis.StandardType.GGTPNI1BC
import CFSG.LocalAnalysis.StandardType.GGTPNThmULabel
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseSpLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly GGQ2Frame

theorem GGSecFiveBCoordBLabel.corner_tag_rank {n p : ℕ} {lab : LargeEvenLabel}
    (h : GGSecFiveBCoordBLabel n p lab ∧ 5 ≤ n ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧
      p = 3) :
    (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = n - 1 ∧ lab.n = 1 := by
  obtain ⟨hl, -, ht, hn1, -⟩ := h
  rcases hl with ⟨-, hr, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨ht, hr, hn1⟩
  all_goals rcases ht with ht | ht <;> rw [ht] at h <;> exact absurd h (by decide)

private theorem corner_hasLabel_C_L {G : Type} [Group G] {Bs L : Subgroup G} {n : ℕ}
    (hM : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧ 5 ≤ n ∧
      (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ p = 3) 3 Bs L) :
    GGHasLabel ⟨.C, n - 1, 1⟩ (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨lab, hbody⟩ := largeEvenMarking_exists_hasLabel hM
  have hlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) := hbody.2.1
  obtain ⟨_R, _instR, _I, _F, _θ, hmark⟩ := hbody.2.2
  obtain ⟨ht, hr, hk1⟩ := GGSecFiveBCoordBLabel.corner_tag_rank hmark.1
  obtain ⟨t, r, k⟩ := lab
  obtain rfl : k = 1 := hk1
  subst hr
  rcases ht with rfl | rfl <;> exact hlab

private theorem corner_hasLabel_C_J {G : Type} [Group G] {Bs L J : Subgroup G} {n : ℕ}
    (hn : 5 ≤ n)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    {k : Fin (n - 1)} (hJ : J = (R.component (.zero (Finset.univ.erase k))).map L.subtype) :
    GGHasLabel ⟨.C, n - 2, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
  classical
  let A : Subgroup ↥L := R.component (.zero (Finset.univ.erase k))
  have hcard : (Finset.univ.erase k : Finset (Fin (n - 1))).card = n - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    omega
  have hne : n - 2 ≠ 2 := by omega
  have hc : (planeEntry .symplectic (n - 1)).admissible (.zero (Finset.univ.erase k)) := by
    refine ⟨by omega, ?_⟩
    simp only [PlaneRaw.admissible, hcard]
    omega
  obtain ⟨lab, hbody⟩ :=
    largeEvenMarking_exists_hasLabel (R.marked (.zero (Finset.univ.erase k)) hc)
  have hlab : GGHasLabel lab (↥A ⧸ Subgroup.center ↥A) := hbody.2.1
  obtain ⟨_R, _instR, _I, _F, _θ, hP⟩ := hbody.2.2
  have hlabel : (planeEntry .symplectic (n - 1)).label (.zero (Finset.univ.erase k)) =
      ⟨.C, n - 2, 1⟩ := by
    change PlaneRaw.label .symplectic (.zero (Finset.univ.erase k)) = ⟨.C, n - 2, 1⟩
    simp only [PlaneRaw.label, hcard, if_neg hne]
  have hlabC : GGHasLabel ⟨.C, n - 2, 1⟩ (↥A ⧸ Subgroup.center ↥A) := by
    rw [hP, hlabel] at hlab
    exact hlab
  have hquot : (↥A ⧸ Subgroup.center ↥A) ≃*
      (↥(A.map L.subtype) ⧸ Subgroup.center ↥(A.map L.subtype)) :=
    QuotientGroup.congr _ _ (Subgroup.equivMapOfInjective A L.subtype L.subtype_injective)
      (Subgroup.map_center_eq _)
  have h1 : GGHasLabel ⟨.C, n - 2, 1⟩
      (↥(A.map L.subtype) ⧸ Subgroup.center ↥(A.map L.subtype)) :=
    ggHasLabel_of_mulEquiv hquot hlabC
  subst hJ
  exact h1


theorem GGSecFiveRouteCfg.false_of_cornerRowOne {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hLB : GGLBalanceInput)
    (hCP : GGLabelCenterPCyclicInput)
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {n : ℕ}
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (hEta : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3)
    {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hM : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧ 5 ≤ n ∧
      (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ p = 3) 3 Bs L)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    {k : Fin (n - 1)} (hJ : J = (R.component (.zero (Finset.univ.erase k))).map L.subtype) :
    False := by
  obtain ⟨-, hrest⟩ := largeEvenMarking_exists' hM
  obtain ⟨lab, _R, _instR, _I, _F, _θ, _hΛ, hmark⟩ := hrest
  have hn5 : 5 ≤ n := hmark.1.2.1
  have hM' : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .B ∨ lab.tag = .C) ∧
      lab.rank = n - 1 ∧ lab.n = 1) 3 Bs L :=
    hM.mono_label (fun lab hl => GGSecFiveBCoordBLabel.corner_tag_rank hl)
  obtain ⟨hxL', hsplit, -⟩ :=
    GGConfig.exists_cornerRealization hR.1.1 hn5 eta hb hM'
  obtain ⟨K, hK𝒦, j, hj, -, hAK⟩ :=
    GGSecFiveRouteCfg.exists_bCoordinateBlock_of_cornerRowOne hX hTCJ hRig hTPn hA8 hraw hiso
      hFC hLB hR hn5 eta hEta hb hxL' hsplit R hJ
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK𝒦
  have hlabL := corner_hasLabel_C_L hM
  have hlabJ := corner_hasLabel_C_J hn5 R hJ
  have hlabK := ggNbr_hasLabel_C_of_le_bCoordinateBlock hTPn.toBCL hRig hCP hR.1.1
    hR.1.2.2.2.1 hR.1.2.2.1.1 (hR.1.2.2.1.2 y K hnb) hnb hn5 hlabL hlabJ eta hAK.le
  obtain ⟨eLK⟩ := nonempty_mulEquiv_of_ggHasLabel hlabL hlabK
  have hLab' : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n = 1 ∧ (lab.tag = .B ∨ lab.tag = .C))) 3 Bs L :=
    hM.mono_label (fun lab hl => ⟨hl.1, hl.2.2.2.1, hl.2.2.1⟩)
  exact GGSecFiveRouteCfg.false_of_qTwoSp_sparse hR hn5 e hP eta hj hEta hb hLab' hK𝒦 eLK hAK

end CFSG.StandardType

end
