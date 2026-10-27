module

public import CFSG.LocalAnalysis.StandardType.GGF4LabelPieces
public import CFSG.LocalAnalysis.StandardType.GGF4SmallBook
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
import CFSG.LocalAnalysis.StandardType.GGTBXDatumOfTor
public import CFSG.LocalAnalysis.StandardType.GGTBE6
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
public import CFSG.LocalAnalysis.StandardType.GGF4H1Rows
import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGF4H1Coverage

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggF4H1_original_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hcard : Nat.card Bs = p ^ 4) :
    GGInnerDiagOnLabel LargeEvenSplit p Bs L := by
  have hB : B = Bs := ggF4Small_eq_Bs hcfg hcard
  have hmk : GGInnerDiagOnLab (fun _ _ => True) p B L :=
    ggInnerDiagOnLab_of_cover (fun _ _ _ _ => trivial) hcfg.1
  rw [hB] at hmk
  exact largeEvenMarking_mono
    (fun _ _ _ _ _ _ h => ⟨h.2.1, h.2.2⟩) hmk

theorem ggF4H1_row_at_L (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hM : GGInnerDiagOnLabel GGTBTorCov p Bs L)
    (hA3 : GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs)) :
    ∃ (lab : LargeEvenLabel) (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)),
      LargeEvenInLambda2 lab ∧ GGHasLabel lab (L ⧸ Subgroup.center L) ∧
        GGTBTorRowAt p lab r m N C M ∧ Nat.card M.Group = 24 := by
  have hp : p.Prime := hcfg.tableB_facts.1
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨lab, r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab, hrow, -, hBsI, hlift,
    hTorW, hHas⟩ := l05nPlQ_marking_with hW hLift hp2 (fun _ _ _ _ _ => True) (by
      refine largeEvenMarking_mono ?_ hM
      intro lab R _ I F θ h
      obtain ⟨r, m, N, C, M, hrow⟩ := h.1
      exact ⟨⟨r, m, N, C, M, hrow, trivial⟩, h.2⟩)
  obtain ⟨w, hw⟩ := hTorW L (ggQuotHom θ) (ggGamma L hN).range
    (ggTorusTBGroup_of_L hcfg hperf θ hN hBsI hlift)
  obtain ⟨hm, hpm, -, -⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  obtain ⟨hnk, -⟩ := ggTD_core hm hpm hcfg.tableB_facts.2.1 hcfg.2.1.2.2.2 hN w hw
  obtain ⟨e, -⟩ := ggTD_weyl hN hw hp2 hcfg.tableB_facts.2.1 hnk
  refine ⟨lab, r, m, N, C, M, hlab, hHas, hrow, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact ggF4Small_card_A3 hA3

section

theorem ggF4H1_toral_label
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hM : GGInnerDiagOnLabel GGTBTorCov p Bs L)
    (hA3 : GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs)) :
    ∃ f : ℕ, 1 ≤ f ∧
      ((p ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.A, 3, f⟩ (L ⧸ Subgroup.center L)) ∨
       (p ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L))) := by
  obtain ⟨lab, r, m, N, C, M, hlab, hHas, hrow, h24⟩ :=
    ggF4H1_row_at_L (ggTBTorWRows_of_all (ggTBTorAll_of_remaining trivial))
      ggTBTorLiftRows_holds hcfg hM hA3
  have hmeta := ggF4H1_row_metadata hlab hrow h24
  obtain ⟨t, l, f⟩ := lab
  rcases hmeta with ⟨ht, hr, hd⟩ | ⟨ht, hr, hd⟩ | ⟨ht, hr, hd⟩ | ⟨ht, hr, hd⟩
  · dsimp only at ht hr hd
    subst ht hr
    exact ⟨f, hlab.1, Or.inl ⟨hd, hHas⟩⟩
  · dsimp only at ht hr hd
    subst ht hr
    exact ⟨f, hlab.1, Or.inr ⟨hd, hHas⟩⟩
  · dsimp only at ht hr hd
    subst ht hr
    exact ⟨f, hlab.1, Or.inl ⟨hd, ggHasLabel_D3_iff_A3.mp hHas⟩⟩
  · dsimp only at ht hr hd
    subst ht hr
    change GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L) at hHas
    exact ⟨f, hlab.1, Or.inr ⟨hd, hHas⟩⟩

theorem ggF4H1_label_of_route (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {ks : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J ks) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs ks)} (hP : GGCoxeterPres p (ggAutomizerJoin L Bs ks) M e)
    (hF : GGIsWeylMatrixF4 M) (hA3 : GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs)) :
    ∃ f : ℕ, 1 ≤ f ∧
      ((p ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.A, 3, f⟩ (L ⧸ Subgroup.center L)) ∨
       (p ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L))) := by
  have hW4 := ggF4Small_weylOfType_F4 e hP hF
  have hne := ggF4Small_ks_nonempty hW4 hA3
  have hcard := ggF4Small_card_Bs hTBF hWI hR hW4 hne
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have hmk := ggF4H1_original_marking hcfg hcard
  rcases ggInnerDiagOnLabel_split (T := GGTBTorCov) hmk with hres | htor
  · exact (ggF4H1_no_residual_label hcfg hR.1.2.2.2.1 hcard hres
      (ggF4Small_card_A3 hA3)).elim
  · exact ggF4H1_toral_label hcfg htor hA3

theorem ggF4LabelH1_holds (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGF4LabelH1 := by
  intro G _ _ p B Bs x L D J ks hsmall
  obtain ⟨hR, -, ⟨ι, M, e, hP, hF⟩, hA3, -⟩ := hsmall
  exact ggF4H1_label_of_route hTBF hWI hR hP hF hA3

end

end CFSG.StandardType

end
