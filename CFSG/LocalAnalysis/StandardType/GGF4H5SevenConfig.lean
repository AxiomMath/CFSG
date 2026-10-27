module

public import CFSG.LocalAnalysis.StandardType.GGF4LabelPieces
public import CFSG.LocalAnalysis.StandardType.GGFFSLSylow
public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveProofSL
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.RankThree.PartTwo.KFacts.K71Item119
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Subgroup
open scoped MatrixGroups

section Certificates


theorem ggF4H5Seven_premises {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {ks : Finset (Subgroup G)} {K : Subgroup G}
    (hres : GGF4SmallRes p B Bs x L D J ks) (hK : K ∈ ks) :
    p.Prime ∧ p ≠ 2 ∧ IsElemAbelian p Bs ∧
      (∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) ∧
      GGNoTransvection p Bs ∧ commutator K = ⊤ ∧
      Bs ≤ Subgroup.normalizer (K : Set G) ∧
      (∃ y : G, GGNbr p B x D J y K) ∧ GGInnerDiagOn Bs K := by
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  have hNT : GGNoTransvection p Bs := hres.1.1.2.2.2.1
  obtain ⟨y, hnb⟩ := hres.1.2.2.2.1.2 K hK
  have hInn : GGInnerDiagOn Bs K := hres.1.1.2.2.1.2 y K hnb
  exact ⟨hp, hp2, hBs, hSC, hNT, hInn.1, hInn.le_normalizer, ⟨y, hnb⟩, hInn⟩

end Certificates

theorem ggHasLabel_A6_two_equiv_SL7 {R : Type} [Group R]
    (h : GGHasLabel (⟨.A, 6, 1⟩ : LargeEvenLabel) R) :
    Nonempty (R ≃* SL(7, ZMod 2)) := by
  classical
  dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeLinear] at h
  obtain ⟨Kf, hf, hfin, hcard, ⟨e⟩⟩ := h
  letI := hf
  letI := hfin
  have hcard2 : Nat.card Kf = 2 := by simpa using hcard
  haveI : Fintype Kf := Fintype.ofFinite Kf
  have hcardZ : Fintype.card Kf = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard2]
    simp [Nat.card_zmod]
  let eF : Kf ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcardZ
  have hunits : Nat.card Kfˣ = 1 := by rw [Nat.card_units, hcard2]
  haveI : Subsingleton Kfˣ := Finite.card_le_one_iff_subsingleton.mp (by rw [hunits])
  have hscal : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 7 Kf = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    rw [Subgroup.mem_bot]
    obtain ⟨c, -, hA'⟩ :=
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_scalars
        (n := 7) (K := Kf)).mp hA
    have hc : (c : Kf) = 1 := by
      have hc1 : c = 1 := Subsingleton.elim c 1
      rw [hc1]
      rfl
    apply Subtype.ext
    rw [hA', hc]
    simp
  let slPSL : LargeEvenProj (LargeEvenSLGroup (Fin 7) Kf) ≃* SL(7, Kf) :=
    (QuotientGroup.congr
        (G' := (LargeEvenScalars (Fin 7) Kf).subgroupOf (LargeEvenSLGroup (Fin 7) Kf))
        (H' := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 7 Kf)
        (TypeA.slKerEquiv 7 Kf)
        (TypeA.map_scalars_slKerEquiv (d := 7) (K := Kf))).trans
      ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot)
  exact ⟨e.trans (slPSL.trans (CFSG.RankThree.PartTwo.KFacts.slCongrOfRingEquiv 7 eF))⟩

noncomputable def ggF4H5Seven_marking {G : Type} [Group G] {K : Subgroup G}
    (h : GGHasLabel (⟨.A, 6, 1⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K)) :
    K ⧸ Subgroup.center K ≃* SL(7, ZMod 2) :=
  Classical.choice (ggHasLabel_A6_two_equiv_SL7 h)

theorem ggF4H5Seven_image_inner {G : Type} [Group G] {p : ℕ} {Bs K : Subgroup G}
    (hp3 : p = 3) (hBs : IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (θ : K ⧸ Subgroup.center K ≃* SL(7, ZMod 2)) :
    ∀ (b : G) (hb : b ∈ Bs),
      ggLAut K θ ⟨b, hN hb⟩ ∈
        Set.range (MulAut.conj : SL(7, ZMod 2) →* MulAut (SL(7, ZMod 2))) := by
  subst hp3
  intro b hb
  have hb3 : b ^ 3 = 1 := hBs.2 b hb
  have h3 : (⟨b, hN hb⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using hb3)
  have hφ3 : ggLAut K θ ⟨b, hN hb⟩ ^ 3 = 1 := by
    have h := congrArg (ggLAut K θ) h3
    simpa only [map_pow, map_one] using h
  obtain ⟨k, hk⟩ := GGFF.inner_odd_SL (n := 7) (by norm_num) (ggLAut K θ ⟨b, hN hb⟩)
    3 (by norm_num) hφ3
  exact ⟨k, hk.symm⟩

noncomputable def ggSL7ToPSL7 :
    SL(7, ZMod 2) ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 7 (ZMod 2) :=
  let hZ : Subgroup.center (SL(7, ZMod 2)) = ⊥ :=
    FieldFiveSL.center_SL_eq_bot_of_card_two (K := ZMod 2) (m := 6) (by simp [Nat.card_zmod])
  let q : Matrix.ProjectiveSpecialLinearGroup (Fin 7) (ZMod 2) ≃* SL(7, ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  q.symm.trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
      7 (ZMod 2))

end CFSG.StandardType

end
