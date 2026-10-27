module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenEightDelta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SecNatRealizes
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL2S5
public import CFSG.Quasithin.Background.RonanF615QTK
public import CFSG.GroupTheory.IrreducibleAbelianAction
public import CFSG.Quasithin.Background.C48AsmLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SuzukiNotClassical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

section Certified

theorem nat18_8_holds (D : Data G) (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    {V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D ⊥ V p L)
    (h1742 : S17.R17_42At D ⊥ V) (h18_4 : R18_4At D ⊥ V p L)
    (h5 : P18_6_5 D ⊥ V p L h) (hUL : UniqueMax D.M L)
    (hLb : barSub ⊥ V h.hyp125.isElemAbelian L ≠ ⊥) :
    Nat18_8 D V L h.hyp125.isElemAbelian := by
  intro hfixne
  have hV := h.hyp125.isElemAbelian
  set Lbar : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV L with hLbardef
  have hsplit := fixV_or_classicalEvenAltG2Der D h640 hFF h hUL hLb
  rcases hsplit with hfix | ⟨-, hCEAG, hJ⟩
  · exact absurd hfix hfixne
  have hJ' : ⁅barSub ⊥ V hV (F12.jOf D.T), Lbar⁆ ≠ ⊥ := by
    simpa only [hLbardef] using hJ
  let n : ℕ := S17.nOf L
  obtain ⟨hshape, hn2, -⟩ := shape18_6_of_ne h h1742 h18_4 h5.1
  have hn2' : 2 < n := hn2
  rcases hshape with hL2 | hSz
  ·
    have hsimple : IsSimpleGroup (Bar2 L) :=
      CFSG.Quasithin.C48.isSimpleGroup_psl_two
        (CFSG.Blueprint.LieModel.statedClassicalModel hL2 (by decide))
    obtain ⟨e⟩ := barSubBar2Equiv_of_isSimpleGroup h.hyp125 h.hL.1 hLb hsimple
    have hLbarL2 : UC22.IsL2 (barSub ⊥ V hV L) n := by
      exact CFSG.Blueprint.LieModel.of_mulEquiv e hL2
    have hmove : ∃ A : Subgroup (MulAut (Vtil ⊥ V hV)),
        IsFFStarOffender (Mbar D.M ⊥ V hV) A ∧ ⁅A, Lbar⁆ ≠ ⊥ := by
      by_contra hno
      push Not at hno
      have hle : ffJ (Mbar D.M ⊥ V hV) ≤ Subgroup.centralizer (Lbar : Set _) := by
        refine iSup₂_le fun A hA => ?_
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 (hno A hA)
      have hJle : barSub ⊥ V hV (F12.jOf D.T) ≤ Subgroup.centralizer (Lbar : Set _) :=
        (barSub_jOf_le_ffJ h.hyp125).trans hle
      refine hJ' ?_
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer
        (H₁ := barSub ⊥ V hV (F12.jOf D.T)) (H₂ := Lbar)).2 hJle
    obtain ⟨A, hAoff, hAL⟩ := hmove
    have hA_le : A ≤ Mbar D.M ⊥ V hV := hAoff.1
    letI : Module (ZMod 2) (Additive (Vtil ⊥ V hV)) :=
      CFSG.GroupTheory.elemModule 2 (s15_Infra_vtil_sq_eq_one ⊥ V hV)
    let ρ : Representation (ZMod 2) ↥(Mbar D.M ⊥ V hV) (Additive (Vtil ⊥ V hV)) :=
      (CFSG.RankThree.FFModules.autRep (Vtil ⊥ V hV)).comp
        (Mbar D.M ⊥ V hV).subtype
    have hρinj : Function.Injective ρ :=
      CFSG.RankThree.FFModules.autRep_injective.comp
        (Subgroup.subtype_injective (Mbar D.M ⊥ V hV))
    let L' : Subgroup ↥(Mbar D.M ⊥ V hV) := Lbar.subgroupOf (Mbar D.M ⊥ V hV)
    let A' : Subgroup ↥(Mbar D.M ⊥ V hV) := A.subgroupOf (Mbar D.M ⊥ V hV)
    have hAL' : ⁅L', A'⁆ ≠ ⊥ := by
      intro hbot
      apply hAL
      rw [Subgroup.commutator_comm]
      have hmap := CFSG.commutator_subgroupOf_map_eq (Mbar D.M ⊥ V hV) A Lbar hA_le
        (barSub_mono ⊥ V hV h.L_le_M)
      rw [hbot, Subgroup.map_bot] at hmap
      exact hmap.symm
    have hrep : CFSG.RankThree.FFModules.repMulAut
        (CFSG.RankThree.FFModules.autRep (Vtil ⊥ V hV)) =
        MonoidHom.id (MulAut (Multiplicative (Additive (Vtil ⊥ V hV)))) := by
      ext φ w
      rfl
    have hmapA : A'.map (CFSG.RankThree.FFModules.repMulAut ρ) = A := by
      have hcomp : CFSG.RankThree.FFModules.repMulAut ρ = (Mbar D.M ⊥ V hV).subtype := by
        rw [show CFSG.RankThree.FFModules.repMulAut ρ =
            (CFSG.RankThree.FFModules.repMulAut
              (CFSG.RankThree.FFModules.autRep (Vtil ⊥ V hV))).comp
              (Mbar D.M ⊥ V hV).subtype from rfl, hrep]
        exact MonoidHom.id_comp _
      rw [hcomp]
      exact Subgroup.map_subgroupOf_eq_of_le hA_le
    have hAcal : A' ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.Ext.calP ρ := by
      rw [CFSG.LocalAnalysis.UniquenessCase.UC22.K148.mem_calP_iff]
      have hiff := CFSG.RankThree.FFModules.isFFStarOffender_map_iff hρinj
        (A := A') (Y := Mbar D.M ⊥ V hV) (by rw [hmapA]; exact hA_le)
      rw [hmapA] at hiff
      exact hiff.1 hAoff
    have hcomp : IsComponentOf L' ⊤ := by
      have hc := barSub_mem_compBar_of_ne_bot h.hyp125 h.hL.1 hLb
      exact CFSG.Quasithin.RonanF615.isComponentOf_subgroupOf hc
    have hL2' : UC22.IsL2 ↥L' n :=
      CFSG.Blueprint.LieModel.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (barSub_mono ⊥ V hV h.L_le_M)).symm hLbarL2
    obtain ⟨B, hinv, hBA, -, -, -, -, hT, F, hFfield, hFfin, hFproj, hFdec, hFcard, α, hout⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.K148.exists_componentOffenderOutput
        hρinj hcomp (by omega) hL2' hAcal hAL'
    have hdich := CFSG.LocalAnalysis.UniquenessCase.UC22.K148.dichotomy_of_componentOffenderOutput
      hρinj hcomp hL2' hAcal hAL' hBA hinv hT hFcard hout
    rcases hdich with ⟨hnat, -⟩ | ⟨hn2', -, -⟩
    ·
      obtain ⟨K, hKfield, hKfin, hKcard, hreal⟩ :=
        natL2_realizes_autSub_commSub
          (ι := (Mbar D.M ⊥ V hV).subtype) hnat
      have hreal' : (FFModel.nat (StatedSL 2 K)).Realizes
          (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L)) ⊤
          (fixV (autSub (barSub ⊥ V hV L) (wTil ⊥ V hV L))) := by
        rwa [show L'.map (Mbar D.M ⊥ V hV).subtype = Lbar from
          Subgroup.map_subgroupOf_eq_of_le (barSub_mono ⊥ V hV h.L_le_M), hLbardef,
          show commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (barSub ⊥ V hV L) =
            wTil ⊥ V hV L from rfl] at hreal
      exact ⟨n, by omega, hLbarL2, K, hKfield, hKfin, hKcard, hreal'⟩
    · omega
  ·
    exact absurd hCEAG (not_classicalEvenAltG2Der_of_isSz hSz)

theorem delta18_8At_holds (D : Data G) (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (h1742 : S17.R17_42At D V₀ V) (h18_4 : R18_4At D V₀ V p L) :
    Delta18_8At D V₀ V p L h := by
  intro h5 h151 hUL hLb hV0
  subst hV0
  exact delta15_lt_of_p18_6_5_of_nat D h h151 hLb
    (nat18_8_holds D h640 hFF h h1742 h18_4 h5 hUL hLb)

theorem r18_8At_closed (D : Data G) (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (hSg : UC6S846.SigmaStd D) (h1217 : R1217 D) (h127 : R127 D)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h17_66_1 : S17.R17_66_1At D V₀ V) (h18_4 : R18_4At D V₀ V p L)
    (h15_13 : R15_13Small D) (h1742 : S17.R17_42At D V₀ V) :
    R18_8At D V₀ V p L h :=
  r18_8At D V₀ V p L h (delta18_8At_holds D h640 hFF h h1742 h18_4)
    hSg h1217 h127 h1669 h17_66_1 h18_4 h15_13

end Certified
