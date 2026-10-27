module

public import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
public import CFSG.LocalAnalysis.StandardType.GGTBJSpPlus
import CFSG.LocalAnalysis.StandardType.GGTBJSpModelTwo
public import CFSG.LocalAnalysis.StandardType.GGResHigherFieldI1
public import CFSG.LocalAnalysis.StandardType.GGResJOpenLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1BC
import CFSG.LocalAnalysis.StandardType.GGTCJHolds
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
import CFSG.LocalAnalysis.StandardType.GGTBE6

public section
namespace CFSG.StandardType
open CFSG CFSG.Assembly
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGResHyp.false_of_exact2_L_spSplit_geSix
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab =>
      (lab.tag = .B ∨ lab.tag = .C) ∧ 6 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hT : GGTBTorAll := ggTBTorAll_of_remaining trivial
  have hLift : GGTBTorLiftRows := ggTBTorLiftRows_holds
  have hSp : GGInnerDiagOnLabel ggTBJSpPlusLabel p Bs L :=
    hL.mono_label fun _ h => ⟨h.1, by omega, h.2.2⟩
  obtain ⟨m, F, _, _, _, hN, ψ, hm4, hpq, -, hTB⟩ :=
    exists_spPlus_model_of_marking hp hp2 hSp (fun R _ θ I hN hI r hLift hperf =>
      ggTorusTBGroup_of_L hH.1 hperf θ hN hI hLift)
  letI : NeZero m := ⟨by omega⟩
  have hEq : Bs = B := ggTBJ_sp_bstar_eq hp hp2 hH.1 L hN hpq ψ hTB
  have hI1 := hH.iOne_of_eq_bstar hEq.symm
  have hrow : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ)
      (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
      GGTBTorRowAt p lab r m N C M ∧ 6 ≤ r) p Bs L := by
    refine hL.mono_label fun lab h => ?_
    refine ⟨lab.rank - ggTorEnn p lab, ggTorMpm p lab, lab.rank,
      CartanMatrix.C lab.rank, CoxeterMatrix.B lab.rank,
      GGTBTorRowAt.c h.1 (dvd_mul_of_dvd_left h.2.2 _), ?_⟩
    simpa only [ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 h.2.2, Nat.sub_zero] using h.2.1
  obtain ⟨_, _, _, _, _, _, _, _, θ, _, _, hperf, -, -, hr6, -, hlift, -, -⟩ :=
    l05nPlQ_marking_with (ggTBTorWRows_of_all hT) hLift hp2 _ hrow
  have hm : 7 ≤ LargeEvenTwoLocalRank p G := by
    have := hH.succ_le_twoLocalRank_of_torusLift_L hperf θ hlift
    omega
  have hbc : GGInnerDiagOnLabel (fun _ lab => lab.tag = .B ∨ lab.tag = .C) p Bs L :=
    hL.mono_label fun _ h => h.1
  have hJ0 : GGInnerDiagOn Bs J := q1On_bc G p B Bs x L D J hH.1 hbc
  have hJ : GGInnerDiagOnLabel (fun _ _ => True) p Bs J :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩) hJ0
  have hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    intro b
    constructor
    · exact hH.fix_mem_centralizer_J_of_tcj_of_seven hT hLift TCJ.ggTCJKnown_holds
        ggLabelRigidInput_holds hm hJ b
    · intro hb
      have hJC : J ≤ Subgroup.centralizer ({(b : G)} : Set G) := by
        intro j hj
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        have hg' : g = (b : G) := by simpa using hg
        subst g
        exact (Subgroup.mem_centralizer_iff.mp hb j hj).symm
      exact ggResI_automizer_fix b.2 hJC
  have htyped := ggResExact2_typed_dichotomy_L_of_fixed hH hI1 hfix hD
  have hsing := GGResLeviDatumCard.singular_card htyped
  apply hH.false_of_singular_card_nonsingular_L hT hLift _ hsing
  refine hL.mono_label fun lab h => ⟨?_, ?_⟩
  · exact ⟨_, _, _, _, _, GGTBTorRowAt.c h.1 (dvd_mul_of_dvd_left h.2.2 _)⟩
  · rcases h.1 with ht | ht <;> simp [ggSingularBaseLabel, ht]

end CFSG.StandardType
