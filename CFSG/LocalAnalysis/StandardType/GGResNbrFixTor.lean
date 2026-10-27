module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRankDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassicalLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmallLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBMain
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGResSevenNbr
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import Certificates.Certificate1953
public import Certificates.Certificate1954
import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrConj

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {y : G} {K : Subgroup G}

theorem GGResHyp.fix_mem_centralizer_of_tbTor (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hH : GGResHyp p B Bs x L D J y K) (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K) (b : ↥Bs)
    (hb : ∀ φ ∈ ggAutomizer K Bs, φ b = b) : (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  have hp : p.Prime := hH.1.tableB_facts.1
  have : Fact p.Prime := ⟨hp⟩
  have hW : GGTBTorWRows := ggTBTorWRows_of_all hT
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨m, N, C, M, hN, hm, hpm, -, -, hTor⟩ := l05nPlP4_core_K hW hLift hH hK
  exact ggTD_fix_mem_centralizer hm hpm hBs hS hN hTor b hb

theorem GGResHyp.fix_mem_centralizer_three_of_F4
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel GGF4ThreeLabel 3 Bs K) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  classical
  have hR : ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma K hN).range := fun hN =>
    ggF4Three_rank_of_marking
      (ggF4ThreeSCTransvInput_of_cube ggF4ThreeSCCubeInput_holds)
      hH.1 hH.2.2.2.1 hK hN
  have hcard := card_eq_of_F4Three_marking hH.1 hK hR
  have hMark : LargeEvenMarking K (fun lab _ _ I _ θ =>
      lab.tag = .F4 ∧ Bs ≤ Subgroup.normalizer (K : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
        (fun l l' : K => (l' : G) = b⁻¹*l*b) φ) :=
    largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨hP.1.1,hP.2⟩) hK
  exact (ggF4NbrAutReflKGInput_holds G 3 Bs K
    Nat.prime_three (by decide) hH.1.2.1.2.1 hH.1.2.1.2.2.2 hMark hcard).2.2

theorem GGResHyp.fix_mem_centralizer_three_of_unitary_six
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel GGNbrInner937U63Label 3 Bs K) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  classical
  obtain ⟨lab, hΛ, hHas, R, hR, I, F, θ, hcov, hN, hact⟩ :=
    largeEvenMarking_exists_hasLabel hK
  obtain ⟨⟨htw, hr, hpq, hpd⟩, hr5, -⟩ := hcov
  obtain ⟨f, hN, hf, hpm, hTor⟩ := ggTwA5Three_torDataAt hRig hLB hPJ hH
    (Or.inr ⟨rfl, rfl⟩) rfl hΛ hHas ⟨htw, hr5, hpq⟩
  have hm : Odd (2 ^ f + 1) := by
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    rw [pow_succ]
    exact ⟨2 ^ g, by omega⟩
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  exact ggTD_fix_mem_centralizer hm hpm hBs hS hN hTor

theorem GGResHyp.fix_mem_centralizer_of_E6_two
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel GGE6TwoThreeLabel p Bs K) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  obtain ⟨lab, hΛ, hHas, R, hR, I, F, θ, hlabel, hN, hact⟩ :=
    largeEvenMarking_exists_hasLabel hK
  have hp3 : p = 3 := hlabel.2.2
  subst p
  exact GGResHyp.fix_mem_centralizer_three_of_E6_two hH hK

theorem GGResHyp.fix_mem_centralizer_of_twE6
    (hRk : GGTwE6ThreeNbrRankInput)
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel GGTableBTwE6ThreeLabel p Bs K) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  obtain ⟨lab, hΛ, hHas, R, hR, I, F, θ, hlabel, hN, hact⟩ :=
    largeEvenMarking_exists_hasLabel hK
  have hp3 : p = 3 := hlabel.2.1
  subst p
  exact GGResHyp.fix_mem_centralizer_three_of_twE6 hRk hH hK

theorem GGResHyp.fix_mem_centralizer_of_F4
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel GGF4ThreeLabel p Bs K) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  obtain ⟨lab, hΛ, hHas, R, hR, I, F, θ, hlabel, hN, hact⟩ :=
    largeEvenMarking_exists_hasLabel hK
  have hp3 : p = 3 := hlabel.2.1
  subst p
  exact GGResHyp.fix_mem_centralizer_three_of_F4 hH hK

theorem GGResHyp.fix_mem_centralizer_of_unitary_six
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K) :
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  obtain ⟨lab, hΛ, hHas, R, hR, I, F, θ, hlabel, hN, hact⟩ :=
    largeEvenMarking_exists_hasLabel hK
  have hp3 : p = 3 := hlabel.2.2
  subst p
  exact GGResHyp.fix_mem_centralizer_three_of_unitary_six hRig hLB hPJ hH hK

theorem GGResHyp.false_of_seven
    (hRig : GGLabelRigidInput) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hH : GGResHyp p B Bs x L D J y K) (hp7 : p = 7)
    (hK : GGInnerDiagOnLabel (fun _ lab => GGSevenLabel lab) p Bs K) : False := by
  have hp : p.Prime := hH.1.tableB_facts.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨lab, hΛ, hHas, R, hR, I, F, θ, hSevenLab, -, -⟩ :=
    largeEvenMarking_exists_hasLabel hK
  exact ggSeven_K_absurd_of_noLine hRig hA8 hraw hiso hH hp7 hΛ hHas hSevenLab

private theorem GGResHyp.fix_mem_centralizer_of_not_tbTor_rest
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hTCJ : GGTCJKnown)
    (hI3 : GGNbrSubcomponentInput)
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : ¬ GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hTwE6 : ¬ GGInnerDiagOnLabel GGTwE6BadLabel p Bs K)
    (hE6Two : ¬ GGInnerDiagOnLabel GGE6TwoThreeLabel p Bs K)
    (hNoTwE6Sub : p = 3 → ¬ GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) p Bs K)
    (hNoNS : p = 3 → ¬ GGInnerDiagOnLabel GGTableBNbrInnerLinearNsLabel p Bs K)
    (hNoSeven : p = 7 → ¬ GGInnerDiagOnLabel (fun _ lab =>
      lab = ⟨.A,8,1⟩ ∨ lab = ⟨.A,11,1⟩ ∨ lab = ⟨.E6,0,1⟩ ∨
        lab = ⟨.twE6,0,1⟩ ∨ lab = ⟨.E8,0,1⟩) p Bs K)
    (b : ↥Bs) (hb : ∀ φ ∈ ggAutomizer K Bs, φ b = b) :
    (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  have hp : p.Prime := hH.1.tableB_facts.1
  have : Fact p.Prime := ⟨hp⟩
  classical
  by_cases hF4 : GGInnerDiagOnLabel GGF4ThreeLabel p Bs K
  · exact hH.fix_mem_centralizer_of_F4 hF4 b hb
  by_cases hU6 : GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K
  · exact hH.fix_mem_centralizer_of_unitary_six hRig hLB hPJ hU6 b hb
  exact (hH.false_of_nbr_rest_known hRig hraw hiso hTCJ hI3
    hK hU6 hF4 hTwE6 hNoNS hE6Two hNoTwE6Sub hNoSeven).elim

private theorem GGResHyp.fix_mem_centralizer_of_not_tbTor_ns_twE6
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hTCJ : GGTCJKnown)
    (hI3 : GGNbrSubcomponentInput) (hRk : GGTwE6ThreeNbrRankInput)
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : ¬ GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hE6Two : ¬ GGInnerDiagOnLabel GGE6TwoThreeLabel p Bs K)
    (hNoTwE6Sub : p = 3 → ¬ GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) p Bs K)
    (hNoSeven : p = 7 → ¬ GGInnerDiagOnLabel (fun _ lab =>
      lab = ⟨.A,8,1⟩ ∨ lab = ⟨.A,11,1⟩ ∨ lab = ⟨.E6,0,1⟩ ∨
        lab = ⟨.twE6,0,1⟩ ∨ lab = ⟨.E8,0,1⟩) p Bs K)
    (b : ↥Bs) (hb : ∀ φ ∈ ggAutomizer K Bs, φ b = b) :
    (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  have hp : p.Prime := hH.1.tableB_facts.1
  have : Fact p.Prime := ⟨hp⟩
  classical
  by_cases hNS : p = 3 ∧ GGInnerDiagOnLabel GGTableBNbrInnerLinearNsLabel p Bs K
  · obtain ⟨rfl, hMark⟩ := hNS
    exact hH.fix_mem_centralizer_three_of_linearNs hMark b hb
  have hNoNS : p = 3 → ¬ GGInnerDiagOnLabel GGTableBNbrInnerLinearNsLabel p Bs K := by
    intro hp3 hMark
    exact hNS ⟨hp3, hMark⟩
  by_cases hTwE6 : GGInnerDiagOnLabel GGTwE6BadLabel p Bs K
  · exact hH.fix_mem_centralizer_of_twE6 hRk hTwE6 b hb
  exact GGResHyp.fix_mem_centralizer_of_not_tbTor_rest hRig hLB hPJ hraw hiso hTCJ hI3
    hH hK hTwE6 hE6Two hNoTwE6Sub hNoNS hNoSeven b hb

private theorem GGResHyp.fix_mem_centralizer_of_not_tbTor_special
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hTCJ : GGTCJKnown)
    (hI3 : GGNbrSubcomponentInput) (hRk : GGTwE6ThreeNbrRankInput)
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : ¬ GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hNoSeven : p = 7 → ¬ GGInnerDiagOnLabel (fun _ lab =>
      lab = ⟨.A,8,1⟩ ∨ lab = ⟨.A,11,1⟩ ∨ lab = ⟨.E6,0,1⟩ ∨
        lab = ⟨.twE6,0,1⟩ ∨ lab = ⟨.E8,0,1⟩) p Bs K)
    (b : ↥Bs) (hb : ∀ φ ∈ ggAutomizer K Bs, φ b = b) :
    (b : G) ∈ Subgroup.centralizer (K : Set G) := by
  have hp : p.Prime := hH.1.tableB_facts.1
  have : Fact p.Prime := ⟨hp⟩
  classical
  by_cases hE6Two : GGInnerDiagOnLabel GGE6TwoThreeLabel p Bs K
  · exact hH.fix_mem_centralizer_of_E6_two hE6Two b hb
  by_cases hTwE6Sub : p = 3 ∧
      GGInnerDiagOnLabel (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) p Bs K
  · obtain ⟨rfl, hMark⟩ := hTwE6Sub
    exact hH.fix_mem_centralizer_three_of_twE6_sub hMark b hb
  have hNoTwE6Sub : p = 3 →
      ¬ GGInnerDiagOnLabel (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) p Bs K := by
    intro hp3 hMark
    exact hTwE6Sub ⟨hp3, hMark⟩
  exact GGResHyp.fix_mem_centralizer_of_not_tbTor_ns_twE6 hRig hLB hPJ hraw hiso hTCJ hI3 hRk
    hH hK hE6Two hNoTwE6Sub hNoSeven b hb

theorem ggResNbrFixCentralizesInput_holds
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hRk : GGTwE6ThreeNbrRankInput) (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput) :
    GGResNbrFixCentralizesInput := by
  intro G _ _ p B Bs x L D J y K hH b hb
  have hp : p.Prime := hH.1.tableB_facts.1
  have : Fact p.Prime := ⟨hp⟩
  by_cases hK : GGInnerDiagOnLabel GGTBTorCov p Bs K
  · exact hH.fix_mem_centralizer_of_tbTor hT hLift hK b hb
  by_cases hClassical : GGInnerDiagOnLabel GGTableBNbrInnerNineClassicalLabel p Bs K
  · exact (hH.false_of_classical_rank_vacuity hClassical).elim
  by_cases hSmall : GGInnerDiagOnLabel
      (fun p lab => GGTableBNbrInnerNineSmallLabel p lab ∨ lab.tag = .triD4 ∨ lab.tag = .twF4)
      p Bs K
  · exact (hH.false_of_small_neighbour hSmall).elim
  by_cases hSeven : p = 7 ∧
      GGInnerDiagOnLabel (fun _ lab => GGSevenLabel lab) p Bs K
  · exact (GGResHyp.false_of_seven hRig hA8 hraw hiso hH hSeven.1 hSeven.2).elim
  have hNoSeven : p = 7 → ¬ GGInnerDiagOnLabel (fun _ lab =>
      lab = ⟨.A,8,1⟩ ∨ lab = ⟨.A,11,1⟩ ∨ lab = ⟨.E6,0,1⟩ ∨
        lab = ⟨.twE6,0,1⟩ ∨ lab = ⟨.E8,0,1⟩) p Bs K := by
    intro hp7 hMark
    exact hSeven ⟨hp7, hMark⟩
  exact GGResHyp.fix_mem_centralizer_of_not_tbTor_special hRig hLB hPJ hraw hiso hTCJ hI3 hRk
    hH hK hNoSeven b hb

end CFSG.StandardType

end
