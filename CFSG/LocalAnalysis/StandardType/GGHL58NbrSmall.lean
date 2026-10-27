module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTWRowData
public import CFSG.LocalAnalysis.StandardType.GGTWRowDataL
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHLK
public import CFSG.LocalAnalysis.StandardType.GGHLNbrInput
public import CFSG.LocalAnalysis.StandardType.GGTWRowGenDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDatumARankFrom
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHLFrom
public import CFSG.LocalAnalysis.StandardType.GGHL58NbrDerive
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGAutomizerLiftTor

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nQS_not_excl_of_S {p : ℕ} {lab : LargeEvenLabel}
    (h : (lab.tag = .A ∨ lab.tag = .twA) ∧ 3 ≤ lab.rank ∧ p ∣ ggTorM lab ∧
      ¬ p ∣ lab.rank + 1) : ¬ GGTBWExcl lab := by
  rintro (hF4 | ⟨hBC, -⟩)
  · rcases h.1 with h | h <;> rw [h] at hF4 <;> exact absurd hF4 (by decide)
  · rcases h.1 with h | h <;> rw [h] at hBC <;> exact absurd hBC (by decide)

private lemma l05nQS_ne_two_of_S {p : ℕ} {lab : LargeEvenLabel}
    (hpp : p.Prime) (hlab : LargeEvenInLambda2 lab)
    (h : (lab.tag = .A ∨ lab.tag = .twA) ∧ 3 ≤ lab.rank ∧ p ∣ ggTorM lab ∧
      ¬ p ∣ lab.rank + 1) : p ≠ 2 := by
  intro h2
  have heven : Even (ggTorM lab) := even_iff_two_dvd.mpr (h2 ▸ h.2.2.1)
  exact (Nat.not_even_iff_odd.mpr (ggHLT_odd_ggTorM hlab)) heven

private lemma l05nQS_split_of_S {p : ℕ} {lab : LargeEvenLabel}
    (h : (lab.tag = .A ∨ lab.tag = .twA) ∧ 3 ≤ lab.rank ∧ p ∣ ggTorM lab ∧
      ¬ p ∣ lab.rank + 1) : LargeEvenSplit p lab := by
  obtain ⟨htag, -, hdvdM, -⟩ := h
  unfold LargeEvenSplit
  unfold ggTorM at hdvdM
  rcases htag with hA | htwA
  · left
    refine ⟨?_, ?_⟩
    · rw [hA]; simp [LargeEvenUntwisted]
    · rwa [if_neg (by rw [hA]; decide)] at hdvdM
  · right; left
    refine ⟨?_, ?_, ?_⟩
    · rw [htwA]; simp [LargeEvenUntwisted]
    · rw [htwA]; decide
    · rwa [if_pos (by rw [htwA]; decide)] at hdvdM

private theorem l05nQS_core_K_aInd (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (fun p lab => (lab.tag = .A ∨ lab.tag = .twA) ∧ 3 ≤ lab.rank ∧
      p ∣ ggTorM lab ∧ ¬ p ∣ lab.rank + 1) p Bs K) :
    ∃ (lab : LargeEvenLabel) (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
        ((lab.tag = .A ∨ lab.tag = .twA) ∧ 3 ≤ lab.rank ∧
          p ∣ ggTorM lab ∧ ¬ p ∣ lab.rank + 1) ∧
        GGTorusTorData (ggTorM lab) lab.rank (CartanMatrix.A lab.rank)
          (CoxeterMatrix.A lab.rank) ↥K (ggGamma K hN).range := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hW : GGTBTorWRows := ggTBTorWRows_of_all hT
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  have hHas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hraw
  obtain ⟨R₀, _instR₀, I₀, F₀, hQ0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ0, hBody0⟩ := hQ0
  obtain ⟨hP, -, -⟩ := hBody0
  have hrow : GGTBTorRowAt p lab (lab.rank - ggTorEnn p lab) (ggTorM lab) lab.rank
      (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) :=
    GGTBTorRowAt.aInd hP.1 hP.2.2.2 hP.2.2.1
  have hWl : LargeEvenLabelAll lab (fun R _ I _ =>
      GGTorusTorW p (lab.rank - ggTorEnn p lab) (ggTorM lab) lab.rank
        (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) R I) :=
    hW p lab (lab.rank - ggTorEnn p lab) (ggTorM lab) lab.rank
      (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) hp hp2 hlab hrow
  have hLl : LargeEvenLabelAll lab (fun R _ _ _ =>
      GGTorusLift p (lab.rank - ggTorEnn p lab) R) :=
    hLift p lab (lab.rank - ggTorEnn p lab) (ggTorM lab) lab.rank
      (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) hp hp2 hlab hrow
  have hBoth := largeEvenLabelAll_and hWl hLl
  obtain ⟨R, _instR, I, F, hQ, hWtor, hlift⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
  obtain ⟨-, -, θ, hP', hN, hBsI⟩ := hQ
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hTB := ggTorusTBGroup_of_nbr hH.1 hnb hperf θ hN
    (fun b hb => ggLAut_mem_of_induces K θ hN hBsI hb) hlift
  refine ⟨lab, hN, hlab, hHas, ?_, ?_⟩
  · exact ⟨hP'.1, hP'.2.1, hP'.2.2.1, hP'.2.2.2⟩
  · exact hWtor ↥K (ggQuotHom θ) (ggGamma K hN).range hTB

theorem ggHL58Nbr_of_lift {S : ℕ → LargeEvenLabel → Prop} (hW' : GGTBWNormInputNbr S)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y)
    (hM : GGInnerDiagOnLab S p Bs K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hlift : GGAutomizerLift K Bs hN) : GGTWHLAt p Bs K y := by
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hyB : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  refine ⟨hyB, ?_⟩
  intro Λ₂ iF₂ iD₂ M₂ C₂ hMw₂ hMC₂ V₂ iV₂add iV₂mod ι₂ φ₂ h₂ α₂ hlin₂ hrefl₂ hpair₂ hgen₂
    t ht htr hty
  exact ggHL_lines_of_lift_K hW' hH hCent hM hN hyB hlift hMw₂ hMC₂ ι₂ φ₂ h₂ α₂ hlin₂ hrefl₂
    hpair₂ hgen₂ t ht htr hty

theorem ggHL58Nbr_of_torData {S : ℕ → LargeEvenLabel → Prop} (hW' : GGTBWNormInputNbr S)
    {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hH : GGResHyp p B Bs x L D J y K)
    (hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y)
    (hM : GGInnerDiagOnLab S p Bs K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hom : Odd m) (hpm : p ∣ m) (hTor : GGTorusTorData m N C M ↥K (ggGamma K hN).range) :
    GGTWHLAt p Bs K y := by
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hSdef : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  exact ggHL58Nbr_of_lift hW' hH hCent hM hN
    (ggAutomizerLift_of_torData hp2 hBs hSdef hN hom hpm hTor)

theorem ggHL58Nbr_small_of_inputs (hRig : GGLabelRigidInput) (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hW : GGTBWNormLabelInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hyK : y ∉ K)
    (hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y)
    (h : GGInnerDiagOnLabel (fun p lab => (lab.tag = .A ∨ lab.tag = .twA) ∧ 3 ≤ lab.rank ∧
      p ∣ ggTorM lab ∧ ¬ p ∣ lab.rank + 1) p Bs K) : GGTWHLAt p Bs K y := by
  have hp : p.Prime := Fact.out
  let S : ℕ → LargeEvenLabel → Prop := fun p lab =>
    (lab.tag = .A ∨ lab.tag = .twA) ∧ 3 ≤ lab.rank ∧ p ∣ ggTorM lab ∧
      ¬ p ∣ lab.rank + 1
  have hW' : GGTBWNormInputNbr S :=
    ggTBWNormInputNbr_of_labels fun p lab hpp hlab hSlab =>
      hW p hpp (l05nQS_ne_two_of_S hpp hlab hSlab) lab hlab (l05nQS_not_excl_of_S hSlab)
        (by rcases hSlab.1 with h | h <;> rw [h] <;> decide)
  have hM : GGInnerDiagOnLab S p Bs K :=
    largeEvenMarking_mono
      (fun lab R _ I F θ hP => ⟨hP.1, l05nQS_split_of_S hP.1, hP.2.1, hP.2.2⟩) h
  obtain ⟨lab, hN, hlab, hHas, hP, hTor⟩ := l05nQS_core_K_aInd hT hLift hH h
  exact ggHL58Nbr_of_torData hW' hH hCent hM hN (ggHLT_odd_ggTorM hlab) hP.2.2.1 hTor

end CFSG.StandardType

end
