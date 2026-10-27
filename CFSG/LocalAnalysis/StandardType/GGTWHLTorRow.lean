module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTWRowData
public import CFSG.LocalAnalysis.StandardType.GGTWRowDataL
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHLK
public import CFSG.LocalAnalysis.StandardType.GGHLNbrInput
public import CFSG.LocalAnalysis.StandardType.GGTWRowGenDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDatumARankFrom
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHLFrom
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
public import CFSG.LocalAnalysis.StandardType.GGAutomizerLiftTor

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nQT_cov_twA_three {p n : ℕ} (hcov : GGTBTorCov p ⟨.twA, 3, n⟩) :
    p ∣ 2 ^ n + 1 := by
  obtain ⟨r, m, N, C, M, hrow⟩ := hcov
  cases hrow with
  | aDep h1 h2 h3 h4 h5 => simpa [ggTorM] using h4
  | aInd h1 h2 h3 => simpa [ggTorM] using h3
  | relA5 h1 h2 => exact absurd h1 (by simp)
  | e6Three h1 h2 h3 => exact absurd h1 (by simp)
  | e6Ind h1 h2 h3 => exact absurd h2 (by simp)
  | e8Three h1 h2 => exact absurd h1 (by simp)
  | e8Ind h1 h2 h3 => exact absurd h2 (by simp)
  | c h1 h2 => exact absurd h1 (by simp)
  | d h1 => rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by simp)
  | e7 h1 h2 => exact absurd h1 (by simp)
  | f4 h1 h2 h3 => exact absurd h1 (by simp)
  | g2 h1 h2 => exact absurd h1 (by simp)
  | relD h1 => rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by simp)
  | relE6 h1 h2 => rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by simp)

private lemma l05nQT_cov_twD_two {p n : ℕ} (hcov : GGTBTorCov p ⟨.twD, 2, n⟩) :
    p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
  obtain ⟨r, m, N, C, M, hrow⟩ := hcov
  cases hrow with
  | aDep h1 h2 h3 h4 h5 => exact absurd h1 (by simp)
  | aInd h1 h2 h3 => exact absurd h1 (by simp)
  | relA5 h1 h2 => exact absurd h1 (by simp)
  | e6Three h1 h2 h3 => exact absurd h1 (by simp)
  | e6Ind h1 h2 h3 => exact absurd h2 (by simp)
  | e8Three h1 h2 => exact absurd h1 (by simp)
  | e8Ind h1 h2 h3 => exact absurd h2 (by simp)
  | c h1 h2 => exact absurd h1 (by simp)
  | e7 h1 h2 => exact absurd h1 (by simp)
  | f4 h1 h2 h3 => exact absurd h1 (by simp)
  | g2 h1 h2 => exact absurd h1 (by simp)
  | relE6 h1 h2 => rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by simp)
  | d h1 =>
      rcases h1 with ⟨h, _⟩ | ⟨h, hd, _⟩
      · exact absurd h (by simp)
      · exact Or.inr hd
  | relD h1 =>
      rcases h1 with ⟨h, _, _⟩ | ⟨h, hd⟩
      · exact absurd h (by simp)
      · rcases hd with hd | ⟨hd, _⟩
        · exact Or.inl hd
        · exact Or.inr hd

private lemma l05nQT_cov_A1 {p n : ℕ} (hcov : GGTBTorCov p ⟨.A, 1, n⟩) :
    p ∣ 2 ^ n - 1 := by
  obtain ⟨r, m, N, C, M, hrow⟩ := hcov
  cases hrow with
  | aInd h1 h2 h3 => simpa [ggTorM] using h3
  | aDep h1 h2 h3 h4 h5 => exact absurd h2 (by simp)
  | relA5 h1 h2 => exact absurd h1 (by simp)
  | e6Three h1 h2 h3 => exact absurd h1 (by simp)
  | e6Ind h1 h2 h3 => exact absurd h2 (by simp)
  | e8Three h1 h2 => exact absurd h1 (by simp)
  | e8Ind h1 h2 h3 => exact absurd h2 (by simp)
  | c h1 h2 => exact absurd h1 (by simp)
  | d h1 => rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by simp)
  | e7 h1 h2 => exact absurd h1 (by simp)
  | f4 h1 h2 h3 => exact absurd h1 (by simp)
  | g2 h1 h2 => exact absurd h1 (by simp)
  | relD h1 => rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by simp)
  | relE6 h1 h2 => rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by simp)

private lemma l05nQT_split_twA3 {p n : ℕ} (h : p ∣ 2 ^ n + 1) :
    LargeEvenSplit p ⟨.twA, 3, n⟩ :=
  Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by simp, h⟩)

private lemma l05nQT_split_twD {p n : ℕ} (h : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) :
    LargeEvenSplit p ⟨.twD, 2, n⟩ := by
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, h⟩))
  · exact Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by simp, h⟩)

private lemma l05nQT_split_A1 {p n : ℕ} (h : p ∣ 2 ^ n - 1) :
    LargeEvenSplit p ⟨.A, 1, n⟩ :=
  Or.inl ⟨by simp [LargeEvenUntwisted], h⟩

private lemma l05nQT_split_of_iso {p : ℕ} (hp : p.Prime) {lab labs : LargeEvenLabel}
    (hcov : GGTBTorCov p lab) (hiso : GGLabelIso lab labs)
    (hs : LargeEvenSplit p labs) : LargeEvenSplit p lab := by
  rcases hiso with h | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h]; exact hs
  · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      (simp only [LargeEvenSplit] at hs ⊢) <;>
      (rw [h1] at ⊢) <;> (rw [h2] at hs) <;>
      (rw [← h4] at hs) <;>
      simpa [LargeEvenSplit, LargeEvenUntwisted] using hs
  · rw [h1] at ⊢
    rw [h2] at hs
    simpa [LargeEvenSplit, LargeEvenUntwisted] using hs
  · rw [h1] at ⊢
    rw [h2] at hs
    simpa [LargeEvenSplit, LargeEvenUntwisted] using hs
  · rw [h1] at ⊢
    rw [h2] at hs
    have hdvd : p ∣ 2 ^ lab.n + 1 ∨ (lab.n = 1 ∧ p = 3) := by
      simpa [LargeEvenSplit, LargeEvenUntwisted] using hs
    rcases hdvd with h | h
    · exact Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by simp, h⟩)
    · exact Or.inr (Or.inr (Or.inr h))
  · rw [h1] at hcov ⊢
    exact l05nQT_split_twA3 (l05nQT_cov_twA_three hcov)
  · rw [h1] at hcov ⊢
    exact l05nQT_split_twD (l05nQT_cov_twD_two hcov)
  · rw [h2] at hcov ⊢
    exact l05nQT_split_A1 (l05nQT_cov_A1 hcov)

theorem ggTWHL_of_lift {S : ℕ → LargeEvenLabel → Prop} (hWn : GGTBWNormInputOn S)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hM : GGInnerDiagOnLab S p Bs L)
    (hnc : ∃ T : Subgroup G, T ≤ L ∧ IsPGroup p T ∧ ¬ IsCyclic T)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hlift : GGAutomizerLift L Bs hN) :
    GGTWHLAt p Bs L x := by
  obtain ⟨-, -, hxB, -, -⟩ := hcfg.tableB_facts
  refine ⟨hxB, ?_⟩
  intro Λ₂ iF₂ iD₂ M₂ C₂ hMw₂ hMC₂ V₂ iV₂add iV₂mod ι₂ φ₂ h₂ α₂ hlin₂ hrefl₂ hpair₂ hgen₂
    t ht htr htx
  exact ggHL_lines_of_lift hWn hcfg hM hnc hN hxB hlift hMw₂ hMC₂ ι₂ φ₂ h₂ α₂ hlin₂ hrefl₂
    hpair₂ hgen₂ t ht htr htx

theorem ggTWHL_of_torData {S : ℕ → LargeEvenLabel → Prop} (hWn : GGTBWNormInputOn S)
    {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hcfg : GGConfig p B Bs x L D J) (hM : GGInnerDiagOnLab S p Bs L)
    (hnc : ∃ T : Subgroup G, T ≤ L ∧ IsPGroup p T ∧ ¬ IsCyclic T)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hom : Odd m) (hpm : p ∣ m)
    (hTor : GGTorusTorData m N C M ↥L (ggGamma L hN).range) : GGTWHLAt p Bs L x := by
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSdef : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  exact ggTWHL_of_lift hWn hcfg hM hnc hN
    (ggAutomizerLift_of_torData hp2 hBs hSdef hN hom hpm hTor)

theorem ggTWHL_of_tbTor_row
    (hRig : GGLabelRigidInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hW : GGTBWNormLabelInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ GGTBWExcl lab ∧
      ¬ GGOutdiagTwistedLabel lab) p Bs L) : GGTWHLAt p Bs L x := by
  have hp : p.Prime := Fact.out
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBBs : B ≤ Bs := hH.1.2.1.1
  let S : ℕ → LargeEvenLabel → Prop := fun p lab =>
    p ≠ 2 ∧ GGTBTorCov p lab ∧ ¬ GGTBWExcl lab ∧ ¬ GGOutdiagTwistedLabel lab
  have hCov : GGInnerDiagOnLabel GGTBTorCov p Bs L :=
    largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨hP.1.1, hP.2⟩) h
  have hWrows : GGTBTorWRows := ggTBTorWRows_of_all hT
  obtain ⟨m, N, C, M, hN, hom, hpm, -, -, hTor⟩ :=
    l05nPlP3_core_L hWrows hLift hH hCov
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨R, _instR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  have hcov : GGTBTorCov p lab := hP.1.1
  have hHasLab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  obtain ⟨-, -, -, -, -, -, -, hstd⟩ := hH.1.1
  obtain ⟨hstdMark, -, -, -⟩ := hstd
  obtain ⟨-, labs, hlabs, hraws⟩ := hstdMark
  obtain ⟨Rs, _instRs, Is, Fs, hQs⟩ := largeEvenRawDatum_exists hraws
  obtain ⟨-, -, θs, hPs⟩ := hQs
  have hHasLabs : GGHasLabel labs (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraws
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hiso : GGLabelIso lab labs :=
    hRig lab labs (↥L ⧸ Subgroup.center ↥L) hlab hlabs hHasLab hHasLabs
  have hsplit : LargeEvenSplit p lab := l05nQT_split_of_iso hp hcov hiso hPs.1
  have hM : GGInnerDiagOnLab S p Bs L := by
    refine ⟨hperf, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hP⟩
    exact ⟨hs, hna, θ, ⟨⟨hp2, hP.1.1, hP.1.2.1, hP.1.2.2⟩, hsplit, hP.2.1, hP.2.2⟩⟩
  have hWn : GGTBWNormInputOn S :=
    ggTBWNormInputOn_of_labels fun p lab hpp hlab' hSlab =>
      hW p hpp hSlab.1 lab hlab' hSlab.2.2.1 fun h => hSlab.2.2.2 (Or.inl h)
  have hnc : ∃ T : Subgroup G, T ≤ L ∧ IsPGroup p T ∧ ¬ IsCyclic T :=
    ggLNoncyclicInputOn_not_twisted G p B x L hH.1.1
      (by
        refine ⟨hperf, lab, hlab, ?_⟩
        refine largeEvenRawDatum_mono ?_ hraw
        rintro R _ I F ⟨hs, hna, θ, hP⟩
        exact ⟨hs, hna, θ, ⟨hP.1.2.2, hsplit, hBBs.trans hP.2.1,
          fun b hb => hP.2.2 b (hBBs hb)⟩⟩)
  exact ggTWHL_of_torData hWn hcfg hM hnc hN hom hpm hTor

end CFSG.StandardType

end
