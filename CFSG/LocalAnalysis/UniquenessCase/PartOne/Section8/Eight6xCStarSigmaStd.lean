module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCStar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRest
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCSylowHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCOutHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 KStrongEmbedded72)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (R72 R76Sig)
open CFSG.LocalAnalysis.UniquenessCase.UC6 (R6_14 R6_38)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
  (SigmaStd not_solvable_of_mem_calC sp_of_mem_sig sig_subset_sig1 le_pRank')

theorem false_of_abelian_sylow_of_bar_of_R6_14
    {G : Type} [Group G] [Finite G] {D : Data G} {L S E : Subgroup G} {r : ℕ}
    (h614 : R6_14 D) (hsub : D.sig ⊆ D.sig1)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrsig : r ∉ D.sig)
    (hnot : ¬ IsStronglyPEmbedded r D.M)
    (hLM : L ≤ D.M) (hLnorm : (L.subgroupOf D.M).Normal)
    (hS : IsSylowOf r S D.M)
    (hdecomp : S ≤ (S ⊓ L) ⊔ centralizerBar S L)
    (hSLab : ∀ x ∈ S ⊓ L, ∀ y ∈ S ⊓ L, x * y = y * x)
    (hSL : S ⊓ L ⊓ pCoreOf 2 L = ⊥)
    (hE : E ≤ S ⊓ L)
    (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (hΓ : rankThreeGamma 1 r E ≤ D.M) :
    False := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hZ := star863_of_bar hLM hLnorm hS hdecomp hSLab hSL
  have hEcenter : E ≤ S ⊓ centralizer (S : Set G) := by
    refine le_inf (hE.trans inf_le_left) ?_
    intro e he
    have heA : e ∈ S ⊓ L := hE he
    have hmem : (⟨e, heA.1⟩ : ↥S) ∈ (S ⊓ L).subgroupOf S :=
      Subgroup.mem_subgroupOf.mpr heA
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h := Subgroup.mem_center_iff.mp (hZ hmem) ⟨s, hs⟩
    simpa using congrArg (fun w : ↥S => (w : G)) h
  exact hnot (h614 hsub r hr hr2 hrsig S hS E hEcenter hEel hEcard hΓ)

theorem false_of_starWitness_of_choiceX_of_sigmaStd {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : SigmaStd D) (h614 : R6_14 D) (h638 : R6_38 D)
    (h858 : R858 D) (h72 : R72 D) (h76 : R76Sig D) (hKF7 : KStrongEmbedded72)
    {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X) (hLX : ⁅L, X⁆ ≤ pCoreOf 2 L)
    (hS : IsSimpleGroup (Bar2 L)) (hOut : IsCyclic (Outer (Bar2 L))) {r : ℕ}
    (hStar : StarWitness (Bar2 L) r) : False := by
  have hr : r.Prime := hStar.1
  have hr5 : 5 ≤ r := hStar.2.1
  obtain ⟨S, B, p, hSyl, hp, hpσ, hBM, hBel, hBcard, hcent⟩ :=
    exists_sigma_ep2_centralizing_sylow_inf hSg h638 h858 h72 hKF7 hX hLX hS hOut hr (by omega)
  have hLM : L ≤ D.M := hX.cex.mem.1.le
  have hLnorm : (L.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mpr
      (normalizer_le_of_r858_of_isSimpleGroup h858 hX.cex hS)
  obtain ⟨hdec, hab, hSL, E, hEle, hEel, hEcard⟩ := starWitness_transport hLM hLnorm hSyl hStar
  have hEL : E ≤ L := hEle.trans inf_le_right
  have hEM : E ≤ D.M := (hEle.trans inf_le_left).trans hSyl.le
  have h1 : 1 < CFSG.Open.pRank r L := by
    have := le_pRank' hr hEL hEel hEcard
    omega
  have hnot : ¬ IsStronglyPEmbedded r D.M :=
    not_stronglyEmbedded_of_choiceX_of_leaves h72 hKF7 hX hLX hS hr (by omega) h1
  have hns : ¬ Group.IsSolvable ↥D.M := not_solvable_of_mem_calC hX.cex.mem
  have hrsig : r ∉ D.sig := fun hrσ => hnot (sp_of_mem_sig hSg hns hrσ)
  have hBE : B ≤ centralizer (E : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.1 (hcent (hEle he))) b hb).symm
  have hpr := D.sig_prime p hpσ
  have hΓ : rankThreeGamma 1 r E ≤ D.M := by
    refine h76 p hpσ hpr.2 (sp_of_mem_sig hSg hns hpσ) r hr E hEM hEel hEcard ?_ ?_
    · have := le_pRank' hpr.1 (le_inf hBM hBE) hBel hBcard
      omega
    · intro Y hYE _
      have hBY : B ≤ D.M ⊓ normalizer (Y : Set G) :=
        le_inf hBM (hBE.trans ((Subgroup.centralizer_le hYE).trans
          (Subgroup.centralizer_le_normalizer (Y : Set G))))
      have := le_pRank' hpr.1 hBY hBel hBcard
      omega
  exact false_of_abelian_sylow_of_bar_of_R6_14 h614 (sig_subset_sig1 hSg hns) hr (by omega)
    hrsig hnot hLM hLnorm hSyl hdec hab hSL hEle hEel hEcard hΓ

theorem false_of_lie_families_of_choiceX_of_sigmaStd
    {G : Type} [Group G] [Finite G] {D : Data G}
    (hNS : G2NonsplitSylowInput) (hTri : TrialityTorusSylowInput) (hOutC : LieOutCyclicInput)
    (hSg : SigmaStd D) (h614 : R6_14 D) (h638 : R6_38 D)
    (h858 : R858 D) (h72 : R72 D) (h76 : R76Sig D) (hKF7 : KStrongEmbedded72)
    {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X) (hLX : ⁅L, X⁆ ≤ pCoreOf 2 L)
    (hS : IsSimpleGroup (Bar2 L))
    (h : (∃ p f : ℕ, LieModel (Bar2 L) .G2 0 p f ∧ p.Prime ∧ p ≠ 3 ∧ 1 ≤ f ∧ 3 ≤ p ^ f ∧
          p ^ f ≠ 5 ∧ p ^ f ≠ 7 ∧ p ^ f ≠ 17) ∨
        (∃ p f : ℕ, LieModel (Bar2 L) .trialityD4 0 p f ∧ p.Prime ∧ 1 ≤ f) ∨
        (∃ f : ℕ, LieModel (Bar2 L) .twistedF4 0 2 f ∧ 3 ≤ f ∧ Odd f)) : False := by
  obtain ⟨r, hStar⟩ := exists_starWitness_of_lie_families hNS hTri h
  have hOut : IsCyclic (Outer (Bar2 L)) := by
    rcases h with ⟨p, f, hK, -, hp3, -⟩ | ⟨p, f, hK, -⟩ | ⟨f, hK, -⟩
    · exact hOutC.1 _ p f hK hp3
    · exact hOutC.2.1 _ p f hK
    · exact hOutC.2.2 _ f hK
  exact false_of_starWitness_of_choiceX_of_sigmaStd hSg h614 h638 h858 h72 h76 hKF7 hX hLX hS hOut
    hStar

theorem list863_of_lieModel_g2_of_choiceX_of_sigmaStd
    {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : SigmaStd D) (h614 : R6_14 D) (h638 : R6_38 D)
    (h858 : R858 D) (h72 : R72 D) (h76 : R76Sig D) (hKF7 : KStrongEmbedded72)
    {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X) (hLX : ⁅L, X⁆ ≤ pCoreOf 2 L)
    {p f : ℕ} (hK : LieModel (Bar2 L) .G2 0 p f) : List863 (Bar2 L) := by
  obtain ⟨hp, hf, -, h3q⟩ := hK.admissible
  have hp3 : p ≠ 3 := p_ne_three_of_cex856_g2 hX.cex hK
  by_cases h5 : p ^ f = 5
  · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 5)).mp h5
    exact Or.inr (Or.inr (Or.inl hK))
  by_cases h7 : p ^ f = 7
  · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp h7
    exact Or.inr (Or.inr (Or.inr (Or.inl hK)))
  by_cases h17 : p ^ f = 17
  · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 17)).mp h17
    exact Or.inr (Or.inr (Or.inr (Or.inr hK)))
  exact (false_of_lie_families_of_choiceX_of_sigmaStd g2NonsplitSylowInput_holds
    trialityTorusSylowInput_holds lieOutCyclicInput_holds hSg h614 h638 h858 h72 h76 hKF7 hX hLX
    (CFSG.Timmesfeld.isSimpleGroup_of_lieModel hK)
    (Or.inl ⟨p, f, hK, hp, hp3, hf, h3q, h5, h7, h17⟩)).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
