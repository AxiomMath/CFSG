module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEighteenPHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeAS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEighteenBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicNineHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicNoncentralONan
public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightTwo
public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenOneUncond
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_HSRu_of_calC_AS {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnorm : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)))
    (hfact : ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y),
      Inputs1719.KYForm Y K S → Nonempty (↥K ≃* Bar2 L) →
      ∃ H₁ H₂ : Subgroup Y, S ≤ H₁ ∧ S ≤ H₂ ∧ H₁ ⊔ H₂ = ⊤ ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSqAS 2 H₁ ∧
          CFSG.LocalAnalysis.WeakClosure81.InFSqAS 2 H₂ ∧
            3 ∣ Nat.card ↥H₁ ∧ 3 ∣ Nat.card ↥H₂) :
    ∃ H₁ H₂ : Subgroup G, D.T ≤ H₁ ∧ D.T ≤ H₂ ∧ H₁ ≤ L ⊔ D.T ∧ H₂ ≤ L ⊔ D.T ∧
      H₁ ⊔ H₂ = L ⊔ D.T ∧
      CFSG.LocalAnalysis.WeakClosure81.InFSqAS 2 H₁ ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSqAS 2 H₂ ∧
          3 ∣ Nat.card ↥H₁ ∧ 3 ∣ Nat.card ↥H₂ :=
  exists_pair_of_calC_of_bar2Inv hL hnorm
    (fun _ _ _ H => CFSG.LocalAnalysis.WeakClosure81.InFSqAS 2 H)
    (fun _ _ _ _ _ _ _ _ ⟨e⟩ =>
      CFSG.LocalAnalysis.WeakClosure81.inFSqAS_iff_bar2_inFAS_mulEquiv e 2) hfact

@[expose] def Gap17_18DeltaAS (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, (c : Ctx17_17 D V₀ V L) → (L.subgroupOf D.M).Normal →
    IsSpor (BarInf L) .ONan → D.k = 1 →
      ∃ Δ : Finset (Subgroup G),
        (∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M) ∧ UniqueMax D.M (⨆ H ∈ Δ, H) ∧
          (∀ H ∈ Δ, CFSG.LocalAnalysis.WeakClosure81.InFSqAS 2 H) ∧
            (∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g)

section Certificates



theorem gap17_18DeltaAS (D : Data G) (V₀ V : Subgroup G)
    (hON : Inputs1719.K_ONanDeltaAS) (h869 : F08.R869 D) :
    Gap17_18DeltaAS D V₀ V := by
  intro L c hN hO hk
  classical
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have h3L := two_lt_pRank_three_of_isSpor_ONan D c hO
  have hnt : ¬ F08.Thin8 L := Inputs1719.not_thin_of_pRank_three (by omega)
  have hU : UniqueMax D.M (L ⊔ D.T) :=
    Inputs1719.uniqueMax_sup_T_of_not_thin h869 c.mem_calC hnt
  obtain ⟨H₁, H₂, hT₁, hT₂, hle₁, hle₂, hsup, hFS₁, hFS₂, h3₁, h3₂⟩ :=
    exists_HSRu_of_calC_AS (D := D) (L := L) c.mem_calC
      (Tbar_le_normalizer_K1 (D := D) (L := L) hN)
      (fun Y _ _ K S hKY hKe => by
        obtain ⟨eK⟩ := hKe
        obtain ⟨eI⟩ := UC22.uc22p21k_barInf_equiv_of_calC c.mem_calC
        have hiso : IsSpor (↥K ⧸ Subgroup.center ↥K) .ONan := by
          obtain ⟨eO⟩ := hO
          exact ⟨(QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)).trans
            (eI.symm.trans eO)⟩
        obtain ⟨A, B, hSA, hSB, hsup', h3A, h3B, hFSA, hFSB⟩ :=
          hON Y K S hKY.1 hKY.2.1 hKY.2.2.1 hiso hKY.2.2.2.1 hKY.2.2.2.2.1 hKY.2.2.2.2.2
        exact ⟨A, B, hSA, hSB, hsup', hFSA, hFSB, h3A, h3B⟩)
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra h
    exact absurd ((Data.k_eq_two_iff D).2 h) (by omega)
  have hHM : L ⊔ D.T ≤ D.M := sup_le hLM D.sylowM.le
  refine ⟨{H₁, H₂}, ?_, ?_, ?_, ?_⟩
  · intro H hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact ⟨hT₁, hle₁.trans hHM⟩
    · exact ⟨hT₂, hle₂.trans hHM⟩
  · have hsupΔ : (⨆ H ∈ ({H₁, H₂} : Finset (Subgroup G)), H) = L ⊔ D.T := by
      rw [← Finset.sup_eq_iSup, Finset.sup_insert, Finset.sup_singleton, hsup]
    rw [hsupΔ]
    exact hU
  · intro H hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact hFS₁
    · exact hFS₂
  · intro H hH g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hH
    have hHM' : H ≤ D.M := by
      rcases hH with rfl | rfl
      · exact hle₁.trans hHM
      · exact hle₂.trans hHM
    have h3H : 3 ∣ Nat.card ↥H := by
      rcases hH with rfl | rfl
      · exact h3₁
      · exact h3₂
    exact CFSG.GroupTheory.twoResidual_not_le_conjSubgroup_of_isStronglyPEmbedded Nat.prime_three
      (by norm_num) hHM' h3H hstr g hg

theorem seventeen_eighteenAS (D : Data G) (V₀ V : Subgroup G)
    (h17_1 : ∀ hV : Hyp125 D V₀ V, R17_1At D V₀ V hV)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h126 : R126 D) (h111 : W3Thm111 G) (h117 : C117 D V₀ V) (h869 : F08.R869 D)
    (hB : B17_18Bound D V₀ V) (h82 : F08.R82 D)
    (hKS1 : Inputs1719.K_SporadicThreePermutingLe (CFSG.Open.pRank 3 D.M))
    (hRes : Gap17_18ReductionResidual D V₀ V)
    (hONK : Inputs1719.K_ONanDeltaAS) :
    R17_18At D V₀ V := by
  intro L c
  have hRed : Gap17_18Reduction D V₀ V := gap17_18Reduction D V₀ V h82 hKS1 hRes
  have hDelta : Gap17_18DeltaAS D V₀ V := gap17_18DeltaAS D V₀ V hONK h869
  by_contra hle
  push Not at hle
  have h3' : 2 < CFSG.pRank 3 ↥(UC22.conjClosure D.M L) := hle
  have h3 : 2 < CFSG.Open.pRank 3 (UC22.conjClosure D.M L) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (UC22.conjClosure D.M L),
      ← CFSG.SectionRank.pRank_eq_open_pRank_top (p := 3) ↥(UC22.conjClosure D.M L)]
    exact h3'
  obtain ⟨hk, hcase⟩ := hRed L c h3
  rcases hcase with ⟨X, hX⟩ | ⟨hnorm, hO⟩
  · exact false_of_k_eq_one_of_inP11 (h17_1 c.hyp125) hk hX
  · have hLM : L ≤ D.M := c.mem_calC.1.le
    have hN : D.M ≤ normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hnorm
    have hcl : UC22.conjClosure D.M L = L := by
      refine le_antisymm ?_ (TwelveTwentyThree.le_conjClosure D.M L)
      refine iSup₂_le ?_
      rintro K ⟨g, hg, rfl⟩
      rw [UC6S846.mem_normalizer_iff_map_conj.mp (hN hg)]
    have hm3L : 2 < CFSG.Open.pRank 3 L := by rwa [hcl] at h3
    have hnt : ¬ F08.Thin8 L := by
      intro ht
      have h1 : CFSG.Open.pRank 3 L ≤ 1 := ht 3 Nat.prime_three (by norm_num)
      omega
    have hU : UniqueMax D.M L := by
      have := uniqueMax_conjClosure_of_not_thin h869 c.mem_calC hnt
      rwa [hcl] at this
    have hUc : UniqueMax D.M (UC22.conjClosure D.M L) := by rw [hcl]; exact hU
    have hL1 : barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥ :=
      barSub_ne_bot_of_not_thin c.hyp125 h117 c.mem_calC hnt
    have hconf : V₀ ≠ ⊥ → ∃ Δ : Finset (Subgroup G),
        (∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M) ∧ UniqueMax D.M (⨆ H ∈ Δ, H) ∧
        (∀ H ∈ Δ, CFSG.LocalAnalysis.WeakClosure81.InFSqAS 2 H) ∧
        (∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g) :=
      fun _ => hDelta L c hnorm hO hk
    have hm := mBar_le_bBar_add_of_deltaAS D hx h61 h127 h1114 h162 hTor h1482 h126 h111
      c.hyp125 1 c.mem_calC.1 c.mem_calC.2.2 hL1 hUc hconf (by omega)
    have hb := hB c.hyp125 L c h3 hk hnorm hO
    omega

section ThreeRankPosCertificates


theorem seventeen_eighteen_holds
    (D : Data G) (V₀ V : Subgroup G)
    (h17_1 : ∀ hV : Hyp125 D V₀ V, R17_1At D V₀ V hV)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h162 : W3Thm162Ext G)
    (h126 : R126 D) (h117 : C117 D V₀ V) (h869 : F08.R869 D)
    (h1214 : F12.R1214 D) (h4128 : W4Lem12_8) (h77 : Inputs1719.W4Lem7_7)
    (hrow : Inputs1719.W4Thm11_1Row .ONan) (h82 : F08.R82 D) (h880 : F08.R880 D)
    (hKS1 : Inputs1719.K_SporadicThreePermutingLe (CFSG.Open.pRank 3 D.M))
    (hONL : Inputs1719.K_ONanLattice)
    (hSg : UC6S846.SigmaStd D) :
    R17_18At D V₀ V :=
  seventeen_eighteenAS D V₀ V h17_1 hx h61 h127 (r1114_holds D hx h61) h162
    CFSG.LocalAnalysis.WeakClosure81.w3Lem148Torus_holds
    CFSG.LocalAnalysis.WeakClosure81.w3Lem148_2_holds h126
    CFSG.LocalAnalysis.WeakClosure81.w3Thm111_unconditional h117 h869
    (b17_18Bound_holds D V₀ V hx h61 h127 h1214 h4128 h117 h77 hrow)
    h82 hKS1
    (gap17_18ReductionResidual_of D V₀ V h82 h880 hKS1 hSg
      (gap17_18P_holds D V₀ V Inputs1719.k_SporadicNine_holds
        Inputs1719.k_SporadicNoncentralThree_holds))
    (Inputs1719.k_ONanDeltaAS_of_lattice hONL)

end ThreeRankPosCertificates

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
