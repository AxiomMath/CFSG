module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourGamma
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourPSub
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourOuterU34
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap19_4_Pin (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  4 < mSub V₀ → R19_2At D V₀ V p L K h → R19_3At D V₀ V p L K h →
    ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M →
    ∀ A ∈ E3.gammaSet V₀ 0 D.T, ∀ J : Subgroup G, JChoice19 D L K J →
      IsSylowIn 2 (D.T ⊓ centralizer (A : Set G)) (D.M ⊓ centralizer (A : Set G)) →
      ¬ ⁅J, A⁆ ≤ pCoreOf 2 D.M → ¬ J ≤ centralizer (E3.cClos V₀ 2 D.T : Set G) →
      (∀ g : G, InCalO 2 D.M ⊥ V₀ g → InCalO 1 D.M ⊥ V₀ g) →
      E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) ≤ 2 →
      (A ≤ (D.T ⊓ J) ⊔ pCoreOf 2 (J ⊔ D.T) ∨
        ¬ E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (L : Set G)) → False

@[expose] def Gap19_4_Orest (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (_h : Ctx19_1 D V₀ V p L K) : Prop :=
  4 < mSub V₀ → ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M →
    ∀ A ∈ E3.gammaSet V₀ 0 D.T, ∀ J : Subgroup G, JChoice19 D L K J →
      IsSylowIn 2 (D.T ⊓ centralizer (A : Set G)) (D.M ⊓ centralizer (A : Set G)) →
      ¬ ⁅J, A⁆ ≤ pCoreOf 2 D.M → ¬ J ≤ centralizer (E3.cClos V₀ 2 D.T : Set G) →
      2 < E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) →
      (J = L ⊔ K ∨ (J = L ∧ IsU3 (Bar2 L) 2)) →
      (A ≤ (D.T ⊓ J) ⊔ pCoreOf 2 (J ⊔ D.T) ∨
        ¬ E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (L : Set G)) →
      ∃ g : G, InCalO 2 D.M ⊥ V₀ g ∧ ¬ InCalO 1 D.M ⊥ V₀ g

theorem gap19_4_innerAt_of
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D)
    (h86 : W3Lem86_1 G) (h88 : W3Thm88 G) (h126 : R126 D) (hSg : UC6S846.SigmaStd D)
    (h71 : W3Lem71 G) (h8107 : F08.R8107 D) (hU : Inputs1719.K_U34OuterInv)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h93 : Thm93 V₀ D.T) (hgP : Gap19_4_Pin D V₀ V p L K h)
    (hgO : Gap19_4_Orest D V₀ V p L K h) : Gap19_4_innerAt D V₀ V p L K h := by
  intro hm h2 h3
  by_contra hN2
  have h5 : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1) h5
  have hO : ∀ g : G, InCalO 2 D.M ⊥ V₀ g → InCalO 1 D.M ⊥ V₀ g := fun g hg =>
    inCalO_one_of_inCalO_two_19 h71 D h h2 h3 hm hg
  obtain ⟨A, hA, J, hJ, hAS, hJA⟩ := exists_gammaZero_19 hTim hcat D h61 h86 h126 h hm
  have hJM : J ≤ D.M ∧ 5 ∣ Nat.card J := by
    have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
    have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
    have h5L : 5 ∣ Nat.card L := (h.p_eq ▸ h.hyp.hL.2 : 5 ∈ piSet L).2
    rcases hJ with ⟨rfl | rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨hLM, h5L⟩
    · exact ⟨hKM, UC22.InS3.UC49.five_dvd_card_of_isAlt h.hKshape⟩
    · exact ⟨sup_le hLM hKM, h5L.trans (Subgroup.card_dvd_of_le le_sup_left)⟩
  have hJC := not_le_centralizer_cClos_two_19 h.hyp.hyp125 hm hsp hN2 hJM.1 hJM.2
  by_cases hW : ¬ A ≤ (D.T ⊓ J) ⊔ pCoreOf 2 (J ⊔ D.T) ∧
      E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (L : Set G)
  · have hP : (calP19_4 D L K J A).Nonempty := by
      by_cases hU3 : J = L ∧ IsU3 (Bar2 L) 2
      · exact calP19_4_nonempty_of_outer_U34 hU D h hA hJ hU3 hW.1
      · exact calP19_4_nonempty_of_outer D h hA hJ hU3 hW.1 hW.2
    obtain ⟨Y, hY⟩ := hP
    have hmem := calP19_4_subset_calPMTA D h8107 hsp h hJ hY
    rw [calPMTA_eq_empty_19 hTim hcat D h66 h88 h.hyp.hyp125 hm h93 hA hAS] at hmem
    exact hmem
  · have hres : A ≤ (D.T ⊓ J) ⊔ pCoreOf 2 (J ⊔ D.T) ∨
        ¬ E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (L : Set G) := by
      by_cases hin : A ≤ (D.T ⊓ J) ⊔ pCoreOf 2 (J ⊔ D.T)
      · exact Or.inl hin
      · exact Or.inr fun hτ => hW ⟨hin, hτ⟩
    by_cases hq : E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) ≤ 2
    · exact hgP hm h2 h3 hN2 A hA J hJ hAS hJA hJC hO hq hres
    · by_cases hrest : J = L ⊔ K ∨ (J = L ∧ IsU3 (Bar2 L) 2)
      · obtain ⟨g, hg2, hg1⟩ := hgO hm hN2 A hA J hJ hAS hJA hJC (by omega) hrest hres
        exact hg1 (hO g hg2)
      · exact hq (mQuot_le_two_19 D h hA hJ hrest)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
