module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourOrestSwap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap19_4_PinRoot (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  4 < mSub V₀ → R19_2At D V₀ V p L K h → R19_3At D V₀ V p L K h →
    ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M →
    ∀ A ∈ E3.gammaSet V₀ 0 D.T, ∀ J : Subgroup G, JChoice19 D L K J →
      IsSylowIn 2 (D.T ⊓ centralizer (A : Set G)) (D.M ⊓ centralizer (A : Set G)) →
      ¬ ⁅J, A⁆ ≤ pCoreOf 2 D.M → ¬ J ≤ centralizer (E3.cClos V₀ 2 D.T : Set G) →
      (∀ g : G, InCalO 2 D.M ⊥ V₀ g → InCalO 1 D.M ⊥ V₀ g) →
      E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) = 1 →
      (A ≤ (D.T ⊓ J) ⊔ pCoreOf 2 (J ⊔ D.T) ∨
        ¬ E1.tauOf (J ⊔ D.T) D.T A ≤ normalizer (L : Set G)) →
      ((L.subgroupOf D.M).Normal ∨ ¬ A ≤ normalizer (L : Set G) ∨
        ⁅L, A⁆ ≤ pCoreOf 2 L ∨ ⁅K, A⁆ ≤ pCoreOf 2 K) → False

theorem gap19_4_Pin_of_root (D : Data G)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hgR : Gap19_4_PinRoot D V₀ V p L K h) :
    Gap19_4_Pin D V₀ V p L K h := by
  intro hm h2 h3 hN2 A hA J hJ hAS hJA hJC hO hq hres
  by_cases h0 : E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) = 0
  · exact (mQuot_ne_zero_19 D h hA hJ hJA) h0
  by_cases h1 : E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) = 1
  · by_cases hdisj : (L.subgroupOf D.M).Normal ∨ ¬ A ≤ normalizer (L : Set G) ∨
        ⁅L, A⁆ ≤ pCoreOf 2 L ∨ ⁅K, A⁆ ≤ pCoreOf 2 K
    · exact hgR hm h2 h3 hN2 A hA J hJ hAS hJA hJC hO h1 hres hdisj
    · have hLn : ¬ (L.subgroupOf D.M).Normal := fun hN => hdisj (Or.inl hN)
      have hAL : A ≤ normalizer (L : Set G) := by
        by_contra hAL
        exact hdisj (Or.inr (Or.inl hAL))
      have hLA : ¬ ⁅L, A⁆ ≤ pCoreOf 2 L := fun hle => hdisj (Or.inr (Or.inr (Or.inl hle)))
      have hKA : ¬ ⁅K, A⁆ ≤ pCoreOf 2 K :=
        fun hle => hdisj (Or.inr (Or.inr (Or.inr hle)))
      have hJeq : J = L ⊔ K := by
        rcases hJ with ⟨-, hLN⟩ | hJK
        · exact absurd hLN hLn
        · exact hJK.1
      refine pin_one_twoSided_19 D hSg h hm hN2 hA hLn ?_ hAL hLA hKA
      rwa [hJeq] at h1
  · have h2eq : E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) = 2 := by omega
    obtain ⟨g, hg2, hg1⟩ := pin_two_19 D hSg h hm hN2 hA hJ hJA h2eq hres
    exact hg1 (hO g hg2)

theorem gap19_4_Orest_holds
    (D : Data G) (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) : Gap19_4_Orest D V₀ V p L K h := by
  classical
  intro hm hN2 A hA J hJ hAS hJA hJC hq hcase hres
  rcases hcase with hJLK | ⟨hJL, hU3⟩
  · subst hJLK
    have hLn : ¬ (L.subgroupOf D.M).Normal := by
      rcases hJ with ⟨h1, -⟩ | ⟨-, hLn⟩
      · rcases h1 with heq | heq
        · exact absurd heq (sup_ne_left_right_19 h).1
        · exact absurd heq (sup_ne_left_right_19 h).2
      · exact hLn
    by_cases hτ : E1.tauOf (L ⊔ K ⊔ D.T) D.T A ≤ normalizer (L : Set G)
    · refine orest_LK_noswap_19 D hSg h hm hN2 hA hLn hJA hq ?_ hτ
      rcases hres with hin | hswap
      · exact hin
      · exact absurd hτ hswap
    · exact orest_LK_swap_19 D hSg h hm hN2 hA hLn hJA hq hτ
  · have hJA' : ¬ ⁅L, A⁆ ≤ pCoreOf 2 D.M := by rwa [hJL] at hJA
    have hq' : 2 < E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ D.T)) := by rwa [hJL] at hq
    have hres' : A ≤ (D.T ⊓ L) ⊔ pCoreOf 2 (L ⊔ D.T) ∨
        ¬ E1.tauOf (L ⊔ D.T) D.T A ≤ normalizer (L : Set G) := by rwa [hJL] at hres
    have hJ' : JChoice19 D L K L := hJL ▸ hJ
    have hLN : (L.subgroupOf D.M).Normal := by
      rcases hJ' with ⟨-, hLN⟩ | ⟨heq, -⟩
      · exact hLN
      · exact absurd heq.symm (sup_ne_left_right_19 h).1
    have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
    have hTN : D.T ≤ normalizer (L : Set G) :=
      D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLN)
    have hin : A ≤ (D.T ⊓ L) ⊔ pCoreOf 2 (L ⊔ D.T) := by
      rcases hres' with hin | hswap
      · exact hin
      · exact absurd ((E1.tauOf_le (L ⊔ D.T) D.T A).trans hTN) hswap
    have hle : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ D.T)) ≤ 2 :=
      mQuot_le_two_U34_inner_19 D h hA hLN hU3 hin
    exact absurd hq' (by omega)

theorem gap19_4_innerAt_of_root
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D)
    (h86 : W3Lem86_1 G) (h88 : W3Thm88 G) (h126 : R126 D) (hSg : UC6S846.SigmaStd D)
    (h71 : W3Lem71 G) (h8107 : F08.R8107 D) (hU : Inputs1719.K_U34OuterInv)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h93 : Thm93 V₀ D.T)
    (hgR : Gap19_4_PinRoot D V₀ V p L K h) : Gap19_4_innerAt D V₀ V p L K h :=
  gap19_4_innerAt_of hTim hcat D h61 h66 h86 h88 h126 hSg h71 h8107 hU h h93
    (gap19_4_Pin_of_root D hSg h hgR) (gap19_4_Orest_holds D hSg h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
