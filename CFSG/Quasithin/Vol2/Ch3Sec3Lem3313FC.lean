module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313FB
public import CFSG.Quasithin.Vol2.Ch1Eight
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch3Sec3Setup

public section

namespace CFSG.Quasithin.H13.Lem3313F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13.Ch3Sec3

variable {G : Type} [Group G] [Finite G]

theorem false_of_faithful (h128 : Lemma128Two) (h323 : Stmt3_2_3)
    (h36 : A36ForSQTK) (h3228 : Vol2.Ch10.TmpL6_3_2_2_eight) (h316 : Theorem316Statement)
    (hD37 : D37) (hD36c : D36c) (hI5 : Insp5a) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {T M L D H K : Subgroup G} (h : Hyp331 G T M L D)
    (huniq : IsUniqueM (L ⊔ T) M) (hH : InH T H) (hO : pCoreOf 2 (H ⊔ D) ≠ ⊥)
    (hK : K ∈ cComp (H ⊔ D)) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hTK : ¬ T ≤ Subgroup.normalizer (K : Set G)) (hKf : quasithinIsFaithfulLocal T K) {q : ℕ}
    (hq : q.Prime) (h24 : q % 24 = 11 ∨ q % 24 = 13)
    (hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 q 1) :
    False := by
  have := h.simple
  have hne : K ≠ conjClosure K T := fun he =>
    hTK (by rw [he]; exact le_normalizer_conjClosure K T)
  have hlt : K < conjClosure K T := lt_of_le_of_ne (le_conjClosure K T) hne
  have hmax : quasithinIsMaximalLocal T K := by
    rcases lemma_1_2_8_three h128 h.qtke h.simple h.nonabelian hKf.1 hlt with hm | hA5
    · exact hm
    · exact (not_fiveShape_of_psl2 hq h24 hmod (Or.inr (Or.inr (Or.inl hA5)))).elim
  obtain ⟨⟨hmaxK, -⟩, -, -⟩ := h323 G T K h.simple h.nonabelian h.qtke h.sylow hmax hKf hKq
  have hTsyl : IsSylowTwoOf T (H ⊔ D) := ⟨hH.1.trans le_sup_left, h.sylow.1,
    Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow (hH.1.trans le_sup_left)⟩
  have hHD : H ⊔ D ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot (qtkeCore_of_cat h.nonabelian h.qtke).1 h37
      h38 hO hTsyl hK
  by_cases hLT : L ⊔ T ≤ Subgroup.normalizer (conjClosure K T : Set G)
  ·
    have he : Subgroup.normalizer (conjClosure K T : Set G) = M := huniq.2 _ ⟨hmaxK, hLT⟩
    apply h.counter
    rw [h.ND]
    exact sup_le h.TM (le_sup_right.trans (hHD.trans he.le))
  ·
    obtain ⟨V₀, c⟩ := exists_ctx h323 h36 h3228 h.simple h.nonabelian h.qtke h.sylow hmax hKf hKq
      hne ⟨le_sup_right, h.Lmax.1.2.2.2⟩ hLT
    exact false_of_ctx h316 hD37 hD36c hI5 h37 h38 c hq h24 hmod

end CFSG.Quasithin.H13.Lem3313F
