module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenThreeHigh
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
public import CFSG.GroupTheory.StronglyPEmbeddedRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sh
public import CFSG.Quasithin.Background.C124Perf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem normalizer_wTwo_le_19 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (h7 : R19_7At D V₀ V p L K h)
    (h81 : R19_8_1At D V₀ V p L K h)
    (hF : (InFSq 2 (L ⊔ D.T) ∧ InFSq 2 (K ⊔ D.T)) ∨ InFSq 2 (L ⊔ K ⊔ D.T)) :
    normalizer (E3.wClos V 2 D.T : Set G) ≤ D.M := by
  have hV₀ : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hV := h.hyp.isElemAbelian
  have hp125 := h.hyp.hyp125
  have hm : 3 < mBar D.M V₀ V hV := nineteen_seven_gt_three D h h7
  have hrk : 2 < rk ↥V := lt_of_lt_of_le (by omega) (hm.le.trans (mBar_le_rk hV hp125.pairFacts.le))
  have hH := (weakClosureSetting_of_hyp125 D hx h61 h127 h1114 hp125 hV₀).hyp6H
  have hkr : ((2 : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (ENat.natCast_lt_natCast.2 (by omega)) h81.1
  have hno : ∀ g : G, ¬ InCalO1 2 D.M V₀ V g := by
    intro g hg
    have hmem : conjSubgroup V g ∈ calO 2 D.M V₀ V := ⟨g, rfl, hg.1⟩
    rw [h81.2.1 2 (by omega)] at hmem
    exact hmem
  have h5 : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1) h5
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have h5L : 5 ∣ Nat.card L := (h.p_eq ▸ h.hyp.hL.2 : 5 ∈ piSet L).2
  have h5K : 5 ∣ Nat.card K := UC22.InS3.UC49.five_dvd_card_of_isAlt h.hKshape
  have halt : ∀ H : Subgroup G, D.T ≤ H → InFSq 2 H →
      H ≤ normalizer (E3.wClos V 0 D.T : Set G) ∨
        CFSG.Quasithin.twoResidual H ≤ centralizer (E3.cClos V 2 D.T : Set G) := by
    intro H hTH hFH
    rcases TwelveEighteen.twelve_eighteen_three_of_no_calO1 hH hV₀ (i := 0) (n := 2) (k := 2)
      le_rfl hkr (by omega) hno (TwelveShort.isSylowIn_of_le D hTH) hFH with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Subgroup.le_centralizer_iff.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1))
  have hres : ∀ {J H : Subgroup G}, J ≤ H → ⁅J, J⁆ = J → J ≤ CFSG.Quasithin.twoResidual H :=
    fun hJH hJ => (CFSG.Quasithin.C124.twoResidual_eq_self_of_perfect' hJ).symm.le.trans
      (CFSG.Quasithin.F6.twoResidual_mono hJH)
  have hcase1 : ∀ J : Subgroup G, J ≤ D.M → 5 ∣ Nat.card J →
      J ≤ centralizer (E3.cClos V 2 D.T : Set G) →
      normalizer (E3.wClos V 2 D.T : Set G) ≤ D.M := by
    intro J hJM h5J hJC g hg
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 5 h5J
    have hxo : orderOf (x : G) = 5 := (Subgroup.orderOf_coe x).trans hx
    exact CFSG.GroupTheory.mem_of_pRank_pos_of_le_inf_conjSubgroup Nat.prime_five hsp
      (le_inf hJM (TwelveTwentyTwo.le_conjSubgroup_of_le_centralizer_cClos hp125 hV₀ hrk hJC hg))
      (CFSG.LocalAnalysis.UniquenessCase.UCK.N588A.one_le_pRank Nat.prime_five
        (Subgroup.zpowers_le.2 x.2) (by rw [Nat.card_zpowers, hxo]))
  have hcase2 : L ≤ normalizer (E3.wClos V 0 D.T : Set G) →
      K ≤ normalizer (E3.wClos V 0 D.T : Set G) →
      normalizer (E3.wClos V 2 D.T : Set G) ≤ D.M := by
    intro hLN hKN
    have hcomm : ⁅L, K⁆ ≤ pCoreOf 2 D.M :=
      ((calC_commutator_le_of_ne h.hyp.hL.1 h.hK (Ne.symm h.hne)).trans inf_le_left).trans
        (UC22.P22s.pCoreOf_le_of_isSubnormal h.hyp.hL.1.1)
    have hU : UniqueMax D.M (D.M ⊓ normalizer (E3.wClos V 0 D.T : Set G)) :=
      uniqueMax_of_commutator_le_pCoreOf D h61 h5 inf_le_left (le_inf hLM hLN) (le_inf hKM hKN)
        hcomm h.hK.2.1 h5K h5L
    have hW0le : V ≤ E3.wClos V 0 D.T := s15_13A_le_wClos hp125
    have hW0ne : E3.wClos V 0 D.T ≠ ⊥ := fun hbot =>
      hp125.pairFacts.ne_bot (le_bot_iff.1 (hbot ▸ hW0le))
    have hW02 : IsPGroup 2 (E3.wClos V 0 D.T) :=
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM).2.1.to_le (E3.wClos_le 0 D.T)
    have hN0 : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
      uc22p22p_le_of_uniqueMax hU ⟨E3.wClos V 0 D.T, hW0ne, hW02, rfl⟩ inf_le_right
    have e0 : E3.wClos V 0 D.T = E3.wClos V 0 (E3.wClos V 1 D.T) :=
      wClos_eq_wClos_succ hV 0 D.T (by omega)
    have e1 : E3.wClos V 1 D.T = E3.wClos V 1 (E3.wClos V 2 D.T) :=
      wClos_eq_wClos_succ hV 1 D.T (by omega)
    have h21 : normalizer (E3.wClos V 2 D.T : Set G) ≤
        normalizer (E3.wClos V 1 D.T : Set G) := by
      rw [e1]
      exact E3.normalizer_le_normalizer_wClos _
    have h10 : normalizer (E3.wClos V 1 D.T : Set G) ≤
        normalizer (E3.wClos V 0 D.T : Set G) := by
      rw [e0]
      exact E3.normalizer_le_normalizer_wClos _
    exact h21.trans (h10.trans hN0)
  rcases hF with ⟨hFL, hFK⟩ | hFLK
  · rcases halt (L ⊔ D.T) le_sup_right hFL with hLN | hLC
    · rcases halt (K ⊔ D.T) le_sup_right hFK with hKN | hKC
      · exact hcase2 (le_sup_left.trans hLN) (le_sup_left.trans hKN)
      · exact hcase1 K hKM h5K ((hres le_sup_left h.hK.2.1).trans hKC)
    · exact hcase1 L hLM h5L ((hres le_sup_left h.hyp.hL.1.2.1).trans hLC)
  · rcases halt (L ⊔ K ⊔ D.T) le_sup_right hFLK with hN | hC
    · exact hcase2 ((le_sup_left.trans le_sup_left).trans hN)
        ((le_sup_right.trans le_sup_left).trans hN)
    · exact hcase1 L hLM h5L ((hres (le_sup_left.trans le_sup_left) h.hyp.hL.1.2.1).trans hC)

theorem nineteen_eight_two (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) (h126 : R126 D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h7 : R19_7At D V₀ V p L K h) (h81 : R19_8_1At D V₀ V p L K h)
    (hN2 : normalizer (E3.wClos V 2 D.T : Set G) ≤ D.M) : R19_8_2At D V₀ V p L K h := by
  have hV₀ : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hV := h.hyp.isElemAbelian
  have hm : 3 < mBar D.M V₀ V hV := nineteen_seven_gt_three D h h7
  have hk : D.k ≤ 2 := TwelveSeven.k_le_two D
  by_contra hne
  have hgt : 2 + D.k < mBar D.M V₀ V hV := by
    have : mBar D.M V₀ V hV ≠ 4 := hne
    omega
  have hkr : ((2 + D.k : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (ENat.natCast_lt_natCast.2 (by omega)) h81.1
  have hno : ∀ g : G, ¬ InCalO1 (2 + D.k) D.M V₀ V g := by
    intro g hg
    have hmem : conjSubgroup V g ∈ calO (2 + D.k) D.M V₀ V := ⟨g, rfl, hg.1⟩
    rw [h81.2.1 (2 + D.k) hgt] at hmem
    exact hmem
  exact S18.not_normalizer_wClos_le_of_no_calO1 D hx h61 h127 h1114 h126 h.hyp.hyp125 hV₀
    hkr hgt hno hN2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
