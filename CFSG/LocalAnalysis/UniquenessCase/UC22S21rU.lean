module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22tc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenGen
import CFSG.LocalAnalysis.WeakClosure81.EightTwelveBridge
import CFSG.LocalAnalysis.UniquenessCase.UC22Main1
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22qv
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
import CFSG.Quasithin.Background.E3Gen
import CFSG.Quasithin.Background.RonanE111MemE1
import CFSG.Quasithin.Background.C126NatDMin
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rHpEqMul
public import CFSG.Holt.General.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22tb
public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenOneUncond
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E2TwoProofDefs
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecBNPCaseS
public import CFSG.Quasithin.Vol2.Ch11SecBTCIso
public import CFSG.Quasithin.Vol2.Ch11StatementsE
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
import CFSG.Quasithin.Background.C1PackC126B
import CFSG.Quasithin.Background.C1PackNat
import CFSG.Quasithin.Background.C1PackSolvBasic
import CFSG.Quasithin.Background.E2Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC
open CFSG.Quasithin (IsSylowIn conjSubgroup conjSubgroup_one rk card_eq_two_pow_of_isPGroup
  twoResidual)
open CFSG.Quasithin.E3 (wClos cClos sParam)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Thm111)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_22Use (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ H₁ ∈ hSet D.T D.M, ∀ H₂ ∈ hSet D.T D.M, c.L0 ≤ H₁ ⊓ H₂ →
    (∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G)) →
    H₁ ⊓ H₂ ≤ D.M

theorem uc22s21ru_contra (D : Data G) (Ch : Choice2011 G) (h111 : W3Thm111 G)
    (h2122 : S21_22Use D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch)
    (hV1 : InCalV1 D.M D.T c.V) (hm2 : MBarGT D.M ⊥ c.V 2) {j : ℕ}
    (hj : MBarGT D.M ⊥ c.V (1 + j))
    (hL0W : c.L0 ≤ normalizer
      ((wClos c.V j D.T ⊓ centralizer (wClos c.V j D.T : Set G) : Subgroup G) : Set G)) :
    False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup G := wClos c.V j D.T with hWdef
  set ZW : Subgroup G := W ⊓ centralizer (W : Set G) with hZWdef
  have hL0 : c.L0 ∈ calL D.T D.M := c.hL0.1
  have hL0M : ¬ c.L0 ≤ D.M := fun h => hL0.2.2.1.2.1 (sup_le h D.sylowM.le)
  have hL0Z : c.L0 ≤ centralizer (D.Z : Set G) := c.hLge.trans (CFSG.Open.IsSubnormal.le c.hL.2)
  have hH₁ : normalizer (D.Z : Set G) ∈ hSet D.T D.M :=
    ⟨fun t ht => centralizer_le_normalizer _ (uc22main1_T_le_centralizer D ht),
      fun h => c.hC ((centralizer_le_normalizer _).trans h),
      D.standing.charTwo _ ⟨D.Z, uc22main1_Z_ne_bot D, D.sylowM.isPGroup.to_le (uc22main1_Z_le_T D),
        rfl⟩⟩
  have hVel : IsElemAbelian 2 c.V := hV1.1.2.2.2
  have hUT : D.U ≤ D.T := by
    obtain ⟨hU1, -⟩ := uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM
    exact (hU1.trans inf_le_left).trans (uc22p22e_pCoreOf_le_T D)
  have hVT : c.V ≤ D.T := c.hVU.trans hUT
  have hjV : j < rk ↥c.V := by
    have h1 := uc22p22ta_card_le hj
    rw [card_eq_two_pow_of_isPGroup (uc22p22e_isPGroup_of_elem hVel)] at h1
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
    omega
  have hVW : c.V ≤ W :=
    CFSG.Quasithin.E3.le_wClos_of_mQuot_le hVel 1 hVT (by rw [conjSubgroup_one])
      (by rw [conjSubgroup_one, CFSG.Quasithin.E3.mQuot_self]; exact Nat.zero_le _) hjV
  have hW2 : IsPGroup 2 W := D.sylowM.isPGroup.to_le (uc22p22ta_wClos_le c.V j D.T)
  have hZW : ZW ≠ ⊥ := by
    have hWne : W ≠ ⊥ := fun h => c.hVne (le_bot_iff.1 (h ▸ hVW))
    haveI : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).2 hWne
    haveI := hW2.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥(center ↥W))
    intro hbot
    have hzmem : ((z : ↥W) : G) ∈ ZW := by
      refine ⟨(z : ↥W).2, mem_centralizer_iff.2 fun h hh => ?_⟩
      exact congrArg Subtype.val ((mem_center_iff.1 z.2) ⟨h, hh⟩)
    rw [hbot, mem_bot] at hzmem
    exact hz (Subtype.ext (Subtype.ext hzmem))
  have hH₂ : normalizer (ZW : Set G) ∈ hSet D.T D.M :=
    ⟨fun t ht => uc22p22ta_mem_normalizer_center
        (CFSG.Quasithin.E3.normalizer_le_normalizer_wClos (V := c.V) (i := j) D.T
          (le_normalizer ht)),
      fun h => hL0M (hL0W.trans h), D.standing.charTwo _ ⟨ZW, hZW, hW2.to_le inf_le_left, rfl⟩⟩
  have hZC : (D.Z : Set G) ⊆ (cClos c.V (j + 1) D.T : Set G) := by
    intro z hz
    refine ⟨uc22main1_Z_le_T D hz, mem_centralizer_iff.2 fun w hw => ?_⟩
    exact ((mem_centralizer_iff.1 (uc22main1_T_le_centralizer D
      (uc22p22ta_wClos_le c.V (j + 1) D.T hw))) z hz).symm
  have hlt : j + 1 < sParam hVel :=
    PartTwo.TwelveShort.lt_sParam_of_mBarGT D h111 hV1 hm2 (by rw [Nat.add_comm]; exact hj)
  have hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((normalizer (D.Z : Set G) ⊓ X : Subgroup G) : Set G) *
        ((normalizer (ZW : Set G) ⊓ X : Subgroup G) : Set G) := by
    intro X hXM hTX hInF
    have h := uc22s21rhp_eq_mul_of_or hVel (uc22p22ta_isSylowIn D hTX) (i := j) (j := 1) le_rfl
      hInF hlt
    apply Set.Subset.antisymm
    · intro x hx
      rw [h] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      refine ⟨a, ⟨?_, ha.1⟩, b, ⟨uc22p22ta_mem_normalizer_center hb.2, hb.1⟩, rfl⟩
      exact centralizer_le_normalizer _ (Subgroup.centralizer_le hZC ha.2)
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact X.mul_mem ha.2 hb.2
  have hL012 : c.L0 ≤ normalizer (D.Z : Set G) ⊓ normalizer (ZW : Set G) :=
    le_inf (hL0Z.trans (centralizer_le_normalizer _)) hL0W
  exact hL0M (hL012.trans (h2122 h1930 c.toCtx21 _ hH₁ _ hH₂ hL012 hfX))

theorem s22_9_of_F229ASU (D : Data G) (Ch : Choice2011 G) (h111 : W3Thm111 G)
    (h2122 : S21_22Use D Ch) (hn3 : H1930 D → ∀ c : Ctx22b D Ch, 3 ≤ c.n) (hF : F229AS D Ch)
    (hV : S22_V D Ch) : S22_9 D Ch := by
  classical
  intro h1930 c hgt
  have hn := hn3 h1930 c
  have hV1 : InCalV1 D.M D.T c.V := (hV h1930 c).1.1
  have hVel : IsElemAbelian 2 c.V := hV1.1.2.2.2
  have hm2 : MBarGT D.M ⊥ c.V 2 := uc22br4_mBarGT_mono _ _ _ hgt (by omega)
  have hlt : 0 + c.n < sParam hVel :=
    PartTwo.TwelveShort.lt_sParam_of_mBarGT D h111 hV1 hm2
      (uc22br4_mBarGT_mono _ _ _ hgt (by omega))
  rcases uc22p22tc_dich hVel (uc22p22ta_isSylowIn D le_sup_right) (hF h1930 c) hlt with h2 | h1
  · exact uc22s21ru_contra D Ch h111 h2122 h1930 c hV1 hm2 (j := 0)
      (uc22br4_mBarGT_mono _ _ _ hgt (by omega))
      fun l hl => uc22p22ta_mem_normalizer_center (h2 ((le_sup_left : c.L0 ≤ c.L0 ⊔ D.T) hl))
  · rw [Nat.zero_add, Subgroup.commutator_comm] at h1
    have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1
    have hL0R : c.L0 ≤ twoResidual (c.L0 ⊔ D.T) :=
      CFSG.Quasithin.C126.Nat.le_twoResidual_of_perfect le_sup_left c.hL0.1.2.1
    refine uc22s21ru_contra D Ch h111 h2122 h1930 c hV1 hm2 (j := c.n)
      (by rw [Nat.add_comm]; exact hgt)
      fun l hl => centralizer_le_normalizer _ (mem_centralizer_iff.2 fun z hz => ?_)
    exact mem_centralizer_iff.1 (hcent (hL0R hl)) z ⟨uc22p22ta_wClos_le c.V c.n D.T hz.1, hz.2⟩

theorem s22_9_of_ASU
    (D : Data G) (Ch : Choice2011 G) (h2122 : S21_22Use D Ch)
    (hn3 : H1930 D → ∀ c : Ctx22b D Ch, 3 ≤ c.n) (hU : UniqueMaxL0T D Ch)
    (hE : InE229 D Ch) (hV : S22_V D Ch) : S22_9 D Ch :=
  s22_9_of_F229ASU D Ch CFSG.LocalAnalysis.WeakClosure81.w3Thm111_unconditional h2122 hn3
    (f229AS_of_uniqueMax D Ch hU hE) hV

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
