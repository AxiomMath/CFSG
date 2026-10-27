module

public import CFSG.Quasithin.Recognition.F112Crit.BenderLocalOf
public import CFSG.Quasithin.Recognition.F112Crit.Lemma71Of
public import CFSG.Quasithin.Recognition.F112Crit.SettingOf
public import CFSG.Quasithin.Recognition.F112Crit.Theorem64
public import CFSG.Quasithin.Recognition.F112Crit.Theorem75
public import CFSG.Quasithin.H13.F112PlusDefs
public import CFSG.Quasithin.EmptyFaithful.S152ZFMain
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7Top
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Surv10
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.D14Normal
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Background.F6Cat
public import CFSG.Quasithin.Background.F6CatSetting
public import CFSG.Quasithin.Background.F6CatTransport
public import CFSG.Quasithin.EmptyFaithful.F112F53Res
public import CFSG.Quasithin.EmptyFaithful.F112RE
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152He9Y1
public import CFSG.Quasithin.EmptyFaithful.S152N2L14C
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.H13.F112DSPartsC
public import CFSG.Quasithin.Recognition.F112J2Split
public import CFSG.Quasithin.Recognition.F112RGold
public import CFSG.Quasithin.Recognition.F112WChief
public import CFSG.Quasithin.Recognition.F112WLocal2
public import CFSG.Quasithin.Recognition.F112WValency
public import CFSG.Quasithin.Recognition.GoldschmidtF112RQ
public import CFSG.Quasithin.Recognition.GoldschmidtF112TitsBorel
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs
public import CFSG.Quasithin.Vol2.Ch5StatementsB
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.RankThree.S4Free.Statement
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import Certificates.Certificate8026Base
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.MS93 (oddGen)

open CosetGeom (nbrs γ₀ γ₁)

@[expose] def ListedNoMcL : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankOneListed K → ¬ Group.IsSolvable K →
    ¬ IsL2Quot 2 K → NoMcLaughlinCover K

@[expose] def L2Even (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L₁ L₂ S Z : Subgroup G), Setting L₁ L₂ S Z →
    VS3 L₁ ∨ VFD L₁ → IsL2Quot n (oTwoQuot ↥L₂) →
    Even (critB (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) Z) →
    4 ≤ critB (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) Z → False

theorem f112SliceFDBigPlus_of_parts (hM : ListedNoMcL)
    (h8 : L2Even 3) (h16 : L2Even 4) : CFSG.Quasithin.H13.F112SliceFDBigPlus := by
  intro G _ _ L1 L2 S hH hBig hFD hc hS
  by_cases hA5 : IsL2Quot 2 (oTwoQuot ↥L1)
  · obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hA5
    have hH' := hH.symm
    exact CFSG.Quasithin.He9.input15204F112_of_untw
      CFSG.Quasithin.Kleidman.F204.input15204F112Untw_holds G L2 L1 S hH'.1 hH'.2.1 hH'.2.2 hFD ⟨e⟩
  have hL1 : IsRankOneListed (oTwoQuot ↥L1) := hH.1.h1.listed
  have hns : ¬ Group.IsSolvable (oTwoQuot ↥L1) := fun h =>
    VBig.not_isSolvable hL1 hBig (isSolvable_vertex_of_oTwoQuot h)
  obtain ⟨n, i, hn, hK, htype⟩ := exists_isBenderQuot_of_listed hL1 hns
  have hs := setting_of_fdBig hH hFD hc hS
  have hcr := hs.toCritAmalgam
  have hcard := card_oTwoQuot_of_vFD hFD
  have hX := hs.isLocalRegGrp (oddGen_inf_borelOf_le hs.hyp (Or.inr hcard))
  rw [relIndex_borelOf_eq_five hs.hyp hcard] at hX
  have hloc := hX.isLocalReg hcr
  have hb : Even (critB (L2 ⊔ L1 ⊔ S) (P₂ L2 L1 S) (P₁ L2 L1 S)
      (omegaOneCenterOf (L1 ⊔ S ⊔ borelOf L2 S))) :=
    Nat.not_odd_iff_even.mp (corollary76 hcr hloc (by norm_num))
  have h3 := hs.three_le_critB (isQuasisimple_of_listed hL1 hns) (hM _ hL1 hns hA5)
  have hb4 : 4 ≤ critB (L2 ⊔ L1 ⊔ S) (P₂ L2 L1 S) (P₁ L2 L1 S)
      (omegaOneCenterOf (L1 ⊔ S ⊔ borelOf L2 S)) := by
    obtain ⟨k, hk⟩ := hb
    omega
  have h17 := theorem723 hcr hloc (Or.inr rfl) (hs.benderLocal hK) hb hb4
  rw [hs.card_nbrs_γ₀ hK] at h17
  rcases htype with ⟨rfl, hL2⟩ | h65
  · have hn4 : n ≤ 4 := by
      by_contra hlt
      have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_one] at h17
      omega
    interval_cases n
    · exact hA5 hL2
    · exact h8 G L2 L1 S _ hs (Or.inr hFD) hL2 hb hb4
    · exact h16 G L2 L1 S _ hs (Or.inr hFD) hL2 hb hb4
  · omega

end CFSG.Quasithin.F112Crit

end
