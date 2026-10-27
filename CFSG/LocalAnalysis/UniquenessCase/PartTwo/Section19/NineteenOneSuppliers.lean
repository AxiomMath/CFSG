module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenThreeY
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEightTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenOneNineAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzAutRankHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexNormalHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourPinRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEightThreeGap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W3Lem71Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ACandidateU34Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34InvolutionGen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSeven
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.GapSingleCompHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwoEFive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Certified


theorem r19_8At_of (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (h3 : R19_3At D V₀ V p L K h)
    (h4 : R19_4At D V₀ V p L K h) (h6 : R19_6At D V₀ V p L K h) (h7 : R19_7At D V₀ V p L K h)
    (h77 : Inputs1719.W4Lem7_7) (hU34 : Inputs1719.K_U34ACand) (h68 : S17.R17_68At D V₀ V)
    (hF : ((L.subgroupOf D.M).Normal ∧ (K.subgroupOf D.M).Normal ∧ InFSq 2 (L ⊔ D.T) ∧
        InFSq 2 (K ⊔ D.T)) ∨ InFSq 2 (L ⊔ K ⊔ D.T)) : R19_8At D V₀ V p L K h := by
  have h81 := nineteen_eight_one D hx h61 h127 h1114 h162 hTor h1482 h h3 h6 h7 h77 hU34
  have h82 := nineteen_eight_two D hx h61 h127 h1114 h126 h h7 h81
    (normalizer_wTwo_le_19 D hx h61 h127 h1114 hSg h h7 h81 (hF.imp_left fun h' => h'.2.2))
  have h83 := nineteen_eight_three D hx h61 h127 h1114 h126 h h3 h4 h81 h82
    (gap19_8_3At_holds D hx h61 h127 h1114 h126 h h68 hF)
  exact ⟨h81, h82, h83, nineteen_eight_four D h hSg h3 (nineteen_five D V₀ V p L K h h4) h83⟩

theorem r19_1At_of_suppliers
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h66 : UC6.R6_6 D) (h86 : W3Lem86_1 G) (h88 : W3Thm88 G) (h126 : R126 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (hSg : UC6S846.SigmaStd D) (h869 : F08.R869 D) (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS)
    (h43c : W3Lem45_2Chief)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp19 D V₀ V p L)
    (h1214 : F12.R1214 D) (h128 : W4Lem12_8)
    (h36 : Inputs1719.W4Lem3_6)
    (h42 : S17.R17_42At D V₀ V) (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V) (h68 : S17.R17_68At D V₀ V)
    (h93 : Thm93 V₀ D.T)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D) (h171 : S17.R17_1At D V₀ V h.hyp125)
    (h1310 : Inputs1719.W4Thm13_10) (h1513 : R15_13 D) (h1219 : D.sig = D.sig1)
    (hU34g : Inputs1719.K_U34InvolutionGen)
    (h8107 : F08.R8107 D)
    (h77 : Inputs1719.W4Lem7_7) (hU34O : Inputs1719.K_U34OuterInv) :
    R19_1At D V₀ V p L h := by
  have hMin : Inputs1719.K_SU3MinDegree := Inputs1719.k_SU3MinDegree_holds
  have hg7 : Gap19_7_SingleComponent := gap19_7_SingleComponent_holds hU34g
  have h3 : ∀ K (hK : Ctx19_1 D V₀ V p L K), R19_3At D V₀ V p L K hK := fun K hK =>
    nineteen_three_At hTim hcat D h61 h66 h86 h88 h126 h127 hSg hK h93
      (gap19_3At_holds D hK h68)
  have h2 : ∀ K (hK : Ctx19_1 D V₀ V p L K), R19_2At D V₀ V p L K hK := fun K hK =>
    have hP : S17.P17_64_2 D 5 2 :=
      p17_64_2_of_ctx19_1 D hK h42 h641 h642 h643 h68
    nineteen_two D hK hSg h76 h614 h171 hP
      (gap19_2_E_of_ctx D hK hSg (k_eq_two_of_borel hK h171 hP) hP
        Inputs1719.k_A5U34BorelQuotient_holds h68)
  have h4 : ∀ K (hK : Ctx19_1 D V₀ V p L K), R19_4At D V₀ V p L K hK := fun K hK =>
    nineteen_four_At D hK h5_11 h5_13 h66 h86 hTim hcat (h2 K hK) (h3 K hK)
      (gap19_4_innerAt_of_root hTim hcat D h61 h66 h86 h88 h126 hSg w3Lem71_holds h8107 hU34O
        hK h93 (gap19_4_PinRoot_holds hTim hcat D h66 h88 hSg h8107 hU34O hK h93))
  have h7 : ∀ K (hK : Ctx19_1 D V₀ V p L K), R19_7At D V₀ V p L K hK := fun K hK =>
    nineteen_seven_of_gap D hK (h2 K hK) (h3 K hK)
      (nineteen_five D V₀ V p L K hK (h4 K hK)) h1310 h1513 hx h61 h126 h127 h1214 hSg h1219
      hg7
  have h8 : ∀ K (hK : Ctx19_1 D V₀ V p L K), R19_8At D V₀ V p L K hK := fun K hK =>
    r19_8At_of D hx h61 h126 h127 h1114 h162 hTor h1482 hSg hK (h3 K hK) (h4 K hK)
      (nineteen_six hK (h2 K hK) (h3 K hK) (h4 K hK) hSg h869) (h7 K hK) h77
      k_U34ACand_holds h68
      (inFSq_19_cases hK Inputs1719.k_L2SzAutRank_holds Inputs1719.k_U3IndexNormal_holds
        h43c)
  exact r19_1At_of_final D hx h61 h127 h1214 h128 hMin h36 h h42 h641 h642 h643 h68 h8 hSg
    h3 h4

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
