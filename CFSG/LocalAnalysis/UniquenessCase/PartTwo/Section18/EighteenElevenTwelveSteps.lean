module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenElevenZ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenElevenW
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwelveK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TwoNatNoSwap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TwoNatInvolution

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section EighteenEleven


theorem eighteen_eleven_of_inputs (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h127 : R127 D) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h66 : UC6.R6_6 D) (h126 : R126 D) (h1114 : R1114 D) (h111 : W3Thm111 G)
    (h183 : W3Thm183 G) (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h67 : S17.R17_67At D V₀ V) (h1742 : S17.R17_42At D V₀ V)
    (h6b : R18_6bAt D V₀ V p L h) (h7b : R18_7bAt D V₀ V p L h)
    (h8 : R18_8At D V₀ V p L h) (h9 : R18_9At D V₀ V p L h)
    (h10 : R18_10At D V₀ V p L h)
    (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D) (h72 : F07.R72 D) (hK35 : UCK.K35w)
    (h109 : Inputs1719.UC2_10_9 D) :
    R18_11At D V₀ V p L h := by
  have hm3 : MBarGT D.M V₀ V 3 :=
    h1669 (by
      have h2 : Nat.card V₀ ≤ 2 :=
        (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small
      omega)
  exact eighteen_eleven D h h127 hx h61 h66 h126 h1114 h111 h183 h1669
    (gap_18_11_V0_of_df D h h67 hm3 h6b h7b h8 h9 h10 Inputs1719.k_Sp4TwoNat_noSwap_holds)
    (gap_18_11_Z_of D h h1742 h6b h7b h1669 h8 h9 h10 Inputs1719.k_Sp4TwoNat_noSwap_holds hSg
      h638 h72 hK35 h109)
    (gap_18_11_W_of D h h1742 h6b h7b h1669 h8 h9 h10 Inputs1719.k_Sp4TwoNat_noSwap_holds hSg
      h638 h72 hK35 h109 h111 Inputs1719.k_Sp4TwoNat_involution_holds)

end EighteenEleven

section EighteenTwelve


theorem eighteen_twelve_of_inputs (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h127 : R127 D) (h17_66_1 : S17.R17_66_1At D V₀ V)
    (h1742 : S17.R17_42At D V₀ V) (h641 : S17.R17_64_1At D V₀ V)
    (h642 : S17.R17_64_2At D V₀ V) (h643 : S17.R17_64_3At D V₀ V)
    (h184 : R18_4At D V₀ V p L) (h6b : R18_6bAt D V₀ V p L h)
    (h7b : R18_7bAt D V₀ V p L h) (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h8 : R18_8At D V₀ V p L h) (h9 : R18_9At D V₀ V p L h)
    (h10 : R18_10At D V₀ V p L h) :
    R18_12At D V₀ V p L h :=
  eighteen_twelve D h h127 h17_66_1
    (gap_18_12_K_of D h h1742 h641 h642 h643 h184 h6b h7b h1669 h8 h9 h10
      )

end EighteenTwelve

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
