module

public import CFSG.Quasithin.Vol2.Ch11SecOE9R
public import CFSG.Quasithin.EmptyFaithful.E22PA6
public import CFSG.Quasithin.EmptyFaithful.E22PL2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Families

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11

variable {G : Type} [Group G] [Finite G]

theorem nParam_le_one_of_l32_or_alt6
    (h : IsPSL 3 2 1 (ASInputs.FStar G) ∨ IsAlt 6 (ASInputs.FStar G)) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  rcases h with h32 | hA6
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact E22L2.nParam_le_one_of_psl2_prime (p := 7) (Or.inr rfl) le_rfl
      (CFSG.QuasithinUnique.Vol2Native.statedClassicalModel_psl_two_seven_of_three_two h32)
  · exact E2.E22N.nParam_le_one_of_alt6 hA6

theorem nParam_eq_of_typeLie
    {T : Subgroup G} (hSQ : SQTKGroup G) (hFs : IsSimpleGroup (ASInputs.FStar G))
    (hT : quasithinIsSylowTwo T) (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) {n : ℕ} (hn : 1 ≤ n)
    (hty : SecB.TypeLie n (ASInputs.FStar G)) : E1.nParam (⊤ : Subgroup G) = n :=
  SecE3.nParam_eq_of_typeLie SecE3.Lie3.e114LieCited_holds hSQ hFs hT hFT
    nParam_le_one_of_l32_or_alt6 hn hty

end CFSG.Quasithin.RonanE114
