module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBMain
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBCrit
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBL31
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBC31
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBL37
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBL324A
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBL324B
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBL324C
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBU0
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBOdd

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph

theorem lemma324One_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    Lemma324One := by
  refine lemma324One_of_aux fun G _ _ T M L Mm I H K m k hd => ?_
  refine I_factorization_aux hd (M_le_L_sup_C_aux hd fun t ht => ?_)
  obtain ⟨l, hl, c, hc, rfl⟩ := T_le_L_rPlus hd (T_acts_inner hd) t ht
  refine ⟨l, hl, ?_⟩
  have hcC : c ∈ rPlus T M L := by rw [rPlus_eq_pCoreOf hd]; exact hc
  have : l⁻¹ * (l * c) = c := by group
  rw [this]
  exact hcC.2

theorem conf4212NoSumBig_of_inputs
    (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h425 : Thm4_2_5) (h48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (hKR : KRInfGammaZero) (hLF : LocalFlip) :
    Conf4212NoSumBig := by
  have h31 : Lemma31 := lemma31_holds h37 h38 h39
  have h32 : Lemma32 := lemma32_of notC31_holds (c41Case4Of_holds h37 h38 h39)
  have hL37 : Lemma37 := lemma37_of h32 h36 h37 h38 h39 h425 h48
  have hAm : AmalgamData := amalgamData_of h31 h32 hKR
  have hU : UZeroNeBot := uZeroNeBot_of notC31_holds h22 h27
  exact conf4212NoSumBig_of_parts (lemma324One_holds h37 h38 h39)
    (notCriticalPair_of h22 h31 h32 hAm hLF)
    (notLeKernelAt_of_parts h37 h38 h39 h31 h32 hU hL37 hAm)

theorem conf4212NoSumBig_of_module_data
    (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h425 : Thm4_2_5) (h48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (h35 : Lemma35KR) (hLF : LocalFlip) :
    Conf4212NoSumBig :=
  conf4212NoSumBig_of_inputs h22 h27 h36 h37 h38 h39 h425 h48
    (kRInfGammaZero_of_module (lemma31_holds h37 h38 h39)
      (lemma32_of notC31_holds (c41Case4Of_holds h37 h38 h39)) h35) hLF

end CFSG.Quasithin.H13.Ch4.NSB
