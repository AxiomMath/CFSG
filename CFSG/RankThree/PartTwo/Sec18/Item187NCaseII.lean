module

public import CFSG.RankThree.PartTwo.Sec18.Item187RLemma
public import CFSG.RankThree.PartTwo.Sec18.SylowPlane
public import CFSG.RankThree.PartTwo.Sec18.Item187NLayer
public import CFSG.RankThree.PartTwo.Sec18.Item187NSuz
public import CFSG.RankThree.PartTwo.Sec18.Item187NFacts
public import CFSG.RankThree.PartTwo.Sec18.Item187NLower
public import CFSG.RankThree.PartTwo.Sec18.Item189StepProofO2Direct

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)


variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G} {X : Subgroup G}

theorem MinCex.not_commutator_le_of_all (h1812 : Item181_2) (h184 : Item184_1)
    (h186 : Item186H) (hX : MinCex A M H c X) :
    ¬ ⁅X, Subgroup.zpowers c⁆ ≤ CFSG.Open.pCoreOf 2 X := by
  have hH := hX.sec18H
  have hcA := hX.c_mem_A
  have hAH : A ≤ H :=
    (le_sup_right.trans le_sup_left :
        A ≤ inSubgroup perfectResidual H ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M)).trans
      (le_of_eq hH.mem_scriptH.2.1.symm)
  have hcH : c ∈ H := hAH hcA
  have hCH : ⁅CFSG.Open.pCoreOf 2 H, Subgroup.zpowers c⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro q hq z hz
    have hqH : q ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hq
    have hzH : z ∈ H := Subgroup.zpowers_le.mpr hcH hz
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hqH hzH) (H.inv_mem hqH)) (H.inv_mem hzH)
  refine hX.not_commutator_le (orderOf_eq_three_of_sec18H h184 hH) (hX.pCoreOf_le_S h186) ?_
  rw [commutator_pCoreOf_inf_eq h1812 hH]
  exact normalizer_le_of_le_normalizer h186 hH hX.hyp187
    (commutator_ne_bot h184 h186 hH hX.hyp187) hCH (le_normalizer_commutator h1812 hH)

theorem MinCex.exists_suzuki_component (h1812 : Item181_2) (h184 : Item184_1)
    (h186 : Item186H) (hX : MinCex A M H c X) (hns : ¬ Group.IsSolvable ↥X) :
    ∃ K : Subgroup (NSolY X), IsComponent K ∧ (∃ n, CFSG.Blueprint.SuzukiModel ↥K 2 n) ∧
      K.map (cAct X hX.c_mem_normalizer).toMonoidHom = K ∧
      ∃ z ∈ K, cAct X hX.c_mem_normalizer z ≠ z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hl : layer (NSolY X) ≠ ⊥ :=
    layer_ne_bot_of_not_isSolvable (pCore_NSolY X) hX.not_three_dvd_Y hX.rank_Y
      (not_isSolvable_nsolY X hns)
  have hY := hX.layer_sup_sylowImage_eq_top h186 hl
  have hσ := cAct_pow_three X hX.c_mem_normalizer hX.c_pow_three
  have hσ1 : cAct X hX.c_mem_normalizer ≠ 1 :=
    cAct_ne_one X hX.c_mem_normalizer (hX.not_commutator_le_of_all h1812 h184 h186)
  obtain ⟨K, hK, hz⟩ := exists_component_not_fixed (pCore_NSolY X) hX.not_three_dvd_Y
    (isPGroup_sylowImage (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M))) hY _ hσ hσ1
  exact ⟨K, hK, suzukiModel_of_isComponent hX.isKGroup_Y hX.not_three_dvd_Y (pCore_NSolY X) hK,
    isComponent_map_eq_of_suzuki hX.isKGroup_Y hX.not_three_dvd_Y (pCore_NSolY X)
      (hX.rank_Y 5 (by norm_num) (by norm_num)) _ hσ hK, hz⟩

theorem MinCex.false_of_pCore_eq_bot (h1812 : Item181_2) (h184 : Item184_1)
    (h1842 : Item184_2) (h186 : Item186H) (hX : MinCex A M H c X)
    (hns : ¬ Group.IsSolvable ↥X)
    (hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := hX.c_mem_normalizer
  have hc3 := hX.c_pow_three
  obtain ⟨K, hK, ⟨n, hSz⟩, hinv, z, hzK, hz⟩ := hX.exists_suzuki_component h1812 h184 h186 hns
  obtain ⟨π, hπ, hker, hπmk, hπα⟩ := exists_restrict_hom X hc K hinv
  have hα1 : restrictAut (cAct X hc) K hinv ≠ 1 :=
    restrictAut_ne_one _ K hinv ⟨z, hzK, hz⟩
  have hα3 : restrictAut (cAct X hc) K hinv ^ 3 = 1 :=
    restrictAut_pow_three _ K hinv (cAct_pow_three X hc hc3)
  obtain ⟨yK, hyK5⟩ := exists_orderOf_eq_five_of_suzukiModel hSz
  obtain ⟨y, hy5, hymem⟩ := exists_order_five_preimage X (yb := (yK : NSolY X))
    (by rw [Subgroup.orderOf_coe]; exact hyK5)
  have hyK : nsolMk X y ∈ K := (Subgroup.zpowers_le.mpr yK.2) hymem
  have hyPre : (y : G) ∈ nsolPre X K := mem_nsolPre.mpr ⟨y.2, hyK⟩
  have hup := card_pCoreOf_inf_centralizer_le_two189 h1812 h184 h1842 hX.sec18H hX.hyp187 hO
  have hlow := eight_le_card_inf_centralizer hc3 (P := CFSG.Open.pCoreOf 2 M)
    (Kt := nsolPre X K) (Q := CFSG.Open.pCoreOf 2 X)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
    (pCoreOf_le_nsolPre X K)
    ((nsolPre_le X K).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hc)
    ((nsolPre_le X K).trans (hX.le_M.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)))
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hX.A_le_M hX.c_mem_A))
    (mem_normalizer_nsolPre hc hinv) (hX.inf_centralizer_pCoreOf_M_le h186 (nsolPre_le X K))
    π hπ hker hSz _ hα1 hα3 hπα (y := ⟨(y : G), hyPre⟩) hy5
  omega

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
