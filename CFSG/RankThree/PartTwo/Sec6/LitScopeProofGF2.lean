module

public import CFSG.RankThree.PartTwo.Sec6.LitScopeProof
import CFSG.RankThree.PartTwo.Sec18.Item183NMProofTools
public import CFSG.RankThree.PartTwo.Sec6.Item611Res5ProofE81
public import CFSG.RankThree.PartTwo.Sec6.Item611Res5ProofE81V

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

namespace LitScope

theorem exists_normal_elemAbelian_of_e27 (h : GF2TypeE27) {G : Type} [Group G] [Finite G]
    (hst : PartTwoStanding G) {t : G} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) {E : Subgroup G}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEt : E ≤ Subgroup.centralizer ({t} : Set G)) :
    ∃ V : Subgroup G, V ≤ Subgroup.centralizer {t} ∧
      Subgroup.centralizer {t} ≤ Subgroup.normalizer (V : Set G) ∧
      CFSG.Assembly.IsElemAbelian 2 V ∧ 4 ≤ Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  set C := Subgroup.centralizer ({t} : Set G) with hC
  set F := inSubgroup (CFSG.pCore 2) C with hF
  have hfit : CFSG.generalizedFitting C = CFSG.pCore 2 C :=
    Sec18.Item183NMProof.generalizedFitting_eq_of_pCoreOf_le hst.charTwoType
      (Res611Res5.isTwoLocal_centralizer hto) le_rfl (CFSG.LieType.BorelTits.pCoreOf_le 2 C)
  have hFfit : inSubgroup CFSG.generalizedFitting C = F := by
    rw [hF, inSubgroup, inSubgroup, hfit]
  have hF2 : IsPGroup 2 F := CFSG.pCore_isPGroup.map _
  have hsymp : ¬ CFSG.Open.GLASymplecticType F := by
    rw [← hFfit]
    exact h G hst t hto E hEe hE27 hEt
  have hex : ∃ A : Subgroup F, A.Characteristic ∧ IsMulCommutative A ∧ ¬ IsCyclic A := by
    by_contra hne
    push Not at hne
    exact hsymp ⟨hF2, fun A hAc hAab => hne A hAc hAab⟩
  obtain ⟨A, hAc, hAab, hAnc⟩ := hex
  have hA2 : IsPGroup 2 A := hF2.to_subgroup A
  refine ⟨Res611Res5.omegaOneIn A hAab, ?_, Res611Res5.le_normalizer_omegaOneIn A hAab,
    Res611Res5.isElemAbelian_omegaOneIn A hAab,
    Res611Res5.four_le_card_omegaOneIn A hAab hA2 hAnc⟩
  rintro _ ⟨a, -, rfl, -⟩
  exact Subgroup.map_subtype_le _ a.2

end LitScope

theorem item611E81V_of_e27 (h : GF2TypeE27) : Item611E81V := by
  intro G _ _ hst A _ _ c _ _ L _ _ E _ _ T _ _ _ _ t _ _ ht1 ht2 hD
  exact LitScope.exists_normal_elemAbelian_of_e27 h hst ht1 ht2 hD.1 hD.2.1 inf_le_right

end CFSG.RankThree.PartTwo.Sec6
