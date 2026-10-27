module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.McL
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43
public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofEightG2
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem noType424At3_of_centCharThree {S P : Type} [Group S] [Finite S] [Group P] (e : S ≃* P)
    (hP : ∀ z : P, orderOf z = 3 →
      IsCharacteristicP 3 ↥(Subgroup.centralizer ({z} : Set P))) :
    Coordinator.CoverCent.NoType424At3 S := by
  intro s hs hHas
  have hso : orderOf (e s) = 3 := by rw [MulEquiv.orderOf_eq]; exact hs
  rw [Item424Res2.fixSub_conj_eq_centralizer_singleton] at hHas
  exact Sec11.KS11Lie3Proof.not_hasType424_of_isCharacteristicP
    (RankThree.PartTwo.Sec14.isCharacteristicP_of_mulEquiv'
      (CFSG.AGLEmbeddingD2.Wilson.Census424Rest.centralizerEquivOfMulEquiv e s).symm
      (hP (e s) hso)) hHas

theorem noType424At3_McL :
    Coordinator.CoverCent.NoType424At3 (Blueprint.NativeSporadic.Carrier .McL) := by
  have eM : Blueprint.NativeSporadic.Carrier .McL ≃* CFSG.Sporadic.Schreier.mclP :=
    CFSG.Sporadic.Schreier.mclPermEquiv
  have : Finite (Blueprint.NativeSporadic.Carrier .McL) := Finite.of_equiv _ eM.symm.toEquiv
  exact noType424At3_of_centCharThree eM
    fun z hz => Sec6.ThreeLocalSporProof.centCharThree_mclP z hz

theorem noType424At3_U43 :
    Coordinator.CoverCent.NoType424At3 (projSU 4 3 1) := by
  have : Finite (projSU 4 3 1) :=
    Nat.finite_of_card_ne_zero
      (by rw [Sec6.BThreeCensus.card_projSU_four_three]; norm_num)
  intro s hs hHas
  rw [Item424Res2.fixSub_conj_eq_centralizer_singleton] at hHas
  exact Sec11.KS11Lie3Proof.not_hasType424_of_isCharacteristicP
    (Sec6.kCentCharThreeU43_holds s hs) hHas

theorem noType424At3_G2
    {S : Type} [Group S] (hS : Blueprint.ChevalleyExceptionalModel S .G2 3 1) :
    Coordinator.CoverCent.NoType424At3 S := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hS
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  let E : S ≃* adjointGroup Tag.G2 K :=
    φ.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  have : Finite S := Finite.of_equiv _ E.symm.toEquiv
  intro s hs hHas
  have hs3 : s ^ 3 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have hT := hHas.of_mulEquiv (Sec11.KS11Lie2Proof.fixSubCongr E (MulAut.conj s))
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj] at hT
  refine Sec11.KS11Lie3Proof.not_hasType424_fixSub_g2_three (z := E s) ?_ ?_ hT
  · intro h1
    exact hs1 (E.injective (h1.trans (map_one E).symm))
  · rw [← map_pow, hs3, map_one]

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
