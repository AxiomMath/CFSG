module

public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.RankThree.GF2n.Stroth80.Conclusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

section D3

private theorem center_SL_two_eq_bot_of_charTwo' {K : Type*} [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hc)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hcA, hc1]
  simp [Matrix.one_apply]

theorem nonempty_mulEquiv_psl2GF_of_isSLModel {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (h : IsSLModel 2 (2 ^ m) X) : Nonempty (X ≃* CFSG.AGLEmbedding.PSL2GF 2 m) := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hm
      hKcard
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hcardF : Fintype.card K = Fintype.card (GaloisField 2 m) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKcard,
      GaloisField.card 2 m (by omega)]
  let iso : K ≃+* GaloisField 2 m := FiniteField.ringEquivOfCardEq hcardF
  let eP : Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq center_SL_two_eq_bot_of_charTwo'.symm)
  exact ⟨e.trans ((specialLinearGroupEquivStatedSL 2 K).symm.trans
    (eP.trans (CFSG.GorensteinWalter.psl2RingEquiv iso)))⟩

variable {H : Type} [Group H] [Finite H] {M Q Z B : Subgroup H}

end D3

end CFSG.RankThree.GF2n.Smith81
