module

public import CFSG.Quasithin.Recognition.St84.Basic
public import CFSG.Quasithin.Recognition.St84.J2Borel
public import CFSG.Quasithin.Recognition.St84.J2Chart
public import CFSG.Quasithin.Recognition.St84.J2VertexS
import CFSG.GroupTheory.PCore.PCoreOfIndex

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
  CFSG.Quasithin.A312J2 CFSG.Quasithin.F112R.St84.Heis CFSG.LieType.BorelTits
  CFSG.Sporadic.SmallOddCore

variable {G : Type} [Group G]

private theorem J2LocalData.card_vertex_left {L1 L2 S : Subgroup G}
    (h1 : VS3 L1) (hD : J2LocalData L1 L2 S) : Nat.card L1 = 384 := by
  rw [card_eq_six_mul_of_vs3 h1, hD.card_left]
  norm_num

private theorem card_borelOf_left [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hD : J2LocalData L1 L2 S) :
    Nat.card ↥(borelOf L1 S) = 128 := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_vs3_va5 hF h1 h2
  have hcardL1 : Nat.card L1 = 384 := J2LocalData.card_vertex_left h1 hD
  have hcardS : Nat.card S = 2 ^ 7 := J2LocalData.card_S hF h1 h2 hD
  have hS1L : S ≤ L1 := J2LocalData.S_le_left hF h1 h2 hD
  have hlt : borelOf L1 S < L1 := F1.lt_borelOf hR
  have hSB : S ⊓ L1 ≤ borelOf L1 S := F1.sylow_le_borelOf L1 S
  have hrelS : (S ⊓ L1).relIndex L1 = 3 := by
    rw [inf_eq_left.mpr hS1L]
    have h := Subgroup.relIndex_mul_card (H := S) (K := L1)
    rw [inf_eq_left.mpr hS1L, hcardS, hcardL1] at h
    omega
  have hmul := Subgroup.relIndex_mul_relIndex (H := S ⊓ L1) (K := borelOf L1 S) (L := L1)
    hSB hlt.le
  have hne : (borelOf L1 S).relIndex L1 ≠ 1 := by
    intro h1'
    exact hlt.not_ge (Subgroup.relIndex_eq_one.mp h1')
  have hdiv : (borelOf L1 S).relIndex L1 ∣ 3 :=
    ⟨_, by rw [Nat.mul_comm, hmul, hrelS]⟩
  have hrel3 : (borelOf L1 S).relIndex L1 = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h | h
    · exact absurd h hne
    · exact h
  have hcard := Subgroup.relIndex_mul_card (H := borelOf L1 S) (K := L1)
  rw [inf_eq_left.mpr (F1.borelOf_le L1 S), hrel3, hcardL1] at hcard
  omega

private theorem J2LocalData.card_bigB [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hD : J2LocalData L1 L2 S) :
    Nat.card ↥(bigB L2 L1 S) = 384 := by
  obtain ⟨eB⟩ := J2LocalData.nonempty_mulEquiv_borel hF h1 h2 hD
  rw [Nat.card_congr eB.toEquiv, ← J2Y.normalizer_eq_inf]
  exact J2Y.card_normalizer

private theorem J2LocalData.card_parabolic_left [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hD : J2LocalData L1 L2 S) :
    Nat.card ↥(L1 ⊔ bigB L2 L1 S) = 1152 := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_vs3_va5 hF h1 h2
  have hBL1 : bigB L2 L1 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (F1.bigB_le_normalizer_left hR.symm).2
  have hBcard : Nat.card ↥(bigB L2 L1 S) = 384 := J2LocalData.card_bigB hF h1 h2 hD
  have hcardL1 : Nat.card L1 = 384 := J2LocalData.card_vertex_left h1 hD
  have hInfCard : Nat.card ↥(L1 ⊓ bigB L2 L1 S) = 128 := by
    rw [CFSG.Quasithin.bigB_comm L1 L2 S, F1.inf_bigB_eq_borelOf hR]
    exact card_borelOf_left hF h1 h2 hD
  have h := CFSG.Quasithin.EmptyFaithfulMultiple.L1547.card_sup_mul_card_inf
    (H := bigB L2 L1 S) (K := L1) hBL1
  rw [inf_comm (bigB L2 L1 S) L1, hInfCard, hBcard, hcardL1,
    sup_comm (bigB L2 L1 S) L1] at h
  have h' : Nat.card ↥(L1 ⊔ bigB L2 L1 S) * 128 = 1152 * 128 := by
    calc Nat.card ↥(L1 ⊔ bigB L2 L1 S) * 128 = 384 * 384 := h
      _ = 1152 * 128 := by norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

private theorem J2LocalData.relIndex_parabolic_left [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hD : J2LocalData L1 L2 S) :
    L1.relIndex (L1 ⊔ bigB L2 L1 S) = 3 := by
  have hcardL1 : Nat.card L1 = 384 := J2LocalData.card_vertex_left h1 hD
  have hcardP : Nat.card ↥(L1 ⊔ bigB L2 L1 S) = 1152 :=
    J2LocalData.card_parabolic_left hF h1 h2 hD
  have h := Subgroup.relIndex_mul_card (H := L1) (K := L1 ⊔ bigB L2 L1 S)
  rw [inf_eq_left.mpr le_sup_left, hcardL1, hcardP] at h
  omega

theorem J2LocalData.nonempty_mulEquiv_left [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hD : J2LocalData L1 L2 S) :
    Nonempty (↥(L1 ⊔ bigB L2 L1 S) ≃* Q1M ⋊[AJ.subtype] ↥AJ) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSL : S ≤ L2 := J2LocalData.S_le_right hF h1 h2 hD
  have hS1L : S ≤ L1 := J2LocalData.S_le_left hF h1 h2 hD
  have hcardS : Nat.card S = 2 ^ 7 := J2LocalData.card_S hF h1 h2 hD
  have hR : Hyp111R L1 L2 S := hyp111R_of_vs3_va5 hF h1 h2
  have hBL1 : bigB L2 L1 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (F1.bigB_le_normalizer_left hR.symm).2
  have hcardP : Nat.card ↥(L1 ⊔ bigB L2 L1 S) = 1152 :=
    J2LocalData.card_parabolic_left hF h1 h2 hD
  have hcore : pCoreOf 2 (L1 ⊔ bigB L2 L1 S) = pCoreOf 2 L1 :=
    CFSG.GroupTheory.pCoreOf_eq_of_not_dvd_relIndex le_sup_left
      (sup_le Subgroup.le_normalizer hBL1)
      (by rw [J2LocalData.relIndex_parabolic_left hF h1 h2 hD]; norm_num)
  obtain ⟨eModel⟩ := hD.nonempty_mulEquiv_model hF h1 h2
  obtain ⟨eY3⟩ := J2Model.nonempty_mulEquiv_Y3
  obtain ⟨eC2⟩ := J2Model.nonempty_C2_equiv_Y3
  obtain ⟨Φ, hΦS⟩ := exists_chartMap_of_mulEquiv ((MulEquiv.subgroupCongr hD.sup_eq).symm.trans
    ((eModel.trans eY3.symm).trans eC2.symm)) hF.1.h2.sylow
  have hQS : pCoreOf 2 L1 ≤ S ⊓ L1 :=
    CFSG.Quasithin.St84.pCoreOf_le_of_isSylowTwoOf hF.1.h1.sylow
  have hS1card : Nat.card ↥(S ⊓ L1) = 2 ^ 7 := by
    rw [inf_eq_left.mpr hS1L]
    exact hcardS
  have hidx : (S ⊓ L2 ⊓ L1).relIndex (S ⊓ L2) ≤ 2 := by
    rw [inf_assoc, inf_eq_left.mpr (le_inf hSL hS1L), inf_eq_left.mpr hSL,
      Subgroup.relIndex_self]
    norm_num
  have hN : borelOf L2 S ≤ Subgroup.normalizer (L1 : Set G) := hF.1.h1.borel_le
  obtain ⟨χ, -, ⟨β, hβBorel, hβ3, hActsβ⟩, ⟨t, htS2, hActst⟩, -⟩ :=
    J2Model.exists_heisChart (L1 := L1) (L2 := L2) (S := S) Φ hΦS hD.card_left hQS hS1card
      hidx hN
  have hβP : β ∈ L1 ⊔ bigB L2 L1 S :=
    (le_sup_right : bigB L2 L1 S ≤ L1 ⊔ bigB L2 L1 S)
      (((le_sup_left : borelOf L2 S ≤ borelOf L2 S ⊔ borelOf L1 S).trans
        (le_sup_left : borelOf L2 S ⊔ borelOf L1 S ≤ bigB L2 L1 S)) hβBorel)
  have htP : t ∈ L1 ⊔ bigB L2 L1 S :=
    (le_sup_right : bigB L2 L1 S ≤ L1 ⊔ bigB L2 L1 S)
      ((le_sup_right : S ≤ bigB L2 L1 S) htS2.1)
  have hQP : pCoreOf 2 L1 ≤ L1 ⊔ bigB L2 L1 S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L1).trans le_sup_left
  have hPQ : L1 ⊔ bigB L2 L1 S ≤
      Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    (sup_le Subgroup.le_normalizer hBL1).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L1)
  have hχβ : parAct hPQ χ ⟨β, hβP⟩ = βM := parAct_eq_of_actsAs hβP hActsβ
  have hχt : parAct hPQ χ ⟨t, htP⟩ = τM := parAct_eq_of_actsAs htP hActst
  have hchar : CharTwo (L1 ⊔ bigB L2 L1 S) := by
    have h := F1.parabolic_charTwo hR
    rwa [← CFSG.Quasithin.bigB_comm L1 L2 S] at h
  have hC : (L1 ⊔ bigB L2 L1 S) ⊓
      Subgroup.centralizer ((pCoreOf 2 L1) : Set G) ≤ pCoreOf 2 L1 := by
    simpa only [CharTwo, hcore] using hchar
  exact nonempty_mulEquiv_heisModel hQP hPQ hcardP hC χ hβP hβ3 hχβ htP hχt

theorem isParabolicAmalgamOfGroup_j2_of_j2LocalData [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hD : J2LocalData L1 L2 S) :
    IsParabolicAmalgamOfGroup (f112Amalgam L2 L1 S)
      (fun Y _ => Nonempty (Y ≃* quasithinJ2)) := by
  classical
  refine ⟨↥CFSG.Sporadic.J2.J, inferInstance,
    ⟨(quasithinJ2MulEquivNative.trans CFSG.Sporadic.J2.nativeEquiv).symm⟩,
    j2CtxA.S, j2CtxA.Y 3, j2CtxA.Y 2, J2Y.isYAmalgamPair, ?_, ?_, ?_⟩
  · obtain ⟨e⟩ := hD.nonempty_mulEquiv_model hF h1 h2
    obtain ⟨f⟩ := J2Model.nonempty_mulEquiv_Y3
    exact ⟨e.trans f.symm⟩
  · obtain ⟨e⟩ := hD.nonempty_mulEquiv_borel hF h1 h2
    exact ⟨(MulEquiv.subgroupCongr (parabolic_inf_eq_bigB_of_vs3_va5 hF h1 h2)).trans e⟩
  · obtain ⟨e⟩ := hD.nonempty_mulEquiv_left hF h1 h2
    obtain ⟨f⟩ := J2Model.nonempty_Y2_equiv
    exact ⟨e.trans f.symm⟩

end CFSG.Quasithin.F112R.St84
