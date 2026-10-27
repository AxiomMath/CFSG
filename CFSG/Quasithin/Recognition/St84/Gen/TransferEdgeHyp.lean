module

public import CFSG.Quasithin.Recognition.St84.TransferVertex

import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
import CFSG.Quasithin.Recognition.St84.Gen.TransferL2Torus
import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {H : Type} [Group H] [Finite H]

private theorem f112ll_borel_edge_le_K {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    borelOf (oTwoPrime (f112saP2' L1 L2 S)) (S ⊓ f112saK L1 L2 S) ≤
      f112saK L1 L2 S := by
  classical
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  obtain ⟨D, hD, hDcard⟩ := f112_exists_torus_X2 hF (by omega) h2
  have hDX2 : D ≤ f112saX2 L1 L2 S := hD.trans inf_le_left
  have hDleK : D ≤ f112saK L1 L2 S := hDX2.trans le_sup_right
  let T := S ⊓ f112saK L1 L2 S
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  change borelOf Lβ T ≤ f112saK L1 L2 S
  have hTleLβ : T ≤ Lβ := f112sa_T_le_oTwoPrime_P2'_of_hyp111R hF hR
  have hDleLβ : D ≤ Lβ :=
    hDX2.trans ((f112sa_X2_le_oTwoRes L1 L2 S).trans
      (f112sa_oTwoRes_le_oTwoPrime_P2'_of_isL2Quot hn h2))
  have hDnt : D ≤ Subgroup.normalizer (T : Set H) := by
    have h := (hDX2.trans (f112sa_X2_le_bigB L1 L2 S)).trans
      ((f112sa_bigB_le_normalizer_K hF).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (f112saK L1 L2 S)))
    rwa [f112ll_pCoreOf_K_eq hF hm hn h1 h2] at h
  have hborel : borelOf Lβ T = Lβ ⊓ Subgroup.normalizer (T : Set H) := by
    rw [borelOf, inf_eq_left.mpr hTleLβ]
  rw [hborel]
  have hcard : Nat.card ↥(T ⊔ D) =
      Nat.card ↥(Lβ ⊓ Subgroup.normalizer (T : Set H)) := by
    have hT2 : IsPGroup 2 ↥T := hF.1.h1.pgroup.to_le inf_le_left
    have hoddD : Odd (Nat.card D) := by
      rw [hDcard]
      exact Nat.Even.sub_odd Nat.one_le_two_pow
        (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two (by omega)) odd_one
    obtain ⟨k, hkT⟩ := IsPGroup.iff_card.mp hT2
    have hcop : Nat.Coprime (Nat.card T) (Nat.card D) := by
      rw [hkT]
      exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hoddD)
    have hTD : Nat.card ↥(T ⊔ D) = Nat.card T * Nat.card D :=
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer T D hDnt
        (Subgroup.disjoint_of_coprime_natCard hcop)
    have hrel : (T.subgroupOf Lβ).relIndex
        (Subgroup.normalizer ((T.subgroupOf Lβ : Subgroup ↥Lβ) : Set ↥Lβ)) = 2 ^ n - 1 :=
      relIndex_normalizer_of_isL2Quot (by omega) (f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2)
        (f112sa_T_sylow_oTwoPrime_P2'_of_hyp111R hF hR)
    have hmul := Subgroup.relIndex_mul_card (H := T.subgroupOf Lβ)
      (K := Subgroup.normalizer ((T.subgroupOf Lβ : Subgroup ↥Lβ) : Set ↥Lβ))
    rw [inf_eq_left.mpr Subgroup.le_normalizer, hrel] at hmul
    have hcardSub : Nat.card ↥(T.subgroupOf Lβ) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTleLβ).toEquiv
    have hcardNorm : Nat.card ↥(Subgroup.normalizer
        ((T.subgroupOf Lβ : Subgroup ↥Lβ) : Set ↥Lβ)) =
        Nat.card ↥(Lβ ⊓ Subgroup.normalizer (T : Set H)) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hTleLβ,
        ← Subgroup.card_subtype Lβ ((Subgroup.normalizer (T : Set H)).subgroupOf Lβ),
        Subgroup.subgroupOf_map_subtype, inf_comm]
    rw [hcardSub, hcardNorm] at hmul
    rw [hTD, hDcard, mul_comm]
    exact hmul
  have hTDle : T ⊔ D ≤ Lβ ⊓ Subgroup.normalizer (T : Set H) :=
    sup_le (le_inf hTleLβ Subgroup.le_normalizer) (le_inf hDleLβ hDnt)
  rw [← Subgroup.eq_of_le_of_card_ge hTDle (le_of_eq hcard.symm)]
  exact sup_le inf_le_right hDleK

private theorem f112ll_charTwo_edge {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    CharTwo (oTwoPrime (f112saP1' L1 L2 S) ⊔ (S ⊓ f112saK L1 L2 S) ⊔
      borelOf (oTwoPrime (f112saP2' L1 L2 S)) (S ⊓ f112saK L1 L2 S)) := by
  classical
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hborel := f112ll_borel_edge_le_K hF hm hn h1 h2
  let T := S ⊓ f112saK L1 L2 S
  let Eα := f112saP1' L1 L2 S
  let Qα := pCoreOf 2 Eα
  let Lα := oTwoPrime Eα
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let X := Lα ⊔ T ⊔ borelOf Lβ T
  change X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set H) ≤ pCoreOf 2 X
  have hT_Lα : T ≤ Lα := f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF hR
  have hT_Eα : T ≤ Eα := hT_Lα.trans (oTwoPrime_le Eα)
  have hX_Eα : X ≤ Eα :=
    sup_le (sup_le (oTwoPrime_le Eα) hT_Eα) (hborel.trans (f112saK_le_P1' L1 L2 S))
  have hQp : IsPGroup 2 Qα := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Eα
  have hQ_X : Qα ≤ X :=
    (le_oTwoPrime_of_isPGroup hQp (CFSG.LieType.BorelTits.pCoreOf_le 2 Eα)).trans
      (le_sup_left.trans le_sup_left)
  have hEα_NQ : Eα ≤ Subgroup.normalizer (Qα : Set H) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Eα
  have hLα_NQ : Lα ≤ Subgroup.normalizer (Qα : Set H) :=
    (oTwoPrime_le Eα).trans hEα_NQ
  have hX_NQ : X ≤ Subgroup.normalizer (Qα : Set H) :=
    sup_le (sup_le hLα_NQ (hT_Eα.trans hEα_NQ))
      ((hborel.trans (f112saK_le_P1' L1 L2 S)).trans hEα_NQ)
  have hQ_coreX : Qα ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQ_X hX_NQ hQp
  intro x hx
  obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
  exact hQ_coreX (f112sa_charTwo_P1'_of_hyp111R hF hR
    ⟨hX_Eα hxX, Subgroup.centralizer_le hQ_coreX hxC⟩)

private theorem f112ll_o2_edge {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S) ⊔ oTwoPrime (f112saP2' L1 L2 S) ⊔
      (S ⊓ f112saK L1 L2 S)) = ⊥ := by
  classical
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let T := S ⊓ f112saK L1 L2 S
  let E' := oTwoPrime (f112saP1' L1 L2 S) ⊔ oTwoPrime (f112saP2' L1 L2 S) ⊔ T
  let G₀ := L1 ⊔ L2 ⊔ S
  change pCoreOf 2 E' = ⊥
  have hBG : bigB L1 L2 S ≤ G₀ := by
    rw [bigB]
    exact sup_le (sup_le ((F1.borelOf_le L1 S).trans (le_sup_left.trans le_sup_left))
      ((F1.borelOf_le L2 S).trans (le_sup_right.trans le_sup_left))) le_sup_right
  have hP1' : f112saP1' L1 L2 S ≤ G₀ := by
    refine (f112sa_P1'_le_P1 hF).trans ?_
    rw [f112sa_P1_eq_oTwoRes_sup_bigB hF]
    exact sup_le ((oTwoRes_le L1).trans (le_sup_left.trans le_sup_left)) hBG
  have hP2' : f112saP2' L1 L2 S ≤ G₀ := by
    refine (f112sa_P2'_le_P2 hF).trans ?_
    rw [f112sa_P2_eq_oTwoRes_sup_bigB hF]
    exact sup_le ((oTwoRes_le L2).trans (le_sup_right.trans le_sup_left)) hBG
  have hE'G0 : E' ≤ G₀ :=
    sup_le (sup_le ((oTwoPrime_le (f112saP1' L1 L2 S)).trans hP1')
      ((oTwoPrime_le (f112saP2' L1 L2 S)).trans hP2')) (inf_le_left.trans le_sup_right)
  have hB_NLα : bigB L1 L2 S ≤
      Subgroup.normalizer (oTwoPrime (f112saP1' L1 L2 S) : Set H) := fun b hb =>
    mem_normalizer_oTwoPrime (f112sa_P1_le_normalizer_P1' hF
      ((le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S) hb))
  have hB_NLβ : bigB L1 L2 S ≤
      Subgroup.normalizer (oTwoPrime (f112saP2' L1 L2 S) : Set H) := fun b hb =>
    mem_normalizer_oTwoPrime (f112sa_P2_le_normalizer_P2' hF
      ((le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S) hb))
  have hB_NT : bigB L1 L2 S ≤ Subgroup.normalizer (T : Set H) := by
    have h := (f112sa_bigB_le_normalizer_K hF).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (f112saK L1 L2 S))
    rwa [f112ll_pCoreOf_K_eq hF hm hn h1 h2] at h
  have hB_NE' : bigB L1 L2 S ≤ Subgroup.normalizer (E' : Set H) :=
    F1.le_normalizer_sup (F1.le_normalizer_sup hB_NLα hB_NLβ) hB_NT
  have hLα_NE' : oTwoPrime (f112saP1' L1 L2 S) ≤ Subgroup.normalizer (E' : Set H) :=
    (le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer
  have hLβ_NE' : oTwoPrime (f112saP2' L1 L2 S) ≤ Subgroup.normalizer (E' : Set H) :=
    (le_sup_right.trans le_sup_left).trans Subgroup.le_normalizer
  have hP1_NE' : oTwoRes L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (E' : Set H) :=
    sup_le ((f112sa_oTwoRes_le_oTwoPrime_P1'_of_isL2Quot hm h1).trans hLα_NE') hB_NE'
  have hP2_NE' : oTwoRes L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (E' : Set H) :=
    sup_le ((f112sa_oTwoRes_le_oTwoPrime_P2'_of_isL2Quot hn h2).trans hLβ_NE') hB_NE'
  have hG0_NE' : G₀ ≤ Subgroup.normalizer (E' : Set H) :=
    sup_le (sup_le ((f112sa_L1_le_oTwoRes_sup_bigB hF).trans hP1_NE')
      ((f112sa_L2_le_oTwoRes_sup_bigB hF).trans hP2_NE'))
      ((le_sup_right : S ≤ bigB L1 L2 S).trans hB_NE')
  have hcore := CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hE'G0 hG0_NE'
  rw [hF.1.o2] at hcore
  exact le_bot_iff.mp hcore

private theorem f112ll_hyp111At_edge {L1 L2 S : Subgroup H} {m n : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Hyp111At (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hborel := f112ll_borel_edge_le_K hF hm hn h1 h2
  refine
    { finite := inferInstance
      pgroup := hF.1.h1.pgroup.to_le inf_le_left
      normalizes := ?_
      sylow := ?_
      listed := Or.inl ⟨m, by omega, f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2⟩
      borel_le := ?_
      charTwo := f112ll_charTwo_edge hF hm hn h1 h2 }
  · intro t ht
    exact mem_normalizer_oTwoPrime
      (Subgroup.le_normalizer (f112saK_le_P1' L1 L2 S (Subgroup.mem_inf.mp ht).2))
  · rw [inf_eq_left.mpr (f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF hR)]
    exact f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R hF hR
  · intro x hx
    exact mem_normalizer_oTwoPrime
      (Subgroup.le_normalizer (f112saK_le_P1' L1 L2 S (hborel hx)))

theorem f112ll_hyp111_edge {L1 L2 S : Subgroup H} {m n : ℕ} (hF : F112HypW L1 L2 S)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    Hyp111 (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) :=
  { h1 := f112ll_hyp111At_edge hF hm hn h1 h2
    h2 := by
      have h := f112ll_hyp111At_edge (L1 := L2) (L2 := L1) hF.symm hn hm h2 h1
      simpa only [f112saP1'_eq_P2'_swap L2 L1 S, f112saP2'_eq_P1'_swap L2 L1 S,
        f112saK_comm L1 L2 S] using h
    o2 := f112ll_o2_edge hF hm hn h1 h2 }

end CFSG.Quasithin.F112R.St84

end
