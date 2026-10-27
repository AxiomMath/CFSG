module

public import CFSG.Quasithin.Recognition.St84.TreeBase
public import CFSG.Quasithin.Recognition.St84.TransferVertex
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Setup
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Two
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Beta
public import CFSG.Quasithin.Background.GoldschmidtAmalgamVBase
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotA

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem card_eq_of_isSylowTwoOf_of_card_eq {T X Q : Subgroup H} (hT : IsSylowTwoOf T X)
    (hQ : IsPGroup 2 Q) {a m : ℕ} (hm : ¬ 2 ∣ m)
    (hX : Nat.card ↥X = 2 ^ a * m * Nat.card ↥Q) :
    Nat.card ↥T = 2 ^ a * Nat.card ↥Q := by
  obtain ⟨b, hb⟩ := hQ.exists_card_eq
  rw [hT.card_eq, hb, S1421QA17.twoPart_eq_of_card (n := a + b) (m := m) hm
    (by rw [hX, hb]; ring), pow_add]

theorem oTwoPrime_eq_self_of_perm3 {A T : Subgroup H} (hT : IsSylowTwoOf T A)
    (hA : Nonempty (oTwoQuot ↥A ≃* Equiv.Perm (Fin 3))) : oTwoPrime A = A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardA : Nat.card ↥A = 6 * Nat.card ↥(pCoreOf 2 A) :=
    CFSG.Quasithin.F6.GoldPair.card_eq_six_mul_pCoreOf hA
  have hcardT : Nat.card ↥T = 2 * Nat.card ↥(pCoreOf 2 A) := by
    have h := card_eq_of_isSylowTwoOf_of_card_eq (a := 1) (m := 3) hT
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A) (by norm_num)
      (by rw [hcardA]; ring)
    simpa using h
  have hTle : T ≤ oTwoPrime A :=
    CFSG.Quasithin.le_oTwoPrime_of_isPGroup hT.2.1 hT.1
  have hle : oTwoPrime A ≤ A := oTwoPrime_le A
  have hA3 : Nat.card ↥A = 3 * Nat.card ↥T := by rw [hcardA, hcardT]; ring
  have hdvd : Nat.card ↥T ∣ Nat.card ↥(oTwoPrime A) := Subgroup.card_dvd_of_le hTle
  have hdvd3 : Nat.card ↥(oTwoPrime A) ∣ 3 * Nat.card ↥T := by
    rw [← hA3]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨c, hc⟩ := hdvd
  obtain ⟨d, hd⟩ := hdvd3
  have hTpos : 0 < Nat.card ↥T := Nat.card_pos
  have hcd : c * d = 3 := by
    have h1 : Nat.card ↥T * 3 = Nat.card ↥T * (c * d) := by
      calc Nat.card ↥T * 3 = 3 * Nat.card ↥T := by ring
        _ = Nat.card ↥(oTwoPrime A) * d := hd
        _ = (Nat.card ↥T * c) * d := by rw [hc]
        _ = Nat.card ↥T * (c * d) := by ring
    exact Nat.eq_of_mul_eq_mul_left hTpos h1.symm
  have hc3 : c ∣ 3 := ⟨d, hcd.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hc3 with hc1 | hc3'
  · have hqpos : 0 < Nat.card ↥(pCoreOf 2 A) := Nat.card_pos
    have hEq : T = oTwoPrime A :=
      Subgroup.eq_of_le_of_card_ge hTle (by rw [hc, hc1, mul_one])
    have hp : IsPGroup 2 (oTwoPrime A) := hEq ▸ hT.2.1
    have hcore : oTwoPrime A ≤ pCoreOf 2 A :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle
        (le_normalizer_oTwoPrime A) hp
    have hlecard : Nat.card ↥(oTwoPrime A) ≤ Nat.card ↥(pCoreOf 2 A) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hcore)
    rw [hc, hc1, mul_one, hcardT] at hlecard
    omega
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hc3']; omega)

theorem f112sa_card_L2 {L2 : Subgroup H} (h2 : VA5 L2) :
    Nat.card ↥L2 = 60 * Nat.card ↥(pCoreOf 2 L2) := by
  rw [CFSG.Quasithin.H13.card_eq_card_oTwoQuot_mul_card_pCoreOf L2,
    IsL2Quot.card (by norm_num) h2]
  norm_num

private theorem f112sa_card_S_inf_L2 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h2 : VA5 L2) :
    Nat.card ↥(S ⊓ L2) = 4 * Nat.card ↥(pCoreOf 2 L2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := card_eq_of_isSylowTwoOf_of_card_eq (a := 2) (m := 15) hF.1.h2.sylow
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L2) (by norm_num)
    (by rw [f112sa_card_L2 h2]; ring)
  simpa using this

theorem f112sa_card_S_inf_L1 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    Nat.card ↥(S ⊓ L1) = 2 * Nat.card ↥(pCoreOf 2 L1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := card_eq_of_isSylowTwoOf_of_card_eq (a := 1) (m := 3) hF.1.h1.sylow
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L1) (by norm_num)
    (by rw [CFSG.Quasithin.F6.GoldPair.card_eq_six_mul_pCoreOf h1]; ring)
  simpa using this

theorem f112sa_card_P2_eq {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    Nat.card ↥(f112P2 L1 L2 S) = 15 * Nat.card ↥S := by
  have hP : f112P2 L1 L2 S = S ⊔ L2 := by
    rw [f112sa_P2_eq_sup hF h1, sup_comm]
  have hprod := CFSG.Quasithin.EmptyFaithfulMultiple.L1547.card_sup_mul_card_inf
    (H := S) (K := L2) hF.1.h2.normalizes
  rw [f112sa_card_S_inf_L2 hF h2, f112sa_card_L2 h2] at hprod
  have hq : 0 < 4 * Nat.card ↥(pCoreOf 2 L2) :=
    Nat.mul_pos (by norm_num) Nat.card_pos
  rw [hP]
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [hprod]; ring)

theorem f112sa_card_bigB {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    Nat.card ↥(bigB L1 L2 S) = 3 * Nat.card ↥S := by
  have h5 := f112sa_card_P2 hF h1 h2
  have h15 := f112sa_card_P2_eq hF h1 h2
  omega

theorem f112sa_card_K {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    Nat.card ↥(f112saK L1 L2 S) = 3 * Nat.card ↥(S ⊓ f112saK L1 L2 S) := by
  have hSN : S ≤ Subgroup.normalizer (f112saK L1 L2 S : Set H) :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans (f112sa_bigB_le_normalizer_K hF.toW)
  have hprod := CFSG.Quasithin.EmptyFaithfulMultiple.L1547.card_sup_mul_card_inf
    (H := S) (K := f112saK L1 L2 S) hSN
  rw [← f112sa_bigB_eq_S_sup_K hF.toW, f112sa_card_bigB hF h1 h2] at hprod
  have h : Nat.card ↥(f112saK L1 L2 S) * Nat.card ↥S =
      3 * Nat.card ↥(S ⊓ f112saK L1 L2 S) * Nat.card ↥S := by
    calc Nat.card ↥(f112saK L1 L2 S) * Nat.card ↥S
        = Nat.card ↥S * Nat.card ↥(f112saK L1 L2 S) := by ring
      _ = (3 * Nat.card ↥S) * Nat.card ↥(S ⊓ f112saK L1 L2 S) := hprod.symm
      _ = 3 * Nat.card ↥(S ⊓ f112saK L1 L2 S) * Nat.card ↥S := by ring
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

theorem f112sa_card_P2' {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    Nat.card ↥(f112saP2' L1 L2 S) = 15 * Nat.card ↥(S ⊓ f112saK L1 L2 S) := by
  have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (f112saP2' L1 L2 S : Set H) :=
    (le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S).trans
      (f112sa_P2_le_normalizer_P2' hF.toW)
  have hprod := CFSG.Quasithin.EmptyFaithfulMultiple.L1547.card_sup_mul_card_inf
    (H := bigB L1 L2 S) (K := f112saP2' L1 L2 S) hBN
  rw [inf_comm, f112sa_P2'_inf_bigB hF.toW] at hprod
  have hsup : bigB L1 L2 S ⊔ f112saP2' L1 L2 S = f112P2 L1 L2 S := by
    rw [sup_comm, f112sa_P2_eq_P2'_sup_bigB hF.toW]
  rw [hsup, f112sa_card_P2_eq hF h1 h2, f112sa_card_bigB hF h1 h2,
    f112sa_card_K hF h1 h2] at hprod
  have h : Nat.card ↥(f112saP2' L1 L2 S) * (3 * Nat.card ↥S) =
      (15 * Nat.card ↥(S ⊓ f112saK L1 L2 S)) * (3 * Nat.card ↥S) := by
    calc Nat.card ↥(f112saP2' L1 L2 S) * (3 * Nat.card ↥S)
        = (3 * Nat.card ↥S) * Nat.card ↥(f112saP2' L1 L2 S) := by ring
      _ = (15 * Nat.card ↥S) * (3 * Nat.card ↥(S ⊓ f112saK L1 L2 S)) := hprod.symm
      _ = (15 * Nat.card ↥(S ⊓ f112saK L1 L2 S)) * (3 * Nat.card ↥S) := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by norm_num) Nat.card_pos) h

private theorem f112sa_card_oTwoPrime_P2' {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    Nat.card ↥(oTwoPrime (f112saP2' L1 L2 S)) =
      60 * Nat.card ↥(pCoreOf 2 (f112saP2' L1 L2 S)) := by
  rw [CFSG.Quasithin.H13.card_eq_card_oTwoQuot_mul_card_pCoreOf,
    IsL2Quot.card (by norm_num) (f112sa_isL2Quot_oTwoPrime_P2' hF h1 h2),
    pCoreOf_oTwoPrime]
  norm_num

theorem f112sa_card_T_eq_QA {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    Nat.card ↥(S ⊓ f112saK L1 L2 S) =
      4 * Nat.card ↥(pCoreOf 2 (f112saP2' L1 L2 S)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : Nat.card ↥(oTwoPrime (f112saP2' L1 L2 S)) =
      2 ^ 2 * 15 * Nat.card ↥(pCoreOf 2 (f112saP2' L1 L2 S)) := by
    rw [f112sa_card_oTwoPrime_P2' hF h1 h2]
    norm_num
  have := card_eq_of_isSylowTwoOf_of_card_eq (a := 2) (m := 15)
    (f112sa_T_sylow_oTwoPrime_P2' hF.toW) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (by norm_num) hX
  simpa using this

theorem f112sa_oTwoPrime_P2'_eq {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    oTwoPrime (f112saP2' L1 L2 S) = f112saP2' L1 L2 S := by
  refine Subgroup.eq_of_le_of_card_ge (oTwoPrime_le _) ?_
  rw [f112sa_card_oTwoPrime_P2' hF h1 h2, f112sa_card_P2' hF h1 h2,
    f112sa_card_T_eq_QA hF h1 h2]
  omega

theorem f112sa_isL2Quot_P2' {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    IsL2Quot 2 (oTwoQuot ↥(f112saP2' L1 L2 S)) := by
  have h := f112sa_isL2Quot_oTwoPrime_P2' hF h1 h2
  rwa [f112sa_oTwoPrime_P2'_eq hF h1 h2] at h

theorem f112sa_P2'_eq_oTwoRes_sup {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    f112saP2' L1 L2 S = oTwoRes L2 ⊔ pCoreOf 2 (f112saP2' L1 L2 S) :=
  (f112sa_oTwoPrime_P2'_eq hF h1 h2).symm.trans
    (f112sa_oTwoPrime_eq_oTwoRes_sup_pCoreOf_P2' hF.toW h2
      (f112sa_isL2Quot_oTwoPrime_P2' hF h1 h2))

theorem f112sa_card_P1_eq {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    Nat.card ↥(f112P1 L1 L2 S) = 9 * Nat.card ↥S := by
  have hri : (bigB L1 L2 S).relIndex (f112P1 L1 L2 S) = 3 := by
    rw [← f112_inf_eq_bigB hF.toW]
    exact f112sa_relIndex_left hF h1 le_rfl h2
  have h := Subgroup.relIndex_mul_card (bigB L1 L2 S) (f112P1 L1 L2 S)
  rw [hri, inf_eq_left.mpr (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S),
    f112sa_card_bigB hF h1 h2] at h
  omega

theorem f112sa_card_oTwoPrime_P1' {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    Nat.card ↥(oTwoPrime (f112saP1' L1 L2 S)) =
      6 * Nat.card ↥(pCoreOf 2 (f112saP1' L1 L2 S)) := by
  rw [CFSG.Quasithin.H13.card_eq_card_oTwoQuot_mul_card_pCoreOf,
    IsL2Quot.card (by norm_num) (f112sa_isL2Quot_oTwoPrime_P1' hF h1 h2),
    pCoreOf_oTwoPrime]
  norm_num

theorem f112sa_card_T_eq_QS {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    Nat.card ↥(S ⊓ f112saK L1 L2 S) =
      2 * Nat.card ↥(pCoreOf 2 (f112saP1' L1 L2 S)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : Nat.card ↥(oTwoPrime (f112saP1' L1 L2 S)) =
      2 ^ 1 * 3 * Nat.card ↥(pCoreOf 2 (f112saP1' L1 L2 S)) := by
    rw [f112sa_card_oTwoPrime_P1' hF h1 h2]
    norm_num
  have := card_eq_of_isSylowTwoOf_of_card_eq (a := 1) (m := 3)
    (f112sa_T_sylow_oTwoPrime_P1' hF.toW) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (by norm_num) hX
  simpa using this

theorem f112sa_sq_mem_QA {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    ∀ t ∈ S ⊓ f112saK L1 L2 S, t ^ 2 ∈ pCoreOf 2 (f112saP2' L1 L2 S) := by
  intro t ht
  have htE : t ∈ f112saP2' L1 L2 S := (f112sa_T_sylow_P2' hF.toW).1 ht
  let t' : ↥(f112saP2' L1 L2 S) := ⟨t, htE⟩
  obtain ⟨n, hn⟩ := hF.1.h1.pgroup ⟨t, ht.1⟩
  have htpow : t' ^ 2 ^ n = 1 := by
    apply Subtype.ext
    show t ^ 2 ^ n = 1
    simpa using congrArg (Subtype.val) hn
  obtain ⟨e1⟩ := f112sa_isL2Quot_P2' hF h1 h2
  obtain ⟨e2⟩ := CFSG.Quasithin.F112J2.nonempty_psl_four_equiv_alt5
  let e := e1.trans e2
  let mk : ↥(f112saP2' L1 L2 S) →* oTwoQuot ↥(f112saP2' L1 L2 S) :=
    QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(f112saP2' L1 L2 S))
  have hsq : (e (mk t')) ^ 2 = 1 := by
    refine CFSG.Quasithin.FA5.alt5_sq_eq_one_of_two_power (k := n) ?_
    rw [← map_pow, ← map_pow, htpow]
    simp
  have hq1 : mk (t' ^ 2) = 1 := by
    apply e.injective
    rw [map_pow, map_pow, hsq, map_one]
  have hmem : (t' ^ 2 : ↥(f112saP2' L1 L2 S)) ∈
      CFSG.Open.pCore 2 ↥(f112saP2' L1 L2 S) :=
    (QuotientGroup.eq_one_iff (t' ^ 2)).mp hq1
  exact Subgroup.mem_map_of_mem (f112saP2' L1 L2 S).subtype hmem

theorem f112sa_exists_k {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h2 : VA5 L2) :
    ∃ k : H, k ∈ f112saX2 L1 L2 S ∧ k ∈ borelOf L2 S ∧ orderOf k = 3 ∧
      k ∈ Subgroup.normalizer ((S ⊓ L2 : Subgroup H) : Set H) := by
  obtain ⟨k, hkX, hkB, hk3, hkN⟩ :=
    f112_exists_orderThree_X1 (L1 := L2) (L2 := L1) hF.symm.toW h2
  exact ⟨k, by simpa [f112saX1, f112saX2, bigB_comm] using hkX, hkB, hk3, hkN⟩

end CFSG.Quasithin.F112R.St84
