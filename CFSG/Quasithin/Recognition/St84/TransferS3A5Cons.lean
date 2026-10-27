module

public import CFSG.Quasithin.Recognition.St84.TransferS3A5Setup
public import CFSG.Quasithin.Recognition.St84.TransferS3A5Count
public import CFSG.Walter.Bender1970.S2.OddFitting

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

private theorem le_of_forall_commute_mem_commutator_inf_centralizer {L Q : Subgroup H} {d : H}
    (hQ : Group.IsSolvable Q) (hQL : Q ≤ Subgroup.normalizer (L : Set H)) (hdL : d ∈ L)
    (hdQ : d ∈ Subgroup.normalizer (Q : Set H)) (hcop : Nat.Coprime (orderOf d) (Nat.card Q))
    (hfix : ∀ e ∈ Q, e * d = d * e →
      e ∈ ⁅Q, Q⁆ ⊓ Subgroup.centralizer (Q : Set H)) : Q ≤ L := by
  classical
  have hTU : Subgroup.zpowers d ≤ Subgroup.normalizer (Q : Set H) :=
    Subgroup.zpowers_le.mpr hdQ
  have hcop' : Nat.Coprime (Nat.card ↥(Subgroup.zpowers d)) (Nat.card ↥Q) := by
    simpa [Nat.card_zpowers] using hcop
  have hdec := CFSG.Walter.le_sup_commutator_of_coprime hTU hQ hcop'
  have hcommL : ⁅Q, Subgroup.zpowers d⁆ ≤ L := by
    refine Subgroup.commutator_le.mpr ?_
    rintro q hq t ht
    have htL : t ∈ L := Subgroup.zpowers_le.mpr hdL ht
    have hconj : q * t * q⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hQL hq) t).mp htL
    simpa [commutatorElement_def] using L.mul_mem hconj (L.inv_mem htL)
  have hcommQ : ⁅Q, Subgroup.zpowers d⁆ ≤ Q := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hTU
  have hfixle : Q ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set H) ≤ ⁅Q, Q⁆ := by
    intro e he
    exact (hfix e he.1
      ((Subgroup.mem_centralizer_iff.mp he.2) d (Subgroup.mem_zpowers d)).symm).1
  have hsup : Q ≤ (L ⊓ Q) ⊔ (Q ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set H)) := by
    simpa [sup_comm] using hdec.trans (sup_le_sup le_rfl (le_inf hcommL hcommQ))
  have hmain := CFSG.GroupTheory.le_of_le_sup_of_le_commutator
    (Q := Q) (M := L ⊓ Q) (K₀ := Q ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set H))
    inf_le_right hsup (fun k hk q hq =>
      ((Subgroup.mem_centralizer_iff.mp (hfix k hk.1
        ((Subgroup.mem_centralizer_iff.mp hk.2) d (Subgroup.mem_zpowers d)).symm).2) q hq).symm)
      hfixle
  exact hmain.trans inf_le_left
private theorem f112sa_mem_QA_of_commute {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hC : S3A5ModuleFacts L1 L2 S)
    {k c : H} (hk : k ∈ borelOf L2 S) (hk3 : orderOf k = 3) (hck : c * k = k * c)
    (hcS : c ∈ S) : c ∈ pCoreOf 2 (f112saP2' L1 L2 S) := by
  have hl := f112_conjModPCore_left hF.symm h2 hk hk3 hck hcS
  have hL := f112sa_commutator_mem_pCoreOf_of_mem_oTwoPrime_P2' hF h2
    (f112sa_isL2Quot_oTwoPrime_P2' hF h1 h2) hcS hl
  rw [f112sa_oTwoPrime_P2'_eq hF h1 h2] at hL
  exact hC.ker_right c hcS hL

private theorem f112sa_le_T_of_normalizes {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hC : S3A5ModuleFacts L1 L2 S) {k : H}
    (hkX : k ∈ f112saX2 L1 L2 S) (hkB : k ∈ borelOf L2 S) (hk3 : orderOf k = 3)
    {N : Subgroup H} (hNS : N ≤ S) (hkN : k ∈ Subgroup.normalizer (N : Set H)) :
    N ≤ S ⊓ f112saK L1 L2 S := by
  classical
  have hTU : Subgroup.zpowers k ≤ Subgroup.normalizer (N : Set H) :=
    Subgroup.zpowers_le.mpr hkN
  have hsolv : Group.IsSolvable ↥N := by
    haveI : Group.IsNilpotent ↥N := (hF.1.h1.pgroup.to_le hNS).isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥N) := by
    obtain ⟨n, hn⟩ := (hF.1.h1.pgroup.to_le hNS).exists_card_eq
    rw [Nat.card_zpowers, hk3, hn]
    exact (by norm_num : Nat.Coprime 3 2).pow_right n
  have hdec := CFSG.Walter.le_sup_commutator_of_coprime hTU hsolv hcop
  have hfix : N ⊓ Subgroup.centralizer (Subgroup.zpowers k : Set H) ≤
      S ⊓ f112saK L1 L2 S := by
    intro c hc
    have hck : c * k = k * c :=
      ((Subgroup.mem_centralizer_iff.mp hc.2) k (Subgroup.mem_zpowers k)).symm
    exact f112sa_QA_le_T hF
      (f112sa_mem_QA_of_commute hF h1 h2 hC hkB hk3 hck (hNS hc.1))
  have hcommN : ⁅N, Subgroup.zpowers k⁆ ≤ N := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hTU
  have hX2N : N ≤ Subgroup.normalizer (f112saX2 L1 L2 S : Set H) :=
    (hNS.trans le_sup_right).trans (f112sa_bigB_le_normalizer_X2 hF.toW)
  have hcommX : ⁅N, Subgroup.zpowers k⁆ ≤ f112saX2 L1 L2 S :=
    (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hkX)).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hX2N)
  have hcomm : ⁅N, Subgroup.zpowers k⁆ ≤ S ⊓ f112saK L1 L2 S :=
    le_inf (hcommN.trans hNS)
      (hcommX.trans (le_sup_right : f112saX2 L1 L2 S ≤ f112saK L1 L2 S))
  exact hdec.trans (sup_le hfix hcomm)

private theorem f112sa_S_inf_L2_le_T {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hC : S3A5ModuleFacts L1 L2 S) :
    S ⊓ L2 ≤ S ⊓ f112saK L1 L2 S := by
  obtain ⟨k, hkX, hkB, hk3, hkN⟩ := f112sa_exists_k hF h2
  exact f112sa_le_T_of_normalizes hF h1 h2 hC hkX hkB hk3 inf_le_left hkN

private theorem f112sa_S_inf_L1_le_T {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hC : S3A5ModuleFacts L1 L2 S) :
    S ⊓ L1 ≤ S ⊓ f112saK L1 L2 S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  obtain ⟨k, hkX, hkB, hk3, -⟩ := f112sa_exists_k hF h2
  have hkN : k ∈ Subgroup.normalizer ((S ⊓ L1 : Subgroup H) : Set H) :=
    (F1.bigB_le_normalizer_sylow hR).1 (f112sa_X2_le_bigB L1 L2 S hkX)
  exact f112sa_le_T_of_normalizes hF h1 h2 hC hkX hkB hk3 inf_le_left hkN

private theorem f112sa_pCoreOf_parabolic_eq {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hC : S3A5ModuleFacts L1 L2 S)
    {P P' : Subgroup H} (hBP : bigB L1 L2 S ≤ P) (hsyl : IsSylowTwoOf S P)
    (hP'P : P' ≤ P) (hKP' : f112saK L1 L2 S ≤ P')
    (hPn : P ≤ Subgroup.normalizer (pCoreOf 2 P' : Set H)) :
    pCoreOf 2 P = pCoreOf 2 P' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hkX, hkB, hk3, -⟩ := f112sa_exists_k hF h2
  have hkP : k ∈ P := hBP (f112sa_X2_le_bigB L1 L2 S hkX)
  refine le_antisymm ?_ ?_
  · have hNS : pCoreOf 2 P ≤ S := F7.isSylowTwoOf_pCoreOf_le hsyl
    have hkN : k ∈ Subgroup.normalizer (pCoreOf 2 P : Set H) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hkP
    have hT := f112sa_le_T_of_normalizes hF h1 h2 hC hkX hkB hk3 hNS hkN
    have hNE : pCoreOf 2 P ≤ P' := hT.trans (inf_le_right.trans hKP')
    have hnorm : P' ≤ Subgroup.normalizer (pCoreOf 2 P : Set H) :=
      hP'P.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNE hnorm
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P)
  · have hle : pCoreOf 2 P' ≤ P := (CFSG.LieType.BorelTits.pCoreOf_le 2 P').trans hP'P
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle hPn
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P')

private theorem f112sa_pCoreOf_P2_eq {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hC : S3A5ModuleFacts L1 L2 S) :
    pCoreOf 2 (f112P2 L1 L2 S) = pCoreOf 2 (f112saP2' L1 L2 S) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  exact f112sa_pCoreOf_parabolic_eq hF h1 h2 hC le_sup_right
    (F112W.isSylowTwoOf_parabolic' hR) (f112sa_P2'_le_P2 hF.toW)
    (f112saK_le_P2' L1 L2 S) (f112sa_P2_le_normalizer_QA hF)

private theorem f112sa_pCoreOf_P1_eq {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hC : S3A5ModuleFacts L1 L2 S) :
    pCoreOf 2 (f112P1 L1 L2 S) = pCoreOf 2 (f112saP1' L1 L2 S) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  exact f112sa_pCoreOf_parabolic_eq hF h1 h2 hC le_sup_right
    (F112W.isSylowTwoOf_parabolic hR) (f112sa_P1'_le_P1 hF.toW)
    (f112saK_le_P1' L1 L2 S) (f112sa_P1_le_normalizer_QS hF)

private theorem f112sa_L1_le_oTwoPrime_P1'
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hC : S3A5ModuleFacts L1 L2 S) :
    L1 ≤ oTwoPrime (f112saP1' L1 L2 S) := by
  have hL1E : L1 ≤ f112saP1' L1 L2 S :=
    (le_oTwoRes_sup_of_isSylowTwoOf hF.1.h1.sylow).trans
      (sup_le le_sup_left ((f112sa_S_inf_L1_le_T hF h1 h2 hC).trans
        (inf_le_right.trans (f112saK_le_P1' L1 L2 S))))
  exact (oTwoPrime_eq_self_of_perm3 hF.1.h1.sylow h1).ge.trans
    (CFSG.Quasithin.St84.oTwoPrime_mono hL1E)

private theorem f112sa_pCoreOf_P1'_le_L1
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hC : S3A5ModuleFacts L1 L2 S) :
    pCoreOf 2 (f112saP1' L1 L2 S) ≤ L1 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  obtain ⟨d, hdL1, hd3⟩ := f112sa_exists_orderThree_L1 (L2 := L2) (S := S) h1
  have hP1N : f112P1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set H) :=
    sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left hR).1
  have hQN : pCoreOf 2 (f112saP1' L1 L2 S) ≤ Subgroup.normalizer (L1 : Set H) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (f112saP1' L1 L2 S)).trans
      (f112sa_P1'_le_P1 hF.toW)).trans hP1N
  have hdQ : d ∈ Subgroup.normalizer (pCoreOf 2 (f112saP1' L1 L2 S) : Set H) :=
    f112sa_P1_le_normalizer_QS hF ((le_sup_left : L1 ≤ f112P1 L1 L2 S) hdL1)
  have hsolv : Group.IsSolvable ↥(pCoreOf 2 (f112saP1' L1 L2 S)) := by
    haveI : Group.IsNilpotent ↥(pCoreOf 2 (f112saP1' L1 L2 S)) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (f112saP1' L1 L2 S)).isNilpotent
    infer_instance
  have hcop : Nat.Coprime (orderOf d) (Nat.card ↥(pCoreOf 2 (f112saP1' L1 L2 S))) := by
    obtain ⟨n, hn⟩ :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (f112saP1' L1 L2 S)).exists_card_eq
    rw [hd3, hn]
    exact (by norm_num : Nat.Coprime 3 2).pow_right n
  exact le_of_forall_commute_mem_commutator_inf_centralizer hsolv hQN hdL1 hdQ hcop
    (hC.fix_left d (f112sa_L1_le_oTwoPrime_P1' hF h1 h2 hC hdL1) hd3)

private theorem f112sa_L2_eq_P2' {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hC : S3A5ModuleFacts L1 L2 S) :
    L2 = f112saP2' L1 L2 S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hL2E : L2 ≤ f112saP2' L1 L2 S :=
    (le_oTwoRes_sup_of_isSylowTwoOf hF.1.h2.sylow).trans
      (sup_le le_sup_left ((f112sa_S_inf_L2_le_T hF h1 h2 hC).trans
        (inf_le_right.trans (f112saK_le_P2' L1 L2 S))))
  have hP2N : f112P2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set H) :=
    sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left hR).2
  have hQN : pCoreOf 2 (f112saP2' L1 L2 S) ≤ Subgroup.normalizer (L2 : Set H) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (f112saP2' L1 L2 S)).trans
      (f112sa_P2'_le_P2 hF.toW)).trans hP2N
  have hQ_le_L2 : pCoreOf 2 (f112saP2' L1 L2 S) ≤ L2 := by
    rw [← hC.indec_right]
    refine Subgroup.commutator_le.mpr ?_
    intro q hq a ha
    have hqN : q ∈ Subgroup.normalizer (L2 : Set H) := hQN hq
    have hconj : q * a * q⁻¹ ∈ L2 :=
      (Subgroup.mem_normalizer_iff.mp hqN a).mp (oTwoRes_le L2 ha)
    have e : ⁅q, a⁆ = (q * a * q⁻¹) * a⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact L2.mul_mem hconj (L2.inv_mem (oTwoRes_le L2 ha))
  have hE2L : f112saP2' L1 L2 S ≤ L2 :=
    (f112sa_P2'_eq_oTwoRes_sup hF h1 h2).le.trans (sup_le (oTwoRes_le L2) hQ_le_L2)
  exact le_antisymm hL2E hE2L

private theorem f112sa_L1_eq_oTwoPrime_P1' {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hC : S3A5ModuleFacts L1 L2 S) :
    L1 = oTwoPrime (f112saP1' L1 L2 S) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hle := f112sa_L1_le_oTwoPrime_P1' hF h1 h2 hC
  have hQ := f112sa_pCoreOf_P1'_le_L1 hF h1 h2 hC
  have hO2 : pCoreOf 2 L1 = pCoreOf 2 (f112saP1' L1 L2 S) := by
    have h := F1.inf_pCoreOf_parabolic_eq hR
    rw [f112sa_pCoreOf_P1_eq hF h1 h2 hC, inf_eq_left.mpr hQ] at h
    exact h.symm
  have hcard : Nat.card ↥L1 = Nat.card ↥(oTwoPrime (f112saP1' L1 L2 S)) := by
    rw [CFSG.Quasithin.F6.GoldPair.card_eq_six_mul_pCoreOf h1, f112sa_card_oTwoPrime_P1' hF h1 h2,
      hO2]
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

theorem s3a5VertexId_of_moduleFacts {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hC : S3A5ModuleFacts L1 L2 S) :
    S3A5VertexId L1 L2 S := by
  have hL2 := f112sa_L2_eq_P2' hF h1 h2 hC
  have hL1 := f112sa_L1_eq_oTwoPrime_P1' hF h1 h2 hC
  have hT : S ⊓ L2 = S ⊓ f112saK L1 L2 S :=
    le_antisymm (f112sa_S_inf_L2_le_T hF h1 h2 hC)
      (le_inf inf_le_left (inf_le_right.trans ((f112saK_le_P2' L1 L2 S).trans hL2.ge)))
  have hS1 : S ⊓ L1 = S ⊓ f112saK L1 L2 S :=
    le_antisymm (f112sa_S_inf_L1_le_T hF h1 h2 hC)
      (le_inf inf_le_left ((f112sa_T_le_oTwoPrime_P1' hF.toW).trans hL1.ge))
  have hQA : pCoreOf 2 L2 = pCoreOf 2 (f112saP2' L1 L2 S) := congrArg (pCoreOf 2) hL2
  have hQS : pCoreOf 2 L1 = pCoreOf 2 (f112saP1' L1 L2 S) :=
    (congrArg (pCoreOf 2) hL1).trans (pCoreOf_oTwoPrime (f112saP1' L1 L2 S))
  have hQR : pCoreOf 2 L2 = dsQ L2 L1 S := by
    unfold dsQ
    rw [bigB_comm]
    exact hQA.trans (f112sa_pCoreOf_P2_eq hF h1 h2 hC).symm
  have hQL : pCoreOf 2 L1 = dsQ L1 L2 S := by
    unfold dsQ
    exact hQS.trans (f112sa_pCoreOf_P1_eq hF h1 h2 hC).symm
  refine
    { T_eq := hT
      L2_eq := hL2
      L1_eq := hL1
      S_inf_L1 := hS1
      QA_eq := hQA
      QS_eq := hQS
      oTwo_right := hQR
      oTwo_left := hQL
      sup_eq := ?_
      charTwo_right := ?_
      plain := ?_ }
  · rw [← hQR, ← hQL, hQA, hQS, sup_comm, f112sa_pCoreOf_sup_eq hF h1 h2, hT]
  · rw [hL2]
    exact f112sa_charTwo_P2' hF.toW
  · intro hS
    rw [bigB_comm, f112sa_bigB_eq_S_sup_K hF.toW]
    exact sup_le hS ((f112saK_le_P2' L1 L2 S).trans hL2.ge)

end CFSG.Quasithin.F112R.St84
