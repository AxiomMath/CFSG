module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma106Hall
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Lemma 10.6: complement assembly

This module assembles the Hall-prime result into the normal complement and
intersection conclusions of source Lemma 10.6.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise IsMulCommutative commutatorElement

universe u

/-- If `V = A P` and `P` is abelian, then `[V,P] ≤ [A,P]`. -/
public theorem lemma106_commutator_le_of_mul_right_commutative
    {X : Type*} [Group X]
    {A P V : Subgroup X} [IsMulCommutative P]
    (hset : (V : Set X) = (A : Set X) * (P : Set X)) :
    ⁅V, P⁆ ≤ ⁅A, P⁆ := by
  apply Subgroup.commutator_le.mpr
  intro x hx p hp
  change x ∈ (V : Set X) at hx
  rw [hset] at hx
  rcases Set.mem_mul.mp hx with ⟨a, ha, q, hq, hxa⟩
  have hqp : ⁅q, p⁆ = 1 := by
    have hcomm : q * p = p * q := by
      exact congrArg Subtype.val
        (mul_comm (⟨q, hq⟩ : P) (⟨p, hp⟩ : P))
    rw [commutatorElement_def, hcomm]
    simp
  rw [← hxa, commutator_mul_left, hqp]
  simpa using Subgroup.commutator_mem_commutator ha hp

/-- Once the Hall conclusion for `C_A(P)` is known, the remaining assertions
of Lemma 10.6 follow from coprime action and the checked factorizations of
Lemma 10.1. -/
public theorem lemma106_assembly_of_hall
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (hDodd : Odd (Nat.card D))
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hHallD : IsHallSubgroup (lemma106Pi d)
      ((lemma104C d).subgroupOf D)) :
    subgroupCentralizerIn
        (Subgroup.closure (peterfalviKSet D t) ⊔ d.choice.initial.A1)
        d.choice.P = lemma104C d ∧
      IsNormalComplementIn D (lemma104C d)
        (lemma106H d ⊔ d.choice.P) ∧
      lemma106H d ⊓ peterfalviV D t =
        ⁅d.choice.initial.A1, d.choice.P⁆ := by
  classical
  let p : ℕ := d.choice.p
  let P : Subgroup X := d.choice.P
  let V : Subgroup X := peterfalviV D t
  let A : Subgroup X := d.choice.initial.A1
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let N : Subgroup X := K ⊔ A
  let C : Subgroup X := lemma104C d
  let H : Subgroup X := lemma106H d
  have hp : p.Prime := by simpa [p] using d.choice.p_prime
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsMulCommutative P :=
    (isCyclic_of_prime_card (by simpa [P] using d.P_card)).isMulCommutative
  have hK_D : K ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hA_V : A ≤ V := by
    dsimp [A, V]
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hA_D : A ≤ D := hA_V.trans inf_le_left
  have hP_D : P ≤ D := by
    simpa [P] using d.choice.P_le_V.trans (show V ≤ D from inf_le_left)
  have hN_D : N ≤ D := sup_le hK_D hA_D
  have hKnormalD : (K.subgroupOf D).Normal := by
    simpa [K] using lemma101_peterfalviKernel_normal ht hDodd hDnorm
  have hDnormK : D ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK_D).mp hKnormalD
  have hAnormK : A ≤ Subgroup.normalizer (K : Set X) :=
    hA_D.trans hDnormK
  have hPnormK : P ≤ Subgroup.normalizer (K : Set X) :=
    hP_D.trans hDnormK
  have hNnormalD : (N.subgroupOf D).Normal := by
    have hNeq : N = (pPrimeCore p D).map D.subtype := by
      simpa [N, K, A, p] using d.kernel_sup_A1_eq_pPrimeCore
    have hNsub : N.subgroupOf D = pPrimeCore p D := by
      rw [hNeq]
      exact subgroupOf_map_subtype_eq (pPrimeCore p D)
    rw [hNsub]
    exact pPrimeCore_normal
  have hDnormN : D ≤ Subgroup.normalizer (N : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN_D).mp hNnormalD
  have hPnormN : P ≤ Subgroup.normalizer (N : Set X) :=
    hP_D.trans hDnormN
  have hNsupP : N ⊔ P = D := by
    apply le_antisymm
    · exact sup_le hN_D hP_D
    · intro x hxD
      have hxprod : x ∈ (K : Set X) * (A : Set X) * (P : Set X) := by
        rw [← d.D_eq_kernel_mul_A1_mul_P]
        exact hxD
      rcases Set.mem_mul.mp hxprod with ⟨ka, hka, q, hqP, hkaq⟩
      rcases Set.mem_mul.mp hka with ⟨k, hkK, a, haA, hka⟩
      have hkN : k ∈ N := (show K ≤ N from le_sup_left) hkK
      have haN : a ∈ N := (show A ≤ N from le_sup_right) haA
      have hkNP : k ∈ N ⊔ P :=
        (show N ≤ N ⊔ P from le_sup_left) hkN
      have haNP : a ∈ N ⊔ P :=
        (show N ≤ N ⊔ P from le_sup_left) haN
      have hqNP : q ∈ N ⊔ P :=
        (show P ≤ N ⊔ P from le_sup_right) hqP
      rw [← hkaq, ← hka]
      exact (N ⊔ P).mul_mem ((N ⊔ P).mul_mem hkNP haNP) hqNP
  have hcopNP : Nat.Coprime (Nat.card N) (Nat.card P) := by
    have hNeq : N = (pPrimeCore p D).map D.subtype := by
      simpa [N, K, A, p] using d.kernel_sup_A1_eq_pPrimeCore
    have hcardN : Nat.card N = Nat.card (pPrimeCore p D) := by
      rw [hNeq, Subgroup.card_map_of_injective D.subtype_injective]
    rw [hcardN]
    simpa [P, p, d.P_card] using
      (pPrimeCore_coprime_card (p := p) (G := D)).symm
  have hNdisjP : Disjoint N P :=
    disjoint_iff.mpr (Subgroup.inf_eq_bot_of_coprime hcopNP)
  have hC_le_N : C ≤ N := by
    change d.choice.initial.A1 ⊓
        Subgroup.centralizer (d.choice.P : Set X) ≤ K ⊔ A
    intro x hx
    exact (show A ≤ K ⊔ A from le_sup_right) hx.1
  have hCcentralP : C ≤ Subgroup.centralizer (P : Set X) := by
    change d.choice.initial.A1 ⊓
        Subgroup.centralizer (d.choice.P : Set X) ≤
      Subgroup.centralizer (d.choice.P : Set X)
    intro x hx
    exact hx.2
  have hNfactor : (normalizerIn D P : Set X) =
      (C : Set X) * (P : Set X) := by
    simpa [C, P, lemma104C] using d.normalizer_factorization.2.1
  have hCentNP : subgroupCentralizerIn N P = C :=
    lemma106_subgroupCentralizerIn_eq_of_normalizer_factorization
      hN_D hC_le_N hNdisjP hNfactor hCcentralP
  have hC_hall_N : IsHallSubgroup (lemma106Pi d) (C.subgroupOf N) :=
    lemma106_hall_subgroupOf_between hC_le_N hN_D hHallD
  have hKcopC : Nat.Coprime (Nat.card K) (Nat.card C) := by
    apply Nat.coprime_of_dvd
    intro q hq hqK hqC
    let q' : Nat.Primes := ⟨q, hq⟩
    have hqPi : q' ∈ lemma106Pi d := by
      apply hC_hall_N.p_in_pi_of_p_dvd_card q'
      simpa [natCard_subgroupOf_eq C N hC_le_N] using hqC
    exact hqPi.2.2 hqK
  have hKcopP : Nat.Coprime (Nat.card K) (Nat.card P) := by
    have hKcop : Nat.Coprime p (Nat.card K) := by
      have hNeq : N = (pPrimeCore p D).map D.subtype := by
        simpa [N, K, A, p] using d.kernel_sup_A1_eq_pPrimeCore
      have hcardN : Nat.card N = Nat.card (pPrimeCore p D) := by
        rw [hNeq, Subgroup.card_map_of_injective D.subtype_injective]
      have hcop : Nat.Coprime p (Nat.card N) := by
        rw [hcardN]
        exact pPrimeCore_coprime_card
      exact Nat.Coprime.of_dvd_right
        (Subgroup.card_dvd_of_le le_sup_left) hcop
    simpa [P, p, d.P_card] using hKcop.symm
  have hNDPcard : Nat.card (normalizerIn D P) =
      Nat.card C * Nat.card P :=
    lemma106_natCard_eq_mul_of_set_mul_disjoint hNfactor
      (by simpa [C, P, lemma104C] using
        d.normalizer_factorization.2.2)
  have hKcopNDP :
      Nat.Coprime (Nat.card K) (Nat.card (normalizerIn D P)) := by
    rw [hNDPcard]
    exact hKcopC.mul_right hKcopP
  have hCKP : subgroupCentralizerIn K P = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxNDP : x ∈ normalizerIn D P :=
      ⟨hK_D hx.1, centralizer_le_normalizer P hx.2⟩
    have hxInf : x ∈ K ⊓ normalizerIn D P := ⟨hx.1, hxNDP⟩
    have hInf : K ⊓ normalizerIn D P = ⊥ :=
      Subgroup.inf_eq_bot_of_coprime hKcopNDP
    rw [hInf] at hxInf
    exact hxInf
  have hKcomm : ⁅K, P⁆ = K := by
    symm
    exact lemma106_eq_commutator_of_coprime_fixedPointFree K P
      hPnormK
      (odd_order_theorem K
        (hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hK_D)))
      hKcopP.symm hCKP
  have hsolvN : IsSolvable N :=
    odd_order_theorem N
      (hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hN_D))
  letI : Subgroup.Normalizes P N := ⟨hPnormN⟩
  letI : MulDistribMulAction P N :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer P N hPnormN
  have hfixN : fixedPointSubgroup P N = C.subgroupOf N := by
    simpa [hCentNP] using
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn N P hPnormN
  have hcopPN : Nat.Coprime (Nat.card P) (Nat.card N) := hcopNP.symm
  obtain ⟨S, _hShall, _hSinv, hScomp, hSnormal, hScomm⟩ :=
    lemma106_hall_complement_action hsolvN hcopPN (lemma106Pi d)
      (C.subgroupOf N) hC_hall_N hfixN
  have hSmap : S.map N.subtype = H := by
    have hcommMap :
        (commutatorAction (A := P) (G := N)).map N.subtype =
          ⁅N, P⁆ :=
      commutatorAction_subgroup_conj_map_eq_commutator N P hPnormN
    have hNPcomm : ⁅N, P⁆ = K ⊔ ⁅A, P⁆ :=
      lemma106_commutator_sup_eq hAnormK hPnormK hKcomm
    rw [← hScomm, hcommMap, hNPcomm]
    rfl
  have hcompHN : IsNormalComplementIn N C H := by
    simpa [hSmap] using
      lemma106_map_normal_complement hC_le_N S hSnormal hScomp
  have hHleN : H ≤ N := by
    rw [← hSmap]
    exact Subgroup.map_subtype_le S
  have hHleNP : H ≤ N ⊔ P := hHleN.trans le_sup_left
  have hHcomm : H = ⁅N, P⁆ := by
    calc
      H = S.map N.subtype := hSmap.symm
      _ = (commutatorAction (A := P) (G := N)).map N.subtype := by
        rw [hScomm]
      _ = ⁅N, P⁆ :=
        commutatorAction_subgroup_conj_map_eq_commutator N P hPnormN
  have hHnormalNP : (H.subgroupOf (N ⊔ P)).Normal := by
    rw [hHcomm]
    exact commutator_normal_in_sup N P
  have hDnormH : N ⊔ P ≤ Subgroup.normalizer (H : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHleNP).mp hHnormalNP
  have hPnormH : P ≤ Subgroup.normalizer (H : Set X) :=
    le_sup_right.trans hDnormH
  have hcompD : IsNormalComplementIn D C (H ⊔ P) :=
    lemma106_extend_normal_complement hN_D hP_D hC_le_N hHleN hNsupP
      hPnormH hcompHN.normal_in_M hCcentralP hcompHN hNdisjP
  have hHcentralP : subgroupCentralizerIn H P = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxC : x ∈ C := by
      have hxNP : x ∈ subgroupCentralizerIn N P :=
        ⟨hHleN hx.1, hx.2⟩
      rw [hCentNP] at hxNP
      exact hxNP
    exact Subgroup.disjoint_def.mp hcompHN.disjoint_D hx.1 hxC
  have hA_P_le_H : ⁅A, P⁆ ≤ H := by
    rw [hHcomm]
    exact Subgroup.commutator_mono le_sup_right le_rfl
  have hA_P_le_V : ⁅A, P⁆ ≤ V := by
    apply Subgroup.commutator_le.mpr
    intro a ha p' hp'
    exact V.mul_mem
      (V.mul_mem (V.mul_mem (hA_V ha) (d.choice.P_le_V hp'))
        (V.inv_mem (hA_V ha)))
      (V.inv_mem (d.choice.P_le_V hp'))
  have hAP_le_inf : ⁅A, P⁆ ≤ H ⊓ V :=
    le_inf hA_P_le_H hA_P_le_V
  let R : Subgroup X := H ⊓ V
  have hPnormV : P ≤ Subgroup.normalizer (V : Set X) :=
    d.choice.P_le_V.trans Subgroup.le_normalizer
  have hPnormR : P ≤ Subgroup.normalizer (R : Set X) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hPnormH hx, hPnormV hx⟩
  have hsolvR : IsSolvable R :=
    odd_order_theorem R (hDodd.of_dvd_nat
      (Subgroup.card_dvd_of_le
        ((show R ≤ N from inf_le_left.trans hHleN).trans hN_D)))
  have hcopPR : Nat.Coprime (Nat.card P) (Nat.card R) :=
    Nat.Coprime.of_dvd_right
      (Subgroup.card_dvd_of_le
        (show R ≤ N from inf_le_left.trans hHleN)) hcopNP.symm
  have hRcentral : subgroupCentralizerIn R P = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxH : (x : X) ∈ subgroupCentralizerIn H P :=
      ⟨hx.1.1, hx.2⟩
    rw [hHcentralP] at hxH
    exact hxH
  have hRcomm : R = ⁅R, P⁆ :=
    lemma106_eq_commutator_of_coprime_fixedPointFree R P hPnormR
      hsolvR hcopPR hRcentral
  have hRcomm_le : ⁅R, P⁆ ≤ ⁅A, P⁆ := by
    have hRV : ⁅R, P⁆ ≤ ⁅V, P⁆ :=
      Subgroup.commutator_mono
        (show R ≤ V from inf_le_right) (show P ≤ P from le_rfl)
    exact hRV.trans
      (lemma106_commutator_le_of_mul_right_commutative
        (by simpa [V, A, P] using d.V_eq_mul))
  have hRleAP : R ≤ ⁅A, P⁆ := by
    rw [hRcomm]
    exact hRcomm_le
  exact ⟨by simpa [N, P, C, K, A, lemma104C] using hCentNP,
    hcompD, le_antisymm hRleAP hAP_le_inf⟩

/-- Package all conclusions of Lemma 10.6 after proving the Hall field. -/
public theorem lemma106_of_hall
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (hDodd : Odd (Nat.card D))
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hHallD : IsHallSubgroup (lemma106Pi d)
      ((lemma104C d).subgroupOf D)) :
    Lemma106Conclusion M W D E (peterfalviV D t) t d := by
  obtain ⟨hcentral, hcomp, hinter⟩ :=
    lemma106_assembly_of_hall d hDodd ht hDnorm hHallD
  exact {
    C_hall_D := hHallD
    centralizer_kernel_sup_A1 := hcentral
    normal_complement := hcomp
    kernel_commutator_inf_V := hinter }

/-- Source Lemma 10.6. -/
public theorem lemma_10_6
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t u0 : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (d97 : Lemma97Conclusion M t)
    (d103 : Lemma103Conclusion M d.choice.P u0)
    (d104 : Lemma104Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t d)
    (h42 : II1Lemma42PrimeTransfer (X := X)) :
    Lemma106Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t d := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hDnorm : t ∈ Subgroup.normalizer (D : Set X) := by
    simpa [D] using inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  have hCcard : Nat.card (lemma104C d) ∣ d.choice.p - 1 :=
    lemma_10_5 hM ht htM d83 h84 d d103 d104
  have hHall : IsHallSubgroup (lemma106Pi d)
      ((lemma104C d).subgroupOf D) :=
    lemma106_C_isHall d hDodd ht hDnorm h42
      (by simpa [D] using d97.peterfalvi_centralizer_eq_bot)
      hCcard
  exact lemma106_of_hall d hDodd ht hDnorm hHall

end CFSG.BenderSuzuki
