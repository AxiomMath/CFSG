module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Nilpotent
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Sylow
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Proposition 10.2(a)

This module assembles Lemmas 10.1 and 10.6 into the commutator identities of
Proposition 10.2(a).  In particular, the displayed source equality involving
`O^p(E)` is not assumed: the needed derived-subgroup equality is proved from
the checked factorization `E = E' P` and solvability.
-/

noncomputable section

set_option maxHeartbeats 2000000

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise IsMulCommutative commutatorElement

universe u

/-- A factor centralized by `P` does not contribute to the commutator with
`P`. -/
public theorem proposition102_commutator_sup_eq_left
    {X : Type u} [Group X]
    {E C P D : Subgroup X}
    (hD : D = E ⊔ C)
    (hCnormE : C ≤ Subgroup.normalizer (E : Set X))
    (hCcentralP : C ≤ Subgroup.centralizer (P : Set X)) :
    ⁅D, P⁆ = ⁅E, P⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx p hp
    have hxprod : x ∈ (E : Set X) * (C : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left E C hCnormE]
      rw [← hD]
      exact hx
    rcases Set.mem_mul.mp hxprod with ⟨e, he, c, hc, hec⟩
    have hcp : ⁅c, p⁆ = 1 := by
      exact commutatorElement_eq_one_iff_commute.mpr
        (Subgroup.mem_centralizer_iff.mp (hCcentralP hc) p hp).symm
    rw [← hec, commutator_mul_left, hcp]
    simpa using Subgroup.commutator_mem_commutator he hp
  · exact Subgroup.commutator_mono
      (by rw [hD]; exact le_sup_left) le_rfl

/-- The Frattini argument in the opening of the proof of Proposition 10.2:
`D = E C_A(P)`. -/
public theorem proposition102_D_eq_E_sup_C
    {X : Type u} [Group X] [Finite X]
    {M W D : Subgroup X} {t : X}
    (hW : IsMinimalNormalSupplement M D W)
    (hDle : D ≤ M)
    (d : Lemma101Conclusion M W D (W ⊓ D) (peterfalviV D t) t) :
    D = (W ⊓ D) ⊔ lemma104C d := by
  classical
  let E : Subgroup X := W ⊓ D
  let P : Subgroup X := d.choice.P
  let C : Subgroup X := lemma104C d
  letI : Fact d.choice.p.Prime := ⟨d.choice.p_prime⟩
  have hED : E ≤ D := inf_le_right
  have hEnormal : (E.subgroupOf D).Normal := by
    simpa [E] using hW.inf_normal_in_right hDle
  have hFrattini : E ⊔ normalizerIn D P = D := by
    simpa [E, P] using
      normal_sup_normalizerIn_eq_of_sylow hED hEnormal d.choice.S
        d.choice.P_eq_map.symm
  have hPE : P ≤ E := by
    change d.choice.P ≤ W ⊓ D
    rw [d.choice.P_eq_map]
    exact Subgroup.map_subtype_le (d.choice.S : Subgroup ↥(W ⊓ D))
  have hEP : E ⊔ P = E := sup_eq_left.mpr hPE
  have hNorm : normalizerIn D P = C ⊔ P := by
    simpa [P, C, lemma104C] using d.normalizer_factorization.1
  symm
  calc
    E ⊔ C = (E ⊔ P) ⊔ C := by rw [hEP]
    _ = E ⊔ (C ⊔ P) := by ac_rfl
    _ = E ⊔ normalizerIn D P := by rw [hNorm]
    _ = D := hFrattini

/-- Lemma 10.6 identifies the fixed-point-free subgroup `H=K[A,P]` and the
ambient commutator `[D,P]`. -/
public theorem proposition102_H_core
    {X : Type u} [Group X] [Finite X]
    {M W D : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D (W ⊓ D) (peterfalviV D t) t)
    (d106 : Lemma106Conclusion M W D (W ⊓ D)
      (peterfalviV D t) t d)
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X)) :
    subgroupCentralizerIn (lemma106H d) d.choice.P = ⊥ ∧
      ⁅D, d.choice.P⁆ = lemma106H d := by
  classical
  let p : ℕ := d.choice.p
  let P : Subgroup X := d.choice.P
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let A : Subgroup X := d.choice.initial.A1
  let N : Subgroup X := K ⊔ A
  let C : Subgroup X := lemma104C d
  let H : Subgroup X := lemma106H d
  have hp : p.Prime := by simpa [p] using d.choice.p_prime
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsMulCommutative P :=
    (isCyclic_of_prime_card (by simpa [P] using d.P_card)).isMulCommutative
  have hA_V : A ≤ peterfalviV D t := by
    dsimp [A]
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hV_D : peterfalviV D t ≤ D := inf_le_left
  have hA_D : A ≤ D := hA_V.trans hV_D
  have hK_D : K ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hN_D : N ≤ D := sup_le hK_D hA_D
  have hP_D : P ≤ D := by
    obtain ⟨Q, hQ⟩ := d.P_sylow_D
    change d.choice.P ≤ D
    rw [hQ]
    exact Subgroup.map_subtype_le (Q : Subgroup D)
  have hA_normal_V : (A.subgroupOf (peterfalviV D t)).Normal := by
    simpa [A] using d.choice.initial.A1_normal_V
  have hPnormA : P ≤ Subgroup.normalizer (A : Set X) :=
    d.choice.P_le_V.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hA_V).mp hA_normal_V)
  have hK_normal_D : (K.subgroupOf D).Normal := by
    simpa [K] using lemma101_peterfalviKernel_normal ht hDodd hDnorm
  have hDnormK : D ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK_D).mp hK_normal_D
  have hPnormK : P ≤ Subgroup.normalizer (K : Set X) := hP_D.trans hDnormK
  have hAnormK : A ≤ Subgroup.normalizer (K : Set X) := hA_D.trans hDnormK
  have hAP_le_A : ⁅A, P⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro a ha q hq
    have hqnorm : q ∈ Subgroup.normalizer (A : Set X) := hPnormA hq
    have hconj : q * a⁻¹ * q⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hqnorm a⁻¹).1 (A.inv_mem ha)
    simpa [commutatorElement_def, mul_assoc] using A.mul_mem ha hconj
  have hAPnorm : P ≤
      Subgroup.normalizer ((⁅A, P⁆ : Subgroup X) : Set X) := by
    have hAPnormal : ((⁅A, P⁆).subgroupOf (A ⊔ P)).Normal :=
      commutator_normal_in_sup A P
    exact le_sup_right.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (commutator_le_sup A P)).mp
        hAPnormal)
  have hPnormH : P ≤ Subgroup.normalizer (H : Set X) := by
    intro q hq
    exact mem_normalizer_sup_of_mem_normalizers (hPnormK hq) (hAPnorm hq)
  have hH_le_N : H ≤ N := by
    apply sup_le
    · exact le_sup_left
    · exact hAP_le_A.trans le_sup_right
  have hCentNP : subgroupCentralizerIn N P = C := by
    simpa [N, P, C, K, A] using d106.centralizer_kernel_sup_A1
  have hHcentral : subgroupCentralizerIn H P = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxC : x ∈ C := by
      have hxNP : x ∈ subgroupCentralizerIn N P := ⟨hH_le_N hx.1, hx.2⟩
      rw [hCentNP] at hxNP
      exact hxNP
    exact Subgroup.disjoint_def.mp d106.normal_complement.disjoint_D
      (Subgroup.mem_sup_left hx.1) hxC
  have hKcentral : subgroupCentralizerIn K P = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxH : x ∈ subgroupCentralizerIn H P :=
      ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
    rw [hHcentral] at hxH
    exact hxH
  have hNnormal : (N.subgroupOf D).Normal := by
    have hNeq : N = (pPrimeCore p D).map D.subtype := by
      simpa [N, K, A, p] using d.kernel_sup_A1_eq_pPrimeCore
    have hNsub : N.subgroupOf D = pPrimeCore p D := by
      rw [hNeq]
      exact subgroupOf_map_subtype_eq (pPrimeCore p D)
    rw [hNsub]
    exact pPrimeCore_normal
  have hDnormN : D ≤ Subgroup.normalizer (N : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN_D).mp hNnormal
  have hPnormN : P ≤ Subgroup.normalizer (N : Set X) := hP_D.trans hDnormN
  have hKsolv : IsSolvable K :=
    odd_order_theorem K (hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hK_D))
  have hcopPN : Nat.Coprime (Nat.card P) (Nat.card N) := by
    have hNeq : N = (pPrimeCore p D).map D.subtype := by
      simpa [N, K, A, p] using d.kernel_sup_A1_eq_pPrimeCore
    have hcardN : Nat.card N = Nat.card (pPrimeCore p D) := by
      rw [hNeq, Subgroup.card_map_of_injective D.subtype_injective]
    rw [hcardN]
    simpa [P, p, d.P_card] using
      (pPrimeCore_coprime_card (p := p) (G := D))
  have hcopPK : Nat.Coprime (Nat.card P) (Nat.card K) :=
    Nat.Coprime.of_dvd_right
      (Subgroup.card_dvd_of_le le_sup_left) hcopPN
  have hKcomm : K = ⁅K, P⁆ :=
    lemma106_eq_commutator_of_coprime_fixedPointFree K P hPnormK
      hKsolv hcopPK hKcentral
  have hNcomm : ⁅N, P⁆ = H := by
    change ⁅K ⊔ A, P⁆ = K ⊔ ⁅A, P⁆
    exact lemma106_commutator_sup_eq hAnormK hPnormK hKcomm.symm
  have hNsupP : N ⊔ P = D := by
    apply le_antisymm
    · exact sup_le hN_D hP_D
    · intro x hxD
      have hxprod : x ∈ (K : Set X) * (A : Set X) * (P : Set X) := by
        rw [← d.D_eq_kernel_mul_A1_mul_P]
        exact hxD
      rcases Set.mem_mul.mp hxprod with ⟨ka, hka, q, hqP, hkaq⟩
      rcases Set.mem_mul.mp hka with ⟨k, hkK, a, haA, hkaa⟩
      rw [← hkaq, ← hkaa]
      have hkN : k ∈ N := (show K ≤ N from le_sup_left) hkK
      have haN : a ∈ N := (show A ≤ N from le_sup_right) haA
      have hkNP : k ∈ N ⊔ P := (show N ≤ N ⊔ P from le_sup_left) hkN
      have haNP : a ∈ N ⊔ P := (show N ≤ N ⊔ P from le_sup_left) haN
      have hqNP : q ∈ N ⊔ P := (show P ≤ N ⊔ P from le_sup_right) hqP
      exact (N ⊔ P).mul_mem ((N ⊔ P).mul_mem hkNP haNP) hqNP
  have hPcentral : P ≤ Subgroup.centralizer (P : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val
      (mul_comm (⟨x, hx⟩ : P) (⟨y, hy⟩ : P)).symm
  have hDcomm : ⁅D, P⁆ = H := by
    rw [lemma106_commutator_sup_right_eq hNsupP.symm hPnormN hPcentral]
    exact hNcomm
  exact ⟨by simpa [H, P] using hHcentral,
    by simpa [H, P] using hDcomm⟩

/-- The part (a) identities and the fixed-point-free field needed for part
(b). -/
public structure Proposition102PartAConclusion
    {X : Type u} [Group X] [Finite X]
    (M W D E V : Subgroup X) (t : X)
    (d : Lemma101Conclusion M W D E V t) : Prop where
  E_eq_H_mul_P :
    (E : Set X) = (lemma106H d : Set X) * (d.choice.P : Set X)
  derived_eq_H :
    (derivedSubgroup E).map E.subtype = lemma106H d
  commutator_eq_H : ⁅E, d.choice.P⁆ = lemma106H d
  derived_inf_V :
    (derivedSubgroup E).map E.subtype ⊓ V =
      ⁅d.choice.initial.A1, d.choice.P⁆
  centralizer_derived_P :
    subgroupCentralizerIn ((derivedSubgroup E).map E.subtype) d.choice.P = ⊥

/-- Checked assembly of Proposition 10.2(a), with the fixed-point-free
centralizer retained for the nilpotence argument in part (b). -/
public theorem proposition102_part_a
    {X : Type u} [Group X] [Finite X]
    {M W D : Subgroup X} {t : X}
    (hW : IsMinimalNormalSupplement M D W)
    (hDle : D ≤ M)
    (d : Lemma101Conclusion M W D (W ⊓ D) (peterfalviV D t) t)
    (d106 : Lemma106Conclusion M W D (W ⊓ D)
      (peterfalviV D t) t d)
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X)) :
    Proposition102PartAConclusion M W D (W ⊓ D)
      (peterfalviV D t) t d := by
  classical
  let E : Subgroup X := W ⊓ D
  let P : Subgroup X := d.choice.P
  let C : Subgroup X := lemma104C d
  let H : Subgroup X := lemma106H d
  letI : Fact d.choice.p.Prime := ⟨d.choice.p_prime⟩
  letI : IsMulCommutative P :=
    (isCyclic_of_prime_card (by simpa [P] using d.P_card)).isMulCommutative
  have hED : E ≤ D := inf_le_right
  have hEsolv : IsSolvable E :=
    odd_order_theorem E
      (hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hED))
  have hPE : P ≤ E := by
    change d.choice.P ≤ W ⊓ D
    rw [d.choice.P_eq_map]
    exact Subgroup.map_subtype_le (d.choice.S : Subgroup ↥(W ⊓ D))
  obtain ⟨hHcentral, hDcomm⟩ :=
    (show subgroupCentralizerIn H P = ⊥ ∧ ⁅D, P⁆ = H from by
      simpa [H, P] using proposition102_H_core d d106 ht hDodd hDnorm)
  have hE_normal : (E.subgroupOf D).Normal := by
    simpa [E] using hW.inf_normal_in_right hDle
  have hDnormE : D ≤ Subgroup.normalizer (E : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hED).mp hE_normal
  have hCcentralP : C ≤ Subgroup.centralizer (P : Set X) := by
    change d.choice.initial.A1 ⊓
      Subgroup.centralizer (d.choice.P : Set X) ≤
      Subgroup.centralizer (d.choice.P : Set X)
    exact inf_le_right
  have hC_D : C ≤ D := by
    change d.choice.initial.A1 ⊓
      Subgroup.centralizer (d.choice.P : Set X) ≤ D
    exact inf_le_left.trans (by
      have hAV : d.choice.initial.A1 ≤ peterfalviV D t := by
        rw [d.choice.initial.A1_eq]
        exact inf_le_left
      exact hAV.trans inf_le_left)
  have hCnormE : C ≤ Subgroup.normalizer (E : Set X) := hC_D.trans hDnormE
  have hD_eq : D = E ⊔ C := by
    simpa [E, C] using proposition102_D_eq_E_sup_C hW hDle d
  have hEder : (derivedSubgroup E).map E.subtype = ⁅E, P⁆ := by
    apply map_derivedSubgroup_eq_commutator_of_solvable_mul hPE hEsolv
      (inferInstance : IsMulCommutative P)
    simpa [E, P] using d.E_eq_derived_mul_P
  have hEcommH : ⁅E, P⁆ = H :=
    (proposition102_commutator_sup_eq_left hD_eq hCnormE hCcentralP).symm.trans
      hDcomm
  have hderivedH : (derivedSubgroup E).map E.subtype = H :=
    hEder.trans hEcommH
  have hEmul : (E : Set X) = (H : Set X) * (P : Set X) := by
    calc
      (E : Set X) =
          ((derivedSubgroup E).map E.subtype : Set X) * (P : Set X) := by
        simpa [E, P] using d.E_eq_derived_mul_P
      _ = (H : Set X) * (P : Set X) := by rw [hderivedH]
  have hinf : (derivedSubgroup E).map E.subtype ⊓ peterfalviV D t =
      ⁅d.choice.initial.A1, d.choice.P⁆ := by
    rw [hderivedH]
    simpa [H] using d106.kernel_commutator_inf_V
  have hcentral :
      subgroupCentralizerIn ((derivedSubgroup E).map E.subtype) P = ⊥ := by
    rw [hderivedH]
    exact hHcentral
  exact {
    E_eq_H_mul_P := by simpa [E, H, P] using hEmul
    derived_eq_H := by simpa [E, H] using hderivedH
    commutator_eq_H := by simpa [E, H, P] using hEcommH
    derived_inf_V := by simpa [E] using hinf
    centralizer_derived_P := by simpa [E, P] using hcentral }

/-- The derived subgroup in part (a) is nilpotent by the checked
fixed-point-free prime-order endpoint. -/
public theorem proposition102_derived_nilpotent
    {X : Type u} [Group X] [Finite X]
    {M W D E V : Subgroup X} {t : X}
    {d : Lemma101Conclusion M W D E V t}
    (h : Proposition102PartAConclusion M W D E V t d) :
    Group.IsNilpotent ((derivedSubgroup E).map E.subtype) := by
  let P : Subgroup X := d.choice.P
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  have hPE : P ≤ E := by
    change d.choice.P ≤ E
    rw [d.choice.P_eq_map]
    exact Subgroup.map_subtype_le (d.choice.S : Subgroup E)
  have hHnormalE : (H.subgroupOf E).Normal := by
    change (((derivedSubgroup E).map E.subtype).subgroupOf E).Normal
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hPnormH : P ≤ Subgroup.normalizer (H : Set X) :=
    hPE.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.map_subtype_le (derivedSubgroup E))).mp hHnormalE)
  have hPprime : Nat.Prime (Nat.card P) := by
    simpa [P, d.P_card] using d.choice.p_prime
  apply proposition102_nilpotent_of_prime_fixedPointFree H P hPnormH hPprime
  simpa [H, P] using h.centralizer_derived_P

end CFSG.BenderSuzuki
