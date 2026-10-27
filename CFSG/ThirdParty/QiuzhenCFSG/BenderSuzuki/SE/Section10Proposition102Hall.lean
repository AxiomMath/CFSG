module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102PrimeSupport
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_3_a

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Proposition 10.2: Hall assembly

This module assembles the Hall part of Proposition 10.2(b).  The route keeps
the Lemma 10.6 prime set explicit until its ambient-card property identifies
it with the actual prime support of `C_A(P)`.  No conclusion of Proposition
10.2, Theorem 6, or Theorem SE is used as an input.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- A Hall prime set supported in the ambient group is the actual support of
the Hall subgroup. -/
public theorem proposition102_hall_primeSet_eq_of_prime_dvd_ambient_card
    {X : Type u} [Group X] [Finite X]
    {D C : Subgroup X} {pi : Set Nat.Primes}
    (hCD : C ≤ D)
    (hHall : IsHallSubgroup pi (C.subgroupOf D))
    (hpiD : ∀ q : Nat.Primes, q ∈ pi → q.val ∣ Nat.card D) :
    pi = subgroupPrimeSet C := by
  ext q
  constructor
  · intro hqpi
    have hqD : q.val ∣ Nat.card D := hpiD q hqpi
    have hqprod : q.val ∣ Nat.card (C.subgroupOf D) * (C.subgroupOf D).index := by
      simpa [Subgroup.card_mul_index] using hqD
    rcases q.property.dvd_mul.mp hqprod with hqCsub | hqidx
    · simpa [subgroupPrimeSet, natCard_subgroupOf_eq C D hCD] using hqCsub
    · exact (hHall.p_in_pi_of_p_dvd_index q hqidx hqpi).elim
  · intro hqC
    apply hHall.p_in_pi_of_p_dvd_card q
    simpa [subgroupPrimeSet, natCard_subgroupOf_eq C D hCD] using hqC

/-- Convert a normal complement in `D` to the corresponding complement of
subgroups of `D`. -/
public theorem proposition102_normalComplement_subtype_isComplement
    {X : Type u} [Group X]
    {D C K : Subgroup X}
    (hcomp : IsNormalComplementIn D C K) :
    (K.subgroupOf D).IsComplement' (C.subgroupOf D) := by
  classical
  have hKle : K ≤ D := hcomp.le_M
  have hCle : C ≤ D := by
    rw [← hcomp.sup_eq]
    exact le_sup_right
  have hKnormal : (K.subgroupOf D).Normal := by
    simpa using hcomp.normal_in_M
  letI : (K.subgroupOf D).Normal := hKnormal
  have hdisj : Disjoint (K.subgroupOf D) (C.subgroupOf D) := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxC
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hcomp.disjoint_D hxK hxC
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
  rw [Set.eq_univ_iff_forall]
  intro x
  have hsupTop : K.subgroupOf D ⊔ C.subgroupOf D = ⊤ := by
    calc
      K.subgroupOf D ⊔ C.subgroupOf D = (K ⊔ C).subgroupOf D :=
        (Subgroup.subgroupOf_sup hKle hCle).symm
      _ = D.subgroupOf D := by rw [hcomp.sup_eq]
      _ = ⊤ := Subgroup.subgroupOf_self D
  have hxSup : x ∈ K.subgroupOf D ⊔ C.subgroupOf D := by simp [hsupTop]
  rcases (Subgroup.mem_sup_of_normal_left
    (s := K.subgroupOf D) (t := C.subgroupOf D)).1 hxSup with
    ⟨k, hk, c, hc, hkc⟩
  exact Set.mem_mul.mpr ⟨k, hk, c, hc, hkc⟩

/-- If a Hall complement has prime set `pi`, then support primes of a subgroup
inside the complementary factor are forced outside `pi`; the displayed
definition of `pi` then transfers them to the kernel. -/
public theorem proposition102_prime_dvd_kernel_of_mem_support
    {X : Type u} [Group X] [Finite X]
    {D E H K : Subgroup X} {p : ℕ} [Fact p.Prime]
    {pi : Set Nat.Primes}
    (hHD : H ≤ D) (hHE : H ≤ E) (hED : E ≤ D)
    (hHall : IsHallSubgroup piᶜ (E.subgroupOf D))
    (hcop : Nat.Coprime p (Nat.card H))
    (hpi : ∀ q : Nat.Primes, q ∈ pi ↔
      q.val ∣ Nat.card D ∧ q.val ≠ p ∧
        ¬ q.val ∣ Nat.card K) :
    ∀ q : Nat.Primes, q ∈ subgroupPrimeSet H → q.val ∣ Nat.card K := by
  intro q hq
  have hqHcard : q.val ∣ Nat.card H := by
    simpa [subgroupPrimeSet] using hq
  have hqEcard : q.val ∣ Nat.card (E.subgroupOf D) := by
    have hqEcard' : q.val ∣ Nat.card E :=
      hqHcard.trans (Subgroup.card_dvd_of_le hHE)
    simpa [natCard_subgroupOf_eq E D hED] using hqEcard'
  have hqPiComp : q ∈ piᶜ :=
    hHall.p_in_pi_of_p_dvd_card q hqEcard
  have hqD : q.val ∣ Nat.card D :=
    hqHcard.trans (Subgroup.card_dvd_of_le hHD)
  have hqNotP : q.val ≠ p := by
    intro hqp
    have hpNotH : ¬ p ∣ Nat.card H :=
      (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcop
    exact hpNotH (by simpa [hqp] using hqHcard)
  by_contra hqK
  apply hqPiComp
  exact hpi q |>.2 ⟨hqD, hqNotP, hqK⟩

/-- The local Hall package needed for Proposition 10.2(b). -/
public structure Proposition102HallLocalData
    {X : Type u} [Group X] [Finite X]
    (D E : Subgroup X) (t : X) : Prop where
  derived_normal_D :
    (((derivedSubgroup E).map E.subtype).subgroupOf D).Normal
  derived_hall_D :
    IsHallSubgroup (subgroupPrimeSet ((derivedSubgroup E).map E.subtype))
      (((derivedSubgroup E).map E.subtype).subgroupOf D)
  support_dvd_kernel :
    ∀ q : Nat.Primes,
      q ∈ subgroupPrimeSet ((derivedSubgroup E).map E.subtype) →
      q.val ∣ Nat.card (Subgroup.closure (peterfalviKSet D t))

/-- Proposition 10.2(b), first assembled in the local subgroup `D`. -/
public theorem proposition102_part_b_hall_D
    {X : Type u} [Group X] [Finite X]
    {M W D : Subgroup X} {t : X}
    (hW : IsMinimalNormalSupplement M D W)
    (hDle : D ≤ M)
    (d : Lemma101Conclusion M W D (W ⊓ D) (peterfalviV D t) t)
    (d106 : Lemma106Conclusion M W D (W ⊓ D)
      (peterfalviV D t) t d)
    (hA : Proposition102PartAConclusion M W D (W ⊓ D)
      (peterfalviV D t) t d) :
    Proposition102HallLocalData D (W ⊓ D) t := by
  classical
  let E : Subgroup X := W ⊓ D
  let p : ℕ := d.choice.p
  let P : Subgroup X := d.choice.P
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  let C : Subgroup X := lemma104C d
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let N : Subgroup X := K ⊔ d.choice.initial.A1
  have hED : E ≤ D := by
    dsimp [E]
    exact inf_le_right
  have hE_normal : (E.subgroupOf D).Normal := by
    dsimp [E]
    simpa using hW.inf_normal_in_right hDle
  have hHnormalD : (H.subgroupOf D).Normal := by
    have hDnormE : D ≤ Subgroup.normalizer (E : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hED).mp hE_normal
    have hNormEnormH : Subgroup.normalizer (E : Set X) ≤
        Subgroup.normalizer (H : Set X) := by
      dsimp [H]
      simpa using
        (section8_normalizer_map_subtype_le_of_characteristic
          (H := E) (K := derivedSubgroup E))
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((Subgroup.map_subtype_le (derivedSubgroup E)).trans hED)).2
        (hDnormE.trans hNormEnormH)
  have hP_E : P ≤ E := by
    dsimp [P, E]
    rw [d.choice.P_eq_map]
    exact Subgroup.map_subtype_le (d.choice.S : Subgroup E)
  have hH_eq : H = lemma106H d := by
    simpa [H, E] using hA.derived_eq_H
  have hEset : (E : Set X) = (H : Set X) * (P : Set X) := by
    rw [hH_eq]
    simpa [E, P] using hA.E_eq_H_mul_P
  have hHP : E = H ⊔ P := by
    apply le_antisymm
    · intro x hx
      change x ∈ (E : Set X) at hx
      rw [hEset] at hx
      rcases Set.mem_mul.mp hx with ⟨h, hh, p0, hp0, hmul⟩
      rw [← hmul]
      exact (H ⊔ P).mul_mem
        ((show H ≤ H ⊔ P from le_sup_left) hh)
        ((show P ≤ H ⊔ P from le_sup_right) hp0)
    · exact sup_le (Subgroup.map_subtype_le (derivedSubgroup E)) hP_E
  have hcompE : IsNormalComplementIn D C E := by
    have hcomp := d106.normal_complement
    have hsup : H ⊔ P = lemma106H d ⊔ d.choice.P := by
      rw [hH_eq]
    refine { le_M := ?_, normal_in_M := ?_, sup_eq := ?_, disjoint_D := ?_ }
    · rw [hHP, hsup]
      exact hcomp.le_M
    · rw [hHP, hsup]
      exact hcomp.normal_in_M
    · rw [hHP, hsup]
      exact hcomp.sup_eq
    · rw [hHP, hsup]
      exact hcomp.disjoint_D
  have hC_le_D : C ≤ D := by
    rw [← hcompE.sup_eq]
    exact le_sup_right
  have hCsubHall0 : IsHallSubgroup (lemma106Pi d)
      (C.subgroupOf D) := by
    simpa [C] using d106.C_hall_D
  have hPi_eq_C : lemma106Pi d = subgroupPrimeSet C := by
    refine proposition102_hall_primeSet_eq_of_prime_dvd_ambient_card
      hC_le_D hCsubHall0 ?_
    intro q hq
    exact hq.1
  have hEsubComplement :
      (E.subgroupOf D).IsComplement' (C.subgroupOf D) :=
    proposition102_normalComplement_subtype_isComplement hcompE
  have hEHallPi : IsHallSubgroup (lemma106Pi d)ᶜ
      (E.subgroupOf D) :=
    Section14.section14_complement_isHall_compl_of_isHall
      hCsubHall0 hEsubComplement.symm
  have hEHall : IsHallSubgroup (subgroupPrimeSet C)ᶜ
      (E.subgroupOf D) := by
    rw [← hPi_eq_C]
    exact hEHallPi
  have hH_le_N : H ≤ N := by
    have hA_V : d.choice.initial.A1 ≤ peterfalviV D t := by
      rw [d.choice.initial.A1_eq]
      exact inf_le_left
    have hPnormA : P ≤ Subgroup.normalizer
        (d.choice.initial.A1 : Set X) := by
      exact d.choice.P_le_V.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hA_V).mp
          d.choice.initial.A1_normal_V)
    have hAP_le_A : ⁅d.choice.initial.A1, P⁆ ≤ d.choice.initial.A1 := by
      rw [Subgroup.commutator_le]
      intro a ha q hq
      have hqnorm : q ∈ Subgroup.normalizer
          (d.choice.initial.A1 : Set X) := hPnormA hq
      have hconj : q * a⁻¹ * q⁻¹ ∈ d.choice.initial.A1 :=
        (Subgroup.mem_normalizer_iff.mp hqnorm a⁻¹).1
          (d.choice.initial.A1.inv_mem ha)
      simpa [commutatorElement_def, mul_assoc] using
        d.choice.initial.A1.mul_mem ha hconj
    rw [hH_eq]
    apply sup_le
    · exact le_sup_left
    · exact hAP_le_A.trans le_sup_right
  have hN_eq_core : N = (pPrimeCore p D).map D.subtype := by
    simpa [N, K, p] using d.kernel_sup_A1_eq_pPrimeCore
  have hcardN : Nat.card N = Nat.card (pPrimeCore p D) := by
    rw [hN_eq_core, Subgroup.card_map_of_injective D.subtype_injective]
  have hp : p.Prime := by simpa [p] using d.choice.p_prime
  letI : Fact p.Prime := ⟨hp⟩
  have hcop_pN : Nat.Coprime p (Nat.card N) := by
    rw [hcardN]
    exact pPrimeCore_coprime_card
  have hcop_pH : Nat.Coprime p (Nat.card H) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hH_le_N) hcop_pN
  have hHsubEindex : (H.subgroupOf E).index = p := by
    change (((derivedSubgroup E).map E.subtype).subgroupOf E).index = p
    rw [subgroupOf_map_subtype_eq]
    rw [Subgroup.index_eq_card]
    simpa [E, p, derivedSubgroup] using d.card_abelianization_eq_p
  have hHindexDfactor :
      (H.subgroupOf D).index = p * (E.subgroupOf D).index := by
    have hrel := Subgroup.relIndex_mul_relIndex H E D
      (Subgroup.map_subtype_le (derivedSubgroup E)) hED
    simpa [Subgroup.relIndex, hHsubEindex] using hrel.symm
  have hHD : H ≤ D :=
    (Subgroup.map_subtype_le (derivedSubgroup E)).trans hED
  have hHallD : IsHallSubgroup (subgroupPrimeSet H)
      (H.subgroupOf D) := by
    refine isHallSubgroup_of (G := D)
      (π := subgroupPrimeSet H) (H := H.subgroupOf D) ?_ ?_
    · intro q hq
      simpa [subgroupPrimeSet, natCard_subgroupOf_eq H D hHD] using hq
    · intro q hqSupport hqIndex
      have hqHcard : q.val ∣ Nat.card H := by
        simpa [subgroupPrimeSet] using hqSupport
      have hqEcard : q.val ∣ Nat.card (E.subgroupOf D) := by
        have hqEcard' : q.val ∣ Nat.card E :=
          hqHcard.trans (Subgroup.card_dvd_of_le
            (Subgroup.map_subtype_le (derivedSubgroup E)))
        simpa [natCard_subgroupOf_eq E D hED] using hqEcard'
      have hqEpiComp : q ∈ (subgroupPrimeSet C)ᶜ :=
        hEHall.p_in_pi_of_p_dvd_card q hqEcard
      have hqNotEIndex : ¬ q.val ∣ (E.subgroupOf D).index := by
        intro hqEidx
        exact (hEHall.p_in_pi_of_p_dvd_index q hqEidx) hqEpiComp
      have hqNotP : ¬ q.val ∣ p := by
        have hcop_pq : Nat.Coprime p q.val :=
          Nat.Coprime.of_dvd_right hqHcard hcop_pH
        exact q.property.coprime_iff_not_dvd.mp hcop_pq.symm
      rw [hHindexDfactor] at hqIndex
      exact q.property.not_dvd_mul hqNotP hqNotEIndex hqIndex
  have hSupportK : ∀ q : Nat.Primes,
      q ∈ subgroupPrimeSet H → q.val ∣ Nat.card K := by
    apply proposition102_prime_dvd_kernel_of_mem_support
      (D := D) (E := E) (H := H) (K := K) (p := p)
      (pi := lemma106Pi d) hHD
      (Subgroup.map_subtype_le (derivedSubgroup E)) hED hEHallPi hcop_pH
    intro q
    simp [lemma106Pi, K, p]
  exact {
    derived_normal_D := by simpa [H, E] using hHnormalD
    derived_hall_D := by simpa [H, E] using hHallD
    support_dvd_kernel := by simpa [H, E, K] using hSupportK }

/-- Promote local Hall data to the ambient group using the checked
Corollary 7.12/Sylow endpoint. -/
public theorem proposition102_hall_ambient_of_local_normal
    {X : Type u} [Group X] [Finite X]
    {M D H : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (hD : D = M ⊓ rightConjugate M t)
    (hHD : H ≤ D)
    (hNormal : (H.subgroupOf D).Normal)
    (hHallD : IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf D))
    (hSupport : ∀ q : Nat.Primes, q ∈ subgroupPrimeSet H →
      q.val ∣ Nat.card (Subgroup.closure (peterfalviKSet D t))) :
    IsHallSubgroup (subgroupPrimeSet H) H := by
  letI : (H.subgroupOf D).Normal := hNormal
  apply proposition102_hall_of_subgroupOf_and_ambient_sylows hHD hHallD
  intro q hq
  obtain ⟨Q, hQbase⟩ :=
    proposition102_ambient_sylow_of_prime_dvd_kernel
      hM ht htM d83 h42 q.property (by simpa [hD] using hSupport q hq)
  have hQD : (Q : Subgroup X) ≤ D := by
    simpa [hD] using hQbase
  let QD : Subgroup D := (Q : Subgroup X).subgroupOf D
  have hQDp : IsPGroup q.val QD :=
    Q.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hQD).symm
  have hQDle : QD ≤ H.subgroupOf D :=
    section12_pSubgroup_le_normal_hall_of_prime_mem hHallD hq hQDp
  refine ⟨Q, ?_⟩
  intro x hxQ
  have hxQD : (⟨x, hQD hxQ⟩ : D) ∈ QD := hxQ
  exact hQDle hxQD

/-- Proposition 10.2(b)'s Hall conclusion in the ambient group `X`. -/
public theorem proposition102_part_b_hall_X
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (d106 : Lemma106Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t d)
    (hA : Proposition102PartAConclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t d)
    (h42 : II1Lemma42PrimeTransfer (X := X)) :
    let D : Subgroup X := M ⊓ rightConjugate M t
    let E : Subgroup X := W ⊓ D
    let H : Subgroup X := (derivedSubgroup E).map E.subtype
    IsHallSubgroup (subgroupPrimeSet H) H := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let E : Subgroup X := W ⊓ D
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  have hLocal : Proposition102HallLocalData D E t := by
    simpa [D, E] using proposition102_part_b_hall_D
      (D := D) hW (by simpa [D] using (inf_le_left : D ≤ M)) d d106 hA
  have hHD : H ≤ D := by
    exact (Subgroup.map_subtype_le (derivedSubgroup E)).trans inf_le_right
  exact proposition102_hall_ambient_of_local_normal hM ht htM d83 h42
    (by rfl) hHD hLocal.derived_normal_D hLocal.derived_hall_D
    hLocal.support_dvd_kernel

end CFSG.BenderSuzuki
