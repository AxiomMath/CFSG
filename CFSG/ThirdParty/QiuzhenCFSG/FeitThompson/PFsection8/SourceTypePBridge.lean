module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_13
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_7_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_5_to_10
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_9
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_8
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_15

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.Section8

universe u v w

private theorem sourceTypeP_complementIn_isComplement_subgroupOf
    {G : Type u} [Group G] [Finite G]
    {M H K : Subgroup G}
    (hcomp : section12ComplementIn M H K)
    [hHNormal : (H.subgroupOf M).Normal] :
    (K.subgroupOf M).IsComplement' (H.subgroupOf M) := by
  rcases hcomp with ⟨hHM, hKM, hsup, hdisj⟩
  have hsup_local : K.subgroupOf M ⊔ H.subgroupOf M = ⊤ := by
    calc
      K.subgroupOf M ⊔ H.subgroupOf M = (K ⊔ H).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := K) (A' := H) (B := M) hKM hHM
      _ = ⊤ := by
        rw [sup_comm, hsup]
        simp
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxK hxH
    apply Subtype.ext
    exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxH,
      by simpa [Subgroup.mem_subgroupOf] using hxK⟩
  · simpa [hsup_local] using
      (Subgroup.mul_normal (K.subgroupOf M) (H.subgroupOf M)).symm

private theorem sourceTypeP_hallSubgroupIn_of_natCard_eq
    {G : Type u} [Group G] [Finite G]
    {π : Set Nat.Primes} {H K M : Subgroup G}
    (hKHall : section12HallSubgroupIn π K M)
    (hHM : H ≤ M)
    (hcard : Nat.card H = Nat.card K) :
    section12HallSubgroupIn π H M := by
  classical
  rcases hKHall with ⟨hKM, hKHallSub⟩
  refine ⟨hHM, ?_⟩
  have hcardHsub : Nat.card (H.subgroupOf M) = Nat.card H :=
    natCard_subgroupOf_eq H M hHM
  have hcardKsub : Nat.card (K.subgroupOf M) = Nat.card K :=
    natCard_subgroupOf_eq K M hKM
  have hcardSub : Nat.card (H.subgroupOf M) = Nat.card (K.subgroupOf M) := by
    rw [hcardHsub, hcardKsub, hcard]
  have hidxEq : (H.subgroupOf M).index = (K.subgroupOf M).index := by
    have hmulH :
        (H.subgroupOf M).index * Nat.card (H.subgroupOf M) = Nat.card M :=
      Subgroup.index_mul_card (H := H.subgroupOf M)
    have hmulK :
        (K.subgroupOf M).index * Nat.card (K.subgroupOf M) = Nat.card M :=
      Subgroup.index_mul_card (H := K.subgroupOf M)
    have hmul :
        (H.subgroupOf M).index * Nat.card (H.subgroupOf M) =
          (K.subgroupOf M).index * Nat.card (K.subgroupOf M) :=
      hmulH.trans hmulK.symm
    rw [hcardSub] at hmul
    exact Nat.mul_right_cancel (Nat.card_pos (α := K.subgroupOf M)) hmul
  refine isHallSubgroup_of (G := M) (π := π) (H := H.subgroupOf M) ?_ ?_
  · intro p hpH
    exact hKHallSub.p_in_pi_of_p_dvd_card p (by
      simpa [hcardHsub, hcardKsub, hcard] using hpH)
  · intro p hpπ hpidx
    exact (hKHallSub.p_in_pi_of_p_dvd_index p (by
      simpa [hidxEq] using hpidx)) hpπ

private theorem sourceTypeP_exists_primeOrderSubgroup_of_ne_bot
    {G : Type u} [Group G] [Finite G]
    {H : Subgroup G}
    (hHne : H ≠ ⊥) :
    ∃ X : Subgroup G, X ∈ section12PrimeOrderSubgroups H := by
  classical
  have hcard_ne_one : Nat.card H ≠ 1 := by
    intro hcard
    exact hHne ((Subgroup.card_eq_one (H := H)).1 hcard)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨p, hpprime, hpdiv⟩
  haveI : Fact p.Prime := ⟨hpprime⟩
  rcases exists_prime_orderOf_dvd_card' (G := H) p hpdiv with ⟨zH, hzH_order⟩
  let z : G := zH
  refine ⟨Subgroup.zpowers z, ?_⟩
  have hzH : z ∈ H := zH.property
  have hz_order : orderOf z = p := by
    simpa [z, Subgroup.orderOf_coe] using hzH_order
  refine ⟨Subgroup.zpowers_le.mpr hzH, ⟨⟨p, hpprime⟩, ?_⟩⟩
  simp [z, Nat.card_zpowers, hz_order]

private theorem sourceTypeP_sylow_map_to_overgroup_sylow
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes} {K : Subgroup H}
    (hKHall : IsHallSubgroup π K) {p : Nat.Primes} (hpπ : p ∈ π)
    (P : Sylow p.val K) :
    ∃ PH : Sylow p.val H, (PH : Subgroup H) = (P : Subgroup K).map K.subtype := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let Psub : Subgroup H := (P : Subgroup K).map K.subtype
  have hPsubp : IsPGroup p.val Psub :=
    IsPGroup.map (p := p.val) (H := (P : Subgroup K)) P.isPGroup' K.subtype
  have hnot_index : ¬ p.val ∣ Psub.index := by
    intro hpidx
    have hidx : Psub.index = (P : Subgroup K).index * K.index := by
      simpa [Psub] using
        (Subgroup.index_map_subtype (H := K) (K := (P : Subgroup K)))
    have hp_prod : p.val ∣ (P : Subgroup K).index * K.index := by
      simpa [hidx] using hpidx
    rcases p.property.dvd_or_dvd hp_prod with hpPidx | hpKidx
    · exact P.not_dvd_index hpPidx
    · exact (hKHall.p_in_pi_of_p_dvd_index p hpKidx) hpπ
  let PH : Sylow p.val H := hPsubp.toSylow hnot_index
  exact ⟨PH, by simp [PH, Psub, IsPGroup.toSylow_coe]⟩

private theorem sourceTypeP_primeRank_le_one_of_cyclic_sylow
    {p : ℕ} {R : Type*} [Group R] [Finite R] [Fact p.Prime]
    (S : Sylow p R) (hS_cyc : IsCyclic (S : Subgroup R)) :
    primeRank p R ≤ 1 := by
  rw [primeRank]
  refine csSup_le ?_ ?_
  · letI : IsCyclic (S : Subgroup R) := hS_cyc
    refine ⟨0, ?_⟩
    exact ⟨(S : Subgroup R), S.isPGroup', inferInstance, by simp⟩
  · intro n hn
    rcases hn with ⟨A, hAp, _hAcomm, hnA⟩
    obtain ⟨T, hA_le_T⟩ := IsPGroup.exists_le_sylow (G := R) (p := p) hAp
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R S T
    have hT_cyc : IsCyclic (T : Subgroup R) := by
      let e :
          (S : Subgroup R) ≃* ((g • S : Sylow p R) : Subgroup R) :=
        Subgroup.equivMapOfInjective
          (f := (MulAut.conj g).toMonoidHom) (S : Subgroup R)
          (EquivLike.injective (MulAut.conj g))
      have hconj_cyc : IsCyclic (((g • S : Sylow p R) : Subgroup R)) :=
        e.isCyclic.mp hS_cyc
      rw [← hg]
      exact hconj_cyc
    have hA_cyc : IsCyclic A := Subgroup.isCyclic_of_le hA_le_T
    exact hnA.trans (generatorRank_le_one_of_isCyclic (G := A) hA_cyc)

private theorem sourceTypeP_primeRank_le_one_of_cyclic_hall_subgroup
    {R : Type*} [Group R] [Finite R]
    {π : Set Nat.Primes} {K : Subgroup R} {p : Nat.Primes}
    (hKHall : IsHallSubgroup π K)
    (hpπ : p ∈ π)
    (hKcyc : IsCyclic K) :
    primeRank p.val R ≤ 1 := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let PK : Sylow p.val K := Classical.choice (Sylow.nonempty (p := p.val) (G := K))
  rcases sourceTypeP_sylow_map_to_overgroup_sylow
      (H := R) (K := K) hKHall hpπ PK with
    ⟨PR, hPReq⟩
  have hPKcyclic : IsCyclic (PK : Subgroup K) := by
    letI : IsCyclic K := hKcyc
    exact Subgroup.isCyclic_of_le (show (PK : Subgroup K) ≤ ⊤ from le_top)
  let Pmap : Subgroup R := (PK : Subgroup K).map K.subtype
  have hPmapCyclic : IsCyclic Pmap := by
    let e :
        (PK : Subgroup K) ≃* Pmap :=
      Subgroup.equivMapOfInjective
        (f := K.subtype) (PK : Subgroup K) K.subtype_injective
    exact e.isCyclic.mp hPKcyclic
  have hPRcyclic : IsCyclic (PR : Subgroup R) := by
    rw [hPReq]
    simpa [Pmap] using hPmapCyclic
  exact sourceTypeP_primeRank_le_one_of_cyclic_sylow PR hPRcyclic

private theorem sourceTypeP_natCard_eq_of_complements_same_normal_left
    {G : Type u} [Group G] [Finite G]
    {M D H K : Subgroup G}
    (hDnormal : (D.subgroupOf M).Normal)
    (hHcomp : section12ComplementIn M D H)
    (hKcomp : section12ComplementIn M K D) :
    Nat.card H = Nat.card K := by
  classical
  letI : (D.subgroupOf M).Normal := hDnormal
  have hKcompSymm : section12ComplementIn M D K := by
    refine ⟨hKcomp.2.1, hKcomp.1, ?_, hKcomp.2.2.2.symm⟩
    rw [sup_comm]
    exact hKcomp.2.2.1
  have hHlocal : (H.subgroupOf M).IsComplement' (D.subgroupOf M) :=
    sourceTypeP_complementIn_isComplement_subgroupOf
      (M := M) (H := D) (K := H) hHcomp
  have hKlocal : (K.subgroupOf M).IsComplement' (D.subgroupOf M) :=
    sourceTypeP_complementIn_isComplement_subgroupOf
      (M := M) (H := D) (K := K) hKcompSymm
  have hDindexH : (D.subgroupOf M).index = Nat.card (H.subgroupOf M) :=
    hHlocal.index_eq_card
  have hDindexK : (D.subgroupOf M).index = Nat.card (K.subgroupOf M) :=
    hKlocal.index_eq_card
  have hHcard : Nat.card (H.subgroupOf M) = Nat.card H :=
    natCard_subgroupOf_eq H M hHcomp.2.1
  have hKcard : Nat.card (K.subgroupOf M) = Nat.card K :=
    natCard_subgroupOf_eq K M hKcomp.1
  calc
    Nat.card H = Nat.card (H.subgroupOf M) := hHcard.symm
    _ = (D.subgroupOf M).index := hDindexH.symm
    _ = Nat.card (K.subgroupOf M) := hDindexK
    _ = Nat.card K := hKcard

private theorem sourceTypeP_left_isHall_of_right_hall
    {G : Type u} [Group G] [Finite G]
    {M H K : Subgroup G}
    (hcomp : section12ComplementIn M H K)
    (hHnormal : (H.subgroupOf M).Normal)
    (hKHall : section16HallSubgroupOf K M) :
    IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf M) := by
  classical
  letI : (H.subgroupOf M).Normal := hHnormal
  have hcomp' : (K.subgroupOf M).IsComplement' (H.subgroupOf M) :=
    sourceTypeP_complementIn_isComplement_subgroupOf
      (M := M) (H := H) (K := K) hcomp
  rcases hcomp with ⟨hHM, _hKM, _hsup, _hdisj⟩
  rcases hKHall with ⟨_hKM, hKHallSub⟩
  refine isHallSubgroup_of (G := M) (π := subgroupPrimeSet H)
    (H := H.subgroupOf M) ?_ ?_
  · intro p hpH
    have hcardH : Nat.card (H.subgroupOf M) = Nat.card H :=
      natCard_subgroupOf_eq H M hHM
    simpa [subgroupPrimeSet, hcardH] using hpH
  · intro p hpH hpidxH
    have hpKcard : p.val ∣ Nat.card (K.subgroupOf M) := by
      simpa [hcomp'.index_eq_card] using hpidxH
    have hpKπ : p ∈ subgroupPrimeSet K :=
      hKHallSub.p_in_pi_of_p_dvd_card p hpKcard
    have hpHcard : p.val ∣ Nat.card (H.subgroupOf M) := by
      have hcardH : Nat.card (H.subgroupOf M) = Nat.card H :=
        natCard_subgroupOf_eq H M hHM
      simpa [subgroupPrimeSet, hcardH] using hpH
    have hpKidx : p.val ∣ (K.subgroupOf M).index := by
      simpa [hcomp'.symm.index_eq_card] using hpHcard
    exact (hKHallSub.p_in_pi_of_p_dvd_index p hpKidx) hpKπ

private theorem sourceTypeP_complementIn_left_relIndex_eq_card_right
    {G : Type u} [Group G] [Finite G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    [hKNormal : (K.subgroupOf M).Normal] :
    K.relIndex M = Nat.card L := by
  have hcomp' : (L.subgroupOf M).IsComplement' (K.subgroupOf M) :=
    sourceTypeP_complementIn_isComplement_subgroupOf
      (M := M) (H := K) (K := L) hcomp
  have hLsubcard : Nat.card (L.subgroupOf M) = Nat.card L :=
    natCard_subgroupOf_eq L M hcomp.2.1
  have hidx : (K.subgroupOf M).index = Nat.card (L.subgroupOf M) :=
    hcomp'.index_eq_card
  simpa [Subgroup.relIndex, hLsubcard] using hidx

private theorem sourceTypeP_card_W1_dvd_card_typeF_complement
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 UF U1 U0 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2)
    (hF : typeFData M MF UF U1 U0) :
    Nat.card W1 ∣ Nat.card UF := by
  classical
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, hMcomp, _hUleD, _hUnil,
      _hW1norm, hDercomp, _hMFnotcyc, _hSecond, _hFit, _hFitDer,
      _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  rcases hF with
    ⟨_hsolv, _hodd, hMFsource, _hMFne, _hMFltM, _hUFne, hMFcomp,
      _hU1le, _hU1comm, _hU1norm, _hCentF, _hU0le, _hexp, _hfrob⟩
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : ((ambientDerivedSubgroup M).subgroupOf M).Normal := hDnormal
  have hW1card :
      Nat.card W1 = (ambientDerivedSubgroup M).relIndex M := by
    exact (sourceTypeP_complementIn_left_relIndex_eq_card_right
      (M := M) (K := ambientDerivedSubgroup M) (L := W1) hMcomp).symm
  have hUFcard : MF.relIndex M = Nat.card UF := by
    have hMFnormal : (MF.subgroupOf M).Normal := by
      exact hMFsource.1.2.1
    letI : (MF.subgroupOf M).Normal := hMFnormal
    exact sourceTypeP_complementIn_left_relIndex_eq_card_right
      (M := M) (K := MF) (L := UF) hMFcomp
  have hDleM : ambientDerivedSubgroup M ≤ M :=
    section12_ambientDerivedSubgroup_le (G := G) (E := M)
  have hMFleD : MF ≤ ambientDerivedSubgroup M := hDercomp.1
  have hrel_dvd :
      (ambientDerivedSubgroup M).relIndex M ∣ MF.relIndex M := by
    let Dsub : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let MFsub : Subgroup M := MF.subgroupOf M
    have hMFsub_le_Dsub : MFsub ≤ Dsub := by
      intro x hx
      exact hMFleD hx
    have hmul : MFsub.relIndex Dsub * Dsub.index = MFsub.index :=
      Subgroup.relIndex_mul_index hMFsub_le_Dsub
    have hdvd : Dsub.index ∣ MFsub.index :=
      ⟨MFsub.relIndex Dsub, by rw [Nat.mul_comm, hmul]⟩
    simpa [Dsub, MFsub, Subgroup.relIndex] using hdvd
  simpa [hW1card, hUFcard] using hrel_dvd

private theorem sourceTypeP_prime_dvd_card_U0_of_typeF
    {G : Type u} [Group G] [Finite G]
    {UF U0 : Subgroup G} {p : ℕ}
    (hp : p.Prime)
    (hpUF : p ∣ Nat.card UF)
    (hFexp : Monoid.exponent U0 = Monoid.exponent UF) :
    p ∣ Nat.card U0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases exists_prime_orderOf_dvd_card' (G := UF) p hpUF with ⟨x, hxorder⟩
  have hpExpUF : p ∣ Monoid.exponent UF := by
    simpa [hxorder] using Monoid.order_dvd_exponent x
  have hpExpU0 : p ∣ Monoid.exponent U0 := by
    simpa [hFexp] using hpExpUF
  exact hpExpU0.trans (Group.exponent_dvd_nat_card (G := U0))

private theorem sourceTypeP_typeF_prime_mem_U0_of_prime_mem_W1
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 UF U1 U0 : Subgroup G} {p : Nat.Primes}
    (hP : typePDefinitionData M MF U W1 W2)
    (hF : typeFData M MF UF U1 U0)
    (hpW1 : p ∈ subgroupPrimeSet W1) :
    p ∈ subgroupPrimeSet U0 := by
  rcases hF with
    ⟨_hsolv, _hodd, _hMFsource, _hMFne, _hMFltM, _hUFne, _hMFcomp,
      _hU1le, _hU1comm, _hU1norm, _hCentF, _hU0le, hExp, _hfrob⟩
  have hcard_dvd :
      Nat.card W1 ∣ Nat.card UF :=
    sourceTypeP_card_W1_dvd_card_typeF_complement hP
      ⟨_hsolv, _hodd, _hMFsource, _hMFne, _hMFltM, _hUFne, _hMFcomp,
        _hU1le, _hU1comm, _hU1norm, _hCentF, _hU0le, hExp, _hfrob⟩
  have hpUF : p.val ∣ Nat.card UF :=
    (show p.val ∣ Nat.card W1 from by simpa [subgroupPrimeSet] using hpW1).trans
      hcard_dvd
  exact sourceTypeP_prime_dvd_card_U0_of_typeF (UF := UF) (U0 := U0)
    p.property hpUF hExp

private theorem sourceTypeP_exists_prime_order_element_in_U0_of_prime_mem_W1
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 UF U1 U0 : Subgroup G} {p : Nat.Primes}
    (hP : typePDefinitionData M MF U W1 W2)
    (hF : typeFData M MF UF U1 U0)
    (hpW1 : p ∈ subgroupPrimeSet W1) :
    ∃ a : G, a ∈ U0 ∧ a ≠ 1 ∧ orderOf a = p.val := by
  classical
  have hpU0 : p ∈ subgroupPrimeSet U0 :=
    sourceTypeP_typeF_prime_mem_U0_of_prime_mem_W1 hP hF hpW1
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases exists_prime_orderOf_dvd_card' (G := U0) p.val
      (by simpa [subgroupPrimeSet] using hpU0) with
    ⟨a0, ha0order⟩
  let a : G := a0
  refine ⟨a, a0.property, ?_, ?_⟩
  · intro ha
    have horder_one : orderOf a0 = 1 := orderOf_eq_one_iff.mpr (Subtype.ext ha)
    exact p.property.ne_one (ha0order.symm.trans horder_one)
  · simpa [a, Subgroup.orderOf_coe] using ha0order

private theorem sourceTypeP_exists_conjugate_mem_of_hall_prime_order
    {G : Type u} [Group G] [Finite G]
    {π : Set Nat.Primes} {H : Subgroup G}
    (hHall : IsHallSubgroup π H)
    {p : Nat.Primes}
    (hpπ : p ∈ π)
    {a : G}
    (haOrder : orderOf a = p.val) :
    ∃ y : G, y * a * y⁻¹ ∈ H := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let PH : Sylow p.val H := Classical.choice (Sylow.nonempty (p := p.val) (G := H))
  let Psub : Subgroup G := (PH : Subgroup H).map H.subtype
  have hPsub_p : IsPGroup p.val Psub := by
    simpa [Psub] using
      (IsPGroup.map (p := p.val) (H := (PH : Subgroup H)) PH.isPGroup' H.subtype)
  have hp_not_dvd_Hindex : ¬ p.val ∣ H.index := by
    intro hp_dvd
    exact (hHall.p_in_pi_of_p_dvd_index p hp_dvd) hpπ
  have hp_not_dvd_PHindex : ¬ p.val ∣ (PH : Subgroup H).index :=
    PH.not_dvd_index
  have hp_not_dvd_Psubindex : ¬ p.val ∣ Psub.index := by
    have hidx : Psub.index = (PH : Subgroup H).index * H.index := by
      simpa [Psub] using (Subgroup.index_map_subtype (K := (PH : Subgroup H)))
    rw [hidx]
    exact Nat.Prime.not_dvd_mul p.property hp_not_dvd_PHindex hp_not_dvd_Hindex
  let S : Sylow p.val G := IsPGroup.toSylow (p := p.val) hPsub_p hp_not_dvd_Psubindex
  have hS_le_H : (S : Subgroup G) ≤ H := by
    intro x hx
    change x ∈ Psub at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  let A : Subgroup G := Subgroup.zpowers a
  have hAp : IsPGroup p.val A := by
    exact IsPGroup.of_card (((Nat.card_zpowers a).trans haOrder).trans (pow_one p.val).symm)
  obtain ⟨Q, hAQ⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hAp
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G Q S
  refine ⟨y, ?_⟩
  have haQ : a ∈ (Q : Subgroup G) := hAQ (Subgroup.mem_zpowers a)
  have hayS : y * a * y⁻¹ ∈ (S : Subgroup G) := by
    have hmem : (MulAut.conj y) a ∈ ((y • Q : Sylow p.val G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul a (MulAut.conj y) (Q : Subgroup G) haQ
    simpa [MulAut.conj_apply, hy] using hmem
  exact hS_le_H hayS

private theorem sourceTypeP_exists_conjugate_in_W1_of_U0_prime
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 UF U1 U0 : Subgroup G} {p : Nat.Primes}
    (hP : typePDefinitionData M MF U W1 W2)
    (_hF : typeFData M MF UF U1 U0)
    (hpW1 : p ∈ subgroupPrimeSet W1)
    {a : G}
    (haU0 : a ∈ U0)
    (haOrder : orderOf a = p.val) :
    ∃ m : M, (m : G) * a * (m : G)⁻¹ ∈ W1 := by
  classical
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, hW1Hall, _hMcomp, _hUleD, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit, _hFitDer,
      _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  rcases hW1Hall with ⟨hW1M, hHallW1⟩
  rcases _hF with
    ⟨_hsolv, _hodd, _hMFsource, _hMFne, _hMFltM, _hUFne, hMFcomp,
      _hU1le, _hU1comm, _hU1norm, _hCentF, hU0le, _hExp, _hfrob⟩
  have haM : a ∈ M := hMFcomp.2.1 (hU0le haU0)
  have haOrderM : orderOf (⟨a, haM⟩ : M) = p.val := by
    simpa [Subgroup.orderOf_coe] using haOrder
  rcases sourceTypeP_exists_conjugate_mem_of_hall_prime_order
      (G := M) (π := subgroupPrimeSet W1)
      (H := W1.subgroupOf M) hHallW1 hpW1
      (a := ⟨a, haM⟩) haOrderM with
    ⟨m, hm⟩
  refine ⟨m, ?_⟩
  simpa [Subgroup.mem_subgroupOf] using hm

private theorem sourceTypeP_frobeniusJoin_centralizer_bot
    {G : Type u} [Group G] [Finite G]
    {K R : Subgroup G}
    (hfrob : section12FrobeniusJoinWithKernel K R)
    {r : G}
    (hr : r ∈ R)
    (hrne : r ≠ 1) :
    elementCentralizerIn (K.subgroupOf ((K ⊔ R : Subgroup G)))
        (⟨r, (le_sup_right : R ≤ (K ⊔ R : Subgroup G)) hr⟩ :
          (K ⊔ R : Subgroup G)) = ⊥ := by
  classical
  let L : Subgroup G := K ⊔ R
  let Ksub : Subgroup L := K.subgroupOf L
  let Rsub : Subgroup L := R.subgroupOf L
  have hfrobL : IsFrobeniusGroupWithKernelComplement Ksub Rsub := by
    simpa [section12FrobeniusJoinWithKernel, L, Ksub, Rsub] using hfrob
  have hrsub : (⟨r, (le_sup_right : R ≤ (K ⊔ R : Subgroup G)) hr⟩ : L) ∈ Rsub := by
    simpa [Rsub, Subgroup.mem_subgroupOf, L] using hr
  let rsub : Rsub := ⟨⟨r, (le_sup_right : R ≤ (K ⊔ R : Subgroup G)) hr⟩, hrsub⟩
  have hrsub_ne : rsub ≠ 1 := by
    intro h
    exact hrne (by simpa [rsub] using congrArg (fun t : Rsub => ((t : L) : G)) h)
  exact
    (lemma_3_1 Ksub Rsub
      (IsFrobeniusGroupWithKernelComplement.kernel_ne_bot hfrobL)
      (IsFrobeniusGroupWithKernelComplement.complement_ne_bot hfrobL)
      (IsFrobeniusGroupWithKernelComplement.normal hfrobL)
      (IsFrobeniusGroupWithKernelComplement.isComplement' hfrobL)).1
      hfrobL rsub hrsub_ne

private theorem sourceTypeP_mem_MF_of_conjBy_MF
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    {m : M} {y : G}
    (hyMF : y ∈ MF) :
    (m : G)⁻¹ * y * (m : G) ∈ MF := by
  rcases hMF.1 with ⟨hMFleM, hMFnorm, _hMFnil, _hMFhall⟩
  letI : (MF.subgroupOf M).Normal := hMFnorm
  have hyM : y ∈ M := hMFleM hyMF
  have hyloc : (⟨y, hyM⟩ : M) ∈ MF.subgroupOf M := by
    simpa [Subgroup.mem_subgroupOf] using hyMF
  have hconjloc :
      m⁻¹ * (⟨y, hyM⟩ : M) * m ∈ MF.subgroupOf M :=
    by simpa using hMFnorm.conj_mem (⟨y, hyM⟩ : M) hyloc m⁻¹
  simpa [Subgroup.mem_subgroupOf] using hconjloc

public theorem sourceTypeP_not_typeFData
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 UF U1 U0 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2)
    (hF : typeFData M MF UF U1 U0) : False := by
  classical
  rcases hP with
    ⟨hMF, _hW1cyc, hW1ne, hW1Hall, _hMcomp, _hUleD, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit, _hFitDer,
      hW2leInf, _hW2cyc, hW2ne, hCent, _hNorm⟩
  let hPfull : typePDefinitionData M MF U W1 W2 :=
    ⟨hMF, _hW1cyc, hW1ne, hW1Hall, _hMcomp, _hUleD, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit, _hFitDer,
      hW2leInf, _hW2cyc, hW2ne, hCent, _hNorm⟩
  rcases hF with
    ⟨_hsolv, _hodd, _hMFsourceF, _hMFneF, _hMFltM, _hUFne, _hMFcomp,
      _hU1le, _hU1comm, _hU1norm, _hCentF, hU0le, _hExp, hfrob⟩
  let hFfull : typeFData M MF UF U1 U0 :=
    ⟨_hsolv, _hodd, _hMFsourceF, _hMFneF, _hMFltM, _hUFne, _hMFcomp,
      _hU1le, _hU1comm, _hU1norm, _hCentF, hU0le, _hExp, hfrob⟩
  rcases sourceTypeP_exists_primeOrderSubgroup_of_ne_bot (G := G) hW1ne with
    ⟨X, hXprime⟩
  rcases hXprime with ⟨hXW1, p, hXcard⟩
  have hpW1 : p ∈ subgroupPrimeSet W1 := by
    have hpX : p.val ∣ Nat.card X := by rw [hXcard]
    exact hpX.trans (Subgroup.card_dvd_of_le hXW1)
  rcases sourceTypeP_exists_prime_order_element_in_U0_of_prime_mem_W1
      hPfull hFfull hpW1 with
    ⟨a, haU0, hane, haOrder⟩
  rcases sourceTypeP_exists_conjugate_in_W1_of_U0_prime
      hPfull hFfull hpW1 haU0 haOrder with
    ⟨m, hmaW1⟩
  let x : G := (m : G) * a * (m : G)⁻¹
  have hxW1 : x ∈ W1 := hmaW1
  have hxne : x ≠ 1 := by
    intro hx
    apply hane
    have hx' := congrArg (fun t => (m : G)⁻¹ * t * (m : G)) hx
    simpa [x, mul_assoc] using hx'
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW2ne with ⟨yW2, hyW2ne⟩
  let y : G := yW2
  have hyW2 : y ∈ W2 := yW2.property
  have hyne : y ≠ 1 := by
    intro hy
    exact hyW2ne (Subtype.ext hy)
  let z : G := (m : G)⁻¹ * y * (m : G)
  have hzMF : z ∈ MF :=
    sourceTypeP_mem_MF_of_conjBy_MF hMF (hW2leInf hyW2).1
  have hzy_ne : z ≠ 1 := by
    intro hz
    apply hyne
    have hz' := congrArg (fun t => (m : G) * t * (m : G)⁻¹) hz
    simpa [z, mul_assoc] using hz'
  have hyCentX : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := by
    simpa [hCent x hxW1 hxne] using hyW2
  have hzCentA : z ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcommYX : Commute y x :=
      Subgroup.mem_centralizer_singleton_iff.mp hyCentX.2
    exact (show Commute z a by
      unfold z x at *
      simpa [Commute, SemiconjBy, mul_assoc] using
        congrArg (fun t => (m : G)⁻¹ * t * (m : G)) hcommYX.eq)
  have hzElem :
      (⟨z, (le_sup_left : MF ≤ (MF ⊔ U0 : Subgroup G)) hzMF⟩ :
          (MF ⊔ U0 : Subgroup G)) ∈
        elementCentralizerIn (MF.subgroupOf (MF ⊔ U0 : Subgroup G))
          (⟨a, (le_sup_right : U0 ≤ (MF ⊔ U0 : Subgroup G)) haU0⟩ :
            (MF ⊔ U0 : Subgroup G)) := by
    refine ⟨?_, ?_⟩
    · simpa [Subgroup.mem_subgroupOf] using hzMF
    · change (⟨z, (le_sup_left : MF ≤ (MF ⊔ U0 : Subgroup G)) hzMF⟩ :
          (MF ⊔ U0 : Subgroup G)) ∈
        Subgroup.centralizer
          ({(⟨a, (le_sup_right : U0 ≤ (MF ⊔ U0 : Subgroup G)) haU0⟩ :
            (MF ⊔ U0 : Subgroup G))} : Set (MF ⊔ U0 : Subgroup G))
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcommZA : Commute z a :=
        Subgroup.mem_centralizer_singleton_iff.mp hzCentA
      ext
      exact hcommZA.eq
  have hcentBot :
      elementCentralizerIn (MF.subgroupOf (MF ⊔ U0 : Subgroup G))
          (⟨a, (le_sup_right : U0 ≤ (MF ⊔ U0 : Subgroup G)) haU0⟩ :
            (MF ⊔ U0 : Subgroup G)) = ⊥ :=
    sourceTypeP_frobeniusJoin_centralizer_bot hfrob haU0 hane
  have hzBot :
      (⟨z, (le_sup_left : MF ≤ (MF ⊔ U0 : Subgroup G)) hzMF⟩ :
          (MF ⊔ U0 : Subgroup G)) ∈
        (⊥ : Subgroup (MF ⊔ U0 : Subgroup G)) := by
    simpa [hcentBot] using hzElem
  exact hzy_ne (by simpa using congrArg Subtype.val (show
    (⟨z, (le_sup_left : MF ≤ (MF ⊔ U0 : Subgroup G)) hzMF⟩ :
      (MF ⊔ U0 : Subgroup G)) = 1 from by simpa using hzBot))

private theorem sourceTypeP_TISubset_of_nonidentityElements
    {G : Type u} [Group G] [Finite G] {X : Set G}
    (h : section16TISubset (section16NonidentityElements X)) :
    section16TISubset X := by
  have hsharp_conj : ∀ g : G,
      section16NonidentityElements (section16ConjugateSet X g) =
        section16ConjugateSet (section16NonidentityElements X) g := by
    intro g
    ext z
    constructor
    · rintro ⟨hz, hz1⟩
      rcases hz with ⟨x, hx, rfl⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      intro hx1
      apply hz1
      simp [hx1]
    · rintro ⟨x, ⟨hx, hx1⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      intro hconj_one
      apply hx1
      have := congrArg (fun t => g⁻¹ * t * g) hconj_one
      simpa [mul_assoc] using this
  intro g
  rcases h g with hconj | hdisj
  · left
    ext y
    constructor
    · intro hy
      by_cases hy1 : y = 1
      · rcases hy with ⟨x, hx, hxy⟩
        rw [hy1] at hxy
        have hx1 : x = 1 := by
          have := congrArg (fun t => g⁻¹ * t * g) hxy.symm
          simpa [mul_assoc] using this
        simpa [hy1, hx1] using hx
      · have hysharp : y ∈ section16NonidentityElements (section16ConjugateSet X g) :=
          ⟨hy, hy1⟩
        have : y ∈ section16ConjugateSet (section16NonidentityElements X) g := by
          simpa [hsharp_conj g] using hysharp
        have : y ∈ section16NonidentityElements X := by
          simpa [hconj] using this
        exact this.1
    · intro hy
      by_cases hy1 : y = 1
      · refine ⟨1, ?_, ?_⟩
        · simpa [← hy1] using hy
        · simp [hy1]
      · have : y ∈ section16NonidentityElements X := ⟨hy, hy1⟩
        have : y ∈ section16ConjugateSet (section16NonidentityElements X) g := by
          simpa [hconj] using this
        rcases this with ⟨x, hx, rfl⟩
        exact ⟨x, hx.1, rfl⟩
  · right
    intro y hy
    by_cases hy1 : y = 1
    · simp [hy1]
    · apply hdisj
      constructor
      · exact ⟨hy.1, hy1⟩
      · have : y ∈ section16NonidentityElements (section16ConjugateSet X g) :=
          ⟨hy.2, hy1⟩
        simpa [hsharp_conj g] using this

public theorem section16TypeIIToIVExtra_of_sourceCondition
    {G : Type u} [Group G] [Finite G]
    {M U W1 : Subgroup G}
    (h : typeIIToIVSourceCondition M U W1) :
    section16TypeIIToIVExtra M W1 :=
  ⟨h.2.1, sourceTypeP_TISubset_of_nonidentityElements h.2.2⟩

public theorem section16TypeCommon_of_source_typeP_with_T6
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2)
    (hT6 : ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥) :
    section16TypeCommon M MF U W1 W2 := by
  rcases hP with
    ⟨_hMF, hW1cyc, _hW1ne, hW1Hall, hMcomp, hUle, hUnil, hW1norm,
      hDercomp, hMFnotcyc, hSecond, hFit, hFitDer, hW2leInf, hW2cyc,
      hW2ne, hCent, hNorm⟩
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hDHall : section16HallSubgroupOf (ambientDerivedSubgroup M) M := by
    refine ⟨section12_ambientDerivedSubgroup_le (G := G) (E := M), ?_⟩
    exact sourceTypeP_left_isHall_of_right_hall
      (M := M) (H := ambientDerivedSubgroup M) (K := W1)
      hMcomp hDnormal hW1Hall
  have hW1card : Nat.card W1 = (ambientDerivedSubgroup M).relIndex M := by
    letI : ((ambientDerivedSubgroup M).subgroupOf M).Normal := hDnormal
    have hcomp' : (W1.subgroupOf M).IsComplement'
        ((ambientDerivedSubgroup M).subgroupOf M) :=
      sourceTypeP_complementIn_isComplement_subgroupOf
        (M := M) (H := ambientDerivedSubgroup M) (K := W1) hMcomp
    have hW1subcard : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
      natCard_subgroupOf_eq W1 M hMcomp.2.1
    have hidx : ((ambientDerivedSubgroup M).subgroupOf M).index =
        Nat.card (W1.subgroupOf M) := hcomp'.index_eq_card
    simpa [Subgroup.relIndex, hW1subcard] using hidx.symm
  have hW2le : W2 ≤ MF := hW2leInf.trans inf_le_left
  exact ⟨hDHall, hDercomp.1, hDercomp, hUnil, hW1norm, hW1cyc, hW1card,
    hMFnotcyc, hSecond, hFit.symm, hFitDer, hW2le, hW2ne, hW2cyc, hCent,
    hNorm, hT6, hW2leInf.trans inf_le_right⟩

public theorem section16TypeIII_of_source_typeIII_with_T6
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (h : typeIIIDefinitionData M MF)
    (hT6 : ∀ {U W1 W2 : Subgroup G},
      typePDefinitionData M MF U W1 W2 →
        ∀ A0 A1 : Subgroup G,
          section16PrimeOrderSubgroupOf A0 U →
            section16PrimeOrderSubgroupOf A1 U →
              section16ConjugateSubgroupsIn ⊤ A0 A1 →
                ¬ section16ConjugateSubgroupsIn M A0 A1 →
                  subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥) :
    section16TypeIII M MF := by
  rcases h with ⟨U, W1, W2, hP, hExtra, hcomm, hnorm⟩
  exact ⟨U, W1, W2, section16TypeCommon_of_source_typeP_with_T6 hP (hT6 hP),
    section16TypeIIToIVExtra_of_sourceCondition hExtra, hcomm, hnorm⟩

public theorem section16TypeIV_of_source_typeIV_with_T6
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (h : typeIVDefinitionData M MF)
    (hT6 : ∀ {U W1 W2 : Subgroup G},
      typePDefinitionData M MF U W1 W2 →
        ∀ A0 A1 : Subgroup G,
          section16PrimeOrderSubgroupOf A0 U →
            section16PrimeOrderSubgroupOf A1 U →
              section16ConjugateSubgroupsIn ⊤ A0 A1 →
                ¬ section16ConjugateSubgroupsIn M A0 A1 →
                  subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥) :
    section16TypeIV M MF := by
  rcases h with ⟨U, W1, W2, hP, hExtra, hncomm, hnorm⟩
  exact ⟨U, W1, W2, section16TypeCommon_of_source_typeP_with_T6 hP (hT6 hP),
    section16TypeIIToIVExtra_of_sourceCondition hExtra, hncomm, hnorm⟩

private theorem sourceTypeP_tau13_of_W1_prime
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hsourceP : typePDefinitionData M MF U W1 W2)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p W1) :
    p ∈ section12Tau1Primes M ∪ section12Tau3Primes M := by
  classical
  rcases hsourceP with
    ⟨_hMFsource, hW1cyc, _hW1ne, hW1Hall, hMcomp, _hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  rcases hW1Hall with ⟨hW1M, hW1HallSub⟩
  rcases hX with ⟨hXW1, hXcard⟩
  have hXM : X ≤ M := hXW1.trans hW1M
  have hpM : p.val ∣ Nat.card M := by
    have hpX : p.val ∣ Nat.card X := by rw [hXcard]
    exact hpX.trans (Subgroup.card_dvd_of_le hXM)
  have hpW1 : p.val ∣ Nat.card W1 := by
    have hpX : p.val ∣ Nat.card X := by rw [hXcard]
    exact hpX.trans (Subgroup.card_dvd_of_le hXW1)
  have hpW1π : p ∈ subgroupPrimeSet W1 := by
    simpa [subgroupPrimeSet] using hpW1
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : ((ambientDerivedSubgroup M).subgroupOf M).Normal := hDnormal
  have hCompLocal : (W1.subgroupOf M).IsComplement'
      ((ambientDerivedSubgroup M).subgroupOf M) :=
    sourceTypeP_complementIn_isComplement_subgroupOf
      (M := M) (H := ambientDerivedSubgroup M) (K := W1) hMcomp
  have hpNotSigma : p ∉ section10SigmaPrimes M := by
    intro hpSigma
    have hSigmaHallM :
        IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
      (theorem_10_2_b (G := G) hM).2
    have hpSigmaSub : p.val ∣ Nat.card (section10MsigmaSubgroup M) := by
      have hprod :
          (section10MsigmaSubgroup M).index * Nat.card (section10MsigmaSubgroup M) =
            Nat.card M :=
        Subgroup.index_mul_card (H := section10MsigmaSubgroup M)
      have hpProd :
          p.val ∣ (section10MsigmaSubgroup M).index *
              Nat.card (section10MsigmaSubgroup M) := by
        simpa [hprod] using hpM
      by_contra hpNotCard
      have hpNotIndex : ¬ p.val ∣ (section10MsigmaSubgroup M).index :=
        fun hpidx => (hSigmaHallM.p_in_pi_of_p_dvd_index p hpidx) hpSigma
      exact (Nat.Prime.not_dvd_mul p.property hpNotIndex hpNotCard) hpProd
    have hMsigmaLeM : section10Msigma M ≤ M := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hpSigmaSubgroupOf :
        p.val ∣ Nat.card ((section10Msigma M).subgroupOf M) := by
      simpa [section12Msigma_subgroupOf_eq (G := G) (M := M)] using hpSigmaSub
    have hpSigmaAmb : p.val ∣ Nat.card (section10Msigma M) := by
      have hcard :
          Nat.card ((section10Msigma M).subgroupOf M) = Nat.card (section10Msigma M) :=
        natCard_subgroupOf_eq (section10Msigma M) M hMsigmaLeM
      simpa [hcard] using hpSigmaSubgroupOf
    have hMsigmaLeDer : section10Msigma M ≤ ambientDerivedSubgroup M := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨y, (theorem_10_2_c (G := G) hM).2 hy, rfl⟩
    have hpDcard : p.val ∣ Nat.card (ambientDerivedSubgroup M) :=
      hpSigmaAmb.trans (Subgroup.card_dvd_of_le hMsigmaLeDer)
    have hDleM : ambientDerivedSubgroup M ≤ M :=
      section12_ambientDerivedSubgroup_le (G := G) (E := M)
    have hpDsub : p.val ∣ Nat.card ((ambientDerivedSubgroup M).subgroupOf M) := by
      have hcard :
          Nat.card ((ambientDerivedSubgroup M).subgroupOf M) =
            Nat.card (ambientDerivedSubgroup M) :=
        natCard_subgroupOf_eq (ambientDerivedSubgroup M) M hDleM
      simpa [hcard] using hpDcard
    have hpW1idx : p.val ∣ (W1.subgroupOf M).index := by
      simpa [hCompLocal.symm.index_eq_card] using hpDsub
    exact (hW1HallSub.p_in_pi_of_p_dvd_index p hpW1idx) hpW1π
  have hW1subCyclic : IsCyclic (W1.subgroupOf M) :=
    (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).isCyclic.2 hW1cyc
  have hRankLe : primeRank p.val M ≤ 1 :=
    sourceTypeP_primeRank_le_one_of_cyclic_hall_subgroup
      (R := M) (π := subgroupPrimeSet W1) (K := W1.subgroupOf M)
      hW1HallSub hpW1π hW1subCyclic
  have hRankPos : 0 < primeRank p.val M :=
    section12_primeRank_pos_of_mem_subgroupPrimeSet (R := M) hpM
  have hRank : primeRank p.val M = 1 := by omega
  by_cases hpDer : p ∈ subgroupPrimeSet (derivedSubgroup M)
  · exact Or.inr (by simpa [section12Tau3Primes] using ⟨hpNotSigma, hpDer, hRank⟩)
  · exact Or.inl (by simpa [section12Tau1Primes] using ⟨hpNotSigma, hpDer, hRank⟩)

private theorem sourceTypeP_msigma_centralizer_ne_bot_of_W1_prime
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 X : Subgroup G} {p : Nat.Primes}
    (hMFle : MF ≤ section10Msigma M)
    (hsourceP : typePDefinitionData M MF U W1 W2)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p W1) :
    subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ := by
  classical
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, hW2leInf, _hW2cyc, hW2ne, hCent, _hNorm⟩
  rcases hX with ⟨hXW1, _hXcard⟩
  haveI : Nontrivial W2 := (Subgroup.nontrivial_iff_ne_bot W2).2 hW2ne
  obtain ⟨yW2, hyW2ne⟩ := exists_ne (1 : W2)
  let y : G := yW2
  have hyW2 : y ∈ W2 := yW2.property
  have hyne : y ≠ 1 := by
    intro hy
    exact hyW2ne (Subtype.ext hy)
  have hyMsigma : y ∈ section10Msigma M :=
    hMFle ((hW2leInf hyW2).1)
  have hyCentX : y ∈ subgroupCentralizerIn (section10Msigma M) X := by
    refine ⟨hyMsigma, ?_⟩
    change y ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hzX
    by_cases hz : z = 1
    · subst hz
      simp
    · have hzW1 : z ∈ W1 := hXW1 hzX
      have hyCentZ : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) z := by
        simpa [hCent z hzW1 hz] using hyW2
      have hcomm : Commute y z :=
        Subgroup.mem_centralizer_singleton_iff.mp hyCentZ.2
      exact hcomm.eq.symm
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨y, hyCentX⟩, ?_⟩
  intro hybot
  exact hyne (by simpa using congrArg Subtype.val hybot)

public theorem sourceTypeP_mFamilyP_of_source_typeP
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hsourceP : typePDefinitionData M MF U W1 W2) :
    M ∈ section14MFamilyP G := by
  classical
  have hsourceP' : typePDefinitionData M MF U W1 W2 := hsourceP
  rcases hsourceP with
    ⟨hMFsource, _hW1cyc, hW1ne, hW1Hall, _hMcomp, _hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  rcases hW1Hall with ⟨hW1M, _hW1HallSub⟩
  have hMF15 : section15MFSubgroup M MF := by
    simpa [section16MFSubgroup, section16NilpotentNormalHallIn,
      section15MFSubgroup, section15NilpotentNormalHallIn] using hMFsource
  have hMFle : MF ≤ section10Msigma M := (theorem_15_2_chain (G := G) hM hMF15).2.1
  rcases sourceTypeP_exists_primeOrderSubgroup_of_ne_bot (G := G) hW1ne with
    ⟨X, hXprime⟩
  rcases hXprime with ⟨hXW1, p, hXcard⟩
  have hXprimeW1 : X ∈ section10PrimeOrderSubgroupsIn p W1 := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hXW1, hXcard⟩
  have hTau13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M :=
    sourceTypeP_tau13_of_W1_prime
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (X := X) (p := p) hM hsourceP' hXprimeW1
  have hCent :
      subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ :=
    sourceTypeP_msigma_centralizer_ne_bot_of_W1_prime
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (X := X) (p := p) hMFle hsourceP' hXprimeW1
  have hXM : X ≤ M := hXW1.trans hW1M
  have hpκ : p ∈ section14KappaPrimes M := by
    exact ⟨hTau13, X, ⟨hXM, hXcard⟩, hCent⟩
  exact ⟨hM, ⟨p, hpκ⟩⟩

public theorem sourceTypeP_W1_kappa_hall
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hsourceP : typePDefinitionData M MF U W1 W2) :
    section12HallSubgroupIn (section14KappaPrimes M) W1 M := by
  classical
  have hMP : M ∈ section14MFamilyP G :=
    sourceTypeP_mFamilyP_of_source_typeP hM hsourceP
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, _U0, hKU⟩
  have hKHall : section12HallSubgroupIn (section14KappaPrimes M) K M := hKU.1
  have hKcomp : section12ComplementIn M K (ambientDerivedSubgroup M) :=
    theorem_14_7_h (G := G) (M := M) (K := K) hMP hKHall
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, hMcomp, _hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hcard : Nat.card W1 = Nat.card K :=
    sourceTypeP_natCard_eq_of_complements_same_normal_left
      (G := G) (M := M) (D := ambientDerivedSubgroup M) (H := W1) (K := K)
      hDnormal hMcomp hKcomp
  exact sourceTypeP_hallSubgroupIn_of_natCard_eq hKHall hMcomp.2.1 hcard


public theorem sourceTypeP_exists_KUData_of_aligned_complement
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hsourceP : typePDefinitionData M MF U W1 W2) :
    ∃ Uc : Subgroup G, section16KUData M W1 Uc := by
  have hMP : section16MaximalTypeP M := by
    simpa [section16MaximalTypeP] using
      (sourceTypeP_mFamilyP_of_source_typeP (G := G) hM hsourceP)
  have hHall : section12HallSubgroupIn (section16KappaPrimes M) W1 M := by
    simpa [section16KappaPrimes] using
      (sourceTypeP_W1_kappa_hall (G := G) hM hsourceP)
  exact section16_exists_KUData_of_kappa_hall (G := G) hMP hHall

/-- If the source Type-P subgroup `U` is trivial, the BG T6 condition is
vacuous: no subgroup of `U` has prime order. -/
public theorem sourceTypeP_T6_of_U_eq_bot
    {G : Type u} [Group G] [Finite G]
    {M MF U : Subgroup G}
    (hUbot : U = ⊥) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
  intro A0 _A1 hA0 _hA1 _hConj _hNotM
  rcases hA0.2 with ⟨p, hcard⟩
  have hA0bot : A0 = ⊥ := by
    rw [hUbot] at hA0
    exact le_bot_iff.mp hA0.1
  rw [hA0bot] at hcard
  have hpone : p.val = 1 := by
    simpa using hcard.symm
  exact False.elim (p.property.ne_one hpone)

/-- Source Type-P data with the trivial complement, in the PF Type-V
alternative, excludes source Type I.

This is the source-level exclusivity boundary used by PF `(10.10)`. The checked
BG transfer gives `¬ section16TypeI`, but converting a source Type-I witness to
BG Type I currently needs the Section 8 choice package; keep that compatibility
claim explicit here rather than in PF10. -/
public theorem not_typeIDefinitionData_of_typeP_bot_typeV_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (hP : typePDefinitionData M MF ⊥ W1 W2)
    (_hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF)) :
    ¬ typeIDefinitionData M MF := by
  rintro ⟨U, U1, U0, hF, _hTypeIAlt⟩
  exact sourceTypeP_not_typeFData hP hF


/-- In a Type-V source context coming from a trivial-complement Type-P witness,
every Type-P witness selected by the same PF `(8.10)` notation also has
trivial complement. -/
public theorem notation_8_10_source_typeP_witness_U_eq_bot_of_typeP_bot
    {G : Type u} [Group G] [Finite G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2') :
    U = ⊥ := by
  rcases hWitness.1 with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hW1comp, _hUleD, _hUnil,
      _hW1norm, hCompMFU, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer,
      _hHatW⟩
  exact typePDefinitionData_bot_complement_eq_bot hPbot hCompMFU


public theorem notation_8_10_source_typeP_witness_typeV_context_of_typeP_bot
    {G : Type u} [Group G] [Finite G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2') :
    U = ⊥ ∧
      typePDefinitionData M MF ⊥ W1' W2' ∧
      typeVDefinitionData M MF ∧
      Ms = MF ∧
      MF = ambientDerivedSubgroup M ∧
      A = section8CentralizerUnion (ambientDerivedSubgroup M) Ms ∧
      A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
      A = A1 := by
  have hUbot :
      U = ⊥ :=
    notation_8_10_source_typeP_witness_U_eq_bot_of_typeP_bot hPbot hWitness
  rcases hWitness with ⟨hP, hTypes, hAcentral, _hA0, hLate⟩
  have hV : typeVDefinitionData M MF := by
    rcases hTypes with hII | hrest
    · exact False.elim (not_typeIIDefinitionData_of_typeP_bot hPbot hII)
    · rcases hrest with hIII | hrest
      · exact False.elim (not_typeIIIDefinitionData_of_typeP_bot hPbot hIII)
      · rcases hrest with hIV | hV
        · exact False.elim (not_typeIVDefinitionData_of_typeP_bot hPbot hIV)
        · exact hV
  have hPbot' : typePDefinitionData M MF ⊥ W1' W2' := by
    simpa [hUbot] using hP
  have hMs : Ms = MF :=
    msChoiceSource_eq_mf_of_typeV hNotation.2.2.1 hV
  have hMF : MF = ambientDerivedSubgroup M :=
    typePDefinitionData_mf_eq_ambientDerived_of_eq_bot hPbot rfl
  have hLate' :
      A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
        A = A1 :=
    hLate (Or.inr (Or.inr hV))
  exact
    ⟨hUbot, hPbot', hV, hMs, hMF, hAcentral, hLate'.1, hLate'.2⟩


public theorem exists_notation_8_14_source_data_of_typeP_bot_typeV_witness
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2') :
    ∃ R : G → Subgroup G, ∃ tildeA tildeA0 tildeA1 : Set G,
      notation_8_14_source_data M A A0 A1
        (section8DSet M A0) tildeA tildeA0 tildeA1 R := by
  rcases notation_8_10_source_typeP_witness_typeV_context_of_typeP_bot
      hPbot hNotation hWitness with
    ⟨_hUbot, _hPbot', _hV, _hMs, _hMF, _hAcentral, _hA1, hAeqA1⟩
  have hA1A : A1 ⊆ A := by
    intro x hx
    rw [hAeqA1]
    exact hx
  have hAA0 : A ⊆ A0 := by
    intro x hx
    rw [hWitness.2.2.2.1]
    exact Or.inl hx
  exact exists_mixed_notation_8_14_source_data_of_theorem_8_13
    M MF Ms A A0 A1 (by infer_instance) hNotation hA1A hAA0


public theorem theorem_8_15_hypothesis_4_6_source_of_typeP_bot_typeV_witness
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2') :
    section8Hypothesis46Source M W1' W2' MF A A0 ∧
      section8Hypothesis46Source M W1' W2' Ms A A0 := by
  rcases exists_notation_8_14_source_data_of_typeP_bot_typeV_witness
      hPbot hNotation hWitness with
    ⟨R, tildeA, tildeA0, tildeA1, h14⟩
  have hSource :
      theorem_8_15_source_data M MF Ms A A0 A1 A0
        (section8DSet M A0) tildeA tildeA0 tildeA1 R :=
    ⟨hNotation, h14, Or.inl rfl⟩
  exact theorem_8_15_hypothesis_4_6_source
    (G := G) (M := M) (MF := MF) (Ms := Ms) (A := A) (A0 := A0)
    (A1 := A1) (D := section8DSet M A0) (tildeA := tildeA)
    (tildeA0 := tildeA0) (tildeA1 := tildeA1) (Achoice := A0)
    (R := R) (by infer_instance) hSource U W1' W2' hWitness

/-- In a Type-P source context, every nonidentity element of `M_F` belongs to
the PF `(8.10)` centralizer union inside `M'`: use the element itself as the
centralizer witness. -/
public theorem a1Set_subset_section8CentralizerUnion_ambientDerived_of_typeP
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    a1Set MF ⊆ section8CentralizerUnion (ambientDerivedSubgroup M) MF := by
  intro x hx
  rcases hx with ⟨hxMF, hxne⟩
  refine ⟨x, ⟨hxMF, hxne⟩, ?_⟩
  refine ⟨?_, hxne⟩
  change x ∈ elementCentralizerIn (ambientDerivedSubgroup M) x
  rw [elementCentralizerIn]
  have hMFleD : MF ≤ ambientDerivedSubgroup M := by
    exact hP.2.2.2.2.2.2.2.2.1.1
  refine ⟨?_, ?_⟩
  · exact hMFleD hxMF
  · simp [Subgroup.mem_centralizer_iff]


public theorem exists_notation_8_14_source_data_of_typeII_notation_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2)
    (hNotation :
      notation_8_10_source_data M MF MF
        (section8CentralizerUnion (ambientDerivedSubgroup M) MF)
        (section8CentralizerUnion (ambientDerivedSubgroup M) MF ∪
          section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G))
        (a1Set MF)) :
    ∃ R : G → Subgroup G, ∃ tildeA tildeA0 tildeA1 : Set G,
      notation_8_14_source_data M
        (section8CentralizerUnion (ambientDerivedSubgroup M) MF)
        (section8CentralizerUnion (ambientDerivedSubgroup M) MF ∪
          section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G))
        (a1Set MF)
        (section8DSet M
          (section8CentralizerUnion (ambientDerivedSubgroup M) MF ∪
            section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G)))
        tildeA tildeA0 tildeA1 R := by
  exact exists_mixed_notation_8_14_source_data_of_theorem_8_13
    M MF MF
    (section8CentralizerUnion (ambientDerivedSubgroup M) MF)
    (section8CentralizerUnion (ambientDerivedSubgroup M) MF ∪
      section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G))
    (a1Set MF) (by infer_instance) hNotation
    (a1Set_subset_section8CentralizerUnion_ambientDerived_of_typeP hP)
    (by
      intro x hx
      exact Or.inl hx)


public theorem exists_hypothesis2_dade_transform_of_typeP_bot_typeV_witness
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2') :
    ∃ R : G → Subgroup G, ∃ tildeA tildeA0 tildeA1 : Set G,
      ∃ _h14 :
        notation_8_14_source_data M A A0 A1
          (section8DSet M A0) tildeA tildeA0 tildeA1 R,
      ∃ _h22A : Section2.hypothesis_2_2_statement A M R,
      ∃ h22A0 : Section2.hypothesis_2_2_statement A0 M R,
      ∃ τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
        τ = Section2.dadeTransformLinear R h22A0.subset_L ∧
          ∀ α : Section1.ClassFunction M,
            τ α = Section2.dadeTransform R h22A0.subset_L α := by
  rcases exists_notation_8_14_source_data_of_typeP_bot_typeV_witness
      hPbot hNotation hWitness with
    ⟨R, tildeA, tildeA0, tildeA1, h14⟩
  have hSourceA :
      theorem_8_15_source_data M MF Ms A A0 A1 A
        (section8DSet M A0) tildeA tildeA0 tildeA1 R :=
    ⟨hNotation, h14, Or.inr (Or.inl rfl)⟩
  have hSourceA0 :
      theorem_8_15_source_data M MF Ms A A0 A1 A0
        (section8DSet M A0) tildeA tildeA0 tildeA1 R :=
    ⟨hNotation, h14, Or.inl rfl⟩
  have h22A : Section2.hypothesis_2_2_statement A M R :=
    theorem_8_15_hypothesis2 (G := G) (M := M) (MF := MF) (Ms := Ms)
      (A := A) (A0 := A0) (A1 := A1) (D := section8DSet M A0)
      (tildeA := tildeA) (tildeA0 := tildeA0) (tildeA1 := tildeA1)
      (Achoice := A) (R := R) (by infer_instance) hSourceA
  have h22A0 : Section2.hypothesis_2_2_statement A0 M R :=
    theorem_8_15_hypothesis2 (G := G) (M := M) (MF := MF) (Ms := Ms)
      (A := A) (A0 := A0) (A1 := A1) (D := section8DSet M A0)
      (tildeA := tildeA) (tildeA0 := tildeA0) (tildeA1 := tildeA1)
      (Achoice := A0) (R := R) (by infer_instance) hSourceA0
  refine
    ⟨R, tildeA, tildeA0, tildeA1, h14, h22A, h22A0,
      Section2.dadeTransformLinear R h22A0.subset_L, rfl, ?_⟩
  intro α
  exact Section2.dadeTransformLinear_apply R h22A0.subset_L α


public theorem subgroupImageSet_section8SubgroupSetPreimage_eq
    {G : Type u} [Group G]
    {M : Subgroup G} {A : Set G}
    (hA : A ⊆ (M : Set G)) :
    Section4Scratch.subgroupImageSet M
        (section8SubgroupSetPreimage M A) = A := by
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa [section8SubgroupSetPreimage] using hm
  · intro hg
    exact ⟨⟨g, hA hg⟩,
      by simpa [section8SubgroupSetPreimage] using hg, rfl⟩

/-- The Type-P cyclic `A₀` carrier maps back to the ambient `A₀` set. -/
public theorem subgroupImageSet_section8CyclicA0Set_eq
    {G : Type u} [Group G] [Finite G]
    {M MF Ms U W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (hP : typePDefinitionData M MF U W1 W2)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1 W2)
    (h46 : section8Hypothesis46Source M W1 W2 Ms A A0) :
    Section4Scratch.subgroupImageSet M (section8CyclicA0Set M W1 W2 A) = A0 := by
  have hA0subM : A0 ⊆ (M : Set G) := by
    rcases hP with
      ⟨hMFsource, _hW1cyc, _hW1ne, hW1hall, _hMcomp, _hUleD,
        _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecondLe,
        _hFittingEq, _hFittingLeD, hW2leInf, _hW2cyc, _hW2ne,
        _hcentralizer, _hhatW⟩
    rcases hWitness with ⟨_hPw, _hTypes, hAeq, hA0eq, _hLate⟩
    have hA_subset_M : A ⊆ (M : Set G) := by
      intro y hy
      have hyA :
          y ∈ section8CentralizerUnion (ambientDerivedSubgroup M) Ms := by
        simpa [hAeq] using hy
      rcases hyA with ⟨_c, _hc, hyD, _hyne⟩
      exact section12_ambientDerivedSubgroup_le (G := G) (E := M) hyD.1
    have hW1M : W1 ≤ M := hW1hall.1
    have hW2M : W2 ≤ M := by
      intro y hy
      exact hMFsource.1.1 ((hW2leInf hy).1)
    have hHatW_M : section16HatW W1 W2 ≤ M := by
      intro y hy
      exact (sup_le hW1M hW2M) hy.1
    intro y hy
    rw [hA0eq] at hy
    rcases hy with hyA | hyConj
    · exact hA_subset_M hyA
    · rcases hyConj with ⟨w, hw, m, hmM, hy_eq⟩
      rw [hy_eq]
      exact M.mul_mem (M.mul_mem hmM (hHatW_M hw)) (M.inv_mem hmM)
  rw [← h46.1]
  exact subgroupImageSet_section8SubgroupSetPreimage_eq hA0subM


public theorem exists_hypothesis2_section4_A_dade_transform_of_typeP_bot_typeV_witness
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2') :
    ∃ R : G → Subgroup G, ∃ tildeA tildeA0 tildeA1 : Set G,
      ∃ _h14 :
        notation_8_14_source_data M A A0 A1
          (section8DSet M A0) tildeA tildeA0 tildeA1 R,
      ∃ _h22A :
        Section2.hypothesis_2_2_statement
          (Section4Scratch.subgroupImageSet M
            (section8SubgroupSetPreimage M A)) M R,
      ∃ h22A0 : Section2.hypothesis_2_2_statement A0 M R,
      ∃ τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
        τ = Section2.dadeTransformLinear R h22A0.subset_L ∧
          ∀ α : Section1.ClassFunction M,
            τ α = Section2.dadeTransform R h22A0.subset_L α := by
  rcases exists_hypothesis2_dade_transform_of_typeP_bot_typeV_witness
      hPbot hNotation hWitness with
    ⟨R, tildeA, tildeA0, tildeA1, h14, h22A, h22A0, τ, hτdef, hτ⟩
  rcases notation_8_10_source_typeP_witness_typeV_context_of_typeP_bot
      hPbot hNotation hWitness with
    ⟨_hUbot, _hPbot', _hV, _hMs, _hMF, _hAcentral, hA1, hAeqA1⟩
  have hA_subset_M : A ⊆ (M : Set G) := by
    intro x hx
    rw [hAeqA1, hA1] at hx
    exact section12_ambientDerivedSubgroup_le hx.1
  have hAimage :
      Section4Scratch.subgroupImageSet M
          (section8SubgroupSetPreimage M A) = A :=
    subgroupImageSet_section8SubgroupSetPreimage_eq hA_subset_M
  have h22Aimage :
      Section2.hypothesis_2_2_statement
        (Section4Scratch.subgroupImageSet M
          (section8SubgroupSetPreimage M A)) M R := by
    simpa [hAimage] using h22A
  exact
    ⟨R, tildeA, tildeA0, tildeA1, h14, h22Aimage, h22A0, τ, hτdef, hτ⟩


public theorem notation_8_10_source_typeP_witness_A0_subset_M_of_typeP_bot
    {G : Type u} [Group G] [Finite G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2') :
    A0 ⊆ (M : Set G) := by
  rcases notation_8_10_source_typeP_witness_typeV_context_of_typeP_bot
      hPbot hNotation hWitness with
    ⟨_hUbot, hPbot', _hV, _hMs, _hMF, _hAcentral, hA1, hAeqA1⟩
  rcases hPbot' with
    ⟨hMF, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  have hW1M : W1' ≤ M := hW1hall.1
  have hW2M : W2' ≤ M := by
    intro x hx
    exact hMF.1.1 ((hW2le hx).1)
  have hWM : W1' ⊔ W2' ≤ M := sup_le hW1M hW2M
  intro x hx
  rw [hWitness.2.2.2.1] at hx
  rcases hx with hxA | hxConj
  · have hxD :
        x ∈ section16NonidentityElements (ambientDerivedSubgroup M : Set G) := by
      simpa [hAeqA1, hA1] using hxA
    exact section12_ambientDerivedSubgroup_le hxD.1
  · rcases hxConj with ⟨w, hw, m, hmM, hx_eq⟩
    have hwM : w ∈ M := hWM hw.1
    rw [hx_eq]
    exact M.mul_mem (M.mul_mem hmM hwM) (M.inv_mem hmM)


public theorem subgroupImageSet_section8CyclicA0Set_eq_of_typeP_bot_typeV_witness
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2') :
    Section4Scratch.subgroupImageSet M
        (section8CyclicA0Set M W1' W2' A) = A0 := by
  have hA0sub : A0 ⊆ (M : Set G) :=
    notation_8_10_source_typeP_witness_A0_subset_M_of_typeP_bot
      hPbot hNotation hWitness
  rcases theorem_8_15_hypothesis_4_6_source_of_typeP_bot_typeV_witness
      hPbot hNotation hWitness with
    ⟨_h46MF, h46MsSource⟩
  rcases h46MsSource with ⟨hA0pre, _h46Ms, _hAsub⟩
  calc
    Section4Scratch.subgroupImageSet M
        (section8CyclicA0Set M W1' W2' A) =
        Section4Scratch.subgroupImageSet M
          (section8SubgroupSetPreimage M A0) := by
          rw [← hA0pre]
    _ = A0 :=
        subgroupImageSet_section8SubgroupSetPreimage_eq hA0sub


public theorem exists_hypothesis2_section8_cyclicA0_dade_transform_of_typeP_bot_typeV_witness
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2') :
    ∃ R : G → Subgroup G, ∃ tildeA tildeA0 tildeA1 : Set G,
      ∃ _h14 :
        notation_8_14_source_data M A A0 A1
          (section8DSet M A0) tildeA tildeA0 tildeA1 R,
      ∃ _h22A :
        Section2.hypothesis_2_2_statement
          (Section4Scratch.subgroupImageSet M
            (section8SubgroupSetPreimage M A)) M R,
      ∃ h22A0 :
        Section2.hypothesis_2_2_statement
          (Section4Scratch.subgroupImageSet M
            (section8CyclicA0Set M W1' W2' A)) M R,
      ∃ τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
        τ = Section2.dadeTransformLinear R h22A0.subset_L ∧
          ∀ α : Section1.ClassFunction M,
            τ α = Section2.dadeTransform R h22A0.subset_L α := by
  rcases exists_hypothesis2_section4_A_dade_transform_of_typeP_bot_typeV_witness
      hPbot hNotation hWitness with
    ⟨R, tildeA, tildeA0, tildeA1, h14, h22A, h22A0, _τ, _hτdef, _hτ⟩
  have hA0image :
      Section4Scratch.subgroupImageSet M
          (section8CyclicA0Set M W1' W2' A) = A0 :=
    subgroupImageSet_section8CyclicA0Set_eq_of_typeP_bot_typeV_witness
      hPbot hNotation hWitness
  have h22A0image :
      Section2.hypothesis_2_2_statement
        (Section4Scratch.subgroupImageSet M
          (section8CyclicA0Set M W1' W2' A)) M R := by
    simpa [hA0image] using h22A0
  refine
    ⟨R, tildeA, tildeA0, tildeA1, h14, h22A, h22A0image,
      Section2.dadeTransformLinear R h22A0image.subset_L, rfl, ?_⟩
  intro α
  exact Section2.dadeTransformLinear_apply R h22A0image.subset_L α


public theorem section8CyclicA0Set_subset_section4_a0Set
    {G : Type u} [Group G] [Finite G]
    {M W1 W2 : Subgroup G} {A : Set G} {W : Subgroup M}
    (hW : W = (W1 ⊔ W2).subgroupOf M) :
    section8CyclicA0Set M W1 W2 A ⊆
      Section4Scratch.a0Set (W2.subgroupOf M) W
        (section8SubgroupSetPreimage M A) := by
  classical
  subst W
  intro x hx
  change x ∈
    section8SubgroupSetPreimage M A ∪
      Section2.conjugateSet
        (Section3.cyclicTISet
          (W1.subgroupOf M) (W2.subgroupOf M) ((W1 ⊔ W2).subgroupOf M)) at hx
  change x ∈
    section8SubgroupSetPreimage M A ∪
      Section2.conjugateSet
        ((((W1 ⊔ W2).subgroupOf M : Subgroup M) : Set M) \
          (W2.subgroupOf M : Set M))
  rcases hx with hxA | hxConj
  · exact Or.inl hxA
  · rcases hxConj with ⟨w, hw, hconj⟩
    refine Or.inr ?_
    refine ⟨w, ?_, hconj⟩
    rcases (Section3.cyclicTISet_mem_iff
      (W1.subgroupOf M) (W2.subgroupOf M) ((W1 ⊔ W2).subgroupOf M)).1 hw with
      ⟨hwW, _hwW1, hwW2⟩
    exact ⟨hwW, hwW2⟩


public theorem exists_typeP_local_section4_character_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    ∃ I : Type u, ∃ J : Type u,
      ∃ instFintypeI : Fintype I, ∃ instFintypeJ : Fintype J,
        ∃ instDecidableEqI : DecidableEq I, ∃ instDecidableEqJ : DecidableEq J,
          letI : Fintype I := instFintypeI
          letI : Fintype J := instFintypeJ
          letI : DecidableEq I := instDecidableEqI
          letI : DecidableEq J := instDecidableEqJ
          ∃ i0 : I, ∃ j0 : J,
            ∃ omega :
              I → J → Section1.ClassFunction ((W1 ⊔ W2).subgroupOf M),
              ∃ hω :
                Section3.notation_3_3_statement
                  (W1.subgroupOf M)
                  (W2.subgroupOf M)
                  ((W1 ⊔ W2).subgroupOf M)
                  I J i0 j0 omega,
                ∃ sigmaM :
                  Section1.ClassFunction ((W1 ⊔ W2).subgroupOf M) →ₗ[ℂ]
                    Section1.ClassFunction M,
                  ∃ piChar : I → J → Section1.ClassFunction M,
                    ∃ deltaSign : J → ℂ,
                      ∃ xChar : J → Section1.ClassFunction (derivedSubgroup M),
                        Section4.theorem_4_3_b_statement
                          (W1.subgroupOf M)
                          (W2.subgroupOf M)
                          ((W1 ⊔ W2).subgroupOf M)
                          I J i0 j0 omega sigmaM piChar deltaSign hω ∧
                          Section4.theorem_4_3_c_statement
                            (W2.subgroupOf M)
                            ((W1 ⊔ W2).subgroupOf M)
                            I J piChar deltaSign omega ∧
                          Section4.theorem_4_3_d_statement
                            (W1.subgroupOf M) I J piChar deltaSign ∧
                          Section4Scratch.theorem_4_5_a_statement
                            (derivedSubgroup M) piChar xChar ∧
                          Section4Scratch.theorem_4_5_b_statement
                            (derivedSubgroup M) piChar xChar := by
  classical
  have h42 :
      Section4.hypothesis_4_2_statement
        (derivedSubgroup M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M) :=
    theorem_8_15_hypothesis_4_2_of_typeP
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (by infer_instance) hP
  have h43a :
      Section4.theorem_4_3_a_statement
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M) :=
    Section4.theorem_4_3_a
      (derivedSubgroup M)
      (W1.subgroupOf M)
      (W2.subgroupOf M)
      ((W1 ⊔ W2).subgroupOf M)
      h42
  have h31 :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M) :=
    h43a.2
  rcases Section3.exists_notation_3_3_of_hypothesis_3_1 h31 with
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, omega, hω⟩
  letI : Fintype I := instFintypeI
  letI : Fintype J := instFintypeJ
  letI : DecidableEq I := instDecidableEqI
  letI : DecidableEq J := instDecidableEqJ
  have h43 :
      Section4.theorem_4_3_statement
        (derivedSubgroup M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M)
        I J i0 j0 omega h42 hω :=
    Section4.theorem_4_3
      (derivedSubgroup M)
      (W1.subgroupOf M)
      (W2.subgroupOf M)
      ((W1 ⊔ W2).subgroupOf M)
      I J i0 j0 omega h42 hω
  rcases h43 with ⟨_h43a, sigmaM, piChar, deltaSign, h43b, h43c, h43d⟩
  have h45 :
      Section4Scratch.theorem_4_5_statement (derivedSubgroup M) piChar :=
    Section4Scratch.theorem_4_5
      (derivedSubgroup M)
      (W1.subgroupOf M)
      (W2.subgroupOf M)
      ((W1 ⊔ W2).subgroupOf M)
      i0 j0 omega sigmaM piChar deltaSign h42 hω h43b h43c
  rcases h45 with ⟨xChar, h45a, h45b⟩
  exact
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, omega, hω, sigmaM, piChar, deltaSign, xChar,
      h43b, h43c, h43d, h45a, h45b⟩


/-- The ambient image of the local subgroup `S ≤ M` is the original ambient
subgroup, provided `S` was obtained by restricting a subgroup already contained
in `M`. -/
public theorem subgroupImage_subgroupOf_eq
    {G : Type u} [Group G] {M S : Subgroup G}
    (hSM : S ≤ M) :
    Section4Scratch.subgroupImage M (S.subgroupOf M) = S := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    rw [← hyx]
    simpa [Subgroup.mem_subgroupOf] using hy
  · intro hx
    exact ⟨⟨x, hSM hx⟩, by simpa [Subgroup.mem_subgroupOf] using hx, rfl⟩

/-- Pulling the ambient image of a relative subgroup back to the intermediate
subgroup recovers the original relative subgroup. -/
public theorem subgroupImage_subgroupOf_self_eq
    {G : Type u} [Group G] (M : Subgroup G) (W : Subgroup M) :
    (Section4Scratch.subgroupImage M W).subgroupOf M = W := by
  ext x
  constructor
  · intro hx
    change ((x : M) : G) ∈ Section4Scratch.subgroupImage M W at hx
    rcases Subgroup.mem_map.mp hx with ⟨w, hw, hwx⟩
    have hxM : x = w := by
      apply M.subtype_injective
      exact hwx.symm
    simpa [hxM] using hw
  · intro hx
    change ((x : M) : G) ∈ Section4Scratch.subgroupImage M W
    exact ⟨x, hx, rfl⟩


@[expose] public noncomputable def subgroupImageEquiv
    {G : Type u} [Group G] (M : Subgroup G) (W : Subgroup M) :
    W ≃* Section4Scratch.subgroupImage M W := by
  unfold Section4Scratch.subgroupImage
  exact Subgroup.equivMapOfInjective (f := M.subtype) W M.subtype_injective

public theorem subgroupImageEquiv_apply_coe
    {G : Type u} [Group G] (M : Subgroup G) (W : Subgroup M) (w : W) :
    ((subgroupImageEquiv M W w : Section4Scratch.subgroupImage M W) : G) =
      ((w : M) : G) := by
  unfold subgroupImageEquiv Section4Scratch.subgroupImage
  exact Subgroup.coe_equivMapOfInjective_apply W M.subtype M.subtype_injective w

public theorem subgroupImageEquiv_symm_apply_coe
    {G : Type u} [Group G] (M : Subgroup G) (W : Subgroup M)
    (x : Section4Scratch.subgroupImage M W) :
    ((((subgroupImageEquiv M W).symm x : W) : M) : G) = (x : G) := by
  simpa using
    (subgroupImageEquiv_apply_coe M W
      ((subgroupImageEquiv M W).symm x)).symm

public theorem mem_subgroupImage_subgroupOf_iff
    {G : Type u} [Group G] (M : Subgroup G) (W : Subgroup M) (x : M) :
    x ∈ (Section4Scratch.subgroupImage M W).subgroupOf M ↔ x ∈ W := by
  rw [subgroupImage_subgroupOf_self_eq M W]

public theorem card_subgroupImage_subgroupOf
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) (W : Subgroup M) :
    Nat.card ((Section4Scratch.subgroupImage M W).subgroupOf M) =
      Nat.card W := by
  rw [subgroupImage_subgroupOf_self_eq M W]

public theorem subgroupImageEquiv_apply_mem_subgroupOf
    {G : Type u} [Group G] {M : Subgroup G} {S W : Subgroup M}
    {x : W} (hx : x ∈ S.subgroupOf W) :
    subgroupImageEquiv M W x ∈
      (Section4Scratch.subgroupImage M S).subgroupOf
        (Section4Scratch.subgroupImage M W) := by
  change ((subgroupImageEquiv M W x :
      Section4Scratch.subgroupImage M W) : G) ∈
        Section4Scratch.subgroupImage M S
  refine ⟨(x : M), ?_, ?_⟩
  · exact (Subgroup.mem_subgroupOf (H := S) (K := W) (h := x)).mp hx
  simp [subgroupImageEquiv_apply_coe]

public theorem subgroupImageEquiv_symm_mem_subgroupOf
    {G : Type u} [Group G] {M : Subgroup G} {S W : Subgroup M}
    (x :
      (Section4Scratch.subgroupImage M S).subgroupOf
        (Section4Scratch.subgroupImage M W)) :
    (subgroupImageEquiv M W).symm x.1 ∈ S.subgroupOf W := by
  change (((subgroupImageEquiv M W).symm x.1 : W) : M) ∈ S
  rcases x.2 with ⟨s, hs, hsx⟩
  have hxG : ((x.1 : Section4Scratch.subgroupImage M W) : G) =
      ((s : M) : G) := by
    change ((s : M) : G) =
      ((x.1 : Section4Scratch.subgroupImage M W) : G) at hsx
    exact hsx.symm
  have hxM : (((subgroupImageEquiv M W).symm x.1 : W) : M) = s := by
    apply M.subtype_injective
    calc
      ((((subgroupImageEquiv M W).symm x.1 : W) : M) : G) =
          ((x.1 : Section4Scratch.subgroupImage M W) : G) := by
            simpa using
              (subgroupImageEquiv_apply_coe M W
                ((subgroupImageEquiv M W).symm x.1)).symm
      _ = ((s : M) : G) := hxG
  simpa [hxM] using hs

public theorem subgroupImageEquiv_mem_cyclicTISet
    {G : Type u} [Group G] {M : Subgroup G} {W1 W2 W : Subgroup M}
    {x : W}
    (hx : (x : M) ∈ Section3.cyclicTISet W1 W2 W) :
    ((subgroupImageEquiv M W x :
        Section4Scratch.subgroupImage M W) : G) ∈
      Section3.cyclicTISet
        (Section4Scratch.subgroupImage M W1)
        (Section4Scratch.subgroupImage M W2)
        (Section4Scratch.subgroupImage M W) := by
  rw [Section3.cyclicTISet_mem_iff] at hx ⊢
  refine ⟨?_, ?_, ?_⟩
  · exact (subgroupImageEquiv M W x).2
  · intro hleft
    exact hx.2.1 (by
      change ((x : W) : M) ∈ W1
      have hlocal :
          ((subgroupImageEquiv M W).symm
              (⟨subgroupImageEquiv M W x, hleft⟩ :
                (Section4Scratch.subgroupImage M W1).subgroupOf
                  (Section4Scratch.subgroupImage M W)) : W) ∈
            W1.subgroupOf W :=
        subgroupImageEquiv_symm_mem_subgroupOf
          (M := M) (S := W1) (W := W)
          ⟨subgroupImageEquiv M W x, hleft⟩
      rw [← (subgroupImageEquiv M W).symm_apply_apply x]
      exact (Subgroup.mem_subgroupOf (H := W1) (K := W)).mp hlocal)
  · intro hright
    exact hx.2.2 (by
      change ((x : W) : M) ∈ W2
      have hlocal :
          ((subgroupImageEquiv M W).symm
              (⟨subgroupImageEquiv M W x, hright⟩ :
                (Section4Scratch.subgroupImage M W2).subgroupOf
                  (Section4Scratch.subgroupImage M W)) : W) ∈
            W2.subgroupOf W :=
        subgroupImageEquiv_symm_mem_subgroupOf
          (M := M) (S := W2) (W := W)
          ⟨subgroupImageEquiv M W x, hright⟩
      rw [← (subgroupImageEquiv M W).symm_apply_apply x]
      exact (Subgroup.mem_subgroupOf (H := W2) (K := W)).mp hlocal)

/-- Membership in the ambient-image cyclic-TI carrier pulls back along
`subgroupImageEquiv` to membership in the relative cyclic-TI carrier. -/
public theorem subgroupImageEquiv_symm_mem_cyclicTISet
    {G : Type u} [Group G] {M : Subgroup G} {W1 W2 W : Subgroup M}
    {x : Section4Scratch.subgroupImage M W}
    (hx : (x : G) ∈
      Section3.cyclicTISet
        (Section4Scratch.subgroupImage M W1)
        (Section4Scratch.subgroupImage M W2)
        (Section4Scratch.subgroupImage M W)) :
    (((subgroupImageEquiv M W).symm x : W) : M) ∈
      Section3.cyclicTISet W1 W2 W := by
  rw [Section3.cyclicTISet_mem_iff] at hx ⊢
  refine ⟨((subgroupImageEquiv M W).symm x).2, ?_, ?_⟩
  · intro hleft
    exact hx.2.1 (by
      change (x : G) ∈ Section4Scratch.subgroupImage M W1
      have himage := subgroupImageEquiv_apply_mem_subgroupOf
        (M := M) (S := W1) (W := W)
        (x := (subgroupImageEquiv M W).symm x) hleft
      rw [← (subgroupImageEquiv M W).apply_symm_apply x]
      exact (Subgroup.mem_subgroupOf
        (H := Section4Scratch.subgroupImage M W1)
        (K := Section4Scratch.subgroupImage M W)).mp himage)
  · intro hright
    exact hx.2.2 (by
      change (x : G) ∈ Section4Scratch.subgroupImage M W2
      have himage := subgroupImageEquiv_apply_mem_subgroupOf
        (M := M) (S := W2) (W := W)
        (x := (subgroupImageEquiv M W).symm x) hright
      rw [← (subgroupImageEquiv M W).apply_symm_apply x]
      exact (Subgroup.mem_subgroupOf
        (H := Section4Scratch.subgroupImage M W2)
        (K := Section4Scratch.subgroupImage M W)).mp himage)

public theorem inducedCF_subgroupImage_eq_inducedCF_trans
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (W : Subgroup M)
    (α : Section1.ClassFunction W) :
    Section1.inducedCF M (Section1.inducedCF W α) =
      Section1.inducedCF (Section4Scratch.subgroupImage M W)
        (Section1.classFunctionLinearEquivOfMulEquiv
          (subgroupImageEquiv M W) α) := by
  -- `Dade_id` rewrite. This is the corresponding Lean transport of
  -- transitivity of induction through `subgroupImageEquiv`.
  classical
  let H := Section4Scratch.subgroupImage M W
  have hHM : H ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨w, _hw, hwx⟩
    rw [← hwx]
    exact w.2
  have hinner :
      Section1.inducedCF W α =
        Section1.inducedCF (H.subgroupOf M)
          (Section1.subgroupOfClassFunction
            (Section1.classFunctionLinearEquivOfMulEquiv
              (subgroupImageEquiv M W) α)) := by
    ext m
    unfold Section1.inducedCF Section1.inducedClassFunction
    rw [card_subgroupImage_subgroupOf M W]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxW : x * m * x⁻¹ ∈ W
    · have hxH : x * m * x⁻¹ ∈ H.subgroupOf M := by
        simpa [H, mem_subgroupImage_subgroupOf_iff M W] using hxW
      have hxHG : (((x * m * x⁻¹ : M) : G)) ∈ H :=
        (Subgroup.mem_subgroupOf (H := H) (K := M)).mp hxH
      have harg :
          (⟨x * m * x⁻¹, hxW⟩ : W) =
            (subgroupImageEquiv M W).symm
              (⟨((x * m * x⁻¹ : M) : G), hxHG⟩ : H) := by
        apply Subtype.ext
        apply M.subtype_injective
        exact (subgroupImageEquiv_symm_apply_coe M W
          (⟨((x * m * x⁻¹ : M) : G), hxHG⟩ : H)).symm
      simp [hxW, hxH, Section1.subgroupOfClassFunction,
        Section1.classFunctionLinearEquivOfMulEquiv, H, harg]
    · have hxH : ¬ x * m * x⁻¹ ∈ H.subgroupOf M := by
        intro hxH
        exact hxW ((mem_subgroupImage_subgroupOf_iff M W _).1 (by simpa [H] using hxH))
      simp [hxW, hxH]
  rw [hinner]
  exact
    Section1.inducedCF_trans H M hHM
      (Section1.classFunctionLinearEquivOfMulEquiv
        (subgroupImageEquiv M W) α)

public theorem notation_3_3_statement_of_subgroupImageEquiv
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {W1 W2 W : Subgroup M}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J → Section1.ClassFunction W}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 omega) :
    Section3.notation_3_3_statement
      (Section4Scratch.subgroupImage M W1)
      (Section4Scratch.subgroupImage M W2)
      (Section4Scratch.subgroupImage M W)
      I J i0 j0
      (fun i j =>
        Section1.classFunctionLinearEquivOfMulEquiv
          (subgroupImageEquiv M W) (omega i j)) := by
  classical
  let e := subgroupImageEquiv M W
  let E := Section1.classFunctionLinearEquivOfMulEquiv e
  have hleftKernel :
      ∀ i,
        Section1.subgroupInKernel' (E (omega i j0))
          ((Section4Scratch.subgroupImage M W2).subgroupOf
            (Section4Scratch.subgroupImage M W)) := by
    intro i x
    have hx : (e.symm x.1 : W) ∈ W2.subgroupOf W :=
      subgroupImageEquiv_symm_mem_subgroupOf (M := M) (S := W2) (W := W) x
    calc
      E (omega i j0) x.1 = omega i j0 (e.symm x.1) := rfl
      _ = Section1.degree (omega i j0) := hω.left_kernel i ⟨e.symm x.1, hx⟩
      _ = Section1.degree (E (omega i j0)) :=
          (Section1.degree_classFunctionLinearEquivOfMulEquiv e
            (omega i j0)).symm
  have hrightKernel :
      ∀ j,
        Section1.subgroupInKernel' (E (omega i0 j))
          ((Section4Scratch.subgroupImage M W1).subgroupOf
            (Section4Scratch.subgroupImage M W)) := by
    intro j x
    have hx : (e.symm x.1 : W) ∈ W1.subgroupOf W :=
      subgroupImageEquiv_symm_mem_subgroupOf (M := M) (S := W1) (W := W) x
    calc
      E (omega i0 j) x.1 = omega i0 j (e.symm x.1) := rfl
      _ = Section1.degree (omega i0 j) := hω.right_kernel j ⟨e.symm x.1, hx⟩
      _ = Section1.degree (E (omega i0 j)) :=
          (Section1.degree_classFunctionLinearEquivOfMulEquiv e
            (omega i0 j)).symm
  refine
    { card_left := ?_
      card_right := ?_
      principal := ?_
      left_kernel := hleftKernel
      right_kernel := hrightKernel
      left_kernel_exact := ?_
      right_kernel_exact := ?_
      product := ?_
      degree_one := ?_
      is_class := ?_
      irreducible := ?_
      orthonormal := ?_
      pairwise_eq := ?_
      all_irreducibles := ?_ }
  · exact hω.card_left.trans (Nat.card_congr (subgroupImageEquiv M W1).toEquiv)
  · exact hω.card_right.trans (Nat.card_congr (subgroupImageEquiv M W2).toEquiv)
  · simpa [E, e, hω.principal] using
      (Section1.principalCharacter_classFunctionLinearEquivOfMulEquiv e)
  · intro chi hchi
    let preChi : Section1.ClassFunction W :=
      Section1.classFunctionLinearEquivOfMulEquiv e.symm chi
    have hpreIrred : Section1.IsIrreducibleCharacterOnGroup preChi := by
      exact Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
        e.symm hchi
    constructor
    · intro hker
      have hpreKer : Section1.subgroupInKernel' preChi (W2.subgroupOf W) := by
        intro x
        have hxImage :
            e x.1 ∈
              (Section4Scratch.subgroupImage M W2).subgroupOf
                (Section4Scratch.subgroupImage M W) :=
          subgroupImageEquiv_apply_mem_subgroupOf
            (M := M) (S := W2) (W := W) x.2
        calc
          preChi x.1 = chi (e x.1) := rfl
          _ = Section1.degree chi := hker ⟨e x.1, hxImage⟩
          _ = Section1.degree preChi :=
              (Section1.degree_classFunctionLinearEquivOfMulEquiv e.symm chi).symm
      rcases (hω.left_kernel_exact preChi hpreIrred).1 hpreKer with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      ext x
      calc
        chi x = preChi (e.symm x) := by
          simp [preChi, Section1.classFunctionLinearEquivOfMulEquiv]
        _ = omega i j0 (e.symm x) := congrFun hi (e.symm x)
    · rintro ⟨i, rfl⟩
      exact hleftKernel i
  · intro chi hchi
    let preChi : Section1.ClassFunction W :=
      Section1.classFunctionLinearEquivOfMulEquiv e.symm chi
    have hpreIrred : Section1.IsIrreducibleCharacterOnGroup preChi := by
      exact Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
        e.symm hchi
    constructor
    · intro hker
      have hpreKer : Section1.subgroupInKernel' preChi (W1.subgroupOf W) := by
        intro x
        have hxImage :
            e x.1 ∈
              (Section4Scratch.subgroupImage M W1).subgroupOf
                (Section4Scratch.subgroupImage M W) :=
          subgroupImageEquiv_apply_mem_subgroupOf
            (M := M) (S := W1) (W := W) x.2
        calc
          preChi x.1 = chi (e x.1) := rfl
          _ = Section1.degree chi := hker ⟨e x.1, hxImage⟩
          _ = Section1.degree preChi :=
              (Section1.degree_classFunctionLinearEquivOfMulEquiv e.symm chi).symm
      rcases (hω.right_kernel_exact preChi hpreIrred).1 hpreKer with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      ext x
      calc
        chi x = preChi (e.symm x) := by
          simp [preChi, Section1.classFunctionLinearEquivOfMulEquiv]
        _ = omega i0 j (e.symm x) := congrFun hj (e.symm x)
    · rintro ⟨j, rfl⟩
      exact hrightKernel j
  · intro i j x
    simpa [E, e, Section1.classFunctionLinearEquivOfMulEquiv] using
      hω.product i j (e.symm x)
  · intro i j
    rw [Section1.degree_classFunctionLinearEquivOfMulEquiv e, hω.degree_one i j]
  · intro i j
    exact Section1.isClassFunction_classFunctionLinearEquivOfMulEquiv e
      (hω.is_class i j)
  · intro i j
    exact Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
      e (hω.irreducible i j)
  · intro p q
    calc
      Section1.scalarProduct (Section4Scratch.subgroupImage M W)
          (E (omega p.1 p.2)) (E (omega q.1 q.2)) =
          Section1.scalarProduct W (omega p.1 p.2) (omega q.1 q.2) :=
            Section1.scalarProduct_classFunctionLinearEquivOfMulEquiv
              e (omega p.1 p.2) (omega q.1 q.2)
      _ = if p = q then 1 else 0 := hω.orthonormal p q
  · intro i i' j j' hEq
    exact hω.pairwise_eq (E.injective hEq)
  · intro chi hchi
    let preChi : Section1.ClassFunction W :=
      Section1.classFunctionLinearEquivOfMulEquiv e.symm chi
    have hpreIrred : Section1.IsIrreducibleCharacterOnGroup preChi := by
      exact Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
        e.symm hchi
    rcases hω.all_irreducibles preChi hpreIrred with ⟨i, j, hij⟩
    refine ⟨i, j, ?_⟩
    ext x
    calc
      chi x = preChi (e.symm x) := by
        simp [preChi, Section1.classFunctionLinearEquivOfMulEquiv]
      _ = omega i j (e.symm x) := congrFun hij (e.symm x)

public theorem characterValueOrder_classFunctionLinearEquivOfMulEquiv_iff
    {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) (φ : Section1.ClassFunction A) (a : ℕ) :
    Section3.characterValueOrder
        (Section1.classFunctionLinearEquivOfMulEquiv e φ) a ↔
      Section3.characterValueOrder φ a := by
  constructor
  · intro h
    rcases h with ⟨ha, hpow⟩
    refine ⟨ha, ?_⟩
    intro x
    simpa [Section1.classFunctionLinearEquivOfMulEquiv] using hpow (e x)
  · intro h
    rcases h with ⟨ha, hpow⟩
    refine ⟨ha, ?_⟩
    intro y
    simpa [Section1.classFunctionLinearEquivOfMulEquiv] using hpow (e.symm y)

public theorem exactCharacterValueOrder_classFunctionLinearEquivOfMulEquiv_iff
    {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) (φ : Section1.ClassFunction A) (a : ℕ) :
    Section3.exactCharacterValueOrder
        (Section1.classFunctionLinearEquivOfMulEquiv e φ) a ↔
      Section3.exactCharacterValueOrder φ a := by
  constructor
  · intro h
    rcases h with ⟨horder, hminimal⟩
    refine
      ⟨(characterValueOrder_classFunctionLinearEquivOfMulEquiv_iff e φ a).1
          horder, ?_⟩
    intro b hb
    exact hminimal b
      ((characterValueOrder_classFunctionLinearEquivOfMulEquiv_iff e φ b).2 hb)
  · intro h
    rcases h with ⟨horder, hminimal⟩
    refine
      ⟨(characterValueOrder_classFunctionLinearEquivOfMulEquiv_iff e φ a).2
          horder, ?_⟩
    intro b hb
    exact hminimal b
      ((characterValueOrder_classFunctionLinearEquivOfMulEquiv_iff e φ b).1 hb)

/-- Transport the ambient-relative PF `(3.9)(a,c)` base-column endpoints from
the ambient subgroup image back to the relative subgroup carrier. -/
public theorem ambientRelativePF39BaseColumnData_of_subgroupImage
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {W1 W : Subgroup M}
    {I J : Type*}
    {i0 : I} {j0 : J}
    {omega : I → J → Section1.ClassFunction W}
    {sigmaImage :
      Section1.ClassFunction (Section4Scratch.subgroupImage M W) →ₗ[ℂ]
        Section1.ClassFunction G}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hImage :
      Section4Scratch.ambientRelativePF39BaseColumnData
        (Nat.card W1)
        (Section4Scratch.subgroupImage M W) i0 j0
        (fun i j =>
          Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M W) (omega i j))
        sigmaImage)
    (hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M W)).toLinearMap) :
    Section4Scratch.ambientRelativePF39BaseColumnData
      (Nat.card W1) W i0 j0 omega sigma := by
  classical
  let e := subgroupImageEquiv M W
  let E := Section1.classFunctionLinearEquivOfMulEquiv e
  rcases hImage with ⟨hInteger, hConj⟩
  constructor
  · intro i hi a ha g hg
    have haImage :
        Section3.exactCharacterValueOrder (E (omega i j0)) a :=
      (exactCharacterValueOrder_classFunctionLinearEquivOfMulEquiv_iff
        e (omega i j0) a).2 ha
    simpa [hSigmaDef, e, E] using hInteger i hi haImage g hg
  · intro g hg c hc i hi
    have hcImage :
        ∀ i : I,
          Section1.conjugateCharacter (E (omega i j0)) =
            E (omega (c i) j0) := by
      intro i
      calc
        Section1.conjugateCharacter (E (omega i j0)) =
            E (Section1.conjugateCharacter (omega i j0)) := by
              exact
        (Section1.conjugateCharacter_classFunctionLinearEquivOfMulEquiv
          e (omega i j0)).symm
        _ = E (omega (c i) j0) := by rw [hc i]
    simpa [hSigmaDef, e, E] using hConj g hg c hcImage i hi

/-- Transport the ambient-relative PF `(3.9)(a)` base-row conjugation endpoint
from the ambient subgroup image back to the relative subgroup carrier. -/
public theorem ambientRelativePF39BaseRowConjugateData_of_subgroupImage
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {W : Subgroup M}
    {I J : Type*}
    {i0 : I} {j0 : J}
    {omega : I → J → Section1.ClassFunction W}
    {sigmaImage :
      Section1.ClassFunction (Section4Scratch.subgroupImage M W) →ₗ[ℂ]
        Section1.ClassFunction G}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hImage :
      Section4Scratch.ambientRelativePF39BaseRowConjugateData
        (Section4Scratch.subgroupImage M W) i0 j0
        (fun i j =>
          Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M W) (omega i j))
        sigmaImage)
    (hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M W)).toLinearMap) :
    Section4Scratch.ambientRelativePF39BaseRowConjugateData
      W i0 j0 omega sigma := by
  intro j hj
  let e := subgroupImageEquiv M W
  let E := Section1.classFunctionLinearEquivOfMulEquiv e
  have hImageConj := hImage j hj
  rw [hSigmaDef]
  change sigmaImage (E (Section1.conjugateCharacter (omega i0 j))) =
    Section1.conjugateCharacter (sigmaImage (E (omega i0 j)))
  rw [Section1.conjugateCharacter_classFunctionLinearEquivOfMulEquiv]
  exact hImageConj

/-- Transport the PF `(3.9)(a)` conjugation compatibility of an ambient-image
Section `(3.2)` map back to the relative subgroup carrier. -/
public theorem ambientRelativePF39ConjugateData_of_subgroupImage
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {W1 W2 W : Subgroup M}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J → Section1.ClassFunction W}
    {sigmaImage :
      Section1.ClassFunction (Section4Scratch.subgroupImage M W) →ₗ[ℂ]
        Section1.ClassFunction G}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h31 :
      Section3.hypothesis_3_1_statement
        (Section4Scratch.subgroupImage M W1)
        (Section4Scratch.subgroupImage M W2)
        (Section4Scratch.subgroupImage M W))
    (homega : Section3.notation_3_3_statement W1 W2 W I J i0 j0 omega)
    (hSigmaImage :
      Section3.theorem_3_2_map_statement
        (Section4Scratch.subgroupImage M W1)
        (Section4Scratch.subgroupImage M W2)
        (Section4Scratch.subgroupImage M W) sigmaImage)
    (hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M W)).toLinearMap) :
    Section4Scratch.ambientRelativePF39ConjugateData W sigma := by
  classical
  let e := subgroupImageEquiv M W
  let E := Section1.classFunctionLinearEquivOfMulEquiv e
  let omegaImage : I → J →
      Section1.ClassFunction (Section4Scratch.subgroupImage M W) :=
    fun i j => E (omega i j)
  have hOmegaImage :
      Section3.notation_3_3_statement
        (Section4Scratch.subgroupImage M W1)
        (Section4Scratch.subgroupImage M W2)
        (Section4Scratch.subgroupImage M W) I J i0 j0 omegaImage := by
    simpa [omegaImage, E, e] using
      notation_3_3_statement_of_subgroupImageEquiv
        (M := M) (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0) (omega := omega) homega
  intro eta heta
  have hEeta : Section1.IsIrreducibleCharacterOnGroup (E eta) :=
    Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
      e heta
  have hImageConj :=
    Section3.theorem_3_2_map_conjugateCharacter_of_irreducible
      h31 hOmegaImage sigmaImage hSigmaImage hEeta
  rw [hSigmaDef]
  change sigmaImage (E (Section1.conjugateCharacter eta)) =
    Section1.conjugateCharacter (sigmaImage (E eta))
  rw [Section1.conjugateCharacter_classFunctionLinearEquivOfMulEquiv]
  exact hImageConj

/-- Extract the base-column consequences used by Section `(4.6)` from the
formal PF `(3.9)(c)` statement plus the exact conjugation endpoint needed on
the base column. -/
public theorem ambientRelativePF39BaseColumnData_of_pf39_base_column
    {G : Type u} [Group G] [Finite G]
    {W1 W : Subgroup G}
    {I J : Type*}
    {i0 : I} {j0 : J}
    {omega : I → J → Section1.ClassFunction W}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hIrred : ∀ i : I,
      Section1.IsIrreducibleCharacterOnGroup (omega i j0))
    (h39c : Section3.proposition_3_9_statement_c sigma)
    (hConj :
      ∀ g : G, Nat.Coprime (orderOf g) (Nat.card W1) →
        ∀ c : I → I,
          (∀ i : I,
            Section1.conjugateCharacter (omega i j0) = omega (c i) j0) →
            ∀ i : I, i ≠ i0 →
              sigma (omega (c i) j0) g = sigma (omega i j0) g) :
    Section4Scratch.ambientRelativePF39BaseColumnData
      (Nat.card W1) W i0 j0 omega sigma := by
  classical
  constructor
  · intro i hi a ha g hg
    exact h39c (hIrred i) ha g hg
  · exact hConj

public theorem isCFLinearIsometry_of_subgroupImage_sigmaDef
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {W : Subgroup M}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {sigmaImage :
      Section1.ClassFunction (Section4Scratch.subgroupImage M W) →ₗ[ℂ]
        Section1.ClassFunction G}
    (hSigmaImage : Section3.IsCFLinearIsometry sigmaImage)
    (hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M W)).toLinearMap) :
    Section3.IsCFLinearIsometry sigma := by
  classical
  let e := subgroupImageEquiv M W
  let E := Section1.classFunctionLinearEquivOfMulEquiv e
  intro α β hα hβ
  have hEα : Section1.IsClassFunction (E α) :=
    Section1.isClassFunction_classFunctionLinearEquivOfMulEquiv e hα
  have hEβ : Section1.IsClassFunction (E β) :=
    Section1.isClassFunction_classFunctionLinearEquivOfMulEquiv e hβ
  rw [hSigmaDef]
  change Section1.scalarProduct G (sigmaImage (E α)) (sigmaImage (E β)) =
    Section1.scalarProduct W α β
  calc
    Section1.scalarProduct G (sigmaImage (E α)) (sigmaImage (E β)) =
        Section1.scalarProduct (Section4Scratch.subgroupImage M W)
          (E α) (E β) := hSigmaImage _ _ hEα hEβ
    _ = Section1.scalarProduct W α β :=
        Section1.scalarProduct_classFunctionLinearEquivOfMulEquiv e α β

public theorem mapsVirtualCharacters_of_subgroupImage_sigmaDef
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {W : Subgroup M}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {sigmaImage :
      Section1.ClassFunction (Section4Scratch.subgroupImage M W) →ₗ[ℂ]
        Section1.ClassFunction G}
    (hSigmaImage : Section3.MapsVirtualCharacters sigmaImage)
    (hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M W)).toLinearMap) :
    Section3.MapsVirtualCharacters sigma := by
  classical
  let e := subgroupImageEquiv M W
  let E := Section1.classFunctionLinearEquivOfMulEquiv e
  intro β hβ
  rw [hSigmaDef]
  change Theory.Character.IsVirtualCharacter (sigmaImage (E β))
  exact hSigmaImage (E β)
    (Section1.virtualCharacter_classFunctionLinearEquivOfMulEquiv e hβ)

public theorem mapsClassFunctions_of_subgroupImage_sigmaDef
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {W : Subgroup M}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {sigmaImage :
      Section1.ClassFunction (Section4Scratch.subgroupImage M W) →ₗ[ℂ]
        Section1.ClassFunction G}
    (hSigmaImage : Section3.MapsClassFunctions sigmaImage)
    (hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M W)).toLinearMap) :
    Section3.MapsClassFunctions sigma := by
  classical
  let e := subgroupImageEquiv M W
  let E := Section1.classFunctionLinearEquivOfMulEquiv e
  intro α hα
  rw [hSigmaDef]
  change Section1.IsClassFunction (sigmaImage (E α))
  exact hSigmaImage (E α)
    (Section1.isClassFunction_classFunctionLinearEquivOfMulEquiv e hα)

public theorem principalCharacter_of_subgroupImage_sigmaDef
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {W : Subgroup M}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {sigmaImage :
      Section1.ClassFunction (Section4Scratch.subgroupImage M W) →ₗ[ℂ]
        Section1.ClassFunction G}
    (hSigmaImage :
      sigmaImage
          (Section1.principalCharacter (Section4Scratch.subgroupImage M W)) =
        Section1.principalCharacter G)
    (hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M W)).toLinearMap) :
    sigma (Section1.principalCharacter W) = Section1.principalCharacter G := by
  classical
  let e := subgroupImageEquiv M W
  let E := Section1.classFunctionLinearEquivOfMulEquiv e
  rw [hSigmaDef]
  change sigmaImage (E (Section1.principalCharacter W)) =
    Section1.principalCharacter G
  rw [Section1.principalCharacter_classFunctionLinearEquivOfMulEquiv e]
  exact hSigmaImage

public theorem agreesOnCyclicTISet_of_subgroupImage_sigmaDef
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {W1 W2 W : Subgroup M}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {sigmaImage :
      Section1.ClassFunction (Section4Scratch.subgroupImage M W) →ₗ[ℂ]
        Section1.ClassFunction G}
    (hSigmaImage :
      Section3.AgreesOnCyclicTISet
        (Section4Scratch.subgroupImage M W1)
        (Section4Scratch.subgroupImage M W2)
        (Section4Scratch.subgroupImage M W) sigmaImage)
    (hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M W)).toLinearMap) :
    ∀ α : Section1.ClassFunction W, Section1.IsClassFunction α →
      ∀ x : M, ∀ hx : x ∈ Section3.cyclicTISet W1 W2 W,
        sigma α (x : G) =
          α ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩ := by
  classical
  let e := subgroupImageEquiv M W
  let E := Section1.classFunctionLinearEquivOfMulEquiv e
  intro α hα x hx
  let xW : W := ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩
  have hEα : Section1.IsClassFunction (E α) :=
    Section1.isClassFunction_classFunctionLinearEquivOfMulEquiv e hα
  have hxImage :
      ((e xW : Section4Scratch.subgroupImage M W) : G) ∈
        Section3.cyclicTISet
          (Section4Scratch.subgroupImage M W1)
          (Section4Scratch.subgroupImage M W2)
          (Section4Scratch.subgroupImage M W) :=
    subgroupImageEquiv_mem_cyclicTISet (M := M) (W1 := W1) (W2 := W2)
      (W := W) (x := xW) hx
  have hval :=
    hSigmaImage (E α) hEα (e xW) hxImage
  have hxArg :
      (e.symm
        (⟨e xW, Section3.cyclicTISet_subset
          (Section4Scratch.subgroupImage M W1)
          (Section4Scratch.subgroupImage M W2)
          (Section4Scratch.subgroupImage M W) hxImage⟩ :
            Section4Scratch.subgroupImage M W)) = xW := by
    simp [e]
  have hright :
      E α
        (⟨e xW, Section3.cyclicTISet_subset
          (Section4Scratch.subgroupImage M W1)
          (Section4Scratch.subgroupImage M W2)
          (Section4Scratch.subgroupImage M W) hxImage⟩ :
            Section4Scratch.subgroupImage M W) = α xW := by
    calc
      E α
          (⟨e xW, Section3.cyclicTISet_subset
            (Section4Scratch.subgroupImage M W1)
            (Section4Scratch.subgroupImage M W2)
            (Section4Scratch.subgroupImage M W) hxImage⟩ :
              Section4Scratch.subgroupImage M W) =
          α
            (e.symm
              (⟨e xW, Section3.cyclicTISet_subset
                (Section4Scratch.subgroupImage M W1)
                (Section4Scratch.subgroupImage M W2)
                (Section4Scratch.subgroupImage M W) hxImage⟩ :
                  Section4Scratch.subgroupImage M W)) := by
            simpa [E] using
              Section1.classFunctionLinearEquivOfMulEquiv_apply e α
                (⟨e xW, Section3.cyclicTISet_subset
                  (Section4Scratch.subgroupImage M W1)
                  (Section4Scratch.subgroupImage M W2)
                  (Section4Scratch.subgroupImage M W) hxImage⟩ :
                    Section4Scratch.subgroupImage M W)
      _ = α xW := by rw [hxArg]
  rw [hright] at hval
  rw [hSigmaDef]
  simpa [E, e, xW, subgroupImageEquiv_apply_coe] using hval


/-- Transport the ambient cyclic-TI Section `(3.2)` map on the subgroup image
back to the relative subgroup carrier, while retaining the ambient-image map
and the definitional relation between the two maps.

This stronger package records the provenance of the relative `σ`; downstream
source leaves should use this instead of accepting an arbitrary map with only
the four projected Section 3 fields. -/
public theorem exists_subgroupImage_section3_sigma_transport_data_with_image
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {W1 W2 W : Subgroup M}
    (h31 :
      Section3.hypothesis_3_1_statement
        (Section4Scratch.subgroupImage M W1)
        (Section4Scratch.subgroupImage M W2)
        (Section4Scratch.subgroupImage M W)) :
    ∃ sigmaImage :
      Section1.ClassFunction (Section4Scratch.subgroupImage M W) →ₗ[ℂ]
        Section1.ClassFunction G,
      ∃ sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
        Section3.theorem_3_2_map_statement
          (Section4Scratch.subgroupImage M W1)
          (Section4Scratch.subgroupImage M W2)
          (Section4Scratch.subgroupImage M W)
          sigmaImage ∧
        sigma =
          sigmaImage.comp
            (Section1.classFunctionLinearEquivOfMulEquiv
              (subgroupImageEquiv M W)).toLinearMap ∧
        Section3.IsCFLinearIsometry sigma ∧
        Section3.MapsVirtualCharacters sigma ∧
        Section3.MapsClassFunctions sigma ∧
        sigma (Section1.principalCharacter W) =
          Section1.principalCharacter G ∧
        (∀ α : Section1.ClassFunction W, Section1.IsClassFunction α →
          ∀ x : M, ∀ hx : x ∈ Section3.cyclicTISet W1 W2 W,
              sigma α (x : G) =
                α ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩) := by
  classical
  rcases Section3.exists_notation_3_3_of_hypothesis_3_1 h31 with
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, omega, hω⟩
  letI : Fintype I := instFintypeI
  letI : Fintype J := instFintypeJ
  letI : DecidableEq I := instDecidableEqI
  letI : DecidableEq J := instDecidableEqJ
  rcases Section3.theorem_3_2_of_notation_3_3
      (Section4Scratch.subgroupImage M W1)
      (Section4Scratch.subgroupImage M W2)
      (Section4Scratch.subgroupImage M W)
      I J i0 j0 omega h31 hω with
    ⟨sigmaImage, hSigmaImage⟩
  let sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G :=
    sigmaImage.comp
      (Section1.classFunctionLinearEquivOfMulEquiv
        (subgroupImageEquiv M W)).toLinearMap
  refine ⟨sigmaImage, sigma, hSigmaImage, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact isCFLinearIsometry_of_subgroupImage_sigmaDef
      (M := M) (W := W) (sigmaImage := sigmaImage) hSigmaImage.1 rfl
  · exact mapsVirtualCharacters_of_subgroupImage_sigmaDef
      (M := M) (W := W) (sigmaImage := sigmaImage) hSigmaImage.2.1 rfl
  · exact mapsClassFunctions_of_subgroupImage_sigmaDef
      (M := M) (W := W) (sigmaImage := sigmaImage) hSigmaImage.2.2.2.1 rfl
  · exact principalCharacter_of_subgroupImage_sigmaDef
      (M := M) (W := W) (sigmaImage := sigmaImage) hSigmaImage.2.2.2.2.1 rfl
  · exact agreesOnCyclicTISet_of_subgroupImage_sigmaDef
      (M := M) (W1 := W1) (W2 := W2) (W := W) (sigmaImage := sigmaImage)
      hSigmaImage.2.2.2.2.2.1 rfl

/-- Transport an internal direct product from a subgroup carrier back to the
ambient group. -/
public theorem internalDirectProduct_of_subgroupOf
    {G : Type u} [Group G]
    {M C H K : Subgroup G}
    (hCM : C ≤ M) (hHM : H ≤ M) (hKM : K ≤ M)
    (h :
      Section2.IsInternalDirectProduct
        (C.subgroupOf M) (H.subgroupOf M) (K.subgroupOf M)) :
    Section2.IsInternalDirectProduct C H K := by
  refine
    { left_le := ?_
      right_le := ?_
      commute := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro x hx
    have hxLocal : (⟨x, hHM hx⟩ : M) ∈ H.subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxC : (⟨x, hHM hx⟩ : M) ∈ C.subgroupOf M := h.left_le hxLocal
    simpa [Subgroup.mem_subgroupOf] using hxC
  · intro x hx
    have hxLocal : (⟨x, hKM hx⟩ : M) ∈ K.subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxC : (⟨x, hKM hx⟩ : M) ∈ C.subgroupOf M := h.right_le hxLocal
    simpa [Subgroup.mem_subgroupOf] using hxC
  · intro x hx y hy
    have hxLocal : (⟨x, hHM hx⟩ : M) ∈ H.subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hyLocal : (⟨y, hKM hy⟩ : M) ∈ K.subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hy
    exact congrArg Subtype.val (h.commute _ hxLocal _ hyLocal)
  · apply le_antisymm
    · intro x hx
      have hxH : x ∈ H := hx.1
      have hxK : x ∈ K := hx.2
      let xM : M := ⟨x, hHM hxH⟩
      have hxLocal : xM ∈ H.subgroupOf M ⊓ K.subgroupOf M := by
        exact ⟨by simpa [xM, Subgroup.mem_subgroupOf] using hxH,
          by simpa [xM, Subgroup.mem_subgroupOf] using hxK⟩
      have hxBot : xM ∈ (⊥ : Subgroup M) := by
        simpa [h.inf_eq_bot] using hxLocal
      have hxOne : x = 1 := by
        simpa [xM] using congrArg Subtype.val (show xM = 1 from by simpa using hxBot)
      simp [hxOne]
    · exact bot_le
  · intro c hc
    let cM : M := ⟨c, hCM hc⟩
    have hcLocal : cM ∈ C.subgroupOf M := by
      simpa [cM, Subgroup.mem_subgroupOf] using hc
    rcases h.mul_surjective cM hcLocal with ⟨x, hxH, y, hyK, hxy⟩
    refine ⟨(x : G), ?_, (y : G), ?_, ?_⟩
    · simpa [Subgroup.mem_subgroupOf] using hxH
    · simpa [Subgroup.mem_subgroupOf] using hyK
    · simpa [cM] using congrArg Subtype.val hxy


public theorem theorem_8_15_typeP_W_ambientInternalDirectProduct
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    Section2.IsInternalDirectProduct (W1 ⊔ W2) W1 W2 := by
  have hP0 : typePDefinitionData M MF U W1 W2 := hP
  rcases hP with
    ⟨_hMF, hW1cyc, hW1ne, hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, hW2cyc, hW2ne, _hCent, _hHatW⟩
  rcases hW1hall with ⟨_hW1M, _hW1HallSub⟩
  have hW2M : W2 ≤ M := by
    intro x hx
    exact _hMF.1.1 ((_hW2le hx).1)
  exact internalDirectProduct_of_subgroupOf
    (C := W1 ⊔ W2) (H := W1) (K := W2)
    (sup_le _hW1M hW2M) _hW1M hW2M
    (theorem_8_15_typeP_W_internalDirectProduct
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      hP0)

/-- Section 2's set normalizer and Mathlib's subgroup normalizer are the same
setwise normalizer. -/
public theorem section2_setNormalizer_eq_subgroupNormalizer
    {G : Type u} [Group G] (A : Set G) :
    Section2.setNormalizer A = Subgroup.normalizer A := by
  ext g
  simp [Section2.setNormalizer, Section2.normalizesSet, Section2.conjBy,
    Subgroup.normalizer, iff_comm]

public theorem section2_setNormalizer_le_of_subgroupNormalizer
    {G : Type u} [Group G] {M : Subgroup G} {A : Set G}
    (h : M ≤ Subgroup.normalizer A) :
    M ≤ Section2.setNormalizer A := by
  intro m hm
  change Section2.normalizesSet A m
  intro a
  have hmnorm := h hm
  change ∀ a : G, a ∈ A ↔ m * a * m⁻¹ ∈ A at hmnorm
  simpa [Section2.conjBy] using (hmnorm a).symm

/-- Section 16's conjugate set is Section 2's conjugate image. -/
public theorem section16ConjugateSet_eq_section2_conjugateImage
    {G : Type u} [Group G] (A : Set G) (g : G) :
    section16ConjugateSet A g = Section2.conjugateImage A g := by
  ext x
  simp [section16ConjugateSet, Section2.conjugateImage, Section2.conjBy]

/-- Convert the Section 16 TI predicate to the Section 2 TI predicate when
the set contains no identity element. -/
public theorem section2_IsTISubset_of_section16TISubset
    {G : Type u} [Group G] {A : Set G}
    (hAne : ∀ x : G, x ∈ A → x ≠ 1)
    (hTI : section16TISubset A) :
    Section2.IsTISubset A := by
  intro g hinter
  rcases hTI g with hsame | hsmall
  · intro x
    constructor
    · intro hx
      have hxImage : g * x * g⁻¹ ∈ section16ConjugateSet A g := by
        simpa [Section2.conjBy, hsame] using hx
      rcases hxImage with ⟨y, hyA, hy_eq⟩
      have hxy : x = y := by
        have h := congrArg (fun z : G => g⁻¹ * z * g) hy_eq
        simpa [mul_assoc] using h
      simpa [hxy] using hyA
    · intro hx
      have hxImage : g * x * g⁻¹ ∈ section16ConjugateSet A g :=
        ⟨x, hx, rfl⟩
      simpa [Section2.conjBy, hsame] using hxImage
  · exfalso
    rcases hinter with ⟨x, hxA, hxConj⟩
    have hxConj16 : x ∈ section16ConjugateSet A g := by
      simpa [section16ConjugateSet_eq_section2_conjugateImage] using hxConj
    have hxOne : x = 1 := by
      have hxSmall : x ∈ ({1} : Set G) := hsmall ⟨hxA, hxConj16⟩
      simpa using hxSmall
    exact hAne x hxA hxOne

/-- Convert Section 16's TI-with-normalizer package to Section 2's
TI-with-normalizer package for identity-free sets. -/
public theorem section2_IsTISubsetWithNormalizer_of_section16
    {G : Type u} [Group G] {A : Set G} {N : Subgroup G}
    (hAne : ∀ x : G, x ∈ A → x ≠ 1)
    (hAnonempty : A.Nonempty)
    (hTI : section16TISubsetWithNormalizer A N) :
    Section2.IsTISubsetWithNormalizer A N := by
  refine ⟨hAnonempty, hAne, ?_, ?_⟩
  · exact section2_IsTISubset_of_section16TISubset hAne hTI.1
  · calc
      Section2.setNormalizer A = Subgroup.normalizer A :=
        section2_setNormalizer_eq_subgroupNormalizer A
      _ = N := hTI.2

/-- The Type-P cyclic-TI carrier `\hat W` is nonempty. -/
public theorem theorem_8_15_typeP_hatW_nonempty
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    (section16HatW W1 W2).Nonempty := by
  classical
  rcases hP with
    ⟨_hMF, _hW1cyc, hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, hW2ne, _hCent, _hHatW⟩
  let hP0 : typePDefinitionData M MF U W1 W2 :=
    ⟨_hMF, _hW1cyc, hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, hW2ne, _hCent, _hHatW⟩
  have hIP :
      Section2.IsInternalDirectProduct (W1 ⊔ W2) W1 W2 :=
    theorem_8_15_typeP_W_ambientInternalDirectProduct hP0
  obtain ⟨a, haW1, ha1⟩ : ∃ a : G, a ∈ W1 ∧ a ≠ 1 := by
    by_contra hnone
    apply hW1ne
    apply le_antisymm
    · intro x hx
      have hx1 : x = 1 := by
        by_contra hxne
        exact hnone ⟨x, hx, hxne⟩
      simp [hx1]
    · exact bot_le
  obtain ⟨b, hbW2, hb1⟩ : ∃ b : G, b ∈ W2 ∧ b ≠ 1 := by
    by_contra hnone
    apply hW2ne
    apply le_antisymm
    · intro x hx
      have hx1 : x = 1 := by
        by_contra hxne
        exact hnone ⟨x, hx, hxne⟩
      simp [hx1]
    · exact bot_le
  refine ⟨a * b, ?_⟩
  constructor
  · exact Subgroup.mul_mem_sup haW1 hbW2
  · intro hab
    rcases hab with habW1 | habW2
    · have hbW1 : b ∈ W1 := by
        have h : a⁻¹ * (a * b) ∈ W1 := W1.mul_mem (W1.inv_mem haW1) habW1
        simpa [mul_assoc] using h
      have hbInf : b ∈ W1 ⊓ W2 := ⟨hbW1, hbW2⟩
      have hbBot : b ∈ (⊥ : Subgroup G) := by
        simpa [hIP.inf_eq_bot] using hbInf
      exact hb1 (by simpa using hbBot)
    · have haW2 : a ∈ W2 := by
        have h : (a * b) * b⁻¹ ∈ W2 := W2.mul_mem habW2 (W2.inv_mem hbW2)
        simpa [mul_assoc] using h
      have haInf : a ∈ W1 ⊓ W2 := ⟨haW1, haW2⟩
      have haBot : a ∈ (⊥ : Subgroup G) := by
        simpa [hIP.inf_eq_bot] using haInf
      exact ha1 (by simpa using haBot)


public theorem theorem_8_15_ambient_hypothesis_3_1_of_typeP
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    Section3.hypothesis_3_1_statement W1 W2 (W1 ⊔ W2) := by
  classical
  have hP0 : typePDefinitionData M MF U W1 W2 := hP
  rcases hP with
    ⟨hMF, hW1cyc, hW1ne, hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, hW2le, hW2cyc, hW2ne, _hCent, _hHatW⟩
  rcases hW1hall with ⟨hW1M, _hW1HallSub⟩
  have hW2M : W2 ≤ M := by
    intro x hx
    exact hMF.1.1 ((hW2le hx).1)
  have hWleM : W1 ⊔ W2 ≤ M := sup_le hW1M hW2M
  have hLocal31 :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf M) (W2.subgroupOf M) ((W1 ⊔ W2).subgroupOf M) :=
    theorem_8_15_hypothesis_3_1_of_typeP
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (by infer_instance) hP0
  have hWcycLocal : IsCyclic ((W1 ⊔ W2).subgroupOf M) := hLocal31.2.2.2.1
  have hWoddLocal : Odd (Nat.card ((W1 ⊔ W2).subgroupOf M)) := hLocal31.2.2.2.2.1
  have hWcyc : IsCyclic (W1 ⊔ W2 : Subgroup G) :=
    (Subgroup.subgroupOfEquivOfLe (H := W1 ⊔ W2) (K := M) hWleM).isCyclic.1
      hWcycLocal
  have hWcard :
      Nat.card ((W1 ⊔ W2).subgroupOf M) =
        Nat.card (W1 ⊔ W2 : Subgroup G) :=
    natCard_subgroupOf_eq (W1 ⊔ W2 : Subgroup G) M hWleM
  have hWodd : Odd (Nat.card (W1 ⊔ W2 : Subgroup G)) := by
    simpa [hWcard] using hWoddLocal
  have hW1card_ne : Nat.card W1 ≠ 1 := by
    intro hcard
    exact hW1ne ((Subgroup.card_eq_one (H := W1)).1 hcard)
  have hW2card_ne : Nat.card W2 ≠ 1 := by
    intro hcard
    exact hW2ne ((Subgroup.card_eq_one (H := W2)).1 hcard)
  have hHatNonempty : (section16HatW W1 W2).Nonempty :=
    theorem_8_15_typeP_hatW_nonempty hP0
  have hHat_ne_one : ∀ x : G, x ∈ section16HatW W1 W2 → x ≠ 1 := by
    intro x hx hx1
    exact hx.2 (Or.inl (by simp [hx1]))
  have hTI16 :
      section16TISubsetWithNormalizer (section16HatW W1 W2) (W1 ⊔ W2) :=
    theorem_8_5_c (G := G) M MF U W1 W2 hP0
  have hTI2 :
      Section2.IsTISubsetWithNormalizer (section16HatW W1 W2) (W1 ⊔ W2) :=
    section2_IsTISubsetWithNormalizer_of_section16 hHat_ne_one hHatNonempty hTI16
  refine ⟨le_sup_left, le_sup_right, ?_, hWcyc, hWodd, hW1card_ne, hW2card_ne, ?_⟩
  · exact theorem_8_15_typeP_W_ambientInternalDirectProduct hP0
  · simpa [Section3.cyclicTISet, section16HatW] using hTI2


public theorem theorem_8_15_subgroupImage_hypothesis_3_1_of_typeP
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    Section3.hypothesis_3_1_statement
      (Section4Scratch.subgroupImage M (W1.subgroupOf M))
      (Section4Scratch.subgroupImage M (W2.subgroupOf M))
      (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M)) := by
  have hP0 : typePDefinitionData M MF U W1 W2 := hP
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  have hW1M : W1 ≤ M := hW1hall.1
  have hW2M : W2 ≤ M := by
    intro x hx
    exact hMF.1.1 ((hW2le hx).1)
  have hWM : W1 ⊔ W2 ≤ M := sup_le hW1M hW2M
  have h31 :
      Section3.hypothesis_3_1_statement W1 W2 (W1 ⊔ W2) :=
    theorem_8_15_ambient_hypothesis_3_1_of_typeP hP0
  simpa [subgroupImage_subgroupOf_eq hW1M, subgroupImage_subgroupOf_eq hW2M,
    subgroupImage_subgroupOf_eq hWM] using h31

/-- The checked static prefix of the full Section `(4.6)` record for a
witness selected by the fixed Type-V notation: bare `(4.6)`, the
`FT_primeTI_hyp` containment `W₂ ≤ M'`, and the `FT_cyclicTI_hyp`
subgroup-image field.

The remaining full-record fields are the prime-Dade/subcoherence data that
construct the ambient `σ` and Dade transform `τ`. -/
public theorem theorem_8_15_fullHypothesis_static_prefix_of_typeP_bot_typeV_witness
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2') :
    Section4Scratch.hypothesis_4_6_statement
        (derivedSubgroup M)
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        (Ms.subgroupOf M)
        (section8SubgroupSetPreimage M A) ∧
      W2'.subgroupOf M ≤ derivedSubgroup M ∧
      Section3.hypothesis_3_1_statement
        (Section4Scratch.subgroupImage M (W1'.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2'.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M)) := by
  rcases theorem_8_15_hypothesis_4_6_source_of_typeP_bot_typeV_witness
      hPbot hNotation hWitness with
    ⟨_h46MF, h46MsSource⟩
  rcases h46MsSource with ⟨_hA0pre, h46Ms, _hAsub⟩
  rcases notation_8_10_source_typeP_witness_typeV_context_of_typeP_bot
      hPbot hNotation hWitness with
    ⟨_hUbot, hPbot', _hV, _hMs, _hMF, _hAcentral, _hA1, _hAeqA1⟩
  have hW2K : W2'.subgroupOf M ≤ derivedSubgroup M :=
    theorem_8_15_typeP_W2_subgroupOf_le_derived
      (G := G) (M := M) (MF := MF) (U := ⊥) (W1 := W1') (W2 := W2')
      hPbot'
  have h31 :
      Section3.hypothesis_3_1_statement
        (Section4Scratch.subgroupImage M (W1'.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2'.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M)) :=
    theorem_8_15_subgroupImage_hypothesis_3_1_of_typeP
      (G := G) (M := M) (MF := MF) (U := ⊥) (W1 := W1') (W2 := W2')
      hPbot'
  exact ⟨h46Ms, hW2K, h31⟩


/-- Witness-local ambient `σ` together with its subgroup-image Section `(3.2)`
source map.  This is the provenance-aware version of
`exists_typeP_ambient_section3_sigma_data_of_typeP_bot_typeV_witness`. -/
public theorem exists_typeP_ambient_section3_sigma_transport_data_of_typeP_bot_typeV_witness
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2') :
    ∃ sigmaImage :
      Section1.ClassFunction
          (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M)) →ₗ[ℂ]
        Section1.ClassFunction G,
      ∃ sigma :
        Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
          Section1.ClassFunction G,
        Section3.theorem_3_2_map_statement
          (Section4Scratch.subgroupImage M (W1'.subgroupOf M))
          (Section4Scratch.subgroupImage M (W2'.subgroupOf M))
          (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
          sigmaImage ∧
        sigma =
          sigmaImage.comp
            (Section1.classFunctionLinearEquivOfMulEquiv
              (subgroupImageEquiv M ((W1' ⊔ W2').subgroupOf M))).toLinearMap ∧
        Section3.IsCFLinearIsometry sigma ∧
        Section3.MapsVirtualCharacters sigma ∧
        Section3.MapsClassFunctions sigma ∧
        sigma
          (Section1.principalCharacter ((W1' ⊔ W2').subgroupOf M)) =
          Section1.principalCharacter G ∧
        (∀ α : Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M),
          Section1.IsClassFunction α →
          ∀ x : M,
          ∀ hx : x ∈ Section3.cyclicTISet
              (W1'.subgroupOf M) (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M),
              sigma α (x : G) =
                α ⟨x, Section3.cyclicTISet_subset
                  (W1'.subgroupOf M) (W2'.subgroupOf M)
                  ((W1' ⊔ W2').subgroupOf M) hx⟩) := by
  rcases theorem_8_15_fullHypothesis_static_prefix_of_typeP_bot_typeV_witness
      hPbot hNotation hWitness with
    ⟨_h46, _hW2K, h31⟩
  exact exists_subgroupImage_section3_sigma_transport_data_with_image h31


public theorem CFOn_of_supportedOn_subgroupImageSet
    {G : Type u} [Group G] {L : Subgroup G} {A : Set L}
    {α : Section1.ClassFunction L}
    (hClass : Section1.IsClassFunction α)
    (hSupp : Section1.supportedOn α A) :
    Section2.CFOn L (Section4Scratch.subgroupImageSet L A) α := by
  rw [Section1.supportedOn_iff] at hSupp
  refine ⟨hClass, ?_⟩
  intro l hl
  exact hSupp l (by
    intro hlA
    exact hl ⟨l, hlA, rfl⟩)

/-- Repackage the Section 2 Dade isometry on the exact prime-Dade carrier. -/
public theorem tau_isometry_on_primeDadeA0_of_hypothesis2_dadeTransform
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} [Finite L]
    {W1 W2 W : Subgroup L}
    {H : G → Subgroup G}
    {A : Set L}
    {tau : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h22 :
      Section2.Hypothesis2
        (Section4Scratch.subgroupImageSet L
          (Section4Scratch.primeDadeA0Set W1 W2 W A)) L H)
    (hTau :
      ∀ alpha : Section1.ClassFunction L,
        Section2.CFOn L
            (Section4Scratch.subgroupImageSet L
              (Section4Scratch.primeDadeA0Set W1 W2 W A)) alpha →
          tau alpha = Section2.dadeTransform H h22.subset_L alpha) :
    Section4Scratch.tau_isometry_on_primeDadeA0_statement W1 W2 W A tau := by
  intro alpha beta hAlphaClass hBetaClass hAlphaSupp hBetaSupp
  have hAlphaCF := CFOn_of_supportedOn_subgroupImageSet hAlphaClass hAlphaSupp
  have hBetaCF := CFOn_of_supportedOn_subgroupImageSet hBetaClass hBetaSupp
  rw [hTau alpha hAlphaCF, hTau beta hBetaCF]
  exact
    (Section2.theorem_2_6
      (Section4Scratch.subgroupImageSet L
        (Section4Scratch.primeDadeA0Set W1 W2 W A))
      L H h22 h22.subset_L).1 alpha beta hAlphaCF hBetaCF

/-- Repackage virtual-character preservation on the exact prime-Dade
carrier. -/
public theorem tau_maps_primeDadeA0_to_virtual_of_hypothesis2_dadeTransform
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} [Finite L]
    {W1 W2 W : Subgroup L}
    {H : G → Subgroup G}
    {A : Set L}
    {tau : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h22 :
      Section2.Hypothesis2
        (Section4Scratch.subgroupImageSet L
          (Section4Scratch.primeDadeA0Set W1 W2 W A)) L H)
    (hTau :
      ∀ alpha : Section1.ClassFunction L,
        Section2.CFOn L
            (Section4Scratch.subgroupImageSet L
              (Section4Scratch.primeDadeA0Set W1 W2 W A)) alpha →
          tau alpha = Section2.dadeTransform H h22.subset_L alpha) :
    Section4Scratch.tau_maps_primeDadeA0_to_virtual_statement
      W1 W2 W A tau := by
  intro alpha hAlphaVirt hAlphaSupp
  have hAlphaCF := CFOn_of_supportedOn_subgroupImageSet
    (Section1.isVirtualCharacter_isClassFunction hAlphaVirt) hAlphaSupp
  rw [hTau alpha hAlphaCF]
  exact
    (Section2.theorem_2_6
      (Section4Scratch.subgroupImageSet L
        (Section4Scratch.primeDadeA0Set W1 W2 W A))
      L H h22 h22.subset_L).2 alpha ⟨hAlphaVirt, hAlphaCF.2⟩


private theorem one_not_mem_dadeSupport_of_hypothesis2
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h22 : Section2.Hypothesis2 A L H) :
    (1 : G) ∉ Section2.dadeSupport A H := by
  intro hmem
  rcases hmem with ⟨a, ha, h0, hh0, hconj⟩
  rcases hconj with ⟨x, hx⟩
  have hprod : a * h0 = 1 := by
    simpa [Section2.conjBy] using hx.symm
  have haH : a ∈ H a := by
    have hhInv : h0⁻¹ ∈ H a := (H a).inv_mem hh0
    have ha_eq : a = h0⁻¹ := by
      calc
        a = a * 1 := by simp
        _ = a * (h0 * h0⁻¹) := by simp
        _ = (a * h0) * h0⁻¹ := by simp [mul_assoc]
        _ = 1 * h0⁻¹ := by rw [hprod]
        _ = h0⁻¹ := by simp
    simpa [ha_eq] using hhInv
  have haCent : a ∈ Section2.centralizerIn L a := by
    refine ⟨h22.subset_L a ha, ?_⟩
    change a ∈ Subgroup.centralizer ({a} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    simp
  have haInf : a ∈ H a ⊓ Section2.centralizerIn L a := ⟨haH, haCent⟩
  have haBot : a ∈ (⊥ : Subgroup G) := by
    simpa [(h22.centralizer_eq_product ha).inf_eq_bot] using haInf
  exact h22.subset_punctured a ha (by simpa using haBot)


public theorem dadeTransform_supportedOn_punctured_of_hypothesis2
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h22 : Section2.Hypothesis2 A L H)
    (α : Section1.ClassFunction L) :
    Section1.supportedOn
      (Section2.dadeTransform H h22.subset_L α)
      Section4Scratch.puncturedSet := by
  rw [Section1.supportedOn_iff]
  intro g hgpunct
  have hg : g = 1 := by simpa [Section4Scratch.puncturedSet] using hgpunct
  rw [hg]
  exact Section2.dadeTransform_eq_zero_of_not_mem_support
    H h22.subset_L α
    (one_not_mem_dadeSupport_of_hypothesis2 h22)

/-- Repackage punctured target support on the exact prime-Dade carrier. -/
public theorem tau_maps_primeDadeA0_to_punctured_of_hypothesis2_dadeTransform
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} [Finite L]
    {W1 W2 W : Subgroup L}
    {H : G → Subgroup G}
    {A : Set L}
    {tau : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h22 :
      Section2.Hypothesis2
        (Section4Scratch.subgroupImageSet L
          (Section4Scratch.primeDadeA0Set W1 W2 W A)) L H)
    (hTau :
      ∀ alpha : Section1.ClassFunction L,
        Section2.CFOn L
            (Section4Scratch.subgroupImageSet L
              (Section4Scratch.primeDadeA0Set W1 W2 W A)) alpha →
          tau alpha = Section2.dadeTransform H h22.subset_L alpha) :
    Section4Scratch.tau_maps_primeDadeA0_to_punctured_statement
      W1 W2 W A tau := by
  intro alpha hAlphaClass hAlphaSupp
  have hAlphaCF := CFOn_of_supportedOn_subgroupImageSet hAlphaClass hAlphaSupp
  rw [hTau alpha hAlphaCF]
  exact dadeTransform_supportedOn_punctured_of_hypothesis2 h22 alpha


public theorem dadeTransformLinear_apply_of_subset_eq
    {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (hAL hAL' : ∀ a ∈ A, a ∈ L)
    (α : Section1.ClassFunction L) :
    Section2.dadeTransformLinear H hAL α =
      Section2.dadeTransform H hAL' α := by
  have hEq : hAL = hAL' := by
    funext a ha
    exact Subsingleton.elim (hAL a ha) (hAL' a ha)
  subst hEq
  exact Section2.dadeTransformLinear_apply H hAL α

public theorem dadeTransformLinear_apply_of_carrier_eq
    {G : Type u} [Group G]
    {A B : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (hAB : A = B)
    (hAL : ∀ a ∈ A, a ∈ L)
    (hBL : ∀ b ∈ B, b ∈ L)
    (α : Section1.ClassFunction L) :
    Section2.dadeTransformLinear H hAL α =
      Section2.dadeTransform H hBL α := by
  subst B
  exact dadeTransformLinear_apply_of_subset_eq hAL hBL α


@[expose] public def section8Hypothesis52FullData_of_supportedHypothesis
    {G : Type u} [Group G] [Finite G]
    {M Ms W1 W2 : Subgroup G}
    {A : Set G}
    {W : Subgroup M}
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J → Section1.ClassFunction W}
    {sigmaM : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction M}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction M}
    {xChar : J → Section1.ClassFunction (derivedSubgroup M)}
    {deltaSign : J → ℂ}
    {tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {H_A H_A0 : G → Subgroup G}
    (hCyclicA0 :
      Section2.hypothesis_2_2_statement
        (Section4Scratch.subgroupImageSet M (section8CyclicA0Set M W1 W2 A))
        M H_A0)
    (hTauCyclicA0 :
      ∀ α : Section1.ClassFunction M,
        Section2.CFOn M
            (Section4Scratch.subgroupImageSet M (section8CyclicA0Set M W1 W2 A))
            α →
          tau α =
            Section2.dadeTransform H_A0 hCyclicA0.subset_L α)
    (hSigmaAgreeCyclicTI :
      ∀ α : Section1.ClassFunction W, Section1.IsClassFunction α →
        ∀ x : M, ∀ hx : x ∈
          Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M) W,
            sigma α (x : G) =
              α ⟨x, Section3.cyclicTISet_subset
                (W1.subgroupOf M) (W2.subgroupOf M) W hx⟩)
    (hW : W = (W1 ⊔ W2).subgroupOf M)
    (hFull :
      Section4Scratch.hypothesis_4_6_supported_statement M
        (derivedSubgroup M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        W
        (Ms.subgroupOf M)
        (section8SubgroupSetPreimage M A)
        i0 j0 omega sigmaM sigma piChar xChar deltaSign tau H_A) :
    section8Hypothesis52FullData M Ms W1 W2 A :=
  { W := W
    I := I
    J := J
    instFintypeI := inferInstance
    instFintypeJ := inferInstance
    instDecidableEqI := inferInstance
    instDecidableEqJ := inferInstance
    i0 := i0
    j0 := j0
    omega := omega
    sigmaM := sigmaM
    sigma := sigma
    piChar := piChar
    xChar := xChar
    deltaSign := deltaSign
    tau := tau
    H_A := H_A
    H_A0 := H_A0
    cyclicA0Hypothesis := hCyclicA0
    tau_cyclicA0 := hTauCyclicA0
    sigma_agrees_cyclicTI := hSigmaAgreeCyclicTI
    W_eq := hW
    fullHypothesis := hFull }


/-- Source-level selected cyclic-TI value agreement for the Section 8
full `(5.2)` table.

This is the local `cycTIiso_restrict` input before the PF `(3.9)(a)`
uniqueness step: the selected ambient map `d52.sigma` agrees with the source
character on the cyclic-TI set of its own carrier. -/
public theorem section8Hypothesis52FullData_sigma_agrees_on_cyclicTI_source_data
    {G : Type u} [Group G] [Finite G]
    {M Ms W1 W2 : Subgroup G}
    {A : Set G}
    (d52 : section8Hypothesis52FullData M Ms W1 W2 A) :
    ∀ α : Section1.ClassFunction d52.W,
      Section1.IsClassFunction α →
        ∀ x : M, ∀ hx : x ∈
          Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M) d52.W,
            d52.sigma α (x : G) =
              α ⟨x, Section3.cyclicTISet_subset
                (W1.subgroupOf M) (W2.subgroupOf M) d52.W hx⟩ := by
  exact d52.sigma_agrees_cyclicTI

/-- Two Section `(3.3)` tables on the same ordered pair of cyclic factors
differ only by independent reindexings of their two axes. -/
public theorem omegaSystem_reindex_equiv
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J I' J' : Type*}
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    [DecidableEq I] [DecidableEq J] [DecidableEq I'] [DecidableEq J']
    {i0 : I} {j0 : J} {i0' : I'} {j0' : J'}
    {omega : I -> J -> Section1.ClassFunction W}
    {omega' : I' -> J' -> Section1.ClassFunction W}
    (hOmega : Section3.OmegaSystem W1 W2 W I J i0 j0 omega)
    (hOmega' : Section3.OmegaSystem W1 W2 W I' J' i0' j0' omega') :
    exists eI : I ≃ I', exists eJ : J ≃ J',
      forall i j, omega i j = omega' (eI i) (eJ j) := by
  classical
  let fI : I -> I' := fun i =>
    Classical.choose ((hOmega'.left_kernel_exact (omega i j0)
      (hOmega.irreducible i j0)).1 (hOmega.left_kernel i))
  have hfI : forall i,
      omega i j0 = omega' (fI i) j0' := fun i =>
    Classical.choose_spec ((hOmega'.left_kernel_exact (omega i j0)
      (hOmega.irreducible i j0)).1 (hOmega.left_kernel i))
  have hfI_injective : Function.Injective fI := by
    intro i k hik
    have hentry : omega i j0 = omega k j0 := by
      rw [hfI i, hfI k, hik]
    exact (hOmega.pairwise_eq hentry).1
  have hfI_bijective : Function.Bijective fI :=
    (Fintype.bijective_iff_injective_and_card fI).2
      ⟨hfI_injective, hOmega.card_left.trans hOmega'.card_left.symm⟩
  let eI : I ≃ I' := Equiv.ofBijective fI hfI_bijective
  let fJ : J -> J' := fun j =>
    Classical.choose ((hOmega'.right_kernel_exact (omega i0 j)
      (hOmega.irreducible i0 j)).1 (hOmega.right_kernel j))
  have hfJ : forall j,
      omega i0 j = omega' i0' (fJ j) := fun j =>
    Classical.choose_spec ((hOmega'.right_kernel_exact (omega i0 j)
      (hOmega.irreducible i0 j)).1 (hOmega.right_kernel j))
  have hfJ_injective : Function.Injective fJ := by
    intro j k hjk
    have hentry : omega i0 j = omega i0 k := by
      rw [hfJ j, hfJ k, hjk]
    exact (hOmega.pairwise_eq hentry).2
  have hfJ_bijective : Function.Bijective fJ :=
    (Fintype.bijective_iff_injective_and_card fJ).2
      ⟨hfJ_injective, hOmega.card_right.trans hOmega'.card_right.symm⟩
  let eJ : J ≃ J' := Equiv.ofBijective fJ hfJ_bijective
  refine ⟨eI, eJ, ?_⟩
  intro i j
  ext x
  calc
    omega i j x = omega i j0 x * omega i0 j x := hOmega.product i j x
    _ = omega' (eI i) j0' x * omega' i0' (eJ j) x := by
      change omega i j0 x * omega i0 j x =
        omega' (fI i) j0' x * omega' i0' (fJ j) x
      rw [hfI i, hfJ j]
    _ = omega' (eI i) (eJ j) x := (hOmega'.product (eI i) (eJ j) x).symm

/-- PF `(10.7)`'s source-level column-to-row identification after
`FTtypeP_coherent_TIred` and `cycTIisoC`.

This remains a source boundary: the external and selected tables must be the
specific transposed tables chosen by the Type-P pair construction. Mere
entrywise coverage is not sufficient, so downstream callers must eventually
thread that source alignment explicitly. -/
public theorem section8_FTtypeP_coherent_TIred_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M Ms W1 W2 : Subgroup G}
    {A : Set G}
    (d52 : section8Hypothesis52FullData M Ms W1 W2 A)
    {L : Type u} [Group L] [Finite L]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    {Wsrc : Subgroup L}
    (e : Wsrc ≃* d52.W)
    (ωsrc : I → J → Section1.ClassFunction Wsrc)
    (_hRowAlignment :
      letI : Fintype d52.I := d52.instFintypeI
      letI : Fintype d52.J := d52.instFintypeJ
      ∀ k : d52.J, ∃ r : I, ∃ reindex : d52.I ≃ J,
        ∀ i : d52.I,
          d52.omega i k =
            Section6.theorem_6_8_transportClassFunction e
              (ωsrc r (reindex i)))
    {T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ν : Section1.ClassFunction M}
    (lam : Section1.ClassFunction M)
    (_hlam_irreducible : Section1.IsIrreducibleCharacterOnGroup lam)
    (_hPreimage :
      letI : Fintype d52.I := d52.instFintypeI
      letI : Fintype d52.J := d52.instFintypeJ
      ∃ k j : d52.J,
        k ≠ d52.j0 ∧
          Section4Scratch.piColumn d52.piChar k = ν ∧
            Section1.conjugateCharacter
                (Section4Scratch.piColumn d52.piChar k) =
              Section4Scratch.piColumn d52.piChar j)
    (_hImage :
      letI : Fintype d52.I := d52.instFintypeI
      ∃ k : d52.J, ∃ ε : ℤ,
        (ε = 1 ∨ ε = -1) ∧
          T ν = (ε : ℂ) • (∑ i : d52.I, d52.sigma (d52.omega i k)))
    (T2 : Finset (Section1.ClassFunction M))
    (_hcohT2 : Section6.coherentFamily T2 T)
    (_hlamT2 : lam ∈ T2)
    (_hνT2 : ν ∈ T2) :
    ∃ r : I, ∃ ε : ℤ,
      (ε = 1 ∨ ε = -1) ∧
        T ν =
          (ε : ℂ) •
            (∑ j : J,
              d52.sigma
                (Section6.theorem_6_8_transportClassFunction e (ωsrc r j))) := by
  classical
  letI : Fintype d52.I := d52.instFintypeI
  letI : Fintype d52.J := d52.instFintypeJ
  letI : DecidableEq d52.I := d52.instDecidableEqI
  letI : DecidableEq d52.J := d52.instDecidableEqJ
  rcases _hImage with ⟨k, ε, hε, hTν⟩
  rcases _hRowAlignment k with ⟨r, reindex, hrowEntry⟩
  refine ⟨r, ε, hε, ?_⟩
  have hrow :
      (∑ i : d52.I, d52.sigma (d52.omega i k)) =
        ∑ j : J,
          d52.sigma
            (Section6.theorem_6_8_transportClassFunction e (ωsrc r j)) := by
    calc
      (∑ i : d52.I, d52.sigma (d52.omega i k)) =
          ∑ i : d52.I,
            d52.sigma
              (Section6.theorem_6_8_transportClassFunction e
                (ωsrc r (reindex i))) := by
            exact Finset.sum_congr rfl
              (fun i _hi => congrArg d52.sigma (hrowEntry i))
      _ = ∑ j : J,
            d52.sigma
              (Section6.theorem_6_8_transportClassFunction e (ωsrc r j)) := by
            exact Fintype.sum_equiv reindex
              (fun i : d52.I =>
                d52.sigma
                  (Section6.theorem_6_8_transportClassFunction e
                    (ωsrc r (reindex i))))
              (fun j : J =>
                d52.sigma
                  (Section6.theorem_6_8_transportClassFunction e (ωsrc r j)))
              (fun _i => rfl)
  rw [hTν, hrow]


public structure TypePBotTypeVPrimeDadeSupportedPackage
    {G : Type u} [Group G] [Finite G]
    (M W1 W2 : Subgroup G) (A : Set G)
    (W : Subgroup M)
    (sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) :
    Type (u + 1) where
  H_A0 : G → Subgroup G
  h22CyclicA0 :
    Section2.hypothesis_2_2_statement
      (Section4Scratch.subgroupImageSet M
        (section8CyclicA0Set M W1 W2 A)) M H_A0
  tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G
  tau_cyclicA0 :
    ∀ α : Section1.ClassFunction M,
      Section2.CFOn M
          (Section4Scratch.subgroupImageSet M
            (section8CyclicA0Set M W1 W2 A)) α →
        tau α = Section2.dadeTransform H_A0 h22CyclicA0.subset_L α
  tau_agrees_cyclic :
    Section4Scratch.tau_agrees_on_cyclicTI_induced_statement
      (W1.subgroupOf M) (W2.subgroupOf M) W sigma tau
  tau_isometry_on_primeDadeA0 :
    Section4Scratch.tau_isometry_on_primeDadeA0_statement
      (W1.subgroupOf M) (W2.subgroupOf M) W
      (section8SubgroupSetPreimage M A) tau
  tau_maps_primeDadeA0_to_punctured :
    Section4Scratch.tau_maps_primeDadeA0_to_punctured_statement
      (W1.subgroupOf M) (W2.subgroupOf M) W
      (section8SubgroupSetPreimage M A) tau
  tau_maps_primeDadeA0_to_virtual :
    Section4Scratch.tau_maps_primeDadeA0_to_virtual_statement
      (W1.subgroupOf M) (W2.subgroupOf M) W
      (section8SubgroupSetPreimage M A) tau


public theorem dadeTransform_eq_self_on_carrier_source_data
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h22 : Section2.hypothesis_2_2_statement A L H)
    (α : Section1.ClassFunction L)
    (hα : Section2.CFOn L A α)
    {a : G} (ha : a ∈ A) :
    Section2.dadeTransform H h22.subset_L α a =
      α ⟨a, h22.subset_L a ha⟩ := by
  have hdef :
      (∀ ⦃g a h' : G⦄, (ha : a ∈ A) → h' ∈ H a →
          Section2.conjugateIn g (a * h') →
            Section2.dadeTransform H h22.subset_L α g =
              α ⟨a, h22.subset_L a ha⟩) ∧
        ∀ g : G, g ∉ Section2.dadeSupport A H →
          Section2.dadeTransform H h22.subset_L α g = 0 :=
    Section2.definition_2_5 A L H h22 h22.subset_L α hα
  have hcoset :
      ∀ ⦃g a h' : G⦄, (ha : a ∈ A) → h' ∈ H a →
        Section2.conjugateIn g (a * h') →
          Section2.dadeTransform H h22.subset_L α g =
            α ⟨a, h22.subset_L a ha⟩ :=
    hdef.left
  have hvalue :=
    hcoset (g := a) (a := a) (h' := 1) ha (H a).one_mem
      (by
        refine ⟨1, ?_⟩
        simp [Section2.conjBy])
  simpa using hvalue


private theorem scalarProduct_irreducible_self_primeDade_pf8
    {G : Type*} [Group G] [Finite G]
    {chi : Section1.ClassFunction G}
    (hchi : Section1.IsIrreducibleCharacterOnGroup chi) :
    Section1.scalarProduct G chi chi = 1 := by
  rcases hchi with ⟨n, rho, hirr, rfl⟩
  exact Section1.scalarProduct_representation_char_self rho hirr

private theorem scalarProduct_irreducible_ne_primeDade_pf8
    {G : Type*} [Group G] [Finite G]
    {phi psi : Section1.ClassFunction G}
    (hphi : Section1.IsIrreducibleCharacterOnGroup phi)
    (hpsi : Section1.IsIrreducibleCharacterOnGroup psi)
    (hne : phi ≠ psi) :
    Section1.scalarProduct G phi psi = 0 := by
  rcases hphi with ⟨nphi, rphi, hirrphi, hphiChar⟩
  rcases hpsi with ⟨npsi, rpsi, hirrpsi, hpsiChar⟩
  exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
    phi psi rphi rpsi hphiChar hpsiChar hirrphi hirrpsi hne


public theorem theorem_4_8_primeDade
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    (K W1 W2 W H : Subgroup M)
    (A : Set M)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (omega : I → J → Section1.ClassFunction W)
    (sigmaM : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction M)
    (sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (piChar : I → J → Section1.ClassFunction M)
    (xChar : J → Section1.ClassFunction K)
    (deltaSign : J → ℂ)
    (tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    {sigmaImage :
      Section1.ClassFunction (Section4Scratch.subgroupImage M W) →ₗ[ℂ]
        Section1.ClassFunction G}
    (h31Image :
      Section3.hypothesis_3_1_statement
        (Section4Scratch.subgroupImage M W1)
        (Section4Scratch.subgroupImage M W2)
        (Section4Scratch.subgroupImage M W))
    (hSigmaImage :
      Section3.theorem_3_2_map_statement
        (Section4Scratch.subgroupImage M W1)
        (Section4Scratch.subgroupImage M W2)
        (Section4Scratch.subgroupImage M W) sigmaImage)
    (hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M W)).toLinearMap)
    {H_A0 : G → Subgroup G}
    (h22 :
      Section2.Hypothesis2
        (Section4Scratch.subgroupImageSet M
          (Section4Scratch.primeDadeA0Set W1 W2 W A)) M H_A0)
    (hTau :
      ∀ alpha : Section1.ClassFunction M,
        Section2.CFOn M
            (Section4Scratch.subgroupImageSet M
              (Section4Scratch.primeDadeA0Set W1 W2 W A)) alpha →
          tau alpha = Section2.dadeTransform H_A0 h22.subset_L alpha)
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (hOmega : Section3.notation_3_3_statement W1 W2 W I J i0 j0 omega)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 omega sigmaM piChar deltaSign hOmega)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign omega)
    (h43d : Section4.theorem_4_3_d_statement W1 I J piChar deltaSign)
    (h47 : Section4Scratch.theorem_4_7_statement K H A) :
    Section4Scratch.theorem_4_8_statement
      W2 W A j0 omega sigma piChar deltaSign tau := by
  classical
  have h43bData := h43b
  rcases h43bData with
    ⟨_hSigmaM, hsign, hirr, hdistinct, _hInd, _hSigmaEntries⟩
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
    Section4Scratch.hypothesis_3_1_of_hypothesis_4_6_pf45 h46
  let e := subgroupImageEquiv M W
  let E := Section1.classFunctionLinearEquivOfMulEquiv e
  let omegaImage : I → J →
      Section1.ClassFunction (Section4Scratch.subgroupImage M W) :=
    fun i j => E (omega i j)
  have hOmegaImage :
      Section3.notation_3_3_statement
        (Section4Scratch.subgroupImage M W1)
        (Section4Scratch.subgroupImage M W2)
        (Section4Scratch.subgroupImage M W)
        I J i0 j0 omegaImage := by
    simpa [omegaImage, E, e] using
      notation_3_3_statement_of_subgroupImageEquiv (M := M) hOmega
  have hTauIso :=
    tau_isometry_on_primeDadeA0_of_hypothesis2_dadeTransform h22 hTau
  have hTauVirt :=
    tau_maps_primeDadeA0_to_virtual_of_hypothesis2_dadeTransform h22 hTau
  intro i j k hj0 hk0 hDegree
  have hSupportExact :
      Section1.supportedOn (piChar i j - piChar i k)
        (Section4Scratch.primeDadeA0Set W1 W2 W A) :=
    Section4Scratch.supportedOn_diff_primeDadeA0_of_equal_degree_pf45
      K W1 W2 W H A i0 j0 omega sigmaM piChar xChar deltaSign
      h46 h45a hOmega h43b h43c h43d h47 hj0 hk0 hDegree
  have hSignEq : deltaSign j = deltaSign k :=
    Section4Scratch.deltaSign_eq_of_equal_degree_pf45
      W1 W2 W piChar deltaSign h31 hsign h43d hDegree
  have hSupportLarge :
      Section1.supportedOn (piChar i j - piChar i k)
        (Section4Scratch.a0Set W2 W A) := by
    rw [Section1.supportedOn_iff] at hSupportExact ⊢
    intro x hxLarge
    exact hSupportExact x (fun hxExact => hxLarge
      (Section4Scratch.primeDadeA0Set_subset_a0Set W1 W2 W A hxExact))
  refine ⟨hSupportLarge, hSignEq, ?_⟩
  by_cases hjk : j = k
  · subst k
    simp
  let alpha : Section1.ClassFunction M := piChar i j - piChar i k
  let phi : Section1.ClassFunction G := tau alpha
  have hAlphaVirt : Theory.Character.IsVirtualCharacter alpha := by
    exact Section3.isVirtualCharacter_sub
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hirr i j))
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hirr i k))
  have hAlphaClass : Section1.IsClassFunction alpha :=
    Section1.isVirtualCharacter_isClassFunction hAlphaVirt
  have hAlphaSupp : Section1.supportedOn alpha
      (Section4Scratch.primeDadeA0Set W1 W2 W A) := by
    simpa [alpha] using hSupportExact
  have hAlphaCF := CFOn_of_supportedOn_subgroupImageSet hAlphaClass hAlphaSupp
  have hPhiVirt : Theory.Character.IsVirtualCharacter phi := by
    dsimp [phi]
    exact hTauVirt alpha hAlphaVirt hAlphaSupp
  have hPiNe : piChar i j ≠ piChar i k := by
    apply hdistinct (i, j) (i, k)
    simp [hjk]
  have hPiNe' : piChar i k ≠ piChar i j := hPiNe.symm
  have hAlphaNorm : Section1.scalarProduct M alpha alpha = 2 := by
    dsimp [alpha]
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right,
      scalarProduct_irreducible_self_primeDade_pf8 (hirr i j),
      scalarProduct_irreducible_ne_primeDade_pf8 (hirr i j) (hirr i k) hPiNe,
      scalarProduct_irreducible_ne_primeDade_pf8 (hirr i k) (hirr i j) hPiNe',
      scalarProduct_irreducible_self_primeDade_pf8 (hirr i k)]
    norm_num
  have hPhiNorm : Section1.scalarProduct G phi phi = 2 := by
    dsimp [phi]
    exact (hTauIso alpha alpha hAlphaClass hAlphaClass hAlphaSupp hAlphaSupp).trans
      hAlphaNorm
  have hDeltaNorm : Complex.normSq (deltaSign j) = 1 := by
    rcases hsign j with h | h <;> simp [h]
  have hLocalCyclic_of_ambient
      {x : G}
      (hx : x ∈ Section3.cyclicTISet
        (Section4Scratch.subgroupImage M W1)
        (Section4Scratch.subgroupImage M W2)
        (Section4Scratch.subgroupImage M W)) :
      let xImage : Section4Scratch.subgroupImage M W := ⟨x, hx.1⟩
      let xW : W := e.symm xImage
      ((xW : W) : M) ∈ Section3.cyclicTISet W1 W2 W := by
    intro xImage xW
    rw [Section3.cyclicTISet_mem_iff] at hx ⊢
    refine ⟨xW.2, ?_, ?_⟩
    · intro hxW1
      have hxW1' : xW ∈ W1.subgroupOf W := hxW1
      have hImage := subgroupImageEquiv_apply_mem_subgroupOf
        (M := M) (S := W1) (W := W) hxW1'
      have hEq : e xW = xImage := e.apply_symm_apply xImage
      change (((e xW : Section4Scratch.subgroupImage M W) : G) ∈
        Section4Scratch.subgroupImage M W1) at hImage
      have hCoe : ((e xW : Section4Scratch.subgroupImage M W) : G) = x := by
        rw [hEq]
      rw [hCoe] at hImage
      exact hx.2.1 hImage
    · intro hxW2
      have hxW2' : xW ∈ W2.subgroupOf W := hxW2
      have hImage := subgroupImageEquiv_apply_mem_subgroupOf
        (M := M) (S := W2) (W := W) hxW2'
      have hEq : e xW = xImage := e.apply_symm_apply xImage
      change (((e xW : Section4Scratch.subgroupImage M W) : G) ∈
        Section4Scratch.subgroupImage M W2) at hImage
      have hCoe : ((e xW : Section4Scratch.subgroupImage M W) : G) = x := by
        rw [hEq]
      rw [hCoe] at hImage
      exact hx.2.2 hImage
  have hAgreement : ∀ x : G,
      ∀ hx : x ∈ Section3.cyclicTISet
        (Section4Scratch.subgroupImage M W1)
        (Section4Scratch.subgroupImage M W2)
        (Section4Scratch.subgroupImage M W),
      phi x =
        (deltaSign j •
          (sigmaImage (omegaImage i j) - sigmaImage (omegaImage i k))) x := by
    intro x hx
    let xImage : Section4Scratch.subgroupImage M W := ⟨x, hx.1⟩
    let xW : W := e.symm xImage
    have hxLocal : ((xW : W) : M) ∈ Section3.cyclicTISet W1 W2 W :=
      hLocalCyclic_of_ambient hx
    have hxM : x ∈ M := by
      rcases hx.1 with ⟨w, hw, hwx⟩
      rw [← hwx]
      exact w.2
    let xM : M := ⟨x, hxM⟩
    have hxMEq : xM = (xW : M) := by
      apply M.subtype_injective
      exact (subgroupImageEquiv_symm_apply_coe M W xImage).symm
    have hxLocalData :=
      (Section3.cyclicTISet_mem_iff W1 W2 W).1 hxLocal
    have hxMW : xM ∈ W := by
      simp [hxMEq]
    have hxMW2 : xM ∉ W2 := by
      intro hxW2
      exact hxLocalData.2.2 (by simpa [hxMEq] using hxW2)
    have hxLocalM : xM ∈ Section3.cyclicTISet W1 W2 W := by
      apply (Section3.cyclicTISet_mem_iff W1 W2 W).2
      exact ⟨hxMW, by simpa [hxMEq] using hxLocalData.2.1, hxMW2⟩
    have hxConj : xM ∈ Section2.conjugateSet
        (Section3.cyclicTISet W1 W2 W) := by
      exact ⟨xM, hxLocalM, ⟨1, by simp [Section2.conjBy]⟩⟩
    have hxCarrier : x ∈ Section4Scratch.subgroupImageSet M
        (Section4Scratch.primeDadeA0Set W1 W2 W A) :=
      ⟨xM, Or.inr hxConj, rfl⟩
    have hDade := dadeTransform_eq_self_on_carrier_source_data
      h22 alpha hAlphaCF hxCarrier
    have hDade' :
        Section2.dadeTransform H_A0 h22.subset_L alpha x = alpha xM := by
      simpa [xM] using hDade
    have hPiJ := h43c.1 i j xM ⟨hxMW, hxMW2⟩
    have hPiK := h43c.1 i k xM ⟨hxMW, hxMW2⟩
    have hxArg : (⟨xM, hxMW⟩ : W) = xW := by
      apply Subtype.ext
      exact hxMEq
    have hSigmaJ : sigmaImage (omegaImage i j) x = omega i j xW := by
      have hAgree := hSigmaImage.2.2.2.2.2.1
        (omegaImage i j) (hOmegaImage.is_class i j) x hx
      calc
        sigmaImage (omegaImage i j) x =
            omegaImage i j
              ⟨x, Section3.cyclicTISet_subset
                (Section4Scratch.subgroupImage M W1)
                (Section4Scratch.subgroupImage M W2)
                (Section4Scratch.subgroupImage M W) hx⟩ := hAgree
        _ = omega i j xW := by
          change omega i j
              (e.symm
                ⟨x, Section3.cyclicTISet_subset
                  (Section4Scratch.subgroupImage M W1)
                  (Section4Scratch.subgroupImage M W2)
                  (Section4Scratch.subgroupImage M W) hx⟩) = omega i j xW
          congr 1
    have hSigmaK : sigmaImage (omegaImage i k) x = omega i k xW := by
      have hAgree := hSigmaImage.2.2.2.2.2.1
        (omegaImage i k) (hOmegaImage.is_class i k) x hx
      calc
        sigmaImage (omegaImage i k) x =
            omegaImage i k
              ⟨x, Section3.cyclicTISet_subset
                (Section4Scratch.subgroupImage M W1)
                (Section4Scratch.subgroupImage M W2)
                (Section4Scratch.subgroupImage M W) hx⟩ := hAgree
        _ = omega i k xW := by
          change omega i k
              (e.symm
                ⟨x, Section3.cyclicTISet_subset
                  (Section4Scratch.subgroupImage M W1)
                  (Section4Scratch.subgroupImage M W2)
                  (Section4Scratch.subgroupImage M W) hx⟩) = omega i k xW
          congr 1
    calc
      phi x = Section2.dadeTransform H_A0 h22.subset_L alpha x := by
        dsimp [phi]
        rw [hTau alpha hAlphaCF]
      _ = alpha xM := hDade'
      _ = deltaSign j * (omega i j xW - omega i k xW) := by
        dsimp [alpha]
        rw [hPiJ, hPiK, hSignEq, hxArg]
        ring
      _ = deltaSign j *
          (sigmaImage (omegaImage i j) x - sigmaImage (omegaImage i k) x) := by
        rw [hSigmaJ, hSigmaK]
      _ = (deltaSign j •
          (sigmaImage (omegaImage i j) - sigmaImage (omegaImage i k))) x := by
        rfl
  have hEq := Section3.eq_signed_sub_cTIiso
    h31Image hOmegaImage hSigmaImage hPhiVirt hPhiNorm hDeltaNorm i
    hjk
    hAgreement
  have hSigmaEntry : ∀ p q, sigmaImage (omegaImage p q) = sigma (omega p q) := by
    intro p q
    rw [hSigmaDef]
    rfl
  rw [hSigmaEntry i j, hSigmaEntry i k] at hEq
  simpa [phi, alpha] using hEq


public theorem typeII_primeDade_cyclic_dade_id_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms U W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (hP : typePDefinitionData M MF U W1 W2)
    (_hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1 W2)
    (h46 :
      section8Hypothesis46Source M W1 W2 Ms A A0)
    {H_A0 : G → Subgroup G}
    {D tildeA tildeA0 tildeA1 : Set G}
    (_h14 :
      notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 H_A0)
    (_h22A0 :
      Section2.hypothesis_2_2_statement
        (Section4Scratch.subgroupImageSet M
          (section8CyclicA0Set M W1 W2 A)) M H_A0)
    {tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (_hTauCyclicA0 :
      ∀ α : Section1.ClassFunction M,
        Section2.CFOn M
            (Section4Scratch.subgroupImageSet M
              (section8CyclicA0Set M W1 W2 A)) α →
          tau α = Section2.dadeTransform H_A0 _h22A0.subset_L α)
    (α : Section1.ClassFunction ((W1 ⊔ W2).subgroupOf M))
    (hα :
      Section2.CFOn ((W1 ⊔ W2).subgroupOf M)
        (Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M)
          ((W1 ⊔ W2).subgroupOf M)) α) :
    Section2.dadeTransform H_A0 _h22A0.subset_L
        (Section1.inducedCF ((W1 ⊔ W2).subgroupOf M) α) =
      Section1.inducedCF
        (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
        (Section1.classFunctionLinearEquivOfMulEquiv
          (subgroupImageEquiv M ((W1 ⊔ W2).subgroupOf M)) α) := by
  -- `Dade` is pointwise the identity, and the ambient image of `W ≤ M`
  -- is transported by `subgroupImageEquiv`.
  let B : Set G :=
    Section4Scratch.subgroupImageSet M
      (Section2.conjugateSet
        (Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M)
          ((W1 ⊔ W2).subgroupOf M)))
  have hBsubA0 :
      B ⊆
        Section4Scratch.subgroupImageSet M
          (section8CyclicA0Set M W1 W2 A) := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, Or.inr hy, rfl⟩
  have hIndCFOn :
      Section2.CFOn M
        B
        (Section1.inducedCF ((W1 ⊔ W2).subgroupOf M) α) := by
    refine ⟨Section1.inducedCF_isClassFunction ((W1 ⊔ W2).subgroupOf M) α, ?_⟩
    intro x hx
    apply Section3.inducedCF_eq_zero_of_not_mem_conjugateSet_of_CFOn
    · exact hα
    · intro hxConj
      exact hx ⟨x, hxConj, rfl⟩
  have hA0image :
      Section4Scratch.subgroupImageSet M (section8CyclicA0Set M W1 W2 A) = A0 :=
    subgroupImageSet_section8CyclicA0Set_eq hP hWitness h46
  have hSignalizerTrivialOnB :
      ∀ ⦃a h0 : G⦄, a ∈ B → h0 ∈ H_A0 a → h0 = 1 := by
    intro a h0 haB hh0
    rcases _h14 with
      ⟨_hA1subA, _hAsubA0, hD, hRbot, _hUnique, _hRsource,
        _htildeA, _htildeA0, _htildeA1⟩
    have haA0 : a ∈ A0 := by
      simpa [hA0image] using hBsubA0 haB
    have haConj :
        a ∈ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G) := by
      rcases haB with ⟨y, hy, hy_eq⟩
      rcases hy with ⟨w, hw, hconj⟩
      rcases hconj with ⟨m, hm⟩
      refine ⟨(w : G), ?_, (m : G), m.property, ?_⟩
      · simpa [Section3.cyclicTISet, section16HatW, Subgroup.mem_subgroupOf] using hw
      · rw [← hy_eq]
        simpa [Section2.conjBy] using (congrArg Subtype.val hm).symm
    have hnotD : ¬ a ∈ D := by
      intro haD
      have haD0 : a ∈ section8DSet M A0 := by
        simpa [hD] using haD
      exact haD0.2
        (theorem_8_13_typeP_conjugates_hatW_centralizer_le
          (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
          hP a haConj)
    have hRbot_a : H_A0 a = ⊥ :=
      hRbot a ⟨haA0, hnotD⟩
    have h0bot : h0 ∈ (⊥ : Subgroup G) := by
      simpa [hRbot_a] using hh0
    exact Subgroup.mem_bot.mp h0bot
  calc
    Section2.dadeTransform H_A0 _h22A0.subset_L
        (Section1.inducedCF ((W1 ⊔ W2).subgroupOf M) α) =
        Section1.inducedCF M
          (Section1.inducedCF ((W1 ⊔ W2).subgroupOf M) α) := by
          exact
            Section2.dadeTransform_eq_inducedCF_of_trivial_signalizer_on_support
              (Section4Scratch.subgroupImageSet M
                (section8CyclicA0Set M W1 W2 A))
              B
              M H_A0 hBsubA0 _h22A0 _h22A0.subset_L
              (Section1.inducedCF ((W1 ⊔ W2).subgroupOf M) α)
              hIndCFOn
              hSignalizerTrivialOnB
    _ =
        Section1.inducedCF
          (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M ((W1 ⊔ W2).subgroupOf M)) α) := by
          exact inducedCF_subgroupImage_eq_inducedCF_trans M
            ((W1 ⊔ W2).subgroupOf M) α


public theorem typeII_primeDade_tau_agrees_cyclic_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms U W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (_hP : typePDefinitionData M MF U W1 W2)
    (_hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (_hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1 W2)
    (_h46 :
      section8Hypothesis46Source M W1 W2 Ms A A0)
    {H_A0 : G → Subgroup G}
    {D tildeA tildeA0 tildeA1 : Set G}
    (_h14 :
      notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 H_A0)
    (_h22A0 :
      Section2.hypothesis_2_2_statement
        (Section4Scratch.subgroupImageSet M
          (section8CyclicA0Set M W1 W2 A)) M H_A0)
    {tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (_hTauCyclicA0 :
      ∀ α : Section1.ClassFunction M,
        Section2.CFOn M
            (Section4Scratch.subgroupImageSet M
              (section8CyclicA0Set M W1 W2 A)) α →
          tau α = Section2.dadeTransform H_A0 _h22A0.subset_L α)
    {sigma :
      Section1.ClassFunction ((W1 ⊔ W2).subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction G}
    {sigmaImage :
      Section1.ClassFunction
          (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M)) →ₗ[ℂ]
        Section1.ClassFunction G}
    (_hSigmaImage :
      Section3.theorem_3_2_map_statement
        (Section4Scratch.subgroupImage M (W1.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
        sigmaImage)
    (_hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M ((W1 ⊔ W2).subgroupOf M))).toLinearMap) :
    Section4Scratch.tau_agrees_on_cyclicTI_induced_statement
      (W1.subgroupOf M) (W2.subgroupOf M) ((W1 ⊔ W2).subgroupOf M)
      sigma tau := by
  intro α hα
  have hIndCFOn :
      Section2.CFOn M
        (Section4Scratch.subgroupImageSet M
          (section8CyclicA0Set M W1 W2 A))
        (Section1.inducedCF ((W1 ⊔ W2).subgroupOf M) α) := by
    refine ⟨Section1.inducedCF_isClassFunction ((W1 ⊔ W2).subgroupOf M) α, ?_⟩
    intro x hx
    apply Section3.inducedCF_eq_zero_of_not_mem_conjugateSet_of_CFOn
    · exact hα
    · intro hxConj
      exact hx ⟨x, Or.inr hxConj, rfl⟩
  rw [_hTauCyclicA0 (Section1.inducedCF ((W1 ⊔ W2).subgroupOf M) α) hIndCFOn]
  -- characters, the selected cyclic `A₀` Dade transform is the ambient
  -- cyclic-TI isometry `sigma`.
  calc
    Section2.dadeTransform H_A0 _h22A0.subset_L
        (Section1.inducedCF ((W1 ⊔ W2).subgroupOf M) α) =
        Section1.inducedCF
          (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
            (Section1.classFunctionLinearEquivOfMulEquiv
              (subgroupImageEquiv M ((W1 ⊔ W2).subgroupOf M)) α) := by
          exact typeII_primeDade_cyclic_dade_id_source_data
            _hP _hNotation _hWitness _h46 _h14 _h22A0 _hTauCyclicA0 α hα
    _ = sigma α := by
      let e := subgroupImageEquiv M ((W1 ⊔ W2).subgroupOf M)
      let E := Section1.classFunctionLinearEquivOfMulEquiv e
      have hEα :
          Section2.CFOn (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
            (Section3.cyclicTISet
              (Section4Scratch.subgroupImage M (W1.subgroupOf M))
              (Section4Scratch.subgroupImage M (W2.subgroupOf M))
              (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M)))
            (E α) := by
        refine ⟨Section1.isClassFunction_classFunctionLinearEquivOfMulEquiv e hα.1, ?_⟩
        intro x hx
        have hxLocal :
            ((e.symm x : (W1 ⊔ W2).subgroupOf M) : M) ∉
              (Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M)
                ((W1 ⊔ W2).subgroupOf M)) := by
          change (((e.symm x : (W1 ⊔ W2).subgroupOf M) : M) ∈
            Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M)
              ((W1 ⊔ W2).subgroupOf M)) → False
          intro hxcyc
          have hxImage :
              ((e (e.symm x) :
                  Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M)) : G) ∈
                Section3.cyclicTISet
                  (Section4Scratch.subgroupImage M (W1.subgroupOf M))
                  (Section4Scratch.subgroupImage M (W2.subgroupOf M))
                  (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M)) :=
            subgroupImageEquiv_mem_cyclicTISet
              (M := M) (W1 := W1.subgroupOf M) (W2 := W2.subgroupOf M)
              (W := (W1 ⊔ W2).subgroupOf M) (x := e.symm x)
              (by simpa using hxcyc)
          exact hx (by simpa using hxImage)
        calc
          E α x = α (e.symm x) := by
            simpa [E] using Section1.classFunctionLinearEquivOfMulEquiv_apply e α x
          _ = 0 := hα.2 (e.symm x) hxLocal
      have hSigmaInd :
          sigmaImage (E α) = Section1.inducedCF
            (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M)) (E α) :=
        _hSigmaImage.2.2.1 (E α) hEα
      rw [_hSigmaDef]
      exact hSigmaInd.symm


public theorem typeII_primeDadeSupportedPackage_package_source_data_for_sigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms U W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (_hP : typePDefinitionData M MF U W1 W2)
    (_hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (_hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1 W2)
    (_h46 :
      section8Hypothesis46Source M W1 W2 Ms A A0)
    {H_A0 : G → Subgroup G}
    {D tildeA tildeA0 tildeA1 : Set G}
    (_h14 :
      notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 H_A0)
    (h22A0 :
      Section2.hypothesis_2_2_statement
        (Section4Scratch.subgroupImageSet M
          (section8CyclicA0Set M W1 W2 A)) M H_A0)
    {tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hTauCyclicA0 :
      ∀ α : Section1.ClassFunction M,
        Section2.CFOn M
            (Section4Scratch.subgroupImageSet M
              (section8CyclicA0Set M W1 W2 A)) α →
          tau α = Section2.dadeTransform H_A0 h22A0.subset_L α)
    {sigma :
      Section1.ClassFunction ((W1 ⊔ W2).subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction G}
    {sigmaImage :
      Section1.ClassFunction
          (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M)) →ₗ[ℂ]
        Section1.ClassFunction G}
    (_hSigmaImage :
      Section3.theorem_3_2_map_statement
        (Section4Scratch.subgroupImage M (W1.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
        sigmaImage)
    (_hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M ((W1 ⊔ W2).subgroupOf M))).toLinearMap) :
    ∃ pkg : TypePBotTypeVPrimeDadeSupportedPackage M W1 W2 A
        ((W1 ⊔ W2).subgroupOf M) sigma,
      pkg.H_A0 = H_A0 ∧ pkg.tau = tau ∧
        HEq pkg.h22CyclicA0 h22A0 := by
  have hTauCyclic :=
    typeII_primeDade_tau_agrees_cyclic_source_data
      _hP _hNotation _hWitness _h46 _h14 h22A0 hTauCyclicA0
      (sigma := sigma) _hSigmaImage _hSigmaDef
  refine ⟨{
    H_A0 := H_A0,
    h22CyclicA0 := h22A0,
    tau := tau,
    tau_cyclicA0 := hTauCyclicA0,
    tau_agrees_cyclic := hTauCyclic,
    tau_isometry_on_primeDadeA0 :=
      tau_isometry_on_primeDadeA0_of_hypothesis2_dadeTransform
        h22A0 hTauCyclicA0,
    tau_maps_primeDadeA0_to_punctured :=
      tau_maps_primeDadeA0_to_punctured_of_hypothesis2_dadeTransform
        h22A0 hTauCyclicA0,
    tau_maps_primeDadeA0_to_virtual :=
      tau_maps_primeDadeA0_to_virtual_of_hypothesis2_dadeTransform
        h22A0 hTauCyclicA0
  }, rfl, rfl, HEq.rfl⟩


public theorem typeP_bot_typeV_primeDadeSupportedPackage_source_data_for_sigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2')
    {sigma :
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction G}
    {sigmaImage :
      Section1.ClassFunction
          (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M)) →ₗ[ℂ]
        Section1.ClassFunction G}
    (_hSigmaImage :
      Section3.theorem_3_2_map_statement
        (Section4Scratch.subgroupImage M (W1'.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2'.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
        sigmaImage)
    (_hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M ((W1' ⊔ W2').subgroupOf M))).toLinearMap) :
    Nonempty
      (TypePBotTypeVPrimeDadeSupportedPackage M W1' W2' A
        ((W1' ⊔ W2').subgroupOf M) sigma) := by
  classical
  rcases notation_8_10_source_typeP_witness_typeV_context_of_typeP_bot
      hPbot hNotation hWitness with
    ⟨_hUbot, _hPbot', _hV, hMs, _hMF, _hAcentral, _hA1, _hA⟩
  have hNotationMF :
      notation_8_10_source_data M MF MF A A0 A1 := by
    simpa [hMs] using hNotation
  have hWitnessMF :
      notation_8_10_source_typeP_witness M MF MF A A0 A1 U W1' W2' := by
    simpa [hMs] using hWitness
  rcases theorem_8_15_hypothesis_4_6_source_of_typeP_bot_typeV_witness
      hPbot hNotation hWitness with
    ⟨h46MF, _h46Ms⟩
  rcases exists_hypothesis2_section8_cyclicA0_dade_transform_of_typeP_bot_typeV_witness
      hPbot hNotation hWitness with
    ⟨H_A0, tildeA, tildeA0, tildeA1, h14, _h22A, h22A0,
      tau, _hτdef, hτ⟩
  have hTauCyclicA0 :
      ∀ α : Section1.ClassFunction M,
        Section2.CFOn M
            (Section4Scratch.subgroupImageSet M
              (section8CyclicA0Set M W1' W2' A)) α →
          tau α = Section2.dadeTransform H_A0 h22A0.subset_L α := by
    intro α _hα
    exact hτ α
  rcases typeII_primeDadeSupportedPackage_package_source_data_for_sigma
      hWitness.1 hNotationMF hWitnessMF h46MF h14 h22A0 hTauCyclicA0
      (sigma := sigma) _hSigmaImage _hSigmaDef with
    ⟨pkg, _hH, _hτ, _h22⟩
  exact ⟨pkg⟩

public theorem typeII_section16ASet_subset_notation_A_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hTypeII : section16TypeII M MF)
    (hSrcII : typeIIDefinitionData M MF)
    (hP : typePDefinitionData M MF U W1 W2)
    (hNotation : notation_8_10_source_data M MF MF A A0 A1) :
    section16ASet M U ⊆ A := by
  classical
  have hMem : notation_8_10_source_membership_data M MF A :=
    notation_8_10_source_membership_data_of_source_data hNotation
  have hMF_eq : MF = section10Msigma M := by
    rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
      ⟨K, Uc, hKU15⟩
    have hKU : section16KUData M K Uc := by
      simpa [section16KUData] using hKU15
    have hProp :=
      proposition_16_1 (G := G) (M := M) (MF := MF)
        (K := K) (U := Uc) hM hMF hKU
    exact hProp.2.2.2.2.2.mpr (Or.inr (Or.inl hTypeII))
  have hASetCentralizer :
      section16ASet M U ⊆
        section8CentralizerUnion (ambientDerivedSubgroup M) MF := by
    rcases hP with
      ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hMcomp, _hUleD,
        _hUnil, _hW1norm, hUSplit, _hMFnotcyc, _hSecondLe, _hFittingEq,
        _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hcentralizer, _hhatW⟩
    intro a ha
    rcases ha with ⟨⟨_haM, hCentSigma_ne⟩, haProd, hane⟩
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hCentSigma_ne with
      ⟨c, hcne⟩
    let x : G := c
    have hxSigma : x ∈ section10Msigma M := c.property.1
    have hxMF : x ∈ MF := by
      simpa [hMF_eq] using hxSigma
    have hxne : x ≠ 1 := by
      intro hx
      exact hcne (Subtype.ext hx)
    have hxCentA : x ∈ Subgroup.centralizer ({a} : Set G) := c.property.2
    have haD : a ∈ ambientDerivedSubgroup M := by
      rcases Set.mem_mul.mp haProd with ⟨u, huU, s, hsSigma, hus⟩
      have hsMF : s ∈ MF := by
        simpa [hMF_eq] using hsSigma
      exact hus ▸ (ambientDerivedSubgroup M).mul_mem
        (hUSplit.2.1 huU) (hUSplit.1 hsMF)
    rw [section8CentralizerUnion]
    refine ⟨x, ⟨hxMF, hxne⟩, ⟨?_, hane⟩⟩
    have hcomm : Commute x a :=
      Subgroup.mem_centralizer_singleton_iff.mp hxCentA
    exact ⟨haD, by
      simpa [Subgroup.mem_centralizer_singleton_iff] using hcomm.symm.eq⟩
  intro x hx
  exact hMem.2 x hSrcII (hASetCentralizer hx)

public theorem typeII_section16ASet_subset_cyclicA0_image_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hTypeII : section16TypeII M MF)
    (hSrcII : typeIIDefinitionData M MF)
    (hP : typePDefinitionData M MF U W1 W2)
    (hNotation : notation_8_10_source_data M MF MF A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF MF A A0 A1 U W1 W2)
    (h46 : section8Hypothesis46Source M W1 W2 MF A A0) :
    section16ASet M U ⊆
      Section4Scratch.subgroupImageSet M (section8CyclicA0Set M W1 W2 A) := by
  intro x hx
  have hxA : x ∈ A :=
    typeII_section16ASet_subset_notation_A_source_data
      hM hMF hTypeII hSrcII hP hNotation hx
  have hxA0 : x ∈ A0 := h46.2.2 hxA
  have hA0image :
      Section4Scratch.subgroupImageSet M (section8CyclicA0Set M W1 W2 A) =
        A0 := by
    have hA0subM : A0 ⊆ (M : Set G) := by
      rcases hP with
        ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, _hMcomp, _hUleD,
          _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecondLe,
          _hFittingEq, _hFittingLeD, hW2leInf, _hW2cyc, _hW2ne,
          _hcentralizer, _hhatW⟩
      rcases hWitness with ⟨_hPw, _hTypes, hAeq, hA0eq, _hLate⟩
      have hA_subset_M : A ⊆ (M : Set G) := by
        intro y hy
        have hyA :
            y ∈ section8CentralizerUnion (ambientDerivedSubgroup M) MF := by
          simpa [hAeq] using hy
        rcases hyA with ⟨c, _hc, hyD, _hyne⟩
        exact section12_ambientDerivedSubgroup_le (G := G) (E := M) hyD.1
      have hW1M : W1 ≤ M := hW1hall.1
      have hW2M : W2 ≤ M := by
        intro y hy
        exact _hMFsource.1.1 ((hW2leInf hy).1)
      have hHatW_M : section16HatW W1 W2 ≤ M := by
        intro y hy
        exact (sup_le hW1M hW2M) hy.1
      intro y hy
      rw [hA0eq] at hy
      rcases hy with hyA | hyConj
      · exact hA_subset_M hyA
      · rcases hyConj with ⟨w, hw, m, hmM, hy_eq⟩
        rw [hy_eq]
        exact M.mul_mem (M.mul_mem hmM (hHatW_M hw)) (M.inv_mem hmM)
    rw [← h46.1]
    exact subgroupImageSet_section8SubgroupSetPreimage_eq hA0subM
  simpa [hA0image] using hxA0

public theorem typeII_section16ASet_le_setNormalizer_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (_hP : typePDefinitionData M MF U W1 W2) :
    U ≤ section10Msigma M →
    M ≤ Section2.setNormalizer (section16ASet M U) := by
  classical
  intro hUσ
  have hconj_mem :
      ∀ {m a : G}, m ∈ M → a ∈ section16ASet M U →
        m * a * m⁻¹ ∈ section16ASet M U := by
    intro m a hm ha
    rcases ha with ⟨_haHat, haProd, hane⟩
    rcases Set.mem_mul.mp haProd with ⟨u, huU, s, hsσ, rfl⟩
    have huσ : u ∈ section10Msigma M := hUσ huU
    have hprodσ : u * s ∈ section10Msigma M :=
      (section10Msigma M).mul_mem huσ hsσ
    have hmNormSigma : m ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
      section12_le_normalizer_msigma (M := M) hm
    have hconjσ : m * (u * s) * m⁻¹ ∈ section10Msigma M :=
      (Subgroup.mem_normalizer_iff.mp hmNormSigma (u * s)).1 hprodσ
    have hconjne : m * (u * s) * m⁻¹ ≠ 1 := by
      intro h
      exact hane (by
        have h' := congrArg (fun t : G => m⁻¹ * t * m) h
        simpa [mul_assoc] using h')
    exact section16_msigma_nonidentity_mem_ASet_public (G := G) hM hconjσ hconjne
  intro m hm
  change Section2.normalizesSet (section16ASet M U) m
  intro a
  constructor
  · intro ha
    have hback :
        m⁻¹ * (m * a * m⁻¹) * (m⁻¹)⁻¹ ∈ section16ASet M U :=
      hconj_mem (M.inv_mem hm) ha
    simpa [mul_assoc] using hback
  · intro ha
    exact hconj_mem hm ha


private theorem exactCharacterValueOrder_exists_dvd_of_characterValueOrder
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G} {b : ℕ}
    (hb : Section3.characterValueOrder χ b) :
    ∃ a : ℕ, a ∣ b ∧ Section3.exactCharacterValueOrder χ a := by
  classical
  letI := Fintype.ofFinite G
  let a : ℕ := (Finset.univ : Finset G).lcm (fun g => orderOf (χ g))
  have hadvd_b : a ∣ b := by
    dsimp [a]
    refine Finset.lcm_dvd ?_
    intro g _hg
    exact orderOf_dvd_of_pow_eq_one (hb.2 g)
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos hadvd_b hb.1
  refine ⟨a, hadvd_b, ?_⟩
  constructor
  · constructor
    · exact hapos
    · intro g
      have hdiv : orderOf (χ g) ∣ a := by
        dsimp [a]
        exact Finset.dvd_lcm (Finset.mem_univ g)
      exact (orderOf_dvd_iff_pow_eq_one).1 hdiv
  · intro c hc
    dsimp [a]
    refine Finset.lcm_dvd ?_
    intro g _hg
    exact orderOf_dvd_of_pow_eq_one (hc.2 g)

private theorem internalDirectProduct_left_subgroupOf_normal
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalDirectProduct C H K) :
    (H.subgroupOf C).Normal := by
  refine ⟨?_⟩
  intro y hyH x
  rcases h.mul_surjective (x : G) x.2 with ⟨h0, hh0, k0, hk0, hx⟩
  have hcomm : k0 * (y : G) = (y : G) * k0 :=
    (h.commute (y : G) hyH k0 hk0).symm
  change ((x : G) * (y : G) * (x : G)⁻¹) ∈ H
  rw [hx]
  have hmid : k0 * (y : G) * k0⁻¹ = (y : G) := by
    calc
      k0 * (y : G) * k0⁻¹ = (y : G) * k0 * k0⁻¹ := by
        rw [hcomm]
      _ = (y : G) := by simp [mul_assoc]
  have hcalc :
      h0 * k0 * (y : G) * (h0 * k0)⁻¹ =
        h0 * (y : G) * h0⁻¹ := by
    calc
      h0 * k0 * (y : G) * (h0 * k0)⁻¹ =
          h0 * (k0 * (y : G) * k0⁻¹) * h0⁻¹ := by
            simp [mul_assoc]
      _ = h0 * (y : G) * h0⁻¹ := by rw [hmid]
  rw [hcalc]
  exact H.mul_mem (H.mul_mem hh0 hyH) (H.inv_mem hh0)

private theorem internalDirectProduct_right_subgroupOf_normal
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalDirectProduct C H K) :
    (K.subgroupOf C).Normal :=
  internalDirectProduct_left_subgroupOf_normal (Section3.internalDirectProduct_swap h)

private theorem internalDirectProduct_left_relIndex_eq_card_right
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalDirectProduct C H K) :
    H.relIndex C = Nat.card K := by
  let hsemi : Section2.IsInternalSemidirectProduct C H K :=
    { left_le := h.left_le
      right_le := h.right_le
      right_normalizes_left := by
        intro k hk h0 hh0
        change k * h0 * k⁻¹ ∈ H
        have hcomm : k * h0 = h0 * k := (h.commute h0 hh0 k hk).symm
        rw [hcomm]
        simpa [mul_assoc] using hh0
      inf_eq_bot := h.inf_eq_bot
      mul_surjective := h.mul_surjective }
  exact Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi

private theorem quotientCharacterInflation_pow_natCard
    {G : Type u} [Group G] [Finite G]
    (H T : Subgroup G) [(H.subgroupOf T).Normal]
    (χ : T ⧸ H.subgroupOf T →* ℂˣ) (t : T) :
    (Section1.quotientCharacterInflation H T χ t) ^
      Nat.card (T ⧸ H.subgroupOf T) = 1 := by
  let q : T ⧸ H.subgroupOf T := t
  have hqpow : q ^ Nat.card (T ⧸ H.subgroupOf T) = 1 :=
    pow_card_eq_one' (x := q)
  have hpow : χ q ^ Nat.card (T ⧸ H.subgroupOf T) = 1 := by
    calc
      χ q ^ Nat.card (T ⧸ H.subgroupOf T) =
          χ (q ^ Nat.card (T ⧸ H.subgroupOf T)) := by
            rw [MonoidHom.map_pow]
      _ = 1 := by rw [hqpow, map_one]
  change ((χ q : ℂˣ) : ℂ) ^ Nat.card (T ⧸ H.subgroupOf T) = 1
  simpa using congrArg (fun z : ℂˣ => (z : ℂ)) hpow

private theorem characterValueOrder_of_leftKernel_internalDirectProduct
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (hIP : Section2.IsInternalDirectProduct W W1 W2)
    {θ : Section1.ClassFunction W}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθker : Section1.subgroupInKernel' θ (W2.subgroupOf W))
    (hθdeg : Section1.degree θ = 1) :
    Section3.characterValueOrder θ (Nat.card W1) := by
  classical
  haveI : (W2.subgroupOf W).Normal :=
    internalDirectProduct_right_subgroupOf_normal hIP
  rcases Section1.exists_quotientLinearCharacter_of_irreducible_degree_one_kernel
      W2 W hθirr hθker hθdeg with ⟨χ, hθ⟩
  have hidx : (W2.subgroupOf W).index = Nat.card W1 := by
    have hrel := internalDirectProduct_left_relIndex_eq_card_right
      (Section3.internalDirectProduct_swap hIP)
    simpa [Subgroup.relIndex] using hrel
  have hcardQ : Nat.card (W ⧸ W2.subgroupOf W) = Nat.card W1 := by
    simpa [Subgroup.index_eq_card] using hidx
  constructor
  · exact Nat.card_pos (α := W1)
  · intro w
    rw [hθ]
    simpa [hcardQ] using
      quotientCharacterInflation_pow_natCard W2 W χ w

private theorem star_eq_zpow_neg_one_of_root
    {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) :
    star z = z ^ (-1 : ℤ) := by
  have hnorm : ‖z‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hz hn.ne'
  calc
    star z = z⁻¹ := (Complex.inv_eq_conj hnorm).symm
    _ = z ^ (-1 : ℤ) := by simp

/-- The ambient cyclic-TI map selected in a supported Section `(4.6)` package
has the PF `(3.9)(b)` base-column Galois transitivity inherited from the
canonical Section `(3.2)` map on the ambient subgroup image.

Only the three fields needed to identify the selected map with that canonical
map are assumed: isometry, preservation of virtual characters, and agreement
on the cyclic-TI carrier. -/
public theorem baseColumn_galoisConjugate_of_subgroupImage_section3_fields
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {W1 W2 W : Subgroup M}
    {I : Type v} {J : Type w}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J → Section1.ClassFunction W}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (h31Image :
      Section3.hypothesis_3_1_statement
        (Section4Scratch.subgroupImage M W1)
        (Section4Scratch.subgroupImage M W2)
        (Section4Scratch.subgroupImage M W))
    (homega : Section3.notation_3_3_statement W1 W2 W I J i0 j0 omega)
    (hSigmaIso : Section3.IsCFLinearIsometry sigma)
    (hSigmaVirt : Section3.MapsVirtualCharacters sigma)
    (hSigmaAgree :
      ∀ alpha : Section1.ClassFunction W, Section1.IsClassFunction alpha →
        ∀ x : M, ∀ hx : x ∈ Section3.cyclicTISet W1 W2 W,
          sigma alpha (x : G) =
            alpha ⟨x, Section3.cyclicTISet_subset W1 W2 W hx⟩)
    (hW1prime : Nat.Prime (Nat.card W1))
    {i k : I} (hi : i ≠ i0) (hk : k ≠ i0) :
    ∃ gamma : Gal(ℂ/ℚ),
      Section3.cyclotomicGaloisAction (Nat.card G) gamma ∧
        sigma (omega i j0) =
          Section3.classFunctionGaloisConjugate gamma (sigma (omega k j0)) := by
  classical
  let e := subgroupImageEquiv M W
  let E := Section1.classFunctionLinearEquivOfMulEquiv e
  let omegaImage : I → J →
      Section1.ClassFunction (Section4Scratch.subgroupImage M W) :=
    fun r s => E (omega r s)
  have hOmegaImage :
      Section3.notation_3_3_statement
        (Section4Scratch.subgroupImage M W1)
        (Section4Scratch.subgroupImage M W2)
        (Section4Scratch.subgroupImage M W)
        I J i0 j0 omegaImage := by
    simpa [omegaImage, E, e] using
      notation_3_3_statement_of_subgroupImageEquiv
        (M := M) (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0) (omega := omega) homega
  rcases Section3.theorem_3_2_of_notation_3_3
      (Section4Scratch.subgroupImage M W1)
      (Section4Scratch.subgroupImage M W2)
      (Section4Scratch.subgroupImage M W)
      I J i0 j0 omegaImage h31Image hOmegaImage with
    ⟨sigmaImage, hSigmaImage⟩
  rcases Section3.pf35_data_of_theorem_3_2_map_statement
      hOmegaImage sigmaImage hSigmaImage with
    ⟨chi, horth, hsigned, h00, hInd, hSigmaOmega⟩
  have hSigmaImageEq : sigmaImage = Section3.sigmaOfPF35 omegaImage chi :=
    Section3.sigma_eq_sigmaOfPF35_of_sigma_eq_omega_pf39
      (W1 := Section4Scratch.subgroupImage M W1)
      (W2 := Section4Scratch.subgroupImage M W2)
      (W := Section4Scratch.subgroupImage M W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := omegaImage) (χ := chi) h31Image hOmegaImage hSigmaOmega
  have hSigmaEq :
      ∀ {eta : Section1.ClassFunction W},
        Section1.IsIrreducibleCharacterOnGroup eta →
          sigma eta = sigmaImage (E eta) := by
    intro eta heta
    have hetaClass : Section1.IsClassFunction eta :=
      Section1.isVirtualCharacter_isClassFunction
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup heta)
    have hSigmaEtaVirt : Theory.Character.IsVirtualCharacter (sigma eta) :=
      hSigmaVirt eta (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup heta)
    have hSigmaEtaSelf :
        Section1.scalarProduct G (sigma eta) (sigma eta) = 1 := by
      calc
        Section1.scalarProduct G (sigma eta) (sigma eta) =
            Section1.scalarProduct W eta eta :=
          hSigmaIso eta eta hetaClass hetaClass
        _ = 1 := Section1.scalarProduct_irreducibleCharacter_self heta
    have hSigmaEtaSigned : Section3.IsSignedIrreducibleCharacter (sigma eta) :=
      Section3.signed_irreducible_of_virtual_norm_one_pf39
        hSigmaEtaVirt hSigmaEtaSelf
    have hEetaIrr :
        Section1.IsIrreducibleCharacterOnGroup (E eta) :=
      Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
        e heta
    have hAgreeImage :
        ∀ x : G,
          ∀ hx : x ∈ Section3.cyclicTISet
            (Section4Scratch.subgroupImage M W1)
            (Section4Scratch.subgroupImage M W2)
            (Section4Scratch.subgroupImage M W),
            sigma eta x =
              E eta ⟨x, Section3.cyclicTISet_subset
                (Section4Scratch.subgroupImage M W1)
                (Section4Scratch.subgroupImage M W2)
                (Section4Scratch.subgroupImage M W) hx⟩ := by
      intro x hx
      let xImage : Section4Scratch.subgroupImage M W :=
        ⟨x, Section3.cyclicTISet_subset
          (Section4Scratch.subgroupImage M W1)
          (Section4Scratch.subgroupImage M W2)
          (Section4Scratch.subgroupImage M W) hx⟩
      let xLocal : W := e.symm xImage
      have hxLocal : (xLocal : M) ∈ Section3.cyclicTISet W1 W2 W := by
        exact subgroupImageEquiv_symm_mem_cyclicTISet
          (M := M) (W1 := W1) (W2 := W2) (W := W) (x := xImage)
          (by simpa [xImage] using hx)
      have hcoe : (((xLocal : W) : M) : G) = x := by
        simpa [xLocal, xImage, e] using
          subgroupImageEquiv_symm_apply_coe M W xImage
      calc
        sigma eta x = sigma eta (((xLocal : W) : M) : G) := by rw [hcoe]
        _ = eta xLocal := by
          simpa [xLocal] using hSigmaAgree eta hetaClass (xLocal : M) hxLocal
        _ = E eta xImage := by
          symm
          simpa [E, e, xLocal] using
            Section1.classFunctionLinearEquivOfMulEquiv_apply e eta xImage
        _ = E eta ⟨x, Section3.cyclicTISet_subset
              (Section4Scratch.subgroupImage M W1)
              (Section4Scratch.subgroupImage M W2)
              (Section4Scratch.subgroupImage M W) hx⟩ := by
          rfl
    have hCurrentModel :
        sigma eta = Section3.sigmaOfPF35 omegaImage chi (E eta) :=
      Section3.proposition_3_9_a_uniqueness_of_pf35
        (W1 := Section4Scratch.subgroupImage M W1)
        (W2 := Section4Scratch.subgroupImage M W2)
        (W := Section4Scratch.subgroupImage M W)
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        (ω := omegaImage) (χ := chi)
        h31Image hOmegaImage horth hsigned h00 hInd hEetaIrr
        hSigmaEtaSigned hAgreeImage
    calc
      sigma eta = Section3.sigmaOfPF35 omegaImage chi (E eta) := hCurrentModel
      _ = sigmaImage (E eta) := by rw [hSigmaImageEq]
  rcases Section4Scratch.baseColumn_omega_power_of_prime_pf45
      h31 hW1prime homega hi hk with
    ⟨n, horder, hcoprime, hpow⟩
  have horderImage :
      Section3.exactCharacterValueOrder (E (omega k j0)) (Nat.card W1) :=
    (exactCharacterValueOrder_classFunctionLinearEquivOfMulEquiv_iff
      e (omega k j0) (Nat.card W1)).2 horder
  have hEbase :
      Section1.IsIrreducibleCharacterOnGroup (E (omega k j0)) :=
    Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
      e (homega.irreducible k j0)
  have hroot :
      ∀ {c b exponent : ℕ}, exponent.Coprime (c * b) →
        ∃ gamma : Gal(ℂ/ℚ),
          ∀ z : ℂ, z ^ (c * b) = 1 → gamma z = z ^ exponent := by
    intro c b exponent hexponent
    exact Section1.complex_galois_aut_pow_on_roots hexponent
  have hB :
      Section3.proposition_3_9_statement_b_complex_galois
        (Section3.sigmaOfPF35 omegaImage chi) :=
    Section3.proposition_3_9_b_of_rootAction_pf35
      (W1 := Section4Scratch.subgroupImage M W1)
      (W2 := Section4Scratch.subgroupImage M W2)
      (W := Section4Scratch.subgroupImage M W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := omegaImage) (χ := chi)
      h31Image hOmegaImage horth hsigned h00 hInd hroot
  rcases hB (ω' := E (omega k j0)) (a := Nat.card W1) (k := n)
      hEbase horderImage hcoprime with
    ⟨omegaN, _homegaNIrr, hpowImage, gamma, hgamma, hSigmaGamma, _hpoint⟩
  have hOmegaNEq : omegaN = E (omega i j0) := by
    ext x
    calc
      omegaN x = E (omega k j0) x ^ n := hpowImage x
      _ = omega k j0 (e.symm x) ^ n := by
        rw [Section1.classFunctionLinearEquivOfMulEquiv_apply]
      _ = omega i j0 (e.symm x) := (hpow (e.symm x)).symm
      _ = E (omega i j0) x := by
        rw [Section1.classFunctionLinearEquivOfMulEquiv_apply]
  refine ⟨gamma, hgamma, ?_⟩
  calc
    sigma (omega i j0) = sigmaImage (E (omega i j0)) :=
      hSigmaEq (homega.irreducible i j0)
    _ = sigmaImage omegaN := by rw [hOmegaNEq]
    _ = Section3.sigmaOfPF35 omegaImage chi omegaN := by rw [hSigmaImageEq]
    _ = Section3.classFunctionGaloisConjugate gamma
          (Section3.sigmaOfPF35 omegaImage chi (E (omega k j0))) := hSigmaGamma
    _ = Section3.classFunctionGaloisConjugate gamma
          (sigmaImage (E (omega k j0))) := by rw [hSigmaImageEq]
    _ = Section3.classFunctionGaloisConjugate gamma
          (sigma (omega k j0)) := by rw [hSigmaEq (homega.irreducible k j0)]

/-- PF `(3.9)(b)` gives the base-column conjugation equality used in the
Section `(4.6)` ambient PF `(3.9)` interface. -/
public theorem baseColumn_conjugate_sigma_eq_of_theorem_3_2_map_statement
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J → Section1.ClassFunction W}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 omega)
    (hSigma : Section3.theorem_3_2_map_statement W1 W2 W sigma) :
    ∀ g : G, Nat.Coprime (orderOf g) (Nat.card W1) →
      ∀ c : I → I,
        (∀ i : I,
          Section1.conjugateCharacter (omega i j0) = omega (c i) j0) →
        ∀ i : I, i ≠ i0 →
          sigma (omega (c i) j0) g = sigma (omega i j0) g := by
  classical
  rcases Section3.pf35_data_of_theorem_3_2_map_statement hω sigma hSigma with
    ⟨chi, horth, hsigned, h00, hInd, hSigmaOmega⟩
  have hSigmaEq : sigma = Section3.sigmaOfPF35 omega chi :=
    Section3.sigma_eq_sigmaOfPF35_of_sigma_eq_omega_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := omega) (χ := chi) h31 hω hSigmaOmega
  have hroot :
      ∀ {c b e : ℕ}, e.Coprime (c * b) →
        ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e := by
    intro c b e he
    exact Section1.complex_galois_aut_pow_on_roots he
  have hB :
      Section3.proposition_3_9_statement_b_complex_galois
        (Section3.sigmaOfPF35 omega chi) :=
    Section3.proposition_3_9_b_of_rootAction_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := omega) (χ := chi) h31 hω horth hsigned h00 hInd hroot
  change Section3.isCyclicTIHypothesis W1 W2 W at h31
  rcases h31 with ⟨_hW1le, _hW2le, hIP, _hcycW, _hoddW,
    _hW1card, _hW2card, _hTI⟩
  have hValueOrder :
      ∀ i : I, Section3.characterValueOrder (omega i j0) (Nat.card W1) := by
    intro i
    exact characterValueOrder_of_leftKernel_internalDirectProduct
      (W1 := W1) (W2 := W2) (W := W) hIP
      (hω.irreducible i j0) (hω.left_kernel i) (hω.degree_one i j0)
  intro g hg c hc i _hi
  rcases exactCharacterValueOrder_exists_dvd_of_characterValueOrder
      (hValueOrder i) with ⟨a, hadvd, ha⟩
  have hcopA : (orderOf g).Coprime a :=
    hg.coprime_dvd_right hadvd
  have hk : IsCoprime (-1 : ℤ) (a : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simp
  rcases hB (ω' := omega i j0) (a := a) (k := (-1 : ℤ))
      (hω.irreducible i j0) ha hk with
    ⟨omegaK, _homegaK, hpow, _τ, _hτ, _hσgalois, hpoint⟩
  have hConjEq : Section1.conjugateCharacter (omega i j0) = omegaK := by
    ext w
    calc
      Section1.conjugateCharacter (omega i j0) w =
          star ((omega i j0) w) := rfl
      _ = (omega i j0 w) ^ (-1 : ℤ) :=
          star_eq_zpow_neg_one_of_root ha.1.1 (ha.1.2 w)
      _ = omegaK w := (hpow w).symm
  have hOmegaK : omegaK = omega (c i) j0 := by
    rw [← hc i, hConjEq]
  calc
    sigma (omega (c i) j0) g =
        Section3.sigmaOfPF35 omega chi (omega (c i) j0) g := by
          rw [hSigmaEq]
    _ = Section3.sigmaOfPF35 omega chi omegaK g := by rw [← hOmegaK]
    _ = Section3.sigmaOfPF35 omega chi (omega i j0) g :=
        hpoint g hcopA
    _ = sigma (omega i j0) g := by rw [← hSigmaEq]

/-- Checked PF `(3.9)` adapter for an ambient-image cyclic-TI map once the
transported Section `(3.3)` table and the source rationality input are made
explicit.

This packages the reusable part of the image-carrier PF `(3.9)` step: the
remaining source work is to transport the `OmegaSystem` to the subgroup image
and prove the rationality precursor used by Section 3's PF `(3.9)(c)` theorem.
-/
public theorem ambientPF39_image_pf39_data_of_image_notation_and_rationality
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J → Section1.ClassFunction W}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 omega)
    (hSigma : Section3.theorem_3_2_map_statement W1 W2 W sigma)
    (hRat :
      ∀ {omega' : Section1.ClassFunction W} {a : ℕ},
        Section1.IsIrreducibleCharacterOnGroup omega' →
          Section3.exactCharacterValueOrder omega' a →
            ∀ g : G, (orderOf g).Coprime a →
              ∃ q : ℚ, sigma omega' g = (q : ℂ))
    (hConjBase :
      ∀ g : G, Nat.Coprime (orderOf g) (Nat.card W1) →
        ∀ c : I → I,
          (∀ i : I,
            Section1.conjugateCharacter (omega i j0) = omega (c i) j0) →
          ∀ i : I, i ≠ i0 →
            sigma (omega (c i) j0) g = sigma (omega i j0) g) :
    Section3.proposition_3_9_statement_c sigma ∧
      (∀ g : G, Nat.Coprime (orderOf g) (Nat.card W1) →
        ∀ c : I → I,
          (∀ i : I,
            Section1.conjugateCharacter (omega i j0) = omega (c i) j0) →
          ∀ i : I, i ≠ i0 →
            sigma (omega (c i) j0) g = sigma (omega i j0) g) := by
  classical
  rcases Section3.pf35_data_of_theorem_3_2_map_statement hω sigma hSigma with
    ⟨chi, horth, hsigned, h00, hInd, hSigmaOmega⟩
  have hSigmaEq : sigma = Section3.sigmaOfPF35 omega chi :=
    Section3.sigma_eq_sigmaOfPF35_of_sigma_eq_omega_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := omega) (χ := chi) h31 hω hSigmaOmega
  have hRatPF35 :
      ∀ {omega' : Section1.ClassFunction W} {a : ℕ},
        Section1.IsIrreducibleCharacterOnGroup omega' →
          Section3.exactCharacterValueOrder omega' a →
            ∀ g : G, (orderOf g).Coprime a →
              ∃ q : ℚ, Section3.sigmaOfPF35 omega chi omega' g = (q : ℂ) := by
    intro omega' a hIrred hOrder g hg
    rcases hRat hIrred hOrder g hg with ⟨q, hq⟩
    exact ⟨q, by simpa [← hSigmaEq] using hq⟩
  have h39cPF35 : Section3.proposition_3_9_statement_c
      (Section3.sigmaOfPF35 omega chi) :=
    Section3.proposition_3_9_c_of_rationality_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := omega) (χ := chi) hω hsigned hRatPF35
  constructor
  · intro omega' a hIrred hOrder g hg
    simpa [hSigmaEq] using h39cPF35 hIrred hOrder g hg
  · exact hConjBase

/-- Source leaf for the PF `(3.9)` image-carrier step after isolating the
checked Section 3 assembly.

The transported image-carrier Section `(3.3)` table is now checked by
`notation_3_3_statement_of_subgroupImageEquiv`; this leaf asks only for the
rationality precursor for PF `(3.9)(c)`.  The wrapper
`typeP_bot_typeV_ambientPF39_image_pf39_source_data_for_sigma` reconstructs
the formal `proposition_3_9_statement_c` and derives the base-column
conjugation endpoint from PF `(3.9)(b)`. -/
public theorem typeP_bot_typeV_ambientPF39_image_pf39_core_source_data_for_sigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (_hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (_hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (_hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2')
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J →
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M)}
    {sigmaM :
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction M}
    {sigmaImage :
      Section1.ClassFunction
          (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M)) →ₗ[ℂ]
        Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction M}
    {deltaSign : J → ℂ}
    (_hω :
      Section3.notation_3_3_statement
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J i0 j0 omega)
    (_h43b :
      Section4.theorem_4_3_b_statement
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J i0 j0 omega sigmaM piChar deltaSign _hω)
    (_hSigmaImage :
      Section3.theorem_3_2_map_statement
        (Section4Scratch.subgroupImage M (W1'.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2'.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
        sigmaImage) :
    ∀ {omega' :
        Section1.ClassFunction
          (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))}
        {a : ℕ},
      Section1.IsIrreducibleCharacterOnGroup omega' →
        Section3.exactCharacterValueOrder omega' a →
          ∀ g : G, (orderOf g).Coprime a →
            ∃ q : ℚ, sigmaImage omega' g = (q : ℂ) := by
  classical
  rcases theorem_8_15_fullHypothesis_static_prefix_of_typeP_bot_typeV_witness
      _hPbot _hNotation _hWitness with
    ⟨_h46, _hW2K, h31Image⟩
  let omegaImage : I → J →
      Section1.ClassFunction
        (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M)) :=
    fun i j =>
      Section1.classFunctionLinearEquivOfMulEquiv
        (subgroupImageEquiv M ((W1' ⊔ W2').subgroupOf M))
        (omega i j)
  have hOmegaImage :
      Section3.notation_3_3_statement
        (Section4Scratch.subgroupImage M (W1'.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2'.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
        I J i0 j0 omegaImage := by
    simpa [omegaImage] using
      notation_3_3_statement_of_subgroupImageEquiv
        (M := M) (W1 := W1'.subgroupOf M) (W2 := W2'.subgroupOf M)
        (W := (W1' ⊔ W2').subgroupOf M)
        (I := I) (J := J) (i0 := i0) (j0 := j0) (omega := omega) _hω
  intro omega' a hIrred hOrder g hg
  exact
    Section3.pf39_rationality_of_theorem_3_2_map_statement
      (σ := sigmaImage) h31Image hOmegaImage _hSigmaImage
      (ω' := omega') (a := a) hIrred hOrder g hg

/-- Source-level ambient-image PF `(3.9)` consequences needed for the
Section `(4.6)` base column.

This is narrower than the old base-column source leaf: it asks for the formal
PF `(3.9)(c)` endpoint for `sigmaImage` and the specific base-column
conjugation invariance supplied by PF `(3.9)(a)`.  The surrounding checked
glue derives the exact `ambientRelativePF39BaseColumnData` package. -/
public theorem typeP_bot_typeV_ambientPF39_image_pf39_source_data_for_sigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (_hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (_hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (_hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2')
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J →
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M)}
    {sigmaM :
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction M}
    {sigmaImage :
      Section1.ClassFunction
          (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M)) →ₗ[ℂ]
        Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction M}
    {deltaSign : J → ℂ}
    (hω :
      Section3.notation_3_3_statement
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J i0 j0 omega)
    (h43b :
      Section4.theorem_4_3_b_statement
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J i0 j0 omega sigmaM piChar deltaSign hω)
    (hSigmaImage :
      Section3.theorem_3_2_map_statement
        (Section4Scratch.subgroupImage M (W1'.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2'.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
        sigmaImage) :
    Section3.proposition_3_9_statement_c sigmaImage ∧
      (∀ g : G,
        Nat.Coprime (orderOf g)
          (Nat.card (Section4Scratch.subgroupImage M (W1'.subgroupOf M))) →
        ∀ c : I → I,
          (∀ i : I,
            Section1.conjugateCharacter
                (Section1.classFunctionLinearEquivOfMulEquiv
                  (subgroupImageEquiv M ((W1' ⊔ W2').subgroupOf M))
                  (omega i j0)) =
              Section1.classFunctionLinearEquivOfMulEquiv
                (subgroupImageEquiv M ((W1' ⊔ W2').subgroupOf M))
                (omega (c i) j0)) →
          ∀ i : I, i ≠ i0 →
            sigmaImage
                (Section1.classFunctionLinearEquivOfMulEquiv
                  (subgroupImageEquiv M ((W1' ⊔ W2').subgroupOf M))
                  (omega (c i) j0)) g =
              sigmaImage
                (Section1.classFunctionLinearEquivOfMulEquiv
                  (subgroupImageEquiv M ((W1' ⊔ W2').subgroupOf M))
                  (omega i j0)) g) := by
  rcases theorem_8_15_fullHypothesis_static_prefix_of_typeP_bot_typeV_witness
      _hPbot _hNotation _hWitness with
    ⟨_h46, _hW2K, h31Image⟩
  let omegaImage : I → J →
      Section1.ClassFunction
        (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M)) :=
    fun i j =>
      Section1.classFunctionLinearEquivOfMulEquiv
        (subgroupImageEquiv M ((W1' ⊔ W2').subgroupOf M))
        (omega i j)
  have hOmegaImage :
      Section3.notation_3_3_statement
        (Section4Scratch.subgroupImage M (W1'.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2'.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
        I J i0 j0 omegaImage := by
    simpa [omegaImage] using
      notation_3_3_statement_of_subgroupImageEquiv
        (M := M) (W1 := W1'.subgroupOf M) (W2 := W2'.subgroupOf M)
        (W := (W1' ⊔ W2').subgroupOf M)
        (I := I) (J := J) (i0 := i0) (j0 := j0) (omega := omega) hω
  have hRat :
      ∀ {omega' :
          Section1.ClassFunction
            (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))}
          {a : ℕ},
        Section1.IsIrreducibleCharacterOnGroup omega' →
          Section3.exactCharacterValueOrder omega' a →
            ∀ g : G, (orderOf g).Coprime a →
              ∃ q : ℚ, sigmaImage omega' g = (q : ℂ) := by
    intro omega' a hIrred hOrder g hg
    exact typeP_bot_typeV_ambientPF39_image_pf39_core_source_data_for_sigma
      _hPbot _hNotation _hWitness hω h43b hSigmaImage
      hIrred hOrder g hg
  have hConjBase :=
    baseColumn_conjugate_sigma_eq_of_theorem_3_2_map_statement
      h31Image hOmegaImage hSigmaImage
  have hData :=
    ambientPF39_image_pf39_data_of_image_notation_and_rationality
      (W1 := Section4Scratch.subgroupImage M (W1'.subgroupOf M))
      (W2 := Section4Scratch.subgroupImage M (W2'.subgroupOf M))
      (W := Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (omega := omegaImage) (sigma := sigmaImage)
      h31Image hOmegaImage hSigmaImage hRat hConjBase
  simpa [omegaImage] using hData

/-- Source-level ambient PF `(3.9)(a,c)` tail for the same ambient cyclic-TI
map on the ambient subgroup image.

This is narrower than the relative-domain source leaf: the carrier is the
actual ambient subgroup image where `hSigmaImage` is a Section `(3.2)` map.  A
checked transport lemma then carries this fact back to the relative subgroup
carrier used by Section `(4.6)`. -/
public theorem typeP_bot_typeV_ambientPF39_image_source_data_for_sigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (_hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (_hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (_hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2')
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J →
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M)}
    {sigmaM :
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction M}
    {sigmaImage :
      Section1.ClassFunction
          (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M)) →ₗ[ℂ]
        Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction M}
    {deltaSign : J → ℂ}
    (hω :
      Section3.notation_3_3_statement
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J i0 j0 omega)
    (h43b :
      Section4.theorem_4_3_b_statement
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J i0 j0 omega sigmaM piChar deltaSign hω)
    (hSigmaImage :
      Section3.theorem_3_2_map_statement
        (Section4Scratch.subgroupImage M (W1'.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2'.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
        sigmaImage) :
    Section4Scratch.ambientRelativePF39BaseColumnData
      (Nat.card (W1'.subgroupOf M))
      (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
      i0 j0
      (fun i j =>
        Section1.classFunctionLinearEquivOfMulEquiv
          (subgroupImageEquiv M ((W1' ⊔ W2').subgroupOf M))
          (omega i j))
      sigmaImage := by
  let e := subgroupImageEquiv M ((W1' ⊔ W2').subgroupOf M)
  have hImageIrred :
      ∀ i : I,
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.classFunctionLinearEquivOfMulEquiv e (omega i j0)) := by
    intro i
    exact Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
      e (hω.irreducible i j0)
  rcases typeP_bot_typeV_ambientPF39_image_pf39_source_data_for_sigma
      _hPbot _hNotation _hWitness hω h43b hSigmaImage with
    ⟨h39c, hConj⟩
  have hCard :
      Nat.card (Section4Scratch.subgroupImage M (W1'.subgroupOf M)) =
        Nat.card (W1'.subgroupOf M) :=
    Nat.card_congr (subgroupImageEquiv M (W1'.subgroupOf M)).symm.toEquiv
  have hData :
      Section4Scratch.ambientRelativePF39BaseColumnData
        (Nat.card (Section4Scratch.subgroupImage M (W1'.subgroupOf M)))
        (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
        i0 j0
        (fun i j => Section1.classFunctionLinearEquivOfMulEquiv e (omega i j))
        sigmaImage :=
    ambientRelativePF39BaseColumnData_of_pf39_base_column
      (W1 := Section4Scratch.subgroupImage M (W1'.subgroupOf M))
      (W := Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
      (i0 := i0) (j0 := j0)
      (omega := fun i j =>
        Section1.classFunctionLinearEquivOfMulEquiv e (omega i j))
      (sigma := sigmaImage) hImageIrred h39c hConj
  simpa [hCard, e] using hData

/-- Source-level ambient PF `(3.9)(a,c)` tail for the same ambient cyclic-TI
map `σ` used by the prime-Dade/subcoherence construction.  The remaining
source fact is now stated on the ambient subgroup image; this theorem is
checked carrier transport back to the relative subgroup. -/
public theorem typeP_bot_typeV_ambientPF39_source_data_for_sigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2')
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J →
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M)}
    {sigmaM :
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction M}
    {sigma :
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction M}
    {deltaSign : J → ℂ}
    (hω :
      Section3.notation_3_3_statement
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J i0 j0 omega)
    (h43b :
      Section4.theorem_4_3_b_statement
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J i0 j0 omega sigmaM piChar deltaSign hω)
    {sigmaImage :
      Section1.ClassFunction
          (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M)) →ₗ[ℂ]
        Section1.ClassFunction G}
    (hSigmaImage :
      Section3.theorem_3_2_map_statement
        (Section4Scratch.subgroupImage M (W1'.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2'.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
        sigmaImage)
    (hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M ((W1' ⊔ W2').subgroupOf M))).toLinearMap)
    (_hσIso : Section3.IsCFLinearIsometry sigma)
    (_hσVirt : Section3.MapsVirtualCharacters sigma)
    (_hσClass : Section3.MapsClassFunctions sigma)
    (_hσPrin :
      sigma (Section1.principalCharacter ((W1' ⊔ W2').subgroupOf M)) =
        Section1.principalCharacter G) :
    Section4Scratch.ambientRelativePF39BaseColumnData
      (Nat.card (W1'.subgroupOf M))
      ((W1' ⊔ W2').subgroupOf M) i0 j0 omega sigma := by
  exact
    ambientRelativePF39BaseColumnData_of_subgroupImage
      (M := M)
      (W1 := W1'.subgroupOf M)
      (W := (W1' ⊔ W2').subgroupOf M)
      (omega := omega)
      (sigmaImage := sigmaImage)
      (sigma := sigma)
      (typeP_bot_typeV_ambientPF39_image_source_data_for_sigma
        hPbot hNotation hWitness hω h43b hSigmaImage)
      hSigmaDef

/-- Source-level prime-Dade/subcoherence payload once the ambient cyclic-TI
map `σ` has been supplied by the checked Section 3 transport.

This checked wrapper recombines the Dade-transform part of
`FT_core_prime_Dade_def`/`prDade_subcoherent` with the separate ambient
PF `(3.9)` base-column tail. -/
public theorem typeP_bot_typeV_primeDade_subcoherence_source_data_for_sigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2')
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J →
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M)}
    {sigmaM :
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction M}
    {sigma :
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction M}
    {xChar : J → Section1.ClassFunction (derivedSubgroup M)}
    {deltaSign : J → ℂ}
    (hω :
      Section3.notation_3_3_statement
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J i0 j0 omega)
    (h43b :
      Section4.theorem_4_3_b_statement
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J i0 j0 omega sigmaM piChar deltaSign hω)
    (_h43c :
      Section4.theorem_4_3_c_statement
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J piChar deltaSign omega)
    (_h43d :
      Section4.theorem_4_3_d_statement
        (W1'.subgroupOf M) I J piChar deltaSign)
    (_h45a :
      Section4Scratch.theorem_4_5_a_statement
        (derivedSubgroup M) piChar xChar)
    (_h45b :
      Section4Scratch.theorem_4_5_b_statement
        (derivedSubgroup M) piChar xChar)
    {sigmaImage :
      Section1.ClassFunction
          (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M)) →ₗ[ℂ]
        Section1.ClassFunction G}
    (hSigmaImage :
      Section3.theorem_3_2_map_statement
        (Section4Scratch.subgroupImage M (W1'.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2'.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
        sigmaImage)
    (hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M ((W1' ⊔ W2').subgroupOf M))).toLinearMap)
    (hσIso : Section3.IsCFLinearIsometry sigma)
    (hσVirt : Section3.MapsVirtualCharacters sigma)
    (hσClass : Section3.MapsClassFunctions sigma)
    (hσPrin :
      sigma (Section1.principalCharacter ((W1' ⊔ W2').subgroupOf M)) =
        Section1.principalCharacter G) :
    ∃ H_A0 : G → Subgroup G,
      ∃ tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
        ∃ hCyclicA0 :
          Section2.hypothesis_2_2_statement
            (Section4Scratch.subgroupImageSet M
              (section8CyclicA0Set M W1' W2' A)) M H_A0,
          (∀ α : Section1.ClassFunction M,
            Section2.CFOn M
                (Section4Scratch.subgroupImageSet M
                  (section8CyclicA0Set M W1' W2' A))
                α →
              tau α = Section2.dadeTransform H_A0 hCyclicA0.subset_L α) ∧
            Section4Scratch.tau_agrees_on_cyclicTI_induced_statement
              (W1'.subgroupOf M)
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M) sigma tau ∧
            Section4Scratch.theorem_4_8_statement
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M)
              (section8SubgroupSetPreimage M A)
              j0 omega sigma piChar deltaSign tau ∧
            Section4Scratch.tau_isometry_on_primeDadeA0_statement
              (W1'.subgroupOf M)
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M)
              (section8SubgroupSetPreimage M A) tau ∧
            Section4Scratch.tau_maps_primeDadeA0_to_punctured_statement
              (W1'.subgroupOf M)
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M)
              (section8SubgroupSetPreimage M A) tau ∧
            Section4Scratch.tau_maps_primeDadeA0_to_virtual_statement
              (W1'.subgroupOf M)
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M)
              (section8SubgroupSetPreimage M A) tau ∧
            Section4Scratch.ambientRelativePF39BaseColumnData
              (Nat.card (W1'.subgroupOf M))
              ((W1' ⊔ W2').subgroupOf M) i0 j0 omega sigma := by
  rcases typeP_bot_typeV_primeDadeSupportedPackage_source_data_for_sigma
      hPbot hNotation hWitness (sigma := sigma) hSigmaImage hSigmaDef with
    ⟨pkg⟩
  rcases theorem_8_15_fullHypothesis_static_prefix_of_typeP_bot_typeV_witness
      hPbot hNotation hWitness with
    ⟨h46, _hW2K, _h31⟩
  have h47 :
      Section4Scratch.theorem_4_7_statement
        (derivedSubgroup M) (Ms.subgroupOf M)
        (section8SubgroupSetPreimage M A) :=
    Section4Scratch.theorem_4_7 _ _ _ _ _ _ h46
  have h48 :
      Section4Scratch.theorem_4_8_statement
        (W2'.subgroupOf M) ((W1' ⊔ W2').subgroupOf M)
        (section8SubgroupSetPreimage M A)
        j0 omega sigma piChar deltaSign pkg.tau :=
    theorem_4_8_primeDade
      (derivedSubgroup M) (W1'.subgroupOf M) (W2'.subgroupOf M)
      ((W1' ⊔ W2').subgroupOf M) (Ms.subgroupOf M)
      (section8SubgroupSetPreimage M A) i0 j0 omega sigmaM sigma
      piChar xChar deltaSign pkg.tau
      (theorem_8_15_subgroupImage_hypothesis_3_1_of_typeP hWitness.1)
      hSigmaImage hSigmaDef pkg.h22CyclicA0 pkg.tau_cyclicA0
      h46 _h45a hω h43b _h43c _h43d h47
  have hAmbientPF39 :
      Section4Scratch.ambientRelativePF39BaseColumnData
        (Nat.card (W1'.subgroupOf M))
        ((W1' ⊔ W2').subgroupOf M) i0 j0 omega sigma :=
    typeP_bot_typeV_ambientPF39_source_data_for_sigma
      hPbot hNotation hWitness (sigma := sigma) hω h43b
      hSigmaImage hSigmaDef
      hσIso hσVirt hσClass hσPrin
  exact
    ⟨pkg.H_A0, pkg.tau, pkg.h22CyclicA0, pkg.tau_cyclicA0,
      pkg.tau_agrees_cyclic, h48,
      pkg.tau_isometry_on_primeDadeA0,
      pkg.tau_maps_primeDadeA0_to_punctured,
      pkg.tau_maps_primeDadeA0_to_virtual, hAmbientPF39⟩

/-- Source-level prime-Dade/subcoherence payload for the witness-local
Type-P/Type-V source context.

The ambient cyclic-TI map `σ` and its basic Section 3 map fields are checked
transport from the Type-P witness. The remaining source leaf is
`typeP_bot_typeV_primeDade_subcoherence_source_data_for_sigma`, which supplies
the Dade/subcoherence data tied to that `σ`. -/
public theorem typeP_bot_typeV_primeDade_subcoherence_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2')
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J →
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M)}
    {sigmaM :
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction M}
    {piChar : I → J → Section1.ClassFunction M}
    {xChar : J → Section1.ClassFunction (derivedSubgroup M)}
    {deltaSign : J → ℂ}
    (hω :
      Section3.notation_3_3_statement
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J i0 j0 omega)
    (h43b :
      Section4.theorem_4_3_b_statement
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J i0 j0 omega sigmaM piChar deltaSign hω)
    (h43c :
      Section4.theorem_4_3_c_statement
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J piChar deltaSign omega)
    (h43d :
      Section4.theorem_4_3_d_statement
        (W1'.subgroupOf M) I J piChar deltaSign)
    (h45a :
      Section4Scratch.theorem_4_5_a_statement
        (derivedSubgroup M) piChar xChar)
    (h45b :
      Section4Scratch.theorem_4_5_b_statement
        (derivedSubgroup M) piChar xChar) :
    ∃ sigma :
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction G,
      ∃ H_A0 : G → Subgroup G,
          ∃ tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
            Section3.IsCFLinearIsometry sigma ∧
              Section3.MapsVirtualCharacters sigma ∧
              Section3.MapsClassFunctions sigma ∧
              sigma
                (Section1.principalCharacter ((W1' ⊔ W2').subgroupOf M)) =
                Section1.principalCharacter G ∧
              (∀ α : Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M),
                Section1.IsClassFunction α →
                ∀ x : M,
                ∀ hx : x ∈ Section3.cyclicTISet
                    (W1'.subgroupOf M) (W2'.subgroupOf M)
                    ((W1' ⊔ W2').subgroupOf M),
                    sigma α (x : G) =
                      α ⟨x, Section3.cyclicTISet_subset
                        (W1'.subgroupOf M) (W2'.subgroupOf M)
                        ((W1' ⊔ W2').subgroupOf M) hx⟩) ∧
              ∃ hCyclicA0 :
                Section2.hypothesis_2_2_statement
                (Section4Scratch.subgroupImageSet M
                  (section8CyclicA0Set M W1' W2' A)) M H_A0,
              (∀ α : Section1.ClassFunction M,
                Section2.CFOn M
                    (Section4Scratch.subgroupImageSet M
                      (section8CyclicA0Set M W1' W2' A))
                    α →
                  tau α =
                    Section2.dadeTransform H_A0 hCyclicA0.subset_L α) ∧
            Section4Scratch.tau_agrees_on_cyclicTI_induced_statement
              (W1'.subgroupOf M)
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M) sigma tau ∧
            Section4Scratch.theorem_4_8_statement
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M)
              (section8SubgroupSetPreimage M A)
              j0 omega sigma piChar deltaSign tau ∧
            Section4Scratch.tau_isometry_on_primeDadeA0_statement
              (W1'.subgroupOf M)
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M)
              (section8SubgroupSetPreimage M A) tau ∧
            Section4Scratch.tau_maps_primeDadeA0_to_punctured_statement
              (W1'.subgroupOf M)
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M)
              (section8SubgroupSetPreimage M A) tau ∧
            Section4Scratch.tau_maps_primeDadeA0_to_virtual_statement
              (W1'.subgroupOf M)
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M)
              (section8SubgroupSetPreimage M A) tau ∧
            Section4Scratch.ambientRelativePF39BaseColumnData
              (Nat.card (W1'.subgroupOf M))
              ((W1' ⊔ W2').subgroupOf M) i0 j0 omega sigma ∧
            Section4Scratch.ambientRelativePF39BaseRowConjugateData
              ((W1' ⊔ W2').subgroupOf M) i0 j0 omega sigma ∧
            Section4Scratch.ambientRelativePF39ConjugateData
              ((W1' ⊔ W2').subgroupOf M) sigma := by
  rcases exists_typeP_ambient_section3_sigma_transport_data_of_typeP_bot_typeV_witness
      hPbot hNotation hWitness with
    ⟨sigmaImage, sigma, hSigmaImage, hSigmaDef, hσIso, hσVirt, hσClass,
      hσPrin, hσAgreeCyc⟩
  rcases typeP_bot_typeV_primeDade_subcoherence_source_data_for_sigma
      hPbot hNotation hWitness (sigma := sigma)
      hω h43b h43c h43d h45a h45b hSigmaImage hSigmaDef
      hσIso hσVirt hσClass hσPrin with
    ⟨H_A0, tau, hCyclicA0, hτCyclicA0, hTauCyclic, h48,
      hTauIsoA0, hTauPunctA0, hTauVirtA0, hAmbientPF39⟩
  have h31 :=
    theorem_8_15_subgroupImage_hypothesis_3_1_of_typeP hWitness.1
  have hAmbientPF39BaseRow :
      Section4Scratch.ambientRelativePF39BaseRowConjugateData
        ((W1' ⊔ W2').subgroupOf M) i0 j0 omega sigma := by
    let e := subgroupImageEquiv M ((W1' ⊔ W2').subgroupOf M)
    let omegaImage : I → J →
        Section1.ClassFunction
          (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M)) :=
      fun i j => Section1.classFunctionLinearEquivOfMulEquiv e (omega i j)
    have hOmegaImage :
        Section3.notation_3_3_statement
          (Section4Scratch.subgroupImage M (W1'.subgroupOf M))
          (Section4Scratch.subgroupImage M (W2'.subgroupOf M))
          (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
          I J i0 j0 omegaImage := by
      simpa [omegaImage, e] using
        notation_3_3_statement_of_subgroupImageEquiv
          (M := M) (W1 := W1'.subgroupOf M) (W2 := W2'.subgroupOf M)
          (W := (W1' ⊔ W2').subgroupOf M)
          (I := I) (J := J) (i0 := i0) (j0 := j0) (omega := omega) hω
    have hImageData :
        Section4Scratch.ambientRelativePF39BaseRowConjugateData
          (Section4Scratch.subgroupImage M ((W1' ⊔ W2').subgroupOf M))
          i0 j0 omegaImage sigmaImage := by
      intro j _hj
      exact Section3.theorem_3_2_map_conjugateCharacter_of_irreducible
        h31 hOmegaImage sigmaImage hSigmaImage
        (hOmegaImage.irreducible i0 j)
    exact
      ambientRelativePF39BaseRowConjugateData_of_subgroupImage
        (M := M) (W := (W1' ⊔ W2').subgroupOf M)
        (omega := omega) (sigmaImage := sigmaImage) (sigma := sigma)
        hImageData hSigmaDef
  have hAmbientPF39Conjugate :
      Section4Scratch.ambientRelativePF39ConjugateData
        ((W1' ⊔ W2').subgroupOf M) sigma :=
    ambientRelativePF39ConjugateData_of_subgroupImage
      h31 hω hSigmaImage hSigmaDef
  exact
    ⟨sigma, H_A0, tau, hσIso, hσVirt, hσClass, hσPrin, hσAgreeCyc,
      hCyclicA0, hτCyclicA0, hTauCyclic, h48, hTauIsoA0,
      hTauPunctA0, hTauVirtA0, hAmbientPF39, hAmbientPF39BaseRow,
      hAmbientPF39Conjugate⟩

/-- Prime-Dade/subcoherence payload plus the checked Section 2 Dade
consequences needed by the full Section `(4.6)` record. -/
public theorem typeP_bot_typeV_primeDade_subcoherence_core
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2')
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J →
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M)}
    {sigmaM :
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction M}
    {piChar : I → J → Section1.ClassFunction M}
    {xChar : J → Section1.ClassFunction (derivedSubgroup M)}
    {deltaSign : J → ℂ}
    (hω :
      Section3.notation_3_3_statement
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J i0 j0 omega)
    (h43b :
      Section4.theorem_4_3_b_statement
        (W1'.subgroupOf M)
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J i0 j0 omega sigmaM piChar deltaSign hω)
    (h43c :
      Section4.theorem_4_3_c_statement
        (W2'.subgroupOf M)
        ((W1' ⊔ W2').subgroupOf M)
        I J piChar deltaSign omega)
    (h43d :
      Section4.theorem_4_3_d_statement
        (W1'.subgroupOf M) I J piChar deltaSign)
    (h45a :
      Section4Scratch.theorem_4_5_a_statement
        (derivedSubgroup M) piChar xChar)
    (h45b :
      Section4Scratch.theorem_4_5_b_statement
        (derivedSubgroup M) piChar xChar) :
    ∃ sigma :
      Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction G,
      ∃ H_A0 : G → Subgroup G,
          ∃ tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
            Section3.IsCFLinearIsometry sigma ∧
              Section3.MapsVirtualCharacters sigma ∧
              Section3.MapsClassFunctions sigma ∧
              sigma
                (Section1.principalCharacter ((W1' ⊔ W2').subgroupOf M)) =
                Section1.principalCharacter G ∧
              (∀ α : Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M),
                Section1.IsClassFunction α →
                ∀ x : M,
                ∀ hx : x ∈ Section3.cyclicTISet
                    (W1'.subgroupOf M) (W2'.subgroupOf M)
                    ((W1' ⊔ W2').subgroupOf M),
                    sigma α (x : G) =
                      α ⟨x, Section3.cyclicTISet_subset
                        (W1'.subgroupOf M) (W2'.subgroupOf M)
                        ((W1' ⊔ W2').subgroupOf M) hx⟩) ∧
              ∃ hCyclicA0 :
                Section2.hypothesis_2_2_statement
                (Section4Scratch.subgroupImageSet M
                  (section8CyclicA0Set M W1' W2' A)) M H_A0,
              (∀ α : Section1.ClassFunction M,
                Section2.CFOn M
                    (Section4Scratch.subgroupImageSet M
                      (section8CyclicA0Set M W1' W2' A))
                    α →
                  tau α =
                    Section2.dadeTransform H_A0 hCyclicA0.subset_L α) ∧
            Section4Scratch.tau_agrees_on_cyclicTI_induced_statement
              (W1'.subgroupOf M)
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M) sigma tau ∧
            Section4Scratch.theorem_4_8_statement
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M)
              (section8SubgroupSetPreimage M A)
              j0 omega sigma piChar deltaSign tau ∧
            Section4Scratch.tau_isometry_on_primeDadeA0_statement
              (W1'.subgroupOf M)
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M)
              (section8SubgroupSetPreimage M A) tau ∧
            Section4Scratch.tau_maps_primeDadeA0_to_punctured_statement
              (W1'.subgroupOf M)
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M)
              (section8SubgroupSetPreimage M A) tau ∧
            Section4Scratch.tau_maps_primeDadeA0_to_virtual_statement
              (W1'.subgroupOf M)
              (W2'.subgroupOf M)
              ((W1' ⊔ W2').subgroupOf M)
              (section8SubgroupSetPreimage M A) tau ∧
            Section4Scratch.ambientRelativePF39BaseColumnData
              (Nat.card (W1'.subgroupOf M))
              ((W1' ⊔ W2').subgroupOf M) i0 j0 omega sigma ∧
            Section4Scratch.ambientRelativePF39BaseRowConjugateData
              ((W1' ⊔ W2').subgroupOf M) i0 j0 omega sigma ∧
            Section4Scratch.ambientRelativePF39ConjugateData
              ((W1' ⊔ W2').subgroupOf M) sigma := by
  rcases typeP_bot_typeV_primeDade_subcoherence_source_data
      hPbot hNotation hWitness hω h43b h43c h43d h45a h45b with
    ⟨sigma, H_A0, tau, hσIso, hσVirt, hσClass, hσPrin, hσAgreeCyc,
      hCyclicA0, hτCyclicA0, hTauCyclic, h48, hTauIsoA0,
      hTauPunctA0, hTauVirtA0, hAmbientPF39, hAmbientPF39BaseRow,
      hAmbientPF39Conjugate⟩
  exact
    ⟨sigma, H_A0, tau, hσIso, hσVirt, hσClass, hσPrin, hσAgreeCyc,
      hCyclicA0, hτCyclicA0, hTauCyclic, h48, hTauIsoA0,
      hTauPunctA0, hTauVirtA0, hAmbientPF39, hAmbientPF39BaseRow,
      hAmbientPF39Conjugate⟩

/-- Assemble the witness-local full Section `(4.6)` record from the checked
static Type-P fields and the prime-Dade/subcoherence core. -/
public theorem typeP_bot_typeV_fullFourSixData_core
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2') :
    ∃ I : Type u, ∃ J : Type u,
      ∃ instFintypeI : Fintype I, ∃ instFintypeJ : Fintype J,
        ∃ instDecidableEqI : DecidableEq I,
          ∃ instDecidableEqJ : DecidableEq J,
            letI : Fintype I := instFintypeI
            letI : Fintype J := instFintypeJ
            letI : DecidableEq I := instDecidableEqI
            letI : DecidableEq J := instDecidableEqJ
            ∃ i0 : I, ∃ j0 : J,
              ∃ omega :
                I → J →
                  Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M),
                ∃ sigmaM :
                  Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
                    Section1.ClassFunction M,
                  ∃ sigma :
                    Section1.ClassFunction ((W1' ⊔ W2').subgroupOf M) →ₗ[ℂ]
                      Section1.ClassFunction G,
                    ∃ piChar : I → J → Section1.ClassFunction M,
                      ∃ xChar : J → Section1.ClassFunction (derivedSubgroup M),
                        ∃ deltaSign : J → ℂ,
                          ∃ tau :
                            Section1.ClassFunction M →ₗ[ℂ]
                              Section1.ClassFunction G,
                            ∃ H_A H_A0 : G → Subgroup G,
                              ∃ hCyclicA0 :
                                Section2.hypothesis_2_2_statement
                                  (Section4Scratch.subgroupImageSet M
                                    (section8CyclicA0Set M W1' W2' A)) M H_A0,
                                (∀ α : Section1.ClassFunction M,
                                  Section2.CFOn M
                                      (Section4Scratch.subgroupImageSet M
                                        (section8CyclicA0Set M W1' W2' A))
                                      α →
                                    tau α =
                                      Section2.dadeTransform H_A0
                                        hCyclicA0.subset_L α) ∧
                                  (∀ α :
                                    Section1.ClassFunction
                                      ((W1' ⊔ W2').subgroupOf M),
                                    Section1.IsClassFunction α →
                                      ∀ x : M, ∀ hx : x ∈
                                        Section3.cyclicTISet
                                          (W1'.subgroupOf M)
                                          (W2'.subgroupOf M)
                                          ((W1' ⊔ W2').subgroupOf M),
                                          sigma α (x : G) =
                                            α ⟨x, Section3.cyclicTISet_subset
                                              (W1'.subgroupOf M)
                                              (W2'.subgroupOf M)
                                              ((W1' ⊔ W2').subgroupOf M)
                                              hx⟩) ∧
                                  Section4Scratch.hypothesis_4_6_supported_statement M
                                    (derivedSubgroup M)
                                    (W1'.subgroupOf M)
                                    (W2'.subgroupOf M)
                                    ((W1' ⊔ W2').subgroupOf M)
                                    (Ms.subgroupOf M)
                                    (section8SubgroupSetPreimage M A)
                                    i0 j0 omega sigmaM sigma piChar xChar
                                    deltaSign tau H_A := by
  classical
  rcases notation_8_10_source_typeP_witness_typeV_context_of_typeP_bot
      hPbot hNotation hWitness with
    ⟨_hUbot, hPbot', _hV, _hMs, _hMF, _hAcentral, _hA1, _hAeqA1⟩
  rcases theorem_8_15_fullHypothesis_static_prefix_of_typeP_bot_typeV_witness
      hPbot hNotation hWitness with
    ⟨h46, hW2K, h31⟩
  rcases exists_hypothesis2_section4_A_dade_transform_of_typeP_bot_typeV_witness
      hPbot hNotation hWitness with
    ⟨H_A, _tildeA, _tildeA0, _tildeA1, _h14, h22A, _h22A0, _tau0,
      _hτdef0, _hτ0⟩
  rcases exists_typeP_local_section4_character_data
      (G := G) (M := M) (MF := MF) (U := ⊥) (W1 := W1') (W2 := W2')
      hPbot' with
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, omega, hω, sigmaM, piChar, deltaSign, xChar,
      h43b, h43c, h43d, h45a, h45b⟩
  letI : Fintype I := instFintypeI
  letI : Fintype J := instFintypeJ
  letI : DecidableEq I := instDecidableEqI
  letI : DecidableEq J := instDecidableEqJ
  rcases typeP_bot_typeV_primeDade_subcoherence_core
      hPbot hNotation hWitness hω h43b h43c h43d h45a h45b with
    ⟨sigma, H_A0, tau, hσIso, hσVirt, hσClass, hσPrin, hσAgreeCyc,
      hCyclicA0, hτCyclicA0,
      hTauCyclic, h48, hTauIsoA0, hTauPunctA0, hTauVirtA0,
      hAmbientPF39, hAmbientPF39BaseRow, hAmbientPF39Conjugate⟩
  refine
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, omega, sigmaM, sigma, piChar, xChar, deltaSign, tau, H_A,
      H_A0, ?_⟩
  exact
    ⟨hCyclicA0, hτCyclicA0, hσAgreeCyc,
      ⟨h46, hW2K, h31, hσIso, hσVirt, hσClass, hσPrin, h22A,
        hω, h43b, h43c, h43d, h45a, h45b, hTauCyclic,
        h48, hTauIsoA0, hTauPunctA0, hTauVirtA0,
        hAmbientPF39, hAmbientPF39BaseRow, hAmbientPF39Conjugate⟩⟩


public theorem section8Hypothesis52FullData_of_notation_8_10_source_typeP_witness
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 U W1' W2' : Subgroup G}
    {A A0 A1 : Set G}
    (_hPbot : typePDefinitionData M MF ⊥ W1 W2)
    (_hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (_hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1' W2') :
    Nonempty (section8Hypothesis52FullData M Ms W1' W2' A) := by
  rcases typeP_bot_typeV_fullFourSixData_core
      _hPbot _hNotation _hWitness with
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, omega, sigmaM, sigma, piChar, xChar, deltaSign, tau, H_A,
      H_A0, hCyclicA0, hτCyclicA0, hσAgreeCyc, hFull⟩
  letI : Fintype I := instFintypeI
  letI : Fintype J := instFintypeJ
  letI : DecidableEq I := instDecidableEqI
  letI : DecidableEq J := instDecidableEqJ
  exact ⟨section8Hypothesis52FullData_of_supportedHypothesis
    (M := M) (Ms := Ms) (W1 := W1') (W2 := W2') (A := A)
    (W := (W1' ⊔ W2').subgroupOf M)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (omega := omega) (sigmaM := sigmaM) (sigma := sigma)
    (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
    (tau := tau) (H_A := H_A) (H_A0 := H_A0)
    hCyclicA0 hτCyclicA0 hσAgreeCyc rfl hFull⟩

/-- Source Type-P data with the trivial complement, in the PF Type-V
alternative, supplies the fixed Section 8 Hypothesis `(5.2)` package used by
PF `(8.15)`.

This is the Section 8 source boundary for PF `(10.10)`: after PF10 has fixed
the `(8.10)` notation and the Type-P witness, Section 8 owns the existence of
the matching full Section `(4.6)`/Dade source package. -/
public theorem section8Hypothesis52Source_of_typeP_bot_typeV_notation_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (hP : typePDefinitionData M MF ⊥ W1 W2)
    (_hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (_hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet
        (section16HatW W1 W2) (M : Set G))
    (_hLate :
      (typeIIIDefinitionData M MF ∨
          typeIVDefinitionData M MF ∨
            typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1) :
    section8Hypothesis52Source M MF Ms A A0 A1 := by
  intro U W1' W2' hWitness
  exact section8Hypothesis52FullData_of_notation_8_10_source_typeP_witness
    (G := G) (M := M) (MF := MF) (Ms := Ms) (W1 := W1) (W2 := W2)
    (U := U) (W1' := W1') (W2' := W2') (A := A) (A0 := A0) (A1 := A1)
    hP hNotation hWitness

private theorem sourceTypeP_MF_eq_msigma_of_not_le_msigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hUnotσ : ¬ U ≤ section10Msigma M)
    (hsourceP : typePDefinitionData M MF U W1 W2) :
    MF = section10Msigma M := by
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  have hMF15 : section15MFSubgroup M MF := by
    simpa [section16MFSubgroup, section16NilpotentNormalHallIn,
      section15MFSubgroup, section15NilpotentNormalHallIn] using hMF
  by_contra hMFne
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, _U0, hKU⟩
  rcases theorem_15_2_c (G := G) (M := M) (MF := MF) (K := K)
      hM hMF15 hKU.1 hMFne with
    ⟨q, hq, Q, hQ, hQnormal, hQMF⟩
  rcases theorem_15_2_d (G := G) (M := M) (MF := MF) (K := K)
      (Q := Q) hM hMF15 hKU.1 hMFne hq hQ hQnormal hQMF with
    ⟨D0, hD0⟩
  have hUσ : U ≤ section10Msigma M := by
    intro x hx
    simpa [hD0.1] using hUleD hx
  exact hUnotσ hUσ

private theorem sourceTypeP_W1_KUData_structural_fields
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hMFeq : MF = section10Msigma M)
    (hsourceP : typePDefinitionData M MF U W1 W2) :
    section12ComplementIn M W1 (U ⊔ section10Msigma M) ∧
      section12ComplementIn M (section10Msigma M) (W1 ⊔ U) ∧
      section10NormalIn (U ⊔ section10Msigma M) M ∧
      section10NormalIn U (W1 ⊔ U) := by
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, hMcomp, _hUleD,
      _hUnil, hW1norm, hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  have hD_eq : ambientDerivedSubgroup M = MF ⊔ U := hDercomp.2.2.1
  have hD_eq_sigma : ambientDerivedSubgroup M = section10Msigma M ⊔ U := by
    simpa [hMFeq] using hD_eq
  have hD_eq_USigma : ambientDerivedSubgroup M = U ⊔ section10Msigma M := by
    calc
      ambientDerivedSubgroup M = MF ⊔ U := hD_eq
      _ = section10Msigma M ⊔ U := by rw [hMFeq]
      _ = U ⊔ section10Msigma M := sup_comm (section10Msigma M) U
  rcases hMcomp with ⟨hDM, hW1M, hM_eq, hD_W1_disj⟩
  rcases hDercomp with ⟨hMFD, hUD, _hD_eq', hMF_U_disj⟩
  have hSigmaM : section10Msigma M ≤ M := by
    intro x hx
    exact hDM (by simpa [hMFeq] using hMFD (by simpa [hMFeq] using hx))
  have hW1U_M : W1 ⊔ U ≤ M :=
    sup_le hW1M (hUD.trans hDM)
  have hW1_norm_U : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro w hw
    exact (mem_subgroupNormalizerIn.mp (hW1norm hw)).1
  have hcompW1USigma : section12ComplementIn M W1 (U ⊔ section10Msigma M) := by
    refine ⟨hW1M, ?_, ?_, ?_⟩
    · rw [← hD_eq_USigma]
      exact hDM
    · calc
        M = ambientDerivedSubgroup M ⊔ W1 := hM_eq
        _ = W1 ⊔ ambientDerivedSubgroup M := sup_comm (ambientDerivedSubgroup M) W1
        _ = W1 ⊔ (U ⊔ section10Msigma M) := by rw [← hD_eq_USigma]
    · rw [← hD_eq_USigma]
      exact hD_W1_disj.symm
  have hcompSigmaW1U : section12ComplementIn M (section10Msigma M) (W1 ⊔ U) := by
    refine ⟨hSigmaM, hW1U_M, ?_, ?_⟩
    · calc
        M = ambientDerivedSubgroup M ⊔ W1 := hM_eq
        _ = (section10Msigma M ⊔ U) ⊔ W1 := by rw [hD_eq_sigma]
        _ = section10Msigma M ⊔ (W1 ⊔ U) := by
          simp [sup_comm, sup_left_comm]
    · rw [Subgroup.disjoint_def]
      intro x hxSigma hxW1U
      have hW1U_mul :
          ((W1 ⊔ U : Subgroup G) : Set G) = (W1 : Set G) * (U : Set G) := by
        exact Subgroup.coe_mul_of_left_le_normalizer_right
          (H := W1) (N := U) hW1_norm_U
      have hxW1Uset : x ∈ ((W1 ⊔ U : Subgroup G) : Set G) := hxW1U
      rw [hW1U_mul, Set.mem_mul] at hxW1Uset
      rcases hxW1Uset with ⟨w, hwW1, u, huU, hwu⟩
      have hxD : x ∈ ambientDerivedSubgroup M := by
        simpa [hMFeq] using hMFD (by simpa [hMFeq] using hxSigma)
      have hwD : w ∈ ambientDerivedSubgroup M := by
        have hw_eq : w = x * u⁻¹ := by
          rw [← hwu]
          simp [mul_assoc]
        rw [hw_eq]
        exact (ambientDerivedSubgroup M).mul_mem hxD (hUD (U.inv_mem huU))
      have hw_bot : w ∈ (⊥ : Subgroup G) :=
        Subgroup.disjoint_def.mp hD_W1_disj hwD hwW1
      have hw_one : w = 1 := by
        simpa using hw_bot
      have hxU : x ∈ U := by
        have hx_eq : x = u := by
          simpa [hw_one] using hwu.symm
        simpa [hx_eq] using huU
      have hxMF : x ∈ MF := by
        simpa [hMFeq] using hxSigma
      exact Subgroup.disjoint_def.mp hMF_U_disj hxMF hxU
  have hUSigmaNormal : section10NormalIn (U ⊔ section10Msigma M) M := by
    have hnormD : section10NormalIn (ambientDerivedSubgroup M) M :=
      section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)
    simpa [← hD_eq_USigma] using hnormD
  have hUnormal : section10NormalIn U (W1 ⊔ U) := by
    refine ⟨le_sup_right, ?_⟩
    simpa using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := W1) (N := U) hW1_norm_U)
  exact ⟨hcompW1USigma, hcompSigmaW1U, hUSigmaNormal, hUnormal⟩

private theorem sourceTypeP_W1_actsRegularlyOn_U
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hsourceP : typePDefinitionData M MF U W1 W2) :
    section14ActsRegularlyOn W1 U := by
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD,
      _hUnil, hW1norm, hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, hW2leInf, _hW2cyc, _hW2ne, hCent, _hNorm⟩
  rcases hDercomp with ⟨_hMFD, hUD, _hD_eq, hMF_U_disj⟩
  refine ⟨?_, ?_⟩
  · intro w hw
    exact (mem_subgroupNormalizerIn.mp (hW1norm hw)).1
  · intro x hxW1 hxne
    apply le_antisymm
    · intro y hy
      have hyU : y ∈ U := hy.1
      have hyD : y ∈ ambientDerivedSubgroup M := hUD hyU
      have hycent : y ∈ Subgroup.centralizer ({x} : Set G) := hy.2
      have hyDcent :
          y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := ⟨hyD, hycent⟩
      have hyW2 : y ∈ W2 := by
        simpa [hCent x hxW1 hxne] using hyDcent
      have hyMF : y ∈ MF := (hW2leInf hyW2).1
      have hybot : y ∈ (⊥ : Subgroup G) :=
        Subgroup.disjoint_def.mp hMF_U_disj hyMF hyU
      simpa using hybot
    · exact bot_le

private theorem sourceTypeP_hallSubgroupIn_of_le_overgroup
    {G : Type u} [Group G] [Finite G]
    {π : Set Nat.Primes} {K E M : Subgroup G}
    (hHall : section12HallSubgroupIn π K M)
    (hKE : K ≤ E) (hEM : E ≤ M) :
    section12HallSubgroupIn π K E := by
  classical
  rcases hHall with ⟨_hKM, hHallM⟩
  refine ⟨hKE, ?_⟩
  refine isHallSubgroup_of (G := E) (π := π) (H := K.subgroupOf E) ?_ ?_
  · intro p hp
    have hcardE : Nat.card (K.subgroupOf E) = Nat.card K :=
      natCard_subgroupOf_eq K E hKE
    have hcardM : Nat.card (K.subgroupOf M) = Nat.card K :=
      natCard_subgroupOf_eq K M (hKE.trans hEM)
    exact hHallM.p_in_pi_of_p_dvd_card p (by simpa [hcardE, hcardM] using hp)
  · intro p hpπ hpidx
    let EsubM : Subgroup M := E.subgroupOf M
    have hKsub_le_Esub : K.subgroupOf M ≤ EsubM := by
      intro x hx
      exact hKE hx
    have hrel_eq :
        (K.subgroupOf E).index = (K.subgroupOf M).relIndex EsubM := by
      have hsub :=
        Subgroup.relIndex_subgroupOf (H := K) (K := E) (L := M) hEM
      simpa [EsubM, Subgroup.relIndex] using hsub.symm
    have hidx_dvd :
        (K.subgroupOf E).index ∣ (K.subgroupOf M).index := by
      have hrel_dvd :
          (K.subgroupOf M).relIndex EsubM ∣ (K.subgroupOf M).index :=
        Subgroup.relIndex_dvd_index_of_le hKsub_le_Esub
      simpa [hrel_eq] using hrel_dvd
    exact (hHallM.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpπ

private theorem sourceTypeP_right_isHall_compl_of_left_hall
    {G : Type u} [Group G] [Finite G]
    {π : Set Nat.Primes} {R K U : Subgroup G}
    (hcomp : section12ComplementIn R K U)
    (hUnormal : section10NormalIn U R)
    (hKHall : section12HallSubgroupIn π K R) :
    section12HallSubgroupIn πᶜ U R := by
  classical
  rcases hcomp with ⟨hKR, hUR, hsup, hdisj⟩
  rcases hKHall with ⟨_hKR', hKHallSub⟩
  have hcompSymm : section12ComplementIn R U K := by
    refine ⟨hUR, hKR, ?_, hdisj.symm⟩
    calc
      R = K ⊔ U := hsup
      _ = U ⊔ K := sup_comm K U
  letI : (U.subgroupOf R).Normal := hUnormal.2
  have hcompLocal : (K.subgroupOf R).IsComplement' (U.subgroupOf R) :=
    sourceTypeP_complementIn_isComplement_subgroupOf
      (M := R) (H := U) (K := K) hcompSymm
  refine ⟨hUR, ?_⟩
  refine isHallSubgroup_of (G := R) (π := πᶜ) (H := U.subgroupOf R) ?_ ?_
  · intro q hqU hqπ
    have hqKidx : q.val ∣ (K.subgroupOf R).index := by
      simpa [hcompLocal.symm.index_eq_card] using hqU
    exact (hKHallSub.p_in_pi_of_p_dvd_index q hqKidx) hqπ
  · intro q hqπc hqUidx
    have hqK : q.val ∣ Nat.card (K.subgroupOf R) := by
      simpa [hcompLocal.index_eq_card] using hqUidx
    exact hqπc (hKHallSub.p_in_pi_of_p_dvd_card q hqK)

private theorem sourceTypeP_U_hall_from_W1_kappa_hall
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMFeq : MF = section10Msigma M)
    (hsourceP : typePDefinitionData M MF U W1 W2)
    (hW1Hallκ : section12HallSubgroupIn (section14KappaPrimes M) W1 M) :
    section12HallSubgroupIn ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ)
      U M := by
  classical
  let E : Subgroup G := W1 ⊔ U
  rcases sourceTypeP_W1_KUData_structural_fields hMFeq hsourceP with
    ⟨hcompW1USigma, hcompSigmaW1U, _hUSigmaNormal, hUnormal⟩
  have hEM : E ≤ M := by
    simpa [E] using hcompSigmaW1U.2.1
  have hUE : U ≤ E := by
    intro x hx
    exact (show x ∈ W1 ⊔ U from (le_sup_right : U ≤ W1 ⊔ U) hx)
  have hW1E : W1 ≤ E := by
    intro x hx
    exact (show x ∈ W1 ⊔ U from (le_sup_left : W1 ≤ W1 ⊔ U) hx)
  have hW1HallE : section12HallSubgroupIn (section14KappaPrimes M) W1 E :=
    sourceTypeP_hallSubgroupIn_of_le_overgroup hW1Hallκ hW1E hEM
  have hW1Udisj : Disjoint W1 U := by
    rw [Subgroup.disjoint_def]
    intro x hxW1 hxU
    exact Subgroup.disjoint_def.mp hcompW1USigma.2.2.2 hxW1
      (show x ∈ U ⊔ section10Msigma M from
        (le_sup_left : U ≤ U ⊔ section10Msigma M) hxU)
  have hcompW1U : section12ComplementIn E W1 U := by
    refine ⟨hW1E, hUE, ?_, hW1Udisj⟩
    simp [E]
  have hUnormalE : section10NormalIn U E := by
    simpa [E] using hUnormal
  have hUHallE : section12HallSubgroupIn (section14KappaPrimes M)ᶜ U E :=
    sourceTypeP_right_isHall_compl_of_left_hall hcompW1U hUnormalE hW1HallE
  have hEHallM : section12HallSubgroupIn (section10SigmaPrimes M)ᶜ E M := by
    refine ⟨hEM, ?_⟩
    simpa [E] using
      (section12_msigma_complement_isHall_sigma_compl (G := G) hM hcompSigmaW1U)
  have hUM : U ≤ M := hUE.trans hEM
  refine ⟨hUM, ?_⟩
  refine isHallSubgroup_of (G := M)
    (π := ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ))
    (H := U.subgroupOf M) ?_ ?_
  · intro p hpUsub
    have hcardUM : Nat.card (U.subgroupOf M) = Nat.card U :=
      natCard_subgroupOf_eq U M hUM
    have hpU : p.val ∣ Nat.card U := by
      simpa [hcardUM] using hpUsub
    have hcardUE : Nat.card (U.subgroupOf E) = Nat.card U :=
      natCard_subgroupOf_eq U E hUE
    have hpUE : p.val ∣ Nat.card (U.subgroupOf E) := by
      simpa [hcardUE] using hpU
    have hpκc : p ∈ (section14KappaPrimes M)ᶜ :=
      hUHallE.2.p_in_pi_of_p_dvd_card p hpUE
    have hpE : p.val ∣ Nat.card E := hpU.trans (Subgroup.card_dvd_of_le hUE)
    have hcardEM : Nat.card (E.subgroupOf M) = Nat.card E :=
      natCard_subgroupOf_eq E M hEM
    have hpEM : p.val ∣ Nat.card (E.subgroupOf M) := by
      simpa [hcardEM] using hpE
    have hpσc : p ∈ (section10SigmaPrimes M)ᶜ :=
      hEHallM.2.p_in_pi_of_p_dvd_card p hpEM
    rw [Set.mem_compl_iff, Set.mem_union]
    intro hpκσ
    exact hpκσ.elim hpκc hpσc
  · intro p hpπ hpidx
    have hpκc : p ∈ (section14KappaPrimes M)ᶜ := by
      rw [Set.mem_compl_iff]
      intro hpκ
      exact hpπ (Or.inl hpκ)
    have hpσc : p ∈ (section10SigmaPrimes M)ᶜ := by
      rw [Set.mem_compl_iff]
      intro hpσ
      exact hpπ (Or.inr hpσ)
    change p.val ∣ U.relIndex M at hpidx
    have hmul : U.relIndex E * E.relIndex M = U.relIndex M :=
      Subgroup.relIndex_mul_relIndex U E M hUE hEM
    have hprod : p.val ∣ U.relIndex E * E.relIndex M := by
      simpa [hmul] using hpidx
    rcases p.2.dvd_mul.mp hprod with hpidxUE | hpidxEM
    · exact (hUHallE.2.p_in_pi_of_p_dvd_index p
        (by simpa [Subgroup.relIndex] using hpidxUE)) hpκc
    · exact (hEHallM.2.p_in_pi_of_p_dvd_index p
        (by simpa [Subgroup.relIndex] using hpidxEM)) hpσc

/-- Source Type-P data in the non-`M_sigma` branch supplies a Section 16
`KUData` package whose complement is the same source subgroup `U`. -/
public theorem sourceTypeP_exists_KUData_of_not_le_msigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (_hUne : U ≠ ⊥)
    (hUnotσ : ¬ U ≤ section10Msigma M)
    (hsourceP : typePDefinitionData M MF U W1 W2) :
    ∃ K : Subgroup G, section16KUData M K U := by
  have hMFeq : MF = section10Msigma M :=
    sourceTypeP_MF_eq_msigma_of_not_le_msigma hM hMF hUnotσ hsourceP
  have hW1Hallκ : section12HallSubgroupIn (section14KappaPrimes M) W1 M :=
    sourceTypeP_W1_kappa_hall (G := G) hM hsourceP
  have hUHall : section12HallSubgroupIn
      ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) U M :=
    sourceTypeP_U_hall_from_W1_kappa_hall hM hMFeq hsourceP hW1Hallκ
  rcases sourceTypeP_W1_KUData_structural_fields hMFeq hsourceP with
    ⟨hcompW1USigma, hcompSigmaW1U, hUSigmaNormal, hUnormal⟩
  have hregular : section14ActsRegularlyOn W1 U :=
    sourceTypeP_W1_actsRegularlyOn_U hsourceP
  exact ⟨W1, hW1Hallκ, hcompW1USigma, hcompSigmaW1U, hUHall, hregular,
    hUSigmaNormal, hUnormal⟩

private theorem sourceTypeP_T6_of_not_le_msigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hUne : U ≠ ⊥)
    (hUnotσ : ¬ U ≤ section10Msigma M)
    (hsourceP : typePDefinitionData M MF U W1 W2) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
  rcases sourceTypeP_exists_KUData_of_not_le_msigma
      hM hMF hUne hUnotσ hsourceP with
    ⟨K, hKU⟩
  exact section16_typeCommon_T6_of_KUData_ne_bot
    (G := G) (M := M) (MF := MF) (K := K) (U := U) hM hMF hKU hUne

private theorem sourceTypeP_T6_of_U_ne_bot
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hUne : U ≠ ⊥)
    (hsourceP : typePDefinitionData M MF U W1 W2) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
  by_cases hUσ : U ≤ section10Msigma M
  · rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
      ⟨K, U0, hKU15⟩
    have hKU : section16KUData M K U0 := by
      simpa [section16KUData] using hKU15
    exact section16_typeCommon_T6_of_le_msigma
      (G := G) (M := M) (MF := MF) (K := K) (U := U0) (V := U)
      hM hMF hKU hUσ
  · exact sourceTypeP_T6_of_not_le_msigma hM hMF hUne hUσ hsourceP

/-- Source Type-P data supplies the BG T6 centralizer alternative for the same
source complement `U`. -/
public theorem sourceTypeP_T6_of_source_typeP
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hsourceP : typePDefinitionData M MF U W1 W2) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
  by_cases hUbot : U = ⊥
  · exact sourceTypeP_T6_of_U_eq_bot hUbot
  · exact sourceTypeP_T6_of_U_ne_bot hM hMF hUbot hsourceP

/-- BG Type II excludes BG Types III and IV for the same maximal subgroup. -/
public theorem section16_not_typeIII_or_typeIV_of_typeII
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hTypeII : section16TypeII M MF) :
    ¬ (section16TypeIII M MF ∨ section16TypeIV M MF) := by
  classical
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U, hKU15⟩
  have hKU : section16KUData M K U := by
    simpa [section16KUData] using hKU15
  have hprop :=
    proposition_16_1 (G := G) (M := M) (MF := MF) (K := K) (U := U)
      hM hMF hKU
  intro hIIIIV
  have hCaseP2 : section16CaseP2 K U := hprop.2.1.mp hTypeII
  have hCaseP1 : section16CaseP1 K U := (hprop.2.2.1.mp hIIIIV).1
  exact hCaseP2.2 hCaseP1.2

/-- Source Types III and IV are incompatible with a BG Type-II maximal subgroup. -/
public theorem not_source_typeIIIIV_of_typeII_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hTypeII : section16TypeII M MF) :
    ¬ (typeIIIDefinitionData M MF ∨ typeIVDefinitionData M MF) := by
  intro hSourceIIIIV
  have hT6 :
      ∀ {U W1 W2 : Subgroup G},
        typePDefinitionData M MF U W1 W2 →
          ∀ A0 A1 : Subgroup G,
            section16PrimeOrderSubgroupOf A0 U →
              section16PrimeOrderSubgroupOf A1 U →
                section16ConjugateSubgroupsIn ⊤ A0 A1 →
                  ¬ section16ConjugateSubgroupsIn M A0 A1 →
                    subgroupCentralizerIn MF A0 = ⊥ ∨
                      subgroupCentralizerIn MF A1 = ⊥ := by
    intro U W1 W2 hP
    exact sourceTypeP_T6_of_source_typeP hM hMF hP
  have hBGIIIIV : section16TypeIII M MF ∨ section16TypeIV M MF := by
    rcases hSourceIIIIV with hIII | hIV
    · exact Or.inl (section16TypeIII_of_source_typeIII_with_T6 hIII hT6)
    · exact Or.inr (section16TypeIV_of_source_typeIV_with_T6 hIV hT6)
  exact section16_not_typeIII_or_typeIV_of_typeII hM hMF hTypeII hBGIIIIV

/-- Source Type-P data is incompatible with source Type-I data for the same
maximal subgroup. -/
public theorem not_typeIDefinitionData_of_typeP_source_data
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    ¬ typeIDefinitionData M MF := by
  rintro ⟨_UF, _U1F, _U0F, hF, _hAltI⟩
  exact sourceTypeP_not_typeFData hP hF

/-- Source Type I determines the strengthened PF `(8.10)` choice `M_s = M_F`.

Each other source type contains Type-P data, which is incompatible with the
Type-F data in the Type-I package. -/
public theorem msChoiceSource_of_typeIDefinitionData
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hTypeI : typeIDefinitionData M MF) :
    msChoiceSource M MF MF := by
  refine Or.inl ⟨hTypeI, ?_, ?_, ?_, ?_, rfl⟩
  · rintro ⟨U, W1, W2, U1, U0, hP, _⟩
    exact not_typeIDefinitionData_of_typeP_source_data hP hTypeI
  · rintro ⟨U, W1, W2, hP, _⟩
    exact not_typeIDefinitionData_of_typeP_source_data hP hTypeI
  · rintro ⟨U, W1, W2, hP, _⟩
    exact not_typeIDefinitionData_of_typeP_source_data hP hTypeI
  · rintro ⟨U, W1, W2, hP, _⟩
    exact not_typeIDefinitionData_of_typeP_source_data hP hTypeI

/-- Package explicit Type-II source fields as source Type-II data. -/
public theorem typeIIDefinitionData_of_typeII_source_fields
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2)
    (hIItoIV : typeIIToIVSourceCondition M U W1)
    (hUcomm : IsMulCommutative U)
    (hUnorm : ¬ Subgroup.normalizer (U : Set G) ≤ M)
    (hF : ∃ U1 U0 : Subgroup G,
      typeFData (ambientDerivedSubgroup M) MF U U1 U0) :
    typeIIDefinitionData M MF := by
  rcases hF with ⟨U1, U0, hF⟩
  exact ⟨U, W1, W2, U1, U0, hP, hIItoIV, hUcomm, hUnorm, hF⟩

/-- Explicit Type-II source fields exclude source Type V. -/
public theorem not_typeVDefinitionData_of_typeII_source_fields
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2)
    (hIItoIV : typeIIToIVSourceCondition M U W1)
    (hUcomm : IsMulCommutative U)
    (hUnorm : ¬ Subgroup.normalizer (U : Set G) ≤ M)
    (hF : ∃ U1 U0 : Subgroup G,
      typeFData (ambientDerivedSubgroup M) MF U U1 U0) :
    ¬ typeVDefinitionData M MF := by
  have hSrcII : typeIIDefinitionData M MF :=
    typeIIDefinitionData_of_typeII_source_fields hP hIItoIV hUcomm hUnorm hF
  rintro ⟨U0, W1V, W2V, hPbot, hU0, _hAlt⟩
  subst U0
  exact not_typeIIDefinitionData_of_typeP_bot hPbot hSrcII

/-- Explicit selected Type-II source fields determine the PF `(8.10)` source
notation in the Type-II branch. -/
public theorem notation_8_10_source_data_of_typeII_source_fields
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hTypeII : section16TypeII M MF)
    (hP : typePDefinitionData M MF U W1 W2)
    (hIItoIV : typeIIToIVSourceCondition M U W1)
    (hUcomm : IsMulCommutative U)
    (hUnorm : ¬ Subgroup.normalizer (U : Set G) ≤ M)
    (hF : ∃ U1 U0 : Subgroup G,
      typeFData (ambientDerivedSubgroup M) MF U U1 U0) :
    notation_8_10_source_data M MF MF
      (section8CentralizerUnion (ambientDerivedSubgroup M) MF)
      (section8CentralizerUnion (ambientDerivedSubgroup M) MF ∪
        section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G))
      (a1Set MF) := by
  let A : Set G := section8CentralizerUnion (ambientDerivedSubgroup M) MF
  let A1 : Set G := a1Set MF
  let A0 : Set G :=
    A ∪ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G)
  have hSrcII : typeIIDefinitionData M MF :=
    typeIIDefinitionData_of_typeII_source_fields hP hIItoIV hUcomm hUnorm hF
  have hnotI : ¬ typeIDefinitionData M MF :=
    not_typeIDefinitionData_of_typeP_source_data hP
  have hnotIIIIV : ¬ (typeIIIDefinitionData M MF ∨ typeIVDefinitionData M MF) :=
    not_source_typeIIIIV_of_typeII_source_data hM hMF hTypeII
  have hnotIII : ¬ typeIIIDefinitionData M MF := by
    intro hIII
    exact hnotIIIIV (Or.inl hIII)
  have hnotIV : ¬ typeIVDefinitionData M MF := by
    intro hIV
    exact hnotIIIIV (Or.inr hIV)
  have hnotV : ¬ typeVDefinitionData M MF :=
    not_typeVDefinitionData_of_typeII_source_fields hP hIItoIV hUcomm hUnorm hF
  have hMsChoice : msChoiceSource M MF MF := by
    refine Or.inr (Or.inl ?_)
    exact ⟨hnotI, hSrcII, hnotIII, hnotIV, hnotV, rfl⟩
  refine ⟨hM, hMF, hMsChoice, rfl, Or.inr ?_⟩
  refine ⟨U, W1, W2, hP, Or.inl hSrcII, rfl, rfl, ?_⟩
  intro hLate
  exfalso
  rcases hLate with hIII | hLate
  · exact hnotIII hIII
  rcases hLate with hIV | hV
  · exact hnotIV hIV
  · exact hnotV hV

/-- Explicit selected Type-II source fields determine the PF `(8.10)` source
notation in the Type-II branch. -/
public theorem exists_notation_8_10_source_data_of_typeII_source_fields
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hTypeII : section16TypeII M MF)
    (hP : typePDefinitionData M MF U W1 W2)
    (hIItoIV : typeIIToIVSourceCondition M U W1)
    (hUcomm : IsMulCommutative U)
    (hUnorm : ¬ Subgroup.normalizer (U : Set G) ≤ M)
    (hF : ∃ U1 U0 : Subgroup G,
      typeFData (ambientDerivedSubgroup M) MF U U1 U0) :
    ∃ A A0 A1 : Set G,
      notation_8_10_source_data M MF MF A A0 A1 := by
  exact
    ⟨section8CentralizerUnion (ambientDerivedSubgroup M) MF,
      section8CentralizerUnion (ambientDerivedSubgroup M) MF ∪
        section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G),
      a1Set MF,
      notation_8_10_source_data_of_typeII_source_fields
        hM hMF hTypeII hP hIItoIV hUcomm hUnorm hF⟩

/-- The PF `(3.9)(a)` base-row conjugation endpoint retained for a selected
Section 8 character table. -/
@[expose] public def section8Hypothesis52BaseRowConjugateData
    {G : Type u} [Group G] [Finite G]
    {M Ms W1 W2 : Subgroup G} {A : Set G}
    (d52 : section8Hypothesis52FullData M Ms W1 W2 A) : Prop :=
  letI : Fintype d52.I := d52.instFintypeI
  letI : Fintype d52.J := d52.instFintypeJ
  letI : DecidableEq d52.I := d52.instDecidableEqI
  letI : DecidableEq d52.J := d52.instDecidableEqJ
  Section4Scratch.ambientRelativePF39BaseRowConjugateData
    d52.W d52.i0 d52.j0 d52.omega d52.sigma

/-- The two ambient PF `(3.9)` endpoints attached to the local Type-P table.
The proof first applies `(3.9)` on the subgroup image and then transports the
result back to the relative subgroup carrier. -/
public theorem ambientRelativePF39Data_of_typeP_local_table
    {G : Type u} [Group G] [Finite G]
    {M W1 W2 : Subgroup G}
    {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {omega : I → J →
      Section1.ClassFunction ((W1 ⊔ W2).subgroupOf M)}
    (hω :
      Section3.notation_3_3_statement
        (W1.subgroupOf M) (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M) I J i0 j0 omega)
    (h31 :
      Section3.hypothesis_3_1_statement
        (Section4Scratch.subgroupImage M (W1.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M)))
    {sigmaImage :
      Section1.ClassFunction
          (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M)) →ₗ[ℂ]
        Section1.ClassFunction G}
    {sigma :
      Section1.ClassFunction ((W1 ⊔ W2).subgroupOf M) →ₗ[ℂ]
        Section1.ClassFunction G}
    (hSigmaImage :
      Section3.theorem_3_2_map_statement
        (Section4Scratch.subgroupImage M (W1.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
        sigmaImage)
    (hSigmaDef :
      sigma =
        sigmaImage.comp
          (Section1.classFunctionLinearEquivOfMulEquiv
            (subgroupImageEquiv M ((W1 ⊔ W2).subgroupOf M))).toLinearMap) :
    Section4Scratch.ambientRelativePF39BaseColumnData
        (Nat.card (W1.subgroupOf M)) ((W1 ⊔ W2).subgroupOf M)
        i0 j0 omega sigma ∧
      Section4Scratch.ambientRelativePF39BaseRowConjugateData
        ((W1 ⊔ W2).subgroupOf M) i0 j0 omega sigma ∧
      Section4Scratch.ambientRelativePF39ConjugateData
        ((W1 ⊔ W2).subgroupOf M) sigma := by
  let e := subgroupImageEquiv M ((W1 ⊔ W2).subgroupOf M)
  let omegaImage : I → J →
      Section1.ClassFunction
        (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M)) :=
    fun i j => Section1.classFunctionLinearEquivOfMulEquiv e (omega i j)
  have hOmegaImage :
      Section3.notation_3_3_statement
        (Section4Scratch.subgroupImage M (W1.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
        I J i0 j0 omegaImage := by
    simpa [omegaImage, e] using
      notation_3_3_statement_of_subgroupImageEquiv
        (M := M) (W1 := W1.subgroupOf M) (W2 := W2.subgroupOf M)
        (W := (W1 ⊔ W2).subgroupOf M)
        (I := I) (J := J) (i0 := i0) (j0 := j0) (omega := omega) hω
  have hRat :
      ∀ {omega' :
          Section1.ClassFunction
            (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))}
          {a : ℕ},
        Section1.IsIrreducibleCharacterOnGroup omega' →
          Section3.exactCharacterValueOrder omega' a →
            ∀ g : G, (orderOf g).Coprime a →
              ∃ q : ℚ, sigmaImage omega' g = (q : ℂ) := by
    intro omega' a hIrred hOrder g hg
    exact Section3.pf39_rationality_of_theorem_3_2_map_statement
      (σ := sigmaImage) h31 hOmegaImage hSigmaImage
      (ω' := omega') (a := a) hIrred hOrder g hg
  have hConjBase :=
    baseColumn_conjugate_sigma_eq_of_theorem_3_2_map_statement
      h31 hOmegaImage hSigmaImage
  have hImageData0 :
      Section3.proposition_3_9_statement_c sigmaImage ∧
        (∀ g : G,
          Nat.Coprime (orderOf g)
            (Nat.card (Section4Scratch.subgroupImage M (W1.subgroupOf M))) →
          ∀ c : I → I,
            (∀ i : I,
              Section1.conjugateCharacter (omegaImage i j0) =
                omegaImage (c i) j0) →
            ∀ i : I, i ≠ i0 →
              sigmaImage (omegaImage (c i) j0) g =
                sigmaImage (omegaImage i j0) g) :=
    ambientPF39_image_pf39_data_of_image_notation_and_rationality
      (W1 := Section4Scratch.subgroupImage M (W1.subgroupOf M))
      (W2 := Section4Scratch.subgroupImage M (W2.subgroupOf M))
      (W := Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (omega := omegaImage) (sigma := sigmaImage)
      h31 hOmegaImage hSigmaImage hRat hConjBase
  have hImageIrred :
      ∀ i : I, Section1.IsIrreducibleCharacterOnGroup (omegaImage i j0) := by
    intro i
    exact Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
      e (hω.irreducible i j0)
  have hCard :
      Nat.card (Section4Scratch.subgroupImage M (W1.subgroupOf M)) =
        Nat.card (W1.subgroupOf M) :=
    Nat.card_congr (subgroupImageEquiv M (W1.subgroupOf M)).symm.toEquiv
  have hImageColumn :
      Section4Scratch.ambientRelativePF39BaseColumnData
        (Nat.card (W1.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
        i0 j0 omegaImage sigmaImage := by
    have hData :
        Section4Scratch.ambientRelativePF39BaseColumnData
          (Nat.card (Section4Scratch.subgroupImage M (W1.subgroupOf M)))
          (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
          i0 j0 omegaImage sigmaImage :=
      ambientRelativePF39BaseColumnData_of_pf39_base_column
        (W1 := Section4Scratch.subgroupImage M (W1.subgroupOf M))
        (W := Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
        (i0 := i0) (j0 := j0) (omega := omegaImage) (sigma := sigmaImage)
        hImageIrred hImageData0.1 hImageData0.2
    simpa [hCard] using hData
  have hImageRow :
      Section4Scratch.ambientRelativePF39BaseRowConjugateData
        (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
        i0 j0 omegaImage sigmaImage := by
    intro j _hj
    exact Section3.theorem_3_2_map_conjugateCharacter_of_irreducible
      h31 hOmegaImage sigmaImage hSigmaImage (hOmegaImage.irreducible i0 j)
  exact
    ⟨ambientRelativePF39BaseColumnData_of_subgroupImage
        (M := M) (W1 := W1.subgroupOf M)
        (W := (W1 ⊔ W2).subgroupOf M)
        (omega := omega) (sigmaImage := sigmaImage) (sigma := sigma)
        hImageColumn hSigmaDef,
      ambientRelativePF39BaseRowConjugateData_of_subgroupImage
        (M := M) (W := (W1 ⊔ W2).subgroupOf M)
        (omega := omega) (sigmaImage := sigmaImage) (sigma := sigma)
        hImageRow hSigmaDef,
      ambientRelativePF39ConjugateData_of_subgroupImage
        h31 hω hSigmaImage hSigmaDef⟩

/-- In the late PF `(8.10)` cases, the selected Type-P witness supplies the
full Section `(4.6)` package for `M_s = M'`, including the PF `(3.9.a)`
base-row endpoint and the original `A₀(M)` Dade transform. -/
public theorem section8Hypothesis52FullData_baseRow_of_late_notation_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms U W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1)
    (hWitness :
      notation_8_10_source_typeP_witness M MF Ms A A0 A1 U W1 W2)
    (hLate :
      typeIIIDefinitionData M MF ∨ typeIVDefinitionData M MF ∨
        typeVDefinitionData M MF) :
    ∃ d52 : section8Hypothesis52FullData M Ms W1 W2 A,
      section8Hypothesis52BaseRowConjugateData d52 ∧
        ∃ hA0M : Section2.Hypothesis2 A0 M d52.H_A0,
          ∀ α : Section1.ClassFunction M,
            d52.tau α =
              Section2.dadeTransform d52.H_A0 hA0M.subset_L α := by
  classical
  have hLateSets := hWitness.2.2.2.2 hLate
  have hA1A : A1 ⊆ A := by rw [hLateSets.2, hLateSets.1]
  have hAA0 : A ⊆ A0 := by
    rw [hWitness.2.2.2.1]
    exact Set.subset_union_left
  rcases exists_mixed_notation_8_14_source_data_of_theorem_8_13
      M MF Ms A A0 A1 (by infer_instance) hNotation hA1A hAA0 with
    ⟨R, tildeA, tildeA0, tildeA1, h14⟩
  have hSourceA0 :
      theorem_8_15_source_data M MF Ms A A0 A1 A0
        (section8DSet M A0) tildeA tildeA0 tildeA1 R :=
    ⟨hNotation, h14, Or.inl rfl⟩
  have hSourceA :
      theorem_8_15_source_data M MF Ms A A0 A1 A
        (section8DSet M A0) tildeA tildeA0 tildeA1 R :=
    ⟨hNotation, h14, Or.inr (Or.inl rfl)⟩
  have h46 := theorem_8_15_hypothesis_4_6_source
    (G := G) (M := M) (MF := MF) (Ms := Ms) (A := A) (A0 := A0)
    (A1 := A1) (D := section8DSet M A0) (tildeA := tildeA)
    (tildeA0 := tildeA0) (tildeA1 := tildeA1) (Achoice := A0)
    (R := R) (by infer_instance) hSourceA0 U W1 W2 hWitness
  have h22A0_raw : Section2.hypothesis_2_2_statement A0 M R :=
    theorem_8_15_hypothesis2 (G := G) (M := M) (MF := MF) (Ms := Ms)
      (A := A) (A0 := A0) (A1 := A1) (D := section8DSet M A0)
      (tildeA := tildeA) (tildeA0 := tildeA0) (tildeA1 := tildeA1)
      (Achoice := A0) (R := R) (by infer_instance) hSourceA0
  have h22A_raw : Section2.hypothesis_2_2_statement A M R :=
    theorem_8_15_hypothesis2 (G := G) (M := M) (MF := MF) (Ms := Ms)
      (A := A) (A0 := A0) (A1 := A1) (D := section8DSet M A0)
      (tildeA := tildeA) (tildeA0 := tildeA0) (tildeA1 := tildeA1)
      (Achoice := A) (R := R) (by infer_instance) hSourceA
  have hAimage :
      Section4Scratch.subgroupImageSet M (section8SubgroupSetPreimage M A) = A :=
    subgroupImageSet_section8SubgroupSetPreimage_eq h22A_raw.subset_L
  have h22A :
      Section2.hypothesis_2_2_statement
        (Section4Scratch.subgroupImageSet M (section8SubgroupSetPreimage M A))
        M R := by
    simpa [hAimage] using h22A_raw
  have hA0image :
      Section4Scratch.subgroupImageSet M (section8CyclicA0Set M W1 W2 A) =
        A0 := by
    rw [← h46.2.1]
    exact subgroupImageSet_section8SubgroupSetPreimage_eq h22A0_raw.subset_L
  have h22A0 :
      Section2.hypothesis_2_2_statement
        (Section4Scratch.subgroupImageSet M (section8CyclicA0Set M W1 W2 A))
        M R := by
    simpa [hA0image] using h22A0_raw
  let tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G :=
    Section2.dadeTransformLinear R h22A0.subset_L
  have hTauCyclicA0 :
      ∀ α : Section1.ClassFunction M,
        Section2.CFOn M
            (Section4Scratch.subgroupImageSet M
              (section8CyclicA0Set M W1 W2 A)) α →
          tau α = Section2.dadeTransform R h22A0.subset_L α := by
    intro α _hα
    exact Section2.dadeTransformLinear_apply R h22A0.subset_L α
  have hW2K : W2.subgroupOf M ≤ derivedSubgroup M :=
    theorem_8_15_typeP_W2_subgroupOf_le_derived hWitness.1
  have h31 :
      Section3.hypothesis_3_1_statement
        (Section4Scratch.subgroupImage M (W1.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M)) :=
    theorem_8_15_subgroupImage_hypothesis_3_1_of_typeP hWitness.1
  rcases exists_subgroupImage_section3_sigma_transport_data_with_image h31 with
    ⟨sigmaImage, sigma, hSigmaImage, hSigmaDef, hσIso, hσVirt, hσClass,
      hσPrin, hσAgreeCyc⟩
  rcases exists_typeP_local_section4_character_data hWitness.1 with
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, omega, hω, sigmaM, piChar, deltaSign, xChar,
      h43b, h43c, h43d, h45a, h45b⟩
  letI : Fintype I := instFintypeI
  letI : Fintype J := instFintypeJ
  letI : DecidableEq I := instDecidableEqI
  letI : DecidableEq J := instDecidableEqJ
  rcases typeII_primeDadeSupportedPackage_package_source_data_for_sigma
      hWitness.1 hNotation hWitness h46.2 h14 h22A0 hTauCyclicA0
      (sigma := sigma) hSigmaImage hSigmaDef with
    ⟨pkg, hPkgH, hPkgTau, _h22⟩
  have h47 :
      Section4Scratch.theorem_4_7_statement
        (derivedSubgroup M) (Ms.subgroupOf M)
        (section8SubgroupSetPreimage M A) :=
    Section4Scratch.theorem_4_7 _ _ _ _ _ _ h46.2.2.1
  have h48 :
      Section4Scratch.theorem_4_8_statement
        (W2.subgroupOf M) ((W1 ⊔ W2).subgroupOf M)
        (section8SubgroupSetPreimage M A)
        j0 omega sigma piChar deltaSign pkg.tau :=
    theorem_4_8_primeDade
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M)
      ((W1 ⊔ W2).subgroupOf M) (Ms.subgroupOf M)
      (section8SubgroupSetPreimage M A) i0 j0 omega sigmaM sigma
      piChar xChar deltaSign pkg.tau h31 hSigmaImage hSigmaDef
      pkg.h22CyclicA0 pkg.tau_cyclicA0 h46.2.2.1
      h45a hω h43b h43c h43d h47
  rcases ambientRelativePF39Data_of_typeP_local_table
      hω h31 hSigmaImage hSigmaDef with
    ⟨hAmbientPF39, hAmbientPF39BaseRow, hAmbientPF39Conjugate⟩
  let hFull :
      Section4Scratch.hypothesis_4_6_supported_statement M
        (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M) (Ms.subgroupOf M)
        (section8SubgroupSetPreimage M A) i0 j0 omega sigmaM sigma
        piChar xChar deltaSign pkg.tau R :=
    ⟨h46.2.2.1, hW2K, h31, hσIso, hσVirt, hσClass, hσPrin, h22A,
      hω, h43b, h43c, h43d, h45a, h45b,
      pkg.tau_agrees_cyclic, h48,
      pkg.tau_isometry_on_primeDadeA0,
      pkg.tau_maps_primeDadeA0_to_punctured,
      pkg.tau_maps_primeDadeA0_to_virtual, hAmbientPF39, hAmbientPF39BaseRow,
      hAmbientPF39Conjugate⟩
  subst A0
  have hTauA0Raw :
      ∀ α : Section1.ClassFunction M,
        tau α = Section2.dadeTransform R h22A0_raw.subset_L α := by
    intro α
    dsimp [tau]
    rw [Section2.dadeTransformLinear_apply]
  let d52 : section8Hypothesis52FullData M Ms W1 W2 A :=
    section8Hypothesis52FullData_of_supportedHypothesis
      (M := M) (Ms := Ms) (W1 := W1) (W2 := W2) (A := A)
      (W := (W1 ⊔ W2).subgroupOf M)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (omega := omega) (sigmaM := sigmaM) (sigma := sigma)
      (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
      (tau := pkg.tau) (H_A := R) (H_A0 := pkg.H_A0)
      pkg.h22CyclicA0 pkg.tau_cyclicA0 hσAgreeCyc rfl hFull
  have hA0M :
      Section2.Hypothesis2
        (Section4Scratch.subgroupImageSet M
          (section8CyclicA0Set M W1 W2 A)) M d52.H_A0 := by
    change Section2.Hypothesis2
      (Section4Scratch.subgroupImageSet M
        (section8CyclicA0Set M W1 W2 A)) M pkg.H_A0
    rw [hPkgH]
    exact h22A0_raw
  refine ⟨d52, ?_, hA0M, ?_⟩
  · change Section4Scratch.ambientRelativePF39BaseRowConjugateData
      ((W1 ⊔ W2).subgroupOf M) i0 j0 omega sigma
    exact hAmbientPF39BaseRow
  · intro α
    change pkg.tau α =
      Section2.dadeTransform pkg.H_A0 hA0M.subset_L α
    rw [hPkgTau, hPkgH]
    exact hTauA0Raw α


public theorem section8Hypothesis52FullData_baseRow_dadeRelative_of_typeII_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (_hMF : section16MFSubgroup M MF)
    (_hTypeII : section16TypeII M MF)
    (_hP : typePDefinitionData M MF U W1 W2)
    (_hIItoIV : typeIIToIVSourceCondition M U W1)
    (_hUcomm : IsMulCommutative U)
    (_hUnorm : ¬ Subgroup.normalizer (U : Set G) ≤ M)
    (_hF : ∃ U1 U0 : Subgroup G,
      typeFData (ambientDerivedSubgroup M) MF U U1 U0) :
    ∃ d52 : section8Hypothesis52FullData M MF W1 W2
        (section8CentralizerUnion (ambientDerivedSubgroup M) MF),
      section8Hypothesis52BaseRowConjugateData d52 ∧
        ∃ H : G → Subgroup G,
          ∃ hAMG : Section2.Hypothesis2 (section16ASet M U) M H,
            (∀ α : Section1.ClassFunction M,
              Section2.CFOn M (section16ASet M U) α →
                d52.tau α = Section2.dadeTransform H hAMG.subset_L α) ∧
            ∃ hA0M : Section2.Hypothesis2
                (section8CentralizerUnion (ambientDerivedSubgroup M) MF ∪
                  section16ConjugatesOfSetBySet
                    (section16HatW W1 W2) (M : Set G)) M d52.H_A0,
              ∀ α : Section1.ClassFunction M,
                d52.tau α =
                  Section2.dadeTransform d52.H_A0 hA0M.subset_L α := by
  let A : Set G := section8CentralizerUnion (ambientDerivedSubgroup M) MF
  let A0 : Set G :=
    A ∪ section16ConjugatesOfSetBySet (section16HatW W1 W2) (M : Set G)
  let A1 : Set G := a1Set MF
  have hSrcII : typeIIDefinitionData M MF :=
    typeIIDefinitionData_of_typeII_source_fields
      _hP _hIItoIV _hUcomm _hUnorm _hF
  have hnotIIIIV : ¬ (typeIIIDefinitionData M MF ∨ typeIVDefinitionData M MF) :=
    not_source_typeIIIIV_of_typeII_source_data _hM _hMF _hTypeII
  have hnotV : ¬ typeVDefinitionData M MF :=
    not_typeVDefinitionData_of_typeII_source_fields
      _hP _hIItoIV _hUcomm _hUnorm _hF
  have hNotation :
      notation_8_10_source_data M MF MF A A0 A1 := by
    simpa [A, A0, A1] using
      notation_8_10_source_data_of_typeII_source_fields
        _hM _hMF _hTypeII _hP _hIItoIV _hUcomm _hUnorm _hF
  rcases exists_notation_8_14_source_data_of_typeII_notation_source
      _hP hNotation with
    ⟨R, tildeA, tildeA0, tildeA1, h14⟩
  have hSourceA0 :
      theorem_8_15_source_data M MF MF A A0 A1 A0
        (section8DSet M A0) tildeA tildeA0 tildeA1 R :=
    ⟨hNotation, h14, Or.inl rfl⟩
  have hSourceA :
      theorem_8_15_source_data M MF MF A A0 A1 A
        (section8DSet M A0) tildeA tildeA0 tildeA1 R :=
    ⟨hNotation, h14, Or.inr (Or.inl rfl)⟩
  have hWitness :
      notation_8_10_source_typeP_witness M MF MF A A0 A1 U W1 W2 := by
    refine ⟨_hP, Or.inl hSrcII, rfl, rfl, ?_⟩
    intro hLate
    exfalso
    rcases hLate with hIII | hLate
    · exact hnotIIIIV (Or.inl hIII)
    rcases hLate with hIV | hV
    · exact hnotIIIIV (Or.inr hIV)
    · exact hnotV hV
  have h46 :
      section8Hypothesis46Source M W1 W2 MF A A0 ∧
        section8Hypothesis46Source M W1 W2 MF A A0 :=
    theorem_8_15_hypothesis_4_6_source
      (G := G) (M := M) (MF := MF) (Ms := MF) (A := A) (A0 := A0)
      (A1 := A1) (D := section8DSet M A0) (tildeA := tildeA)
      (tildeA0 := tildeA0) (tildeA1 := tildeA1) (Achoice := A0)
      (R := R) (by infer_instance) hSourceA0 U W1 W2 hWitness
  have h22A0_raw : Section2.hypothesis_2_2_statement A0 M R :=
    theorem_8_15_hypothesis2 (G := G) (M := M) (MF := MF) (Ms := MF)
      (A := A) (A0 := A0) (A1 := A1) (D := section8DSet M A0)
      (tildeA := tildeA) (tildeA0 := tildeA0) (tildeA1 := tildeA1)
      (Achoice := A0) (R := R) (by infer_instance) hSourceA0
  have h22A_raw : Section2.hypothesis_2_2_statement A M R :=
    theorem_8_15_hypothesis2 (G := G) (M := M) (MF := MF) (Ms := MF)
      (A := A) (A0 := A0) (A1 := A1) (D := section8DSet M A0)
      (tildeA := tildeA) (tildeA0 := tildeA0) (tildeA1 := tildeA1)
      (Achoice := A) (R := R) (by infer_instance) hSourceA
  have hAimage :
      Section4Scratch.subgroupImageSet M (section8SubgroupSetPreimage M A) =
        A :=
    subgroupImageSet_section8SubgroupSetPreimage_eq h22A_raw.subset_L
  have h22A :
      Section2.hypothesis_2_2_statement
        (Section4Scratch.subgroupImageSet M (section8SubgroupSetPreimage M A))
        M R := by
    simpa [hAimage] using h22A_raw
  have hA0image :
      Section4Scratch.subgroupImageSet M
          (section8CyclicA0Set M W1 W2 A) = A0 := by
    rw [← h46.1.1]
    exact subgroupImageSet_section8SubgroupSetPreimage_eq h22A0_raw.subset_L
  have h22A0 :
      Section2.hypothesis_2_2_statement
        (Section4Scratch.subgroupImageSet M
          (section8CyclicA0Set M W1 W2 A)) M R := by
    simpa [hA0image] using h22A0_raw
  have hTauCyclicA0 :
      ∀ α : Section1.ClassFunction M,
        Section2.CFOn M
            (Section4Scratch.subgroupImageSet M
              (section8CyclicA0Set M W1 W2 A)) α →
          Section2.dadeTransformLinear R h22A0.subset_L α =
            Section2.dadeTransform R h22A0.subset_L α := by
    intro α _hα
    exact Section2.dadeTransformLinear_apply R h22A0.subset_L α
  have hW2K : W2.subgroupOf M ≤ derivedSubgroup M :=
    theorem_8_15_typeP_W2_subgroupOf_le_derived
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) _hP
  have h31 :
      Section3.hypothesis_3_1_statement
        (Section4Scratch.subgroupImage M (W1.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2.subgroupOf M))
        (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M)) :=
    theorem_8_15_subgroupImage_hypothesis_3_1_of_typeP
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) _hP
  rcases exists_subgroupImage_section3_sigma_transport_data_with_image h31 with
    ⟨sigmaImage, sigma, hSigmaImage, hSigmaDef, hσIso, hσVirt, hσClass,
      hσPrin, hσAgreeCyc⟩
  rcases exists_typeP_local_section4_character_data
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) _hP with
    ⟨I, J, instFintypeI, instFintypeJ, instDecidableEqI, instDecidableEqJ,
      i0, j0, omega, hω, sigmaM, piChar, deltaSign, xChar,
      h43b, h43c, h43d, h45a, h45b⟩
  letI : Fintype I := instFintypeI
  letI : Fintype J := instFintypeJ
  letI : DecidableEq I := instDecidableEqI
  letI : DecidableEq J := instDecidableEqJ
  rcases typeII_primeDadeSupportedPackage_package_source_data_for_sigma
      _hP hNotation hWitness h46.1 h14 h22A0 hTauCyclicA0
      (sigma := sigma) hSigmaImage hSigmaDef with
    ⟨pkg, hPkgH, hPkgTau, _hPkgHyp⟩
  have hASetSub :
      section16ASet M U ⊆
        Section4Scratch.subgroupImageSet M
          (section8CyclicA0Set M W1 W2 A) :=
    typeII_section16ASet_subset_cyclicA0_image_source_data
      _hM _hMF _hTypeII hSrcII _hP hNotation hWitness h46.1
  have hASetNorm : M ≤ Section2.setNormalizer (section16ASet M U) := by
    by_cases hUσ : U ≤ section10Msigma M
    · exact typeII_section16ASet_le_setNormalizer_source_data
        _hM _hP hUσ
    · have hUne : U ≠ ⊥ := by
        intro hUbot
        exact hUσ (by rw [hUbot]; exact bot_le)
      rcases sourceTypeP_exists_KUData_of_not_le_msigma
          _hM _hMF hUne hUσ _hP with
        ⟨K, hKU⟩
      exact section2_setNormalizer_le_of_subgroupNormalizer
        (section16_ASet_le_normalizer_public (G := G) _hM hKU)
  have hAMG : Section2.Hypothesis2 (section16ASet M U) M pkg.H_A0 :=
    Section2.proposition_2_11_hypothesis pkg.h22CyclicA0 hASetSub hASetNorm
  have hTauAMG :
      ∀ α : Section1.ClassFunction M,
        Section2.CFOn M (section16ASet M U) α →
          pkg.tau α =
            Section2.dadeTransform pkg.H_A0 hAMG.subset_L α := by
    intro α hα
    have hRestrict :
        Section2.dadeTransform pkg.H_A0 pkg.h22CyclicA0.subset_L α =
          Section2.dadeTransform pkg.H_A0 hAMG.subset_L α :=
      ((Section2.proposition_2_11
          (Section4Scratch.subgroupImageSet M
            (section8CyclicA0Set M W1 W2 A))
          (section16ASet M U) M pkg.H_A0)
          hASetSub hASetNorm pkg.h22CyclicA0).2
        pkg.h22CyclicA0.subset_L hAMG.subset_L α hα
    exact (pkg.tau_cyclicA0 α
        ⟨hα.1, fun m hmA0 => hα.2 m (fun hmA => hmA0 (hASetSub hmA))⟩).trans
      hRestrict
  have h47 :
      Section4Scratch.theorem_4_7_statement
        (derivedSubgroup M) (MF.subgroupOf M)
        (section8SubgroupSetPreimage M A) :=
    Section4Scratch.theorem_4_7 _ _ _ _ _ _ h46.1.2.1
  have h48 :
      Section4Scratch.theorem_4_8_statement
        (W2.subgroupOf M) ((W1 ⊔ W2).subgroupOf M)
        (section8SubgroupSetPreimage M A)
        j0 omega sigma piChar deltaSign pkg.tau :=
    theorem_4_8_primeDade
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M)
      ((W1 ⊔ W2).subgroupOf M) (MF.subgroupOf M)
      (section8SubgroupSetPreimage M A) i0 j0 omega sigmaM sigma
      piChar xChar deltaSign pkg.tau h31 hSigmaImage hSigmaDef
      pkg.h22CyclicA0 pkg.tau_cyclicA0 h46.1.2.1
      h45a hω h43b h43c h43d h47
  have hAmbientPF39 :
      Section4Scratch.ambientRelativePF39BaseColumnData
        (Nat.card (W1.subgroupOf M))
        ((W1 ⊔ W2).subgroupOf M) i0 j0 omega sigma := by
    let e := subgroupImageEquiv M ((W1 ⊔ W2).subgroupOf M)
    let omegaImage : I → J →
        Section1.ClassFunction
          (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M)) :=
      fun i j => Section1.classFunctionLinearEquivOfMulEquiv e (omega i j)
    have hOmegaImage :
        Section3.notation_3_3_statement
          (Section4Scratch.subgroupImage M (W1.subgroupOf M))
          (Section4Scratch.subgroupImage M (W2.subgroupOf M))
          (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
          I J i0 j0 omegaImage := by
      simpa [omegaImage, e] using
        notation_3_3_statement_of_subgroupImageEquiv
          (M := M) (W1 := W1.subgroupOf M) (W2 := W2.subgroupOf M)
          (W := (W1 ⊔ W2).subgroupOf M)
          (I := I) (J := J) (i0 := i0) (j0 := j0) (omega := omega) hω
    have hRat :
        ∀ {omega' :
            Section1.ClassFunction
              (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))}
            {a : ℕ},
          Section1.IsIrreducibleCharacterOnGroup omega' →
            Section3.exactCharacterValueOrder omega' a →
              ∀ g : G, (orderOf g).Coprime a →
                ∃ q : ℚ, sigmaImage omega' g = (q : ℂ) := by
      intro omega' a hIrred hOrder g hg
      exact
        Section3.pf39_rationality_of_theorem_3_2_map_statement
          (σ := sigmaImage) h31 hOmegaImage hSigmaImage
          (ω' := omega') (a := a) hIrred hOrder g hg
    have hConjBase :=
      baseColumn_conjugate_sigma_eq_of_theorem_3_2_map_statement
        h31 hOmegaImage hSigmaImage
    have hImageData0 :
        Section3.proposition_3_9_statement_c sigmaImage ∧
          (∀ g : G,
            Nat.Coprime (orderOf g)
              (Nat.card (Section4Scratch.subgroupImage M (W1.subgroupOf M))) →
            ∀ c : I → I,
              (∀ i : I,
                Section1.conjugateCharacter (omegaImage i j0) =
                  omegaImage (c i) j0) →
              ∀ i : I, i ≠ i0 →
                sigmaImage (omegaImage (c i) j0) g =
                  sigmaImage (omegaImage i j0) g) :=
      ambientPF39_image_pf39_data_of_image_notation_and_rationality
        (W1 := Section4Scratch.subgroupImage M (W1.subgroupOf M))
        (W2 := Section4Scratch.subgroupImage M (W2.subgroupOf M))
        (W := Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        (omega := omegaImage) (sigma := sigmaImage)
        h31 hOmegaImage hSigmaImage hRat hConjBase
    have hImageIrred :
        ∀ i : I, Section1.IsIrreducibleCharacterOnGroup (omegaImage i j0) := by
      intro i
      exact Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
        e (hω.irreducible i j0)
    have hCard :
        Nat.card (Section4Scratch.subgroupImage M (W1.subgroupOf M)) =
          Nat.card (W1.subgroupOf M) :=
      Nat.card_congr (subgroupImageEquiv M (W1.subgroupOf M)).symm.toEquiv
    have hImageData :
        Section4Scratch.ambientRelativePF39BaseColumnData
          (Nat.card (W1.subgroupOf M))
          (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
          i0 j0 omegaImage sigmaImage := by
      have hData :
          Section4Scratch.ambientRelativePF39BaseColumnData
            (Nat.card (Section4Scratch.subgroupImage M (W1.subgroupOf M)))
            (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
            i0 j0 omegaImage sigmaImage :=
        ambientRelativePF39BaseColumnData_of_pf39_base_column
          (W1 := Section4Scratch.subgroupImage M (W1.subgroupOf M))
          (W := Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
          (i0 := i0) (j0 := j0)
          (omega := omegaImage) (sigma := sigmaImage)
          hImageIrred hImageData0.1 hImageData0.2
      simpa [hCard] using hData
    exact
      ambientRelativePF39BaseColumnData_of_subgroupImage
        (M := M) (W1 := W1.subgroupOf M)
        (W := (W1 ⊔ W2).subgroupOf M)
        (omega := omega) (sigmaImage := sigmaImage) (sigma := sigma)
        hImageData hSigmaDef
  have hAmbientPF39BaseRow :
      Section4Scratch.ambientRelativePF39BaseRowConjugateData
        ((W1 ⊔ W2).subgroupOf M) i0 j0 omega sigma := by
    let e := subgroupImageEquiv M ((W1 ⊔ W2).subgroupOf M)
    let omegaImage : I → J →
        Section1.ClassFunction
          (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M)) :=
      fun i j => Section1.classFunctionLinearEquivOfMulEquiv e (omega i j)
    have hOmegaImage :
        Section3.notation_3_3_statement
          (Section4Scratch.subgroupImage M (W1.subgroupOf M))
          (Section4Scratch.subgroupImage M (W2.subgroupOf M))
          (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
          I J i0 j0 omegaImage := by
      simpa [omegaImage, e] using
        notation_3_3_statement_of_subgroupImageEquiv
          (M := M) (W1 := W1.subgroupOf M) (W2 := W2.subgroupOf M)
          (W := (W1 ⊔ W2).subgroupOf M)
          (I := I) (J := J) (i0 := i0) (j0 := j0) (omega := omega) hω
    have hImageData :
        Section4Scratch.ambientRelativePF39BaseRowConjugateData
          (Section4Scratch.subgroupImage M ((W1 ⊔ W2).subgroupOf M))
          i0 j0 omegaImage sigmaImage := by
      intro j _hj
      exact Section3.theorem_3_2_map_conjugateCharacter_of_irreducible
        h31 hOmegaImage sigmaImage hSigmaImage
        (hOmegaImage.irreducible i0 j)
    exact
      ambientRelativePF39BaseRowConjugateData_of_subgroupImage
        (M := M) (W := (W1 ⊔ W2).subgroupOf M)
        (omega := omega) (sigmaImage := sigmaImage) (sigma := sigma)
        hImageData hSigmaDef
  have hAmbientPF39Conjugate :
      Section4Scratch.ambientRelativePF39ConjugateData
        ((W1 ⊔ W2).subgroupOf M) sigma :=
    ambientRelativePF39ConjugateData_of_subgroupImage
      h31 hω hSigmaImage hSigmaDef
  let hFull :
      Section4Scratch.hypothesis_4_6_supported_statement M
        (derivedSubgroup M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M)
        (MF.subgroupOf M)
        (section8SubgroupSetPreimage M A)
        i0 j0 omega sigmaM sigma piChar xChar deltaSign pkg.tau R :=
    ⟨h46.1.2.1, hW2K, h31, hσIso, hσVirt, hσClass, hσPrin,
      h22A,
      hω, h43b, h43c, h43d, h45a, h45b,
      pkg.tau_agrees_cyclic,
      h48,
      pkg.tau_isometry_on_primeDadeA0,
      pkg.tau_maps_primeDadeA0_to_punctured,
      pkg.tau_maps_primeDadeA0_to_virtual,
      hAmbientPF39, hAmbientPF39BaseRow, hAmbientPF39Conjugate⟩
  let d52 : section8Hypothesis52FullData M MF W1 W2 A :=
    section8Hypothesis52FullData_of_supportedHypothesis
      (M := M) (Ms := MF) (W1 := W1) (W2 := W2) (A := A)
      (W := (W1 ⊔ W2).subgroupOf M)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (omega := omega) (sigmaM := sigmaM) (sigma := sigma)
      (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
      (tau := pkg.tau) (H_A := R) (H_A0 := pkg.H_A0)
      pkg.h22CyclicA0 pkg.tau_cyclicA0 hσAgreeCyc rfl hFull
  have hTauA0Raw :
      ∀ α : Section1.ClassFunction M,
        Section2.dadeTransformLinear R h22A0.subset_L α =
          Section2.dadeTransform R h22A0_raw.subset_L α := by
    intro α
    exact dadeTransformLinear_apply_of_carrier_eq
      hA0image h22A0.subset_L h22A0_raw.subset_L α
  have hA0M :
      Section2.Hypothesis2
        (A ∪ section16ConjugatesOfSetBySet
          (section16HatW W1 W2) (M : Set G)) M d52.H_A0 := by
    change Section2.Hypothesis2 A0 M pkg.H_A0
    rw [hPkgH]
    exact h22A0_raw
  refine ⟨d52, ?_, pkg.H_A0, hAMG, ?_, ?_, ?_⟩
  · change Section4Scratch.ambientRelativePF39BaseRowConjugateData
      ((W1 ⊔ W2).subgroupOf M) i0 j0 omega sigma
    exact hAmbientPF39BaseRow
  · intro α hα
    change pkg.tau α =
      Section2.dadeTransform pkg.H_A0 hAMG.subset_L α
    exact hTauAMG α hα
  · simpa [A] using hA0M
  · intro α
    change pkg.tau α =
      Section2.dadeTransform pkg.H_A0 hA0M.subset_L α
    rw [hPkgTau, hPkgH]
    exact hTauA0Raw α

/-- Source-level Type-II full Section `(4.6)`/Dade package for the selected
Type-P witness. -/
public theorem section8Hypothesis52FullData_dadeRelative_of_typeII_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (_hMF : section16MFSubgroup M MF)
    (_hTypeII : section16TypeII M MF)
    (_hP : typePDefinitionData M MF U W1 W2)
    (_hIItoIV : typeIIToIVSourceCondition M U W1)
    (_hUcomm : IsMulCommutative U)
    (_hUnorm : ¬ Subgroup.normalizer (U : Set G) ≤ M)
    (_hF : ∃ U1 U0 : Subgroup G,
      typeFData (ambientDerivedSubgroup M) MF U U1 U0) :
    ∃ d52 : section8Hypothesis52FullData M MF W1 W2
        (section8CentralizerUnion (ambientDerivedSubgroup M) MF),
      ∃ H : G → Subgroup G,
        ∃ hAMG : Section2.Hypothesis2 (section16ASet M U) M H,
          ∀ α : Section1.ClassFunction M,
            Section2.CFOn M (section16ASet M U) α →
              d52.tau α = Section2.dadeTransform H hAMG.subset_L α := by
  rcases
      section8Hypothesis52FullData_baseRow_dadeRelative_of_typeII_source_data
        _hM _hMF _hTypeII _hP _hIItoIV _hUcomm _hUnorm _hF with
    ⟨d52, _hBaseRow, H, hAMG, hTau, _hA0M, _hTauA0⟩
  exact ⟨d52, H, hAMG, hTau⟩

end CFSG.Section8
