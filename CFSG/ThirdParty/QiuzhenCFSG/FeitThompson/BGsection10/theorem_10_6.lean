module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_4_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Theorem 10.6 from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [IsMinCE G] in
private theorem CFSG.section10_hasPLengthOne_of_quotient_Op_coprime
    {H : Type*} [Group H] [Finite H] {p : Nat.Primes}
    (hcop : Nat.Coprime p.val (Nat.card (H ⧸ Op_p'p p.val H))) :
    HasPLengthOne p.val H := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have htop_le_core :
      (⊤ : Subgroup (H ⧸ Op_p'p p.val H)) ≤
        pPrimeCore p.val (H ⧸ Op_p'p p.val H) := by
    exact le_sSup
      ⟨(inferInstance : (⊤ : Subgroup (H ⧸ Op_p'p p.val H)).Normal),
        by simpa using hcop⟩
  have hcore_top : pPrimeCore p.val (H ⧸ Op_p'p p.val H) = ⊤ :=
    top_unique htop_le_core
  simp [HasPLengthOne, Op_p'pp', hcore_top]

omit [IsMinCE G] in
private theorem CFSG.section10_hasPLengthOne_of_primeRank_le_two
    {H : Type*} [Group H] [Finite H] {p : Nat.Primes}
    (hsolv : Group.IsSolvable H) (hodd : Odd (Nat.card H))
    (hrank : primeRank p.val H ≤ 2) :
    HasPLengthOne p.val H := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  by_cases hp_mem : p.val ∣ Nat.card H
  · exact section10_hasPLengthOne_of_quotient_Op_coprime
      (p := p) ((theorem_4_18_e (G := H) (p := p.val) hsolv hodd hp_mem hrank).1)
  · exact hasPLengthOne_of_coprime_card (G := H) (p := p.val)
      ((p.property.coprime_iff_not_dvd).2 hp_mem)

omit [IsMinCE G] in
public theorem CFSG.section10_exists_maximalSubgroupsContaining_of_ne_top
    {H : Subgroup G} (hHproper : H ≠ ⊤) :
    ∃ M : Subgroup G, M ∈ section9MaximalSubgroupsContaining H := by
  rcases eq_top_or_exists_le_coatom H with hHtop | ⟨M, hMcoatom, hHM⟩
  · exact False.elim (hHproper hHtop)
  · refine ⟨M, ?_⟩
    exact ⟨hMcoatom, hHM⟩

omit [IsMinCE G] in
private theorem CFSG.section10_hasPLengthOne_of_le_hasPLengthOne
    {H M : Subgroup G} {p : Nat.Primes} (hHM : H ≤ M)
    (hMplen : HasPLengthOne p.val M) :
    HasPLengthOne p.val H := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let Hsub : Subgroup M := H.subgroupOf M
  have hHsub : HasPLengthOne p.val Hsub :=
    lemma_1_21_a (G := M) p.val Hsub hMplen
  exact hasPLengthOne_of_equiv (p := p.val)
    (Subgroup.subgroupOfEquivOfLe (H := H) (K := M) hHM) hHsub

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_malpha_subgroupOf_eq
    (M : Subgroup G) :
    (section10Malpha M).subgroupOf M = section10MalphaSubgroup M := by
  ext x
  constructor
  · intro hx
    change ((x : M) : G) ∈ (section10MalphaSubgroup M).map M.subtype at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    have hxy : x = y := Subtype.ext hyx.symm
    simpa [hxy] using hy
  · intro hx
    change ((x : M) : G) ∈ (section10MalphaSubgroup M).map M.subtype
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_zpowers_subgroupOf_eq
    {M : Subgroup G} {x : G} (hxM : x ∈ M) :
    (Subgroup.zpowers x).subgroupOf M = Subgroup.zpowers (⟨x, hxM⟩ : M) := by
  let xM : M := ⟨x, hxM⟩
  ext y
  constructor
  · intro hy
    have hyG : ((y : M) : G) ∈ Subgroup.zpowers x := by
      simpa [Subgroup.mem_subgroupOf] using hy
    rcases hyG with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    simpa [xM] using hn
  · intro hy
    rcases hy with ⟨n, hn⟩
    change ((y : M) : G) ∈ Subgroup.zpowers x
    refine ⟨n, ?_⟩
    simpa [xM] using congrArg (fun z : M => (z : G)) hn

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_isZGroup_malphaSubgroup_centralizer_zpowers_of_ambient
    {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (hZ : IsZGroup ↥(elementCentralizerIn (section10Malpha M) x)) :
    IsZGroup ↥(subgroupCentralizerIn (section10MalphaSubgroup M)
      (Subgroup.zpowers (⟨x, hxM⟩ : M))) := by
  classical
  let R : Subgroup G := Subgroup.zpowers x
  have hR_le_M : R ≤ M := by
    simpa [R] using (Subgroup.zpowers_le_of_mem hxM)
  have hZamb : IsZGroup ↥(subgroupCentralizerIn (section10Malpha M) R) := by
    have hZ' := hZ
    rw [section10_elementCentralizerIn_eq_subgroupCentralizerIn_zpowers
      (section10Malpha M) x] at hZ'
    simpa [R] using hZ'
  let : IsZGroup ↥(subgroupCentralizerIn (section10Malpha M) R) := hZamb
  have hZsub :
      IsZGroup ↥(subgroupCentralizerIn ((section10Malpha M).subgroupOf M)
        (R.subgroupOf M)) :=
    isZGroup_subgroupCentralizerIn_subgroupOf M (section10Malpha M) R hR_le_M
  have hRsub :
      R.subgroupOf M = Subgroup.zpowers (⟨x, hxM⟩ : M) := by
    simpa [R] using section10_zpowers_subgroupOf_eq (M := M) hxM
  have hZsub' := hZsub
  rw [section10_malpha_subgroupOf_eq M, hRsub] at hZsub'
  exact hZsub'

private theorem CFSG.section10_coprime_quotient_malpha_of_mem_alpha
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) {p : Nat.Primes}
    (hpα : p ∈ section10AlphaPrimes M) :
    Nat.Coprime p.val (Nat.card (M ⧸ section10MalphaSubgroup M)) := by
  classical
  have hHall : IsHallSubgroup (section10AlphaPrimes M) (section10MalphaSubgroup M) :=
    (theorem_10_2_a hM).2
  have hnot : ¬ p.val ∣ (section10MalphaSubgroup M).index := by
    intro hpidx
    exact (hHall.p_in_pi_of_p_dvd_index p hpidx) hpα
  simpa [Subgroup.index_eq_card] using (p.property.coprime_iff_not_dvd).2 hnot

private theorem CFSG.section10_malpha_hasPLengthOne_of_high_primeRank
    {M : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hαrank : 2 < primeRank p.val M) :
    HasPLengthOne p.val (section10MalphaSubgroup M) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let A : Subgroup M := section10MalphaSubgroup M
  have : A.Normal := by
    dsimp [A]
    infer_instance
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  let : Group.IsSolvable M := hMsolv
  have hModd : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hthree : 3 ≤ primeRank p.val M := by omega
  have hp_dvd_M : p.val ∣ Nat.card M :=
    section10_prime_dvd_card_of_three_le_primeRank_pre
      (p := p.val) (R := M) hthree
  have hpα : p ∈ section10AlphaPrimes M := by
    simpa [section10AlphaPrimes, subgroupPrimeSet] using
      (show p ∈ section10AlphaPrimes M from ⟨hp_dvd_M, hαrank⟩)
  have hHallA : IsHallSubgroup (section10AlphaPrimes M) A := by
    simpa [A] using (theorem_10_2_a hM).2
  have hp_not_Aidx : ¬ p.val ∣ A.index := by
    intro hpidx
    exact (hHallA.p_in_pi_of_p_dvd_index p hpidx) hpα
  have hp_prod : p.val ∣ Nat.card A * A.index := by
    rw [A.card_mul_index]
    exact hp_dvd_M
  have hp_dvd_A : p.val ∣ Nat.card A := by
    rcases p.property.dvd_or_dvd hp_prod with hpA | hpidx
    · exact hpA
    · exact False.elim (hp_not_Aidx hpidx)
  have hA_ne_bot : A ≠ ⊥ := by
    intro hAbot
    have hAcard : Nat.card A = 1 := (Subgroup.card_eq_one (H := A)).2 hAbot
    exact p.property.not_dvd_one (by simpa [hAcard] using hp_dvd_A)
  have hMalpha_ne : section10Malpha M ≠ ⊥ := by
    simpa [A, section10Malpha] using
      section10_map_subtype_ne_bot_of_ne_bot (G := G) (M := M) (K := A) hA_ne_bot
  have hA_le_D : A ≤ derivedSubgroup M := by
    dsimp [A]
    exact (section10_malphaSubgroup_le_msigmaSubgroup hM).trans
      (section10_msigmaSubgroup_le_derivedSubgroup hM)
  obtain ⟨K, hAK⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := A) hHallA.card_coprime_index
  have hcopAK : Nat.Coprime (Nat.card A) (Nat.card K) := by
    have hidx : A.index = Nat.card K := hAK.symm.index_eq_card
    simpa [hidx] using hHallA.card_coprime_index
  have hcardM_ne_one : Nat.card M ≠ 1 := by
    intro hcard
    exact p.property.not_dvd_one (by simpa [hcard] using hp_dvd_M)
  have hcardM_gt_one : 1 < Nat.card M := by
    exact lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.card_pos (α := M)))
      (Ne.symm hcardM_ne_one)
  let : Nontrivial M := (Finite.one_lt_card_iff_nontrivial (α := M)).1 hcardM_gt_one
  have hDlt : derivedSubgroup M < ⊤ := by
    simpa [derivedSubgroup] using
      (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := M))
  have hDneTop : derivedSubgroup M ≠ ⊤ := hDlt.ne
  let : Nontrivial (M ⧸ derivedSubgroup M) :=
    (QuotientGroup.nontrivial_iff (G := M) (N := derivedSubgroup M)).2 hDneTop
  have hquot_gt_one : 1 < Nat.card (M ⧸ derivedSubgroup M) :=
    (Finite.one_lt_card_iff_nontrivial (α := M ⧸ derivedSubgroup M)).2 inferInstance
  have hquot_ne_one : Nat.card (M ⧸ derivedSubgroup M) ≠ 1 :=
    ne_of_gt hquot_gt_one
  obtain ⟨q0, hq0prime, hq0dvd⟩ :=
    Nat.exists_prime_and_dvd hquot_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  have : Fact q.val.Prime := ⟨q.property⟩
  have hq_dvd_Dquot : q.val ∣ Nat.card (M ⧸ derivedSubgroup M) := by
    simpa [q] using hq0dvd
  have hqM : q ∈ subgroupPrimeSet M := by
    exact hq_dvd_Dquot.trans
      (Subgroup.card_quotient_dvd_card (s := derivedSubgroup M))
  have hq_not_alpha : q ∉ section10AlphaPrimes M :=
    lemma_10_4_a hM hq_dvd_Dquot
  have hq_not_sigma : q ∉ section10SigmaPrimes M := by
    intro hqσ
    exact section10_sigma_not_dvd_quotient_derived hM hqσ hq_dvd_Dquot
  have hDidx_dvd_Aidx : (derivedSubgroup M).index ∣ A.index :=
    Subgroup.index_dvd_of_le hA_le_D
  have hDquot_dvd_Aquot :
      Nat.card (M ⧸ derivedSubgroup M) ∣ Nat.card (M ⧸ A) := by
    simpa [Subgroup.index_eq_card] using hDidx_dvd_Aidx
  have hq_dvd_Aquot : q.val ∣ Nat.card (M ⧸ A) :=
    hq_dvd_Dquot.trans hDquot_dvd_Aquot
  have hcardK_eq_Aquot : Nat.card K = Nat.card (M ⧸ A) := by
    have hidx : A.index = Nat.card K := hAK.symm.index_eq_card
    simpa [Subgroup.index_eq_card] using hidx.symm
  have hq_dvd_K : q.val ∣ Nat.card K := by
    rw [hcardK_eq_Aquot]
    exact hq_dvd_Aquot
  let Q : Sylow q.val K := Classical.choice (Sylow.nonempty (p := q.val) (G := K))
  let QK : Subgroup K := (Q : Subgroup K)
  let Qmap : Subgroup M := QK.map K.subtype
  have hQmap_p : IsPGroup q.val Qmap := by
    exact IsPGroup.map (p := q.val) (H := QK) Q.isPGroup' K.subtype
  have hQmap_le_K : Qmap ≤ K := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨z, _hz, rfl⟩
    exact z.property
  have hq_not_Acard : ¬ q.val ∣ Nat.card A := by
    intro hqA
    exact hq_not_alpha (hHallA.p_in_pi_of_p_dvd_card q hqA)
  have hq_not_Kidx : ¬ q.val ∣ K.index := by
    intro hqidx
    exact hq_not_Acard (by
      simpa [hAK.index_eq_card] using hqidx)
  have hQmap_index : Qmap.index = QK.index * K.index := by
    simpa [Qmap, QK] using
      (Subgroup.index_map_subtype (H := K) (K := QK))
  have hQmap_not_index : ¬ q.val ∣ Qmap.index := by
    intro hqidx
    have hqprod : q.val ∣ QK.index * K.index := by
      simpa [hQmap_index] using hqidx
    rcases q.property.dvd_or_dvd hqprod with hqQ | hqK
    · exact Q.not_dvd_index hqQ
    · exact hq_not_Kidx hqK
  let P : Sylow q.val M := hQmap_p.toSylow hQmap_not_index
  have hP_eq : (P : Subgroup M) = Qmap := rfl
  obtain ⟨x, hxΩ, hxne, _hfamily, hZ⟩ :=
    lemma_10_4_b (G := G) hM hqM P hq_not_sigma hMalpha_ne
  have hxPG : x ∈ section10AmbientSylowSubgroup M P :=
    section10_mem_omegaOneCenter_le_ambient_sylow (G := G) (p := q) hxΩ
  change x ∈ (P : Subgroup M).map M.subtype at hxPG
  rcases Subgroup.mem_map.mp hxPG with ⟨xM, hxP, hx_eq⟩
  have hxM : x ∈ M := by
    rw [← hx_eq]
    exact xM.property
  let xM0 : M := ⟨x, hxM⟩
  have hxM0_eq : xM0 = xM := by
    apply Subtype.ext
    exact hx_eq.symm
  have hxP_Qmap : xM ∈ Qmap := by
    simpa [hP_eq] using hxP
  have hxM0_K : xM0 ∈ K := by
    simpa [hxM0_eq] using hQmap_le_K hxP_Qmap
  let R0 : Subgroup M := Subgroup.zpowers xM0
  have hR0_le_K : R0 ≤ K := by
    simpa [R0] using (Subgroup.zpowers_le_of_mem hxM0_K)
  have horderx : orderOf x = q.val := by
    simpa using
      section10_zpowers_card_eq_prime_of_mem_omegaOneCenter (G := G) hxΩ hxne
  have hR0_card : Nat.card R0 = q.val := by
    calc
      Nat.card R0 = orderOf xM0 := by simp [R0]
      _ = orderOf x := by
        rw [← Subgroup.orderOf_coe xM0]
      _ = q.val := horderx
  have hR0_prime : Nat.Prime (Nat.card R0) := by
    rw [hR0_card]
    exact q.property
  have hCZ : IsZGroup ↥(subgroupCentralizerIn A R0) := by
    simpa [A, R0, xM0] using
      section10_isZGroup_malphaSubgroup_centralizer_zpowers_of_ambient
        (M := M) hxM hZ
  have hplen_comm : HasPLengthOne p.val ↥⁅A, K⁆ :=
    theorem_3_6 (G := M) A K R0 p.val hMsolv hModd hAK hcopAK
      hR0_le_K hR0_prime p.property hCZ
  have hA_eq_comm : A = ⁅A, K⁆ := by
    exact lemma_6_3_a_1 (G := M) (H := A)
      ⟨section10AlphaPrimes M, hHallA⟩ hAK.isCompl hA_le_D
  let e : ↥⁅A, K⁆ ≃* A := MulEquiv.subgroupCongr hA_eq_comm.symm
  exact hasPLengthOne_of_equiv (p := p.val) e hplen_comm

omit [IsMinCE G] in
private theorem CFSG.section10_hasPLengthOne_of_normal_pLengthOne_and_coprime_quotient
    {H : Type*} [Group H] [Finite H] {N : Subgroup H} [N.Normal] {p : Nat.Primes}
    (hNplen : HasPLengthOne p.val N)
    (hquot : Nat.Coprime p.val (Nat.card (H ⧸ N))) :
    HasPLengthOne p.val H := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let P : Subgroup H := pElementsSubgroup p.val H
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  have hP_le_N : P ≤ N := by
    have hEqOne_of_isPElement {y : H ⧸ N} (hy : IsPElement (p := p.val) y) : y = 1 := by
      rcases hy with ⟨n, hn⟩
      have hcopOrd : Nat.Coprime p.val (orderOf y) :=
        Nat.Coprime.of_dvd_right (orderOf_dvd_natCard y) hquot
      rw [hn] at hcopOrd
      have hnzero : n = 0 := by
        by_contra hn0
        have hdvd : p.val ∣ p.val ^ n := dvd_pow_self p.val (Nat.pos_iff_ne_zero.mpr hn0).ne'
        exact ((Nat.Prime.coprime_iff_not_dvd p.property).1 hcopOrd) hdvd
      have horder_one : orderOf y = 1 := by simpa [hnzero] using hn
      exact orderOf_eq_one_iff.mp horder_one
    have hgen_ker : {x : H | IsPElement (p := p.val) x} ⊆ q.ker := by
      intro x hx
      have hxQ : IsPElement (p := p.val) (q x) := by
        rcases hx with ⟨n, hn⟩
        have hdiv : orderOf (q x) ∣ p.val ^ n :=
          (orderOf_map_dvd (ψ := q) x).trans (by simp [hn])
        rcases (Nat.dvd_prime_pow p.property).1 hdiv with ⟨m, _hmle, hm⟩
        exact ⟨m, hm⟩
      exact (MonoidHom.mem_ker (f := q) (x := x)).2 (hEqOne_of_isPElement hxQ)
    change Subgroup.closure {x : H | IsPElement (p := p.val) x} ≤ N
    simpa [q, QuotientGroup.ker_mk'] using (Subgroup.closure_le (K := q.ker)).2 hgen_ker
  let Psub : Subgroup N := P.subgroupOf N
  have hcompNelems : HasNormalPComplement p.val (pElementsSubgroup p.val N) :=
    (hasPLengthOne_iff_hasNormalPComplement_pElements (G := N) (p := p.val)).1 hNplen
  have hP_le_map : P ≤ (pElementsSubgroup p.val N).map N.subtype := by
    change Subgroup.closure {x : H | IsPElement (p := p.val) x} ≤
      (pElementsSubgroup p.val N).map N.subtype
    refine (Subgroup.closure_le (K := (pElementsSubgroup p.val N).map N.subtype)).2 ?_
    intro x hx
    have hxN : x ∈ N := hP_le_N (Subgroup.subset_closure hx)
    let xN : N := ⟨x, hxN⟩
    have hxN_p : IsPElement (p := p.val) xN := by
      rcases hx with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      simpa [xN, Subgroup.orderOf_coe] using hn
    exact ⟨xN, Subgroup.subset_closure hxN_p, rfl⟩
  have hPsub_le_Nelems : Psub ≤ pElementsSubgroup p.val N := by
    intro x hx
    have hxmap : ((x : N) : H) ∈ (pElementsSubgroup p.val N).map N.subtype :=
      hP_le_map hx
    rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
    have hxy : x = y := by
      apply Subtype.ext
      exact hyx.symm
    simpa [hxy]
  have hcompPsub : HasNormalPComplement p.val Psub :=
    hasNormalPComplement_of_le (G := N) (p := p.val) hPsub_le_Nelems hcompNelems
  let eP : Psub ≃* P := Subgroup.subgroupOfEquivOfLe (H := P) (K := N) hP_le_N
  have hcompP : HasNormalPComplement p.val P :=
    hasNormalPComplement_of_equiv (G := Psub) (G' := P) (p := p.val) eP hcompPsub
  exact (hasPLengthOne_iff_hasNormalPComplement_pElements (G := H) (p := p.val)).2 hcompP

/-- Theorem 10.6. -/
public theorem CFSG.theorem_10_6
    {H : Subgroup G} {p : Nat.Primes} (hHproper : H ≠ ⊤) :
    HasPLengthOne p.val H := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  obtain ⟨M, hMcont⟩ :=
    section10_exists_maximalSubgroupsContaining_of_ne_top (G := G) hHproper
  have hM : M ∈ section9MaximalSubgroups G := hMcont.1
  have hHM : H ≤ M := hMcont.2
  refine section10_hasPLengthOne_of_le_hasPLengthOne (p := p) hHM ?_
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hModd : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  by_cases hrank : primeRank p.val M ≤ 2
  · exact section10_hasPLengthOne_of_primeRank_le_two (p := p) hMsolv hModd hrank
  · have hαrank : 2 < primeRank p.val M := by omega
    have hp_dvd_M : p.val ∣ Nat.card M :=
      section10_prime_dvd_card_of_three_le_primeRank_pre
        (p := p.val) (R := M) (by omega)
    have hpα : p ∈ section10AlphaPrimes M := by
      simpa [section10AlphaPrimes, subgroupPrimeSet] using
        (show p ∈ section10AlphaPrimes M from ⟨hp_dvd_M, hαrank⟩)
    have hMalpha_plen :
        HasPLengthOne p.val (section10MalphaSubgroup M) :=
      section10_malpha_hasPLengthOne_of_high_primeRank (G := G) hM hαrank
    have hcop :
        Nat.Coprime p.val (Nat.card (M ⧸ section10MalphaSubgroup M)) :=
      section10_coprime_quotient_malpha_of_mem_alpha (G := G) hM hpα
    exact section10_hasPLengthOne_of_normal_pLengthOne_and_coprime_quotient
      (H := M) (N := section10MalphaSubgroup M) (p := p) hMalpha_plen hcop

end Section10
