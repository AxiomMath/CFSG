module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section7Proposition74
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStabilityReduction

import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.InvolutionCore
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingOddCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl

namespace CFSG
end CFSG
open CFSG

/-!
# Section 7: the second-stage setup

This module starts the source's second stage after Proposition 7.2.  The
first declaration is deliberately only the checked prelude to `(7D)`: it
packages the selected point, the two stabilizers, oddness/solvability of the
triple stabilizer, its `z`-normalization, and the nontrivial commutator
containment supplied by the `(6A)` witness.  The Sylow commutator-divisibility
step is kept separate, so it cannot silently become an assumption of the
maximality argument.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise commutatorElement

universe u

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

private theorem subgroupOf_le_pPrimeCore_map
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K H : Subgroup G} (hKH : K ≤ H) [hKN : (K.subgroupOf H).Normal]
    (hcop : Nat.Coprime p (Nat.card K)) :
    K ≤ (pPrimeCore p ↥H).map H.subtype := by
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have hcop' : Nat.Coprime p (Nat.card (K.subgroupOf H)) := by
    rw [hcard]
    exact hcop
  have hsub : K.subgroupOf H ≤ pPrimeCore p ↥H :=
    le_sSup ⟨hKN, hcop'⟩
  simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKH] using
    (Subgroup.map_mono (f := H.subtype) hsub)

/-- The source data available immediately after Proposition 7.2. -/
public structure Theorem4bSection7SecondStage
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixD M) where
  beta : conjugateCosetSpace M
  hbetaK : beta ∈ d.data.kFixedPoints
  hbetaNe : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)
  htheta : corollary64Theta d.data.p (theorem4bSection7D M beta) = ⊥
  hWleE : d.data.W ≤ theorem4bSection7E M d.data.z beta
  hEodd : Odd (Nat.card (theorem4bSection7E M d.data.z beta))
  hzNormE : d.data.z ∈
    Subgroup.normalizer (theorem4bSection7E M d.data.z beta : Set X)
  hWcomm : d.data.W ≤
    ⁅theorem4bSection7E M d.data.z beta, Subgroup.zpowers d.data.z⁆
  hEsolv : Group.IsSolvable (theorem4bSection7E M d.data.z beta)

/-- Proposition 7.2, expanded into the exact source `(7D)` prelude. -/
public theorem IsStronglyEmbedded.theorem4b_section7_secondStage
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N) :
    Nonempty (Theorem4bSection7SecondStage d) := by
  obtain ⟨beta, hbetaK, hbetaNe, htheta⟩ :=
    hM.theorem4b_proposition72 hX d hrank hT2 hinduction
  have hWbeta : d.data.W ≤ MulAction.stabilizer X beta := by
    exact d.data.kFixedPoints_subset_fixedPoints hbetaK
  have hWD : d.data.W ≤ theorem4bSection7D M beta := by
    exact le_inf d.data.hWM hWbeta
  have hWleE : d.data.W ≤ theorem4bSection7E M d.data.z beta := by
    simpa [theorem4bSection7E, theorem4bSection7D] using
      theorem4b_le_triple_stabilizer_of_le_two_point_stabilizer
        d.data.hzNorm hWD
  have hDodd : Odd (Nat.card (theorem4bSection7D M beta)) := by
    simpa [theorem4bSection7D] using
      hM.base_inf_stabilizer_card_odd hbetaNe
  have hEodd : Odd (Nat.card (theorem4bSection7E M d.data.z beta)) := by
    exact Odd.of_dvd_nat hDodd
      (Subgroup.card_dvd_of_le (show theorem4bSection7E M d.data.z beta ≤
        theorem4bSection7D M beta from inf_le_left))
  have hzNormE : d.data.z ∈
      Subgroup.normalizer (theorem4bSection7E M d.data.z beta : Set X) := by
    simpa [theorem4bSection7E, theorem4bSection7D] using
      theorem4b_mem_normalizer_tripleStabilizer
        (M := M) (z := d.data.z) (beta := beta)
        d.data.hz d.data.hzM
  have hWcomm : d.data.W ≤
      ⁅theorem4bSection7E M d.data.z beta,
        Subgroup.zpowers d.data.z⁆ := by
    have hmono :
        ⁅d.data.W, Subgroup.zpowers d.data.z⁆ ≤
          ⁅theorem4bSection7E M d.data.z beta,
            Subgroup.zpowers d.data.z⁆ :=
      Subgroup.commutator_mono hWleE
        (le_refl (Subgroup.zpowers d.data.z))
    rw [d.data.hcomm] at hmono
    exact hmono
  have hEsolv : Group.IsSolvable (theorem4bSection7E M d.data.z beta) :=
    odd_order_theorem _ hEodd
  exact ⟨⟨beta, hbetaK, hbetaNe, htheta, hWleE, hEodd, hzNormE,
    hWcomm, hEsolv⟩⟩

/-- If a coprime solvable action saturates its target and that target has a
nontrivial `p`-subgroup, then the induced action on its first nontrivial
`p`-layer cannot be trivial. -/
private theorem theorem4b_section7_nontrivial_pCore_quotient_action
    {H A : Type*} [Group H] [Finite H] [Group A] [Finite A]
    [MulDistribMulAction A H]
    (p : ℕ) [Fact p.Prime]
    (hsolv : Group.IsSolvable H)
    (hcoprime : Nat.Coprime (Nat.card A) (Nat.card H))
    (hcomm : commutatorAction (A := A) (G := H) = ⊤)
    {W : Subgroup H} (hWp : IsPGroup p W) (hWne : W ≠ ⊥) :
    let K : Subgroup H := pPrimeCore p H
    letI : IsInvariant A H K := isInvariant_of_characteristic K
    letI : MulDistribMulAction A (H ⧸ K) :=
      quotientMulDistribMulAction (A := A) (G := H) K
        (isInvariant_of_characteristic K)
    letI : IsInvariant A (H ⧸ K) (pCore p (H ⧸ K)) :=
      isInvariant_of_characteristic _
    ¬ ActsTrivially (A := A) (G := pCore p (H ⧸ K)) := by
  dsimp only
  letI : Group.IsSolvable H := hsolv
  let K : Subgroup H := pPrimeCore p H
  letI : IsInvariant A H K := isInvariant_of_characteristic K
  letI : MulDistribMulAction A (H ⧸ K) :=
    quotientMulDistribMulAction (A := A) (G := H) K
      (isInvariant_of_characteristic K)
  letI : IsInvariant A (H ⧸ K) (pCore p (H ⧸ K)) :=
    isInvariant_of_characteristic _
  intro htrivP
  have hsolvQ : Group.IsSolvable (H ⧸ K) := by
    letI : Group.IsSolvable H := hsolv
    exact Group.isSolvable_of_surjective
      (f := QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
  have hcoreQ : pPrimeCore p (H ⧸ K) = ⊥ := by
    simpa [K] using
      (pPrimeCore_quotient_pPrimeCore_eq_bot (G := H) (p := p))
  have hfitQ : fittingSubgroup (H ⧸ K) = pCore p (H ⧸ K) :=
    Fitting_eq_pcore (H ⧸ K) p hcoreQ
  have hcoprimeQ : Nat.Coprime (Nat.card A) (Nat.card (H ⧸ K)) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_quotient_dvd_card K) hcoprime
  have htrivQ : ActsTrivially (A := A) (G := H ⧸ K) := by
    intro a q
    exact section8_element_actsTrivially_of_centralizes_fitting_of_coprime
      hsolvQ hcoprimeQ a (fun f => by
        have hfP : (f : H ⧸ K) ∈ pCore p (H ⧸ K) := by
          rw [← hfitQ]
          exact f.property
        have hf := htrivP a ⟨(f : H ⧸ K), hfP⟩
        exact congrArg Subtype.val hf) q
  have hcomm_le : commutatorAction (A := A) (G := H) ≤ K := by
    rw [commutatorAction_eq_closure (G := H) (A := A)]
    refine (Subgroup.closure_le (K := K)).2 ?_
    rintro x ⟨a, g, rfl⟩
    apply (QuotientGroup.eq_one_iff (N := K) (x := g⁻¹ * (a • g))).mp
    change QuotientGroup.mk' K (g⁻¹ * (a • g)) = 1
    rw [map_mul, map_inv]
    have hmk : QuotientGroup.mk' K (a • g) = QuotientGroup.mk' K g := by
      calc
        QuotientGroup.mk' K (a • g) = a • QuotientGroup.mk' K g := by
          simpa only [QuotientGroup.mk'_apply] using
            (MulAction.Quotient.smul_mk K a g).symm
        _ = QuotientGroup.mk' K g := htrivQ a _
    rw [hmk]
    simp
  have hKtop : K = ⊤ := by
    rw [hcomm] at hcomm_le
    exact top_unique hcomm_le
  have hpW : p ∣ Nat.card W := by
    rcases hWp.card_eq_or_dvd with hWcard | hpW
    · exact False.elim (hWne (Subgroup.card_eq_one.mp hWcard))
    · exact hpW
  have hpH : p ∣ Nat.card H :=
    dvd_trans hpW (by
      simpa using
        (Subgroup.card_dvd_of_le (show W ≤ (⊤ : Subgroup H) from le_top)))
  have hcoprimeCore := pPrimeCore_coprime_card (G := H) (p := p)
  have hcoprimeH : Nat.Coprime p (Nat.card H) := by
    rw [show pPrimeCore p H = ⊤ from hKtop] at hcoprimeCore
    simpa using hcoprimeCore
  exact
    ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hcoprimeH) hpH

/-- A nontrivial action on the canonical `p`-layer of `[E,A]` is visible in
the commutator with every Sylow `p`-subgroup of `E`. -/
private theorem theorem4b_section7_p_dvd_commutator_card
    {X : Type*} [Group X] [Finite X]
    (p : ℕ) [Fact p.Prime] (E A : Subgroup X)
    (hA_norm_E : A ≤ Subgroup.normalizer (E : Set X)) :
    letI : Subgroup.Normalizes A E := ⟨hA_norm_E⟩
    let H : Subgroup E := commutatorAction (A := A) (G := E)
    letI : IsInvariant A E H := commutatorAction_isInvariant
    let K : Subgroup H := pPrimeCore p H
    letI : IsInvariant A H K := isInvariant_of_characteristic K
    letI : MulDistribMulAction A (H ⧸ K) :=
      quotientMulDistribMulAction (A := A) (G := H) K
        (isInvariant_of_characteristic K)
    letI : IsInvariant A (H ⧸ K) (pCore p (H ⧸ K)) :=
      isInvariant_of_characteristic _
    (∃ a : A, ∃ q : pCore p (H ⧸ K), a • q ≠ q) →
      ∀ S : Sylow p E,
        p ∣ Nat.card (⁅A, (S : Subgroup E).map E.subtype⁆ : Subgroup X) := by
  classical
  dsimp only
  letI : Subgroup.Normalizes A E := ⟨hA_norm_E⟩
  let H : Subgroup E := commutatorAction (A := A) (G := E)
  letI : H.Normal := commutatorAction_normal
  letI : IsInvariant A E H := commutatorAction_isInvariant
  let K : Subgroup H := pPrimeCore p H
  letI : IsInvariant A H K := isInvariant_of_characteristic K
  letI : MulDistribMulAction A (H ⧸ K) :=
    quotientMulDistribMulAction (A := A) (G := H) K
      (isInvariant_of_characteristic K)
  letI : IsInvariant A (H ⧸ K) (pCore p (H ⧸ K)) :=
    isInvariant_of_characteristic _
  intro hnontriv S
  let qH : H →* H ⧸ K := QuotientGroup.mk' K
  let T : Sylow p H :=
    External.hallSylowSubgroupOfNormal S H
  let Tbar : Sylow p (H ⧸ K) :=
    T.mapSurjective (f := qH) (QuotientGroup.mk'_surjective K)
  let U : Subgroup (H ⧸ K) :=
    (Tbar : Subgroup (H ⧸ K)) ⊔ pCore p (H ⧸ K)
  have hsupP : IsPGroup p U := by
    dsimp [U]
    exact IsPGroup.to_sup_of_normal_right Tbar.isPGroup'
      (pCore_isPGroup (G := H ⧸ K) (p := p))
  have hsupEq : U = (Tbar : Subgroup (H ⧸ K)) :=
    Tbar.is_maximal' hsupP (by
      dsimp [U]
      exact le_sup_left)
  have hpcore_le_Tbar : pCore p (H ⧸ K) ≤ Tbar := by
    calc
      pCore p (H ⧸ K) ≤ U := by
        dsimp [U]
        exact le_sup_right
      _ = Tbar := hsupEq
  obtain ⟨a, q, hqmove⟩ := hnontriv
  have hqTbar : (q : H ⧸ K) ∈ (Tbar : Subgroup (H ⧸ K)) :=
    hpcore_le_Tbar q.property
  have hqmap : (q : H ⧸ K) ∈ (T : Subgroup H).map qH := by
    simpa [Tbar] using hqTbar
  rcases hqmap with ⟨t, htT, hqt⟩
  have hqmoveVal : a • (q : H ⧸ K) ≠ (q : H ⧸ K) := by
    intro hfix
    apply hqmove
    exact Subtype.ext hfix
  have htmove : a • qH t ≠ qH t := by
    simpa [hqt] using hqmoveVal
  let c : H := t⁻¹ * (a • t)
  have hqc : qH c = (qH t)⁻¹ * (a • qH t) := by
    simp [c, qH]
  have hqc_ne : qH c ≠ 1 := by
    intro hc1
    apply htmove
    have hinv : (qH t)⁻¹ * (a • qH t) = 1 := by
      simpa [hqc] using hc1
    exact (eq_of_inv_mul_eq_one hinv).symm
  have hqtP : qH t ∈ pCore p (H ⧸ K) := by
    rw [hqt]
    exact q.property
  have haqtP : a • qH t ∈ pCore p (H ⧸ K) :=
    (IsInvariant.invariant (A := A) (G := H ⧸ K)
      (H := pCore p (H ⧸ K)) a (qH t)).1 hqtP
  have hqcP : qH c ∈ pCore p (H ⧸ K) := by
    rw [hqc]
    exact (pCore p (H ⧸ K)).mul_mem
      ((pCore p (H ⧸ K)).inv_mem hqtP) haqtP
  let cP : pCore p (H ⧸ K) := ⟨qH c, hqcP⟩
  have hcP_ne : cP ≠ 1 := by
    intro hcP
    exact hqc_ne (congrArg Subtype.val hcP)
  obtain ⟨n, hn⟩ :=
    (IsPGroup.iff_orderOf.mp
      (pCore_isPGroup (G := H ⧸ K) (p := p))) cP
  have hn_ne : n ≠ 0 := by
    intro hn0
    subst n
    have hcP_order : orderOf cP = 1 := by simpa using hn
    exact hcP_ne (orderOf_eq_one_iff.mp hcP_order)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne
  have hp_order_cP : p ∣ orderOf cP := by
    rw [hn]
    simp [pow_succ]
  have hp_order_qc : p ∣ orderOf (qH c) := by
    rw [show orderOf (qH c) = orderOf cP from Subgroup.orderOf_coe cP]
    exact hp_order_cP
  have hp_order_c : p ∣ orderOf c :=
    dvd_trans hp_order_qc (orderOf_map_dvd qH c)
  have htS : (t : E) ∈ (S : Subgroup E) := by
    simpa [T, External.hallSylowSubgroupOfNormal_coe,
      Subgroup.mem_subgroupOf] using htT
  have htSX : (t : X) ∈ (S : Subgroup E).map E.subtype :=
    Subgroup.mem_map_of_mem E.subtype htS
  have hcComm : (c : X) ∈
      ⁅(S : Subgroup E).map E.subtype, A⁆ := by
    have hgen : ⁅(t : X)⁻¹, (a : X)⁆ ∈
        ⁅(S : Subgroup E).map E.subtype, A⁆ :=
      Subgroup.commutator_mem_commutator
        (H₁ := (S : Subgroup E).map E.subtype) (H₂ := A)
        (((S : Subgroup E).map E.subtype).inv_mem htSX) a.property
    have hsmul : ((a • t : H) : X) =
        (a : X) * (t : X) * (a : X)⁻¹ := by
      change ((a • (t : E) : E) : X) =
        (a : X) * (t : X) * (a : X)⁻¹
      exact Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
        A E a (t : E)
    change (t : X)⁻¹ * ((a • t : H) : X) ∈
      ⁅(S : Subgroup E).map E.subtype, A⁆
    rw [hsmul]
    simpa [commutatorElement_def, mul_assoc] using hgen
  have hp_order_cX : p ∣ orderOf (c : X) := by
    simpa only [Subgroup.orderOf_coe] using hp_order_c
  let C : Subgroup X := ⁅(S : Subgroup E).map E.subtype, A⁆
  let cComm : C := ⟨(c : X), hcComm⟩
  have hp_card_comm : p ∣ Nat.card C := by
    apply dvd_trans hp_order_cX
    have horder : orderOf (c : X) = orderOf cComm := by
      simpa [cComm] using (Subgroup.orderOf_coe cComm)
    rw [horder]
    exact orderOf_dvd_natCard cComm
  simpa only [C, Subgroup.commutator_comm] using hp_card_comm

/-- In the source second-stage configuration, `z` acts nontrivially on the
`O_{p',p}/O_{p'}` layer of `[E,z]`. -/
private theorem theorem4b_section7_nontrivial_pCore_quotient_action_of_secondStage
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixD M) (s : Theorem4bSection7SecondStage d) :
    let E : Subgroup X := theorem4bSection7E M d.data.z s.beta
    let A : Subgroup X := Subgroup.zpowers d.data.z
    letI : Subgroup.Normalizes A E := ⟨by
      rw [Subgroup.zpowers_le]
      exact s.hzNormE⟩
    let H : Subgroup E := commutatorAction (A := A) (G := E)
    letI : IsInvariant A E H := commutatorAction_isInvariant
    let K : Subgroup H := pPrimeCore d.data.p H
    letI : IsInvariant A H K := isInvariant_of_characteristic K
    letI : MulDistribMulAction A (H ⧸ K) :=
      quotientMulDistribMulAction (A := A) (G := H) K
        (isInvariant_of_characteristic K)
    letI : IsInvariant A (H ⧸ K) (pCore d.data.p (H ⧸ K)) :=
      isInvariant_of_characteristic _
    ∃ a : A, ∃ q : pCore d.data.p (H ⧸ K), a • q ≠ q := by
  classical
  dsimp only
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let E : Subgroup X := theorem4bSection7E M d.data.z s.beta
  let A : Subgroup X := Subgroup.zpowers d.data.z
  have hA_norm_E : A ≤ Subgroup.normalizer (E : Set X) := by
    rw [Subgroup.zpowers_le]
    exact s.hzNormE
  letI : Subgroup.Normalizes A E := ⟨hA_norm_E⟩
  let H : Subgroup E := commutatorAction (A := A) (G := E)
  letI : IsInvariant A E H := commutatorAction_isInvariant
  let K : Subgroup H := pPrimeCore d.data.p H
  letI : IsInvariant A H K := isInvariant_of_characteristic K
  letI : MulDistribMulAction A (H ⧸ K) :=
    quotientMulDistribMulAction (A := A) (G := H) K
      (isInvariant_of_characteristic K)
  letI : IsInvariant A (H ⧸ K) (pCore d.data.p (H ⧸ K)) :=
    isInvariant_of_characteristic _
  have horder : orderOf d.data.z = 2 :=
    (orderOf_eq_prime_iff).2 ⟨d.data.hz.sq_eq_one, d.data.hz.ne_one⟩
  have hAcard : Nat.card A = 2 := by
    simp [A, Nat.card_zpowers, horder]
  have hcopAE : Nat.Coprime (Nat.card A) (Nat.card E) := by
    rw [hAcard]
    exact s.hEodd.coprime_two_left
  letI : Group.IsSolvable E := s.hEsolv
  have hHsolv : Group.IsSolvable H := by infer_instance
  have hcopAH : Nat.Coprime (Nat.card A) (Nat.card H) :=
    Nat.Coprime.of_dvd_right (by
      simpa using
        (Subgroup.card_dvd_of_le (show H ≤ (⊤ : Subgroup E) from le_top))) hcopAE
  have hsat : commutatorAction₂ (A := A) (G := E) = H := by
    simpa [H] using
      (commutatorAction₂_eq_commutatorAction_of_solvable_coprime
        (G := E) (A := A) s.hEsolv hcopAE)
  have hcommTop : commutatorAction (A := A) (G := H) = ⊤ := by
    apply (Subgroup.map_injective H.subtype_injective)
    rw [commutatorAction_map_subtype_eq_commutatorAction₂]
    rw [hsat]
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    · rintro ⟨y, _hy, rfl⟩
      exact y.property
  let WE : Subgroup E := d.data.W.subgroupOf E
  have hmapComm : H.map E.subtype = ⁅E, A⁆ := by
    simpa [H] using
      (commutatorAction_subgroup_conj_map_eq_commutator E A hA_norm_E)
  have hWEleH : WE ≤ H := by
    intro w hw
    have hwW : (w : X) ∈ d.data.W := by
      simpa [WE, Subgroup.mem_subgroupOf] using hw
    have hwComm : (w : X) ∈ ⁅E, A⁆ := s.hWcomm hwW
    rw [← hmapComm] at hwComm
    rcases hwComm with ⟨y, hy, hyw⟩
    have hywE : (y : E) = w := E.subtype_injective hyw
    simpa [hywE] using hy
  let WH : Subgroup H := WE.subgroupOf H
  have hWEp : IsPGroup d.data.p WE :=
    d.data.hWp.of_equiv (Subgroup.subgroupOfEquivOfLe s.hWleE).symm
  have hWHp : IsPGroup d.data.p WH :=
    hWEp.of_equiv (Subgroup.subgroupOfEquivOfLe hWEleH).symm
  have hWEne : WE ≠ ⊥ := by
    intro hbot
    exact d.data.hWne
      ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le s.hWleE)
  have hWHne : WH ≠ ⊥ := by
    intro hbot
    exact hWEne
      ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hWEleH)
  have hnot := theorem4b_section7_nontrivial_pCore_quotient_action
    (H := H) (A := A) d.data.p hHsolv hcopAH hcommTop hWHp hWHne
  apply Classical.byContradiction
  intro hex
  apply hnot
  intro a q
  by_contra hne
  exact hex ⟨a, q, hne⟩

/-- Equation `(7D)`: for every Sylow `p`-subgroup `S` of the selected triple
stabilizer `E`, the commutator `[z,S]` has order divisible by `p`. -/
public theorem theorem4b_section7_sevenD
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixD M) (s : Theorem4bSection7SecondStage d) :
    ∀ S : Subgroup X,
      theorem4bIsSylowSubgroupOf d.data.p S
        (theorem4bSection7E M d.data.z s.beta) →
      d.data.p ∣
        Nat.card (⁅Subgroup.zpowers d.data.z, S⁆ : Subgroup X) := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  intro S hSsyl
  let E : Subgroup X := theorem4bSection7E M d.data.z s.beta
  let A : Subgroup X := Subgroup.zpowers d.data.z
  have hA_norm_E : A ≤ Subgroup.normalizer (E : Set X) := by
    rw [Subgroup.zpowers_le]
    exact s.hzNormE
  letI : Subgroup.Normalizes A E := ⟨hA_norm_E⟩
  let H : Subgroup E := commutatorAction (A := A) (G := E)
  letI : IsInvariant A E H := commutatorAction_isInvariant
  let K : Subgroup H := pPrimeCore d.data.p H
  letI : IsInvariant A H K := isInvariant_of_characteristic K
  letI : MulDistribMulAction A (H ⧸ K) :=
    quotientMulDistribMulAction (A := A) (G := H) K
      (isInvariant_of_characteristic K)
  letI : IsInvariant A (H ⧸ K) (pCore d.data.p (H ⧸ K)) :=
    isInvariant_of_characteristic _
  have hnontriv :
      ∃ a : A, ∃ q : pCore d.data.p (H ⧸ K), a • q ≠ q := by
    have hraw :=
      theorem4b_section7_nontrivial_pCore_quotient_action_of_secondStage d s
    dsimp only at hraw
    exact hraw
  rcases hSsyl with ⟨SE, hSE⟩
  have hpmap := theorem4b_section7_p_dvd_commutator_card
    d.data.p E A hA_norm_E hnontriv SE
  simpa [E, A, hSE] using hpmap

/-- The source conditions `(a)` and `(b)` on the subgroups considered in the
maximal choice after `(7D)`.  The field `P₁` is the supplied `t`-invariant
Sylow `p`-subgroup of `E` contained in `N_E(Q)`. -/
public structure Theorem4bSection7AdmissibleQ
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixD M) (s : Theorem4bSection7SecondStage d) where
  Q : Subgroup X
  hQp : IsPGroup d.data.p Q
  hQne : Q ≠ ⊥
  hQE : Q ≤ theorem4bSection7E M d.data.z s.beta
  hzNormQ : d.data.z ∈ Subgroup.normalizer (Q : Set X)
  t : X
  ht : IsInvolution t
  htNormQ : t ∈ Subgroup.normalizer (Q : Set X)
  htBase : t • theorem4bSection7Base = s.beta
  htBeta : t • s.beta = theorem4bSection7Base
  P₁ : Subgroup X
  hP₁sylow : theorem4bIsSylowSubgroupOf d.data.p P₁
    (theorem4bSection7E M d.data.z s.beta)
  hP₁NormQ : P₁ ≤ Subgroup.normalizer (Q : Set X)
  htNormP₁ : t ∈ Subgroup.normalizer (P₁ : Set X)

private theorem theorem4bIsSylowSubgroupOf_isPGroup_final
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P E : Subgroup X}
    (hP : theorem4bIsSylowSubgroupOf p P E) : IsPGroup p P := by
  rcases hP with ⟨PE, rfl⟩
  exact PE.isPGroup'.map E.subtype

private theorem theorem4bIsSylowSubgroupOf_le_final
    {X : Type u} [Group X] {p : ℕ} {P E : Subgroup X}
    (hP : theorem4bIsSylowSubgroupOf p P E) : P ≤ E := by
  rcases hP with ⟨PE, rfl⟩
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

private theorem theorem4bIsSylowSubgroupOf_of_le_final
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P E D : Subgroup X}
    (hp : Nat.Prime p)
    (hPsyl : theorem4bIsSylowSubgroupOf p P D)
    (hPE : P ≤ E) (hED : E ≤ D) :
    theorem4bIsSylowSubgroupOf p P E := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨PD, hP⟩
  let ED : Subgroup D := E.subgroupOf D
  have hPDle : (PD : Subgroup D) ≤ ED := by
    intro x hx
    change (x : X) ∈ E
    apply hPE
    rw [hP]
    exact Subgroup.mem_map_of_mem D.subtype hx
  let PED : Sylow p ED := PD.subtype hPDle
  let e : ED ≃* E := Subgroup.subgroupOfEquivOfLe hED
  let PE : Sylow p E := PED.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨PE, ?_⟩
  apply le_antisymm
  · intro x hxP
    rw [hP] at hxP
    rcases Subgroup.mem_map.mp hxP with ⟨xD, hxPD, rfl⟩
    apply Subgroup.mem_map.mpr
    let xED : ED := ⟨xD, hPDle hxPD⟩
    refine ⟨e xED, ?_, rfl⟩
    have hxPED : xED ∈ PED := hxPD
    simpa [PE] using Subgroup.mem_map_of_mem e.toMonoidHom hxPED
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xE, hxPE, rfl⟩
    have hxPE' : xE ∈ (PED : Subgroup ED).map e.toMonoidHom := by
      simpa [PE] using hxPE
    rcases Subgroup.mem_map.mp hxPE' with ⟨xED, hxPED, hx⟩
    change (xED : D) ∈ (PD : Subgroup D) at hxPED
    rw [hP]
    apply Subgroup.mem_map.mpr
    refine ⟨(xED : D), hxPED, ?_⟩
    change (xED : X) = (xE : X)
    calc
      (xED : X) = (e xED : X) := by rfl
      _ = (xE : X) := congrArg (fun y : E => (y : X)) hx

/-- Lemma 7.3 supplies an initial admissible subgroup for the finite maximal
choice: take a `z`-invariant Sylow subgroup `P` of `E` containing `W`, and set
both `Q` and `P₁` equal to `P`. -/
public theorem IsStronglyEmbedded.theorem4b_section7_initial_admissibleQ
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (d : Theorem4bSixD M) (s : Theorem4bSection7SecondStage d) :
    ∃ a : Theorem4bSection7AdmissibleQ d s, a.Q = a.P₁ := by
  obtain ⟨P, hPsylow, hWP, hzNormP⟩ :=
    hM.theorem4b_lemma73_exists_invariant_sylow d s.hbetaNe
      d.data.hWp s.hWleE d.data.hzNorm
  obtain ⟨t, ht, htNormP, htBase, htBeta⟩ :=
    hM.theorem4b_lemma73 hT2 d s.hbetaK s.hbetaNe hPsylow hzNormP
  have hPp : IsPGroup d.data.p P :=
    theorem4bIsSylowSubgroupOf_isPGroup_final hPsylow
  have hPne : P ≠ ⊥ := by
    intro hPbot
    apply d.data.hWne
    exact bot_unique (by simpa [hPbot] using hWP)
  have hPE : P ≤ theorem4bSection7E M d.data.z s.beta :=
    theorem4bIsSylowSubgroupOf_le_final hPsylow
  let a : Theorem4bSection7AdmissibleQ d s := {
    Q := P
    hQp := hPp
    hQne := hPne
    hQE := hPE
    hzNormQ := hzNormP
    t := t
    ht := ht
    htNormQ := htNormP
    htBase := htBase
    htBeta := htBeta
    P₁ := P
    hP₁sylow := hPsylow
    hP₁NormQ := Subgroup.le_normalizer
    htNormP₁ := htNormP }
  exact ⟨a, rfl⟩

/-- In particular, the admissible family is nonempty. -/
public theorem IsStronglyEmbedded.theorem4b_section7_admissibleQ_nonempty
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (d : Theorem4bSixD M) (s : Theorem4bSection7SecondStage d) :
    Nonempty (Theorem4bSection7AdmissibleQ d s) := by
  obtain ⟨a, _⟩ := hM.theorem4b_section7_initial_admissibleQ hT2 d s
  exact ⟨a⟩

/-- The source subgroup `N_D(Q)`, where `D = X_{alpha,beta}`. -/
@[expose] public def theorem4bSection7NormalizerInD
    {X : Type u} [Group X] [Finite X] (M : Subgroup X)
    (beta : conjugateCosetSpace M) (Q : Subgroup X) : Subgroup X :=
  theorem4bSection7D M beta ⊓ Subgroup.normalizer (Q : Set X)

/-- The finite maximal choice in condition `(c)`: among all packages
satisfying source conditions `(a,b)`, choose one maximizing the `p`-part of
`N_D(Q)`. -/
public theorem IsStronglyEmbedded.theorem4b_section7_exists_maximal_admissibleQ
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (d : Theorem4bSixD M) (s : Theorem4bSection7SecondStage d) :
    ∃ a : Theorem4bSection7AdmissibleQ d s,
      ∀ b : Theorem4bSection7AdmissibleQ d s,
        (Nat.card (theorem4bSection7NormalizerInD M s.beta b.Q)).factorization
            d.data.p ≤
          (Nat.card (theorem4bSection7NormalizerInD M s.beta a.Q)).factorization
            d.data.p := by
  classical
  let A := Theorem4bSection7AdmissibleQ d s
  obtain ⟨a₀⟩ := hM.theorem4b_section7_admissibleQ_nonempty hT2 d s
  let S := {Q : Subgroup X // ∃ a : A, Q = a.Q}
  letI : Fintype S := Fintype.ofFinite S
  let q₀ : S := ⟨a₀.Q, ⟨a₀, rfl⟩⟩
  have hnonempty : (Finset.univ : Finset S).Nonempty := by
    exact ⟨q₀, by simp⟩
  let score : S → ℕ := fun q =>
    (Nat.card (theorem4bSection7NormalizerInD M s.beta q.1)).factorization
      d.data.p
  rcases Finset.exists_max_image (Finset.univ : Finset S) score hnonempty with
    ⟨q, _hq, hmax⟩
  rcases q.2 with ⟨a, hqa⟩
  refine ⟨a, ?_⟩
  intro b
  let qb : S := ⟨b.Q, ⟨b, rfl⟩⟩
  have hbmax := hmax qb (by simp)
  simpa [score, qb, hqa] using hbmax

private theorem theorem4b_section7_factorization_lt_normalizerIn_of_not_sylow
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    (hp : Nat.Prime p) {P D : Subgroup X}
    (hPp : IsPGroup p P) (hPD : P ≤ D)
    (hnot : ¬ theorem4bIsSylowSubgroupOf p P D) :
    (Nat.card P).factorization p <
      (Nat.card ((D ⊓ Subgroup.normalizer (P : Set X)) : Subgroup X)).factorization p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let PD : Subgroup D := P.subgroupOf D
  have hPDp : IsPGroup p PD :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  obtain ⟨S, hPDleS⟩ := IsPGroup.exists_le_sylow (G := D) (p := p) hPDp
  have hPDltS : PD < (S : Subgroup D) := by
    refine lt_of_le_of_ne hPDleS ?_
    intro heq
    apply hnot
    refine ⟨S, ?_⟩
    rw [← heq]
    exact (by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPD])
  have hlt := External.hkt_factorization_lt_ambient_normalizer_of_lt_sylow
    (S := S) hPDltS
  have hcardPD : Nat.card PD = Nat.card P :=
    natCard_subgroupOf_eq P D hPD
  have hnorm : Subgroup.normalizer (PD : Set D) =
      (Subgroup.normalizer (P : Set X)).subgroupOf D := by
    exact (Subgroup.subgroupOf_normalizer_eq hPD).symm
  rw [hnorm] at hlt
  let ND : Subgroup D := (Subgroup.normalizer (P : Set X)).subgroupOf D
  have hmapND : ND.map D.subtype =
      Subgroup.normalizer (P : Set X) ⊓ D := by
    dsimp [ND]
    rw [Subgroup.subgroupOf_map_subtype]
  have hcardMap : Nat.card (ND.map D.subtype) = Nat.card ND :=
    Subgroup.card_map_of_injective D.subtype_injective
  have hcardND : Nat.card ND =
      Nat.card ((D ⊓ Subgroup.normalizer (P : Set X)) : Subgroup X) := by
    rw [hmapND, inf_comm] at hcardMap
    exact hcardMap.symm
  change (Nat.card PD).factorization p < (Nat.card ND).factorization p at hlt
  rw [hcardPD, hcardND] at hlt
  exact hlt

private theorem theorem4b_section7_subgroup_conjBy_eq_self_of_mem
    {G : Type*} [Group G] (H : Subgroup G) {g : G} (hg : g ∈ H) :
    H.conjBy g = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg)
  · intro hx
    apply Subgroup.mem_map.mpr
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · exact H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg
    · simp [MulAut.conj_apply, mul_assoc]

private theorem theorem4b_section7_normalizerIn_card_eq_of_sylow
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P Q E D : Subgroup X}
    (hp : Nat.Prime p)
    (hPsylow : theorem4bIsSylowSubgroupOf p P E)
    (hQsylow : theorem4bIsSylowSubgroupOf p Q E)
    (hED : E ≤ D) :
    Nat.card ((D ⊓ Subgroup.normalizer (P : Set X)) : Subgroup X) =
      Nat.card ((D ⊓ Subgroup.normalizer (Q : Set X)) : Subgroup X) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rcases hPsylow with ⟨P₀, hP⟩
  rcases hQsylow with ⟨Q₀, hQ⟩
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq E P₀ Q₀
  have hQconj : Q = P.conjBy (x : X) := by
    rw [hQ, hP, ← hx]
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rw [Subgroup.conjBy]
    change Subgroup.map E.subtype
        (Subgroup.map (MulDistribMulAction.toMonoidHom E (MulAut.conj x))
          (P₀ : Subgroup E)) =
      Subgroup.map ((MulAut.conj (x : X)).toMonoidHom)
        (Subgroup.map E.subtype (P₀ : Subgroup E))
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hxD : (x : X) ∈ D := hED x.property
  have hDconj : D.conjBy (x : X) = D :=
    theorem4b_section7_subgroup_conjBy_eq_self_of_mem D hxD
  have hnormConj :
      (Subgroup.normalizer (P : Set X)).conjBy (x : X) =
        Subgroup.normalizer (Q : Set X) := by
    rw [Subgroup.conjBy, Subgroup.map_equiv_normalizer_eq]
    have hmapPQ : P.map (MulAut.conj (x : X)).toMonoidHom = Q := by
      simpa [Subgroup.conjBy] using hQconj.symm
    rw [hmapPQ]
  have hNDconj :
      (D ⊓ Subgroup.normalizer (P : Set X)).conjBy (x : X) =
        D ⊓ Subgroup.normalizer (Q : Set X) := by
    rw [Subgroup.conjBy,
      Subgroup.map_inf _ _ _ (MulAut.conj (x : X)).injective]
    change D.conjBy (x : X) ⊓
      (Subgroup.normalizer (P : Set X)).conjBy (x : X) = _
    rw [hDconj, hnormConj]
  have hcardConj :
      Nat.card ((D ⊓ Subgroup.normalizer (P : Set X)).conjBy (x : X)) =
        Nat.card ((D ⊓ Subgroup.normalizer (P : Set X)) : Subgroup X) :=
    Subgroup.card_map_of_injective (MulAut.conj (x : X)).injective
  rw [hNDconj] at hcardConj
  exact hcardConj.symm

private theorem theorem4bIsSylowSubgroupOf_of_subgroup_card_eq_final
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P Q E : Subgroup X}
    (hp : Nat.Prime p)
    (hPsyl : theorem4bIsSylowSubgroupOf p P E)
    (hQE : Q ≤ E) (hcard : Nat.card Q = Nat.card P) :
    theorem4bIsSylowSubgroupOf p Q E := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨PE, hP⟩
  have hPcard : Nat.card P = p ^ (Nat.card E).factorization p := by
    rw [hP, Subgroup.card_map_of_injective E.subtype_injective]
    exact Sylow.card_eq_multiplicity PE
  have hQEcard : Nat.card (Q.subgroupOf E) =
      p ^ (Nat.card E).factorization p := by
    rw [natCard_subgroupOf_eq Q E hQE, hcard, hPcard]
  let QE : Sylow p E := Sylow.ofCard (Q.subgroupOf E) hQEcard
  refine ⟨QE, ?_⟩
  change Q = (Q.subgroupOf E).map E.subtype
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQE]

private theorem theorem4bIsSylowSubgroupOf_card_eq_final
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P Q E : Subgroup X}
    (hp : Nat.Prime p)
    (hPsyl : theorem4bIsSylowSubgroupOf p P E)
    (hQsyl : theorem4bIsSylowSubgroupOf p Q E) :
    Nat.card P = Nat.card Q := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨PE, hP⟩
  rcases hQsyl with ⟨QE, hQ⟩
  rw [hP, hQ, Subgroup.card_map_of_injective E.subtype_injective,
    Subgroup.card_map_of_injective E.subtype_injective,
    PE.card_eq_multiplicity, QE.card_eq_multiplicity]

/-- The normalizer-cardinality chain preceding Lemma 7.10.  It retains the
initial `z`-invariant Sylow subgroup, the maximal admissible package, the two
non-Sylow conclusions in `D`, strict normalizer growth for `P₁`, and the
comparison supplied by maximality. -/
public theorem IsStronglyEmbedded.theorem4b_section7_maximalQ_normalizer_chain
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N)
    (s : Theorem4bSection7SecondStage d) :
    ∃ a₀ a : Theorem4bSection7AdmissibleQ d s,
      a₀.Q = a₀.P₁ ∧
      (∀ b : Theorem4bSection7AdmissibleQ d s,
        (Nat.card (theorem4bSection7NormalizerInD M s.beta b.Q)).factorization
            d.data.p ≤
          (Nat.card (theorem4bSection7NormalizerInD M s.beta a.Q)).factorization
            d.data.p) ∧
      ¬ theorem4bIsSylowSubgroupOf d.data.p a₀.Q
        (theorem4bSection7D M s.beta) ∧
      ¬ theorem4bIsSylowSubgroupOf d.data.p a.P₁
        (theorem4bSection7D M s.beta) ∧
      (Nat.card a.P₁).factorization d.data.p <
        (Nat.card (theorem4bSection7NormalizerInD M s.beta a.P₁)).factorization
          d.data.p ∧
      (Nat.card (theorem4bSection7NormalizerInD M s.beta a.P₁)).factorization
          d.data.p ≤
        (Nat.card (theorem4bSection7NormalizerInD M s.beta a.Q)).factorization
          d.data.p := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let D : Subgroup X := theorem4bSection7D M s.beta
  let E : Subgroup X := theorem4bSection7E M d.data.z s.beta
  have hED : E ≤ D := by
    change theorem4bSection7D M s.beta ⊓
      MulAction.stabilizer X (d.data.z • s.beta) ≤
      theorem4bSection7D M s.beta
    exact inf_le_left
  have h72 : Theorem4bProposition72 d.data :=
    ⟨s.beta, s.hbetaK, s.hbetaNe, s.htheta⟩
  have hltCard :=
    hM.theorem4b_proposition79 hX d hrank hT2 hinduction h72
  obtain ⟨a₀, hinit⟩ :=
    hM.theorem4b_section7_initial_admissibleQ hT2 d s
  obtain ⟨a, hmax⟩ :=
    hM.theorem4b_section7_exists_maximal_admissibleQ hT2 d s
  have hP₀sylE : theorem4bIsSylowSubgroupOf d.data.p a₀.Q E := by
    rw [hinit]
    exact a₀.hP₁sylow
  have hP₀leD : a₀.Q ≤ D :=
    (theorem4bIsSylowSubgroupOf_le_final hP₀sylE).trans hED
  have hP₀notD : ¬ theorem4bIsSylowSubgroupOf d.data.p a₀.Q D := by
    intro hP₀D
    have heq := (d.lemma62 hM s.hbetaK s.hbetaNe).1
      ⟨a₀.Q, hP₀D, a₀.hzNormQ⟩
    rw [heq] at hltCard
    exact (Nat.lt_irrefl _ hltCard)
  have hP₁leD : a.P₁ ≤ D :=
    (theorem4bIsSylowSubgroupOf_le_final a.hP₁sylow).trans hED
  have hcardP₀P₁ : Nat.card a₀.Q = Nat.card a.P₁ := by
    rw [hinit]
    exact theorem4bIsSylowSubgroupOf_card_eq_final
      d.data.hp a₀.hP₁sylow a.hP₁sylow
  have hP₁notD : ¬ theorem4bIsSylowSubgroupOf d.data.p a.P₁ D := by
    intro hP₁D
    apply hP₀notD
    exact theorem4bIsSylowSubgroupOf_of_subgroup_card_eq_final
      d.data.hp hP₁D hP₀leD hcardP₀P₁
  have hP₁p : IsPGroup d.data.p a.P₁ :=
    theorem4bIsSylowSubgroupOf_isPGroup_final a.hP₁sylow
  have hgrowth :=
    theorem4b_section7_factorization_lt_normalizerIn_of_not_sylow
      d.data.hp hP₁p hP₁leD hP₁notD
  have hnormEq := theorem4b_section7_normalizerIn_card_eq_of_sylow
    d.data.hp hP₀sylE a.hP₁sylow hED
  have hscoreInit := hmax a₀
  have hscoreP₁ :
      (Nat.card (theorem4bSection7NormalizerInD M s.beta a.P₁)).factorization
          d.data.p ≤
        (Nat.card (theorem4bSection7NormalizerInD M s.beta a.Q)).factorization
          d.data.p := by
    calc
      _ = (Nat.card (theorem4bSection7NormalizerInD M s.beta a₀.Q)).factorization
          d.data.p := by
        have hfac := congrArg (fun n : ℕ => n.factorization d.data.p)
          hnormEq.symm
        simpa [theorem4bSection7NormalizerInD, D] using hfac
      _ ≤ _ := hscoreInit
  refine ⟨a₀, a, hinit, hmax, hP₀notD, hP₁notD, ?_, hscoreP₁⟩
  change (Nat.card a.P₁).factorization d.data.p <
    (Nat.card ((theorem4bSection7D M s.beta ⊓
      Subgroup.normalizer (a.P₁ : Set X)) : Subgroup X)).factorization d.data.p
  exact hgrowth

/-- The complete maximal-`Q` package immediately before Lemma 7.10,
including the `t`-invariant Sylow subgroup `R` of `N_D(Q)` and the strict
cardinality comparison `|P₁| < |R|`. -/
public structure Theorem4bSection7MaximalQData
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixD M) (s : Theorem4bSection7SecondStage d) where
  initial : Theorem4bSection7AdmissibleQ d s
  chosen : Theorem4bSection7AdmissibleQ d s
  hinitial : initial.Q = initial.P₁
  maximal : ∀ b : Theorem4bSection7AdmissibleQ d s,
    (Nat.card (theorem4bSection7NormalizerInD M s.beta b.Q)).factorization
        d.data.p ≤
      (Nat.card (theorem4bSection7NormalizerInD M s.beta chosen.Q)).factorization
        d.data.p
  hInitialNotSylowD : ¬ theorem4bIsSylowSubgroupOf d.data.p initial.Q
    (theorem4bSection7D M s.beta)
  hP₁NotSylowD : ¬ theorem4bIsSylowSubgroupOf d.data.p chosen.P₁
    (theorem4bSection7D M s.beta)
  hP₁NormalizerGrowth : (Nat.card chosen.P₁).factorization d.data.p <
    (Nat.card (theorem4bSection7NormalizerInD M s.beta chosen.P₁)).factorization
      d.data.p
  hP₁NormalizerLeQ :
    (Nat.card (theorem4bSection7NormalizerInD M s.beta chosen.P₁)).factorization
        d.data.p ≤
      (Nat.card (theorem4bSection7NormalizerInD M s.beta chosen.Q)).factorization
        d.data.p
  R : Subgroup X
  hRsylow : theorem4bIsSylowSubgroupOf d.data.p R
    (theorem4bSection7NormalizerInD M s.beta chosen.Q)
  hP₁R : chosen.P₁ ≤ R
  htNormR : chosen.t ∈ Subgroup.normalizer (R : Set X)
  hP₁card_lt_R : Nat.card chosen.P₁ < Nat.card R

/-- The source subgroup `R` selected inside `N_D(Q)`. -/
@[expose] public def theorem4bSection7R
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {d : Theorem4bSixD M} {s : Theorem4bSection7SecondStage d}
    (q : Theorem4bSection7MaximalQData d s) : Subgroup X :=
  q.R

/-- The source subgroup `Z = Omega₁(Z(J(R)))`. -/
@[expose] public def theorem4bSection7Z
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {d : Theorem4bSixD M} {s : Theorem4bSection7SecondStage d}
    (q : Theorem4bSection7MaximalQData d s) : Subgroup X :=
  corollary64Z ⟨d.data.p, d.data.hp⟩ (theorem4bSection7R q)

/-- Proposition 3.7 applied inside `N_D(Q)` constructs the source subgroup
`R`; the preceding exponent inequalities give `|P₁| < |R|`. -/
public theorem IsStronglyEmbedded.theorem4b_section7_maximalQData
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N)
    (s : Theorem4bSection7SecondStage d) :
    Nonempty (Theorem4bSection7MaximalQData d s) := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  obtain ⟨a₀, a, hinit, hmax, hP₀notD, hP₁notD, hgrowth, hscore⟩ :=
    hM.theorem4b_section7_maximalQ_normalizer_chain
      hX d hrank hT2 hinduction s
  let D : Subgroup X := theorem4bSection7D M s.beta
  let NDQ : Subgroup X := theorem4bSection7NormalizerInD M s.beta a.Q
  have hED : theorem4bSection7E M d.data.z s.beta ≤ D := by
    change theorem4bSection7D M s.beta ⊓
      MulAction.stabilizer X (d.data.z • s.beta) ≤
      theorem4bSection7D M s.beta
    exact inf_le_left
  have hP₁D : a.P₁ ≤ D :=
    (theorem4bIsSylowSubgroupOf_le_final a.hP₁sylow).trans hED
  have hP₁NDQ : a.P₁ ≤ NDQ := by
    exact le_inf hP₁D a.hP₁NormQ
  have htNormD : a.t ∈ Subgroup.normalizer (D : Set X) := by
    have hnorm := theorem4b_mem_normalizer_tripleStabilizer
      (M := (⊤ : Subgroup X)) (z := a.t)
      (beta := theorem4bSection7Base (X := X) (M := M))
      a.ht (Subgroup.mem_top a.t)
    simpa [D, theorem4bSection7D, theorem4bSection7Base,
      baseCoset_stabilizer, a.htBase] using hnorm
  have htNormNQ : a.t ∈
      Subgroup.normalizer (Subgroup.normalizer (a.Q : Set X) : Set X) :=
    Subgroup.le_normalizer a.htNormQ
  have htNormNDQ : a.t ∈ Subgroup.normalizer (NDQ : Set X) := by
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨htNormD, htNormNQ⟩
  have hDodd : Odd (Nat.card D) := by
    simpa [D, theorem4bSection7D] using
      hM.base_inf_stabilizer_card_odd s.hbetaNe
  have hNDQodd : Odd (Nat.card NDQ) := by
    exact Odd.of_dvd_nat hDodd
      (Subgroup.card_dvd_of_le (show NDQ ≤ D from inf_le_left))
  have hP₁p : IsPGroup d.data.p a.P₁ :=
    theorem4bIsSylowSubgroupOf_isPGroup_final a.hP₁sylow
  obtain ⟨R, hRsylow, hP₁R, htNormR⟩ :=
    theorem4b_exists_invariant_sylow_containing hNDQodd a.ht htNormNDQ
      d.data.hp hP₁p hP₁NDQ a.htNormP₁
  have hfac : (Nat.card a.P₁).factorization d.data.p <
      (Nat.card NDQ).factorization d.data.p :=
    lt_of_lt_of_le hgrowth hscore
  have hRcard : Nat.card R =
      d.data.p ^ (Nat.card NDQ).factorization d.data.p := by
    rcases hRsylow with ⟨RN, hReq⟩
    rw [hReq, Subgroup.card_map_of_injective NDQ.subtype_injective]
    exact Sylow.card_eq_multiplicity RN
  have hP₁card : Nat.card a.P₁ =
      d.data.p ^ (Nat.card a.P₁).factorization d.data.p :=
    section8_card_eq_prime_pow_factorization_of_isPGroup hP₁p
  have hP₁card_lt_R : Nat.card a.P₁ < Nat.card R := by
    rw [hP₁card, hRcard]
    exact Nat.pow_lt_pow_right d.data.hp.one_lt hfac
  exact ⟨{
    initial := a₀
    chosen := a
    hinitial := hinit
    maximal := hmax
    hInitialNotSylowD := hP₀notD
    hP₁NotSylowD := hP₁notD
    hP₁NormalizerGrowth := hgrowth
    hP₁NormalizerLeQ := hscore
    R := R
    hRsylow := hRsylow
    hP₁R := hP₁R
    htNormR := htNormR
    hP₁card_lt_R := hP₁card_lt_R }⟩

/-! ## Lemma 7.10: the `[II1; 4.1]` invariant-Sylow core -/

/-- If `G = O_{2'}(G) C_G(u)`, then `u` normalizes the subgroup generated by
`O_{2'}(G)` and any supplied subgroup.  This is the normalizer input used in
the proof of `[II1; 4.1]`. -/
private theorem theorem4b_mem_normalizer_oddCore_sup_of_factorization
    {G : Type*} [Group G] [Finite G]
    {u : G} (hu : IsInvolution u) (B : Subgroup G)
    (hfactor : pPrimeCore 2 G ⊔
      Subgroup.centralizer ({u} : Set G) = ⊤) :
    u ∈ Subgroup.normalizer
      ((pPrimeCore 2 G ⊔ B : Subgroup G) : Set G) := by
  classical
  let O : Subgroup G := pPrimeCore 2 G
  let H : Subgroup G := O ⊔ B
  have hOnormal : O.Normal := by
    dsimp [O]
    exact pPrimeCore_normal
  letI : O.Normal := hOnormal
  have hforward : ∀ x : G, x ∈ H → u * x * u⁻¹ ∈ H := by
    intro x hx
    rcases Subgroup.mem_sup_of_normal_left.mp hx with
      ⟨o, hoO, b, hbB, hob⟩
    have hbFactor : b ∈ O ⊔ Subgroup.centralizer ({u} : Set G) := by
      rw [hfactor]
      trivial
    rcases Subgroup.mem_sup_of_normal_left.mp hbFactor with
      ⟨o', ho'O, c, hcC, hoc⟩
    have hcH : c ∈ H := by
      have hcEq : c = o'⁻¹ * b := by
        calc
          c = o'⁻¹ * (o' * c) := by group
          _ = o'⁻¹ * b := by rw [hoc]
      rw [hcEq]
      exact H.mul_mem
        (H.inv_mem ((le_sup_left : O ≤ O ⊔ B) ho'O))
        ((le_sup_right : B ≤ O ⊔ B) hbB)
    have hconjO : u * o * u⁻¹ ∈ O := hOnormal.conj_mem o hoO u
    have hconjO' : u * o' * u⁻¹ ∈ O := hOnormal.conj_mem o' ho'O u
    have hcu : Commute c u := by
      exact (commute_iff_eq c u).mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hcC)
    have hconjB : u * b * u⁻¹ ∈ H := by
      have hEq : u * b * u⁻¹ = (u * o' * u⁻¹) * c := by
        calc
          u * b * u⁻¹ = u * (o' * c) * u⁻¹ := by rw [hoc]
          _ = u * o' * (c * u⁻¹) := by simp only [mul_assoc]
          _ = u * o' * (u⁻¹ * c) := by rw [hcu.inv_right.eq]
          _ = (u * o' * u⁻¹) * c := by simp only [mul_assoc]
      rw [hEq]
      exact H.mul_mem ((le_sup_left : O ≤ O ⊔ B) hconjO') hcH
    have hEq : u * x * u⁻¹ =
        (u * o * u⁻¹) * (u * b * u⁻¹) := by
      rw [← hob]
      group
    rw [hEq]
    exact H.mul_mem ((le_sup_left : O ≤ O ⊔ B) hconjO) hconjB
  change u ∈ Subgroup.normalizer (H : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward x
  · intro hx
    have htwice := hforward (u * x * u⁻¹) hx
    have huInv : u⁻¹ = u := by
      apply mul_left_cancel (a := u)
      simpa [← pow_two, hu.sq_eq_one]
    rw [huInv] at htwice
    have huu : u * u = 1 := by simpa [pow_two] using hu.sq_eq_one
    have hEq : u * (u * x * u) * u = x := by
      calc
        u * (u * x * u) * u = (u * u) * x * (u * u) := by group
        _ = x := by rw [huu]; simp
    rw [hEq] at htwice
    exact htwice

/-- For odd `p`, adjoining a Sylow `p`-subgroup to `O_{2'}(G)` still gives
an odd-order subgroup. -/
private theorem theorem4b_odd_card_oddCore_sup_sylow
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : Nat.Prime p) (hpOdd : Odd p)
    (B : Sylow p G) :
    Odd (Nat.card (pPrimeCore 2 G ⊔ (B : Subgroup G) : Subgroup G)) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact p.Prime := ⟨hp⟩
  let O : Subgroup G := pPrimeCore 2 G
  let H : Subgroup G := O ⊔ (B : Subgroup G)
  have hOnormal : O.Normal := by
    dsimp [O]
    exact pPrimeCore_normal
  letI : O.Normal := hOnormal
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using pPrimeCore_coprime_card (p := 2) (G := G)
  have hBodd : Odd (Nat.card (B : Subgroup G)) := by
    rw [B.card_eq_multiplicity]
    exact hpOdd.pow
  have hBcop : Nat.Coprime 2 (Nat.card (B : Subgroup G)) :=
    hBodd.coprime_two_left
  have hmul : (H : Set G) =
      ((B : Subgroup G) : Set G) * (O : Set G) := by
    simpa [H, sup_comm] using
      (Subgroup.mul_normal (B : Subgroup G) O)
  have hcardH : Nat.card H =
      Nat.card (((B : Subgroup G) : Set G) * (O : Set G) : Set G) := by
    exact Nat.card_congr (Set.equivOfEq hmul)
  have hcardMul :
      Nat.card (((B : Subgroup G) : Set G) * (O : Set G) : Set G) =
        Nat.card O *
          Nat.card (((B : Subgroup G) : Set G).image (↑) : Set (G ⧸ O)) := by
    simpa using
      (Subgroup.card_mul_eq_card_subgroup_mul_card_quotient
        (s := O) (t := ((B : Subgroup G) : Set G)))
  have hsetImage :
      (((B : Subgroup G) : Set G).image (↑) : Set (G ⧸ O)) =
        ((B : Subgroup G).map (QuotientGroup.mk' O) : Set (G ⧸ O)) := by
    simp [Subgroup.coe_map]
  have hcardImageSet :
      Nat.card (((B : Subgroup G) : Set G).image (↑) : Set (G ⧸ O)) =
        Nat.card ((B : Subgroup G).map (QuotientGroup.mk' O) : Set (G ⧸ O)) :=
    Nat.card_congr (Set.equivOfEq hsetImage)
  have hcardImageSubgroup :
      Nat.card (((B : Subgroup G) : Set G).image (↑) : Set (G ⧸ O)) =
        Nat.card ((B : Subgroup G).map (QuotientGroup.mk' O)) := by
    exact hcardImageSet
  have himageDvd :
      Nat.card ((B : Subgroup G).map (QuotientGroup.mk' O)) ∣
        Nat.card (B : Subgroup G) :=
    Subgroup.card_map_dvd (B : Subgroup G) (QuotientGroup.mk' O)
  have himageCop : Nat.Coprime 2
      (Nat.card (((B : Subgroup G) : Set G).image (↑) : Set (G ⧸ O))) := by
    have hcop : Nat.Coprime 2
        (Nat.card ((B : Subgroup G).map (QuotientGroup.mk' O))) :=
      Nat.Coprime.of_dvd_right himageDvd hBcop
    rw [hcardImageSubgroup]
    exact hcop
  apply Nat.coprime_two_left.mp
  rw [hcardH, hcardMul]
  exact Nat.Coprime.mul_right hOcop himageCop

/-- `[II1; 4.1]` in the exact form used by Lemma 7.10.  If the operational
`Z*` factorization holds for an involution `u`, then every `u`-invariant
`p`-subgroup for odd `p` lies in a `u`-invariant Sylow `p`-subgroup. -/
public theorem exists_invariant_sylow_containing_of_pPrimeCore_sup_centralizer_eq_top
    {G : Type*} [Group G] [Finite G]
    {u : G} (hu : IsInvolution u)
    {p : ℕ} (hp : Nat.Prime p) (hpOdd : Odd p)
    {P : Subgroup G} (hPp : IsPGroup p P)
    (huNormP : u ∈ Subgroup.normalizer (P : Set G))
    (hfactor : pPrimeCore 2 G ⊔
      Subgroup.centralizer ({u} : Set G) = ⊤) :
    ∃ S : Sylow p G,
      P ≤ (S : Subgroup G) ∧
        u ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hPB⟩ := hPp.exists_le_sylow
  let H : Subgroup G := pPrimeCore 2 G ⊔ (B : Subgroup G)
  have hBH : (B : Subgroup G) ≤ H := le_sup_right
  have hPH : P ≤ H := hPB.trans hBH
  have hHodd : Odd (Nat.card H) := by
    simpa [H] using theorem4b_odd_card_oddCore_sup_sylow hp hpOdd B
  have huNormH : u ∈ Subgroup.normalizer (H : Set G) := by
    simpa [H] using
      theorem4b_mem_normalizer_oddCore_sup_of_factorization
        hu (B : Subgroup G) hfactor
  obtain ⟨Q, hQSylH, hPQ, huNormQ⟩ :=
    theorem4b_exists_invariant_sylow_containing
      hHodd hu huNormH hp hPp hPH huNormP
  rcases hQSylH with ⟨QH, hQeq⟩
  let BH : Sylow p H := B.subtype hBH
  have hQcard : Nat.card Q = Nat.card (B : Subgroup G) := by
    calc
      Nat.card Q = Nat.card (QH : Subgroup H) := by
        rw [hQeq, Subgroup.card_map_of_injective H.subtype_injective]
      _ = p ^ (Nat.card H).factorization p := QH.card_eq_multiplicity
      _ = Nat.card (BH : Subgroup H) := BH.card_eq_multiplicity.symm
      _ = Nat.card (B : Subgroup G) := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hQcardGlobal : Nat.card Q =
      p ^ (Nat.card G).factorization p := by
    rw [hQcard]
    exact B.card_eq_multiplicity
  let S : Sylow p G := Sylow.ofCard Q hQcardGlobal
  refine ⟨S, ?_, ?_⟩
  · simpa [S] using hPQ
  · simpa [S] using huNormQ

/-- The operational `Z*` factorization inherited by a subgroup containing the
centralizer of the distinguished involution. -/
private theorem theorem4b_lemma710_factorization_subgroup
    {G : Type*} [Group G] [Finite G]
    (M : Subgroup G) {z : G} (hzM : z ∈ M)
    (hcentM : Subgroup.centralizer ({z} : Set G) ≤ M)
    (hfactor : pPrimeCore 2 G ⊔
      Subgroup.centralizer ({z} : Set G) = ⊤) :
    let zM : M := ⟨z, hzM⟩
    pPrimeCore 2 M ⊔ Subgroup.centralizer ({zM} : Set M) = ⊤ := by
  classical
  let zM : M := ⟨z, hzM⟩
  let O : Subgroup G := pPrimeCore 2 G
  let OM : Subgroup M := O.comap M.subtype
  have hOnormal : O.Normal := by
    dsimp [O]
    exact pPrimeCore_normal
  letI : O.Normal := hOnormal
  have hOMnormal : OM.Normal := by infer_instance
  letI : OM.Normal := hOMnormal
  have hOMmapLe : OM.map M.subtype ≤ O := by
    rw [Subgroup.map_le_iff_le_comap]
  have hOMcard : Nat.card OM ∣ Nat.card O := by
    calc
      Nat.card OM = Nat.card (OM.map M.subtype) := by
        symm
        exact Subgroup.card_map_of_injective M.subtype_injective
      _ ∣ Nat.card O := Subgroup.card_dvd_of_le hOMmapLe
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using pPrimeCore_coprime_card (p := 2) (G := G)
  have hOMcop : Nat.Coprime 2 (Nat.card OM) :=
    Nat.Coprime.of_dvd_right hOMcard hOcop
  have hOMle : OM ≤ pPrimeCore 2 M := le_sSup ⟨hOMnormal, hOMcop⟩
  apply top_unique
  intro m _hm
  have hmSup : (m : G) ∈ O ⊔ Subgroup.centralizer ({z} : Set G) := by
    rw [hfactor]
    trivial
  rcases Subgroup.mem_sup_of_normal_left.mp hmSup with
    ⟨o, hoO, c, hcC, hoc⟩
  have hcM : c ∈ M := hcentM hcC
  have hoM : o ∈ M := by
    have : (m : G) * c⁻¹ ∈ M := M.mul_mem m.property (M.inv_mem hcM)
    rwa [← hoc, mul_inv_cancel_right] at this
  let oM : M := ⟨o, hoM⟩
  let cM : M := ⟨c, hcM⟩
  have hoOM : oM ∈ OM := hoO
  have hoCore : oM ∈ pPrimeCore 2 M := hOMle hoOM
  have hcCM : cM ∈ Subgroup.centralizer ({zM} : Set M) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hcC
  have hprod := Subgroup.mul_mem_sup hoCore hcCM
  have hprodEq : oM * cM = m := by
    apply Subtype.ext
    exact hoc
  rwa [hprodEq] at hprod

/-- Cardinality comparison with a Sylow subgroup represented in an ambient
group by `theorem4bIsSylowSubgroupOf`. -/
private theorem theorem4b_lemma710_card_le_sylow_of_isPGroup
    {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : Nat.Prime p) {P Q E : Subgroup X}
    (hPp : IsPGroup p P) (hPE : P ≤ E)
    (hQsyl : theorem4bIsSylowSubgroupOf p Q E) :
    Nat.card P ≤ Nat.card Q := by
  letI : Fact p.Prime := ⟨hp⟩
  let PE : Subgroup E := P.subgroupOf E
  have hPEp : IsPGroup p PE :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPE).symm
  obtain ⟨S, hPES⟩ := hPEp.exists_le_sylow
  rcases hQsyl with ⟨QE, hQeq⟩
  calc
    Nat.card P = Nat.card PE := (natCard_subgroupOf_eq P E hPE).symm
    _ ≤ Nat.card (S : Subgroup E) := Subgroup.card_le_of_le hPES
    _ = Nat.card (QE : Subgroup E) := by
      rw [S.card_eq_multiplicity, QE.card_eq_multiplicity]
    _ = Nat.card Q := by
      rw [hQeq, Subgroup.card_map_of_injective E.subtype_injective]

/-- A `p`-subgroup fixing a source triple has cardinality at most the selected
Sylow subgroup `P₁` of the reference triple stabilizer. -/
private theorem theorem4b_lemma710_card_le_P₁_of_le_tripleStabilizer
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (d : Theorem4bSixD M) (s : Theorem4bSection7SecondStage d)
    (a : Theorem4bSection7AdmissibleQ d s)
    {w : X} (hw : IsInvolution w)
    {gamma delta : conjugateCosetSpace M}
    (hwGamma : w • gamma = gamma) (hgammaDelta : gamma ≠ delta)
    {P : Subgroup X} (hPp : IsPGroup d.data.p P)
    (hPtriple : P ≤
      (MulAction.stabilizer X gamma ⊓ MulAction.stabilizer X delta) ⊓
        MulAction.stabilizer X (w • delta)) :
    Nat.card P ≤ Nat.card a.P₁ := by
  obtain ⟨g, hgGamma, hgDelta, hgw⟩ :=
    lemma61_triple_transport hM htwo d.data.hzM d.data.hz hw
      hwGamma hgammaDelta s.hbetaNe
  have hconj := lemma73_tripleStabilizer_conjBy_eq_E
    hgGamma hgDelta hgw
  let Pg : Subgroup X := P.conjBy g
  have hPgp : IsPGroup d.data.p Pg := by
    exact hPp.map (MulAut.conj g).toMonoidHom
  have hPgE : Pg ≤ theorem4bSection7E M d.data.z s.beta := by
    change P.map (MulAut.conj g).toMonoidHom ≤ _
    rw [← hconj]
    exact Subgroup.map_mono hPtriple
  have hcardPg : Nat.card Pg = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [← hcardPg]
  exact theorem4b_lemma710_card_le_sylow_of_isPGroup
    d.data.hp hPgp hPgE a.hP₁sylow

/-- Conjugating a subgroup transports both its fixed point and uniqueness of
that fixed point. -/
private theorem theorem4b_lemma710_conjBy_fixed_unique
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (P : Subgroup G) (g : G) (alpha : Omega)
    (hfix : P ≤ MulAction.stabilizer G alpha)
    (hunique : ∀ omega : Omega,
      P ≤ MulAction.stabilizer G omega → omega = alpha) :
    P.conjBy g ≤ MulAction.stabilizer G (g • alpha) ∧
      ∀ omega : Omega,
        P.conjBy g ≤ MulAction.stabilizer G omega → omega = g • alpha := by
  constructor
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    apply MulAction.mem_stabilizer_iff.mpr
    have hpfix := MulAction.mem_stabilizer_iff.mp (hfix hp)
    simp [MulAut.conj_apply, mul_smul, hpfix]
  · intro omega homega
    have hpre : P ≤ MulAction.stabilizer G (g⁻¹ • omega) := by
      intro p hp
      have hconj : g * p * g⁻¹ ∈ P.conjBy g := by
        exact Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
      have hfixConj := MulAction.mem_stabilizer_iff.mp (homega hconj)
      apply MulAction.mem_stabilizer_iff.mpr
      calc
        p • (g⁻¹ • omega) = g⁻¹ • ((g * p * g⁻¹) • omega) := by
          simp [mul_smul]
        _ = g⁻¹ • omega := by rw [hfixConj]
    have hpreEq := hunique (g⁻¹ • omega) hpre
    calc
      omega = g • (g⁻¹ • omega) := (smul_inv_smul g omega).symm
      _ = g • alpha := by rw [hpreEq]

/-- Lemma 7.10.  For the normalizer `N = N_X(Q)` selected by the maximal
`Q` construction, not every involution satisfies the operational `Z*`
factorization in `N`. -/
public theorem IsStronglyEmbedded.theorem4b_lemma710
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    let N : Subgroup X := Subgroup.normalizer (q.chosen.Q : Set X)
    ¬ ∀ u : N, IsInvolution u →
      pPrimeCore 2 N ⊔ Subgroup.centralizer ({u} : Set N) = ⊤ := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let a := q.chosen
  let N : Subgroup X := Subgroup.normalizer (a.Q : Set X)
  let NA : Subgroup N := M.comap N.subtype
  let alpha : conjugateCosetSpace M := theorem4bSection7Base
  dsimp only
  intro hfactorAll
  have h72 : Theorem4bProposition72 d.data :=
    ⟨s.beta, s.hbetaK, s.hbetaNe, s.htheta⟩
  have htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2 :=
    hM.theorem4b_proposition78 hX d hrank hT2 hinduction h72
  have hzNmem : d.data.z ∈ N := a.hzNormQ
  let zN : N := ⟨d.data.z, hzNmem⟩
  have hzNI : IsInvolution zN := IsInvolution.subtype d.data.hz hzNmem
  have hzFactor : pPrimeCore 2 N ⊔
      Subgroup.centralizer ({zN} : Set N) = ⊤ := hfactorAll zN hzNI
  have hzNA : zN ∈ NA := by
    exact d.data.hzM
  have hcentNA : Subgroup.centralizer ({zN} : Set N) ≤ NA := by
    intro x hx
    change ((x : N) : X) ∈ M
    apply hM.centralizer_le d.data.hzM d.data.hz
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp hx)
  let zA : NA := ⟨zN, hzNA⟩
  have hzAI : IsInvolution zA := IsInvolution.subtype hzNI hzNA
  have hzAFactor : pPrimeCore 2 NA ⊔
      Subgroup.centralizer ({zA} : Set NA) = ⊤ := by
    simpa [zA] using theorem4b_lemma710_factorization_subgroup
      NA hzNA hcentNA hzFactor
  obtain ⟨Pstar, _hbot, hzANormPstar⟩ :=
    exists_invariant_sylow_containing_of_pPrimeCore_sup_centralizer_eq_top
      hzAI d.data.hp d.data.hpOdd (P := (⊥ : Subgroup NA))
      (IsPGroup.of_bot (p := d.data.p) (G := NA)) (by
        rw [Subgroup.normalizer_eq_top_iff.mpr
          (inferInstance : (⊥ : Subgroup NA).Normal)]
        trivial) hzAFactor
  let PstarN : Subgroup N := (Pstar : Subgroup NA).map NA.subtype
  let PstarX : Subgroup X := PstarN.map N.subtype
  have hPstarNp : IsPGroup d.data.p PstarN :=
    Pstar.isPGroup'.map NA.subtype
  have hPstarXp : IsPGroup d.data.p PstarX :=
    hPstarNp.map N.subtype
  have hPstarNNA : PstarN ≤ NA := by
    exact Subgroup.map_subtype_le (Pstar : Subgroup NA)
  have hPstarXAlpha : PstarX ≤ MulAction.stabilizer X alpha := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xN, hxN, rfl⟩
    have hxNA : xN ∈ NA := hPstarNNA hxN
    apply MulAction.mem_stabilizer_iff.mpr
    change ((xN : N) : X) • alpha = alpha
    apply MulAction.mem_stabilizer_iff.mp
    rw [show MulAction.stabilizer X alpha = M by
      simp [alpha, theorem4bSection7Base]]
    exact hxNA
  have hzNNormPstarN : zN ∈
      Subgroup.normalizer (PstarN : Set N) := by
    have hzMap : zN ∈
        (Subgroup.normalizer ((Pstar : Subgroup NA) : Set NA)).map
          NA.subtype :=
      Subgroup.mem_map.mpr ⟨zA, hzANormPstar, rfl⟩
    exact (Subgroup.le_normalizer_map
      (H := (Pstar : Subgroup NA)) NA.subtype) hzMap
  have hzXNormPstarX : d.data.z ∈
      Subgroup.normalizer (PstarX : Set X) := by
    have hzMap : d.data.z ∈
        (Subgroup.normalizer (PstarN : Set N)).map N.subtype :=
      Subgroup.mem_map.mpr ⟨zN, hzNNormPstarN, rfl⟩
    exact (Subgroup.le_normalizer_map (H := PstarN) N.subtype) hzMap
  have hRleNDQ : q.R ≤ theorem4bSection7NormalizerInD M s.beta a.Q :=
    theorem4bIsSylowSubgroupOf_le_final q.hRsylow
  have hRN : q.R ≤ N := by
    exact hRleNDQ.trans inf_le_right
  let RN : Subgroup N := q.R.subgroupOf N
  have hRNA : RN ≤ NA := by
    intro r hr
    change ((r : N) : X) ∈ M
    have hrR : ((r : N) : X) ∈ q.R := hr
    exact (hRleNDQ hrR).1.1
  have hRNp : IsPGroup d.data.p RN := by
    have hRp : IsPGroup d.data.p q.R :=
      theorem4bIsSylowSubgroupOf_isPGroup_final q.hRsylow
    exact hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm
  have hRcard_le_PstarN : Nat.card q.R ≤ Nat.card PstarN := by
    have hcardRN : Nat.card RN = Nat.card q.R :=
      natCard_subgroupOf_eq q.R N hRN
    rw [← hcardRN]
    exact theorem4b_lemma710_card_le_sylow_of_isPGroup d.data.hp
      hRNp hRNA ⟨Pstar, rfl⟩
  have hPstarNcardX : Nat.card PstarX = Nat.card PstarN :=
    Subgroup.card_map_of_injective N.subtype_injective
  have hPstarUniqueX : ∀ delta : conjugateCosetSpace M,
      PstarX ≤ MulAction.stabilizer X delta → delta = alpha := by
    intro delta hPdelta
    by_contra hdelta
    have hPzdelta : PstarX ≤ MulAction.stabilizer X (d.data.z • delta) :=
      theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
        hzXNormPstarX hPdelta
    have hPtriple : PstarX ≤
        (MulAction.stabilizer X alpha ⊓ MulAction.stabilizer X delta) ⊓
          MulAction.stabilizer X (d.data.z • delta) :=
      le_inf (le_inf hPstarXAlpha hPdelta) hPzdelta
    have hzAlpha : d.data.z • alpha = alpha := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [show MulAction.stabilizer X alpha = M by
        simp [alpha, theorem4bSection7Base]]
      exact d.data.hzM
    have hcardLe := theorem4b_lemma710_card_le_P₁_of_le_tripleStabilizer
      hM htwo d s a d.data.hz hzAlpha (Ne.symm hdelta)
      hPstarXp hPtriple
    have hPstarNcard_le_P₁ : Nat.card PstarN ≤ Nat.card a.P₁ := by
      simpa [hPstarNcardX] using hcardLe
    have hRcard_le_P₁ : Nat.card q.R ≤ Nat.card a.P₁ :=
      hRcard_le_PstarN.trans hPstarNcard_le_P₁
    exact (not_lt_of_ge hRcard_le_P₁) (by
      simpa [a] using q.hP₁card_lt_R)
  have hnormalizerPstar_le_NA :
      Subgroup.normalizer (PstarN : Set N) ≤ NA := by
    intro n hn
    have hfixConj : PstarX ≤
        MulAction.stabilizer X ((n : X) • alpha) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨p, hpPstar, rfl⟩
      have hconjP : n⁻¹ * p * n ∈ PstarN :=
        (Subgroup.mem_normalizer_iff''.mp hn p).mp hpPstar
      have hconjFix : ((n⁻¹ * p * n : N) : X) • alpha = alpha := by
        apply MulAction.mem_stabilizer_iff.mp
        rw [show MulAction.stabilizer X alpha = M by
          simp [alpha, theorem4bSection7Base]]
        exact hPstarNNA hconjP
      apply MulAction.mem_stabilizer_iff.mpr
      calc
        ((p : N) : X) • (((n : N) : X) • alpha) =
            ((n : N) : X) • (((n⁻¹ * p * n : N) : X) • alpha) := by
          simp [mul_smul]
        _ = ((n : N) : X) • alpha := by rw [hconjFix]
    have hnFix : ((n : N) : X) • alpha = alpha :=
      hPstarUniqueX _ hfixConj
    change ((n : N) : X) ∈ M
    rw [← baseCoset_stabilizer M]
    exact MulAction.mem_stabilizer_iff.mpr (by
      simpa [alpha, theorem4bSection7Base] using hnFix)
  have hPstarSylowTop : theorem4bIsSylowSubgroupOf d.data.p PstarN
      (⊤ : Subgroup N) := by
    by_contra hnotSylow
    have hgrowth :=
      theorem4b_section7_factorization_lt_normalizerIn_of_not_sylow
        d.data.hp hPstarNp (show PstarN ≤ (⊤ : Subgroup N) from le_top)
        hnotSylow
    have hnormLe :
        (⊤ : Subgroup N) ⊓ Subgroup.normalizer (PstarN : Set N) ≤ NA := by
      simpa using hnormalizerPstar_le_NA
    have hfacLe :
        Nat.factorization
            (Nat.card (((⊤ : Subgroup N) ⊓
              Subgroup.normalizer (PstarN : Set N)) : Subgroup N)) d.data.p ≤
          Nat.factorization (Nat.card NA) d.data.p :=
      Nat.factorization_le_factorization_of_dvd_right
        (Subgroup.card_dvd_of_le hnormLe) Nat.card_pos.ne' Nat.card_pos.ne'
    have hPstarCard : Nat.card PstarN =
        d.data.p ^ (Nat.card NA).factorization d.data.p := by
      dsimp [PstarN]
      rw [Subgroup.card_map_of_injective NA.subtype_injective]
      exact Pstar.card_eq_multiplicity
    have hfacEq : (Nat.card PstarN).factorization d.data.p =
        (Nat.card NA).factorization d.data.p := by
      rw [hPstarCard, Nat.factorization_pow_self d.data.hp]
    rw [hfacEq] at hgrowth
    exact (not_lt_of_ge hfacLe) hgrowth
  rcases hPstarSylowTop with ⟨Ptop, hPtop⟩
  have hPstarCardN : Nat.card PstarN =
      d.data.p ^ (Nat.card N).factorization d.data.p := by
    calc
      Nat.card PstarN = Nat.card (Ptop : Subgroup (⊤ : Subgroup N)) := by
        rw [hPtop, Subgroup.card_map_of_injective
          (⊤ : Subgroup N).subtype_injective]
      _ = d.data.p ^ (Nat.card (⊤ : Subgroup N)).factorization d.data.p :=
        Ptop.card_eq_multiplicity
      _ = d.data.p ^ (Nat.card N).factorization d.data.p := by simp
  let P0 : Sylow d.data.p N := Sylow.ofCard PstarN hPstarCardN
  have hP0coe : (P0 : Subgroup N) = PstarN := by rfl
  have htNmem : a.t ∈ N := a.htNormQ
  let tN : N := ⟨a.t, htNmem⟩
  have htNI : IsInvolution tN := IsInvolution.subtype a.ht htNmem
  have htFactor : pPrimeCore 2 N ⊔
      Subgroup.centralizer ({tN} : Set N) = ⊤ := hfactorAll tN htNI
  have htNormRN : tN ∈ Subgroup.normalizer (RN : Set N) := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    change ((r : N) : X) ∈ q.R ↔
      a.t * ((r : N) : X) * a.t⁻¹ ∈ q.R
    exact (Subgroup.mem_normalizer_iff.mp q.htNormR ((r : N) : X))
  obtain ⟨Rstar, hRNRstar, htNormRstar⟩ :=
    exists_invariant_sylow_containing_of_pPrimeCore_sup_centralizer_eq_top
      htNI d.data.hp d.data.hpOdd hRNp htNormRN htFactor
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N P0 Rstar
  have hRstarEq : (Rstar : Subgroup N) = PstarN.conjBy n := by
    have hcoe := congrArg
      (fun S : Sylow d.data.p N => (S : Subgroup N)) hn
    have hconjHom :
        (MulDistribMulAction.toMonoidEnd (MulAut N) N) (MulAut.conj n) =
          (MulAut.conj n).toMonoidHom := by
      ext x
      rfl
    simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      hP0coe] at hcoe
    rw [hconjHom] at hcoe
    symm
    simpa only [Subgroup.conjBy] using hcoe
  have hPstarFixAlphaN : PstarN ≤ MulAction.stabilizer N alpha := by
    intro p hp
    apply MulAction.mem_stabilizer_iff.mpr
    change ((p : N) : X) • alpha = alpha
    apply MulAction.mem_stabilizer_iff.mp
    exact hPstarXAlpha (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)
  have hPstarUniqueN : ∀ omega : conjugateCosetSpace M,
      PstarN ≤ MulAction.stabilizer N omega → omega = alpha := by
    intro omega homega
    apply hPstarUniqueX omega
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    exact homega hp
  have hconjFix := theorem4b_lemma710_conjBy_fixed_unique
    PstarN n alpha hPstarFixAlphaN hPstarUniqueN
  have hRstarFix : (Rstar : Subgroup N) ≤
      MulAction.stabilizer N (n • alpha) := by
    rw [hRstarEq]
    exact hconjFix.1
  have hRstarUnique : ∀ omega : conjugateCosetSpace M,
      (Rstar : Subgroup N) ≤ MulAction.stabilizer N omega →
        omega = n • alpha := by
    intro omega homega
    rw [hRstarEq] at homega
    exact hconjFix.2 omega homega
  have htRstarPoint : tN • (n • alpha) = n • alpha := by
    apply hRstarUnique
    exact theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
      htNormRstar hRstarFix
  obtain ⟨gamma, htGamma, hgammaUnique⟩ :=
    hM.involution_fixed_coset_unique a.ht
  have hpointEq : n • alpha = gamma := by
    apply hgammaUnique
    change (⟨a.t, htNmem⟩ : N) • (n • alpha) = n • alpha
    exact htRstarPoint
  have hRgamma : q.R ≤ MulAction.stabilizer X gamma := by
    intro r hr
    let rN : N := ⟨r, hRN hr⟩
    have hrRN : rN ∈ RN := hr
    have hrRstar : rN ∈ (Rstar : Subgroup N) := hRNRstar hrRN
    have hrFix := MulAction.mem_stabilizer_iff.mp (hRstarFix hrRstar)
    apply MulAction.mem_stabilizer_iff.mpr
    change rN • gamma = gamma
    simpa [hpointEq] using hrFix
  have hRalpha : q.R ≤ MulAction.stabilizer X alpha := by
    intro r hr
    have hrM : r ∈ M := (hRleNDQ hr).1.1
    apply MulAction.mem_stabilizer_iff.mp
    rw [show MulAction.stabilizer X alpha = M by
      simp [alpha, theorem4bSection7Base]]
    exact hrM
  have hRtalpha : q.R ≤ MulAction.stabilizer X (a.t • alpha) :=
    theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
      q.htNormR hRalpha
  have hgammaAlpha : gamma ≠ alpha := by
    intro heq
    have htAlpha : a.t • alpha = alpha := by simpa [heq] using htGamma
    exact s.hbetaNe (a.htBase.symm.trans htAlpha)
  have hRtriple : q.R ≤
      (MulAction.stabilizer X gamma ⊓ MulAction.stabilizer X alpha) ⊓
        MulAction.stabilizer X (a.t • alpha) :=
    le_inf (le_inf hRgamma hRalpha) hRtalpha
  have hRcardLe := theorem4b_lemma710_card_le_P₁_of_le_tripleStabilizer
    hM htwo d s a a.ht htGamma hgammaAlpha
      (theorem4bIsSylowSubgroupOf_isPGroup_final q.hRsylow) hRtriple
  exact (not_lt_of_ge hRcardLe) (by
    simpa [a] using q.hP₁card_lt_R)

/-- A four-group in a group is also a four-group in its involution core. -/
private theorem theorem4b_twoRank_involutionCore_of_twoRank
    {G : Type*} [Group G]
    (hrank : TwoRankAtLeastTwo G) :
    TwoRankAtLeastTwo (involutionCore G) := by
  obtain ⟨E, hEcard, hEsq⟩ := TwoRankAtLeastTwo.exists_subgroup hrank
  have hEcore : E ≤ involutionCore G := by
    intro x hx
    by_cases hx1 : x = 1
    · simpa [hx1]
    rw [involutionCore_eq_closure]
    apply Subgroup.subset_closure
    refine ⟨hx1, ?_⟩
    exact congrArg Subtype.val (hEsq ⟨x, hx⟩)
  let EL : Subgroup (involutionCore G) := E.subgroupOf (involutionCore G)
  refine ⟨EL, ?_, ?_⟩
  · rw [show Nat.card EL = Nat.card E from
      natCard_subgroupOf_eq E (involutionCore G) hEcore]
    exact hEcard
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val (hEsq ⟨(x : G), x.property⟩)

/-- A strongly embedded subgroup of a finite group inherits every ambient
four-group up to conjugacy. -/
private theorem theorem4b_twoRank_stronglyEmbedded
    {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hM : IsStronglyEmbedded M) (hrank : TwoRankAtLeastTwo G) :
    TwoRankAtLeastTwo M := by
  classical
  obtain ⟨E, hEcard, hEsq⟩ := TwoRankAtLeastTwo.exists_subgroup hrank
  have hEp : IsPGroup 2 E := by
    refine IsPGroup.of_card (p := 2) (G := E) (n := 2) ?_
    norm_num [hEcard]
  obtain ⟨T, hET⟩ := IsPGroup.exists_le_sylow (G := G) (p := 2) hEp
  obtain ⟨S, hSM⟩ := hM.containsSylowTwo
  obtain ⟨g, hgTS⟩ := MulAction.exists_smul_eq G T S
  let A : Subgroup G := E.map (MulAut.conj g).toMonoidHom
  have hAM : A ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨e, heE, rfl⟩
    apply hSM
    rw [← hgTS]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hET heE)
  have hAcard : Nat.card A = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hAsq : ∀ x : A, x ^ 2 = 1 := by
    intro x
    rcases Subgroup.mem_map.mp x.property with ⟨e, heE, heq⟩
    apply Subtype.ext
    change (x : G) ^ 2 = 1
    rw [← heq]
    have heSqG : (e : G) ^ 2 = 1 :=
      congrArg (fun y : E => (y : G)) (hEsq ⟨e, heE⟩)
    simpa using congrArg (MulAut.conj g) heSqG
  let AM : Subgroup M := A.subgroupOf M
  refine ⟨AM, ?_, ?_⟩
  · rw [show Nat.card AM = Nat.card A from
      natCard_subgroupOf_eq A M hAM]
    exact hAcard.trans hEcard
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    change ((x : G) ^ 2 = 1)
    let xA : A := ⟨(x : G), x.property⟩
    simpa [xA] using congrArg Subtype.val (hAsq xA)

/-- The embedded Section 7 subgroup `N°`, generated by the involutions of
`N_X(Q)`. -/
@[expose] public def theorem4bSection7NCore
    {X : Type*} [Group X] (Q : Subgroup X) : Subgroup X :=
  let N : Subgroup X := Subgroup.normalizer (Q : Set X)
  (involutionCore N).map N.subtype

/-- Equation `(7E)`: the odd core of `N°` is contained in the selected
triple stabilizer `E`. -/
public theorem IsStronglyEmbedded.theorem4b_section7_sevenE
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    let N0 : Subgroup X := theorem4bSection7NCore q.chosen.Q
    let O : Subgroup X := (twoPrimeCore N0).map N0.subtype
    O ≤ theorem4bSection7E M d.data.z s.beta := by
  classical
  let a := q.chosen
  let N : Subgroup X := Subgroup.normalizer (a.Q : Set X)
  let L : Subgroup N := involutionCore N
  let N0 : Subgroup X := L.map N.subtype
  let M1 : Subgroup N0 := M.comap N0.subtype
  let O : Subgroup X := (twoPrimeCore N0).map N0.subtype
  let alpha : conjugateCosetSpace M := theorem4bSection7Base
  dsimp only [theorem4bSection7NCore]
  have htNotM : a.t ∉ M := by
    intro htM
    apply s.hbetaNe
    calc
      s.beta = a.t • alpha := a.htBase.symm
      _ = alpha := by
        apply MulAction.mem_stabilizer_iff.mp
        rw [show MulAction.stabilizer X alpha = M by
          simp [alpha, theorem4bSection7Base]]
        exact htM
  have hrankL : TwoRankAtLeastTwo L := by
    apply theorem4b_twoRank_involutionCore_of_twoRank
    by_contra hNrank
    apply (hM.theorem4b_lemma710 hX d hrank hT2 hinduction s q)
    intro u hu
    exact PFAppendixII.pPrimeCore_sup_centralizer_eq_top_of_not_twoRank
      hNrank hu
  let eLN0 : L ≃* N0 := by
    simpa [L, N0] using
      (Subgroup.equivMapOfInjective L N.subtype Subtype.val_injective)
  have hrankN0 : TwoRankAtLeastTwo N0 :=
    hrankL.map_of_injective eLN0.toMonoidHom eLN0.injective
  have htN0 : a.t ∈ N0 := by
    apply Subgroup.mem_map.mpr
    let tN : N := ⟨a.t, a.htNormQ⟩
    refine ⟨tN, ?_, rfl⟩
    change tN ∈ Subgroup.closure (involutionsSet N)
    exact Subgroup.subset_closure (IsInvolution.subtype a.ht a.htNormQ)
  have hzN0 : d.data.z ∈ N0 := by
    apply Subgroup.mem_map.mpr
    let zN : N := ⟨d.data.z, a.hzNormQ⟩
    refine ⟨zN, ?_, rfl⟩
    change zN ∈ Subgroup.closure (involutionsSet N)
    exact Subgroup.subset_closure
      (IsInvolution.subtype d.data.hz a.hzNormQ)
  have hM1strong : IsStronglyEmbedded M1 := by
    apply hM.comap_of_injective N0.subtype Subtype.val_injective
    · intro htop
      apply htNotM
      let t0 : N0 := ⟨a.t, htN0⟩
      have htTop : t0 ∈ (⊤ : Subgroup N0) := Subgroup.mem_top _
      rw [← htop] at htTop
      exact htTop
    · exact ⟨⟨d.data.z, hzN0⟩, d.data.hzM,
        IsInvolution.subtype d.data.hz hzN0⟩
  have hrankM1 : TwoRankAtLeastTwo M1 :=
    theorem4b_twoRank_stronglyEmbedded hM1strong hrankN0
  have hOM : O ≤ M := by
    exact oddCore_map_le_stronglyEmbedded_of_twoRank_intersection
      M N0 hM hrankM1
  have hnormalizerO_of_mem_N0 : ∀ x : X, x ∈ N0 →
      x ∈ Subgroup.normalizer (O : Set X) := by
    intro x hxN0
    let x0 : N0 := ⟨x, hxN0⟩
    have hxNormCore : x0 ∈
        Subgroup.normalizer ((twoPrimeCore N0) : Set N0) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr
        (inferInstance : (twoPrimeCore N0).Normal)]
      trivial
    have hxMap : x ∈
        (Subgroup.normalizer ((twoPrimeCore N0) : Set N0)).map N0.subtype :=
      Subgroup.mem_map.mpr ⟨x0, hxNormCore, rfl⟩
    exact (Subgroup.le_normalizer_map
      (H := twoPrimeCore N0) N0.subtype) hxMap
  have hzNormO : d.data.z ∈ Subgroup.normalizer (O : Set X) :=
    hnormalizerO_of_mem_N0 d.data.z hzN0
  have htNormO : a.t ∈ Subgroup.normalizer (O : Set X) :=
    hnormalizerO_of_mem_N0 a.t htN0
  have hOalpha : O ≤ MulAction.stabilizer X alpha := by
    rw [show MulAction.stabilizer X alpha = M by
      simp [alpha, theorem4bSection7Base]]
    exact hOM
  have hObeta : O ≤ MulAction.stabilizer X s.beta := by
    have h := theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
      htNormO hOalpha
    rwa [a.htBase] at h
  have hOzbeta : O ≤ MulAction.stabilizer X (d.data.z • s.beta) :=
    theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
      hzNormO hObeta
  exact le_inf (le_inf hOM hObeta) hOzbeta

/-- The Section 7 subgroup `M₁ = M ∩ N°`, represented internally as a
subgroup of `N°`. -/
@[expose] public def theorem4bSection7M1
    {X : Type*} [Group X] (M Q : Subgroup X) :
    Subgroup (theorem4bSection7NCore Q) :=
  M.comap (theorem4bSection7NCore Q).subtype

/-- The source subgroup `M₁ = M ∩ N°`, mapped back into the ambient group. -/
@[expose] public def theorem4bSection7M1InX
    {X : Type*} [Group X] (M Q : Subgroup X) : Subgroup X :=
  (theorem4bSection7M1 M Q).map
    (theorem4bSection7NCore Q).subtype

/-- The copy of `O₂'(N°)` inside `M₁`.  Equation `(7E)` later identifies
this pullback with the full odd core, rather than merely its intersection with
`M₁`. -/
@[expose] public def theorem4bSection7O1
    {X : Type*} [Group X] (M Q : Subgroup X) :
    Subgroup (theorem4bSection7M1 M Q) :=
  (twoPrimeCore (theorem4bSection7NCore Q)).comap
    (theorem4bSection7M1 M Q).subtype

public instance theorem4bSection7O1_normal
    {X : Type*} [Group X] (M Q : Subgroup X) :
    (theorem4bSection7O1 M Q).Normal := by
  exact Subgroup.Normal.comap
    (inferInstance : (twoPrimeCore (theorem4bSection7NCore Q)).Normal)
    (theorem4bSection7M1 M Q).subtype

/-- The image of the involution core of `M₁` in
`M₁ / O₂'(N°)` is a `2`-group.  This is the internal-copy form of the
`[II4; 3.2(b)]` conclusion used in `(7F)`. -/
private theorem theorem4b_section7_M1_core_quotient_isPGroup
    {X : Type*} [Group X] [Finite X]
    (M Q : Subgroup X)
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (hN0proper : theorem4bSection7NCore Q ≠ ⊤)
    (hM1 : IsStronglyEmbedded (theorem4bSection7M1 M Q))
    (hrank : TwoRankAtLeastTwo (theorem4bSection7M1 M Q)) :
    IsPGroup 2
      ((involutionCore (theorem4bSection7M1 M Q)).map
        (QuotientGroup.mk' (theorem4bSection7O1 M Q))) := by
  let A : Subgroup (theorem4bSection7NCore Q) := theorem4bSection7M1 M Q
  let N0 : Subgroup X := theorem4bSection7NCore Q
  let Amap : Subgroup X := A.map N0.subtype
  have hcomap : Amap.comap N0.subtype = A := by
    dsimp [Amap]
    exact Subgroup.comap_map_eq_self_of_injective
      Subtype.val_injective A
  have hML : IsStronglyEmbedded (Amap.comap N0.subtype) := by
    rw [hcomap]
    exact hM1
  have hConclusion : TheoremSEConclusion (Amap.comap N0.subtype) :=
    hinduction N0 hN0proper (Amap.comap N0.subtype) hML
  have hrankAmap : TwoRankAtLeastTwo (Amap.comap N0.subtype) := by
    rw [hcomap]
    exact hrank
  have hAmapN0 : Amap ≤ N0 := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, _ha, rfl⟩
    exact a.property
  have hcoreM : (involutionCore Amap).map Amap.subtype ≤ N0 :=
    (Subgroup.map_subtype_le (involutionCore Amap)).trans hAmapN0
  have hN0core : N0 = (involutionCore N0).map N0.subtype := by
    have htop : involutionCore N0 = ⊤ := by
      change involutionCore
          ((involutionCore (Subgroup.normalizer (Q : Set X))).map
            (Subgroup.normalizer (Q : Set X)).subtype) = ⊤
      exact involutionCore_map_subtype_eq_top
        (Subgroup.normalizer (Q : Set X))
    rw [htop]
    ext x
    constructor
    · intro hx
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    · rintro ⟨y, _hy, rfl⟩
      exact y.property
  let f : involutionCore Amap →* N0 ⧸ twoPrimeCore N0 :=
    theorem4bProposition63CoreQuotientMap hcoreM
  have hRangeP : IsPGroup 2 f.range := by
    exact theorem4bProposition63_II4b_image_isPGroup
      hConclusion hN0core hrankAmap hcoreM
  let eA : A ≃* Amap := by
    simpa [Amap] using
      (Subgroup.equivMapOfInjective A N0.subtype Subtype.val_injective)
  have heA_coe (a : A) :
      ((eA a : Amap) : X) = (((a : A) : N0) : X) := by
    change ((Subgroup.equivMapOfInjective A N0.subtype
      Subtype.val_injective a : A.map N0.subtype) : X) =
      ((a : A) : N0)
    exact Subgroup.coe_equivMapOfInjective_apply A N0.subtype
      Subtype.val_injective a
  have hcoreMap : (involutionCore A).map eA.toMonoidHom =
      involutionCore Amap :=
    involutionCore_map_mulEquiv eA
  let eC : involutionCore A →* involutionCore Amap :=
    { toFun := fun c => ⟨eA c, by
        rw [← hcoreMap]
        exact ⟨c, c.property, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        exact eA.map_one
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact eA.map_mul x y }
  have heC_coe (c : involutionCore A) :
      ((eC c : involutionCore Amap) : Amap) = eA (c : A) := by
    rfl
  have heC_surj : Function.Surjective eC := by
    intro y
    have hy : (y : Amap) ∈
        (involutionCore A).map eA.toMonoidHom := by
      rw [hcoreMap]
      exact y.property
    rcases hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let fA : involutionCore A →* N0 ⧸ twoPrimeCore N0 :=
    f.comp eC
  have hfrange : fA.range = f.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨eC x, rfl⟩
    · rintro ⟨x, rfl⟩
      rcases heC_surj x with ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  have hRangePA : IsPGroup 2 fA.range := by
    rw [hfrange]
    exact hRangeP
  let qA : A →* A ⧸ theorem4bSection7O1 M Q :=
    QuotientGroup.mk' (theorem4bSection7O1 M Q)
  let phi : (A ⧸ theorem4bSection7O1 M Q) →*
      N0 ⧸ twoPrimeCore N0 :=
    QuotientGroup.map (theorem4bSection7O1 M Q) (twoPrimeCore N0)
      A.subtype (by
        intro x hx
        exact hx)
  have hphi_inj : Function.Injective phi := by
    intro a b hab
    rcases QuotientGroup.mk'_surjective
      (theorem4bSection7O1 M Q) a with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective
      (theorem4bSection7O1 M Q) b with ⟨y, rfl⟩
    apply QuotientGroup.eq.mpr
    have hxy : ((x : A) : N0) ⁻¹ * (y : A) ∈ twoPrimeCore N0 := by
      apply QuotientGroup.eq.mp
      change QuotientGroup.mk' (twoPrimeCore N0) ((x : A) : N0) =
        QuotientGroup.mk' (twoPrimeCore N0) ((y : A) : N0)
      change QuotientGroup.map (theorem4bSection7O1 M Q) (twoPrimeCore N0)
          A.subtype (by intro z hz; exact hz)
          (QuotientGroup.mk' (theorem4bSection7O1 M Q) x) =
        QuotientGroup.map (theorem4bSection7O1 M Q) (twoPrimeCore N0)
          A.subtype (by intro z hz; exact hz)
          (QuotientGroup.mk' (theorem4bSection7O1 M Q) y) at hab
      have hab' := hab
      change QuotientGroup.mk' (twoPrimeCore N0) (A.subtype x) =
        QuotientGroup.mk' (twoPrimeCore N0) (A.subtype y) at hab'
      change QuotientGroup.mk' (twoPrimeCore N0) (A.subtype x) =
        QuotientGroup.mk' (twoPrimeCore N0) (A.subtype y)
      exact hab'
    exact hxy
  let Cbar : Subgroup (A ⧸ theorem4bSection7O1 M Q) :=
    (involutionCore A).map qA
  have hCbarP : IsPGroup 2 Cbar := by
    let psi : Cbar →* fA.range :=
      { toFun := fun x => ⟨phi x, by
          rcases Subgroup.mem_map.mp x.property with ⟨c, hc, hcx⟩
          refine ⟨⟨c, hc⟩, ?_⟩
          rw [← hcx]
          let cN0 : N0 :=
            ⟨(((eC ⟨c, hc⟩ : involutionCore Amap) : Amap) : X),
              hcoreM (Subgroup.mem_map_of_mem Amap.subtype
                (eC ⟨c, hc⟩).property)⟩
          have hcN0 : cN0 = ((c : A) : N0) := by
            apply Subtype.ext
            exact (congrArg (fun y : Amap => ((y : X)))
              (heC_coe ⟨c, hc⟩)).trans (heA_coe c)
          have hcN0' := congrArg (QuotientGroup.mk' (twoPrimeCore N0)) hcN0
          dsimp [fA, f, eC, phi, qA]
          rw [theorem4bProposition63CoreQuotientMap_apply]
          change QuotientGroup.mk' (twoPrimeCore N0) (cN0 : N0) =
            QuotientGroup.mk' (twoPrimeCore N0) (A.subtype c)
          exact hcN0'⟩
        map_one' := by ext; rfl
        map_mul' := by
          intro x y
          apply Subtype.ext
          exact phi.map_mul x y }
    apply hRangePA.of_injective psi
    intro x y hxy
    apply Subtype.ext
    apply hphi_inj
    exact congrArg Subtype.val hxy
  simpa [Cbar, qA, A] using hCbarP

/-- The right side of `(7F)`, namely `Omega₁(O₂(M₁/O₂'(N°)))`. -/
@[expose] public def theorem4bSection7M2Quotient
    {X : Type*} [Group X] (M Q : Subgroup X) :
    Subgroup ((theorem4bSection7M1 M Q) ⧸
      (theorem4bSection7O1 M Q)) :=
  let P := pCore 2 ((theorem4bSection7M1 M Q) ⧸
    (theorem4bSection7O1 M Q))
  (omega₁ (G := P) (p := 2)).map P.subtype

public instance theorem4bSection7M2Quotient_characteristic
    {X : Type*} [Group X] (M Q : Subgroup X) :
    (theorem4bSection7M2Quotient M Q).Characteristic := by
  let G := (theorem4bSection7M1 M Q) ⧸ (theorem4bSection7O1 M Q)
  let P := pCore 2 G
  haveI : P.Characteristic := pCore_characteristic
  haveI : (omega₁ (G := P) (p := 2)).Characteristic :=
    omega₁_characteristic P
  have hchar : ((omega₁ (G := P) (p := 2)).map P.subtype).Characteristic :=
    characteristic_map_subtype_of_characteristic P
      (omega₁ (G := P) (p := 2))
  simpa [theorem4bSection7M2Quotient, G, P] using
    hchar

public instance theorem4bSection7M2Quotient_normal
    {X : Type*} [Group X] (M Q : Subgroup X) :
    (theorem4bSection7M2Quotient M Q).Normal := by
  infer_instance

/-- Pulling back a characteristic quotient subgroup commutes with an
automorphism that preserves the quotient kernel. -/
private theorem theorem4b_quotient_characteristic_comap_map_mulEquiv
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (U : Subgroup (G ⧸ N)) [U.Characteristic]
    (e : G ≃* G) (hN : N.map e.toMonoidHom = N) :
    (U.comap (QuotientGroup.mk' N)).map e.toMonoidHom =
      U.comap (QuotientGroup.mk' N) := by
  letI : (N.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map (inferInstance : N.Normal) e.toMonoidHom e.surjective
  let eQ : (G ⧸ N) ≃* (G ⧸ N) :=
    (quotientMulEquivOfMulEquiv e N).trans
      (QuotientGroup.quotientMulEquivOfEq hN)
  have hUmap : U.map eQ.toMonoidHom = U :=
    Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : U.Characteristic) eQ
  have heQ_mk (x : G) :
      eQ ((QuotientGroup.mk' N) x) = (QuotientGroup.mk' N) (e x) := by
    change (QuotientGroup.quotientMulEquivOfEq hN)
        (quotientMulEquivOfMulEquiv e N (QuotientGroup.mk x)) =
      QuotientGroup.mk (e x)
    rw [quotientMulEquivOfMulEquiv_mk,
      QuotientGroup.quotientMulEquivOfEq_mk]
  have heQ_symm_mk (x : G) :
      eQ.symm ((QuotientGroup.mk' N) x) =
        (QuotientGroup.mk' N) (e.symm x) := by
    apply eQ.injective
    rw [eQ.apply_symm_apply, heQ_mk]
    simp
  apply le_antisymm
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyU : (QuotientGroup.mk' N) y ∈ U := hy
    have heU : eQ ((QuotientGroup.mk' N) y) ∈ U := by
      rw [← hUmap]
      exact Subgroup.mem_map_of_mem eQ.toMonoidHom hyU
    rw [heQ_mk] at heU
    exact heU
  · intro x hx
    have hxU : (QuotientGroup.mk' N) x ∈ U := hx
    have hesU : eQ.symm ((QuotientGroup.mk' N) x) ∈ U := by
      have hUmapSymm : U.map eQ.symm.toMonoidHom = U :=
        Subgroup.characteristic_iff_map_eq.mp
          (inferInstance : U.Characteristic) eQ.symm
      rw [← hUmapSymm]
      exact Subgroup.mem_map_of_mem eQ.symm.toMonoidHom hxU
    apply Subgroup.mem_map.mpr
    refine ⟨e.symm x, ?_, by simp⟩
    rw [heQ_symm_mk] at hesU
    exact hesU

/-- The source subgroup `M₂`, defined as the full preimage in `M₁` of
`Omega₁(O₂(M₁/O₂'(N°)))`. -/
@[expose] public def theorem4bSection7M2
    {X : Type*} [Group X] (M Q : Subgroup X) :
    Subgroup (theorem4bSection7M1 M Q) :=
  (theorem4bSection7M2Quotient M Q).comap
    (QuotientGroup.mk' (theorem4bSection7O1 M Q))

public instance theorem4bSection7M2_normal
    {X : Type*} [Group X] (M Q : Subgroup X) :
    (theorem4bSection7M2 M Q).Normal := by
  exact Subgroup.Normal.comap (theorem4bSection7M2Quotient_normal M Q)
    (QuotientGroup.mk' (theorem4bSection7O1 M Q))

/-- Equation `(7F)` in quotient form. -/
public theorem theorem4b_section7_sevenF
    {X : Type*} [Group X] (M Q : Subgroup X) :
    (theorem4bSection7M2 M Q).map
        (QuotientGroup.mk' (theorem4bSection7O1 M Q)) =
      theorem4bSection7M2Quotient M Q := by
  exact Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective (theorem4bSection7O1 M Q)) _

/-- Equation `(7G)`: `M₂` is normal in `M₁`. -/
public theorem theorem4b_section7_sevenG
    {X : Type*} [Group X] (M Q : Subgroup X) :
    (theorem4bSection7M2 M Q).Normal :=
  theorem4bSection7M2_normal M Q

/-- The source subgroup `M₂`, mapped back into `X`. -/
@[expose] public def theorem4bSection7M2InX
    {X : Type*} [Group X] (M Q : Subgroup X) : Subgroup X :=
  ((theorem4bSection7M2 M Q).map
      (theorem4bSection7M1 M Q).subtype).map
    (theorem4bSection7NCore Q).subtype

public theorem theorem4b_section7_M2_le_M1InX
    {X : Type*} [Group X] (M Q : Subgroup X) :
    theorem4bSection7M2InX M Q ≤ theorem4bSection7M1InX M Q := by
  simpa [theorem4bSection7M2InX, theorem4bSection7M1InX] using
    (Subgroup.map_mono (f := (theorem4bSection7NCore Q).subtype)
      (Subgroup.map_subtype_le (theorem4bSection7M2 M Q)))

/-- The source overgroup `M̂₂ = M₂ R`.  Once normalization is established,
the supremum is the corresponding subgroup product. -/
@[expose] public def theorem4bSection7M2Hat
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {d : Theorem4bSixD M} {s : Theorem4bSection7SecondStage d}
    (q : Theorem4bSection7MaximalQData d s) : Subgroup X :=
  theorem4bSection7M2InX M q.chosen.Q ⊔ theorem4bSection7R q

/-! The quotient of a normalized product by its first factor is a p-group
    whenever the second factor is a p-group.  This is the local quotient
    input for the p-prime-core comparison below. -/
private theorem theorem4b_section7_quotient_sup_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    (B R : Subgroup G) [(B.subgroupOf (B ⊔ R)).Normal]
    (hRp : IsPGroup p R) :
    IsPGroup p (↥(B ⊔ R) ⧸ B.subgroupOf (B ⊔ R)) := by
  let H : Subgroup G := B ⊔ R
  let Bsub : Subgroup H := B.subgroupOf H
  let Rsub : Subgroup H := R.subgroupOf H
  have hBH : B ≤ H := le_sup_left
  have hRH : R ≤ H := le_sup_right
  letI : Bsub.Normal := by
    dsimp [Bsub, H]
    infer_instance
  have hsup : Bsub ⊔ Rsub = ⊤ := by
    apply top_unique
    intro h _hh
    have hxH : (h : G) ∈ H := h.property
    have hmapSup : (Bsub ⊔ Rsub).map H.subtype = H := by
      rw [Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le hBH,
        Subgroup.map_subgroupOf_eq_of_le hRH]
    have hxMap : (h : G) ∈ (Bsub ⊔ Rsub).map H.subtype := by
      rw [hmapSup]
      exact hxH
    rcases Subgroup.mem_map.mp hxMap with ⟨k, hk, hkEq⟩
    have : k = h := Subtype.ext hkEq
    rwa [this] at hk
  let qH : H →* H ⧸ Bsub := QuotientGroup.mk' Bsub
  let rToH : R →* H := Subgroup.inclusion hRH
  let f : R →* H ⧸ Bsub := qH.comp rToH
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective Bsub y
    have hh : h ∈ Bsub ⊔ Rsub := by
      rw [hsup]
      trivial
    rcases Subgroup.mem_sup_of_normal_left.mp hh with
      ⟨b, hb, r, hr, hbr⟩
    let rr : R := ⟨((r : H) : G), hr⟩
    refine ⟨rr, ?_⟩
    change qH r = qH h
    have hqb : qH b = 1 := (QuotientGroup.eq_one_iff b).2 hb
    rw [← hbr, map_mul, hqb, one_mul]
  exact IsPGroup.of_surjective hRp f hf

private theorem theorem4b_section7_pPrimeCore_sup_eq
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (B R : Subgroup G)
    (hRnorm : R ≤ Subgroup.normalizer (B : Set G))
    (hRp : IsPGroup p R) :
    (pPrimeCore p (↥(B ⊔ R))).map (B ⊔ R).subtype =
      (pPrimeCore p B).map B.subtype := by
  classical
  let H : Subgroup G := B ⊔ R
  have hBH : B ≤ H := by simpa [H] using (le_sup_left : B ≤ B ⊔ R)
  have hHnormB : H ≤ Subgroup.normalizer (B : Set G) := by
    simpa [H] using (sup_le Subgroup.le_normalizer hRnorm)
  have hBnorm : (B.subgroupOf H).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hBH).2
    exact hHnormB
  letI : (B.subgroupOf H).Normal := hBnorm
  have hquotP : IsPGroup p (↥H ⧸ B.subgroupOf H) := by
    simpa [H] using theorem4b_section7_quotient_sup_isPGroup B R hRp
  let qH : H →* H ⧸ B.subgroupOf H := QuotientGroup.mk' (B.subgroupOf H)
  let OH : Subgroup H := pPrimeCore p H
  have hmapP : IsPGroup p (OH.map qH) := hquotP.to_subgroup (OH.map qH)
  have hmapCop : Nat.Coprime p (Nat.card (OH.map qH)) := by
    exact Nat.Coprime.of_dvd_right
      (Subgroup.card_map_dvd (H := OH) qH)
      (pPrimeCore_coprime_card (p := p) (G := H))
  have hmapCard : Nat.card (OH.map qH) = 1 := by
    rcases hmapP.card_eq_or_dvd with hcard | hpDvd
    · exact hcard
    · exact False.elim
        (((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hmapCop) hpDvd)
  have hmapBot : OH.map qH = ⊥ :=
    (Subgroup.card_eq_one (H := OH.map qH)).1 hmapCard
  have hOHleB : OH ≤ B.subgroupOf H := by
    have hker : OH ≤ qH.ker :=
      (Subgroup.map_eq_bot_iff (f := qH) (H := OH)).1 hmapBot
    simpa [qH, QuotientGroup.ker_mk'] using hker
  let OHX : Subgroup G := OH.map H.subtype
  let OBX : Subgroup G := (pPrimeCore p B).map B.subtype
  have hOHXleB : OHX ≤ B := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    change (y : G) ∈ B
    exact hOHleB hy
  haveI : OH.Characteristic := pPrimeCore_characteristic
  have hHnormOHX : H ≤ Subgroup.normalizer (OHX : Set G) := by
    exact Subgroup.le_normalizer.trans
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := H) (K := OH))
  haveI : (OHX.subgroupOf B).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hOHXleB).2
    exact hBH.trans hHnormOHX
  have hOHXcop : Nat.Coprime p (Nat.card OHX) := by
    rw [show Nat.card OHX = Nat.card OH by
      simpa [OHX] using
        (Subgroup.card_map_of_injective (K := OH) (f := H.subtype)
          H.subtype_injective)]
    exact pPrimeCore_coprime_card (p := p) (G := H)
  have hfirst : OHX ≤ OBX := by
    exact subgroupOf_le_pPrimeCore_map (p := p) hOHXleB hOHXcop
  have hOBXleH : OBX ≤ H := by
    intro x hx
    exact hBH (by
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.property)
  haveI : (pPrimeCore p B).Characteristic := pPrimeCore_characteristic
  have hHnormOBX : H ≤ Subgroup.normalizer (OBX : Set G) := by
    exact hHnormB.trans
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := B) (K := pPrimeCore p B))
  haveI : (OBX.subgroupOf H).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hOBXleH).2
    exact hHnormOBX
  have hOBXcop : Nat.Coprime p (Nat.card OBX) := by
    rw [show Nat.card OBX = Nat.card (pPrimeCore p B) by
      simpa [OBX] using
        (Subgroup.card_map_of_injective (K := pPrimeCore p B)
          (f := B.subtype) B.subtype_injective)]
    exact pPrimeCore_coprime_card (p := p) (G := B)
  have hsecond : OBX ≤ OHX := by
    exact subgroupOf_le_pPrimeCore_map (p := p) hOBXleH hOBXcop
  exact le_antisymm (by simpa [OHX, OBX, H] using hfirst)
    (by simpa [OHX, OBX, H] using hsecond)

/-! Intersecting the ambient p-prime core of an overgroup with a subgroup
    gives a normal p-prime subgroup of the latter. -/
private theorem theorem4b_section7_inf_pPrimeCore_le_pPrimeCore_map
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (B A : Subgroup G) (hBA : B ≤ A) :
    (pPrimeCore p A).map A.subtype ⊓ B ≤
      (pPrimeCore p B).map B.subtype := by
  let OA : Subgroup G := (pPrimeCore p A).map A.subtype
  let K : Subgroup G := OA ⊓ B
  have hKleB : K ≤ B := inf_le_right
  haveI : (pPrimeCore p A).Characteristic := pPrimeCore_characteristic
  have hAnormOA : A ≤ Subgroup.normalizer (OA : Set G) := by
    exact Subgroup.le_normalizer.trans
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := A) (K := pPrimeCore p A))
  have hBnormK : B ≤ Subgroup.normalizer (K : Set G) := by
    intro b hb
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hAnormOA (hBA hb), Subgroup.le_normalizer hb⟩
  haveI : (K.subgroupOf B).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hKleB).2
    exact hBnormK
  have hOAcop : Nat.Coprime p (Nat.card OA) := by
    rw [show Nat.card OA = Nat.card (pPrimeCore p A) by
      simpa [OA] using
        (Subgroup.card_map_of_injective (K := pPrimeCore p A)
          (f := A.subtype) A.subtype_injective)]
    exact pPrimeCore_coprime_card (p := p) (G := A)
  have hKcop : Nat.Coprime p (Nat.card K) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hOAcop
  simpa [K, OA] using
    subgroupOf_le_pPrimeCore_map (p := p) hKleB hKcop

/-! If the ambient image of `O_{p′}(A)` has odd order, then it already lies
    in `O_{2′}(A)`, so the two-stage source subgroup `theta(A)` is exactly
    `O_{p′}(A)`. -/
private theorem theorem4b_section7_theta_eq_pPrimeCore_of_odd
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (A : Subgroup G)
    (hodd : Odd (Nat.card ((pPrimeCore p A).map A.subtype))) :
    corollary64Theta p A = (pPrimeCore p A).map A.subtype := by
  classical
  let PX : Subgroup G := (pPrimeCore p A).map A.subtype
  let O : Subgroup G := corollary64OddCore A
  let T : Subgroup G := corollary64Theta p A
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPXleA : PX ≤ A := by
    simpa [PX] using (Subgroup.map_subtype_le (pPrimeCore p A))
  haveI : (pPrimeCore p A).Characteristic := pPrimeCore_characteristic
  have hAnormPX : A ≤ Subgroup.normalizer (PX : Set G) := by
    exact Subgroup.le_normalizer.trans
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := A) (K := pPrimeCore p A))
  haveI : (PX.subgroupOf A).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hPXleA).2
    exact hAnormPX
  have hPXcop : Nat.Coprime p (Nat.card PX) := by
    rw [show Nat.card PX = Nat.card (pPrimeCore p A) by
      simpa [PX] using
        (Subgroup.card_map_of_injective (K := pPrimeCore p A)
          (f := A.subtype) A.subtype_injective)]
    exact pPrimeCore_coprime_card (p := p) (G := A)
  have hPXleO : PX ≤ O := by
    have hPXtwoCop : Nat.Coprime 2 (Nat.card PX) :=
      hodd.coprime_two_left
    simpa [PX, O, corollary64OddCore, twoPrimeCore] using
      (subgroupOf_le_pPrimeCore_map (p := 2) hPXleA hPXtwoCop)
  have hOleA : O ≤ A := by
    simpa [O, corollary64OddCore] using
      (Subgroup.map_subtype_le (twoPrimeCore A))
  have hOnormPX : O ≤ Subgroup.normalizer (PX : Set G) :=
    hOleA.trans hAnormPX
  haveI : (PX.subgroupOf O).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hPXleO).2
    exact hOnormPX
  have hPXleT : PX ≤ T := by
    simpa [T, corollary64Theta] using
      (subgroupOf_le_pPrimeCore_map (p := p) hPXleO hPXcop)
  haveI : (twoPrimeCore A).Characteristic := by
    simpa [twoPrimeCore] using
      (pPrimeCore_characteristic (p := 2) (G := A))
  have hAnormO : A ≤ Subgroup.normalizer (O : Set G) := by
    simpa [O, corollary64OddCore, twoPrimeCore] using
      (Subgroup.le_normalizer.trans
        (section8_normalizer_map_subtype_le_of_characteristic
          (H := A) (K := twoPrimeCore A)))
  haveI : (pPrimeCore p O).Characteristic := pPrimeCore_characteristic
  have hNormOnormT : Subgroup.normalizer (O : Set G) ≤
      Subgroup.normalizer (T : Set G) := by
    simpa [T, corollary64Theta] using
      (External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
        O (pPrimeCore p O))
  have hAnormT : A ≤ Subgroup.normalizer (T : Set G) :=
    hAnormO.trans hNormOnormT
  have hTleO : T ≤ O := by
    simpa [T, O, corollary64Theta] using
      (Subgroup.map_subtype_le (pPrimeCore p O))
  have hTleA : T ≤ A := hTleO.trans hOleA
  haveI : (T.subgroupOf A).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hTleA).2
    exact hAnormT
  have hTcop : Nat.Coprime p (Nat.card T) := by
    rw [show Nat.card T = Nat.card (pPrimeCore p O) by
      simpa [T, corollary64Theta] using
        (Subgroup.card_map_of_injective (K := pPrimeCore p O)
          (f := O.subtype) O.subtype_injective)]
    exact pPrimeCore_coprime_card (p := p) (G := O)
  have hTlePX : T ≤ PX := by
    exact subgroupOf_le_pPrimeCore_map (p := p) hTleA hTcop
  exact le_antisymm hTlePX hPXleT

private theorem theorem4b_section7_pPrimeCore_odd_of_mulEquiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {p : ℕ} [Fact p.Prime] (e : G ≃* H)
    (hodd : Odd (Nat.card (pPrimeCore p G))) :
    Odd (Nat.card (pPrimeCore p H)) := by
  have hmap : (pPrimeCore p G).map e.toMonoidHom = pPrimeCore p H :=
    pPrimeCore_map_iso (p := p) e
  have hcard : Nat.card ((pPrimeCore p G).map e.toMonoidHom) =
      Nat.card (pPrimeCore p G) := by
    exact Subgroup.card_map_of_injective e.injective
  rw [← hmap, hcard]
  exact hodd

/-- The selected subgroup `R ≤ N_X(Q)` normalizes the involution-generated
subgroup `N°` of `N_X(Q)`. -/
public theorem theorem4b_section7_R_le_normalizer_NCore
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {d : Theorem4bSixD M} {s : Theorem4bSection7SecondStage d}
    (q : Theorem4bSection7MaximalQData d s) :
    q.R ≤ Subgroup.normalizer
      (theorem4bSection7NCore q.chosen.Q : Set X) := by
  let N : Subgroup X := Subgroup.normalizer (q.chosen.Q : Set X)
  have hRN : q.R ≤ N :=
    (theorem4bIsSylowSubgroupOf_le_final q.hRsylow).trans inf_le_right
  have hNnormN0 : N ≤ Subgroup.normalizer
      ((involutionCore N).map N.subtype : Set X) := by
    exact Subgroup.le_normalizer.trans
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := N) (K := involutionCore N))
  exact hRN.trans (by
    simpa [N, theorem4bSection7NCore] using hNnormN0)

/-- Since `R ≤ D ≤ M` and `R` normalizes `N°`, it normalizes the ambient
copy of `M₁ = M ∩ N°`. -/
public theorem theorem4b_section7_R_le_normalizer_M1
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {d : Theorem4bSixD M} {s : Theorem4bSection7SecondStage d}
    (q : Theorem4bSection7MaximalQData d s) :
    q.R ≤ Subgroup.normalizer
      ((theorem4bSection7M1 M q.chosen.Q).map
        (theorem4bSection7NCore q.chosen.Q).subtype : Set X) := by
  let N0 : Subgroup X := theorem4bSection7NCore q.chosen.Q
  let A : Subgroup N0 := theorem4bSection7M1 M q.chosen.Q
  let AX : Subgroup X := theorem4bSection7M1InX M q.chosen.Q
  have hRM : q.R ≤ M :=
    (theorem4bIsSylowSubgroupOf_le_final q.hRsylow).trans
      (inf_le_left.trans inf_le_left)
  have hRN0 : q.R ≤ Subgroup.normalizer (N0 : Set X) := by
    simpa [N0] using theorem4b_section7_R_le_normalizer_NCore q
  have hRinf : q.R ≤ Subgroup.normalizer (M ⊓ N0 : Set X) := by
    intro r hr
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hRM.trans Subgroup.le_normalizer hr, hRN0 hr⟩
  have hAXeq : AX = M ⊓ N0 := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
      exact ⟨ha, a.property⟩
    · rintro ⟨hxM, hxN0⟩
      let xN0 : N0 := ⟨x, hxN0⟩
      exact Subgroup.mem_map.mpr ⟨xN0, hxM, rfl⟩
  change q.R ≤ Subgroup.normalizer (AX : Set X)
  rw [hAXeq]
  exact hRinf

/-- The quotient definition `(7F)` is invariant under conjugation by `R`, so
`R` normalizes the ambient copy of `M₂`. -/
public theorem theorem4b_section7_R_le_normalizer_M2
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {d : Theorem4bSixD M} {s : Theorem4bSection7SecondStage d}
    (q : Theorem4bSection7MaximalQData d s) :
    q.R ≤ Subgroup.normalizer
      (theorem4bSection7M2InX M q.chosen.Q : Set X) := by
  classical
  let Q : Subgroup X := q.chosen.Q
  let N0 : Subgroup X := theorem4bSection7NCore Q
  let A : Subgroup N0 := theorem4bSection7M1 M Q
  let AX : Subgroup X := A.map N0.subtype
  let O1 : Subgroup A := theorem4bSection7O1 M Q
  let U : Subgroup (A ⧸ O1) := theorem4bSection7M2Quotient M Q
  let A2 : Subgroup A := theorem4bSection7M2 M Q
  have hRN0 : q.R ≤ Subgroup.normalizer (N0 : Set X) := by
    simpa [Q, N0] using theorem4b_section7_R_le_normalizer_NCore q
  have hRAX : q.R ≤ Subgroup.normalizer (AX : Set X) := by
    simpa [Q, N0, A, AX] using theorem4b_section7_R_le_normalizer_M1 q
  intro r hr
  let rN0 : Subgroup.normalizer (N0 : Set X) := ⟨r, hRN0 hr⟩
  let eN0 : N0 ≃* N0 := N0.normalizerMonoidHom rN0
  let iA : A ≃* AX := by
    simpa [AX] using
      (Subgroup.equivMapOfInjective A N0.subtype N0.subtype_injective)
  let rAX : Subgroup.normalizer (AX : Set X) := ⟨r, hRAX hr⟩
  let cAX : AX ≃* AX := AX.normalizerMonoidHom rAX
  let eA : A ≃* A := iA.trans (cAX.trans iA.symm)
  have heN0_apply (x : N0) :
      ((eN0 x : N0) : X) = r * (x : X) * r⁻¹ := by
    exact Subgroup.normalizerMonoidHom_apply_apply_coe N0 rN0 x
  have heA_apply (x : A) :
      (((eA x : A) : N0) : X) =
        r * (((x : A) : N0) : X) * r⁻¹ := by
    have hmap : iA (eA x) = cAX (iA x) := by
      simp [eA]
    calc
      (((eA x : A) : N0) : X) = (iA (eA x) : X) := by rfl
      _ = (cAX (iA x) : X) := congrArg Subtype.val hmap
      _ = r * (iA x : X) * r⁻¹ := by
        exact Subgroup.normalizerMonoidHom_apply_apply_coe AX rAX (iA x)
      _ = r * (((x : A) : N0) : X) * r⁻¹ := by rfl
  haveI : (twoPrimeCore N0).Characteristic := by
    simpa [twoPrimeCore] using
      (pPrimeCore_characteristic (p := 2) (G := N0))
  have hcoreMap :
      (twoPrimeCore N0).map eN0.toMonoidHom = twoPrimeCore N0 :=
    Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (twoPrimeCore N0).Characteristic) eN0
  have hO1le : O1.map eA.toMonoidHom ≤ O1 := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyO1, rfl⟩
    have hyCore : ((y : A) : N0) ∈ twoPrimeCore N0 := hyO1
    have heCore : eN0 ((y : A) : N0) ∈ twoPrimeCore N0 := by
      rw [← hcoreMap]
      exact Subgroup.mem_map_of_mem eN0.toMonoidHom hyCore
    have heq : ((eA y : A) : N0) = eN0 ((y : A) : N0) := by
      apply Subtype.ext
      rw [heN0_apply, heA_apply]
    change ((eA y : A) : N0) ∈ twoPrimeCore N0
    rw [heq]
    exact heCore
  have hO1map : O1.map eA.toMonoidHom = O1 := by
    apply Subgroup.eq_of_le_of_card_ge hO1le
    rw [Subgroup.card_map_of_injective eA.injective]
  letI : U.Characteristic := by
    dsimp [U]
    infer_instance
  have hA2map : A2.map eA.toMonoidHom = A2 := by
    simpa [A2, A, O1, U, theorem4bSection7M2] using
      theorem4b_quotient_characteristic_comap_map_mulEquiv O1 U eA hO1map
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  change x ∈ (A2.map A.subtype).map N0.subtype at hx
  rcases Subgroup.mem_map.mp hx with ⟨xN0, hxN0, rfl⟩
  rcases Subgroup.mem_map.mp hxN0 with ⟨xA, hxA2, rfl⟩
  have hexA2 : eA xA ∈ A2 := by
    rw [← hA2map]
    exact Subgroup.mem_map_of_mem eA.toMonoidHom hxA2
  change r * N0.subtype (A.subtype xA) * r⁻¹ ∈
    (A2.map A.subtype).map N0.subtype
  have hconjEq :
      r * N0.subtype (A.subtype xA) * r⁻¹ =
        N0.subtype (A.subtype (eA xA)) :=
    (heA_apply xA).symm
  rw [hconjEq]
  apply Subgroup.mem_map.mpr
  refine ⟨(eA xA : A), ?_, rfl⟩
  exact Subgroup.mem_map_of_mem A.subtype hexA2

/-- A subgroup normalized by the right commutator factor contains the
resulting subgroup commutator. -/
private theorem theorem4b_commutator_le_left_of_le_normalizer
    {G : Type*} [Group G] {K P : Subgroup G}
    (hPnormK : P ≤ Subgroup.normalizer (K : Set G)) :
    ⁅K, P⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro k hk p hp
  have hpNorm : p ∈ Subgroup.normalizer (K : Set G) := hPnormK hp
  have hpkInv : p * k⁻¹ * p⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hpNorm k⁻¹).1 (K.inv_mem hk)
  simpa [commutatorElement_def, mul_assoc] using K.mul_mem hk hpkInv

/-- Quotient glue for the source assertion `z ∈ M₂`: an involution in `M₁`
whose involution-core image is a normal `2`-subgroup of the quotient lies in
the pullback of `Omega₁(O₂(-))`. -/
private theorem theorem4b_section7_z_mem_M2_of_core_quotient
    {X : Type*} [Group X] [Finite X]
    (M Q : Subgroup X) (z : X)
    (hzN0 : z ∈ theorem4bSection7NCore Q)
    (hzM : z ∈ M) (hzI : IsInvolution z)
    (hcoreQuot : IsPGroup 2
      ((involutionCore (theorem4bSection7M1 M Q)).map
        (QuotientGroup.mk' (theorem4bSection7O1 M Q)))) :
    z ∈ theorem4bSection7M2InX M Q := by
  let A : Subgroup (theorem4bSection7NCore Q) := theorem4bSection7M1 M Q
  let N0 : Subgroup X := theorem4bSection7NCore Q
  let O1 : Subgroup A := theorem4bSection7O1 M Q
  let qA : A →* A ⧸ O1 := QuotientGroup.mk' O1
  let Cbar : Subgroup (A ⧸ O1) :=
    (involutionCore A).map qA
  let zN0 : N0 := ⟨z, hzN0⟩
  let zA : A := ⟨zN0, hzM⟩
  have hzN0I : IsInvolution zN0 := IsInvolution.subtype hzI hzN0
  have hzA : IsInvolution zA := IsInvolution.subtype hzN0I hzM
  have hzCore : zA ∈ involutionCore A := by
    rw [involutionCore_eq_closure]
    exact Subgroup.subset_closure hzA
  have hzCbar : qA zA ∈ Cbar := by
    exact Subgroup.mem_map_of_mem qA hzCore
  letI : Cbar.Normal := by
    dsimp [Cbar, qA]
    exact (inferInstance : (involutionCore A).Normal).map
      (QuotientGroup.mk' O1) (QuotientGroup.mk'_surjective O1)
  have hCbar_le : Cbar ≤ pCore 2 (A ⧸ O1) := by
    exact le_sSup ⟨inferInstance, hcoreQuot⟩
  have hqP : qA zA ∈ pCore 2 (A ⧸ O1) := hCbar_le hzCbar
  let P : Subgroup (A ⧸ O1) := pCore 2 (A ⧸ O1)
  let qzP : P := ⟨qA zA, hqP⟩
  have hqz_pow : qzP ^ 2 = 1 := by
    apply Subtype.ext
    change (qA zA) ^ 2 = 1
    rw [← map_pow, hzA.sq_eq_one, map_one]
  have hqz_omega : qzP ∈ omega₁ (G := P) (p := 2) := by
    change qzP ∈ Subgroup.closure {x : P | x ^ (2 ^ 1) = 1}
    apply Subgroup.subset_closure
    simpa [pow_one] using hqz_pow
  have hqM2 : qA zA ∈ theorem4bSection7M2Quotient M Q := by
    exact Subgroup.mem_map_of_mem P.subtype hqz_omega
  have hzM2 : zA ∈ theorem4bSection7M2 M Q := by
    exact hqM2
  apply Subgroup.mem_map.mpr
  refine ⟨zN0, ?_, rfl⟩
  apply Subgroup.mem_map.mpr
  exact ⟨zA, hzM2, rfl⟩

public theorem theorem4b_section7_z_mem_NCore
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixD M) (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    d.data.z ∈ theorem4bSection7NCore q.chosen.Q := by
  let N : Subgroup X := Subgroup.normalizer (q.chosen.Q : Set X)
  apply Subgroup.mem_map.mpr
  let zN : N := ⟨d.data.z, q.chosen.hzNormQ⟩
  refine ⟨zN, ?_, rfl⟩
  rw [involutionCore_eq_closure]
  exact Subgroup.subset_closure
    (IsInvolution.subtype d.data.hz q.chosen.hzNormQ)

public theorem IsStronglyEmbedded.theorem4b_section7_M1_stronglyEmbedded
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (d : Theorem4bSixD M)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    IsStronglyEmbedded (theorem4bSection7M1 M q.chosen.Q) := by
  let a := q.chosen
  let N : Subgroup X := Subgroup.normalizer (a.Q : Set X)
  let N0 : Subgroup X := theorem4bSection7NCore a.Q
  let M1 : Subgroup N0 := theorem4bSection7M1 M a.Q
  let alpha : conjugateCosetSpace M := theorem4bSection7Base
  have htNotM : a.t ∉ M := by
    intro htM
    apply s.hbetaNe
    calc
      s.beta = a.t • alpha := a.htBase.symm
      _ = alpha := by
        apply MulAction.mem_stabilizer_iff.mp
        rw [show MulAction.stabilizer X alpha = M by
          simp [alpha, theorem4bSection7Base]]
        exact htM
  have htN0 : a.t ∈ N0 := by
    apply Subgroup.mem_map.mpr
    let tN : N := ⟨a.t, a.htNormQ⟩
    refine ⟨tN, ?_, rfl⟩
    change tN ∈ involutionCore N
    rw [involutionCore_eq_closure]
    exact Subgroup.subset_closure (IsInvolution.subtype a.ht a.htNormQ)
  have hzN0 : d.data.z ∈ N0 := by
    apply Subgroup.mem_map.mpr
    let zN : N := ⟨d.data.z, a.hzNormQ⟩
    refine ⟨zN, ?_, rfl⟩
    change zN ∈ involutionCore N
    rw [involutionCore_eq_closure]
    exact Subgroup.subset_closure
      (IsInvolution.subtype d.data.hz a.hzNormQ)
  apply hM.comap_of_injective N0.subtype Subtype.val_injective
  · intro htop
    apply htNotM
    let t0 : N0 := ⟨a.t, htN0⟩
    have htTop : t0 ∈ (⊤ : Subgroup N0) := Subgroup.mem_top _
    rw [← htop] at htTop
    exact htTop
  · exact ⟨⟨d.data.z, hzN0⟩, d.data.hzM,
      IsInvolution.subtype d.data.hz hzN0⟩

/-- The involution `z` belongs to the source subgroup `M₂`. -/
public theorem IsStronglyEmbedded.theorem4b_section7_z_mem_M2
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    d.data.z ∈ theorem4bSection7M2InX M q.chosen.Q := by
  classical
  let a := q.chosen
  let N : Subgroup X := Subgroup.normalizer (a.Q : Set X)
  let L : Subgroup N := involutionCore N
  let N0 : Subgroup X := L.map N.subtype
  let M1 : Subgroup N0 := theorem4bSection7M1 M a.Q
  let alpha : conjugateCosetSpace M := theorem4bSection7Base
  have htNotM : a.t ∉ M := by
    intro htM
    apply s.hbetaNe
    calc
      s.beta = a.t • alpha := a.htBase.symm
      _ = alpha := by
        apply MulAction.mem_stabilizer_iff.mp
        rw [show MulAction.stabilizer X alpha = M by
          simp [alpha, theorem4bSection7Base]]
        exact htM
  have hrankL : TwoRankAtLeastTwo L := by
    apply theorem4b_twoRank_involutionCore_of_twoRank
    by_contra hNrank
    apply (hM.theorem4b_lemma710 hX d hrank hT2 hinduction s q)
    intro u hu
    exact PFAppendixII.pPrimeCore_sup_centralizer_eq_top_of_not_twoRank
      hNrank hu
  let eLN0 : L ≃* N0 := by
    simpa [L, N0, N] using
      (Subgroup.equivMapOfInjective L N.subtype Subtype.val_injective)
  have hrankN0 : TwoRankAtLeastTwo N0 :=
    hrankL.map_of_injective eLN0.toMonoidHom eLN0.injective
  have htN0 : a.t ∈ N0 := by
    apply Subgroup.mem_map.mpr
    let tN : N := ⟨a.t, a.htNormQ⟩
    refine ⟨tN, ?_, rfl⟩
    change tN ∈ Subgroup.closure (involutionsSet N)
    exact Subgroup.subset_closure (IsInvolution.subtype a.ht a.htNormQ)
  have hzN0 : d.data.z ∈ N0 := by
    apply Subgroup.mem_map.mpr
    let zN : N := ⟨d.data.z, a.hzNormQ⟩
    refine ⟨zN, ?_, rfl⟩
    change zN ∈ Subgroup.closure (involutionsSet N)
    exact Subgroup.subset_closure
      (IsInvolution.subtype d.data.hz a.hzNormQ)
  have hM1strong : IsStronglyEmbedded M1 := by
    apply hM.comap_of_injective N0.subtype Subtype.val_injective
    · intro htop
      apply htNotM
      let t0 : N0 := ⟨a.t, htN0⟩
      have htTop : t0 ∈ (⊤ : Subgroup N0) := Subgroup.mem_top _
      rw [← htop] at htTop
      exact htTop
    · exact ⟨⟨d.data.z, hzN0⟩, d.data.hzM,
        IsInvolution.subtype d.data.hz hzN0⟩
  have hrankM1 : TwoRankAtLeastTwo M1 :=
    theorem4b_twoRank_stronglyEmbedded hM1strong hrankN0
  have hQM : a.Q ≤ M := by
    exact a.hQE.trans (inf_le_left.trans inf_le_left)
  have hNproper : N ≠ ⊤ := by
    exact hM.normalizer_ne_top_of_isSimpleGroup_of_ne_bot_of_le
      hX a.hQne hQM
  have hN0N : N0 ≤ N := by
    dsimp [N0, N, theorem4bSection7NCore]
    exact Subgroup.map_subtype_le _
  have hN0properLocal : N0 ≠ ⊤ := by
    intro hN0top
    apply hNproper
    apply top_unique
    intro x _hx
    apply hN0N
    rw [hN0top]
    exact Subgroup.mem_top x
  have hN0proper : theorem4bSection7NCore a.Q ≠ ⊤ := by
    change N0 ≠ ⊤
    exact hN0properLocal
  have hcoreQuot : IsPGroup 2
      ((involutionCore (theorem4bSection7M1 M a.Q)).map
        (QuotientGroup.mk' (theorem4bSection7O1 M a.Q))) := by
    apply theorem4b_section7_M1_core_quotient_isPGroup
      M a.Q hinduction hN0proper
    · change IsStronglyEmbedded (theorem4bSection7M1 M a.Q)
      exact hM1strong
    · change TwoRankAtLeastTwo (theorem4bSection7M1 M a.Q)
      exact hrankM1
  simpa [a] using theorem4b_section7_z_mem_M2_of_core_quotient
    M a.Q d.data.z hzN0 d.data.hzM d.data.hz hcoreQuot

/-- The corrected consequence of the source setup: `(7D)` is supported inside
`M₂` because `z ∈ M₂`, `P₁ ≤ R`, and `R` normalizes `M₂`. -/
public theorem IsStronglyEmbedded.theorem4b_section7_commutator_le_M2
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    ⁅Subgroup.zpowers d.data.z, q.chosen.P₁⁆ ≤
      theorem4bSection7M2InX M q.chosen.Q := by
  have hzM2 : d.data.z ∈ theorem4bSection7M2InX M q.chosen.Q :=
    hM.theorem4b_section7_z_mem_M2 hX d hrank hT2 hinduction s q
  have hzPow : Subgroup.zpowers d.data.z ≤
      theorem4bSection7M2InX M q.chosen.Q := by
    rw [Subgroup.zpowers_le]
    exact hzM2
  have hP₁Norm : q.chosen.P₁ ≤ Subgroup.normalizer
      (theorem4bSection7M2InX M q.chosen.Q : Set X) :=
    q.hP₁R.trans (theorem4b_section7_R_le_normalizer_M2 q)
  exact (Subgroup.commutator_mono hzPow le_rfl).trans
    (theorem4b_commutator_le_left_of_le_normalizer hP₁Norm)

/-- Equation `(7D)` excludes the distinguished involution from the ambient
copy of `O_{p'}(M̂₂)`. -/
public theorem theorem4b_section7_z_not_mem_pPrimeCore_M2Hat
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixD M) (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    d.data.z ∉
      (pPrimeCore d.data.p (theorem4bSection7M2Hat q)).map
        (theorem4bSection7M2Hat q).subtype := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let H : Subgroup X := theorem4bSection7M2Hat q
  let O : Subgroup H := pPrimeCore d.data.p H
  let OX : Subgroup X := O.map H.subtype
  let C : Subgroup X :=
    ⁅Subgroup.zpowers d.data.z, q.chosen.P₁⁆
  intro hzO
  have hP₁H : q.chosen.P₁ ≤ H := by
    exact q.hP₁R.trans (by
      simpa [H, theorem4bSection7M2Hat, theorem4bSection7R] using
        (le_sup_right : q.R ≤
          theorem4bSection7M2InX M q.chosen.Q ⊔ q.R))
  haveI : O.Characteristic := by
    dsimp [O]
    infer_instance
  have hHnormO : H ≤ Subgroup.normalizer (OX : Set X) := by
    exact Subgroup.le_normalizer.trans (by
      simpa [OX] using
        (section8_normalizer_map_subtype_le_of_characteristic
          (H := H) (K := O)))
  have hP₁normO : q.chosen.P₁ ≤ Subgroup.normalizer (OX : Set X) :=
    hP₁H.trans hHnormO
  have hzPowO : Subgroup.zpowers d.data.z ≤ OX := by
    rw [Subgroup.zpowers_le]
    simpa [H, O, OX] using hzO
  have hCO : C ≤ OX := by
    exact (Subgroup.commutator_mono hzPowO le_rfl).trans
      (theorem4b_commutator_le_left_of_le_normalizer hP₁normO)
  have hcardDvd : Nat.card C ∣ Nat.card OX :=
    Subgroup.card_dvd_of_le hCO
  have hOcop : Nat.Coprime d.data.p (Nat.card OX) := by
    rw [show Nat.card OX = Nat.card O by
      simpa [OX] using
        (Subgroup.card_map_of_injective (K := O) (f := H.subtype)
          H.subtype_injective)]
    exact pPrimeCore_coprime_card
  have hCcop : Nat.Coprime d.data.p (Nat.card C) :=
    Nat.Coprime.of_dvd_right hcardDvd hOcop
  have hpC : d.data.p ∣ Nat.card C := by
    simpa [C] using
      theorem4b_section7_sevenD d s q.chosen.P₁ q.chosen.hP₁sylow
  exact ((d.data.hp.coprime_iff_not_dvd).1 hCcop) hpC

/-- The ambient p-prime cores of `M̂₂ = M₂R` and `M₂` coincide.  The
quotient `M̂₂/M₂` is a p-group, so the p-prime core of `M̂₂` lies in `M₂`;
normality of `M₂` in `M̂₂` gives the reverse inclusion. -/
public theorem theorem4b_section7_pPrimeCore_M2Hat_eq_M2
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixD M) (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    (pPrimeCore d.data.p (theorem4bSection7M2Hat q)).map
        (theorem4bSection7M2Hat q).subtype =
      (pPrimeCore d.data.p
          (theorem4bSection7M2InX M q.chosen.Q)).map
        (theorem4bSection7M2InX M q.chosen.Q).subtype := by
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let B : Subgroup X := theorem4bSection7M2InX M q.chosen.Q
  let R : Subgroup X := q.R
  have hRnorm : R ≤ Subgroup.normalizer (B : Set X) := by
    simpa [B, R, theorem4bSection7R] using
      theorem4b_section7_R_le_normalizer_M2 q
  change q.R ≤ Subgroup.normalizer (B : Set X) at hRnorm
  have hRp : IsPGroup d.data.p R := by
    change IsPGroup d.data.p q.R
    exact theorem4bIsSylowSubgroupOf_isPGroup_final q.hRsylow
  change (pPrimeCore d.data.p (theorem4bSection7M2Hat q)).map
      (theorem4bSection7M2Hat q).subtype =
    (pPrimeCore d.data.p
        (theorem4bSection7M2InX M q.chosen.Q)).map
      (theorem4bSection7M2InX M q.chosen.Q).subtype
  convert theorem4b_section7_pPrimeCore_sup_eq
      (theorem4bSection7M2InX M q.chosen.Q) q.R hRnorm hRp using 1 <;>
    ext x <;> rfl

public theorem theorem4b_section7_z_not_mem_pPrimeCore_M2
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixD M) (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    d.data.z ∉
      (pPrimeCore d.data.p
          (theorem4bSection7M2InX M q.chosen.Q)).map
        (theorem4bSection7M2InX M q.chosen.Q).subtype := by
  have hznot := theorem4b_section7_z_not_mem_pPrimeCore_M2Hat d s q
  rw [theorem4b_section7_pPrimeCore_M2Hat_eq_M2 d s q] at hznot
  exact hznot

/-- Corrected form of the source's next nonmembership step.  If `z` lay in
`O_{p′}(M₁)`, then, since `z ∈ M₂`, it would lie in the normal p-prime
subgroup `O_{p′}(M₁) ∩ M₂` of `M₂`, hence in `O_{p′}(M₂)`. -/
public theorem IsStronglyEmbedded.theorem4b_section7_z_not_mem_pPrimeCore_M1
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    d.data.z ∉
      (pPrimeCore d.data.p
          (theorem4bSection7M1InX M q.chosen.Q)).map
        (theorem4bSection7M1InX M q.chosen.Q).subtype := by
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let A : Subgroup X := theorem4bSection7M1InX M q.chosen.Q
  let B : Subgroup X := theorem4bSection7M2InX M q.chosen.Q
  have hBA : B ≤ A := by
    simpa [A, B] using theorem4b_section7_M2_le_M1InX M q.chosen.Q
  have hzB : d.data.z ∈ B := by
    simpa [B] using hM.theorem4b_section7_z_mem_M2
      hX d hrank hT2 hinduction s q
  have hznotB : d.data.z ∉ (pPrimeCore d.data.p B).map B.subtype := by
    simpa [B] using theorem4b_section7_z_not_mem_pPrimeCore_M2 d s q
  intro hzA
  apply hznotB
  exact theorem4b_section7_inf_pPrimeCore_le_pPrimeCore_map B A hBA
    ⟨hzA, hzB⟩

/-- The p-prime core of `M₁` has odd order.  Otherwise it contains an
involution; the strong embedding of the internal copy of `M₁` conjugates that
involution to `z`, contradicting the preceding nonmembership theorem. -/
public theorem IsStronglyEmbedded.theorem4b_section7_pPrimeCore_M1_odd
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    Odd (Nat.card
      (pPrimeCore d.data.p (theorem4bSection7M1 M q.chosen.Q))) := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let N0 : Subgroup X := theorem4bSection7NCore q.chosen.Q
  let A : Subgroup N0 := theorem4bSection7M1 M q.chosen.Q
  let AX : Subgroup X := theorem4bSection7M1InX M q.chosen.Q
  have hzN0 : d.data.z ∈ N0 := by
    simpa [N0] using theorem4b_section7_z_mem_NCore d s q
  let zN0 : N0 := ⟨d.data.z, hzN0⟩
  let zA : A := ⟨zN0, d.data.hzM⟩
  have hAXeq : A.map N0.subtype = AX := by
    rfl
  let eA0 : A ≃* A.map N0.subtype :=
    Subgroup.equivMapOfInjective A N0.subtype N0.subtype_injective
  let eA : A ≃* AX := eA0.trans (MulEquiv.subgroupCongr hAXeq)
  have heAcoe (a : A) : ((eA a : AX) : X) = (((a : A) : N0) : X) := by
    change ((eA0 a : A.map N0.subtype) : X) = (((a : A) : N0) : X)
    exact Subgroup.coe_equivMapOfInjective_apply A N0.subtype
      N0.subtype_injective a
  have hzNotAmbient : d.data.z ∉
      (pPrimeCore d.data.p AX).map AX.subtype := by
    have hpub := hM.theorem4b_section7_z_not_mem_pPrimeCore_M1
      hX d hrank hT2 hinduction s q
    change d.data.z ∉ (pPrimeCore d.data.p AX).map AX.subtype at hpub
    exact hpub
  have hzNotCore : zA ∉ pPrimeCore d.data.p A := by
    intro hzCore
    have hcoreMap :
        (pPrimeCore d.data.p A).map eA.toMonoidHom =
          pPrimeCore d.data.p AX :=
      pPrimeCore_map_iso (p := d.data.p) eA
    have heCore : eA zA ∈ pPrimeCore d.data.p AX := by
      rw [← hcoreMap]
      exact Subgroup.mem_map_of_mem eA.toMonoidHom hzCore
    apply hzNotAmbient
    apply Subgroup.mem_map.mpr
    refine ⟨eA zA, heCore, ?_⟩
    exact heAcoe zA
  have hAstrong : IsStronglyEmbedded A := by
    simpa [A, N0] using hM.theorem4b_section7_M1_stronglyEmbedded d s q
  by_contra hodd
  have heven : Even (Nat.card (pPrimeCore d.data.p A)) :=
    Nat.not_odd_iff_even.mp hodd
  have htwo : 2 ∣ Nat.card (pPrimeCore d.data.p A) :=
    even_iff_two_dvd.mp heven
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup A := pPrimeCore d.data.p A
  obtain ⟨u, huOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := P) 2 (by simpa [P] using htwo)
  let uA : A := (u : A)
  have huOrderN0 : orderOf ((uA : A) : N0) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, huOrder]
  have huParts :=
    (orderOf_eq_prime_iff (x := ((uA : A) : N0)) (p := 2)).mp huOrderN0
  have huI : IsInvolution ((uA : A) : N0) := ⟨huParts.2, huParts.1⟩
  have hzI : IsInvolution (zN0 : N0) :=
    IsInvolution.subtype d.data.hz hzN0
  obtain ⟨g, hgA, hconj⟩ := hAstrong.involutions_conjugate_in
    uA.property huI zA.property hzI
  let gA : A := ⟨g, hgA⟩
  have huP : uA ∈ P := u.property
  have hconjP : rightConjugateElem uA gA ∈ P := by
    simpa [rightConjugateElem] using
      (inferInstance : P.Normal).conj_mem uA huP gA⁻¹
  have hconjA : rightConjugateElem uA gA = zA := by
    apply Subtype.ext
    exact hconj
  rw [hconjA] at hconjP
  exact hzNotCore hconjP

public theorem IsStronglyEmbedded.theorem4b_section7_pPrimeCore_M2_odd
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    Odd (Nat.card
      (pPrimeCore d.data.p (theorem4bSection7M2 M q.chosen.Q))) := by
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let A : Subgroup (theorem4bSection7NCore q.chosen.Q) :=
    theorem4bSection7M1 M q.chosen.Q
  let B : Subgroup A := theorem4bSection7M2 M q.chosen.Q
  letI : B.Normal := by
    simpa [B, A] using theorem4bSection7M2_normal M q.chosen.Q
  have hAodd : Odd (Nat.card (pPrimeCore d.data.p A)) := by
    simpa [A] using hM.theorem4b_section7_pPrimeCore_M1_odd
      hX d hrank hT2 hinduction s q
  have hmaple : (pPrimeCore d.data.p B).map B.subtype ≤
      pPrimeCore d.data.p A := by
    exact pPrimeCore_map_subtype_le_pPrimeCore_of_normal
      (G := A) (p := d.data.p) B
  have hcardMap : Nat.card ((pPrimeCore d.data.p B).map B.subtype) =
      Nat.card (pPrimeCore d.data.p B) := by
    exact Subgroup.card_map_of_injective B.subtype_injective
  apply hAodd.of_dvd_nat
  rw [← hcardMap]
  exact Subgroup.card_dvd_of_le hmaple

/-- Source identity `O_{p′}(M₁) = theta(M₁)`, in the ambient group. -/
public theorem IsStronglyEmbedded.theorem4b_section7_pPrimeCore_M1_eq_theta
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    (pPrimeCore d.data.p
        (theorem4bSection7M1InX M q.chosen.Q)).map
        (theorem4bSection7M1InX M q.chosen.Q).subtype =
      corollary64Theta d.data.p
        (theorem4bSection7M1InX M q.chosen.Q) := by
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let N0 : Subgroup X := theorem4bSection7NCore q.chosen.Q
  let A : Subgroup N0 := theorem4bSection7M1 M q.chosen.Q
  let AX : Subgroup X := theorem4bSection7M1InX M q.chosen.Q
  have hAXeq : A.map N0.subtype = AX := by
    rfl
  let eA0 : A ≃* A.map N0.subtype :=
    Subgroup.equivMapOfInjective A N0.subtype N0.subtype_injective
  let eA : A ≃* AX := eA0.trans (MulEquiv.subgroupCongr hAXeq)
  have hAodd : Odd (Nat.card (pPrimeCore d.data.p A)) := by
    simpa [A] using hM.theorem4b_section7_pPrimeCore_M1_odd
      hX d hrank hT2 hinduction s q
  have hAXodd : Odd (Nat.card (pPrimeCore d.data.p AX)) :=
    theorem4b_section7_pPrimeCore_odd_of_mulEquiv eA hAodd
  have hmapOdd : Odd (Nat.card
      ((pPrimeCore d.data.p AX).map AX.subtype)) := by
    rw [show Nat.card ((pPrimeCore d.data.p AX).map AX.subtype) =
        Nat.card (pPrimeCore d.data.p AX) by
      exact Subgroup.card_map_of_injective AX.subtype_injective]
    exact hAXodd
  simpa [AX] using
    (theorem4b_section7_theta_eq_pPrimeCore_of_odd AX hmapOdd).symm

/-- Source identity `O_{p′}(M₂) = theta(M₂)`, in the ambient group. -/
public theorem IsStronglyEmbedded.theorem4b_section7_pPrimeCore_M2_eq_theta
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    (pPrimeCore d.data.p
        (theorem4bSection7M2InX M q.chosen.Q)).map
        (theorem4bSection7M2InX M q.chosen.Q).subtype =
      corollary64Theta d.data.p
        (theorem4bSection7M2InX M q.chosen.Q) := by
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let N0 : Subgroup X := theorem4bSection7NCore q.chosen.Q
  let A : Subgroup N0 := theorem4bSection7M1 M q.chosen.Q
  let B : Subgroup A := theorem4bSection7M2 M q.chosen.Q
  let B0 : Subgroup N0 := B.map A.subtype
  let BX : Subgroup X := theorem4bSection7M2InX M q.chosen.Q
  let e1 : B ≃* B0 := by
    simpa [B0] using
      (Subgroup.equivMapOfInjective B A.subtype A.subtype_injective)
  have hBXeq : B0.map N0.subtype = BX := by
    rfl
  let e2₀ : B0 ≃* B0.map N0.subtype :=
    Subgroup.equivMapOfInjective B0 N0.subtype N0.subtype_injective
  let e2 : B0 ≃* BX := e2₀.trans (MulEquiv.subgroupCongr hBXeq)
  let eB : B ≃* BX := e1.trans e2
  have hBodd : Odd (Nat.card (pPrimeCore d.data.p B)) := by
    simpa only [B] using hM.theorem4b_section7_pPrimeCore_M2_odd
      hX d hrank hT2 hinduction s q
  have hBXodd : Odd (Nat.card (pPrimeCore d.data.p BX)) :=
    theorem4b_section7_pPrimeCore_odd_of_mulEquiv eB hBodd
  have hmapOdd : Odd (Nat.card
      ((pPrimeCore d.data.p BX).map BX.subtype)) := by
    rw [show Nat.card ((pPrimeCore d.data.p BX).map BX.subtype) =
        Nat.card (pPrimeCore d.data.p BX) by
      exact Subgroup.card_map_of_injective BX.subtype_injective]
    exact hBXodd
  simpa [BX] using
    (theorem4b_section7_theta_eq_pPrimeCore_of_odd BX hmapOdd).symm

/-- Source identity `O_{p′}(M̂₂) = theta(M̂₂)`. -/
public theorem IsStronglyEmbedded.theorem4b_section7_pPrimeCore_M2Hat_eq_theta
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    (pPrimeCore d.data.p (theorem4bSection7M2Hat q)).map
        (theorem4bSection7M2Hat q).subtype =
      corollary64Theta d.data.p (theorem4bSection7M2Hat q) := by
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let H : Subgroup X := theorem4bSection7M2Hat q
  let B : Subgroup X := theorem4bSection7M2InX M q.chosen.Q
  have hcoreEq : (pPrimeCore d.data.p H).map H.subtype =
      (pPrimeCore d.data.p B).map B.subtype := by
    simpa [H, B] using theorem4b_section7_pPrimeCore_M2Hat_eq_M2 d s q
  have hBtheta : (pPrimeCore d.data.p B).map B.subtype =
      corollary64Theta d.data.p B := by
    simpa [B] using hM.theorem4b_section7_pPrimeCore_M2_eq_theta
      hX d hrank hT2 hinduction s q
  have hmapOdd : Odd (Nat.card ((pPrimeCore d.data.p H).map H.subtype)) := by
    rw [hcoreEq, hBtheta]
    exact lemma75_theta_odd_card d.data.p B
  simpa [H] using
    (theorem4b_section7_theta_eq_pPrimeCore_of_odd H hmapOdd).symm

/-! ## The ZJ normality-to-factorization bridge -/

/-- Frattini's argument converts normality of
`Z(J(P)) O_{p'}(G)` into the normalizer factorization used in Lemma 7.11.
The characteristic subgroup `Omega₁(Z(J(P)))` has at least as large a
normalizer as `Z(J(P))`. -/
private theorem theorem4b_zj_factorization_of_normal
    {G : Type u} [Group G] [Finite G] {p : ℕ} (hp : Nat.Prime p)
    (P : Sylow p G)
    (hnorm :
      (thompsonCenter (G := G) (P : Subgroup G) ⊔ pPrimeCore p G).Normal) :
    pPrimeCore p G ⊔
        Subgroup.normalizer
          (corollary64Z ⟨p, hp⟩ (P : Subgroup G) : Set G) =
      ⊤ := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let J : Subgroup G := thompsonCenter (G := G) (P : Subgroup G)
  let O : Subgroup G := pPrimeCore p G
  let K : Subgroup G := J ⊔ O
  let Z : Subgroup G := corollary64Z ⟨p, hp⟩ (P : Subgroup G)
  haveI : O.Normal := by
    dsimp [O]
    infer_instance
  haveI : K.Normal := by
    simpa [K, J, O] using hnorm
  have hJP : J ≤ (P : Subgroup G) := by
    simpa [J] using thompsonCenter_le (G := G) (P : Subgroup G)
  have hPOcop : Nat.Coprime (Nat.card (P : Subgroup G)) (Nat.card O) := by
    rcases P.isPGroup'.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
  have hPO : (P : Subgroup G) ⊓ O = ⊥ :=
    Subgroup.inf_eq_bot_of_coprime hPOcop
  have hPK : (P : Subgroup G) ⊓ K = J := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_sup_of_normal_right.mp hx.2 with
        ⟨j, hj, o, ho, hjo⟩
      have hjP : j ∈ (P : Subgroup G) := hJP hj
      have hoP : o ∈ (P : Subgroup G) := by
        have hoeq : o = j⁻¹ * x := by
          rw [← hjo]
          simp
        rw [hoeq]
        exact P.mul_mem (P.inv_mem hjP) hx.1
      have hoBot : o ∈ (⊥ : Subgroup G) := by
        rw [← hPO]
        exact ⟨hoP, ho⟩
      have hoOne : o = 1 := by simpa using hoBot
      rw [← hjo, hoOne]
      simpa using hj
    · exact le_inf hJP le_sup_left
  let PK : Sylow p K := External.hallSylowSubgroupOfNormal P K
  have hPKmap : (PK : Subgroup K).map K.subtype = J := by
    rw [show (PK : Subgroup K) =
        (P : Subgroup G).comap K.subtype by
      exact External.hallSylowSubgroupOfNormal_coe P K]
    rw [Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype]
    simpa [inf_comm] using hPK
  have hfrattini : Subgroup.normalizer (J : Set G) ⊔ K = ⊤ := by
    simpa [hPKmap] using
      (Sylow.normalizer_sup_eq_top (G := G) (N := K) PK)
  have hnormJZ : Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (Z : Set G) := by
    haveI : (omega₁ (G := J) (p := p)).Characteristic :=
      omega₁_characteristic (G := J) (p := p)
    simpa [J, Z, corollary64Z] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (G := G) (H := J) (K := omega₁ (G := J) (p := p)))
  change O ⊔ Subgroup.normalizer (Z : Set G) = ⊤
  apply top_unique
  rw [← hfrattini]
  apply sup_le
  · exact hnormJZ.trans le_sup_right
  · change J ⊔ O ≤ O ⊔ Subgroup.normalizer (Z : Set G)
    apply sup_le
    · exact Subgroup.le_normalizer.trans (hnormJZ.trans le_sup_right)
    · exact le_sup_left

/-- The operational form of Glauberman's ZJ theorem used below.  Constraint
and stability supply normality; the preceding checked Frattini bridge gives
the actual normalizer factorization. -/
private theorem theorem4b_zj_factorization_of_constrained_stable
    {G : Type u} [Group G] [Finite G] {p : ℕ} (hp : Nat.Prime p)
    (hpodd : p ≠ 2)
    (hOp_ne : pCore p G ≠ ⊥)
    (hconstrained : PConstrainedGroup (G := G) p)
    (hstable : PStableGroup' (G := G) p)
    (P : Sylow p G) :
    pPrimeCore p G ⊔
        Subgroup.normalizer
          (corollary64Z ⟨p, hp⟩ (P : Subgroup G) : Set G) =
      ⊤ := by
  letI : Fact p.Prime := ⟨hp⟩
  apply theorem4b_zj_factorization_of_normal hp P
  exact G_theorem_8_2_11 p hpodd hOp_ne hconstrained hstable P

/-! ## Lemma 7.11: the selected odd-prime Sylow subgroup -/

/-- Hall intersection extracts a Sylow subgroup of a normal subgroup inside
a supplied ambient Sylow subgroup. -/
private theorem theorem4b_section7_exists_sylow_normal_le
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K S H : Subgroup G}
    (hKH : K ≤ H)
    (hHnormK : H ≤ Subgroup.normalizer (K : Set G))
    (hSsyl : theorem4bIsSylowSubgroupOf p S H) :
    ∃ P : Subgroup G,
      theorem4bIsSylowSubgroupOf p P K ∧ P ≤ S := by
  classical
  let KH : Subgroup H := K.subgroupOf H
  letI : KH.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2
    exact hHnormK
  rcases hSsyl with ⟨SH, hSeq⟩
  let T : Sylow p KH := External.hallSylowSubgroupOfNormal SH KH
  let e : KH ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  let PK : Sylow p K :=
    T.mapSurjective (f := e.toMonoidHom) e.surjective
  let P : Subgroup G := (PK : Subgroup K).map K.subtype
  refine ⟨P, ⟨PK, rfl⟩, ?_⟩
  intro x hxP
  rcases Subgroup.mem_map.mp hxP with ⟨xK, hxPK, rfl⟩
  change xK ∈ (T : Subgroup KH).map e.toMonoidHom at hxPK
  rcases Subgroup.mem_map.mp hxPK with ⟨xKH, hxT, hxEq⟩
  have hxSH : (xKH : H) ∈ (SH : Subgroup H) := by
    change xKH ∈ (SH : Subgroup H).comap KH.subtype
    rw [← External.hallSylowSubgroupOfNormal_coe SH KH]
    exact hxT
  have hxS : (((xKH : KH) : H) : G) ∈ S := by
    rw [hSeq]
    exact Subgroup.mem_map_of_mem H.subtype hxSH
  have hval : (xK : G) = (((xKH : KH) : H) : G) := by
    rw [← hxEq]
    rfl
  change (xK : G) ∈ S
  rw [hval]
  exact hxS

/-- If a Sylow subgroup maps into a quotient of order coprime to its prime,
then it lies in the quotient kernel. -/
private theorem theorem4b_section7_sylow_le_of_quotient_coprime
    {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hcop : Nat.Coprime p (Nat.card (G ⧸ N))) :
    (P : Subgroup G) ≤ N := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Pbar : Subgroup (G ⧸ N) := (P : Subgroup G).map q
  have hPbarp : IsPGroup p Pbar := P.isPGroup'.map q
  have hPbarcop : Nat.Coprime p (Nat.card Pbar) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card Pbar) hcop
  have hPbarCard : Nat.card Pbar = 1 := by
    rcases hPbarp.card_eq_or_dvd with hcard | hdiv
    · exact hcard
    · exact False.elim
        (((Fact.out : Nat.Prime p).coprime_iff_not_dvd).1 hPbarcop hdiv)
  have hPbarBot : Pbar = ⊥ := Subgroup.card_eq_one.mp hPbarCard
  intro x hx
  have hxbar : q x ∈ Pbar := Subgroup.mem_map_of_mem q hx
  have hxone : q x = 1 := by
    simpa [hPbarBot] using hxbar
  exact (QuotientGroup.eq_one_iff (N := N) (x := x)).1 hxone

/-- A Sylow subgroup of a normal subgroup is Sylow in the overgroup when the
quotient order is coprime to the prime. -/
private theorem theorem4b_section7_sylow_of_normal_quotient_coprime
    {G : Type u} [Group G] [Finite G] {p : ℕ}
    {N P H : Subgroup G}
    (hp : Nat.Prime p)
    (hNH : N ≤ H)
    (hHnormN : H ≤ Subgroup.normalizer (N : Set G))
    (hPsyl : theorem4bIsSylowSubgroupOf p P N)
    (hcop : Nat.Coprime p (Nat.card (H ⧸ N.subgroupOf H))) :
    theorem4bIsSylowSubgroupOf p P H := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let NH : Subgroup H := N.subgroupOf H
  letI : NH.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2
    exact hHnormN
  rcases hPsyl with ⟨PN, hPeq⟩
  let S : Sylow p H := Classical.choice inferInstance
  have hSleNH : (S : Subgroup H) ≤ NH :=
    theorem4b_section7_sylow_le_of_quotient_coprime S hcop
  let SN : Sylow p NH := S.subtype hSleNH
  have hPcard : Nat.card P = p ^ (Nat.card N).factorization p := by
    rw [hPeq, Subgroup.card_map_of_injective N.subtype_injective]
    exact PN.card_eq_multiplicity
  have hScard : Nat.card (S : Subgroup H) =
      p ^ (Nat.card N).factorization p := by
    calc
      Nat.card (S : Subgroup H) = Nat.card (SN : Subgroup NH) := by
        symm
        simpa [SN] using
          (natCard_subgroupOf_eq (S : Subgroup H) NH hSleNH)
      _ = p ^ (Nat.card NH).factorization p := SN.card_eq_multiplicity
      _ = p ^ (Nat.card N).factorization p := by
        rw [show Nat.card NH = Nat.card N by
          simpa [NH] using natCard_subgroupOf_eq N H hNH]
  have hPN : P ≤ N := by
    rw [hPeq]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hPH : P ≤ H := hPN.trans hNH
  have hPHcard : Nat.card (P.subgroupOf H) =
      p ^ (Nat.card H).factorization p := by
    calc
      Nat.card (P.subgroupOf H) = Nat.card P :=
        natCard_subgroupOf_eq P H hPH
      _ = Nat.card (S : Subgroup H) := hPcard.trans hScard.symm
      _ = p ^ (Nat.card H).factorization p := S.card_eq_multiplicity
  let PH : Sylow p H := Sylow.ofCard (P.subgroupOf H) hPHcard
  refine ⟨PH, ?_⟩
  change P = (P.subgroupOf H).map H.subtype
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPH]

/-- Equation `(7E)` identifies the nested ambient image of the internal
pullback `O1` with the full odd core of `N°`. -/
private theorem IsStronglyEmbedded.theorem4b_section7_O1InX_eq_oddCore
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    let Q : Subgroup X := q.chosen.Q
    let N0 : Subgroup X := theorem4bSection7NCore Q
    let A : Subgroup N0 := theorem4bSection7M1 M Q
    let O1 : Subgroup A := theorem4bSection7O1 M Q
    ((O1.map A.subtype).map N0.subtype : Subgroup X) =
      (twoPrimeCore N0).map N0.subtype := by
  classical
  dsimp only
  let Q : Subgroup X := q.chosen.Q
  let N0 : Subgroup X := theorem4bSection7NCore Q
  let A : Subgroup N0 := theorem4bSection7M1 M Q
  let O1 : Subgroup A := theorem4bSection7O1 M Q
  let OX : Subgroup X := (twoPrimeCore N0).map N0.subtype
  let E : Subgroup X := theorem4bSection7E M d.data.z s.beta
  have hOXE : OX ≤ E := by
    simpa [OX, N0, Q] using
      hM.theorem4b_section7_sevenE hX d hrank hT2 hinduction s q
  have hEM : E ≤ M := inf_le_left.trans inf_le_left
  apply le_antisymm
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨n, hn, rfl⟩
    rcases Subgroup.mem_map.mp hn with ⟨a, ha, rfl⟩
    exact Subgroup.mem_map_of_mem N0.subtype ha
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨n, hn, rfl⟩
    have hnOX : (n : X) ∈ OX :=
      Subgroup.mem_map_of_mem N0.subtype hn
    have hnM : (n : X) ∈ M := hEM (hOXE hnOX)
    let a : A := ⟨n, hnM⟩
    apply Subgroup.mem_map.mpr
    refine ⟨(a : N0), ?_, rfl⟩
    apply Subgroup.mem_map.mpr
    refine ⟨a, ?_, rfl⟩
    exact hn

/-- The kernel of `(7F)` lies in its full preimage, so the odd core of `N°`
lies in the ambient copy of `M₂`. -/
private theorem IsStronglyEmbedded.theorem4b_section7_oddCore_le_M2
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    let N0 : Subgroup X := theorem4bSection7NCore q.chosen.Q
    (twoPrimeCore N0).map N0.subtype ≤
      theorem4bSection7M2InX M q.chosen.Q := by
  dsimp only
  let Q : Subgroup X := q.chosen.Q
  let N0 : Subgroup X := theorem4bSection7NCore Q
  let A : Subgroup N0 := theorem4bSection7M1 M Q
  let O1 : Subgroup A := theorem4bSection7O1 M Q
  let B0 : Subgroup A := theorem4bSection7M2 M Q
  let U : Subgroup (A ⧸ O1) := theorem4bSection7M2Quotient M Q
  have hO1B0 : O1 ≤ B0 := by
    intro a ha
    change QuotientGroup.mk' O1 a ∈ U
    have haOne : QuotientGroup.mk' O1 a = 1 :=
      (QuotientGroup.eq_one_iff (N := O1) (x := a)).2 ha
    rw [haOne]
    exact U.one_mem
  have hOeq : ((O1.map A.subtype).map N0.subtype : Subgroup X) =
      (twoPrimeCore N0).map N0.subtype := by
    simpa [Q, N0, A, O1] using
      hM.theorem4b_section7_O1InX_eq_oddCore
        hX d hrank hT2 hinduction s q
  rw [← hOeq]
  change (O1.map A.subtype).map N0.subtype ≤
    (B0.map A.subtype).map N0.subtype
  exact Subgroup.map_mono (Subgroup.map_mono hO1B0)

/-- The selected subgroup `R` is a Sylow `p`-subgroup of
`M̂₂ = M₂ R`.  This is the corrected Sylow step in Lemma 7.11; the proof
uses the Hall intersection in `O₂'(N°) ⊔ P₁` and never asserts
`P₁ ≤ M₂`. -/
public theorem IsStronglyEmbedded.theorem4b_section7_R_isSylow_M2Hat
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    theorem4bIsSylowSubgroupOf d.data.p
      (theorem4bSection7R q) (theorem4bSection7M2Hat q) := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let Q : Subgroup X := q.chosen.Q
  let E : Subgroup X := theorem4bSection7E M d.data.z s.beta
  let N0 : Subgroup X := theorem4bSection7NCore Q
  let A : Subgroup N0 := theorem4bSection7M1 M Q
  let O1 : Subgroup A := theorem4bSection7O1 M Q
  let B0 : Subgroup A := theorem4bSection7M2 M Q
  let U : Subgroup (A ⧸ O1) := theorem4bSection7M2Quotient M Q
  let OX : Subgroup X := (twoPrimeCore N0).map N0.subtype
  let P1 : Subgroup X := q.chosen.P₁
  let R : Subgroup X := q.R
  let B : Subgroup X := theorem4bSection7M2InX M Q
  let H : Subgroup X := theorem4bSection7M2Hat q
  have hOXE : OX ≤ E := by
    simpa [OX, N0, Q, E] using
      hM.theorem4b_section7_sevenE hX d hrank hT2 hinduction s q
  have hP1E : P1 ≤ E := by
    simpa [P1, E] using
      theorem4bIsSylowSubgroupOf_le_final q.chosen.hP₁sylow
  have hP1R : P1 ≤ R := by
    simpa [P1, R, theorem4bSection7R] using q.hP₁R
  have hRnormN0 : R ≤ Subgroup.normalizer (N0 : Set X) := by
    simpa [R, N0, Q] using theorem4b_section7_R_le_normalizer_NCore q
  haveI : (twoPrimeCore N0).Characteristic := by
    simpa [twoPrimeCore] using
      (pPrimeCore_characteristic (p := 2) (G := N0))
  have hNormN0normOX : Subgroup.normalizer (N0 : Set X) ≤
      Subgroup.normalizer (OX : Set X) := by
    simpa [OX] using
      (External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
        N0 (twoPrimeCore N0))
  have hP1normOX : P1 ≤ Subgroup.normalizer (OX : Set X) :=
    hP1R.trans (hRnormN0.trans hNormN0normOX)
  let H0 : Subgroup X := OX ⊔ P1
  have hH0E : H0 ≤ E := sup_le hOXE hP1E
  have hP1H0 : P1 ≤ H0 := le_sup_right
  have hP1sylH0 : theorem4bIsSylowSubgroupOf d.data.p P1 H0 := by
    exact theorem4bIsSylowSubgroupOf_of_le_final d.data.hp
      q.chosen.hP₁sylow hP1H0 hH0E
  have hH0normOX : H0 ≤ Subgroup.normalizer (OX : Set X) :=
    sup_le Subgroup.le_normalizer hP1normOX
  obtain ⟨P0, hP0sylOX, hP0P1⟩ :=
    theorem4b_section7_exists_sylow_normal_le
      (K := OX) (S := P1) (H := H0)
      le_sup_left hH0normOX hP1sylH0
  have hP0R : P0 ≤ R := hP0P1.trans hP1R
  have hOXB : OX ≤ B := by
    simpa [OX, B, N0, Q] using
      hM.theorem4b_section7_oddCore_le_M2
        hX d hrank hT2 hinduction s q
  have hBleN0 : B ≤ N0 := by
    change (B0.map A.subtype).map N0.subtype ≤ N0
    exact Subgroup.map_subtype_le _
  have hN0normOX : N0 ≤ Subgroup.normalizer (OX : Set X) :=
    Subgroup.le_normalizer.trans hNormN0normOX
  have hBnormOX : B ≤ Subgroup.normalizer (OX : Set X) :=
    hBleN0.trans hN0normOX
  letI : (OX.subgroupOf B).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hOXB).2
    exact hBnormOX
  have hO1B0 : O1 ≤ B0 := by
    intro a ha
    change QuotientGroup.mk' O1 a ∈ U
    have haOne : QuotientGroup.mk' O1 a = 1 :=
      (QuotientGroup.eq_one_iff (N := O1) (x := a)).2 ha
    rw [haOne]
    exact U.one_mem
  letI : (O1.subgroupOf B0).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hO1B0).2
    rw [Subgroup.normalizer_eq_top_iff.mpr
      (inferInstance : O1.Normal)]
    exact le_top
  let P2 : Subgroup (A ⧸ O1) := pCore 2 (A ⧸ O1)
  have hOmega2 : IsPGroup 2 (omega₁ (G := P2) (p := 2)) :=
    pCore_isPGroup.to_subgroup (omega₁ (G := P2) (p := 2))
  have hU2 : IsPGroup 2 U := by
    change IsPGroup 2 ((omega₁ (G := P2) (p := 2)).map P2.subtype)
    exact hOmega2.map P2.subtype
  let qA : A →* A ⧸ O1 := QuotientGroup.mk' O1
  have hB0map : B0.map qA = U := by
    simpa [B0, qA, U, A, O1] using theorem4b_section7_sevenF M Q
  let eQuot : B0 ⧸ O1.subgroupOf B0 ≃* B0.map qA :=
    quotientSubgroupRangeEquiv B0 O1
  have hRange2 : IsPGroup 2 (B0.map qA) := by
    rw [hB0map]
    exact hU2
  have hInternalQuot2 : IsPGroup 2 (B0 ⧸ O1.subgroupOf B0) :=
    hRange2.of_equiv eQuot.symm
  have hOeq : ((O1.map A.subtype).map N0.subtype : Subgroup X) = OX := by
    simpa [Q, N0, A, O1, OX] using
      hM.theorem4b_section7_O1InX_eq_oddCore
        hX d hrank hT2 hinduction s q
  have hcardB : Nat.card B = Nat.card B0 := by
    change Nat.card ((B0.map A.subtype).map N0.subtype) = Nat.card B0
    rw [Subgroup.card_map_of_injective N0.subtype_injective,
      Subgroup.card_map_of_injective A.subtype_injective]
  have hcardOX : Nat.card OX = Nat.card O1 := by
    rw [← hOeq,
      Subgroup.card_map_of_injective N0.subtype_injective,
      Subgroup.card_map_of_injective A.subtype_injective]
  have hcardOXsub : Nat.card (OX.subgroupOf B) = Nat.card O1 :=
    (natCard_subgroupOf_eq OX B hOXB).trans hcardOX
  have hcardO1sub : Nat.card (O1.subgroupOf B0) = Nat.card O1 :=
    natCard_subgroupOf_eq O1 B0 hO1B0
  have hquotCard : Nat.card (B ⧸ OX.subgroupOf B) =
      Nat.card (B0 ⧸ O1.subgroupOf B0) := by
    apply Nat.mul_right_cancel (Nat.card_pos (α := O1))
    calc
      Nat.card (B ⧸ OX.subgroupOf B) * Nat.card O1 =
          Nat.card (B ⧸ OX.subgroupOf B) *
            Nat.card (OX.subgroupOf B) := by rw [hcardOXsub]
      _ = Nat.card B :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup
          (s := OX.subgroupOf B)).symm
      _ = Nat.card B0 := hcardB
      _ = Nat.card (B0 ⧸ O1.subgroupOf B0) *
          Nat.card (O1.subgroupOf B0) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup
          (s := O1.subgroupOf B0)
      _ = Nat.card (B0 ⧸ O1.subgroupOf B0) * Nat.card O1 := by
        rw [hcardO1sub]
  have hAmbientQuot2 : IsPGroup 2 (B ⧸ OX.subgroupOf B) := by
    rcases IsPGroup.iff_card.mp hInternalQuot2 with ⟨n, hn⟩
    apply IsPGroup.iff_card.mpr
    refine ⟨n, ?_⟩
    rw [hquotCard, hn]
  have hquotCop : Nat.Coprime d.data.p
      (Nat.card (B ⧸ OX.subgroupOf B)) := by
    rcases IsPGroup.iff_card.mp hAmbientQuot2 with ⟨n, hn⟩
    rw [hn]
    exact d.data.hpOdd.coprime_two_right.pow_right n
  have hP0sylB : theorem4bIsSylowSubgroupOf d.data.p P0 B :=
    theorem4b_section7_sylow_of_normal_quotient_coprime
      d.data.hp hOXB hBnormOX hP0sylOX hquotCop
  have hRnormB : R ≤ Subgroup.normalizer (B : Set X) := by
    simpa [R, B, Q, theorem4bSection7R] using
      theorem4b_section7_R_le_normalizer_M2 q
  have hBH : B ≤ H := by
    simp [H, B, Q, theorem4bSection7M2Hat, theorem4bSection7R]
  have hRH : R ≤ H := by
    simp [H, R, theorem4bSection7M2Hat, theorem4bSection7R]
  have hHnormB : H ≤ Subgroup.normalizer (B : Set X) := by
    simpa [H, B, R, Q, theorem4bSection7M2Hat,
      theorem4bSection7R] using
      (sup_le Subgroup.le_normalizer hRnormB :
        B ⊔ R ≤ Subgroup.normalizer (B : Set X))
  let BH : Subgroup H := B.subgroupOf H
  let RH : Subgroup H := R.subgroupOf H
  letI : BH.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hBH).2
    exact hHnormB
  have hRp : IsPGroup d.data.p R := by
    change IsPGroup d.data.p q.R
    exact theorem4bIsSylowSubgroupOf_isPGroup_final q.hRsylow
  have hRHp : IsPGroup d.data.p RH :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm
  obtain ⟨S, hRHleS⟩ := hRHp.exists_le_sylow
  let Sx : Subgroup X := (S : Subgroup H).map H.subtype
  have hRSx : R ≤ Sx := by
    intro x hxR
    let xH : H := ⟨x, hRH hxR⟩
    apply Subgroup.mem_map.mpr
    refine ⟨xH, ?_, rfl⟩
    apply hRHleS
    exact hxR
  let K : Subgroup X := Sx ⊓ B
  have hP0B : P0 ≤ B := theorem4bIsSylowSubgroupOf_le_final hP0sylB
  have hP0K : P0 ≤ K := le_inf (hP0R.trans hRSx) hP0B
  have hSxp : IsPGroup d.data.p Sx := S.isPGroup'.map H.subtype
  let KS : Subgroup Sx := K.subgroupOf Sx
  have hKSp : IsPGroup d.data.p KS := hSxp.to_subgroup KS
  let eKS : KS ≃* K := Subgroup.subgroupOfEquivOfLe inf_le_left
  have hKp : IsPGroup d.data.p K := hKSp.of_equiv eKS
  have hcardKle : Nat.card K ≤ Nat.card P0 :=
    theorem4b_lemma710_card_le_sylow_of_isPGroup
      d.data.hp hKp inf_le_right hP0sylB
  have hP0eqK : P0 = K :=
    Subgroup.eq_of_le_of_card_ge hP0K hcardKle
  have hsup : BH ⊔ RH = ⊤ := by
    apply top_unique
    intro x _hx
    have hxH : (x : X) ∈ H := x.property
    have hmapSup : (BH ⊔ RH).map H.subtype = H := by
      rw [Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le hBH,
        Subgroup.map_subgroupOf_eq_of_le hRH]
      rfl
    have hxMap : (x : X) ∈ (BH ⊔ RH).map H.subtype := by
      rw [hmapSup]
      exact hxH
    rcases Subgroup.mem_map.mp hxMap with ⟨y, hy, hyx⟩
    have hyEq : y = x := Subtype.ext hyx
    rwa [hyEq] at hy
  have hSxR : Sx ≤ R := by
    intro x hxSx
    rcases Subgroup.mem_map.mp hxSx with ⟨xH, hxS, rfl⟩
    have hxSup : xH ∈ BH ⊔ RH := by
      rw [hsup]
      trivial
    rcases Subgroup.mem_sup_of_normal_left.mp hxSup with
      ⟨b, hbB, r, hrR, hbr⟩
    have hrS : r ∈ (S : Subgroup H) := hRHleS hrR
    have hbS : b ∈ (S : Subgroup H) := by
      have hbEq : b = xH * r⁻¹ := by
        rw [← hbr]
        simp
      rw [hbEq]
      exact S.mul_mem hxS (S.inv_mem hrS)
    have hbK : (b : X) ∈ K := by
      refine ⟨Subgroup.mem_map_of_mem H.subtype hbS, ?_⟩
      exact hbB
    have hbP0 : (b : X) ∈ P0 := by
      rw [hP0eqK]
      exact hbK
    have hbR : (b : X) ∈ R := hP0R hbP0
    have hbrX : (b : X) * (r : X) = (xH : X) :=
      congrArg (fun y : H => (y : X)) hbr
    change (xH : X) ∈ R
    rw [← hbrX]
    exact R.mul_mem hbR hrR
  have hReq : R = Sx := le_antisymm hRSx hSxR
  refine ⟨S, ?_⟩
  change R = (S : Subgroup H).map H.subtype
  exact hReq

/-! ## Lemma 7.11: solvability and transport support -/

/-- The pulled-back odd kernel in `(7F)` has odd order. -/
private theorem theorem4b_section7_O1_odd
    {X : Type u} [Group X] [Finite X] (M Q : Subgroup X) :
    Odd (Nat.card (theorem4bSection7O1 M Q)) := by
  let N0 : Subgroup X := theorem4bSection7NCore Q
  let A : Subgroup N0 := theorem4bSection7M1 M Q
  let O1 : Subgroup A := theorem4bSection7O1 M Q
  have hO1le : O1.map A.subtype ≤ twoPrimeCore N0 := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    exact ha
  have hcoreOdd : Odd (Nat.card (twoPrimeCore N0)) :=
    Nat.coprime_two_left.mp (by
      simpa [twoPrimeCore] using
        (pPrimeCore_coprime_card (G := N0) (p := 2)))
  have hmapOdd : Odd (Nat.card (O1.map A.subtype)) :=
    Odd.of_dvd_nat hcoreOdd (Subgroup.card_dvd_of_le hO1le)
  rw [Subgroup.card_map_of_injective A.subtype_injective] at hmapOdd
  exact hmapOdd

/-- The quotient in `(7F)` has abelian Sylow `2`-subgroups, by the strong
embedding conjugacy of involutions and the oddness of `O₁`. -/
private theorem theorem4b_section7_M2_hasAbelianSylow
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (d : Theorem4bSixD M)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    HasAbelianSylow 2
      (theorem4bSection7M2InX M q.chosen.Q) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup X := q.chosen.Q
  let N0 : Subgroup X := theorem4bSection7NCore Q
  let A : Subgroup N0 := theorem4bSection7M1 M Q
  let O1 : Subgroup A := theorem4bSection7O1 M Q
  let B0 : Subgroup A := theorem4bSection7M2 M Q
  let U : Subgroup (A ⧸ O1) := theorem4bSection7M2Quotient M Q
  let B : Subgroup X := theorem4bSection7M2InX M Q
  have hO1odd : Odd (Nat.card O1) := by
    simpa [O1, A, N0, Q] using theorem4b_section7_O1_odd M Q
  have hAstrong : IsStronglyEmbedded A := by
    simpa [A, N0, Q] using
      hM.theorem4b_section7_M1_stronglyEmbedded d s q
  have hUcomm : IsMulCommutative U := by
    change IsMulCommutative
      ((omega₁ (G := pCore 2 (A ⧸ O1)) (p := 2)).map
        (pCore 2 (A ⧸ O1)).subtype)
    exact omega₁_pCore_quotient_isMulCommutative_of_stronglyEmbedded
      hAstrong O1 hO1odd
  have hO1B0 : O1 ≤ B0 := by
    intro a ha
    change QuotientGroup.mk' O1 a ∈ U
    have haOne : QuotientGroup.mk' O1 a = 1 :=
      (QuotientGroup.eq_one_iff (N := O1) (x := a)).2 ha
    rw [haOne]
    exact U.one_mem
  haveI : (O1.subgroupOf B0).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hO1B0).2
    rw [Subgroup.normalizer_eq_top_iff.mpr
      (inferInstance : O1.Normal)]
    exact le_top
  let qA : A →* A ⧸ O1 := QuotientGroup.mk' O1
  have hB0map : B0.map qA = U := by
    simpa [B0, qA, U, A, O1, N0, Q] using
      theorem4b_section7_sevenF M Q
  let eQuot : B0 ⧸ O1.subgroupOf B0 ≃* B0.map qA :=
    quotientSubgroupRangeEquiv B0 O1
  have hquotComm : IsMulCommutative (B0 ⧸ O1.subgroupOf B0) := by
    letI : IsMulCommutative (B0.map qA) := by
      rw [hB0map]
      exact hUcomm
    refine ⟨⟨?_⟩⟩
    intro x y
    apply eQuot.injective
    simpa using mul_comm' (eQuot x) (eQuot y)
  have hO1subOdd : Odd (Nat.card (O1.subgroupOf B0)) := by
    rw [natCard_subgroupOf_eq O1 B0 hO1B0]
    exact hO1odd
  have hB0abel : HasAbelianSylow 2 B0 :=
    hasAbelianSylowTwo_of_odd_normal_quotient_isMulCommutative
      (O1.subgroupOf B0) hO1subOdd hquotComm
  let e1 : B0 ≃* B0.map A.subtype :=
    Subgroup.equivMapOfInjective B0 A.subtype A.subtype_injective
  let e2 : B0.map A.subtype ≃* B :=
    Subgroup.equivMapOfInjective (B0.map A.subtype) N0.subtype
      N0.subtype_injective
  let eB : B0 ≃* B := e1.trans e2
  change HasAbelianSylow 2 B
  exact hB0abel.of_mulEquiv eB

/-- Since `M̂₂/M₂` is an odd `p`-group, the abelian Sylow `2`-subgroups of
`M₂` are also Sylow in `M̂₂`. -/
private theorem theorem4b_section7_M2Hat_hasAbelianSylow
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    {d : Theorem4bSixD M} {s : Theorem4bSection7SecondStage d}
    (q : Theorem4bSection7MaximalQData d s) :
    HasAbelianSylow 2 (theorem4bSection7M2Hat q) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let Q : Subgroup X := q.chosen.Q
  have hQeq : Q = q.chosen.Q := rfl
  cases hQeq
  let B : Subgroup X := theorem4bSection7M2InX M Q
  let R : Subgroup X := q.R
  let H : Subgroup X := theorem4bSection7M2Hat q
  have hBH : B ≤ H := by
    change theorem4bSection7M2InX M q.chosen.Q ≤
      theorem4bSection7M2InX M q.chosen.Q ⊔ q.R
    exact le_sup_left
  have hRnormB : R ≤ Subgroup.normalizer (B : Set X) := by
    change q.R ≤ Subgroup.normalizer
      (theorem4bSection7M2InX M q.chosen.Q : Set X)
    exact theorem4b_section7_R_le_normalizer_M2 q
  have hHnormB : H ≤ Subgroup.normalizer (B : Set X) := by
    change (theorem4bSection7M2InX M q.chosen.Q ⊔ q.R) ≤
      Subgroup.normalizer
        (theorem4bSection7M2InX M q.chosen.Q : Set X)
    exact sup_le Subgroup.le_normalizer hRnormB
  let BH : Subgroup H := B.subgroupOf H
  letI : BH.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hBH).2
    exact hHnormB
  have hBabel : HasAbelianSylow 2 B := by
    simpa [B, Q] using theorem4b_section7_M2_hasAbelianSylow hM d s q
  let eB : BH ≃* B := Subgroup.subgroupOfEquivOfLe hBH
  have hBHabel : HasAbelianSylow 2 BH :=
    hBabel.of_mulEquiv eB.symm
  have hRp : IsPGroup d.data.p R := by
    change IsPGroup d.data.p q.R
    exact theorem4bIsSylowSubgroupOf_isPGroup_final q.hRsylow
  haveI : (B.subgroupOf (B ⊔ R)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
    exact sup_le Subgroup.le_normalizer hRnormB
  have hquotP : IsPGroup d.data.p (H ⧸ BH) := by
    change IsPGroup d.data.p
      (↥(theorem4bSection7M2InX M q.chosen.Q ⊔ q.R) ⧸
        (theorem4bSection7M2InX M q.chosen.Q).subgroupOf
          (theorem4bSection7M2InX M q.chosen.Q ⊔ q.R))
    exact theorem4b_section7_quotient_sup_isPGroup
      (theorem4bSection7M2InX M q.chosen.Q) q.R hRp
  have hquotOdd : Odd (Nat.card (H ⧸ BH)) := by
    rcases IsPGroup.iff_card.mp hquotP with ⟨n, hn⟩
    rw [hn]
    exact d.data.hpOdd.pow
  exact HasAbelianSylow.of_normal_odd_quotient BH hBHabel hquotOdd

/-- The subgroup `M₂` is solvable: its normal odd layer is solvable by the
odd-order theorem, and its quotient is the `2`-group specified in `(7F)`. -/
private theorem theorem4b_section7_M2_solvable
    {X : Type*} [Group X] [Finite X] (M Q : Subgroup X) :
    Group.IsSolvable (theorem4bSection7M2InX M Q) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N0 : Subgroup X := theorem4bSection7NCore Q
  let A : Subgroup N0 := theorem4bSection7M1 M Q
  let O1 : Subgroup A := theorem4bSection7O1 M Q
  let B0 : Subgroup A := theorem4bSection7M2 M Q
  let U : Subgroup (A ⧸ O1) := theorem4bSection7M2Quotient M Q
  let B : Subgroup X := theorem4bSection7M2InX M Q
  have hO1le : O1.map A.subtype ≤ twoPrimeCore N0 := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    exact ha
  have hO1odd : Odd (Nat.card O1) := by
    have hcoreOdd : Odd (Nat.card (twoPrimeCore N0)) :=
      Nat.coprime_two_left.mp (by
        simpa [twoPrimeCore] using
          (pPrimeCore_coprime_card (G := N0) (p := 2)))
    have hmapOdd : Odd (Nat.card (O1.map A.subtype)) :=
      Odd.of_dvd_nat hcoreOdd (Subgroup.card_dvd_of_le hO1le)
    rw [Subgroup.card_map_of_injective A.subtype_injective] at hmapOdd
    exact hmapOdd
  letI : Group.IsSolvable O1 := odd_order_theorem O1 hO1odd
  have hO1B0 : O1 ≤ B0 := by
    intro a ha
    change QuotientGroup.mk' O1 a ∈ U
    have haOne : QuotientGroup.mk' O1 a = 1 :=
      (QuotientGroup.eq_one_iff (N := O1) (x := a)).2 ha
    rw [haOne]
    exact U.one_mem
  have hU2 : IsPGroup 2 U := by
    let P2 : Subgroup (A ⧸ O1) := pCore 2 (A ⧸ O1)
    have hOmega2 : IsPGroup 2 (omega₁ (G := P2) (p := 2)) :=
      pCore_isPGroup.to_subgroup (omega₁ (G := P2) (p := 2))
    change IsPGroup 2 ((omega₁ (G := P2) (p := 2)).map P2.subtype)
    exact hOmega2.map P2.subtype
  let qA : A →* A ⧸ O1 := QuotientGroup.mk' O1
  have hB0map : B0.map qA = U := by
    simpa [B0, qA, U, A, O1] using theorem4b_section7_sevenF M Q
  let eQuot : B0 ⧸ O1.subgroupOf B0 ≃* B0.map qA :=
    quotientSubgroupRangeEquiv B0 O1
  have hquot0 : IsPGroup 2 (B0 ⧸ O1.subgroupOf B0) := by
    have hRange2 : IsPGroup 2 (B0.map qA) := by
      rw [hB0map]
      exact hU2
    exact hRange2.of_equiv eQuot.symm
  haveI : (O1.subgroupOf B0).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hO1B0).2
    rw [Subgroup.normalizer_eq_top_iff.mpr
      (inferInstance : O1.Normal)]
    exact le_top
  have hO1subSolv : Group.IsSolvable (O1.subgroupOf B0) := by
    let eO : O1.subgroupOf B0 ≃* O1 :=
      Subgroup.subgroupOfEquivOfLe hO1B0
    exact Group.isSolvable_of_isSolvable_injective (f := eO.toMonoidHom) eO.injective
  letI : Group.IsSolvable (O1.subgroupOf B0) := hO1subSolv
  letI : Group.IsSolvable (B0 ⧸ O1.subgroupOf B0) := by
    have hnil := hquot0.isNilpotent
    letI : Group.IsNilpotent (B0 ⧸ O1.subgroupOf B0) := hnil
    infer_instance
  have hB0solv : Group.IsSolvable B0 :=
    isSolvable_of_normal_subgroup_and_quotient (O1.subgroupOf B0)
  letI : Group.IsSolvable B0 := hB0solv
  let e1 : B0 ≃* B0.map A.subtype :=
    Subgroup.equivMapOfInjective B0 A.subtype A.subtype_injective
  let e2 : B0.map A.subtype ≃* B :=
    Subgroup.equivMapOfInjective (B0.map A.subtype) N0.subtype
      N0.subtype_injective
  let eB : B0 ≃* B := e1.trans e2
  change Group.IsSolvable B
  exact Group.isSolvable_of_isSolvable_injective (f := eB.symm.toMonoidHom)
    eB.symm.injective

/-- The normalized product `M̂₂ = M₂R` is solvable, since both `M₂` and the
quotient by `M₂` are solvable. -/
private theorem theorem4b_section7_M2Hat_solvable
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {d : Theorem4bSixD M} {s : Theorem4bSection7SecondStage d}
    (q : Theorem4bSection7MaximalQData d s) :
    Group.IsSolvable (theorem4bSection7M2Hat q) := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let Q : Subgroup X := q.chosen.Q
  have hQeq : Q = q.chosen.Q := rfl
  cases hQeq
  let B : Subgroup X := theorem4bSection7M2InX M Q
  let R : Subgroup X := q.R
  let H : Subgroup X := theorem4bSection7M2Hat q
  have hBH : B ≤ H := by
    change theorem4bSection7M2InX M q.chosen.Q ≤
      theorem4bSection7M2InX M q.chosen.Q ⊔ q.R
    exact le_sup_left
  have hRnormB : R ≤ Subgroup.normalizer (B : Set X) := by
    change q.R ≤ Subgroup.normalizer
      (theorem4bSection7M2InX M q.chosen.Q : Set X)
    exact theorem4b_section7_R_le_normalizer_M2 q
  have hHnormB : H ≤ Subgroup.normalizer (B : Set X) := by
    change (theorem4bSection7M2InX M q.chosen.Q ⊔ q.R) ≤
      Subgroup.normalizer
        (theorem4bSection7M2InX M q.chosen.Q : Set X)
    exact sup_le Subgroup.le_normalizer hRnormB
  let BH : Subgroup H := B.subgroupOf H
  letI : BH.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hBH).2
    exact hHnormB
  have hBsolv : Group.IsSolvable B := theorem4b_section7_M2_solvable M Q
  letI : Group.IsSolvable B := hBsolv
  have hBHsolv : Group.IsSolvable BH := by
    let eB : BH ≃* B := Subgroup.subgroupOfEquivOfLe hBH
    exact Group.isSolvable_of_isSolvable_injective (f := eB.toMonoidHom) eB.injective
  letI : Group.IsSolvable BH := hBHsolv
  have hRp : IsPGroup d.data.p R := by
    change IsPGroup d.data.p q.R
    exact theorem4bIsSylowSubgroupOf_isPGroup_final q.hRsylow
  haveI : (B.subgroupOf (B ⊔ R)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
    exact sup_le Subgroup.le_normalizer hRnormB
  have hquotP : IsPGroup d.data.p (H ⧸ BH) := by
    change IsPGroup d.data.p
      (↥(theorem4bSection7M2InX M q.chosen.Q ⊔ q.R) ⧸
        (theorem4bSection7M2InX M q.chosen.Q).subgroupOf
          (theorem4bSection7M2InX M q.chosen.Q ⊔ q.R))
    exact theorem4b_section7_quotient_sup_isPGroup
      (theorem4bSection7M2InX M q.chosen.Q) q.R hRp
  letI : Group.IsSolvable (H ⧸ BH) := by
    have hnil := hquotP.isNilpotent
    letI : Group.IsNilpotent (H ⧸ BH) := hnil
    infer_instance
  change Group.IsSolvable H
  exact isSolvable_of_normal_subgroup_and_quotient BH

/-- `Omega₁` commutes with transport along a group equivalence. -/
private theorem theorem4b_omega1_map_mulEquiv
    {G H : Type*} [Group G] [Group H] {p : ℕ} (e : G ≃* H) :
    (omega₁ (G := G) (p := p)).map e.toMonoidHom =
      omega₁ (G := H) (p := p) := by
  rw [omega₁, omega, MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [pow_one] using congrArg e.toMonoidHom hx
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    simpa [pow_one] using congrArg e.symm.toMonoidHom hy

/-- The Thompson subgroup commutes with transport along an ambient group
equivalence. -/
private theorem theorem4b_thompsonSubgroup_map_mulEquiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (P : Subgroup G) (e : G ≃* H) :
    (thompsonSubgroup (G := G) P).map e.toMonoidHom =
      thompsonSubgroup (G := H) (P.map e.toMonoidHom) := by
  classical
  let eP : P ≃* P.map e.toMonoidHom :=
    Subgroup.equivMapOfInjective P e.toMonoidHom e.injective
  have hcomp :
      ((P.map e.toMonoidHom).subtype).comp eP.toMonoidHom =
        e.toMonoidHom.comp P.subtype := by
    ext p
    rfl
  calc
    (thompsonSubgroup (G := G) P).map e.toMonoidHom =
        ((thompsonSubgroup (G := P) (⊤ : Subgroup P)).map P.subtype).map
          e.toMonoidHom := by rw [thompsonSubgroup_top_map_subtype]
    _ = (thompsonSubgroup (G := P) (⊤ : Subgroup P)).map
          (e.toMonoidHom.comp P.subtype) := by rw [Subgroup.map_map]
    _ = ((thompsonSubgroup (G := P) (⊤ : Subgroup P)).map
          eP.toMonoidHom).map (P.map e.toMonoidHom).subtype := by
            rw [Subgroup.map_map, hcomp]
    _ = (thompsonSubgroup (G := P.map e.toMonoidHom)
          (⊤ : Subgroup (P.map e.toMonoidHom))).map
          (P.map e.toMonoidHom).subtype := by
            rw [thompsonSubgroup_top_map_mulEquiv]
    _ = thompsonSubgroup (G := H) (P.map e.toMonoidHom) := by
          rw [thompsonSubgroup_top_map_subtype]

/-- The Thompson center commutes with transport along an ambient group
equivalence. -/
private theorem theorem4b_thompsonCenter_map_mulEquiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (P : Subgroup G) (e : G ≃* H) :
    (thompsonCenter (G := G) P).map e.toMonoidHom =
      thompsonCenter (G := H) (P.map e.toMonoidHom) := by
  calc
    (thompsonCenter (G := G) P).map e.toMonoidHom =
        (centerIn (G := G) (thompsonSubgroup (G := G) P)).map
          e.toMonoidHom := by rfl
    _ = centerIn (G := H)
        ((thompsonSubgroup (G := G) P).map e.toMonoidHom) := by
          exact centerIn_map_mulEquiv e (thompsonSubgroup (G := G) P)
    _ = thompsonCenter (G := H) (P.map e.toMonoidHom) := by
          rw [theorem4b_thompsonSubgroup_map_mulEquiv]
          rfl

/-- The Thompson subgroup of an intrinsic subgroup maps to the Thompson
subgroup of its ambient image. -/
private theorem theorem4b_thompsonSubgroup_map_subtype_eq
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) (P : Subgroup N) :
    (thompsonSubgroup (G := N) P).map N.subtype =
      thompsonSubgroup (G := G) (P.map N.subtype) := by
  classical
  let e : P ≃* P.map N.subtype :=
    Subgroup.equivMapOfInjective (f := N.subtype) P N.subtype_injective
  have hcomp :
      ((P.map N.subtype).subtype).comp e.toMonoidHom =
        N.subtype.comp P.subtype := by
    ext x
    rfl
  calc
    (thompsonSubgroup (G := N) P).map N.subtype =
        ((thompsonSubgroup (G := P) (⊤ : Subgroup P)).map P.subtype).map
          N.subtype := by rw [thompsonSubgroup_top_map_subtype]
    _ = (thompsonSubgroup (G := P) (⊤ : Subgroup P)).map
          (N.subtype.comp P.subtype) := by rw [Subgroup.map_map]
    _ = ((thompsonSubgroup (G := P) (⊤ : Subgroup P)).map
          e.toMonoidHom).map (P.map N.subtype).subtype := by
            rw [Subgroup.map_map, hcomp]
    _ = (thompsonSubgroup (G := P.map N.subtype)
          (⊤ : Subgroup (P.map N.subtype))).map
          (P.map N.subtype).subtype := by
            rw [thompsonSubgroup_top_map_mulEquiv]
    _ = thompsonSubgroup (G := G) (P.map N.subtype) := by
          rw [thompsonSubgroup_top_map_subtype]

/-- The intrinsic `Omega₁(Z(J(P)))` maps to the ambient subgroup attached to
the image of `P`. -/
private theorem theorem4b_corollary64Z_map_subtype
    {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    {p : Nat.Primes} (P : Subgroup H) (R : Subgroup X)
    (hPR : P.map H.subtype = R) :
    (corollary64Z p P).map H.subtype = corollary64Z p R := by
  let JH : Subgroup H := thompsonCenter (G := H) P
  let JX : Subgroup X := thompsonCenter (G := X) R
  have hJmap : JH.map H.subtype = JX := by
    calc
      JH.map H.subtype =
          (centerIn (G := H) (thompsonSubgroup (G := H) P)).map
            H.subtype := by rfl
      _ = centerIn (G := X)
          ((thompsonSubgroup (G := H) P).map H.subtype) := by
            exact centerIn_top_map_subtype H (thompsonSubgroup (G := H) P)
      _ = thompsonCenter (G := X) (P.map H.subtype) := by
            rw [theorem4b_thompsonSubgroup_map_subtype_eq]
            rfl
      _ = JX := by rw [hPR]
  let eJ0 : JH ≃* JH.map H.subtype :=
    Subgroup.equivMapOfInjective JH H.subtype H.subtype_injective
  let eJ : JH ≃* JX := eJ0.trans (MulEquiv.subgroupCongr hJmap)
  have hOmega :
      (omega₁ (G := JH) (p := p.val)).map eJ.toMonoidHom =
        omega₁ (G := JX) (p := p.val) :=
    theorem4b_omega1_map_mulEquiv eJ
  have hcomp :
      JX.subtype.comp eJ.toMonoidHom = H.subtype.comp JH.subtype := by
    ext x
    simp [eJ, eJ0, MulEquiv.subgroupCongr_apply]
  calc
    (corollary64Z p P).map H.subtype =
        ((omega₁ (G := JH) (p := p.val)).map JH.subtype).map
          H.subtype := by rfl
    _ = (omega₁ (G := JH) (p := p.val)).map
          (H.subtype.comp JH.subtype) := by rw [Subgroup.map_map]
    _ = ((omega₁ (G := JH) (p := p.val)).map eJ.toMonoidHom).map
          JX.subtype := by rw [Subgroup.map_map, hcomp]
    _ = (omega₁ (G := JX) (p := p.val)).map JX.subtype := by rw [hOmega]
    _ = corollary64Z p R := by rfl

/-- The Corollary 6.4 characteristic subgroup commutes with transport along
an ambient group equivalence. -/
private theorem theorem4b_corollary64Z_map_mulEquiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {p : Nat.Primes} (R : Subgroup G) (e : G ≃* H) :
    (corollary64Z p R).map e.toMonoidHom =
      corollary64Z p (R.map e.toMonoidHom) := by
  let JG : Subgroup G := thompsonCenter (G := G) R
  let JH : Subgroup H := thompsonCenter (G := H) (R.map e.toMonoidHom)
  have hJmap : JG.map e.toMonoidHom = JH := by
    simpa [JG, JH] using theorem4b_thompsonCenter_map_mulEquiv R e
  let eJ0 : JG ≃* JG.map e.toMonoidHom :=
    Subgroup.equivMapOfInjective JG e.toMonoidHom e.injective
  let eJ : JG ≃* JH := eJ0.trans (MulEquiv.subgroupCongr hJmap)
  have hOmega :
      (omega₁ (G := JG) (p := p.val)).map eJ.toMonoidHom =
        omega₁ (G := JH) (p := p.val) :=
    theorem4b_omega1_map_mulEquiv eJ
  have hcomp :
      JH.subtype.comp eJ.toMonoidHom =
        e.toMonoidHom.comp JG.subtype := by
    ext j
    change (((MulEquiv.subgroupCongr hJmap) (eJ0 j) : JH) : H) = e (j : G)
    calc
      (((MulEquiv.subgroupCongr hJmap) (eJ0 j) : JH) : H) =
          ((eJ0 j : JG.map e.toMonoidHom) : H) :=
        MulEquiv.subgroupCongr_apply hJmap (eJ0 j)
      _ = e (j : G) :=
        Subgroup.coe_equivMapOfInjective_apply JG e.toMonoidHom e.injective j
  calc
    (corollary64Z p R).map e.toMonoidHom =
        ((omega₁ (G := JG) (p := p.val)).map JG.subtype).map
          e.toMonoidHom := by rfl
    _ = (omega₁ (G := JG) (p := p.val)).map
          (e.toMonoidHom.comp JG.subtype) := by rw [Subgroup.map_map]
    _ = ((omega₁ (G := JG) (p := p.val)).map eJ.toMonoidHom).map
          JH.subtype := by rw [Subgroup.map_map, hcomp]
    _ = (omega₁ (G := JH) (p := p.val)).map JH.subtype := by rw [hOmega]
    _ = corollary64Z p (R.map e.toMonoidHom) := by rfl

/-- In particular, `Omega₁(Z(J(R)))` conjugates with `R`. -/
private theorem theorem4b_corollary64Z_conjBy
    {G : Type*} [Group G] [Finite G] {p : Nat.Primes}
    (R : Subgroup G) (x : G) :
    (corollary64Z p R).conjBy x = corollary64Z p (R.conjBy x) := by
  simpa [Subgroup.conjBy] using
    theorem4b_corollary64Z_map_mulEquiv R (MulAut.conj x)

/-- If an intrinsic subgroup maps onto an ambient subgroup, its normalizer is
the comap of the ambient normalizer. -/
private theorem theorem4b_normalizer_comap_of_map_subtype_eq
    {X : Type*} [Group X] (H : Subgroup X) (K : Subgroup H)
    (L : Subgroup X) (hKL : K.map H.subtype = L) :
    (Subgroup.normalizer (L : Set X)).comap H.subtype =
      Subgroup.normalizer (K : Set H) := by
  have hLrange : L ≤ H.subtype.range := by
    rw [← hKL]
    exact Subgroup.map_le_range H.subtype K
  calc
    (Subgroup.normalizer (L : Set X)).comap H.subtype =
        Subgroup.normalizer (L.comap H.subtype : Set H) :=
      Subgroup.comap_normalizer_eq_of_le_range hLrange
    _ = Subgroup.normalizer (K : Set H) := by
      rw [← hKL,
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective]

/-- Intersect a normal-factor factorization with an intermediate subgroup. -/
private theorem theorem4b_intersect_factorization
    {G : Type*} [Group G]
    {H B O N : Subgroup G}
    (hfactor : O ⊔ N = H) (hOnorm : O.Normal)
    (hOB : O ≤ B) (hBH : B ≤ H) :
    B = O ⊔ (B ⊓ N) := by
  letI : O.Normal := hOnorm
  apply le_antisymm
  · intro x hxB
    have hxSup : x ∈ O ⊔ N := by
      rw [hfactor]
      exact hBH hxB
    rcases Subgroup.mem_sup_of_normal_left.mp hxSup with
      ⟨o, ho, n, hn, hon⟩
    have hoB : o ∈ B := hOB ho
    have hnB : n ∈ B := by
      have hne : n = o⁻¹ * x := by
        rw [← hon]
        simp
      rw [hne]
      exact B.mul_mem (B.inv_mem hoB) hxB
    exact Subgroup.mem_sup_of_normal_left.mpr
      ⟨o, ho, n, ⟨hnB, hn⟩, hon⟩
  · exact sup_le hOB inf_le_left

/-- The maximal subgroup `Q` lies in the selected Sylow subgroup `R` of its
normalizer in `D`. -/
private theorem theorem4b_section7_Q_le_R
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {d : Theorem4bSixD M} {s : Theorem4bSection7SecondStage d}
    (q : Theorem4bSection7MaximalQData d s) :
    q.chosen.Q ≤ q.R := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let Q : Subgroup X := q.chosen.Q
  let D : Subgroup X := theorem4bSection7D M s.beta
  let NDQ : Subgroup X := theorem4bSection7NormalizerInD M s.beta Q
  let R : Subgroup X := q.R
  have hQD : Q ≤ D := q.chosen.hQE.trans inf_le_left
  have hQNDQ : Q ≤ NDQ := le_inf hQD Subgroup.le_normalizer
  have hNDQnormQ : NDQ ≤ Subgroup.normalizer (Q : Set X) := inf_le_right
  let QN : Subgroup NDQ := Q.subgroupOf NDQ
  letI : QN.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQNDQ).2
    exact hNDQnormQ
  have hQNp : IsPGroup d.data.p QN :=
    q.chosen.hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQNDQ).symm
  rcases q.hRsylow with ⟨RN, hReq⟩
  change Sylow d.data.p NDQ at RN
  change q.R = (RN : Subgroup NDQ).map NDQ.subtype at hReq
  have hsupP : IsPGroup d.data.p
      (↥((RN : Subgroup NDQ) ⊔ QN)) :=
    IsPGroup.to_sup_of_normal_right RN.isPGroup' hQNp
  have hsupEq : (RN : Subgroup NDQ) ⊔ QN = (RN : Subgroup NDQ) :=
    RN.is_maximal' hsupP le_sup_left
  have hQNleRN : QN ≤ RN := by
    calc
      QN ≤ (RN : Subgroup NDQ) ⊔ QN := le_sup_right
      _ = (RN : Subgroup NDQ) := hsupEq
  change Q ≤ q.R
  rw [hReq]
  intro x hxQ
  let xN : NDQ := ⟨x, hQNDQ hxQ⟩
  apply Subgroup.mem_map.mpr
  refine ⟨xN, ?_, rfl⟩
  exact hQNleRN hxQ

/-- The `p`-core of `M̂₂` is nontrivial because it contains the selected
nontrivial normal `p`-subgroup `Q`. -/
private theorem theorem4b_section7_pCore_M2Hat_ne_bot
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {d : Theorem4bSixD M} {s : Theorem4bSection7SecondStage d}
    (q : Theorem4bSection7MaximalQData d s) :
    pCore d.data.p (theorem4bSection7M2Hat q) ≠ ⊥ := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let Q : Subgroup X := q.chosen.Q
  have hQeq : Q = q.chosen.Q := rfl
  cases hQeq
  let N : Subgroup X := Subgroup.normalizer (Q : Set X)
  let N0 : Subgroup X := theorem4bSection7NCore Q
  let B : Subgroup X := theorem4bSection7M2InX M Q
  let R : Subgroup X := q.R
  let H : Subgroup X := theorem4bSection7M2Hat q
  have hQR : Q ≤ R := by
    exact theorem4b_section7_Q_le_R q
  have hRH : R ≤ H := by
    change q.R ≤ theorem4bSection7M2InX M q.chosen.Q ⊔
      theorem4bSection7R q
    rw [show theorem4bSection7R q = q.R by rfl]
    exact le_sup_right
  have hQH : Q ≤ H := hQR.trans hRH
  have hN0N : N0 ≤ N := by
    dsimp [N0, N, theorem4bSection7NCore]
    exact Subgroup.map_subtype_le _
  have hBN0 : B ≤ N0 :=
    (theorem4b_section7_M2_le_M1InX M Q).trans
      (Subgroup.map_subtype_le _)
  have hBN : B ≤ N := hBN0.trans hN0N
  have hRN : R ≤ N := by
    rcases q.hRsylow with ⟨RN, hReq⟩
    have hRNDQ : q.R ≤ theorem4bSection7NormalizerInD M s.beta q.chosen.Q := by
      rw [hReq]
      exact Subgroup.map_subtype_le _
    change q.R ≤ N
    exact hRNDQ.trans inf_le_right
  have hHN : H ≤ N := by
    change (B ⊔ q.R) ≤ N
    exact sup_le hBN hRN
  let QH : Subgroup H := Q.subgroupOf H
  letI : QH.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).2
    exact hHN
  have hQHp : IsPGroup d.data.p QH :=
    q.chosen.hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hQHne : QH ≠ ⊥ := by
    intro hbot
    apply q.chosen.hQne
    change Q = ⊥
    change Q.subgroupOf H = ⊥ at hbot
    rw [← Subgroup.map_subgroupOf_eq_of_le hQH, hbot, Subgroup.map_bot]
  have hQHcore : QH ≤ pCore d.data.p H := le_sSup ⟨inferInstance, hQHp⟩
  intro hcore
  apply hQHne
  rw [hcore] at hQHcore
  exact bot_unique hQHcore

/-- Conditional ZJ factorization for `M̂₂`.  The only unproved source
input retained here is the `[IG; 25.4]` p-stability assertion. -/
public theorem IsStronglyEmbedded.theorem4b_section7_M2Hat_factorization_of_pStable
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s)
    (hstable : PStableGroup'
      (G := theorem4bSection7M2Hat q) d.data.p) :
    let H : Subgroup X := theorem4bSection7M2Hat q
    pPrimeCore d.data.p H ⊔
        (Subgroup.normalizer (theorem4bSection7Z q : Set X)).comap
          H.subtype =
      ⊤ := by
  classical
  dsimp only
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let H : Subgroup X := theorem4bSection7M2Hat q
  let R : Subgroup X := q.R
  obtain ⟨P, hRP⟩ :=
    hM.theorem4b_section7_R_isSylow_M2Hat
      hX d hrank hT2 hinduction s q
  have hsolv : Group.IsSolvable H := by
    simpa [H] using theorem4b_section7_M2Hat_solvable q
  have hconstrained : PConstrainedGroup (G := H) d.data.p :=
    theorem4b_pConstrainedGroup_of_solvable hsolv d.data.p
  have hcoreNe : pCore d.data.p H ≠ ⊥ := by
    simpa [H] using theorem4b_section7_pCore_M2Hat_ne_bot q
  have hpodd : d.data.p ≠ 2 := by
    intro hp
    have htwoOdd : Odd 2 := hp ▸ d.data.hpOdd
    exact htwoOdd.not_two_dvd_nat (dvd_refl 2)
  have hfactor :
      pPrimeCore d.data.p H ⊔
          Subgroup.normalizer
            (corollary64Z ⟨d.data.p, d.data.hp⟩
              (P : Subgroup H) : Set H) =
        ⊤ := by
    apply theorem4b_zj_factorization_of_constrained_stable
      d.data.hp hpodd hcoreNe hconstrained hstable P
  have hPmap : (P : Subgroup H).map H.subtype = R := by
    change (P : Subgroup H).map H.subtype = q.R
    have hRP' := hRP
    rw [show theorem4bSection7R q = q.R by rfl] at hRP'
    exact hRP'.symm
  have hZmap :
      (corollary64Z ⟨d.data.p, d.data.hp⟩ (P : Subgroup H)).map
          H.subtype = theorem4bSection7Z q := by
    change (corollary64Z ⟨d.data.p, d.data.hp⟩ (P : Subgroup H)).map
          H.subtype = corollary64Z ⟨d.data.p, d.data.hp⟩ q.R
    exact theorem4b_corollary64Z_map_subtype
      (p := ⟨d.data.p, d.data.hp⟩) (P : Subgroup H) q.R hPmap
  have hnorm :
      (Subgroup.normalizer (theorem4bSection7Z q : Set X)).comap
          H.subtype =
        Subgroup.normalizer
          (corollary64Z ⟨d.data.p, d.data.hp⟩
            (P : Subgroup H) : Set H) :=
    theorem4b_normalizer_comap_of_map_subtype_eq H
      (corollary64Z ⟨d.data.p, d.data.hp⟩ (P : Subgroup H))
      (theorem4bSection7Z q) hZmap
  change pPrimeCore d.data.p H ⊔
      (Subgroup.normalizer (theorem4bSection7Z q : Set X)).comap
        H.subtype = ⊤
  rw [hnorm]
  exact hfactor

/-- Lemma 7.11, conditional only on the source's `[IG; 25.4]` p-stability
input: `M₂ = theta(M₂) N_{M₂}(Z)`. -/
public theorem IsStronglyEmbedded.theorem4b_lemma711_of_pStable
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s)
    (hstable : PStableGroup'
      (G := theorem4bSection7M2Hat q) d.data.p) :
    theorem4bSection7M2InX M q.chosen.Q =
      corollary64Theta d.data.p
        (theorem4bSection7M2InX M q.chosen.Q) ⊔
        (theorem4bSection7M2InX M q.chosen.Q ⊓
          Subgroup.normalizer (theorem4bSection7Z q : Set X)) := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let H : Subgroup X := theorem4bSection7M2Hat q
  let B : Subgroup X := theorem4bSection7M2InX M q.chosen.Q
  let O : Subgroup H := pPrimeCore d.data.p H
  let N : Subgroup H :=
    (Subgroup.normalizer (theorem4bSection7Z q : Set X)).comap H.subtype
  have hfac : O ⊔ N = ⊤ := by
    simpa [O, N, H] using
      hM.theorem4b_section7_M2Hat_factorization_of_pStable
        hX d hrank hT2 hinduction s q hstable
  have hBH : B ≤ H := by
    simpa [B, H, theorem4bSection7M2Hat] using
      (le_sup_left : theorem4bSection7M2InX M q.chosen.Q ≤
        theorem4bSection7M2InX M q.chosen.Q ⊔ theorem4bSection7R q)
  have hcoreEq : O.map H.subtype =
      (pPrimeCore d.data.p B).map B.subtype := by
    simpa [O, H, B] using
      theorem4b_section7_pPrimeCore_M2Hat_eq_M2 d s q
  have hOB : O ≤ B.subgroupOf H := by
    intro x hx
    change (x : X) ∈ B
    have hxO : (x : X) ∈ O.map H.subtype :=
      Subgroup.mem_map_of_mem H.subtype hx
    rw [hcoreEq] at hxO
    rcases Subgroup.mem_map.mp hxO with ⟨y, hy, hxy⟩
    exact hxy ▸ y.property
  have hinter : B.subgroupOf H = O ⊔ (B.subgroupOf H ⊓ N) := by
    apply theorem4b_intersect_factorization hfac
    · infer_instance
    · exact hOB
    · exact le_top
  have hmapN : N.map H.subtype =
      H ⊓ Subgroup.normalizer (theorem4bSection7Z q : Set X) := by
    change ((Subgroup.normalizer (theorem4bSection7Z q : Set X)).comap
      H.subtype).map H.subtype =
        H ⊓ Subgroup.normalizer (theorem4bSection7Z q : Set X)
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
  have hmap : B = O.map H.subtype ⊔
      (B.subgroupOf H ⊓ N).map H.subtype := by
    calc
      B = (B.subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hBH).symm
      _ = (O ⊔ (B.subgroupOf H ⊓ N)).map H.subtype :=
        congrArg (Subgroup.map H.subtype) hinter
      _ = O.map H.subtype ⊔
          (B.subgroupOf H ⊓ N).map H.subtype := by rw [Subgroup.map_sup]
  have hmapInf : (B.subgroupOf H ⊓ N).map H.subtype =
      B ⊓ (H ⊓ Subgroup.normalizer (theorem4bSection7Z q : Set X)) := by
    calc
      (B.subgroupOf H ⊓ N).map H.subtype =
          (B.subgroupOf H).map H.subtype ⊓ N.map H.subtype :=
        Subgroup.map_inf _ _ H.subtype H.subtype_injective
      _ = B ⊓ (H ⊓
          Subgroup.normalizer (theorem4bSection7Z q : Set X)) := by
        rw [Subgroup.map_subgroupOf_eq_of_le hBH, hmapN]
  have htheta : (pPrimeCore d.data.p B).map B.subtype =
      corollary64Theta d.data.p B := by
    simpa [B] using hM.theorem4b_section7_pPrimeCore_M2_eq_theta
      hX d hrank hT2 hinduction s q
  change B = corollary64Theta d.data.p B ⊔
    (B ⊓ Subgroup.normalizer (theorem4bSection7Z q : Set X))
  calc
    B = O.map H.subtype ⊔
        (B.subgroupOf H ⊓ N).map H.subtype := hmap
    _ = (pPrimeCore d.data.p B).map B.subtype ⊔
        (B ⊓ (H ⊓
          Subgroup.normalizer (theorem4bSection7Z q : Set X))) := by
      rw [hcoreEq, hmapInf]
    _ = corollary64Theta d.data.p B ⊔
        (B ⊓ Subgroup.normalizer (theorem4bSection7Z q : Set X)) := by
      rw [htheta, ← inf_assoc, inf_eq_left.mpr hBH]

/-- Lemma 7.11: `M₂ = theta(M₂) N_{M₂}(Z)`. -/
public theorem IsStronglyEmbedded.theorem4b_lemma711
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    theorem4bSection7M2InX M q.chosen.Q =
      corollary64Theta d.data.p
        (theorem4bSection7M2InX M q.chosen.Q) ⊔
        (theorem4bSection7M2InX M q.chosen.Q ⊓
          Subgroup.normalizer (theorem4bSection7Z q : Set X)) := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let H : Subgroup X := theorem4bSection7M2Hat q
  have hstable : PStableGroup' (G := H) d.data.p :=
    pStableGroup'_of_solvable_abelianSylowTwo
      (theorem4b_section7_M2Hat_solvable q)
      (theorem4b_section7_M2Hat_hasAbelianSylow hM q)
      d.data.hpOdd
  exact hM.theorem4b_lemma711_of_pStable
    hX d hrank hT2 hinduction s q (by simpa [H] using hstable)

/-! ## The final post-Lemma-7.11 Sylow conjugacy -/

/-- If `B = T N`, where `T` is an odd-order normal subgroup of `B`, then
`N` and `B` have the same 2-part. -/
private theorem factorization_two_subgroupOf_eq_of_eq_sup_odd_normal
    {G : Type*} [Group G] [Finite G]
    {B T N : Subgroup G}
    (hTB : T ≤ B) (hNB : N ≤ B)
    (hBnormT : B ≤ Subgroup.normalizer (T : Set G))
    (hTodd : Odd (Nat.card T)) (hsup : B = T ⊔ N) :
    (Nat.card (N.subgroupOf B)).factorization 2 =
      (Nat.card B).factorization 2 := by
  classical
  let TB : Subgroup B := T.subgroupOf B
  let NB : Subgroup B := N.subgroupOf B
  haveI : TB.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hTB).2
    exact hBnormT
  have hsupB : TB ⊔ NB = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hTB,
      Subgroup.map_subgroupOf_eq_of_le hNB,
      ← hsup]
    rw [← MonoidHom.range_eq_map]
    exact (Subgroup.range_subtype (H := B)).symm
  let qB : B →* B ⧸ TB := QuotientGroup.mk' TB
  let f : NB →* B ⧸ TB := qB.comp NB.subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective TB y
    have hb : b ∈ TB ⊔ NB := by rw [hsupB]; trivial
    rcases Subgroup.mem_sup_of_normal_left.mp hb with ⟨t, ht, n, hn, htn⟩
    let nn : NB := ⟨n, hn⟩
    refine ⟨nn, ?_⟩
    change qB n = qB b
    have hqt : qB t = 1 := (QuotientGroup.eq_one_iff t).2 ht
    rw [← htn, map_mul, hqt, one_mul]
  have hkerMapLe : f.ker.map NB.subtype ≤ TB := by
    intro b hb
    rcases Subgroup.mem_map.mp hb with ⟨n, hn, rfl⟩
    change qB n = 1 at hn
    exact (QuotientGroup.eq_one_iff (N := TB) (x := (n : B))).1 hn
  have hkerCardDvd : Nat.card f.ker ∣ Nat.card T := by
    have hmapCard : Nat.card (f.ker.map NB.subtype) = Nat.card f.ker :=
      Subgroup.card_map_of_injective NB.subtype_injective
    have hdiv : Nat.card (f.ker.map NB.subtype) ∣ Nat.card TB :=
      Subgroup.card_dvd_of_le hkerMapLe
    rw [show Nat.card TB = Nat.card T by
      simpa [TB] using natCard_subgroupOf_eq T B hTB, hmapCard] at hdiv
    exact hdiv
  have hkerOdd : Odd (Nat.card f.ker) := hTodd.of_dvd_nat hkerCardDvd
  have hquotCard : Nat.card (NB ⧸ f.ker) = Nat.card (B ⧸ TB) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have hBcard := Subgroup.card_eq_card_quotient_mul_card_subgroup TB
  have hNBcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  calc
    (Nat.card NB).factorization 2 =
        (Nat.card (NB ⧸ f.ker) * Nat.card f.ker).factorization 2 := by
      rw [hNBcard]
    _ = (Nat.card (NB ⧸ f.ker)).factorization 2 := by
      rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne')]
      simp only [Finsupp.add_apply]
      rw [Nat.factorization_eq_zero_of_not_dvd hkerOdd.not_two_dvd_nat]
      simp
    _ = (Nat.card (B ⧸ TB)).factorization 2 := by rw [hquotCard]
    _ = (Nat.card (B ⧸ TB) * Nat.card TB).factorization 2 := by
      rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne')]
      simp only [Finsupp.add_apply]
      rw [show (Nat.card TB).factorization 2 = 0 by
        apply Nat.factorization_eq_zero_of_not_dvd
        have hTBodd : Odd (Nat.card TB) := by
          simpa [TB, natCard_subgroupOf_eq T B hTB] using hTodd
        exact hTBodd.not_two_dvd_nat]
      simp
    _ = (Nat.card B).factorization 2 := by rw [hBcard]

/-- If an involution lies in `B = T (B ∩ N_G(K))`, with `T` normal of odd
order, an element of `T` conjugates `K` to a subgroup normalized by that
involution. -/
private theorem theorem4b_exists_conjugate_normalized_of_eq_sup_odd_normal
    {G : Type*} [Group G] [Finite G]
    {B T K : Subgroup G} {z : G}
    (hTB : T ≤ B)
    (hBnormT : B ≤ Subgroup.normalizer (T : Set G))
    (hTodd : Odd (Nat.card T))
    (hsup : B = T ⊔ (B ⊓ Subgroup.normalizer (K : Set G)))
    (hzB : z ∈ B) (hz : IsInvolution z) :
    ∃ x : G, x ∈ T ∧
      z ∈ Subgroup.normalizer (K.conjBy x : Set G) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := B ⊓ Subgroup.normalizer (K : Set G)
  have hNB : N ≤ B := inf_le_left
  let TB : Subgroup B := T.subgroupOf B
  let NB : Subgroup B := N.subgroupOf B
  haveI : TB.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hTB).2
    exact hBnormT
  have hsupB : TB ⊔ NB = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hTB,
      Subgroup.map_subgroupOf_eq_of_le hNB,
      ← hsup]
    rw [← MonoidHom.range_eq_map]
    exact (Subgroup.range_subtype (H := B)).symm
  have hfac : (Nat.card NB).factorization 2 =
      (Nat.card B).factorization 2 := by
    exact factorization_two_subgroupOf_eq_of_eq_sup_odd_normal
      hTB hNB hBnormT hTodd (by simpa [N] using hsup)
  let SN : Sylow 2 NB := Classical.choice inferInstance
  let SB0 : Subgroup B := (SN : Subgroup NB).map NB.subtype
  have hSB0card : Nat.card SB0 =
      2 ^ (Nat.card B).factorization 2 := by
    rw [show Nat.card SB0 = Nat.card (SN : Subgroup NB) by
      exact Subgroup.card_map_of_injective NB.subtype_injective,
      SN.card_eq_multiplicity, hfac]
  let SB : Sylow 2 B := Sylow.ofCard SB0 hSB0card
  let zB : B := ⟨z, hzB⟩
  have hzBI : IsInvolution zB := IsInvolution.subtype hz hzB
  have hzP : IsPGroup 2 (Subgroup.zpowers zB) := by
    have horder : orderOf zB = 2 :=
      (orderOf_eq_prime_iff).2 ⟨hzBI.sq_eq_one, hzBI.ne_one⟩
    apply IsPGroup.of_card (p := 2) (G := Subgroup.zpowers zB) (n := 1)
    simp [Nat.card_zpowers, horder]
  obtain ⟨Pz, hzlePz⟩ := IsPGroup.exists_le_sylow hzP
  have hzPz : zB ∈ (Pz : Subgroup B) :=
    hzlePz (Subgroup.mem_zpowers zB)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq B SB Pz
  have hPzConj : (Pz : Subgroup B) = (SB : Subgroup B).conjBy g := by
    rw [← hg]
    simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      Subgroup.conjBy]
    congr 1
  have hgSup : g ∈ TB ⊔ NB := by
    rw [hsupB]
    trivial
  rcases Subgroup.mem_sup_of_normal_left.mp hgSup with
    ⟨t, htT, n, hnN, htn⟩
  have hzConj : zB ∈ (SB : Subgroup B).conjBy g := by
    rw [← hPzConj]
    exact hzPz
  rw [Subgroup.conjBy, Subgroup.mem_map] at hzConj
  rcases hzConj with ⟨s0, hs0, hsEq⟩
  have hSBleNB : (SB : Subgroup B) ≤ NB := by
    change SB0 ≤ NB
    exact Subgroup.map_subtype_le _
  have hsN : (s0 : G) ∈ N := hSBleNB hs0
  have hnNG : (n : G) ∈ N := hnN
  have hyN : (n : G) * (s0 : G) * (n : G)⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem hnNG hsN) (N.inv_mem hnNG)
  have hzNconj : z ∈ N.conjBy (t : G) := by
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨(n : G) * (s0 : G) * (n : G)⁻¹, hyN, ?_⟩
    change (t : G) * ((n : G) * (s0 : G) * (n : G)⁻¹) * (t : G)⁻¹ = z
    calc
      _ = ((t * n : B) : G) * (s0 : G) * ((t * n : B) : G)⁻¹ := by
        change (t : G) * ((n : G) * (s0 : G) * (n : G)⁻¹) * (t : G)⁻¹ =
          ((t : G) * (n : G)) * (s0 : G) * (((t : G) * (n : G))⁻¹)
        group
      _ = (g : G) * (s0 : G) * (g : G)⁻¹ := by rw [htn]
      _ = z := congrArg Subtype.val hsEq
  refine ⟨(t : G), ?_, ?_⟩
  · exact htT
  · exact (section11_conjBy_le_normalizer_conjBy_of_le_normalizer
      (H := N) (K := K) inf_le_right (t : G)) hzNconj

/-- An odd-order subgroup maps trivially to a 2-group quotient. -/
private theorem odd_subgroup_le_of_quotient_isPGroup_two
    {G : Type*} [Group G] [Finite G] {T O B : Subgroup G}
    [(O.subgroupOf B).Normal]
    (hTB : T ≤ B)
    (hTodd : Odd (Nat.card T))
    (hquot2 : IsPGroup 2 (B ⧸ O.subgroupOf B)) :
    T ≤ O := by
  classical
  let OB : Subgroup B := O.subgroupOf B
  letI : OB.Normal := by
    change (O.subgroupOf B).Normal
    infer_instance
  let TB : Subgroup B := T.subgroupOf B
  let qB : B →* B ⧸ OB := QuotientGroup.mk' OB
  let Tbar : Subgroup (B ⧸ OB) := TB.map qB
  have hTbar2 : IsPGroup 2 Tbar := hquot2.to_subgroup Tbar
  have hTbarOdd : Odd (Nat.card Tbar) := by
    apply hTodd.of_dvd_nat
    have hdiv : Nat.card Tbar ∣ Nat.card TB :=
      Subgroup.card_map_dvd (H := TB) qB
    simpa [TB, natCard_subgroupOf_eq T B hTB] using hdiv
  have hTbarCard : Nat.card Tbar = 1 := by
    rcases hTbar2.card_eq_or_dvd with hcard | hdiv
    · exact hcard
    · exact False.elim (hTbarOdd.not_two_dvd_nat hdiv)
  have hTbarBot : Tbar = ⊥ := Subgroup.card_eq_one.mp hTbarCard
  intro t ht
  let tB : B := ⟨t, hTB ht⟩
  have htbar : qB tB ∈ Tbar :=
    Subgroup.mem_map_of_mem qB (show tB ∈ TB from ht)
  have htone : qB tB = 1 := by simpa [hTbarBot] using htbar
  exact (QuotientGroup.eq_one_iff (N := OB) (x := tB)).1 htone

/-- The first sentence after Lemma 7.11: an element of `theta(M₂)`
conjugates `Z` to a subgroup normalized by the distinguished involution. -/
private theorem IsStronglyEmbedded.theorem4b_section7_exists_theta_conjugate_normalized
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    ∃ x : X,
      x ∈ corollary64Theta d.data.p
        (theorem4bSection7M2InX M q.chosen.Q) ∧
      d.data.z ∈ Subgroup.normalizer
        ((theorem4bSection7Z q).conjBy x : Set X) := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let B : Subgroup X := theorem4bSection7M2InX M q.chosen.Q
  let T : Subgroup X := corollary64Theta d.data.p B
  let Z : Subgroup X := theorem4bSection7Z q
  have hTB : T ≤ B := by
    change (pPrimeCore d.data.p (corollary64OddCore B)).map
        (corollary64OddCore B).subtype ≤ B
    exact (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  have hBnormT : B ≤ Subgroup.normalizer (T : Set X) := by
    simpa [T] using theorem4b_section7_theta_le_normalizer
      (p := d.data.p) B
  have hTodd : Odd (Nat.card T) := by
    simpa [T] using lemma75_theta_odd_card d.data.p B
  have hsup : B = T ⊔ (B ⊓ Subgroup.normalizer (Z : Set X)) := by
    simpa [B, T, Z] using
      hM.theorem4b_lemma711 hX d hrank hT2 hinduction s q
  have hzB : d.data.z ∈ B := by
    simpa [B] using hM.theorem4b_section7_z_mem_M2
      hX d hrank hT2 hinduction s q
  simpa [B, T, Z] using
    theorem4b_exists_conjugate_normalized_of_eq_sup_odd_normal
      hTB hBnormT hTodd hsup hzB d.data.hz

/-- Equations `(7E--7F)` put `theta(M₂)` inside the ambient copy of
`O₂'(N°)`: the quotient of `M₂` by that odd core is a 2-group, whereas
`theta(M₂)` has odd order. -/
private theorem IsStronglyEmbedded.theorem4b_section7_theta_M2_le_oddCore
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    corollary64Theta d.data.p
        (theorem4bSection7M2InX M q.chosen.Q) ≤
      (twoPrimeCore (theorem4bSection7NCore q.chosen.Q)).map
        (theorem4bSection7NCore q.chosen.Q).subtype := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup X := q.chosen.Q
  let N0 : Subgroup X := theorem4bSection7NCore Q
  let A : Subgroup N0 := theorem4bSection7M1 M Q
  let O1 : Subgroup A := theorem4bSection7O1 M Q
  let B0 : Subgroup A := theorem4bSection7M2 M Q
  let U : Subgroup (A ⧸ O1) := theorem4bSection7M2Quotient M Q
  let OX : Subgroup X := (twoPrimeCore N0).map N0.subtype
  let B : Subgroup X := theorem4bSection7M2InX M Q
  let T : Subgroup X := corollary64Theta d.data.p B
  have hOXB : OX ≤ B := by
    simpa [OX, B, N0, Q] using
      hM.theorem4b_section7_oddCore_le_M2
        hX d hrank hT2 hinduction s q
  have hBleN0 : B ≤ N0 := by
    change ((B0.map A.subtype).map N0.subtype : Subgroup X) ≤ N0
    exact Subgroup.map_subtype_le _
  haveI : (twoPrimeCore N0).Characteristic := by
    simpa [twoPrimeCore] using
      (pPrimeCore_characteristic (p := 2) (G := N0))
  have hNormN0normOX : Subgroup.normalizer (N0 : Set X) ≤
      Subgroup.normalizer (OX : Set X) := by
    simpa [OX] using
      (External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
        N0 (twoPrimeCore N0))
  have hN0normOX : N0 ≤ Subgroup.normalizer (OX : Set X) :=
    Subgroup.le_normalizer.trans hNormN0normOX
  have hBnormOX : B ≤ Subgroup.normalizer (OX : Set X) :=
    hBleN0.trans hN0normOX
  letI : (OX.subgroupOf B).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hOXB).2
    exact hBnormOX
  have hO1B0 : O1 ≤ B0 := by
    intro a ha
    change QuotientGroup.mk' O1 a ∈ U
    have haOne : QuotientGroup.mk' O1 a = 1 :=
      (QuotientGroup.eq_one_iff (N := O1) (x := a)).2 ha
    rw [haOne]
    exact U.one_mem
  letI : (O1.subgroupOf B0).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hO1B0).2
    rw [Subgroup.normalizer_eq_top_iff.mpr
      (inferInstance : O1.Normal)]
    exact le_top
  let P2 : Subgroup (A ⧸ O1) := pCore 2 (A ⧸ O1)
  have hOmega2 : IsPGroup 2 (omega₁ (G := P2) (p := 2)) :=
    pCore_isPGroup.to_subgroup (omega₁ (G := P2) (p := 2))
  have hU2 : IsPGroup 2 U := by
    change IsPGroup 2 ((omega₁ (G := P2) (p := 2)).map P2.subtype)
    exact hOmega2.map P2.subtype
  let qA : A →* A ⧸ O1 := QuotientGroup.mk' O1
  have hB0map : B0.map qA = U := by
    simpa [B0, qA, U, A, O1] using theorem4b_section7_sevenF M Q
  let eQuot : B0 ⧸ O1.subgroupOf B0 ≃* B0.map qA :=
    quotientSubgroupRangeEquiv B0 O1
  have hRange2 : IsPGroup 2 (B0.map qA) := by
    rw [hB0map]
    exact hU2
  have hInternalQuot2 : IsPGroup 2 (B0 ⧸ O1.subgroupOf B0) :=
    hRange2.of_equiv eQuot.symm
  have hOeq : ((O1.map A.subtype).map N0.subtype : Subgroup X) = OX := by
    simpa [Q, N0, A, O1, OX] using
      hM.theorem4b_section7_O1InX_eq_oddCore
        hX d hrank hT2 hinduction s q
  have hcardB : Nat.card B = Nat.card B0 := by
    change Nat.card ((B0.map A.subtype).map N0.subtype) = Nat.card B0
    rw [Subgroup.card_map_of_injective N0.subtype_injective,
      Subgroup.card_map_of_injective A.subtype_injective]
  have hcardOX : Nat.card OX = Nat.card O1 := by
    rw [← hOeq,
      Subgroup.card_map_of_injective N0.subtype_injective,
      Subgroup.card_map_of_injective A.subtype_injective]
  have hcardOXsub : Nat.card (OX.subgroupOf B) = Nat.card O1 :=
    (natCard_subgroupOf_eq OX B hOXB).trans hcardOX
  have hcardO1sub : Nat.card (O1.subgroupOf B0) = Nat.card O1 :=
    natCard_subgroupOf_eq O1 B0 hO1B0
  have hquotCard : Nat.card (B ⧸ OX.subgroupOf B) =
      Nat.card (B0 ⧸ O1.subgroupOf B0) := by
    apply Nat.mul_right_cancel (Nat.card_pos (α := O1))
    calc
      Nat.card (B ⧸ OX.subgroupOf B) * Nat.card O1 =
          Nat.card (B ⧸ OX.subgroupOf B) *
            Nat.card (OX.subgroupOf B) := by rw [hcardOXsub]
      _ = Nat.card B :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup
          (s := OX.subgroupOf B)).symm
      _ = Nat.card B0 := hcardB
      _ = Nat.card (B0 ⧸ O1.subgroupOf B0) *
          Nat.card (O1.subgroupOf B0) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup
          (s := O1.subgroupOf B0)
      _ = Nat.card (B0 ⧸ O1.subgroupOf B0) * Nat.card O1 := by
        rw [hcardO1sub]
  have hAmbientQuot2 : IsPGroup 2 (B ⧸ OX.subgroupOf B) := by
    rcases IsPGroup.iff_card.mp hInternalQuot2 with ⟨n, hn⟩
    apply IsPGroup.iff_card.mpr
    refine ⟨n, ?_⟩
    rw [hquotCard, hn]
  have hTB : T ≤ B := by
    change (pPrimeCore d.data.p (corollary64OddCore B)).map
        (corollary64OddCore B).subtype ≤ B
    exact (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  have hTodd : Odd (Nat.card T) := by
    simpa [T] using lemma75_theta_odd_card d.data.p B
  exact odd_subgroup_le_of_quotient_isPGroup_two
    (T := T) (O := OX) (B := B) hTB hTodd hAmbientQuot2

/-- Conjugating by the element supplied after Lemma 7.11 produces another
admissible subgroup: `Z^x`, together with `t^x` and `P₁^x`, satisfies the
source conditions `(a,b)`. -/
private theorem IsStronglyEmbedded.theorem4b_section7_conjugated_admissibleQ
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    ∃ x : X,
      x ∈ corollary64Theta d.data.p
        (theorem4bSection7M2InX M q.chosen.Q) ∧
      x ∈ theorem4bSection7E M d.data.z s.beta ∧
      d.data.z ∈ Subgroup.normalizer
        ((theorem4bSection7Z q).conjBy x : Set X) ∧
      ∃ a : Theorem4bSection7AdmissibleQ d s,
        a.Q = (theorem4bSection7Z q).conjBy x ∧
        a.P₁ = q.chosen.P₁.conjBy x ∧
        a.t = (MulAut.conj x) q.chosen.t := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let B : Subgroup X := theorem4bSection7M2InX M q.chosen.Q
  let T : Subgroup X := corollary64Theta d.data.p B
  let D : Subgroup X := theorem4bSection7D M s.beta
  let E : Subgroup X := theorem4bSection7E M d.data.z s.beta
  let R : Subgroup X := q.R
  let Z : Subgroup X := theorem4bSection7Z q
  obtain ⟨x, hxT, hzNormZx⟩ :=
    hM.theorem4b_section7_exists_theta_conjugate_normalized
      hX d hrank hT2 hinduction s q
  have hxOX : x ∈
      (twoPrimeCore (theorem4bSection7NCore q.chosen.Q)).map
        (theorem4bSection7NCore q.chosen.Q).subtype := by
    exact hM.theorem4b_section7_theta_M2_le_oddCore
      hX d hrank hT2 hinduction s q hxT
  have hOXE :
      (twoPrimeCore (theorem4bSection7NCore q.chosen.Q)).map
          (theorem4bSection7NCore q.chosen.Q).subtype ≤ E := by
    simpa [E] using hM.theorem4b_section7_sevenE
      hX d hrank hT2 hinduction s q
  have hxE : x ∈ E := hOXE hxOX
  have hED : E ≤ D := inf_le_left
  have hxD : x ∈ D := hED hxE
  have hxM : x ∈ M := (inf_le_left : D ≤ M) hxD
  have hxBeta : x • s.beta = s.beta :=
    MulAction.mem_stabilizer_iff.mp ((inf_le_right : D ≤
      MulAction.stabilizer X s.beta) hxD)
  let alpha : conjugateCosetSpace M := theorem4bSection7Base
  have hxAlpha : x • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    simpa [alpha, theorem4bSection7Base, baseCoset_stabilizer] using hxM
  have hxInvAlpha : x⁻¹ • alpha = alpha := by
    calc
      x⁻¹ • alpha = x⁻¹ • (x • alpha) :=
        (congrArg (fun y => x⁻¹ • y) hxAlpha).symm
      _ = alpha := inv_smul_smul x alpha
  have hxInvBeta : x⁻¹ • s.beta = s.beta := by
    calc
      x⁻¹ • s.beta = x⁻¹ • (x • s.beta) :=
        (congrArg (fun y => x⁻¹ • y) hxBeta).symm
      _ = s.beta := inv_smul_smul x s.beta
  have hRp : IsPGroup d.data.p R := by
    change IsPGroup d.data.p q.R
    exact theorem4bIsSylowSubgroupOf_isPGroup_final q.hRsylow
  have hRne : R ≠ ⊥ := by
    intro hRbot
    have hqRbot : q.R = ⊥ := by
      simpa [R, theorem4bSection7R] using hRbot
    have hP₁bot : q.chosen.P₁ = ⊥ := by
      exact le_antisymm (q.hP₁R.trans hqRbot.le) bot_le
    have hlt := q.hP₁card_lt_R
    rw [hP₁bot, hqRbot] at hlt
    simp at hlt
  have hZne : Z ≠ ⊥ := by
    have hJne : thompsonCenter R ≠ ⊥ :=
      section8_centerIn_thompsonSubgroup_ne_bot_of_ne_bot hRp hRne
    have hJp : IsPGroup d.data.p (thompsonCenter R) :=
      hRp.to_le (thompsonCenter_le R)
    have hpdiv : d.data.p ∣ Nat.card (thompsonCenter R) := by
      rcases hJp.card_eq_or_dvd with hcard | hdiv
      · have hJbot : thompsonCenter R = ⊥ :=
          Subgroup.card_eq_one.mp hcard
        exact False.elim (hJne hJbot)
      · exact hdiv
    have h := omega₁_map_subtype_ne_bot (thompsonCenter R) d.data.p hpdiv
    convert h using 1
    ext x
    rfl
  have hZR : Z ≤ R := by
    change (omega₁ (G := thompsonCenter R) (p := d.data.p)).map
        (thompsonCenter R).subtype ≤ R
    exact (Subgroup.map_subtype_le _).trans (thompsonCenter_le R)
  let Zx : Subgroup X := Z.conjBy x
  let Rx : Subgroup X := R.conjBy x
  let P₁x : Subgroup X := q.chosen.P₁.conjBy x
  let t₁ : X := (MulAut.conj x) q.chosen.t
  have hZxp : IsPGroup d.data.p Zx := by
    change IsPGroup d.data.p
      (Z.map (MulAut.conj x).toMonoidHom)
    exact (hRp.to_le hZR).map (MulAut.conj x).toMonoidHom
  have hZxne : Zx ≠ ⊥ := by
    intro hbot
    apply hZne
    have hconj := congrArg (fun H : Subgroup X => H.conjBy x⁻¹) hbot
    have hbotConj : (⊥ : Subgroup X).conjBy x⁻¹ = ⊥ := by
      ext y
      simp [Subgroup.conjBy]
    simpa [Zx, Subgroup.conjBy_inv, hbotConj] using hconj
  have hRD : R ≤ D := by
    exact (theorem4bIsSylowSubgroupOf_le_final q.hRsylow).trans inf_le_left
  have hRxD : Rx ≤ D := by
    calc
      Rx ≤ D.conjBy x := Subgroup.map_mono hRD
      _ = D := theorem4b_section7_subgroup_conjBy_eq_self_of_mem D hxD
  have hZxRx : Zx ≤ Rx := Subgroup.map_mono hZR
  have hZxD : Zx ≤ D := hZxRx.trans hRxD
  have hZxE : Zx ≤ E := by
    simpa [D, E, theorem4bSection7D, theorem4bSection7E] using
      theorem4b_le_triple_stabilizer_of_le_two_point_stabilizer
        (by simpa [Zx, Z] using hzNormZx) hZxD
  have htNormZ : q.chosen.t ∈ Subgroup.normalizer (Z : Set X) := by
    exact normalizer_le_normalizer_corollary64Z R q.htNormR
  have ht₁I : IsInvolution t₁ := by
    exact IsInvolution.map_of_injective q.chosen.ht
      (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective
  have ht₁NormZx : t₁ ∈ Subgroup.normalizer (Zx : Set X) := by
    have hle := section11_conjBy_le_normalizer_conjBy_of_le_normalizer
      (H := Subgroup.zpowers q.chosen.t) (K := Z)
      (Subgroup.zpowers_le.mpr htNormZ) x
    apply hle
    rw [Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨q.chosen.t, Subgroup.mem_zpowers q.chosen.t, rfl⟩
  have ht₁Alpha : t₁ • alpha = s.beta := by
    change (x * q.chosen.t * x⁻¹) • alpha = s.beta
    calc
      _ = x • (q.chosen.t • (x⁻¹ • alpha)) := by
        simp [mul_smul, mul_assoc]
      _ = x • (q.chosen.t • alpha) := by rw [hxInvAlpha]
      _ = x • s.beta := by rw [q.chosen.htBase]
      _ = s.beta := hxBeta
  have ht₁Beta : t₁ • s.beta = alpha := by
    change (x * q.chosen.t * x⁻¹) • s.beta = alpha
    calc
      _ = x • (q.chosen.t • (x⁻¹ • s.beta)) := by
        simp [mul_smul, mul_assoc]
      _ = x • (q.chosen.t • s.beta) := by rw [hxInvBeta]
      _ = x • alpha := by rw [q.chosen.htBeta]
      _ = alpha := hxAlpha
  have hP₁E : q.chosen.P₁ ≤ E :=
    theorem4bIsSylowSubgroupOf_le_final q.chosen.hP₁sylow
  have hP₁xE : P₁x ≤ E := by
    calc
      P₁x ≤ E.conjBy x := Subgroup.map_mono hP₁E
      _ = E := theorem4b_section7_subgroup_conjBy_eq_self_of_mem E hxE
  have hP₁xcard : Nat.card P₁x = Nat.card q.chosen.P₁ := by
    exact Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hP₁xsyl : theorem4bIsSylowSubgroupOf d.data.p P₁x E :=
    theorem4bIsSylowSubgroupOf_of_subgroup_card_eq_final d.data.hp
      q.chosen.hP₁sylow hP₁xE hP₁xcard
  have hP₁NormZ : q.chosen.P₁ ≤
      Subgroup.normalizer (Z : Set X) := by
    exact q.hP₁R.trans
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_corollary64Z R))
  have hP₁xNormZx : P₁x ≤ Subgroup.normalizer (Zx : Set X) := by
    simpa [P₁x, Zx] using
      section11_conjBy_le_normalizer_conjBy_of_le_normalizer hP₁NormZ x
  have ht₁NormP₁x : t₁ ∈ Subgroup.normalizer (P₁x : Set X) := by
    have hle := section11_conjBy_le_normalizer_conjBy_of_le_normalizer
      (H := Subgroup.zpowers q.chosen.t) (K := q.chosen.P₁)
      (Subgroup.zpowers_le.mpr q.chosen.htNormP₁) x
    apply hle
    rw [Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨q.chosen.t, Subgroup.mem_zpowers q.chosen.t, rfl⟩
  let a : Theorem4bSection7AdmissibleQ d s := {
    Q := Zx
    hQp := hZxp
    hQne := hZxne
    hQE := hZxE
    hzNormQ := by simpa [Zx, Z] using hzNormZx
    t := t₁
    ht := ht₁I
    htNormQ := ht₁NormZx
    htBase := by simpa [alpha, theorem4bSection7Base] using ht₁Alpha
    htBeta := by simpa [alpha, theorem4bSection7Base] using ht₁Beta
    P₁ := P₁x
    hP₁sylow := hP₁xsyl
    hP₁NormQ := hP₁xNormZx
    htNormP₁ := ht₁NormP₁x }
  exact ⟨x, hxT, hxE, by simpa [Zx, Z] using hzNormZx,
    a, rfl, rfl, rfl⟩

/-- The final maximality argument after Lemma 7.11: the conjugate `R^x`
attached to the admissible subgroup `Z^x` is a Sylow `p`-subgroup of the
two-point stabilizer `D`. -/
private theorem IsStronglyEmbedded.theorem4b_section7_final_sylow
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (A : Subgroup H), IsStronglyEmbedded A →
        TheoremSEConclusion A)
    (s : Theorem4bSection7SecondStage d)
    (q : Theorem4bSection7MaximalQData d s) :
    ∃ x : X,
      x ∈ corollary64Theta d.data.p
        (theorem4bSection7M2InX M q.chosen.Q) ∧
      d.data.z ∈ Subgroup.normalizer
        ((theorem4bSection7Z q).conjBy x : Set X) ∧
      theorem4bIsSylowSubgroupOf d.data.p
        ((theorem4bSection7R q).conjBy x)
        (theorem4bSection7D M s.beta) := by
  classical
  letI : Fact d.data.p.Prime := ⟨d.data.hp⟩
  let D : Subgroup X := theorem4bSection7D M s.beta
  let E : Subgroup X := theorem4bSection7E M d.data.z s.beta
  let R : Subgroup X := q.R
  let Z : Subgroup X := theorem4bSection7Z q
  obtain ⟨x, hxT, hxE, hzNormZx, a, hQa, _hP₁a, _hta⟩ :=
    hM.theorem4b_section7_conjugated_admissibleQ
      hX d hrank hT2 hinduction s q
  let Rx : Subgroup X := R.conjBy x
  let NDQ : Subgroup X :=
    theorem4bSection7NormalizerInD M s.beta q.chosen.Q
  let NDZ : Subgroup X :=
    theorem4bSection7NormalizerInD M s.beta a.Q
  let NDR : Subgroup X :=
    theorem4bSection7NormalizerInD M s.beta Rx
  have hxD : x ∈ D := by
    exact (show E ≤ D from inf_le_left) hxE
  have hRp : IsPGroup d.data.p R := by
    change IsPGroup d.data.p q.R
    exact theorem4bIsSylowSubgroupOf_isPGroup_final q.hRsylow
  have hRxp : IsPGroup d.data.p Rx := by
    change IsPGroup d.data.p
      (R.map (MulAut.conj x).toMonoidHom)
    exact hRp.map (MulAut.conj x).toMonoidHom
  have hRD : R ≤ D := by
    exact (theorem4bIsSylowSubgroupOf_le_final q.hRsylow).trans inf_le_left
  have hRxD : Rx ≤ D := by
    calc
      Rx ≤ D.conjBy x := Subgroup.map_mono hRD
      _ = D := theorem4b_section7_subgroup_conjBy_eq_self_of_mem D hxD
  have hRxNDR : Rx ≤ NDR := by
    exact le_inf hRxD Subgroup.le_normalizer
  have hnormRxZx :
      Subgroup.normalizer (Rx : Set X) ≤
        Subgroup.normalizer (Z.conjBy x : Set X) := by
    have h := section11_conjBy_le_normalizer_conjBy_of_le_normalizer
      (H := Subgroup.normalizer (R : Set X)) (K := Z)
      (by simpa [Z, R, theorem4bSection7Z, theorem4bSection7R] using
        (normalizer_le_normalizer_corollary64Z R)) x
    rw [Subgroup.conjBy, Subgroup.map_equiv_normalizer_eq] at h
    simpa [Rx, Subgroup.conjBy, Set.image_image] using h
  have hnormRxA :
      Subgroup.normalizer (Rx : Set X) ≤
        Subgroup.normalizer (a.Q : Set X) := by
    rw [hQa]
    exact hnormRxZx
  have hNDRNDZ : NDR ≤ NDZ := by
    simpa [NDR, NDZ, theorem4bSection7NormalizerInD, D] using
      (inf_le_inf_left D hnormRxA)
  have hfacRxNDR :
      (Nat.card Rx).factorization d.data.p ≤
        (Nat.card NDR).factorization d.data.p :=
    Nat.factorization_le_factorization_of_dvd_right
      (Subgroup.card_dvd_of_le hRxNDR) Nat.card_pos.ne' Nat.card_pos.ne'
  have hfacNDRNDZ :
      (Nat.card NDR).factorization d.data.p ≤
        (Nat.card NDZ).factorization d.data.p :=
    Nat.factorization_le_factorization_of_dvd_right
      (Subgroup.card_dvd_of_le hNDRNDZ) Nat.card_pos.ne' Nat.card_pos.ne'
  have hfacNDZNDQ :
      (Nat.card NDZ).factorization d.data.p ≤
        (Nat.card NDQ).factorization d.data.p := by
    simpa [NDZ, NDQ] using q.maximal a
  have hRfacNDQ :
      (Nat.card R).factorization d.data.p =
        (Nat.card NDQ).factorization d.data.p := by
    rcases q.hRsylow with ⟨RN, hReq⟩
    have hcard : Nat.card R = Nat.card (RN : Subgroup NDQ) := by
      rw [show R = (RN : Subgroup NDQ).map NDQ.subtype by
        simpa [R, NDQ, theorem4bSection7R] using hReq]
      exact Subgroup.card_map_of_injective NDQ.subtype_injective
    rw [hcard]
    exact section8_factorization_card_sylow RN
  have hRxcard : Nat.card Rx = Nat.card R := by
    exact Subgroup.card_map_of_injective (MulAut.conj x).injective
  have houter :
      (Nat.card Rx).factorization d.data.p =
        (Nat.card NDQ).factorization d.data.p := by
    rw [hRxcard]
    exact hRfacNDQ
  refine ⟨x, hxT, hzNormZx, ?_⟩
  by_contra hnot
  have hgrowth :
      (Nat.card Rx).factorization d.data.p <
        (Nat.card NDR).factorization d.data.p := by
    simpa [NDR, theorem4bSection7NormalizerInD, D] using
      theorem4b_section7_factorization_lt_normalizerIn_of_not_sylow
        d.data.hp hRxp hRxD hnot
  have hback :
      (Nat.card NDR).factorization d.data.p ≤
        (Nat.card Rx).factorization d.data.p := by
    calc
      (Nat.card NDR).factorization d.data.p ≤
          (Nat.card NDZ).factorization d.data.p := hfacNDRNDZ
      _ ≤ (Nat.card NDQ).factorization d.data.p := hfacNDZNDQ
      _ = (Nat.card Rx).factorization d.data.p := houter.symm
  have heq :
      (Nat.card Rx).factorization d.data.p =
        (Nat.card NDR).factorization d.data.p :=
    le_antisymm hfacRxNDR hback
  exact (ne_of_lt hgrowth) heq

/-- Proposition 7.1, and hence Theorem 4(b): denying the base-point
conclusion produces the Section 7 maximal configuration, while the final
Sylow subgroup contradicts Corollary 6.4. -/
public theorem IsStronglyEmbedded.theorem4bAtBase_of_section7
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N) :
    Theorem4bAtBase M := by
  classical
  by_contra hnot
  obtain ⟨d⟩ := exists_theorem4bSixD_of_not_Theorem4bAtBase hnot
  obtain ⟨s⟩ :=
    hM.theorem4b_section7_secondStage hX d hrank hT2 hinduction
  obtain ⟨q⟩ :=
    hM.theorem4b_section7_maximalQData hX d hrank hT2 hinduction s
  obtain ⟨x, _hxTheta, hzNormZx, hRxsyl⟩ :=
    hM.theorem4b_section7_final_sylow hX d hrank hT2 hinduction s q
  let D : Subgroup X := theorem4bSection7D M s.beta
  let R : Subgroup X := q.R
  let Rx : Subgroup X := R.conjBy x
  have hRxsylD : theorem4bIsSylowSubgroupOf d.data.p Rx D := by
    have hReq : theorem4bSection7R q = q.R := rfl
    rw [hReq] at hRxsyl
    exact hRxsyl
  have hRxp : IsPGroup d.data.p Rx :=
    theorem4bIsSylowSubgroupOf_isPGroup_final hRxsylD
  have hRxD : Rx ≤ D := theorem4bIsSylowSubgroupOf_le_final hRxsylD
  have hDodd : Odd (Nat.card D) := by
    simpa [D, theorem4bSection7D] using
      hM.base_inf_stabilizer_card_odd s.hbetaNe
  have hcontains :
      ∃ P₀ : Sylow d.data.p (twoPrimeCore D),
        ((((P₀ : Subgroup (twoPrimeCore D)).map
          (twoPrimeCore D).subtype).map D.subtype) : Subgroup X) ≤ Rx :=
    by
      convert theorem4b_section7_sylow_contains_oddCore
        d.data.hp hDodd hRxsylD using 1
  have hzNormTheta : d.data.z ∈ Subgroup.normalizer
      (corollary64Theta d.data.p D : Set X) := by
    have htheta : corollary64Theta d.data.p D = ⊥ := by
      simpa [D] using s.htheta
    rw [htheta]
    apply Subgroup.mem_normalizer_fintype
    intro y hy
    have hy1 : y = 1 := by simpa using hy
    subst y
    simp
  have hcor := hM.corollary64 hX d.data hrank hT2 hinduction
    s.hbetaK s.hbetaNe (by
      simpa [D, theorem4bSection7D] using hzNormTheta)
  have hforbid : d.data.z ∉ Subgroup.normalizer
      (corollary64Z ⟨d.data.p, d.data.hp⟩ Rx : Set X) := by
    exact (hcor.2 Rx hRxp
      (by simpa [D, theorem4bSection7D] using hRxD)
      (by
        convert hcontains using 1
        · rfl
        · simp only [D, theorem4bSection7D]
          rfl)).1
  have hZconj :
      (theorem4bSection7Z q).conjBy x =
      corollary64Z ⟨d.data.p, d.data.hp⟩ Rx := by
    have hReq : theorem4bSection7R q = q.R := rfl
    change (theorem4bSection7Z q).conjBy x =
      corollary64Z ⟨d.data.p, d.data.hp⟩ (q.R.conjBy x)
    rw [← hReq]
    exact theorem4b_corollary64Z_conjBy
      (p := ⟨d.data.p, d.data.hp⟩) (theorem4bSection7R q) x
  apply hforbid
  rw [← hZconj]
  exact hzNormZx

end CFSG.BenderSuzuki
