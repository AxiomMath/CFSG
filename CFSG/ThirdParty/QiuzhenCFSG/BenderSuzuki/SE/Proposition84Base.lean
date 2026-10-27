module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Corollary713
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.InvolutionCore
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Action
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Coprime
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Sylow
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84TorusModels
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_1

namespace CFSG
end CFSG
open CFSG

/-!
# Proposition 8.4: the base case `Y₁ = Y`

This file proves all checked glue in the base case of Proposition 8.4.  The
remaining hypothesis of `proposition_8_4_base_of_source_endpoints` is the
earlier-section Theorem 4(b) contract.  The odd normalizer decomposition and
the `[II4; 3.2(c,d)]` model conclusions are discharged internally by checked
coprime-action, natural-model, and central odd-kernel theorems.  None assumes
`Proposition84BaseStep` or its complete conclusion.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open scoped Pointwise
open PFAppendixIII PFchapter1section1

universe u

/-- Inclusion of ambient subgroups induces inclusion of their embedded
involution cores. -/
public theorem involutionCoreIn_mono
    {X : Type u} [Group X] {H K : Subgroup X} (hHK : H ≤ K) :
    involutionCoreIn H ≤ involutionCoreIn K := by
  intro x hx
  rw [involutionCoreIn, Subgroup.mem_map] at hx ⊢
  rcases hx with ⟨h, hh, rfl⟩
  let hk : K := ⟨(h : X), hHK h.property⟩
  refine ⟨hk, ?_, rfl⟩
  rw [involutionCore_eq_closure] at hh ⊢
  refine Subgroup.closure_induction (p := fun a : H => fun _ha =>
    (⟨(a : X), hHK a.property⟩ : K) ∈
      Subgroup.closure (involutionsSet K)) ?_ ?_ ?_ ?_ hh
  · intro a ha
    apply Subgroup.subset_closure
    constructor
    · intro h
      apply ha.ne_one
      apply Subtype.ext
      exact congrArg (fun z : K => (z : X)) h
    · apply Subtype.ext
      exact congrArg (fun z : H => (z : X)) ha.sq_eq_one
  · exact Subgroup.one_mem _
  · intro a b _ha _hb ha hb
    exact (Subgroup.closure (involutionsSet K)).mul_mem ha hb
  · intro a _ha ha
    exact (Subgroup.closure (involutionsSet K)).inv_mem ha

/-- Every subgroup of the `V = C_D(u) = C_D(t)` supplied by Lemma 8.3 fixes
at least the three source points. -/
public theorem IsStronglyEmbedded.three_le_fixedPoints_of_le_lemma83V
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t) {Y : Subgroup X}
    (hYV : Y ≤ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({d83.u} : Set X)) :
    3 ≤ Nat.card (theorem4bFixedPoints M Y) := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  have hYVt : Y ≤ D ⊓ Subgroup.centralizer ({t} : Set X) := by
    rw [d83.centralizer_eq]
    exact hYV
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have hYleM : Y ≤ M := hYVt.trans (inf_le_left.trans inf_le_left)
  have hYleConj : Y ≤ rightConjugate M t :=
    hYVt.trans (inf_le_left.trans inf_le_right)
  have halpha : alpha ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) Y :=
    theorem4b_baseCoset_mem_fixedPoints hYleM
  have hbeta : beta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) Y := by
    intro y hy
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugateCoset_stabilizer M t, ht.inv_eq_self]
    exact hYleConj hy
  obtain ⟨gamma, htGamma, hgammaUnique⟩ :=
    hM.involution_fixed_coset_unique ht
  have hgamma : gamma ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) Y := by
    intro y hy
    have hcomm : y * t = t * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYVt hy).2
    apply hgammaUnique
    calc
      t • (y • gamma) = (t * y) • gamma := by rw [mul_smul]
      _ = (y * t) • gamma := by rw [hcomm]
      _ = y • (t • gamma) := by rw [mul_smul]
      _ = y • gamma := by rw [htGamma]
  have halphaBeta : alpha ≠ beta := by
    intro h
    apply htM
    simpa [alpha, beta] using QuotientGroup.eq.mp h
  have hgammaAlpha : gamma ≠ alpha := by
    intro h
    apply htM
    have htAlpha : t • alpha = alpha := by simpa [h] using htGamma
    have htStab : t ∈ MulAction.stabilizer X alpha :=
      MulAction.mem_stabilizer_iff.mpr htAlpha
    simpa [alpha, baseCoset_stabilizer M] using htStab
  have htBetaAlpha : t • beta = alpha := by
    have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
    simp [beta, alpha, MulAction.Quotient.smul_mk, htt]
  have hgammaBeta : gamma ≠ beta := by
    intro h
    have htBeta : t • beta = beta := by simpa [h] using htGamma
    exact halphaBeta (htBetaAlpha.symm.trans htBeta)
  let p0 : theorem4bFixedPoints M Y := ⟨alpha, halpha⟩
  let p1 : theorem4bFixedPoints M Y := ⟨beta, hbeta⟩
  let p2 : theorem4bFixedPoints M Y := ⟨gamma, hgamma⟩
  let f : Fin 3 → theorem4bFixedPoints M Y := ![p0, p1, p2]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      apply halphaBeta
      change (p0 : conjugateCosetSpace M) = (p1 : conjugateCosetSpace M)
      exact congrArg
        (fun z : theorem4bFixedPoints M Y => (z : conjugateCosetSpace M)) hij
    · exfalso
      apply hgammaAlpha
      change (p2 : conjugateCosetSpace M) = (p0 : conjugateCosetSpace M)
      exact congrArg
        (fun z : theorem4bFixedPoints M Y => (z : conjugateCosetSpace M)) hij.symm
    · exfalso
      apply halphaBeta
      change (p0 : conjugateCosetSpace M) = (p1 : conjugateCosetSpace M)
      exact congrArg
        (fun z : theorem4bFixedPoints M Y => (z : conjugateCosetSpace M)) hij.symm
    · rfl
    · exfalso
      apply hgammaBeta
      change (p2 : conjugateCosetSpace M) = (p1 : conjugateCosetSpace M)
      exact congrArg
        (fun z : theorem4bFixedPoints M Y => (z : conjugateCosetSpace M)) hij.symm
    · exfalso
      apply hgammaAlpha
      change (p2 : conjugateCosetSpace M) = (p0 : conjugateCosetSpace M)
      exact congrArg
        (fun z : theorem4bFixedPoints M Y => (z : conjugateCosetSpace M)) hij
    · exfalso
      apply hgammaBeta
      change (p2 : conjugateCosetSpace M) = (p1 : conjugateCosetSpace M)
      exact congrArg
        (fun z : theorem4bFixedPoints M Y => (z : conjugateCosetSpace M)) hij
    · rfl
  simpa using Nat.card_le_card_of_injective f hf

/-- If the normalizer is transitive on the fixed-point set, that set is
exactly the orbit of any one of its points. -/
public theorem normalizer_orbit_iff_fixedPoints_of_transitive
    {X Omega : Type*} [Group X] [MulAction X Omega]
    (Y : Subgroup X) (alpha omega : Omega)
    (halpha : alpha ∈ fixedPointsOfSubgroup X Omega Y)
    (htrans : IsTransitiveOn (Subgroup.normalizer (Y : Set X))
      (fixedPointsOfSubgroup X Omega Y)) :
    InOrbit (Subgroup.normalizer (Y : Set X)) alpha omega ↔
      omega ∈ fixedPointsOfSubgroup X Omega Y := by
  constructor
  · rintro ⟨n, hn⟩
    rw [← hn]
    intro y hyY
    have hyConj : (n : X)⁻¹ * y * (n : X) ∈ Y :=
      ((Subgroup.mem_normalizer_iff''.mp n.property) y).mp hyY
    calc
      y • ((n : X) • alpha) =
          (n : X) • (((n : X)⁻¹ * y * (n : X)) • alpha) := by
            simp [smul_smul, mul_assoc]
      _ = (n : X) • alpha := by rw [halpha _ hyConj]
  · intro homega
    exact htrans halpha homega

/-- If `x` lies in the Peterfalvi set and normalizes `Y`, then the dihedral
subgroup generated by `x` and the outside involution lies in `N_X(Y)`.
Writing `x = (x t)t` expresses `x` as a product of two involutions of the
normalizer, hence puts it in the embedded involution core. -/
public theorem peterfalviKSet_inter_normalizer_le_involutionCoreIn
    {X : Type*} [Group X] [Finite X]
    (M Y : Subgroup X) {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (htN : t ∈ Subgroup.normalizer (Y : Set X)) :
    {x : X | x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
      x ∈ Subgroup.normalizer (Y : Set X)} ⊆
        involutionCoreIn (Subgroup.normalizer (Y : Set X)) := by
  intro x hx
  let N : Subgroup X := Subgroup.normalizer (Y : Set X)
  have hxt_ne : x * t ≠ 1 := by
    intro hxt
    apply htM
    have hxt' : x = t⁻¹ := eq_inv_of_mul_eq_one_left hxt
    rw [ht.inv_eq_self] at hxt'
    rw [← hxt']
    exact hx.1.1.1
  have hconj : t * x * t = x⁻¹ := by
    simpa [peterfalviKSet, rightConjugateElem, ht.inv_eq_self] using hx.1.2
  have hxt_sq : (x * t) ^ 2 = 1 := by
    calc
      (x * t) ^ 2 = x * (t * x * t) := by simp [pow_two, mul_assoc]
      _ = x * x⁻¹ := by rw [hconj]
      _ = 1 := mul_inv_cancel x
  have hxt_inv : IsInvolution (x * t) := ⟨hxt_ne, hxt_sq⟩
  have hxtN : x * t ∈ N := N.mul_mem hx.2 htN
  have htCore : t ∈ involutionCoreIn N :=
    involution_mem_involutionCoreIn htN ht
  have hxtCore : x * t ∈ involutionCoreIn N :=
    involution_mem_involutionCoreIn hxtN hxt_inv
  have hxprod : (x * t) * t = x := by
    calc
      (x * t) * t = x * (t * t) := by rw [mul_assoc]
      _ = x := by
        simpa [pow_two] using congrArg (fun z => x * z) ht.sq_eq_one
  rw [← hxprod]
  exact (involutionCoreIn N).mul_mem hxtCore htCore

/-- If a finite group is the product of a normal subgroup and an odd-order
subgroup, then the quotient by the normal subgroup has odd order. -/
private theorem odd_card_quotient_of_eq_mul_odd
    {G : Type u} [Group G] [Finite G]
    (K R : Subgroup G) [K.Normal]
    (hfactor : (Set.univ : Set G) = (K : Set G) * (R : Set G))
    (hRodd : Odd (Nat.card R)) :
    Odd (Nat.card (G ⧸ K)) := by
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let qR : R →* G ⧸ K := q.comp R.subtype
  have hsurj : Function.Surjective qR := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K z
    have hg : g ∈ (K : Set G) * (R : Set G) := by
      rw [← hfactor]
      exact Set.mem_univ g
    rw [Set.mem_mul] at hg
    rcases hg with ⟨k, hk, r, hr, hkr⟩
    refine ⟨⟨r, hr⟩, ?_⟩
    change q r = q g
    rw [← hkr, map_mul]
    have hkq : q k = 1 := (QuotientGroup.eq_one_iff k).2 hk
    rw [hkq, one_mul]
  exact hRodd.of_dvd_nat (Subgroup.card_dvd_of_surjective hsurj)

/-- In a finite group with a strongly embedded subgroup, every normal
subgroup containing one involution contains the full involution core. -/
private theorem involutionCore_le_normal_of_stronglyEmbedded_of_mem
    {G : Type u} [Group G] [Finite G]
    {M K : Subgroup G} (hM : IsStronglyEmbedded M) [K.Normal]
    {t : G} (ht : IsInvolution t) (htK : t ∈ K) :
    involutionCore G ≤ K := by
  rw [involutionCore_eq_closure, Subgroup.closure_le]
  intro x hx
  have hxInv : IsInvolution x := hx
  obtain ⟨g, hg⟩ := hM.involutions_conjugate ht hxInv
  rw [← hg]
  simpa [rightConjugateElem, mul_assoc] using
    (inferInstance : K.Normal).conj_mem t htK g⁻¹

/-- Every normal subgroup containing an involution contains the involution
core when a strongly embedded subgroup makes all involutions conjugate. -/
public theorem IsStronglyEmbedded.involutionCore_le_normal_of_mem
    {G : Type u} [Group G] [Finite G]
    {M K : Subgroup G} (hM : IsStronglyEmbedded M) [K.Normal]
    {t : G} (ht : IsInvolution t) (htK : t ∈ K) :
    involutionCore G ≤ K :=
  involutionCore_le_normal_of_stronglyEmbedded_of_mem hM ht htK

/-- In the Proposition 8.4 base case, Corollary 7.13's factorization and the
oddness of the two-point stabilizer identify the normalizer involution core
with `O^{2'}(C_X(Y))`. -/
public theorem IsStronglyEmbedded.involutionCoreIn_normalizer_eq_centralizerTwoPrimeResidual
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (h82base : Proposition82aAtBase M)
    (d83 : Lemma83Data M t)
    {Y : Subgroup X}
    (hYV : Y ≤ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({d83.u} : Set X))
    (hnonsolv : Corollary713NonsolvableConclusion M
      (Subgroup.normalizer (Y : Set X))) :
    involutionCoreIn (Subgroup.normalizer (Y : Set X)) =
      centralizerTwoPrimeResidual Y := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let N : Subgroup X := Subgroup.normalizer (Y : Set X)
  let C : Subgroup X := Subgroup.centralizer (Y : Set X)
  let F1 : Subgroup X := involutionCoreIn N
  let F : Subgroup X := centralizerTwoPrimeResidual Y
  have hfixed : 3 ≤ Nat.card (theorem4bFixedPoints M Y) :=
    hM.three_le_fixedPoints_of_le_lemma83V ht htM d83 hYV
  have h82aY : Proposition82aConclusion M Y :=
    h82base.proposition82aConclusion Y
  have hC_le_N : C ≤ N := centralizer_le_normalizer Y
  have hcore_le_N : involutionCoreIn C ≤ N :=
    (involutionCoreIn_le C).trans hC_le_N
  obtain ⟨_hNtrans, hNstrong⟩ :=
    hM.proposition_8_2_b h82aY N hcore_le_N le_rfl hfixed
  have hYM : Y ≤ M := hYV.trans (inf_le_left.trans inf_le_left)
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  have halpha : alpha ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) Y :=
    theorem4b_baseCoset_mem_fixedPoints hYM
  have hNstrongAlpha : IsStronglyEmbedded (pointStabilizerIn N alpha) :=
    hNstrong alpha halpha
  have hYVt : Y ≤ D ⊓ Subgroup.centralizer ({t} : Set X) := by
    dsimp [D]
    rw [d83.centralizer_eq]
    exact hYV
  have htC : t ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hyY
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYVt hyY).2
  have htN : t ∈ N := hC_le_N htC
  have htF : t ∈ F :=
    (zpowers_le_centralizerTwoPrimeResidual_of_isInvolution Y ht htC)
      (Subgroup.mem_zpowers t)
  have hF_le_N : F ≤ N :=
    (centralizerTwoPrimeResidual_le_ambientCentralizer Y).trans hC_le_N
  letI : (F.subgroupOf N).Normal := by
    simpa [F, N] using centralizerTwoPrimeResidual_normal_in_normalizer Y
  let tN : N := ⟨t, htN⟩
  have htNInv : IsInvolution tN := IsInvolution.subtype ht htN
  have htFsub : tN ∈ F.subgroupOf N := htF
  have hcoreN_le_Fsub : involutionCore N ≤ F.subgroupOf N :=
    involutionCore_le_normal_of_stronglyEmbedded_of_mem
      hNstrongAlpha htNInv htFsub
  have hF1_le_F : F1 ≤ F := by
    intro x hx
    change x ∈ involutionCoreIn N at hx
    rw [involutionCoreIn, Subgroup.mem_map] at hx
    rcases hx with ⟨n, hn, rfl⟩
    exact hcoreN_le_Fsub hn
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have hbetaOrbit : InOrbit N alpha beta := by
    refine ⟨⟨t, htN⟩, ?_⟩
    simp [alpha, beta, MulAction.Quotient.smul_mk]
  have hbetaNe : beta ≠ alpha := by
    intro h
    apply htM
    simpa [alpha, beta] using QuotientGroup.eq.mp h.symm
  dsimp [Corollary713NonsolvableConclusion] at hnonsolv
  have hNfactor := hnonsolv.2.2.2 beta hbetaOrbit hbetaNe
  have htwoPoint :
      N ⊓ MulAction.stabilizer X alpha ⊓
          MulAction.stabilizer X beta = normalizerIn D Y := by
    have halphaStab : MulAction.stabilizer X alpha = M := by
      simp [alpha]
    have hbetaStab : MulAction.stabilizer X beta = rightConjugate M t := by
      simpa [beta, ht.inv_eq_self] using conjugateCoset_stabilizer M t
    rw [halphaStab, hbetaStab]
    ext x
    change ((x ∈ N ∧ x ∈ M) ∧ x ∈ rightConjugate M t) ↔
      ((x ∈ M ∧ x ∈ rightConjugate M t) ∧ x ∈ N)
    constructor
    · rintro ⟨⟨hxN, hxM⟩, hxt⟩
      exact ⟨⟨hxM, hxt⟩, hxN⟩
    · rintro ⟨⟨hxM, hxt⟩, hxN⟩
      exact ⟨⟨hxN, hxM⟩, hxt⟩
  let R : Subgroup X := normalizerIn D Y
  have hNfactor' : (N : Set X) = (F1 : Set X) * (R : Set X) := by
    change (N : Set X) =
      (F1 : Set X) *
        ((N ⊓ MulAction.stabilizer X alpha ⊓
          MulAction.stabilizer X beta : Subgroup X) : Set X) at hNfactor
    rw [htwoPoint] at hNfactor
    exact hNfactor
  have hF1_le_N : F1 ≤ N := involutionCoreIn_le N
  have hR_le_N : R ≤ N := by
    intro x hx
    exact hx.2
  have hF1sub : F1.subgroupOf N = involutionCore N := by
    simpa [F1, involutionCoreIn] using
      subgroupOf_map_subtype_eq (involutionCore N)
  have hNfactor_subtype :
      (Set.univ : Set N) =
        (involutionCore N : Set N) * ((R.subgroupOf N) : Set N) := by
    ext n
    constructor
    · intro _hn
      have hnFactor : (n : X) ∈ (F1 : Set X) * (R : Set X) := by
        rw [← hNfactor']
        exact n.property
      rw [Set.mem_mul] at hnFactor ⊢
      rcases hnFactor with ⟨f, hf, r, hr, hfr⟩
      let fN : N := ⟨f, hF1_le_N hf⟩
      let rN : N := ⟨r, hR_le_N hr⟩
      refine ⟨fN, ?_, rN, hr, ?_⟩
      · have hfsub : fN ∈ F1.subgroupOf N := hf
        rw [hF1sub] at hfsub
        exact hfsub
      · apply Subtype.ext
        exact hfr
    · intro _hn
      exact Set.mem_univ n
  have hRodd : Odd (Nat.card R) := by
    apply odd_of_card_dvd (hM.inf_rightConjugate_card_odd htM)
    exact Subgroup.card_dvd_of_le inf_le_left
  have hRsubOdd : Odd (Nat.card (R.subgroupOf N)) := by
    have hcard : Nat.card (R.subgroupOf N) = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR_le_N).toEquiv
    rw [hcard]
    exact hRodd
  have hquotOdd : Odd (Nat.card (N ⧸ involutionCore N)) :=
    odd_card_quotient_of_eq_mul_odd
      (involutionCore N) (R.subgroupOf N) hNfactor_subtype hRsubOdd
  have hresN : twoPrimeResidual N ≤ involutionCore N :=
    PFchapter1section3.twoPrimeResidual_le_of_odd_quotient hquotOdd
  let i : C →* N := Subgroup.inclusion hC_le_N
  have hmapres : (twoPrimeResidual C).map i ≤ twoPrimeResidual N :=
    twoPrimeResidual_map_le i
  have hF_le_F1 : F ≤ F1 := by
    intro x hx
    change x ∈ (twoPrimeResidual C).map C.subtype at hx
    rw [Subgroup.mem_map] at hx
    rcases hx with ⟨c, hc, rfl⟩
    have hicRes : i c ∈ twoPrimeResidual N :=
      hmapres (Subgroup.mem_map_of_mem i hc)
    have hicCore : i c ∈ involutionCore N := hresN hicRes
    change (c : X) ∈ involutionCoreIn N
    rw [involutionCoreIn, Subgroup.mem_map]
    exact ⟨i c, hicCore, rfl⟩
  exact le_antisymm hF1_le_F hF_le_F1

/-- The `[II4; 3.2(c)]` normal-Sylow conclusion transported from the Borel
quotient through the central odd core and then from stabilizer cosets to the
ambient fixed-point orbit. -/
public theorem proposition84_base_normalSylow_regular_of_borel
    {X : Type u} [Group X] [Finite X]
    (M Y F : Subgroup X)
    (hFcentral : F ≤ Subgroup.centralizer (Y : Set X))
    (hFnormal :
      (F.subgroupOf (Subgroup.normalizer (Y : Set X))).Normal)
    (hcore : twoPrimeCore F = Subgroup.center F)
    (hcoreM : (twoPrimeCore F).map F.subtype ≤ M)
    (hBorel : IsBorelSubgroup
      (((F ⊓ M).subgroupOf F).map
        (QuotientGroup.mk' (twoPrimeCore F))))
    (hmodel : IsSimpleBenderGroup (F ⧸ twoPrimeCore F))
    (horbit : ∀ omega : conjugateCosetSpace M,
      InOrbit F (QuotientGroup.mk 1) omega ↔
        omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y) :
    ∃ S : Subgroup X,
      (S.subgroupOf (normalizerIn M Y)).Normal ∧
      (∃ P : Sylow 2 ↥(F ⊓ M),
        S = (P : Subgroup ↥(F ⊓ M)).map (F ⊓ M).subtype) ∧
      IsRegularOn S
        {omega : conjugateCosetSpace M |
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y ∧
            omega ≠ QuotientGroup.mk 1} := by
  let K : Subgroup F := twoPrimeCore F
  let H0 : Subgroup X := F ⊓ M
  let H : Subgroup F := H0.subgroupOf F
  let q : F →* (F ⧸ K) := QuotientGroup.mk' K
  let B : Subgroup (F ⧸ K) := H.map q
  have hKH : K ≤ H := by
    intro k hk
    change ((k : X) ∈ F ∧ (k : X) ∈ M)
    refine ⟨k.property, ?_⟩
    exact hcoreM (Subgroup.mem_map_of_mem F.subtype hk)
  have hKodd : Nat.Coprime 2 (Nat.card K) := by
    simpa [K, twoPrimeCore] using
      (pPrimeCore_coprime_card (p := 2) (G := F))
  have hKcentral : K ≤ Subgroup.center F := by
    rw [show K = twoPrimeCore F by rfl, hcore]
  have hBorel' : IsBorelSubgroup B := by
    simpa [B, H, H0, q, K] using hBorel
  have hmodel' : IsSimpleBenderGroup (F ⧸ K) := by
    simpa [K] using hmodel
  obtain ⟨Pbar, hPbarNormal, hPbarRegular⟩ :=
    simpleBender_borel_normalSylow_regular hBorel' hmodel'
  obtain ⟨P, hPNormal, hPmap, hPinj⟩ :=
    sylow_lift_of_central_odd_core K H hKH hKodd hKcentral
      Pbar hPbarNormal
  let e : H ≃* H0 := Subgroup.subgroupOfEquivOfLe inf_le_left
  have he_surj : Function.Surjective (e : H →* H0) := by
    exact e.surjective
  let P0 : Sylow 2 H0 :=
    Sylow.mapSurjective (f := (e : H →* H0)) he_surj P
  have hP0map : (P0 : Subgroup H0) =
      (P : Subgroup H).map (e : H →* H0) := by
    dsimp [P0]
  have hP0normal : (P0 : Subgroup H0).Normal := by
    rw [hP0map]
    exact hPNormal.map (e : H →* H0) he_surj
  let SF : Subgroup F := (P : Subgroup H).map H.subtype
  let S : Subgroup X := (P0 : Subgroup H0).map H0.subtype
  have hS_eq : S = SF.map F.subtype := by
    dsimp [S, SF]
    rw [hP0map]
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hker : q.ker ≤ H := by
    simpa [q, QuotientGroup.ker_mk'] using hKH
  have hregCoset : IsRegularOn SF
      {c : F ⧸ H | c ≠ QuotientGroup.mk 1} := by
    apply coset_isRegularOn_of_surjective q
      (QuotientGroup.mk'_surjective K) H SF
      ((Pbar : Subgroup B).map B.subtype)
    · exact hker
    · simpa [SF, B, q] using hPmap
    · simpa [SF, q] using hPinj
    · simpa [B] using hPbarRegular
  have hpoint : pointStabilizerIn F
      (QuotientGroup.mk 1 : conjugateCosetSpace M) = H := by
    ext f
    change (f : X) ∈ MulAction.stabilizer X
        (QuotientGroup.mk 1 : conjugateCosetSpace M) ↔
      ((f : X) ∈ F ∧ (f : X) ∈ M)
    rw [baseCoset_stabilizer]
    simp
  have hregOrbit : IsRegularOn (SF.map F.subtype)
      {omega : conjugateCosetSpace M |
        InOrbit F (QuotientGroup.mk 1) omega ∧
          omega ≠ QuotientGroup.mk 1} := by
    apply regularOn_orbit_of_coset F
      (QuotientGroup.mk 1 : conjugateCosetSpace M) SF
    rw [hpoint]
    exact hregCoset
  have hSle : S ≤ normalizerIn M Y := by
    intro s hs
    rcases Subgroup.mem_map.mp hs with ⟨p, hp, rfl⟩
    exact ⟨p.property.2,
      centralizer_le_normalizer Y (hFcentral p.property.1)⟩
  have hH0le : H0 ≤ normalizerIn M Y := by
    intro x hx
    exact ⟨hx.2, centralizer_le_normalizer Y (hFcentral hx.1)⟩
  have hH0normal :
      (H0.subgroupOf (normalizerIn M Y)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hH0le]
    intro f n hf hn
    refine ⟨?_, M.mul_mem (M.mul_mem hn.1 hf.2) (M.inv_mem hn.1)⟩
    exact (Subgroup.normal_subgroupOf_iff
      (hFcentral.trans (centralizer_le_normalizer Y))).mp hFnormal
        f n hf.1 hn.2
  have hP0char : (P0 : Subgroup H0).Characteristic :=
    Sylow.characteristic_of_normal P0 hP0normal
  have hSnormal : (S.subgroupOf (normalizerIn M Y)).Normal :=
    normal_subgroupOf_map_of_characteristic_of_normal
      H0 S (normalizerIn M Y) hH0le hH0normal
      (P0 : Subgroup H0) hP0char rfl hSle
  refine ⟨S, hSnormal, ⟨P0, rfl⟩, ?_⟩
  rw [hS_eq]
  simpa only [horbit] using hregOrbit

/-- Checked base-case assembly from Corollary 7.13 with its retained Borel
witness; the `[II4; 3.2(d)]` endpoint is proved internally. -/
public theorem IsStronglyEmbedded.proposition_8_4_base_full_of_corollary713
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (h82base : Proposition82aAtBase M)
    (d83 : Lemma83Data M t)
    (h713 : ∀ (Y : Subgroup X),
      Y ≤ (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({d83.u} : Set X) →
      Y ≠ ⊥ →
      HasNontrivialPeterfalviNormalizer
        (M ⊓ rightConjugate M t) t Y →
      Corollary713BorelConclusion M
        (Subgroup.normalizer (Y : Set X))) :
  Proposition84BaseFullStep M t d83.u := by
  dsimp [Proposition84BaseFullStep]
  intro Y hYV hYne hI
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := D ⊓ Subgroup.centralizer ({d83.u} : Set X)
  let N : Subgroup X := Subgroup.normalizer (Y : Set X)
  let F1 : Subgroup X := involutionCoreIn N
  let F : Subgroup X := centralizerTwoPrimeResidual Y
  have hfixed : 3 ≤ Nat.card (theorem4bFixedPoints M Y) :=
    hM.three_le_fixedPoints_of_le_lemma83V ht htM d83 hYV
  have h82aY : Proposition82aConclusion M Y :=
    h82base.proposition82aConclusion Y
  have hC_le_N : Subgroup.centralizer (Y : Set X) ≤ N := by
    exact centralizer_le_normalizer Y
  have hcore_le_N : involutionCoreIn (Subgroup.centralizer (Y : Set X)) ≤ N :=
    (involutionCoreIn_le _).trans hC_le_N
  have hN_le_norm : N ≤ Subgroup.normalizer (Y : Set X) := le_rfl
  obtain ⟨hNtrans, _hNstrong⟩ :=
    hM.proposition_8_2_b h82aY N hcore_le_N hN_le_norm hfixed
  have hcore_le_F1 :
      involutionCoreIn (Subgroup.centralizer (Y : Set X)) ≤ F1 :=
    involutionCoreIn_mono hC_le_N
  have hF1_le_N : F1 ≤ N := involutionCoreIn_le N
  obtain ⟨hF1trans, _hF1strong⟩ :=
    hM.proposition_8_2_b h82aY F1 hcore_le_F1 hF1_le_N hfixed
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have hYM : Y ≤ M := hYV.trans (inf_le_left.trans inf_le_left)
  have halpha : alpha ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) Y :=
    theorem4b_baseCoset_mem_fixedPoints hYM
  have horbit : ∀ omega : conjugateCosetSpace M,
      InOrbit N alpha omega ↔
        omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y :=
    fun omega =>
      normalizer_orbit_iff_fixedPoints_of_transitive
        Y alpha omega halpha hNtrans
  have huC : d83.u ∈ Subgroup.centralizer (Y : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hyY
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYV hyY).2
  have huN : d83.u ∈ N := hC_le_N huC
  have h713Y : Corollary713BorelConclusion M N := h713 Y hYV hYne hI
  rcases h713Y.2 with hsolv |
    ⟨_hF1notSolvable, hnonsolv, hBorelF1⟩
  · exfalso
    rcases hsolv with ⟨_hsolv, z, hzNM, hz, hunique, hNMcentral⟩
    have huNM : d83.u ∈ N ⊓ M := ⟨huN, d83.u_mem_M⟩
    have huz : d83.u = z := hunique d83.u huNM d83.u_involution
    obtain ⟨x, hxI, hxN, hxne⟩ := hI
    have hxM : x ∈ M := hxI.1.1
    have hxNM : x ∈ N ⊓ M := ⟨hxN, hxM⟩
    have hxCentZ : x ∈ Subgroup.centralizer ({z} : Set X) := by
      have hx := hxNM
      rw [hNMcentral] at hx
      exact hx.2
    have hxCentU : x ∈ Subgroup.centralizer ({d83.u} : Set X) := by
      simpa [huz] using hxCentZ
    exact hxne (hM.eq_one_of_mem_peterfalviKSet_and_centralizes_involution
      d83.u_mem_M d83.u_involution ht htM hxI hxCentU)
  · have hF1F : F1 = F :=
      hM.involutionCoreIn_normalizer_eq_centralizerTwoPrimeResidual
        ht htM h82base d83 hYV hnonsolv
    have hcoreF1 : twoPrimeCore F1 = Subgroup.center F1 := hnonsolv.1
    have hcoreF : twoPrimeCore F = Subgroup.center F := by
      rw [← hF1F]
      exact hcoreF1
    have htwoF : IsTwoTransitiveOn F
        (fixedPointsOfSubgroup X (conjugateCosetSpace M) Y) := by
      dsimp [Corollary713NonsolvableConclusion] at hnonsolv
      rw [← hF1F]
      intro a b c d ha hb hc hd hab hcd
      exact hnonsolv.2.2.1 ((horbit a).2 ha) ((horbit b).2 hb)
        ((horbit c).2 hc) ((horbit d).2 hd) hab hcd
    have hYVt : Y ≤ D ⊓ Subgroup.centralizer ({t} : Set X) := by
      dsimp [D]
      rw [d83.centralizer_eq]
      exact hYV
    have htC : t ∈ Subgroup.centralizer (Y : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyY
      exact Subgroup.mem_centralizer_singleton_iff.mp (hYVt hyY).2
    have htN : t ∈ N := hC_le_N htC
    have hbetaOrbit : InOrbit N alpha beta := by
      refine ⟨⟨t, htN⟩, ?_⟩
      simp [alpha, beta, MulAction.Quotient.smul_mk]
    have hbetaNe : beta ≠ alpha := by
      intro h
      apply htM
      simpa [alpha, beta] using QuotientGroup.eq.mp h.symm
    have hNfactor := hnonsolv.2.2.2 beta hbetaOrbit hbetaNe
    have htwoPoint :
        N ⊓ MulAction.stabilizer X alpha ⊓
            MulAction.stabilizer X beta =
          normalizerIn D Y := by
      have halphaStab : MulAction.stabilizer X alpha = M := by
        simp [alpha]
      have hbetaStab : MulAction.stabilizer X beta = rightConjugate M t := by
        simpa [beta, ht.inv_eq_self] using conjugateCoset_stabilizer M t
      rw [halphaStab, hbetaStab]
      ext x
      change ((x ∈ N ∧ x ∈ M) ∧ x ∈ rightConjugate M t) ↔
        ((x ∈ M ∧ x ∈ rightConjugate M t) ∧ x ∈ N)
      constructor
      · rintro ⟨⟨hxN, hxM⟩, hxt⟩
        exact ⟨⟨hxM, hxt⟩, hxN⟩
      · rintro ⟨⟨hxM, hxt⟩, hxN⟩
        exact ⟨⟨hxN, hxM⟩, hxt⟩
    have hNfactor' :
        (N : Set X) =
          (F : Set X) * (normalizerIn D Y : Set X) := by
      change (N : Set X) =
        (F1 : Set X) *
          ((N ⊓ MulAction.stabilizer X alpha ⊓
            MulAction.stabilizer X beta : Subgroup X) : Set X) at hNfactor
      rw [hF1F, htwoPoint] at hNfactor
      exact hNfactor
    have hNormalizer :
        (N : Set X) =
          (F : Set X) * (normalizerIn V Y : Set X) := by
      apply Set.Subset.antisymm
      · intro x hxN
        have hxFactor : x ∈
            (F : Set X) * (normalizerIn D Y : Set X) := by
          rw [← hNfactor']
          exact hxN
        rw [Set.mem_mul] at hxFactor
        rcases hxFactor with ⟨a, haF, d, hdD, had⟩
        have hdFactor :=
          (normalizerIn_le_centralizerResidual_mul_normalizerIn
            hM ht htM d83 hYV) hdD
        rw [Set.mem_mul] at hdFactor
        rcases hdFactor with ⟨b, hbF, v, hvV, hbv⟩
        rw [Set.mem_mul]
        refine ⟨a * b, F.mul_mem haF hbF, v, hvV, ?_⟩
        rw [mul_assoc, hbv, had]
      · intro x hx
        rw [Set.mem_mul] at hx
        rcases hx with ⟨a, haF, v, hvV, hav⟩
        have hFleN : F ≤ N := by
          rw [← hF1F]
          exact hF1_le_N
        rw [← hav]
        exact N.mul_mem (hFleN haF) hvV.2
    have hbenderFplain : IsSimpleBenderGroup
        (F ⧸ twoPrimeCore F) := by
      rw [← hF1F]
      exact hnonsolv.2.1
    have hBorelF : IsBorelSubgroup
        (((F ⊓ M).subgroupOf F).map
          (QuotientGroup.mk' (twoPrimeCore F))) := by
      rw [← hF1F]
      simpa [F1, N, inf_comm] using hBorelF1
    have huF1 : d83.u ∈ F1 := by
      change d83.u ∈ involutionCoreIn N
      exact involution_mem_involutionCoreIn huN d83.u_involution
    have huF : d83.u ∈ F := by
      rw [← hF1F]
      exact huF1
    have hcoreM : (twoPrimeCore F).map F.subtype ≤ M := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
      apply hM.centralizer_le d83.u_mem_M d83.u_involution
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hkCenter : k ∈ Subgroup.center F := by
        rw [← hcoreF]
        exact hk
      let uF : F := ⟨d83.u, huF⟩
      exact congrArg Subtype.val
        ((Subgroup.mem_center_iff.mp hkCenter) uF).symm
    have hFtrans : IsTransitiveOn F
        (fixedPointsOfSubgroup X (conjugateCosetSpace M) Y) := by
      rw [← hF1F]
      exact hF1trans
    have horbitF : ∀ omega : conjugateCosetSpace M,
        InOrbit F alpha omega ↔
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y := by
      intro omega
      constructor
      · rintro ⟨f, rfl⟩
        exact smul_mem_fixedPointsOfSubgroup_of_mem_normalizer
          (centralizer_le_normalizer Y
            (centralizerTwoPrimeResidual_le_ambientCentralizer Y f.property))
          halpha
      · exact hFtrans halpha
    obtain ⟨S, hSnormal, hSsylow, hSregular⟩ :=
      proposition84_base_normalSylow_regular_of_borel M Y F
        (by simpa [F] using
          centralizerTwoPrimeResidual_le_ambientCentralizer Y)
        (by simpa [F] using
          centralizerTwoPrimeResidual_normal_in_normalizer Y)
        hcoreF hcoreM hBorelF hbenderFplain
        (by simpa [alpha] using horbitF)
    rcases hSsylow with ⟨P, hSmap⟩
    have hSle : S ≤ normalizerIn M Y := by
      rw [hSmap]
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨p, _hp, rfl⟩
      exact ⟨p.property.2, centralizer_le_normalizer Y
        (centralizerTwoPrimeResidual_le_ambientCentralizer Y p.property.1)⟩
    have hSfactor := normalizerIn_eq_mul_normalizerIn_of_regularOn
      M Y S ht htM (hYV.trans inf_le_left) hSle hSregular
    obtain ⟨n, hn, hmodel⟩ := hbenderFplain.exists_exponent
    have htF : t ∈ F := by
      rw [← hF1F]
      exact involution_mem_involutionCoreIn htN ht
    have hFleN : F ≤ N := by
      rw [← hF1F]
      exact hF1_le_N
    have hlocalLeF :
        {x : X | x ∈ peterfalviKSet D t ∧ x ∈ N} ⊆ F := by
      intro x hx
      rw [← hF1F]
      exact peterfalviKSet_inter_normalizer_le_involutionCoreIn
        M Y ht htM htN hx
    obtain ⟨J, hJset, hJcyclic, hJcard⟩ :=
      proposition84_base_cyclicNormalizer_of_borel_model
        M F N t ht htM htF hFleN hcoreF hcoreM hBorelF
          n hn hmodel (by simpa [D] using hlocalLeF)
    have hJF1 : J ≤ F1 := by
      intro x hxJ
      apply peterfalviKSet_inter_normalizer_le_involutionCoreIn
        M Y ht htM htN
      rw [← hJset]
      exact hxJ
    have hJF : J ≤ F := by
      rw [← hF1F]
      exact hJF1
    refine ⟨?_, ?_⟩
    · dsimp [Proposition84Conclusion, Proposition84ABConclusion,
        Proposition84CDConclusion]
      refine ⟨⟨htwoF, ?_, ?_⟩, ?_⟩
      · simpa [N, V, F, D] using hNormalizer
      · exact ⟨S, hSle, hSnormal, ⟨P, hSmap⟩, hSregular, hSfactor⟩
      · intro _hI
        exact ⟨n, J, hn, hJset, hJF, hJcyclic, hJcard, hcoreF, hmodel⟩
    · exact
        { oddCore_map_le_M := by simpa [F] using hcoreM
          quotient_borel := by simpa [F] using hBorelF }

/-- The numbered Proposition 8.4 base step, projected from the strengthened
proof-support package. -/
public theorem IsStronglyEmbedded.proposition_8_4_base_of_corollary713
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (h82base : Proposition82aAtBase M)
    (d83 : Lemma83Data M t)
    (h713 : ∀ (Y : Subgroup X),
      Y ≤ (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({d83.u} : Set X) →
      Y ≠ ⊥ →
      HasNontrivialPeterfalviNormalizer
        (M ⊓ rightConjugate M t) t Y →
      Corollary713BorelConclusion M
        (Subgroup.normalizer (Y : Set X))) :
  Proposition84BaseStep M t d83.u := by
  intro Y hYV hYne hI
  exact (hM.proposition_8_4_base_full_of_corollary713
    ht htM h82base d83 h713 Y hYV hYne hI).1

/-- The support facts retained from the same Proposition 8.4 base proof. -/
public theorem IsStronglyEmbedded.proposition_8_4_modelSupport_of_corollary713
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (h82base : Proposition82aAtBase M)
    (d83 : Lemma83Data M t)
    (h713 : ∀ (Y : Subgroup X),
      Y ≤ (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({d83.u} : Set X) →
      Y ≠ ⊥ →
      HasNontrivialPeterfalviNormalizer
        (M ⊓ rightConjugate M t) t Y →
      Corollary713BorelConclusion M
        (Subgroup.normalizer (Y : Set X))) :
  Proposition84ModelSupportStatement M t d83.u := by
  intro Y hYV hYne hI
  exact (hM.proposition_8_4_base_full_of_corollary713
    ht htM h82base d83 h713 Y hYV hYne hI).2

/-- Proposition 8.4's exact base-step interface from the standing simple
minimal-counterexample context, the proper-subgroup Theorem SE induction
hypothesis, and the earlier-section Theorem 4(b) contract.  The
`[II4; 3.2(d)]` model endpoint is derived from the recognized natural models
and the central odd-kernel lift.
The solvable branch is discharged internally by Lemma 3.12.
The nonsolvable-rank exclusion is derived from the independent
rank-one/Brauer--Suzuki argument.  Corollary 7.13 recognition/Borel data, residual
identification, the normal Sylow regular action, and the odd normalizer
decomposition are derived internally. -/
public theorem IsStronglyEmbedded.proposition_8_4_base_full_of_source_endpoints
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hXsimple : IsSimpleGroup X) {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (h82base : Proposition82aAtBase M)
    (d83 : Lemma83Data M t)
    (h4b : Theorem4bAtBase M)
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N) :
    Proposition84BaseFullStep M t d83.u := by
  apply hM.proposition_8_4_base_full_of_corollary713 ht htM h82base d83
  · intro Y hYV hYne hI
    let N : Subgroup X := Subgroup.normalizer (Y : Set X)
    have hYVt :
        Y ≤ (M ⊓ rightConjugate M t) ⊓
          Subgroup.centralizer ({t} : Set X) := by
      rw [d83.centralizer_eq]
      exact hYV
    have htC : t ∈ Subgroup.centralizer (Y : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyY
      exact Subgroup.mem_centralizer_singleton_iff.mp (hYVt hyY).2
    have htN : t ∈ N := centralizer_le_normalizer Y htC
    have huC : d83.u ∈ Subgroup.centralizer (Y : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyY
      exact Subgroup.mem_centralizer_singleton_iff.mp (hYV hyY).2
    have huN : d83.u ∈ N := centralizer_le_normalizer Y huC
    have hNnotle : ¬ N ≤ M := by
      intro hle
      exact htM (hle htN)
    have hNproper : N ≠ ⊤ := by
      simpa [N] using
        hM.normalizer_ne_top_of_isSimpleGroup_of_ne_bot_of_le
          hXsimple hYne (hYV.trans (inf_le_left.trans inf_le_left))
    exact corollary713_borel_of_source_endpoints M N hM h4b hNnotle hNproper
      hinduction
      ⟨huN, d83.u_mem_M⟩ d83.u_involution

/-- The source-facing Proposition 8.4 base step. -/
public theorem IsStronglyEmbedded.proposition_8_4_base_of_source_endpoints
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hXsimple : IsSimpleGroup X) {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (h82base : Proposition82aAtBase M)
    (d83 : Lemma83Data M t)
    (h4b : Theorem4bAtBase M)
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N) :
    Proposition84BaseStep M t d83.u := by
  intro Y hYV hYne hI
  exact (hM.proposition_8_4_base_full_of_source_endpoints
    hXsimple ht htM h82base d83 h4b hinduction Y hYV hYne hI).1

/-- The Proposition 8.4 model support retained for Section 11. -/
public theorem IsStronglyEmbedded.proposition_8_4_modelSupport_of_source_endpoints
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hXsimple : IsSimpleGroup X) {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (h82base : Proposition82aAtBase M)
    (d83 : Lemma83Data M t)
    (h4b : Theorem4bAtBase M)
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N) :
    Proposition84ModelSupportStatement M t d83.u := by
  intro Y hYV hYne hI
  exact (hM.proposition_8_4_base_full_of_source_endpoints
    hXsimple ht htM h82base d83 h4b hinduction Y hYV hYne hI).2

end CFSG.BenderSuzuki
