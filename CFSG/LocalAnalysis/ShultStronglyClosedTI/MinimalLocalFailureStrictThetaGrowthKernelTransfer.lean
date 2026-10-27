module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureStrictThetaGrowthTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddKernelNormalizerTransfer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaActualIndex
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaNormalizerLift

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.StrictThetaGrowth

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.OrderReductions.PrimePart
open CFSG.RankThreeEvenClassification.Helpers
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem kernel_transfer_orderZJ_admissible
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (X A : Subgroup G) (v : G) (hadm : Admissible H z beta p X A v)
    (Q : Sylow p (Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta : Subgroup G))
    (hAQ : A ≤ (Q : Subgroup _).map
      (Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta).subtype)
    (hvQ : v ∈ Subgroup.normalizer ((Q : Subgroup _).map
      (Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta).subtype : Set G))
    (hQne : (Q : Subgroup _).map
      (Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta).subtype ≠ ⊥)
    (K : Subgroup G)
    (hTK : Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta ≤ K)
    (hzK : z ∈ K) (hrankK : 2 ≤ twoRank K)
    (hclass : ∀ a : G, (a ∈ K ∧ IsInvolution a) ↔
      a ∈ conjugacyWithin (Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta) z)
    (hWodd : Odd (Nat.card (CFSG.pPrimeCore p K)))
    (hWE : (CFSG.pPrimeCore p K).map K.subtype ≤ triplePointStabilizer H z beta)
    (S : Sylow p K)
    (hSQ : (S : Subgroup K).map K.subtype = (Q : Subgroup _).map
      (Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta).subtype)
    (hprod :
      let QG := (Q : Subgroup _).map
        (Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta).subtype
      let R := (orderZJ QG).map QG.subtype
      (K : Set G) = ((CFSG.pPrimeCore p K).map K.subtype : Set G) *
        (K ⊓ Subgroup.normalizer (R : Set G) : Set G)) :
    let T := Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta
    let QG := (Q : Subgroup T).map T.subtype
    let R := (orderZJ QG).map QG.subtype
    ∃ w ∈ (CFSG.pPrimeCore p K).map K.subtype,
      let Q1 := rightConjugate QG w⁻¹
      let R1 := rightConjugate R w⁻¹
      let A1 := rightConjugate A w⁻¹
      let v1 := rightConjugateElem v w⁻¹
      Admissible H z beta p R1 A1 v1 ∧ Q1 ≤ pairOddCore H beta ∧
        R1 ≤ Q1 ∧ (R1.subgroupOf Q1).Characteristic ∧ IsPGroup p Q1 ∧
        v1 ∈ Subgroup.normalizer (Q1 : Set G) ∧
        R1 = (orderZJ Q1).map Q1.subtype ∧ Q1 ≠ ⊥ ∧
        Nat.card Q1 = primePart p (Nat.card T) := by
  let : Fact p.Prime := ⟨hp⟩
  let T := Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta
  let QG := (Q : Subgroup T).map T.subtype
  let R := (orderZJ QG).map QG.subtype
  let SK := (S : Subgroup K)
  let RK := (orderZJ SK).map SK.subtype
  let AK := A.subgroupOf K
  let W := CFSG.pPrimeCore p K
  let N := Subgroup.normalizer (RK : Set K)
  let zK : K := ⟨z, hzK⟩
  have hQp : IsPGroup p QG := Q.isPGroup'.map T.subtype
  have hRQ : R ≤ QG := Subgroup.map_subtype_le _
  have hQJ : QG ≤ pairOddCore H beta :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  have hRJ : R ≤ pairOddCore H beta := hRQ.trans hQJ
  let : Nontrivial QG := (Subgroup.nontrivial_iff_ne_bot QG).mpr hQne
  have hRne : R ≠ ⊥ := by
    intro hbot
    exact primeComplementGrowth_order_zj_ne_bot p hQp
      ((Subgroup.map_eq_bot_iff_of_injective _ QG.subtype_injective).mp hbot)
  have hRchar : (orderZJ QG).Characteristic := primeComplementGrowth_order_zj_characteristic
  have hvR : v ∈ Subgroup.normalizer (R : Set G) :=
    generatedPairGrowth_normalizer_le_characteristic_image QG (orderZJ QG) hRchar hvQ
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAQ.trans (Subgroup.le_normalizer.trans
      (generatedPairGrowth_normalizer_le_characteristic_image QG (orderZJ QG) hRchar))
  have hKker : Nat.Coprime p (Nat.card K.subtype.ker) := by
    rw [MonoidHom.ker_eq_bot _ K.subtype_injective, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hRimage : RK.map K.subtype = R := by
    have hh := LocalTheta.orderZJ_image_of_coprime_kernel hp K.subtype hKker SK S.isPGroup'
    rwa [hSQ] at hh
  have hRKQ : RK ≤ SK := Subgroup.map_subtype_le _
  have hRKchar : (RK.subgroupOf SK).Characteristic := by
    change (((orderZJ SK).map SK.subtype).comap SK.subtype).Characteristic
    rw [Subgroup.comap_map_eq_self_of_injective SK.subtype_injective]
    exact primeComplementGrowth_order_zj_characteristic
  have hAKQ : AK ≤ SK := by
    have hh := Subgroup.comap_mono (f := K.subtype) hAQ
    rwa [← hSQ, Subgroup.comap_map_eq_self_of_injective K.subtype_injective] at hh
  have hAK : A ≤ K := hAQ.trans ((Subgroup.map_subtype_le _).trans hTK)
  have hAKimage : AK.map K.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAK
  have hzAK : zK ∈ Subgroup.normalizer (AK : Set K) :=
    Subgroup.le_normalizer_comap K.subtype
      (invariant_subgroup_mem_normalizer hadm.witness_distinguished_invariant)
  have hAKz : rightConjugate AK zK = AK := rightConjugate_eq_self_of_mem_normalizer hzAK
  have hAKnoncentral : ¬ AK ≤ Subgroup.centralizer ({zK} : Set K) := by
    intro hcent
    apply hadm.witness_noncentral
    intro a ha
    have hh := Subgroup.mem_centralizer_singleton_iff.mp
      (hcent (show (⟨a, hAK ha⟩ : K) ∈ AK from ha))
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hh)
  have hzKi : IsInvolution zK := by
    have hz : IsInvolution z :=
      ⟨(orderOf_eq_prime_iff.mp h.distinguished_order).2,
        (orderOf_eq_prime_iff.mp h.distinguished_order).1⟩
    exact ⟨fun h1 => hz.ne_one (congrArg Subtype.val h1), Subtype.ext hz.sq_eq_one⟩
  have hclassK : ∀ a : K, IsInvolution a → a ∈ involutionPointClass zK := by
    intro a ha
    have haG : IsInvolution (a : G) :=
      ⟨fun h1 => ha.ne_one (Subtype.ext h1), congrArg Subtype.val ha.sq_eq_one⟩
    obtain ⟨t, ht⟩ := (hclass a.val).mp ⟨a.property, haG⟩
    exact ⟨⟨t.val, hTK t.property⟩, Subtype.ext ht⟩
  have hNinternal : N = (Subgroup.normalizer (R : Set G)).subgroupOf K := by
    rw [← hRimage]
    symm
    change (Subgroup.normalizer (RK.map K.subtype : Set G)).comap K.subtype = N
    rw [Subgroup.comap_normalizer_eq_of_le_range (Subgroup.map_le_range K.subtype RK),
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  have hsup : W ⊔ N = ⊤ := by
    apply top_le_iff.mp
    intro k _
    have hk : (k : G) ∈
        (W.map K.subtype : Set G) * (K ⊓ Subgroup.normalizer (R : Set G) : Set G) := by
      rw [← hprod]
      exact k.property
    obtain ⟨w, hw, n, hn, hmul⟩ := Set.mem_mul.mp hk
    obtain ⟨wK, hwK, hww⟩ := hw
    let nK : K := ⟨n, hn.1⟩
    have hnK : nK ∈ N := by rw [hNinternal]; exact hn.2
    have heq : wK * nK = k := by
      apply Subtype.ext
      change (wK : G) * n = (k : G)
      change (wK : G) = w at hww
      rw [hww]
      exact hmul
    rw [← heq]
    exact (W ⊔ N).mul_mem ((le_sup_left : W ≤ W ⊔ N) hwK)
      ((le_sup_right : N ≤ W ⊔ N) hnK)
  obtain ⟨wK, hwK, hsN, hsA, hsnoncentral, _hsinv, hNs, _hNclass, _hSylowTwo⟩ :=
    OddKernelNormalizerTransfer.odd_kernel_normalizer_rank_and_noncentral_action_transfer
      p hp hpodd hrankK zK hzKi hclassK W hWodd CFSG.pPrimeCore_coprime_card
      S RK hRKQ hRKchar hsup AK hAKQ hAKz hAKnoncentral
  let w := wK.val
  let sK := rightConjugateElem zK wK
  let NG := N.map K.subtype
  have hw : w ∈ W.map K.subtype := Subgroup.mem_map.mpr ⟨wK, hwK, rfl⟩
  have hwE : w ∈ triplePointStabilizer H z beta := hWE hw
  have hNR : NG ≤ Subgroup.normalizer (R : Set G) := by
    rw [← hRimage]
    exact Subgroup.le_normalizer_map K.subtype
  have hsR : rightConjugateElem z w ∈ Subgroup.normalizer (R : Set G) :=
    hNR (Subgroup.mem_map_of_mem K.subtype hsN)
  have hsAG : rightConjugateElem z w ∈ Subgroup.normalizer (A : Set G) := by
    rw [← hAKimage]
    exact Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hsA)
  have hsnoncentralG : ¬ A ≤ Subgroup.centralizer ({rightConjugateElem z w} : Set G) := by
    intro hcent
    apply hsnoncentral
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hcent ha)))
  have hclassimage : K.subtype '' conjugacyWithin N sK =
      conjugacyWithin NG (sK : G) := by
    have hh := LocalTheta.subgroup_class_image K NG (Subgroup.map_subtype_le _) sK.property
    have hsub : NG.subgroupOf K = N :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [hsub] at hh
    exact hh
  have hhullimage : (Subgroup.closure (conjugacyWithin N sK)).map K.subtype =
      Subgroup.closure (conjugacyWithin NG (rightConjugateElem z w)) := by
    rw [MonoidHom.map_closure, hclassimage]
    rfl
  have hNsG : 2 ≤ CFSG.Open.pRank 2
      (Subgroup.closure (conjugacyWithin NG (rightConjugateElem z w))) := by
    have hh := pRank_eq_of_subgroup_equiv 2 Nat.prime_two
      (Subgroup.closure (conjugacyWithin N sK))
      ((Subgroup.closure (conjugacyWithin N sK)).map K.subtype)
      ((Subgroup.closure (conjugacyWithin N sK)).equivMapOfInjective
        K.subtype K.subtype_injective)
    rw [hhullimage] at hh
    exact hNs.trans_eq hh
  have hadm1 := admissible_of_kernel_transfer H z beta p X A v hadm R NG hRne hRJ
    hvR hAR hNR w hwE hsR hsAG hsnoncentralG hNsG
  let g := w⁻¹
  let f := MulAut.conj g⁻¹
  let Q1 := rightConjugate QG g
  let R1 := rightConjugate R g
  have hgB : g ∈ pairPointStabilizer H beta :=
    (pairPointStabilizer H beta).inv_mem hwE.1
  have hJnormal : ((pairOddCore H beta).subgroupOf (pairPointStabilizer H beta)).Normal := by
    change (((CFSG.oddCore (pairPointStabilizer H beta)).map
      (pairPointStabilizer H beta).subtype).comap
        (pairPointStabilizer H beta).subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective (pairPointStabilizer H beta).subtype_injective]
    infer_instance
  let : ((pairOddCore H beta).subgroupOf (pairPointStabilizer H beta)).Normal := hJnormal
  have hgJ : g ∈ Subgroup.normalizer (pairOddCore H beta : Set G) := by
    have hJB : pairOddCore H beta ≤ pairPointStabilizer H beta :=
      Subgroup.map_subtype_le _
    exact Subgroup.le_normalizer_of_normal_subgroupOf hJB hgB
  have hJg : rightConjugate (pairOddCore H beta) g = pairOddCore H beta :=
    rightConjugate_eq_self_of_mem_normalizer hgJ
  have hQ1J : Q1 ≤ pairOddCore H beta := by
    have hh := Subgroup.map_mono (f := f.toMonoidHom) hQJ
    change Q1 ≤ rightConjugate (pairOddCore H beta) g at hh
    rwa [hJg] at hh
  have hR1Q1 : R1 ≤ Q1 := Subgroup.map_mono hRQ
  have hfker : Nat.Coprime p (Nat.card f.toMonoidHom.ker) := by
    rw [MonoidHom.ker_eq_bot _ f.injective, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hR1ZJ : R1 = (orderZJ Q1).map Q1.subtype :=
    LocalTheta.orderZJ_image_of_coprime_kernel hp f.toMonoidHom hfker QG hQp
  have hR1char : (R1.subgroupOf Q1).Characteristic := by
    rw [hR1ZJ]
    change (((orderZJ Q1).map Q1.subtype).comap Q1.subtype).Characteristic
    rw [Subgroup.comap_map_eq_self_of_injective Q1.subtype_injective]
    exact primeComplementGrowth_order_zj_characteristic
  have hQ1ne : Q1 ≠ ⊥ := by
    intro hbot
    exact hQne ((Subgroup.map_eq_bot_iff_of_injective _ f.injective).mp hbot)
  have hQ1card : Nat.card Q1 = primePart p (Nat.card T) := by
    rw [show Q1 = QG.map f.toMonoidHom from rfl,
      Subgroup.card_map_of_injective f.injective]
    exact sylow_map_card_eq_primePart p T Q
  exact ⟨w, hw, hadm1, hQ1J, hR1Q1, hR1char, hQp.map f.toMonoidHom,
    CFSG.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersection.right_conjugate_mem_normalizer
      hvQ g, hR1ZJ, hQ1ne, hQ1card⟩

end CFSG.ShultStronglyClosedTI.StrictThetaGrowth
