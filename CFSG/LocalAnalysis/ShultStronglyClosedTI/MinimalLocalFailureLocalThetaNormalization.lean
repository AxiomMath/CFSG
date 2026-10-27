module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaCapture
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaZJ
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStability
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaNormalizerLift

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem local_theta_actual_normalization
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (X : Subgroup G) (hXH : X ≤ H) (hXne : X ≠ ⊥)
    (hXz : rightConjugate X z = X)
    (hescape : ¬ Subgroup.normalizer (X : Set G) ≤ H)
    (hrank : 2 ≤ CFSG.Open.pRank 2
      (Subgroup.closure (conjugacyWithin (Subgroup.normalizer (X : Set G)) z)))
    (beta : numeratorRightOrbit H (Subgroup.normalizer (X : Set G)) (rightCosetMk H 1))
    (hbeta : beta.val ≠ rightCosetMk H 1) {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (A0 : Subgroup G)
    (hA0T : A0 ≤ Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta.val)
    (hA0p : IsPGroup p A0) (hA0z : rightConjugate A0 z = A0)
    (hnoncentral : ¬ A0 ≤ Subgroup.centralizer ({z} : Set G)) :
    let Y := Subgroup.normalizer (X : Set G)
    let D := Y ⊓ pairPointStabilizer H beta.val
    let T := Y ⊓ pairOddCore H beta.val
    let U := T ⊔ minimalLocalFailurePairConfinementTheta p D
    let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
    let K := I ⊔ U
    let W := CFSG.pPrimeCore p K
    ∀ Q : Sylow p T,
      let QG := (Q : Subgroup T).map T.subtype
      let ZJ := (orderZJ QG).map QG.subtype
      (K : Set G) = (W.map K.subtype : Set G) *
        (K ⊓ Subgroup.normalizer (ZJ : Set G) : Set G) ∧
      ∃ w ∈ W.map K.subtype,
        rightConjugateElem z w ∈ Subgroup.normalizer (ZJ : Set G) ∧
        IsInvolution (rightConjugateElem z w) ∧
        rightConjugateElem z w ∈ conjugacyWithin (triplePointStabilizer H z beta.val) z := by
  let Y := Subgroup.normalizer (X : Set G)
  have hzY : z ∈ Y := invariant_subgroup_mem_normalizer hXz
  let zY : Y := ⟨z, hzY⟩
  let L := involutionPointHull zY
  let D := Y ⊓ pairPointStabilizer H beta.val
  let T := Y ⊓ pairOddCore H beta.val
  let U := T ⊔ minimalLocalFailurePairConfinementTheta p D
  let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
  let K := I ⊔ U
  let W := CFSG.pPrimeCore p K
  obtain ⟨S2, hzS2, hzcenter⟩ := h.central_sylow
  obtain ⟨_hDpoint, _hTD, _hTnormal, _hUD, _hUnormal, _hUodd, _hpart, _hSylowU,
    _hIpoint, _hInormal, hzI, _hKpoint, _hKnorm, _hIKnormal, _hgen, _hUprod, _hKprod⟩ :=
    local_theta_auxiliary_construction h.local_datum S2 hzS2 hzcenter Y hzY hescape
      beta hbeta hp
  obtain ⟨hsol, _hfour, htwo, _hclass, _himage⟩ :=
    local_theta_actual_structure h hcomm X hXH hXne hXz hescape hrank beta hbeta hp
  let : Group.IsSolvable K := hsol
  obtain ⟨hWodd, _hThetaW, hWconfined, _hpartK, hSylowK⟩ :=
    local_theta_actual_capture h hcomm X hXH hXne hXz hescape hrank beta hbeta hp hpodd
      A0 hA0T hA0p hA0z hnoncentral
  have hzK : z ∈ K := (le_sup_left : I ≤ K) hzI
  let zK : K := ⟨z, hzK⟩
  have hz : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).2,
      (orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).1⟩
  have hzKi : IsInvolution zK :=
    ⟨fun hz1 => hz.ne_one (congrArg Subtype.val hz1),
      Subtype.ext hz.sq_eq_one⟩
  have habelian : HasAbelianSylow 2 K := by
    intro S
    let : IsElementaryAbelian 2 (S : Subgroup K) := htwo _ S.isPGroup'
    infer_instance
  let q := QuotientGroup.mk' W
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hquotabelian : HasAbelianSylow 2 (K ⧸ W) :=
    habelian.mapSurjective q (QuotientGroup.mk'_surjective W)
  let : Fact p.Prime := ⟨hp⟩
  have hquotcore : CFSG.pPrimeCore p (K ⧸ W) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := K) (p := p)
  change ∀ Q : Sylow p T,
    let QG := (Q : Subgroup T).map T.subtype
    let ZJ := (orderZJ QG).map QG.subtype
    (K : Set G) = (W.map K.subtype : Set G) *
      (K ⊓ Subgroup.normalizer (ZJ : Set G) : Set G) ∧
    ∃ w ∈ W.map K.subtype,
      rightConjugateElem z w ∈ Subgroup.normalizer (ZJ : Set G) ∧
      IsInvolution (rightConjugateElem z w) ∧
      rightConjugateElem z w ∈ conjugacyWithin (triplePointStabilizer H z beta.val) z
  intro Q
  let QG := (Q : Subgroup T).map T.subtype
  let ZJ := (orderZJ QG).map QG.subtype
  obtain ⟨S, hSQ⟩ := hSylowK Q
  let SK := (S : Subgroup K)
  let ZJK := (orderZJ SK).map SK.subtype
  let QS := S.mapSurjective (QuotientGroup.mk'_surjective W)
  have hchar : ((orderZJ (QS : Subgroup (K ⧸ W))).map
      (QS : Subgroup (K ⧸ W)).subtype).Characteristic :=
    solvable_abelian_sylow_two_orderZJ_characteristic hp hpodd hquotabelian hquotcore QS
  have hqker : Nat.Coprime p (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pPrimeCore_coprime_card
  have hZJquot : ZJK.map q =
      (orderZJ (QS : Subgroup (K ⧸ W))).map (QS : Subgroup (K ⧸ W)).subtype :=
    orderZJ_image_of_coprime_kernel hp q hqker SK S.isPGroup'
  have hnormal : (ZJK.map q).Normal := by
    rw [hZJquot]
    let : ((orderZJ (QS : Subgroup (K ⧸ W))).map
      (QS : Subgroup (K ⧸ W)).subtype).Characteristic := hchar
    infer_instance
  have hKker : Nat.Coprime p (Nat.card K.subtype.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff K.subtype).mpr K.subtype_injective]
    simp
  have hZJambient : ZJK.map K.subtype = ZJ := by
    have hh := orderZJ_image_of_coprime_kernel hp K.subtype hKker SK S.isPGroup'
    change (S : Subgroup K).map K.subtype = QG at hSQ
    rwa [hSQ] at hh
  let M := Subgroup.normalizer (ZJK : Set K)
  have hMambient : M = (Subgroup.normalizer (ZJ : Set G)).subgroupOf K := by
    rw [← hZJambient]
    symm
    change (Subgroup.normalizer (ZJK.map K.subtype : Set G)).comap K.subtype = M
    rw [Subgroup.comap_normalizer_eq_of_le_range
      (Subgroup.map_le_range K.subtype ZJK),
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  have hprod : (K : Set G) = (W.map K.subtype : Set G) *
      (K ⊓ Subgroup.normalizer (ZJ : Set G) : Set G) := by
    ext g
    constructor
    · intro hg
      obtain ⟨w, hw, n, hn, hmul⟩ :=
        orderZJ_normal_complement_normalizer_product hp W
          CFSG.pPrimeCore_coprime_card SK S.isPGroup' hnormal (⟨g, hg⟩ : K)
      have hnG : n.val ∈ Subgroup.normalizer (ZJ : Set G) := by
        change n ∈ M at hn
        rw [hMambient] at hn
        exact hn
      exact Set.mem_mul.mpr ⟨w.val, Subgroup.mem_map.mpr ⟨w, hw, rfl⟩,
        n.val, ⟨n.property, hnG⟩, congrArg Subtype.val hmul⟩
    · rintro ⟨w, hw, n, hn, rfl⟩
      exact K.mul_mem ((Subgroup.map_subtype_le W) hw) hn.1
  obtain ⟨w, hw, hnorm, hwi⟩ := orderZJ_odd_normal_complement_involution hp W
    CFSG.pPrimeCore_coprime_card hWodd SK S.isPGroup' hnormal hzKi
  have hwG : w.val ∈ W.map K.subtype := Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
  have hnormG : rightConjugateElem z w.val ∈ Subgroup.normalizer (ZJ : Set G) := by
    change rightConjugateElem zK w ∈ M at hnorm
    rw [hMambient] at hnorm
    exact hnorm
  have hwiG : IsInvolution (rightConjugateElem z w.val) :=
    ⟨fun hs1 => hwi.ne_one (Subtype.ext hs1), congrArg Subtype.val hwi.sq_eq_one⟩
  have hwE : w.val ∈ triplePointStabilizer H z beta.val := (hWconfined hwG).2.1
  exact ⟨hprod, w.val, hwG, hnormG, hwiG, ⟨⟨w.val, hwE⟩, rfl⟩⟩

end CFSG.ShultStronglyClosedTI.LocalTheta
