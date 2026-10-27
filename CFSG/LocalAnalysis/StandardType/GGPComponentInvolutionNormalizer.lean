module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVPComp
public import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.RankThree.GroupTheory.PerfectSubnormalModNormal
public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
public import CFSG.Fischer.Aut.TwoPower
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import TauCeti.GroupTheory.DerivedCentralQuotient
public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open scoped commutatorElement

section Quotient

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem ggCentralizer_involution_le_normalizer_map
    {L : Subgroup H} (hL : CFSG.IsPComponent p L)
    (hOdd : Odd (Nat.card (CFSG.pPrimeCore p L)))
    (hZ : Odd (Nat.card (Subgroup.center (L ⧸ CFSG.pPrimeCore p L))))
    {r : H} (hrL : r ∈ L) (hr2 : orderOf r = 2) :
    (Subgroup.centralizer ({r} : Set H)).map (QuotientGroup.mk' (CFSG.pPrimeCore p H)) ≤
      Subgroup.normalizer ((L.map (QuotientGroup.mk' (CFSG.pPrimeCore p H)) :
        Subgroup (H ⧸ CFSG.pPrimeCore p H)) : Set (H ⧸ CFSG.pPrimeCore p H)) := by
  classical
  let O : Subgroup H := CFSG.pPrimeCore p H
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let Q : Subgroup L := CFSG.pPrimeCore p L
  let qL : L →* L ⧸ Q := QuotientGroup.mk' Q
  let C : Subgroup (H ⧸ O) := L.map q
  have hsub : L.IsSubnormal := hL.choose_spec.2.1
  have hC : CFSG.IsComponent C := by
    change CFSG.IsComponent (L.map (QuotientGroup.mk' (CFSG.pPrimeCore p H)))
    rw [hL.choose_spec.2.2.1]
    exact hL.choose_spec.1
  let e : (L ⧸ Q) ≃* C :=
    CFSG.ComponentClassification.CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage p L hsub
  have hqrC : q r ∈ C := Subgroup.mem_map_of_mem q hrL
  have hq2 : orderOf (qL ⟨r, hrL⟩) = 2 := by
    have hr2L : orderOf (⟨r, hrL⟩ : L) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hr2
    exact CFSG.ComponentClassification.UnbalancedLayer.orderOf_mk_eq_two hOdd hr2L
  have hnotcenter : qL ⟨r, hrL⟩ ∉ Subgroup.center (L ⧸ Q) := by
    intro hc
    have hdvd : 2 ∣ Nat.card (Subgroup.center (L ⧸ Q)) := by
      rw [← hq2]
      exact Subgroup.orderOf_dvd_natCard _ hc
    exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr hdvd)
  have hval : e (qL ⟨r, hrL⟩) = ⟨q r, hqrC⟩ := by
    apply Subtype.ext
    exact CFSG.ComponentClassification.CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage_mk
      p L hsub ⟨r, hrL⟩
  have hnotcenterC : (⟨q r, hqrC⟩ : C) ∉ Subgroup.center C := by
    rw [← hval]
    exact fun hc => hnotcenter ((MulEquivClass.apply_mem_center_iff e).mp hc)
  rintro y ⟨g, hg, rfl⟩
  have hgcomm : g * r = r * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hs : q g * q r = q r * q g := by
    rw [← map_mul, ← map_mul, hgcomm]
  have hxZ : q r ∉ Subgroup.centralizer (C : Set (H ⧸ O)) := by
    intro hx
    apply hnotcenterC
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hx y y.2
  have hcompOpen : CFSG.Open.IsComponentOf C ⊤ := (CFSG.isComponent_iff_open C).mp hC
  exact CFSG.AGLEmbedding.mem_normalizer_of_commute_of_isComponentOf hcompOpen hqrC hxZ hs

end Quotient

section Ambient

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem le_normalizer_of_mem_centralizer_involution_of_largeEvenPComponent
    {X A : Subgroup G} (hA : LargeEvenPComponent p X A)
    (hOdd : Odd (Nat.card (LargeEvenPPrimeCoreOf p A)))
    (hZ : Odd (Nat.card (Subgroup.center (A ⧸ CFSG.pPrimeCore p A))))
    {r : G} (hr : r ∈ A) (hr2 : orderOf r = 2) :
    X ⊓ Subgroup.centralizer ({r} : Set G) ≤ Subgroup.normalizer (A : Set G) := by
  classical
  have hApc : CFSG.IsPComponent p (A.subgroupOf X) :=
    (ggLargeEvenPComponent_iff p X A).mp hA |>.2
  let K : Subgroup X := A.subgroupOf X
  have hK : CFSG.IsPComponent p K := hApc
  have hOddA : Odd (Nat.card (CFSG.pPrimeCore p A)) := by
    rw [LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective A.subtype_injective] at hOdd
    simpa [LargeEvenPPrimeCore] using hOdd
  let eK : K ≃* A := Subgroup.subgroupOfEquivOfLe hA.1
  have hOddK : Odd (Nat.card (CFSG.pPrimeCore p K)) := by
    have hcard : Nat.card (CFSG.pPrimeCore p K) = Nat.card (CFSG.pPrimeCore p A) := by
      calc Nat.card (CFSG.pPrimeCore p K)
          = Nat.card ((CFSG.pPrimeCore p K).map eK.toMonoidHom) :=
            (Subgroup.card_map_of_injective eK.injective).symm
        _ = Nat.card (CFSG.pPrimeCore p A) := by rw [CFSG.pPrimeCore_map_iso]
    rw [hcard]
    exact hOddA
  have hZK : Odd (Nat.card (Subgroup.center (K ⧸ CFSG.pPrimeCore p K))) := by
    let eQK : (K ⧸ CFSG.pPrimeCore p K) ≃* (A ⧸ CFSG.pPrimeCore p A) :=
      QuotientGroup.congr (CFSG.pPrimeCore p K) (CFSG.pPrimeCore p A) eK
        (CFSG.pPrimeCore_map_iso p eK)
    have hcard : Nat.card (Subgroup.center (K ⧸ CFSG.pPrimeCore p K)) =
        Nat.card (Subgroup.center (A ⧸ CFSG.pPrimeCore p A)) :=
      Nat.card_congr (Subgroup.centerCongr eQK).toEquiv
    rw [hcard]
    exact hZ
  have hrX : r ∈ X := hA.1 hr
  have hrK : (⟨r, hrX⟩ : X) ∈ K := hr
  have hr2K : orderOf (⟨r, hrX⟩ : X) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hr2
  have hquot := ggCentralizer_involution_le_normalizer_map (H := X) (p := p) (L := K)
    hK hOddK hZK hrK hr2K
  intro g hg
  obtain ⟨hgX, hgC⟩ := hg
  have hcommX : (⟨g, hgX⟩ : X) ∈ Subgroup.centralizer ({⟨r, hrX⟩} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hgC
  have hnormC := hquot (Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pPrimeCore p X)) hcommX)
  have hnormK : (⟨g, hgX⟩ : X) ∈ Subgroup.normalizer (K : Set X) :=
    CFSG.ComponentClassification.UnbalancedLayer.mem_normalizer_of_map hK hnormC
  exact CFSG.RankThree.GroupTheory.mem_normalizer_of_mem_normalizer_subgroupOf hA.1 hnormK

end Ambient


section RootAction

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
variable {X A : Subgroup G}

@[expose] def ggPComponentRootKernelInA (p : ℕ) (A : Subgroup G) : Subgroup ↥A :=
  (Subgroup.center (↥A ⧸ CFSG.pPrimeCore p A)).comap
    (QuotientGroup.mk' (CFSG.pPrimeCore p A))

@[expose] def ggPComponentRootKernel (p : ℕ) (A : Subgroup G) : Subgroup G :=
  (ggPComponentRootKernelInA p A).map A.subtype

instance ggPComponentRootKernelInA_normal (p : ℕ) (A : Subgroup G) :
    (ggPComponentRootKernelInA p A).Normal :=
  (inferInstance : (Subgroup.center (↥A ⧸ CFSG.pPrimeCore p A)).Normal).comap
    (QuotientGroup.mk' (CFSG.pPrimeCore p A))

abbrev ggPComponentRootQuotient (p : ℕ) (A : Subgroup G) :=
  ↥A ⧸ ggPComponentRootKernelInA p A

abbrev ggPComponentRootInvolutionImage (p : ℕ) (A : Subgroup G) {r : G} (hr : r ∈ A) :
    ggPComponentRootQuotient p A :=
  QuotientGroup.mk' (ggPComponentRootKernelInA p A) ⟨r, hr⟩

abbrev ggPComponentRootImage (p : ℕ) (A : Subgroup G) (R : Subgroup G) :
    Subgroup (ggPComponentRootQuotient p A) :=
  (R.subgroupOf A).map (QuotientGroup.mk' (ggPComponentRootKernelInA p A))

instance ggPComponentRootKernelInA_characteristic (p : ℕ) (A : Subgroup G) :
    (ggPComponentRootKernelInA p A).Characteristic :=
  Subgroup.Characteristic.comap_quotient_mk (H := CFSG.pPrimeCore p A)
    (K := Subgroup.center (↥A ⧸ CFSG.pPrimeCore p A))
    (inferInstance : (Subgroup.center (↥A ⧸ CFSG.pPrimeCore p A)).Characteristic)

def ggPComponentRootTheta {N : Subgroup G} (hN : N ≤ Subgroup.normalizer (A : Set G)) :
    N →* MulAut (ggPComponentRootQuotient p A) :=
  (CFSG.FiveTransitive.CharacteristicAutomorphism.quotient (ggPComponentRootKernelInA p A)).comp
    ((Subgroup.normalizerMonoidHom A).comp (Subgroup.inclusion hN))

lemma ggPComponentRootTheta_apply_mk {N : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (A : Set G)) (n : N) (a : ↥A) :
    ggPComponentRootTheta (p := p) (A := A) hN n
        (QuotientGroup.mk' (ggPComponentRootKernelInA p A) a) =
      QuotientGroup.mk' (ggPComponentRootKernelInA p A)
        (⟨(n : G) * (a : G) * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp
          (hN n.2) (a : G)).mp a.2⟩ : ↥A) := by
  simp only [ggPComponentRootTheta, MonoidHom.comp_apply, Subgroup.inclusion,
    CFSG.FiveTransitive.CharacteristicAutomorphism.quotient_apply_mk]
  congr 1

lemma ggPComponentRootKernelInA_odd
    (hOdd : Odd (Nat.card (CFSG.Assembly.LargeEvenPPrimeCoreOf p A)))
    (hZ : Odd (Nat.card (Subgroup.center (↥A ⧸ CFSG.pPrimeCore p A)))) :
    Odd (Nat.card (ggPComponentRootKernelInA p A)) := by
  have hOddQ : Odd (Nat.card (CFSG.pPrimeCore p A)) := by
    rw [CFSG.Assembly.LargeEvenPPrimeCoreOf,
      Subgroup.card_map_of_injective A.subtype_injective] at hOdd
    simpa [CFSG.Assembly.LargeEvenPPrimeCore] using hOdd
  let Q : Subgroup ↥A := CFSG.pPrimeCore p A
  let Z : Subgroup (↥A ⧸ Q) := Subgroup.center (↥A ⧸ Q)
  let K : Subgroup ↥A := ggPComponentRootKernelInA p A
  let φ : K →* (↥A ⧸ Q) := (QuotientGroup.mk' Q).comp K.subtype
  have hker : φ.ker = Q.subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff (x : ↥A)).mp hx
    · intro hx
      exact (QuotientGroup.eq_one_iff (x : ↥A)).mpr hx
  have hrange : φ.range = Z := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hz
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Q z
      exact ⟨⟨a, hz⟩, rfl⟩
  let e : (K ⧸ φ.ker) ≃* Z :=
    (QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange)
  have hcardQuot : Nat.card (K ⧸ φ.ker) = Nat.card Z :=
    Nat.card_congr e.toEquiv
  rw [hker] at hcardQuot
  have hQK : Q ≤ K := by
    intro q hq
    change QuotientGroup.mk' Q q ∈ Z
    have h1 : (QuotientGroup.mk' Q) q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
    rw [h1]
    exact Subgroup.one_mem _
  have hcardSub : Nat.card (Q.subgroupOf K) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf K)
  rw [hcard, hcardQuot, hcardSub]
  exact hZ.mul hOddQ

lemma ggPComponentRootQuotient_center_eq_bot (hA : LargeEvenPComponent p X A) :
    Subgroup.center (ggPComponentRootQuotient p A) = ⊥ := by
  have hApc : CFSG.IsPComponent p (A.subgroupOf X) :=
    (ggLargeEvenPComponent_iff p X A).mp hA |>.2
  have hQqs : CFSG.IsQuasisimple (↥A ⧸ CFSG.pPrimeCore p A) :=
    ((ggPComponent_iff_data p hA.1).mp hApc).2.2
  let Q : Subgroup ↥A := CFSG.pPrimeCore p A
  let Z : Subgroup (↥A ⧸ Q) := Subgroup.center (↥A ⧸ Q)
  let K : Subgroup ↥A := ggPComponentRootKernelInA p A
  have hQK : Q ≤ K := by
    intro q hq
    change QuotientGroup.mk' Q q ∈ Z
    have h1 : (QuotientGroup.mk' Q) q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
    rw [h1]
    exact Subgroup.one_mem _
  have hmap : K.map (QuotientGroup.mk' Q) = Z :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q) Z
  let eS : ggPComponentRootQuotient p A ≃* (↥A ⧸ Q) ⧸ Z :=
    (QuotientGroup.quotientQuotientEquivQuotient (N := Q) (M := K) hQK).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hmap)
  haveI : IsSimpleGroup ((↥A ⧸ Q) ⧸ Z) := hQqs.2.1
  have hsimple : IsSimpleGroup (ggPComponentRootQuotient p A) := eS.isSimpleGroup
  have hnc : ¬ IsMulCommutative (ggPComponentRootQuotient p A) := by
    intro h
    have h' : IsMulCommutative ((↥A ⧸ Q) ⧸ Z) := by
      refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨a', rfl⟩ := eS.surjective a
      obtain ⟨b', rfl⟩ := eS.surjective b
      rw [← map_mul, ← map_mul]
      exact congrArg eS (h.is_comm.comm a' b')
    obtain ⟨a, b, hab⟩ := hQqs.2.2
    exact hab (h'.is_comm.comm a b)
  exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc


lemma ggPComponentRootTheta_eq_conj_mk {N : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (A : Set G)) (n : N) (hnA : (n : G) ∈ A) :
    ggPComponentRootTheta (p := p) (A := A) hN n =
      MulAut.conj (QuotientGroup.mk' (ggPComponentRootKernelInA p A)
        (⟨n, hnA⟩ : ↥A)) := by
  ext y
  refine Quotient.inductionOn y ?_
  intro a
  change ggPComponentRootTheta (p := p) (A := A) hN n
      (QuotientGroup.mk' (ggPComponentRootKernelInA p A) a) =
    MulAut.conj (QuotientGroup.mk' (ggPComponentRootKernelInA p A)
      (⟨n, hnA⟩ : ↥A)) (QuotientGroup.mk' (ggPComponentRootKernelInA p A) a)
  rw [ggPComponentRootTheta_apply_mk, MulAut.conj_apply]
  congr 1

lemma ggPComponentRootTheta_eq_one_mem_kernel
    (hA : LargeEvenPComponent p X A) {N : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (A : Set G)) (n : N) (hnA : (n : G) ∈ A)
    (hθ : ggPComponentRootTheta (p := p) (A := A) hN n = 1) :
    (n : G) ∈ ggPComponentRootKernel p A := by
  have hconj : MulAut.conj (QuotientGroup.mk' (ggPComponentRootKernelInA p A)
      (⟨n, hnA⟩ : ↥A)) = 1 := by
    rw [← ggPComponentRootTheta_eq_conj_mk hN n hnA]
    exact hθ
  have hcenter : QuotientGroup.mk' (ggPComponentRootKernelInA p A)
      (⟨n, hnA⟩ : ↥A) ∈
      Subgroup.center (ggPComponentRootQuotient p A) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : QuotientGroup.mk' (ggPComponentRootKernelInA p A) (⟨n, hnA⟩ : ↥A) * g *
        (QuotientGroup.mk' (ggPComponentRootKernelInA p A) (⟨n, hnA⟩ : ↥A))⁻¹ = g := by
      have := congrArg (fun τ : MulAut (ggPComponentRootQuotient p A) => τ g) hconj
      simpa [MulAut.conj_apply] using this
    calc g * QuotientGroup.mk' (ggPComponentRootKernelInA p A) (⟨n, hnA⟩ : ↥A) =
        (QuotientGroup.mk' (ggPComponentRootKernelInA p A) (⟨n, hnA⟩ : ↥A) * g *
          (QuotientGroup.mk' (ggPComponentRootKernelInA p A) (⟨n, hnA⟩ : ↥A))⁻¹) *
          QuotientGroup.mk' (ggPComponentRootKernelInA p A) (⟨n, hnA⟩ : ↥A) := by rw [h1]
      _ = QuotientGroup.mk' (ggPComponentRootKernelInA p A) (⟨n, hnA⟩ : ↥A) * g := by group
  have hbot : Subgroup.center (ggPComponentRootQuotient p A) = ⊥ :=
    ggPComponentRootQuotient_center_eq_bot hA
  rw [hbot] at hcenter
  have hx : QuotientGroup.mk' (ggPComponentRootKernelInA p A) (⟨n, hnA⟩ : ↥A) = 1 := by
    simpa using hcenter
  have hmem : (⟨n, hnA⟩ : ↥A) ∈ ggPComponentRootKernelInA p A :=
    (QuotientGroup.eq_one_iff (⟨n, hnA⟩ : ↥A)).mp hx
  exact Subgroup.mem_map.mpr ⟨⟨n, hnA⟩, hmem, rfl⟩

lemma ggPComponentRootTheta_mem_N_fixes
    {r : G} {N : Subgroup G} (hN : N ≤ Subgroup.normalizer (A : Set G))
    (hNdef : N = X ⊓ Subgroup.centralizer ({r} : Set G)) (hrA : r ∈ A) (n : N) :
    ggPComponentRootTheta (p := p) (A := A) hN n
        (ggPComponentRootInvolutionImage p A (r := r) hrA) =
      ggPComponentRootInvolutionImage p A (r := r) hrA := by
  rw [ggPComponentRootTheta_apply_mk]
  congr 1
  apply Subtype.ext
  have hnN : (n : G) ∈ X ⊓ Subgroup.centralizer ({r} : Set G) := by
    rw [← hNdef]
    exact n.2
  have hn : (n : G) * r = r * (n : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hnN.2
  calc (n : G) * r * (n : G)⁻¹ = r * (n : G) * (n : G)⁻¹ := by rw [hn]
    _ = r := by rw [mul_assoc, mul_inv_cancel, mul_one]

lemma ggPComponentRootTheta_innerAut_inf_fixAut_le_range
    {r : G} (hA : LargeEvenPComponent p X A)
    (hOdd : Odd (Nat.card (CFSG.Assembly.LargeEvenPPrimeCoreOf p A)))
    (hZ : Odd (Nat.card (Subgroup.center (↥A ⧸ CFSG.pPrimeCore p A))))
    {N : Subgroup G} (hN : N ≤ Subgroup.normalizer (A : Set G))
    (hNdef : N = X ⊓ Subgroup.centralizer ({r} : Set G)) (hrA : r ∈ A)
    (hr2 : orderOf r = 2) :
    CFSG.Fischer.innerAut (ggPComponentRootQuotient p A) ⊓
        CFSG.Fischer.fixAut (ggPComponentRootInvolutionImage p A (r := r) hrA) ≤
      (ggPComponentRootTheta (p := p) (A := A) hN).range := by
  intro α hα
  rw [Subgroup.mem_inf] at hα
  obtain ⟨hαInn, hαfix⟩ := hα
  let rb : ggPComponentRootQuotient p A := ggPComponentRootInvolutionImage p A (r := r) hrA
  have hcenter : Subgroup.center (ggPComponentRootQuotient p A) = ⊥ :=
    ggPComponentRootQuotient_center_eq_bot hA
  have hαcent : α ∈ Subgroup.centralizer ({MulAut.conj rb} : Set (MulAut (ggPComponentRootQuotient p A))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    ext x
    have hfix' : α rb = rb := hαfix
    calc α (rb * x * rb⁻¹) = α rb * α x * (α rb)⁻¹ := by simp
      _ = rb * α x * rb⁻¹ := by rw [hfix']
  have hInnerSol := CFSG.innerAut_inf_centralizer_conj hcenter rb
  have hInner : CFSG.Fischer.innerAut (ggPComponentRootQuotient p A) ⊓
      Subgroup.centralizer ({MulAut.conj rb} : Set (MulAut (ggPComponentRootQuotient p A))) =
      (Subgroup.centralizer ({rb} : Set (ggPComponentRootQuotient p A))).map
        (MulAut.conj : ggPComponentRootQuotient p A →* MulAut (ggPComponentRootQuotient p A)) := by
    simpa only [CFSG.Fischer.innerAut,
      CFSG.HardMathSupport.Solomon.LocalBalance.innerAut] using hInnerSol
  have hαMap : α ∈ (Subgroup.centralizer ({rb} : Set (ggPComponentRootQuotient p A))).map
      (MulAut.conj : ggPComponentRootQuotient p A →* MulAut (ggPComponentRootQuotient p A)) := by
    rw [← hInner]
    exact ⟨hαInn, hαcent⟩
  rcases Subgroup.mem_map.mp hαMap with ⟨x, hxCent, hxα⟩
  have hK0odd : Odd (Nat.card (ggPComponentRootKernelInA p A)) :=
    ggPComponentRootKernelInA_odd (A := A) hOdd hZ
  let rA : ↥A := ⟨r, hrA⟩
  have hr2A : rA * rA = 1 := by
    apply Subtype.ext
    have h : r ^ 2 = 1 := by
      rw [← hr2]
      exact pow_orderOf_eq_one r
    simpa [rA, pow_two] using h
  have hCmap := CFSG.ComponentClassification.UnbalancedLayer.map_centralizer_eq
    (H := ↥A) (R := ggPComponentRootKernelInA p A) hK0odd hr2A
  have hxCentA : x ∈ Subgroup.centralizer
      ({(QuotientGroup.mk' (ggPComponentRootKernelInA p A)) rA} :
        Set (ggPComponentRootQuotient p A)) := by
    change x ∈ Subgroup.centralizer ({rb} : Set (ggPComponentRootQuotient p A))
    exact hxCent
  have hxMap : x ∈ (Subgroup.centralizer ({rA} : Set ↥A)).map
      (QuotientGroup.mk' (ggPComponentRootKernelInA p A)) := by
    rw [hCmap]
    exact hxCentA
  rcases Subgroup.mem_map.mp hxMap with ⟨a, haCent, hax⟩
  let aG : G := (a : G)
  have haX : aG ∈ X := hA.1 a.2
  have haCentG : aG ∈ Subgroup.centralizer ({r} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp haCent)
  have haN : aG ∈ N := by
    rw [hNdef]
    exact ⟨haX, haCentG⟩
  let n : N := ⟨aG, haN⟩
  refine MonoidHom.mem_range.mpr ⟨n, ?_⟩
  have htheta : ggPComponentRootTheta (p := p) (A := A) hN n = MulAut.conj x := by
    ext y
    refine Quotient.inductionOn y ?_
    intro b
    change ggPComponentRootTheta (p := p) (A := A) hN n
        (QuotientGroup.mk' (ggPComponentRootKernelInA p A) b) =
      MulAut.conj x (QuotientGroup.mk' (ggPComponentRootKernelInA p A) b)
    rw [ggPComponentRootTheta_apply_mk, MulAut.conj_apply, ← hax]
    congr 1
  rw [htheta, hxα]


theorem commutator_eq_bot_of_largeEvenPComponent_rootAction
    {X A R U : Subgroup G} (hA : LargeEvenPComponent p X A)
    (hOdd : Odd (Nat.card (CFSG.Assembly.LargeEvenPPrimeCoreOf p A)))
    (hZ : Odd (Nat.card (Subgroup.center (↥A ⧸ CFSG.pPrimeCore p A))))
    (hRA : R ≤ A) [hRelem : IsElementaryAbelian 2 R]
    {r : G} (hrR : r ∈ R) (hr2 : orderOf r = 2)
    (hUN0 : U ≤ X ⊓ Subgroup.centralizer ({r} : Set G))
    (hUnormal0 : (U.subgroupOf (X ⊓ Subgroup.centralizer ({r} : Set G))).Normal)
    (hUtwo : IsPGroup 2 U)
    (hRoot : ∀ (T : Subgroup (MulAut (ggPComponentRootQuotient p A))),
      CFSG.Fischer.innerAut (ggPComponentRootQuotient p A) ≤ T →
      ∀ f : ↥(T ⊓ CFSG.Fischer.fixAut
          (ggPComponentRootInvolutionImage p A (r := r) (hRA hrR))),
        f ∈ CFSG.pCore 2 ↥(T ⊓ CFSG.Fischer.fixAut
          (ggPComponentRootInvolutionImage p A (r := r) (hRA hrR))) →
        ∀ x : ggPComponentRootQuotient p A,
          x ∈ ggPComponentRootImage p A R →
          (f : MulAut (ggPComponentRootQuotient p A)) x = x) :
    ⁅R, U⁆ = ⊥ := by
  classical
  let N : Subgroup G := X ⊓ Subgroup.centralizer ({r} : Set G)
  have hNdef : N = X ⊓ Subgroup.centralizer ({r} : Set G) := rfl
  have hUN : U ≤ N := hUN0
  have hUnormal : (U.subgroupOf N).Normal := hUnormal0
  have hrA : r ∈ A := hRA hrR
  have hNnormA : N ≤ Subgroup.normalizer (A : Set G) := by
    rw [hNdef]
    exact le_normalizer_of_mem_centralizer_involution_of_largeEvenPComponent hA hOdd hZ hrA hr2
  have hK0odd : Odd (Nat.card (ggPComponentRootKernelInA p A)) :=
    ggPComponentRootKernelInA_odd (A := A) hOdd hZ
  have hKambOdd : Odd (Nat.card (ggPComponentRootKernel p A)) := by
    change Odd (Nat.card ((ggPComponentRootKernelInA p A).map A.subtype))
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hK0odd
  have hRleX : R ≤ X := hRA.trans hA.1
  have hRcent : R ≤ Subgroup.centralizer ({r} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hRelem.is_comm.comm ⟨x, hx⟩ ⟨r, hrR⟩)
  have hRN : R ≤ N := by
    rw [hNdef]
    exact le_inf hRleX hRcent
  have hNnormU : N ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUN).mp hUnormal
  have hRnormU : R ≤ Subgroup.normalizer (U : Set G) := hRN.trans hNnormU
  have hcomm_le_U : ⁅R, U⁆ ≤ U :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hRnormU
  let θ : N →* MulAut (ggPComponentRootQuotient p A) :=
    ggPComponentRootTheta (p := p) (A := A) hNnormA
  let V : Subgroup (MulAut (ggPComponentRootQuotient p A)) := (U.subgroupOf N).map θ
  let T : Subgroup (MulAut (ggPComponentRootQuotient p A)) :=
    CFSG.Fischer.innerAut (ggPComponentRootQuotient p A) ⊔ V
  let rb : ggPComponentRootQuotient p A :=
    ggPComponentRootInvolutionImage p A (r := r) hrA
  have hUtwoN : IsPGroup 2 (U.subgroupOf N) := hUtwo.comap_subtype
  have hVtwo : IsPGroup 2 V := hUtwoN.map θ
  have hVleFix : V ≤ CFSG.Fischer.fixAut rb := by
    rintro v ⟨n, _hn, rfl⟩
    exact ggPComponentRootTheta_mem_N_fixes hNnormA hNdef hrA n
  have hVleT : V ≤ T := le_sup_right
  have hVleCT : V ≤ T ⊓ CFSG.Fischer.fixAut rb := le_inf hVleT hVleFix
  have hVleRange : V ≤ θ.range := by
    rintro v ⟨n, _hn, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨n, rfl⟩
  have hCTleRange : T ⊓ CFSG.Fischer.fixAut rb ≤ θ.range := by
    intro f hf
    rw [Subgroup.mem_inf] at hf
    obtain ⟨hfT, hffix⟩ := hf
    change f ∈ CFSG.Fischer.innerAut (ggPComponentRootQuotient p A) ⊔ V at hfT
    letI : (CFSG.Fischer.innerAut (ggPComponentRootQuotient p A)).Normal :=
      CFSG.Fischer.innerAut_normal
    obtain ⟨i, hiInn, v, hvV, hiv⟩ :=
      (Subgroup.mem_sup_of_normal_left
        (s := CFSG.Fischer.innerAut (ggPComponentRootQuotient p A)) (t := V)).mp hfT
    have hvfix : v rb = rb := hVleFix hvV
    have hifix : i rb = rb := by
      calc i rb = i (v rb) := by rw [hvfix]
        _ = (i * v) rb := rfl
        _ = f rb := by rw [hiv]
        _ = rb := hffix
    have hiRange : i ∈ θ.range :=
      ggPComponentRootTheta_innerAut_inf_fixAut_le_range hA hOdd hZ hNnormA hNdef hrA hr2
        ⟨hiInn, hifix⟩
    have hvRange : v ∈ θ.range := hVleRange hvV
    rw [← hiv]
    exact θ.range.mul_mem hiRange hvRange
  have hVnormalCT : (V.subgroupOf (T ⊓ CFSG.Fischer.fixAut rb)).Normal := by
    refine ⟨?conj_mem⟩
    intro v hv c
    rw [Subgroup.mem_subgroupOf] at hv
    rw [Subgroup.mem_subgroupOf]
    change (c : MulAut (ggPComponentRootQuotient p A)) * (v : MulAut (ggPComponentRootQuotient p A)) *
      (c : MulAut (ggPComponentRootQuotient p A))⁻¹ ∈ V
    have hcRange : (c : MulAut (ggPComponentRootQuotient p A)) ∈ θ.range := hCTleRange c.2
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp hcRange
    obtain ⟨u, hu, hθv⟩ := Subgroup.mem_map.mp hv
    rw [← hθv]
    change (c : MulAut (ggPComponentRootQuotient p A)) * θ u *
      (c : MulAut (ggPComponentRootQuotient p A))⁻¹ ∈ V
    rw [← hn]
    change θ n * θ u * (θ n)⁻¹ ∈ V
    refine Subgroup.mem_map.mpr ⟨n * u * n⁻¹, hUnormal.conj_mem u hu n, ?_⟩
    simp [map_mul, map_inv]
  have hVleCore : V.subgroupOf (T ⊓ CFSG.Fischer.fixAut rb) ≤
      CFSG.pCore 2 ↥(T ⊓ CFSG.Fischer.fixAut rb) := by
    refine le_sSup ?_
    exact ⟨hVnormalCT, hVtwo.comap_subtype⟩
  have hRootV : ∀ v ∈ V, ∀ x ∈ ggPComponentRootImage p A R, v x = x := by
    intro v hv x hx
    let f : ↥(T ⊓ CFSG.Fischer.fixAut rb) := ⟨v, hVleCT hv⟩
    have hfsub : f ∈ V.subgroupOf (T ⊓ CFSG.Fischer.fixAut rb) :=
      Subgroup.mem_subgroupOf.mpr hv
    have hfcore : f ∈ CFSG.pCore 2 ↥(T ⊓ CFSG.Fischer.fixAut rb) := hVleCore hfsub
    exact hRoot T le_sup_left f hfcore x hx
  have hcomm_le_K : ⁅R, U⁆ ≤ ggPComponentRootKernel p A := by
    refine Subgroup.commutator_le.mpr ?_
    intro r' hr' u hu
    have hr'A : r' ∈ A := hRA hr'
    have hr'N : r' ∈ N := hRN hr'
    have huN : u ∈ N := hUN hu
    have huNormA : u ∈ Subgroup.normalizer (A : Set G) := hNnormA huN
    have hconjA : u * r'⁻¹ * u⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp huNormA (r'⁻¹)).mp (A.inv_mem hr'A)
    have hcommA : ⁅r', u⁆ ∈ A := by
      rw [commutatorElement_def]
      simpa [mul_assoc] using A.mul_mem hr'A hconjA
    have hcommN : ⁅r', u⁆ ∈ N := by
      rw [commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hr'N huN) (N.inv_mem hr'N)) (N.inv_mem huN)
    let n : N := ⟨⁅r', u⁆, hcommN⟩
    have hvV : θ ⟨u, huN⟩ ∈ V :=
      Subgroup.mem_map.mpr ⟨⟨u, huN⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    have hxImage : ggPComponentRootInvolutionImage p A (r := r') hr'A ∈
        ggPComponentRootImage p A R :=
      Subgroup.mem_map.mpr ⟨⟨r', hr'A⟩, Subgroup.mem_subgroupOf.mpr hr', rfl⟩
    have hfixv : θ ⟨u, huN⟩
        (ggPComponentRootInvolutionImage p A (r := r') hr'A) =
        ggPComponentRootInvolutionImage p A (r := r') hr'A :=
      hRootV (θ ⟨u, huN⟩) hvV _ hxImage
    let rq : ggPComponentRootQuotient p A :=
      ggPComponentRootInvolutionImage p A (r := r') hr'A
    have hfixv' : θ ⟨u, huN⟩ rq = rq := hfixv
    have hcommute : θ ⟨r', hr'N⟩ * θ ⟨u, huN⟩ = θ ⟨u, huN⟩ * θ ⟨r', hr'N⟩ := by
      rw [ggPComponentRootTheta_eq_conj_mk hNnormA ⟨r', hr'N⟩ hr'A]
      ext x
      change MulAut.conj rq ((θ ⟨u, huN⟩) x) =
        (θ ⟨u, huN⟩) (MulAut.conj rq x)
      calc MulAut.conj rq ((θ ⟨u, huN⟩) x)
          = rq * (θ ⟨u, huN⟩) x * rq⁻¹ := rfl
        _ = (θ ⟨u, huN⟩) rq * (θ ⟨u, huN⟩) x * ((θ ⟨u, huN⟩) rq)⁻¹ := by rw [hfixv']
        _ = (θ ⟨u, huN⟩) (rq * x * rq⁻¹) := by simp [map_mul, map_inv]
        _ = (θ ⟨u, huN⟩) (MulAut.conj rq x) := rfl
    have hθone : θ n = 1 := by
      have hmap : θ ⁅(⟨r', hr'N⟩ : N), (⟨u, huN⟩ : N)⁆ =
          ⁅θ (⟨r', hr'N⟩ : N), θ (⟨u, huN⟩ : N)⁆ :=
        map_commutatorElement (f := θ) (⟨r', hr'N⟩ : N) (⟨u, huN⟩ : N)
      have hn : n = (⁅(⟨r', hr'N⟩ : N), (⟨u, huN⟩ : N)⁆ : N) := by
        apply Subtype.ext
        rfl
      have hmapn : θ n =
          ⁅θ (⟨r', hr'N⟩ : N), θ (⟨u, huN⟩ : N)⁆ := by
        rw [hn]
        exact hmap
      rw [hmapn]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcommute
    exact ggPComponentRootTheta_eq_one_mem_kernel hA hNnormA n hcommA hθone
  have hinf : U ⊓ ggPComponentRootKernel p A = ⊥ :=
    CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hUtwo hKambOdd
  have hXle : ⁅R, U⁆ ≤ U ⊓ ggPComponentRootKernel p A := le_inf hcomm_le_U hcomm_le_K
  rw [hinf] at hXle
  exact le_bot_iff.mp hXle

end RootAction

section RootActionTransport

private lemma mulAut_congr_apply_apply {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (f : MulAut S) (x : S) :
    (MulAut.congr e f) (e x) = e (f x) := by
  simp [MulAut.congr_apply]

private lemma innerAut_map_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') :
    (CFSG.Fischer.innerAut S).map (MulAut.congr e).toMonoidHom =
      CFSG.Fischer.innerAut S' := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨s, rfl⟩ := hb
    exact ⟨e s, by
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]⟩
  · rintro ⟨s, rfl⟩
    refine ⟨MulAut.conj (e.symm s), ⟨e.symm s, rfl⟩, ?_⟩
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]

private lemma fixAut_map_congr {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (r : S) :
    (CFSG.Fischer.fixAut r).map (MulAut.congr e).toMonoidHom =
      CFSG.Fischer.fixAut (e r) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hbr : b r = r := hb
    change (MulAut.congr e b) (e r) = e r
    rw [mulAut_congr_apply_apply, hbr]
  · intro ha
    have har : a (e r) = e r := ha
    refine ⟨(MulAut.congr e).symm a, ?_, ?_⟩
    · change ((MulAut.congr e).symm a) r = r
      apply e.injective
      change e (((MulAut.congr e).symm a) r) = e r
      rw [← mulAut_congr_apply_apply e ((MulAut.congr e).symm a) r]
      rw [MulEquiv.apply_symm_apply]
      exact har
    · exact MulEquiv.apply_symm_apply (MulAut.congr e) a

theorem pCore_transport_of_mulEquiv
    {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (R : Subgroup S) (r : S)
    (hNative : ∀ (T' : Subgroup (MulAut S')),
      CFSG.Fischer.innerAut S' ≤ T' →
      ∀ a : MulAut S',
        a ∈ CFSG.Assembly.pCoreOf 2 (T' ⊓ CFSG.Fischer.fixAut (e r)) →
        ∀ v : S', v ∈ R.map e.toMonoidHom → a v = v) :
    ∀ (T : Subgroup (MulAut S)),
      CFSG.Fischer.innerAut S ≤ T →
      ∀ f : ↥(T ⊓ CFSG.Fischer.fixAut r),
        f ∈ CFSG.pCore 2 ↥(T ⊓ CFSG.Fischer.fixAut r) →
        ∀ x : S, x ∈ R → (f : MulAut S) x = x := by
  intro T hInn f hf x hx
  let c : MulAut S ≃* MulAut S' := MulAut.congr e
  let T' : Subgroup (MulAut S') := T.map c.toMonoidHom
  have hInn' : CFSG.Fischer.innerAut S' ≤ T' := by
    rw [← innerAut_map_congr e]
    exact Subgroup.map_mono hInn
  let K : Subgroup (MulAut S) := T ⊓ CFSG.Fischer.fixAut r
  let K' : Subgroup (MulAut S') := T' ⊓ CFSG.Fischer.fixAut (e r)
  have hfix : Subgroup.map c.toMonoidHom (CFSG.Fischer.fixAut r) =
      CFSG.Fischer.fixAut (e r) := by
    simpa [c] using fixAut_map_congr e r
  have hKmap : K.map c.toMonoidHom = K' := by
    dsimp [K, K', T']
    rw [Subgroup.map_inf_eq _ _ _ c.injective]
    change Subgroup.map c.toMonoidHom T ⊓
        Subgroup.map c.toMonoidHom (CFSG.Fischer.fixAut r) =
      Subgroup.map c.toMonoidHom T ⊓ CFSG.Fischer.fixAut (e r)
    rw [hfix]
  let eK : ↥K ≃* ↥K' :=
    (Subgroup.equivMapOfInjective K c.toMonoidHom c.injective).trans
      (MulEquiv.subgroupCongr hKmap)
  have hfK' : eK f ∈ CFSG.pCore 2 ↥K' := by
    rw [← CFSG.pCore_map_iso 2 eK]
    exact Subgroup.mem_map.mpr ⟨f, hf, rfl⟩
  have hfAmbient : (eK f : MulAut S') ∈ CFSG.Assembly.pCoreOf 2 K' := by
    change (eK f : MulAut S') ∈ (CFSG.pCore 2 ↥K').map K'.subtype
    exact Subgroup.mem_map.mpr ⟨eK f, hfK', rfl⟩
  have hxmap : e x ∈ R.map e.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hact := hNative T' hInn' (eK f : MulAut S') hfAmbient (e x) hxmap
  have hcoe : (eK f : MulAut S') = c f := by
    change (((MulEquiv.subgroupCongr hKmap)
      ((Subgroup.equivMapOfInjective K c.toMonoidHom c.injective) f) : ↥K') :
        MulAut S') = c f
    rw [MulEquiv.subgroupCongr_apply]
    exact Subgroup.coe_equivMapOfInjective_apply K c.toMonoidHom c.injective f
  have hcongr : (eK f : MulAut S') (e x) = e ((f : MulAut S) x) := by
    rw [hcoe, mulAut_congr_apply_apply]
  exact e.injective (by rw [← hcongr, hact])

lemma ggPComponentRootInvolutionImage_mem
    {G : Type} [Group G] {p : ℕ} {A R : Subgroup G}
    (hRA : R ≤ A) {r : G} (hrR : r ∈ R) :
    ggPComponentRootInvolutionImage p A (r := r) (hRA hrR) ∈
      ggPComponentRootImage p A R := by
  rw [ggPComponentRootImage]
  exact Subgroup.mem_map.mpr ⟨⟨r, hRA hrR⟩, hrR, rfl⟩

lemma ggPComponentRootInvolutionImage_ne_one
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact (Nat.Prime p)] {A R : Subgroup G}
    (hOdd : Odd (Nat.card ↥(CFSG.Assembly.LargeEvenPPrimeCoreOf p A)))
    (hZ : Odd (Nat.card ↥(Subgroup.center (↥A ⧸ CFSG.pPrimeCore p ↥A))))
    (hRA : R ≤ A) {r : G} (hrR : r ∈ R) (hr2 : orderOf r = 2) :
    ggPComponentRootInvolutionImage p A (r := r) (hRA hrR) ≠ 1 := by
  have hKodd : Odd (Nat.card (ggPComponentRootKernelInA p A)) :=
    ggPComponentRootKernelInA_odd (A := A) hOdd hZ
  have hrA2 : orderOf (⟨r, hRA hrR⟩ : ↥A) = 2 := by
    simpa using hr2
  have hquot2 : orderOf (ggPComponentRootInvolutionImage p A (r := r) (hRA hrR)) = 2 := by
    simpa [ggPComponentRootInvolutionImage] using
      CFSG.ComponentClassification.UnbalancedLayer.orderOf_mk_eq_two
        (R := ggPComponentRootKernelInA p A) hKodd hrA2
  intro h1
  rw [h1, orderOf_one] at hquot2
  norm_num at hquot2

theorem hRoot_of_native
    {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (R : Subgroup S) (r : S) (R' : Subgroup S')
    (hRmap : R.map e.toMonoidHom = R')
    (hNative : ∀ (T' : Subgroup (MulAut S')),
      CFSG.Fischer.innerAut S' ≤ T' →
      ∀ a : MulAut S',
        a ∈ CFSG.Assembly.pCoreOf 2 (T' ⊓ CFSG.Fischer.fixAut (e r)) →
        ∀ v : S', v ∈ R' → a v = v) :
    ∀ (T : Subgroup (MulAut S)),
      CFSG.Fischer.innerAut S ≤ T →
      ∀ f : ↥(T ⊓ CFSG.Fischer.fixAut r),
        f ∈ CFSG.pCore 2 ↥(T ⊓ CFSG.Fischer.fixAut r) →
        ∀ x : S, x ∈ R → (f : MulAut S) x = x := by
  intro T hInn f hf x hx
  exact pCore_transport_of_mulEquiv e R r
    (by
      intro T' hInn' a ha v hv
      rw [hRmap] at hv
      exact hNative T' hInn' a ha v hv) T hInn f hf x hx

end RootActionTransport

end CFSG.StandardType
