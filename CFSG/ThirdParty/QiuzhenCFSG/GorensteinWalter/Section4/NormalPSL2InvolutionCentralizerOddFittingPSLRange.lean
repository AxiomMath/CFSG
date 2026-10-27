module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalPSL2ToPGammaL2Apply
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2WeakFittingFieldProjection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearFittingExtraction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FittingCentralizes
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.PGammaL2InnerReflectedTorusPComplementFixed
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.PSL2ReflectedTorusCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarCommute
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Odd Fitting subgroups in involution centralizers of normal `PSL₂` extensions

This is the generic semilinear core of Bender's Fact 1.10(ii).  It is stated
for a self-centralizing normal `PSL₂` subgroup and is independent of the
particular Section 4 maximal subgroup or normalizer.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- A normal odd nilpotent subgroup of an involution centralizer in a
self-centralizing normal `PSL₂(K)` extension has image in the canonical PSL
range of the normal-extension embedding. -/
public theorem normalPSL2_involutionCentralizer_oddFitting_image_le_pslRange
    {R : Type u} [Group R] [Finite R]
    (L : Subgroup R) [L.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : L ≃* PSL2 K)
    (hLcent : Subgroup.centralizer (L : Set R) = ⊥)
    (hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard))
    {t : R} (htL : t ∈ L) (ht : IsInvolution t)
    (P : Subgroup R)
    (hPleC : P ≤ Subgroup.centralizer ({t} : Set R))
    (hPnormal : IsNormalIn P (Subgroup.centralizer ({t} : Set R)))
    (hPodd : Odd (Nat.card P)) (hPnil : Group.IsNilpotent P) :
    P.map (normalPSL2ToPGammaL2 L K hK hcard e hsurj) ≤
      pGammaL2PSLRange K := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Fintype K := Fintype.ofFinite K
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun a : K ≃+* K => (a : K → K)) (by
      intro a b hab
      ext x
      exact congrFun hab x)
  let : Finite (PGammaL2 K) :=
    Finite.of_injective (fun x : PGammaL2 K => (x.left, x.right)) (by
      intro x y hxy
      exact SemidirectProduct.ext
        (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  let f : R →* PGammaL2 K := normalPSL2ToPGammaL2 L K hK hcard e hsurj
  have hfinj : Function.Injective f :=
    normalPSL2ToPGammaL2_injective L K hK hcard e hLcent hsurj
  let toPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)
  let i : PGL2 K →* PGammaL2 K := SemidirectProduct.inl
  let j : PSL2 K →* PGammaL2 K := i.comp toPGL
  have htoPGLinj : Function.Injective toPGL :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hiinj : Function.Injective i := SemidirectProduct.inl_injective
  have hjinj : Function.Injective j := hiinj.comp htoPGLinj
  let C : Subgroup R := Subgroup.centralizer ({t} : Set R)
  let A : Subgroup (PGammaL2 K) := C.map f
  let P0 : Subgroup (PGammaL2 K) := P.map f
  have hP0leA : P0 ≤ A := Subgroup.map_mono hPleC
  let N : Subgroup A := P0.subgroupOf A
  have hNnormal : N.Normal := by
    refine ⟨?_⟩
    intro n hn a
    have hn0 : (n : PGammaL2 K) ∈ P0 := Subgroup.mem_subgroupOf.mp hn
    rcases Subgroup.mem_map.mp hn0 with ⟨p0, hp0, hp0eq⟩
    rcases Subgroup.mem_map.mp a.2 with ⟨c0, hc0, hc0eq⟩
    apply Subgroup.mem_subgroupOf.mpr
    apply Subgroup.mem_map.mpr
    refine ⟨c0 * p0 * c0⁻¹, hPnormal.2 c0 hc0 p0 hp0, ?_⟩
    rw [map_mul, map_mul, map_inv, hc0eq, hp0eq]
    rfl
  let : N.Normal := hNnormal
  have hNcard : Nat.card N = Nat.card P0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP0leA).toEquiv
  have hP0card : Nat.card P0 = Nat.card P :=
    Subgroup.card_map_of_injective hfinj
  have hNodd : Odd (Nat.card N) := by rw [hNcard, hP0card]; exact hPodd
  have hNnil : Group.IsNilpotent N := by
    let eP : P ≃* P0 := Subgroup.equivMapOfInjective P f hfinj
    have hP0nil : Group.IsNilpotent P0 := by
      have : Group.IsNilpotent P := hPnil
      exact Group.nilpotent_of_mulEquiv (G := P) (G' := P0) eP
    have : Group.IsNilpotent P0 := hP0nil
    exact Group.nilpotent_of_mulEquiv (G := P0) (G' := N)
      (Subgroup.subgroupOfEquivOfLe hP0leA).symm
  let tL : L := ⟨t, htL⟩
  let tauP : PSL2 K := e tL
  let tauPGL : PGL2 K := toPGL tauP
  let tau : PGammaL2 K := f t
  have htLinv : IsInvolution tL := by
    constructor
    · intro h1
      exact ht.1 (congrArg Subtype.val h1)
    · apply Subtype.ext
      simpa using ht.2
  have htauPinv : IsInvolution tauP := by
    constructor
    · intro h1
      exact htLinv.1 (e.injective (by simpa [tauP] using h1))
    · simpa [tauP] using congrArg e htLinv.2
  have htauPGLinv : IsInvolution tauPGL := by
    constructor
    · intro h1
      exact htauPinv.1 (htoPGLinj (by simpa [tauPGL] using h1))
    · simpa [tauPGL, map_pow] using congrArg toPGL htauPinv.2
  have htauEq : tau = j tauP := by
    simpa [tau, tauP, tauPGL, j, i, toPGL, f, tL] using
      normalPSL2ToPGammaL2_apply_subtype L K hK hcard e hsurj tL
  have htauL : tau ∈ pGammaL2PSLRange K := by
    rw [htauEq]
    exact (mem_pGammaL2PSLRange_iff K (j tauP)).mpr ⟨tauP, rfl⟩
  have htauInv : IsInvolution tau := by
    constructor
    · intro h1
      exact ht.1 (hfinj (by simpa [tau] using h1))
    · simpa [tau, map_pow] using congrArg f ht.2
  have hAcent : A ≤ Subgroup.centralizer ({tau} : Set (PGammaL2 K)) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨c0, hc0, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change f c0 * f t = f t * f c0
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subgroup.mem_centralizer_singleton_iff.mp hc0)
  have hAcont : (Subgroup.centralizer ({tau} : Set (PGammaL2 K)) ⊓
      pGammaL2PSLRange K) ≤ A := by
    intro x hx
    rcases (mem_pGammaL2PSLRange_iff K x).mp hx.2 with ⟨y, hy⟩
    let l : L := e.symm y
    have hfl : f (l : R) = x := by
      calc
        f (l : R) = j (e l) := by
          simpa [f, j, i, toPGL] using
            normalPSL2ToPGammaL2_apply_subtype L K hK hcard e hsurj l
        _ = j y := by simp [l]
        _ = x := hy
    have hlC : (l : R) ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hfinj
      change f ((l : R) * t) = f (t * (l : R))
      rw [map_mul, map_mul, hfl]
      have hxcomm := Subgroup.mem_centralizer_singleton_iff.mp hx.1
      simpa [tau] using hxcomm
    exact Subgroup.mem_map.mpr ⟨(l : R), hlC, hfl⟩
  obtain ⟨T, s, hTcyc, htT, hsI, hsT, hsInv, hCT, hTeven, hTcard⟩ :=
    psl2_reflected_torus_card hK htauPinv
  let UPGL : Subgroup (PGL2 K) := T.map toPGL
  let U : Subgroup (PGammaL2 K) := UPGL.map i
  have hUPGLcyc : IsCyclic UPGL := by
    let eT : T ≃* UPGL := Subgroup.equivMapOfInjective T toPGL htoPGLinj
    exact (MulEquiv.isCyclic eT).mp hTcyc
  have hUcyc : IsCyclic U := by
    let eU : UPGL ≃* U := Subgroup.equivMapOfInjective UPGL i hiinj
    exact (MulEquiv.isCyclic eU).mp hUPGLcyc
  have hUPGLcard : Nat.card UPGL = Nat.card T :=
    Subgroup.card_map_of_injective htoPGLinj
  have hUcard : Nat.card U = Nat.card T := by
    rw [← hUPGLcard]
    exact Subgroup.card_map_of_injective hiinj
  have htauUPGL : tauPGL ∈ UPGL :=
    Subgroup.mem_map.mpr ⟨tauP, htT, rfl⟩
  have htauU : tau ∈ U := by
    rw [htauEq]
    exact Subgroup.mem_map.mpr ⟨tauPGL, htauUPGL, rfl⟩
  have hUlePSL : U ≤ pGammaL2PSLRange K := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
    rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
    exact (mem_pGammaL2PSLRange_iff K (j y)).mpr ⟨y, rfl⟩
  have hUleCent : U ≤ Subgroup.centralizer ({tau} : Set (PGammaL2 K)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hUcyc with ⟨a, ha⟩
    rcases ha ⟨x, hx⟩ with ⟨m, hm⟩
    rcases ha ⟨tau, htauU⟩ with ⟨n, hn⟩
    have hc : (⟨x, hx⟩ : U) * (⟨tau, htauU⟩ : U) =
        (⟨tau, htauU⟩ : U) * (⟨x, hx⟩ : U) := by
      calc
        (⟨x, hx⟩ : U) * (⟨tau, htauU⟩ : U) = a ^ m * a ^ n := by
          simp [hm, hn]
        _ = a ^ (m + n) := by rw [zpow_add]
        _ = a ^ (n + m) := by rw [add_comm]
        _ = a ^ n * a ^ m := by rw [zpow_add]
        _ = (⟨tau, htauU⟩ : U) * (⟨x, hx⟩ : U) := by
          simp [← hn, ← hm]
    exact congrArg Subtype.val hc
  have hUleC : U ≤ Subgroup.centralizer ({tau} : Set (PGammaL2 K)) ⊓
      pGammaL2PSLRange K := fun _ hx => ⟨hUleCent hx, hUlePSL hx⟩
  have hUnormA : IsNormalIn U A := by
    refine ⟨hUleC.trans hAcont, ?_⟩
    intro a ha x hx
    rcases Subgroup.mem_map.mp ha with ⟨c0, hc0, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨z, hzUPGL, hzx⟩
    rcases Subgroup.mem_map.mp hzUPGL with ⟨u, huT, hzu⟩
    let alphaL : L ≃* L := MulAut.conjNormal c0
    let alphaP : PSL2 K ≃* PSL2 K := MulAut.congr e alphaL
    have halpha_t : alphaP tauP = tauP := by
      dsimp [alphaP, tauP]
      rw [MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      change e (alphaL tL) = e tL
      apply congrArg e
      apply Subtype.ext
      change c0 * t * c0⁻¹ = t
      have hccomm := Subgroup.mem_centralizer_singleton_iff.mp hc0
      calc
        c0 * t * c0⁻¹ = (t * c0) * c0⁻¹ := by rw [hccomm]
        _ = t := by group
    let X : Subgroup (PSL2 K) := T.map alphaP.toMonoidHom
    have hXcyc : IsCyclic X := by
      let eX : T ≃* X := Subgroup.equivMapOfInjective T
        alphaP.toMonoidHom alphaP.injective
      exact (MulEquiv.isCyclic eX).mp hTcyc
    have htX : tauP ∈ X :=
      Subgroup.mem_map.mpr ⟨tauP, htT, by simp [halpha_t]⟩
    have hXcent : X ≤ Subgroup.centralizer ({tauP} : Set (PSL2 K)) := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨v, hv, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hvcomm : v * tauP = tauP * v := by
        rw [← Subgroup.mem_centralizer_singleton_iff]
        rw [hCT]
        exact (show T ≤ T ⊔ Subgroup.zpowers s from le_sup_left) hv
      have h := congrArg alphaP hvcomm
      simpa [map_mul, halpha_t] using h
    have hXleT : X ≤ T :=
      cyclic_subgroup_containing_involution_le_reflected_torus
        htauPinv T s hTcyc htT hsI hsT hsInv hCT hXcyc hXcent htX
    have halphau : alphaP u ∈ T :=
      hXleT (Subgroup.mem_map.mpr ⟨u, huT, rfl⟩)
    apply Subgroup.mem_map.mpr
    refine ⟨toPGL (alphaP u),
      Subgroup.mem_map.mpr ⟨alphaP u, halphau, rfl⟩, ?_⟩
    subst hzx
    subst hzu
    let l : L := e.symm u
    let al : L := alphaL l
    have hfl : f (l : R) = i (toPGL u) := by
      calc
        f (l : R) = i (toPGL (e l)) := by
          simpa [f, i, toPGL] using
            normalPSL2ToPGammaL2_apply_subtype L K hK hcard e hsurj l
        _ = i (toPGL u) := by simp [l]
    have hfal : f (al : R) = i (toPGL (alphaP u)) := by
      calc
        f (al : R) = i (toPGL (e al)) := by
          simpa [f, i, toPGL] using
            normalPSL2ToPGammaL2_apply_subtype L K hK hcard e hsurj al
        _ = i (toPGL (alphaP u)) := by rfl
    symm
    calc
      f c0 * i (toPGL u) * (f c0)⁻¹ =
          f c0 * f (l : R) * (f c0)⁻¹ := by rw [hfl]
      _ = f (c0 * (l : R) * c0⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = f (al : R) := by rfl
      _ = i (toPGL (alphaP u)) := hfal
  have hUnilp : Group.IsNilpotent U := by
    let : IsCyclic U := hUcyc
    let : CommGroup U := IsCyclic.commGroup
    infer_instance
  have hNker : N ≤ pGammaL2LinearKernel K A := by
    by_contra hnle
    have hproj : ∃ n : N, SemidirectProduct.rightHom (n : PGammaL2 K) ≠ 1 := by
      rcases SetLike.not_le_iff_exists.mp hnle with ⟨n, hnN, hnker⟩
      refine ⟨⟨n, hnN⟩, ?_⟩
      intro hright
      apply hnker
      rw [mem_pGammaL2LinearKernel_iff]
      simpa [pGammaL2FieldProjection] using hright
    obtain ⟨p, hp, hpodd, sigma, hsigord, Qp, hQpleF, hQpnormF, hQpp,
      a0, ha0Qp, ha0sigma, _ha0pow⟩ :=
      secondCase_fitting_fieldProjection_pElement A N hNodd hNnil hproj
    let : Fact p.Prime := ⟨hp⟩
    let U0U : Subgroup U := pPrimeCore p U
    let U0 : Subgroup (PGammaL2 K) := U0U.map U.subtype
    have hU0leU : U0 ≤ U := Subgroup.map_subtype_le U0U
    have hU0normU : IsNormalIn U0 U :=
      fstar_characteristic_subgroupOf_map_normal_in
        (pPrimeCore_characteristic (p := p) (G := U)) ⟨le_rfl, by
          intro a ha x hx
          exact U.mul_mem (U.mul_mem ha hx) (U.inv_mem ha)⟩
    have hU0normA : IsNormalIn U0 A :=
      fstar_characteristic_subgroupOf_map_normal_in
        (pPrimeCore_characteristic (p := p) (G := U)) hUnormA
    have hU0card : Nat.card U0 = Nat.card U0U :=
      Subgroup.card_map_of_injective U.subtype_injective
    have hU0cop : Nat.Coprime p (Nat.card U0) := by
      rw [hU0card]
      exact pPrimeCore_coprime_card (p := p) (G := U)
    have hU0sub : U0.subgroupOf U = U0U := by
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx) with
          ⟨y, hy, hxy⟩
        have : y = x := by
          apply U.subtype_injective
          exact hxy
        simpa [this] using hy
      · intro hx
        apply Subgroup.mem_subgroupOf.mpr
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hU0quot : IsPGroup p (↥U ⧸ U0.subgroupOf U) := by
      rw [hU0sub]
      have : Group.IsNilpotent U := hUnilp
      have hQnil : Group.IsNilpotent (U ⧸ pPrimeCore p U) :=
        Group.nilpotent_of_surjective (QuotientGroup.mk' (pPrimeCore p U))
          (QuotientGroup.mk'_surjective (pPrimeCore p U))
      have htopnil : Group.IsNilpotent
          (⊤ : Subgroup (U ⧸ pPrimeCore p U)) := by
        let : Group.IsNilpotent (U ⧸ pPrimeCore p U) := hQnil
        infer_instance
      have htopP : IsPGroup p (⊤ : Subgroup (U ⧸ pPrimeCore p U)) :=
        isPGroup_of_nilpotent_normal (⊤ : Subgroup (U ⧸ pPrimeCore p U))
          inferInstance htopnil (pPrimeCore_quotient_pPrimeCore_eq_bot p)
      exact htopP.of_equiv Subgroup.topEquiv
    let Fld := FixedPoints.subfield (Subgroup.zpowers sigma) K
    obtain ⟨hr, _hp3, hq⟩ := finiteField_primeOrder_fixedSubfield_data
      K hK sigma p hp hpodd hsigord
    have hKodd : Odd (Nat.card K) := by
      rcases hK with ⟨ell, n, hell, hellodd, hn, hKcard⟩
      rw [hKcard]
      exact hellodd.pow
    have hrOdd : Odd (Nat.card Fld) := by
      rcases Nat.even_or_odd (Nat.card Fld) with hrEven | hrOdd
      · exfalso
        have h2r : 2 ∣ Nat.card Fld := even_iff_two_dvd.mp hrEven
        have h2pow : 2 ∣ Nat.card Fld ^ p := dvd_pow h2r hp.ne_zero
        rw [← hq] at h2pow
        exact hKodd.not_two_dvd_nat h2pow
      · exact hrOdd
    have hUPGLeven : Even (Nat.card UPGL) := by rw [hUPGLcard]; exact hTeven
    have hUPGLhalf : Nat.card UPGL = (Nat.card K - 1) / 2 ∨
        Nat.card UPGL = (Nat.card K + 1) / 2 := by
      rcases hTcard with hminus | hplus
      · exact Or.inl (hUPGLcard.trans hminus)
      · exact Or.inr (hUPGLcard.trans hplus)
    have hUPGLinner : UPGL ≤ commutator (PGL2 K) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
      exact ⟨y, rfl⟩
    have hU0fixed : ∀ b0 : PGammaL2 K, b0 ∈ Qp →
        SemidirectProduct.rightHom b0 = sigma →
        (∃ k : ℕ, b0 ^ p ^ k = 1) →
        (∀ u : PGammaL2 K, u ∈ U0 → b0 * u * b0⁻¹ = u) →
        (Nat.card U = (Nat.card K - 1) / 2 ∧
            Nat.card U0 ∣ (Nat.card Fld - 1) / 2) ∨
          (Nat.card U = (Nat.card K + 1) / 2 ∧
            Nat.card U0 ∣ (Nat.card Fld + 1) / 2) := by
      intro b0 _hb0Qp hb0sigma _hb0pow hb0fix
      simpa [U, Fld] using
        pGammaL2_inner_reflected_torus_pComplement_fixed
          K hK hcard p hpodd sigma hsigord UPGL hUPGLcyc hUPGLinner
          hUPGLeven hUPGLhalf tauPGL htauUPGL htauPGLinv U0
          (by simpa [U, i] using hU0leU) b0 hb0sigma hb0fix
    apply hnle
    exact pGammaL2_weak_normal_nilpotent_odd_fieldProjection_trivial
      K hK hcard A tau htauL htauInv hAcent hAcont N hNodd hNnil
      p hpodd sigma hsigord Qp hQpleF hQpnormF hQpp
      ⟨a0, ha0Qp, ha0sigma⟩ U hUleC hUnormA hUcyc hUnilp U0
      hU0leU hU0normU hU0normA hU0cop hU0quot
      (Nat.card Fld) hr hrOdd hq hU0fixed
  intro x hx
  have hxA : x ∈ A := hP0leA hx
  have hxker : (⟨x, hxA⟩ : A) ∈ pGammaL2LinearKernel K A :=
    hNker (Subgroup.mem_subgroupOf.mpr hx)
  have hxodd : Odd (orderOf x) :=
    Odd.of_dvd_nat (by rw [hP0card]; exact hPodd)
      (Subgroup.orderOf_dvd_natCard P0 hx)
  exact pGammaL2_linearKernel_odd_order_mem_pslRange
    K hK A hxA hxker hxodd

end CFSG.GorensteinWalter
