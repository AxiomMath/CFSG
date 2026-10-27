module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinResidual
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang
public import CFSG.LieType.AlgebraicGroups.ZariskiClosureFrobenius
public import CFSG.LieType.AlgebraicGroups.RationalPointEndomorphism
public import CFSG.Mathlib.RingTheory.UnitOrderOf
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageBasic
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Core
public import CFSG.RankThree.Classical2.SLnFrobeniusFormFixed
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.LocalAnalysis.StandardType.GGTwE6ConnectedReflection
public import CFSG.LocalAnalysis.StandardType.GGTwE6ReflectionRadical
public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidInduced
public import CFSG.RankThree.PartOne.KE.SuzukiLangSp4Group
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyIdentityComponent
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.StandardType.TwE6FixedComponent

open CFSG.ComponentClassification.CatalogueBPrimeJoin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.AlgebraicGroups
open scoped commutatorElement MatrixGroups

theorem isPGroup_zpowers_of_pow_two_pow {X : Type*} [Group X] {g : X} {k : ℕ}
    (hg : g ^ (2 ^ k) = 1) : IsPGroup 2 (Subgroup.zpowers g) := by
  rintro ⟨x, m, rfl⟩
  refine ⟨k, Subtype.ext ?_⟩
  change (g ^ m) ^ (2 ^ k) = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

theorem mem_primeResidual_two_of_inverted {X : Type*} [Group X] {g e : X}
    (hg : IsPGroup 2 (Subgroup.zpowers g)) (he : e ^ 3 = 1) (hinv : g * e * g⁻¹ = e⁻¹) :
    e ∈ primeResidual 2 X := by
  have h1 : g ∈ primeResidual 2 X :=
    pSubgroup_le_residual 2 _ hg (Subgroup.mem_zpowers g)
  have h2 : e * g⁻¹ * e⁻¹ ∈ primeResidual 2 X := by
    have hP : IsPGroup 2 ((Subgroup.zpowers g).map (MulAut.conj e).toMonoidHom) := hg.map _
    exact pSubgroup_le_residual 2 _ hP
      ⟨g⁻¹, inv_mem (Subgroup.mem_zpowers g), rfl⟩
  have hprod := mul_mem h1 h2
  have heq : g * (e * g⁻¹ * e⁻¹) = e := by
    calc g * (e * g⁻¹ * e⁻¹) = (g * e * g⁻¹) * e⁻¹ := by group
      _ = e⁻¹ * e⁻¹ := by rw [hinv]
      _ = e⁻¹ * e⁻¹ * e ^ 3 := by rw [he, mul_one]
      _ = e := by group
  rwa [heq] at hprod

theorem primeResidual_two_eq_of_normal_quasisimple {X : Type*} [Group X] [Finite X]
    {N : Subgroup X} [N.Normal] (hN : CFSG.IsQuasisimple N) (hodd : Odd N.index)
    {t : X} (htN : t ∈ N) (ht : IsPGroup 2 (Subgroup.zpowers t))
    (htc : ∃ n ∈ N, t * n ≠ n * t) : primeResidual 2 X = N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm
    (primeResidual_le_normal_of_coprime_index 2 N (Nat.coprime_two_left.mpr hodd)) ?_
  have hRn : (primeResidual 2 X).Normal := by
    have := primeResidual_characteristic 2 X
    infer_instance
  have hRN : ((primeResidual 2 X).subgroupOf N).Normal := Subgroup.Normal.subgroupOf hRn N
  have htR : t ∈ primeResidual 2 X := pSubgroup_le_residual 2 _ ht (Subgroup.mem_zpowers t)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hN hRN with h | h
  · intro x hx
    have hx' : (⟨x, hx⟩ : N) ∈ (primeResidual 2 X).subgroupOf N := by rw [h]; trivial
    exact hx'
  · exfalso
    obtain ⟨n, hn, hne⟩ := htc
    have htZ : (⟨t, htN⟩ : N) ∈ Subgroup.center N := h htR
    exact hne (congrArg Subtype.val ((Subgroup.mem_center_iff.mp htZ) ⟨n, hn⟩)).symm

theorem three_dvd_card_primeResidual_two_of_inverted {X : Type*} [Group X] [Finite X]
    {g e : X} (hg : IsPGroup 2 (Subgroup.zpowers g)) (he1 : e ≠ 1) (he : e ^ 3 = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) : 3 ∣ Nat.card (primeResidual 2 X) := by
  have hmem := mem_primeResidual_two_of_inverted hg he hinv
  have hord : orderOf e = 3 := orderOf_eq_prime he he1
  have hdvd := Subgroup.orderOf_dvd_natCard (primeResidual 2 X) hmem
  rwa [hord] at hdvd


theorem mem_center_of_map_commute {G D : Type*} [Group G] [Group D]
    (hDperf : Group.IsPerfect D) {Kc : Subgroup G} (ι : D →* G) (hιK : ∀ y, ι y ∈ Kc)
    (hιker : ι.ker ≤ Subgroup.center D) {x : D} (hx : ∀ y ∈ Kc, ι x * y = y * ι x) :
    x ∈ Subgroup.center D := by
  rw [← CFSG.LocalCores.comap_center_eq_of_perfect hDperf
    (QuotientGroup.mk' (Subgroup.center D)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])]
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro yb
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center D) yb
  have hc : ⁅x, y⁆ ∈ Subgroup.center D := by
    apply hιker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hx (ι y) (hιK y)
  have h1 : (QuotientGroup.mk' (Subgroup.center D)) ⁅x, y⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hc
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem exists_odd_pow_eq_one_of_centralProduct_central
    {G D : Type*} [Group G] [Group D]
    {Kc Zc : Subgroup G} (hDperf : Group.IsPerfect D) [Finite (Subgroup.center D)]
    (hZD : Odd (Nat.card (Subgroup.center D)))
    (ι : D →* G) (hιK : ∀ B, ι B ∈ Kc) (hιker : ι.ker ≤ Subgroup.center D)
    (hZcent : ∀ z ∈ Zc, ∀ y ∈ Kc, z * y = y * z)
    (hZodd : ∀ z ∈ Zc, ∃ m, Odd m ∧ z ^ m = 1)
    (hKdec : ∀ x ∈ Kc, ∃ z ∈ Zc, ∃ B : D, x = z * ι B)
    {x : G} (hx : x ∈ Kc) (hxc : ∀ y ∈ Kc, x * y = y * x) :
    ∃ m, Odd m ∧ x ^ m = 1 := by
  obtain ⟨z, hz, B, rfl⟩ := hKdec x hx
  have hBc : B ∈ Subgroup.center D := mem_center_of_map_commute hDperf ι hιK hιker
    (fun y hy => by
      have hzy := hZcent z hz y hy
      have hxcomm := hxc y hy
      calc
        ι B * y = z⁻¹ * (z * ι B * y) := by group
        _ = z⁻¹ * (y * (z * ι B)) := by rw [hxcomm]
        _ = z⁻¹ * ((y * z) * ι B) := by group
        _ = z⁻¹ * ((z * y) * ι B) := by rw [← hzy]
        _ = y * ι B := by group)
  have hBD : B ^ Nat.card (Subgroup.center D) = 1 := by
    have h : (⟨B, hBc⟩ : Subgroup.center D) ^ Nat.card (Subgroup.center D) = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h
  obtain ⟨m, hm, hzm⟩ := hZodd z hz
  have hc : Commute z (ι B) := hZcent z hz _ (hιK B)
  refine ⟨m * Nat.card (Subgroup.center D), hm.mul hZD, ?_⟩
  rw [hc.mul_pow, pow_mul, hzm, one_pow, mul_comm m, pow_mul, ← map_pow, hBD, map_one,
    one_pow, mul_one]

theorem primeResidual_two_eq_isogenyImage
    {G : Type*} [Group G] {Kc Rg Zc : Subgroup G} {F : G →* G}
    (hRg : ∀ x ∈ Kc, x ∈ Rg ↔ F x = x) [Finite ↥(Kc ⊓ Rg)]
    {D : Type*} [Group D] (hDperf : Group.IsPerfect D) [Finite (Subgroup.center D)]
    (hZD : Odd (Nat.card (Subgroup.center D)))
    (ι : D →* G) (hιK : ∀ x, ι x ∈ Kc) (hιker : ι.ker ≤ Subgroup.center D)
    (σ : D →* D) (hFι : ∀ x, F (ι x) = ι (σ x))
    (hDσ : CFSG.IsQuasisimple (σ.eqLocus (MonoidHom.id D)))
    (hZcent : ∀ z ∈ Zc, ∀ x ∈ Kc, z * x = x * z) (hFZ : ∀ z ∈ Zc, F z ∈ Zc)
    (hZodd : ∀ z ∈ Zc, ∃ m, Odd m ∧ z ^ m = 1)
    (hKdec : ∀ k ∈ Kc, ∃ z ∈ Zc, ∃ B : D, k = z * ι B)
    {e g : G} (heK : e ∈ Kc) (heF : e ∈ Rg) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hgK : g ∈ Kc) (hgF : g ∈ Rg) {k : ℕ} (hg2 : g ^ (2 ^ k) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) :
    (primeResidual 2 ↥(Kc ⊓ Rg)).map (Kc ⊓ Rg).subtype =
      (σ.eqLocus (MonoidHom.id D)).map ι := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set KF : Subgroup G := Kc ⊓ Rg with hKF
  set Dσ : Subgroup D := σ.eqLocus (MonoidHom.id D) with hDσdef
  set I : Subgroup G := Dσ.map ι with hIdef
  have hIKF : I ≤ KF := by
    rintro _ ⟨A, hA, rfl⟩
    refine ⟨hιK A, (hRg _ (hιK A)).mpr ?_⟩
    rw [hFι]
    exact congrArg ι hA
  have hdec : ∀ x ∈ KF, ∃ z ∈ Zc, ∃ B : D, x = z * ι B ∧ σ B * B⁻¹ ∈ Subgroup.center D := by
    intro x hx
    obtain ⟨z, hz, B, rfl⟩ := hKdec x hx.1
    refine ⟨z, hz, B, rfl, mem_center_of_map_commute hDperf ι hιK hιker ?_⟩
    have hFx : F (z * ι B) = z * ι B := (hRg _ hx.1).mp hx.2
    rw [map_mul, hFι] at hFx
    have heq : ι (σ B * B⁻¹) = (F z)⁻¹ * z := by
      rw [map_mul, map_inv]
      calc ι (σ B) * (ι B)⁻¹ = (F z)⁻¹ * (F z * ι (σ B)) * (ι B)⁻¹ := by group
        _ = (F z)⁻¹ * (z * ι B) * (ι B)⁻¹ := by rw [hFx]
        _ = (F z)⁻¹ * z := by group
    intro y hy
    rw [heq]
    exact hZcent _ (mul_mem (inv_mem (hFZ z hz)) hz) y hy
  let N : Subgroup ↥KF := I.subgroupOf KF
  have hNnormal : N.Normal := by
    constructor
    intro n hn x
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨A, hA, hAn⟩ := hn
    obtain ⟨z, hz, B, hxB, hc⟩ := hdec x x.2
    have hσA : σ A = A := hA
    have hcc := Subgroup.mem_center_iff.mp hc
    refine ⟨B * A * B⁻¹, ?_, ?_⟩
    · change σ (B * A * B⁻¹) = B * A * B⁻¹
      have hσB : σ B = (σ B * B⁻¹) * B := by group
      rw [map_mul, map_mul, map_inv, hσA, hσB]
      calc σ B * B⁻¹ * B * A * (σ B * B⁻¹ * B)⁻¹
          = (σ B * B⁻¹) * (B * A * B⁻¹) * (σ B * B⁻¹)⁻¹ := by group
        _ = (B * A * B⁻¹) * (σ B * B⁻¹) * (σ B * B⁻¹)⁻¹ := by rw [hcc (B * A * B⁻¹)]
        _ = B * A * B⁻¹ := by group
    · have hconj : ι (B * A * B⁻¹) ∈ Kc := hιK _
      change ι (B * A * B⁻¹) = (x : G) * (n : G) * (x : G)⁻¹
      rw [hxB, ← hAn]
      have hz' := hZcent z hz _ hconj
      rw [map_mul, map_mul, map_inv] at hz' ⊢
      calc ι B * ι A * (ι B)⁻¹ = z * (ι B * ι A * (ι B)⁻¹) * z⁻¹ := by
            rw [hz']
            group
        _ = z * ι B * ι A * (z * ι B)⁻¹ := by group
  have hpow : ∀ x : ↥KF, ∃ m, Odd m ∧ x ^ m ∈ N := by
    intro x
    obtain ⟨z, hz, B, hxB, hc⟩ := hdec x x.2
    obtain ⟨mz, hmz, hzm⟩ := hZodd z hz
    set mZ := Nat.card (Subgroup.center D) with hmZ
    have hcZ : (σ B * B⁻¹) ^ mZ = 1 := by
      have h : (⟨σ B * B⁻¹, hc⟩ : Subgroup.center D) ^ mZ = 1 := pow_card_eq_one'
      exact congrArg Subtype.val h
    have hcB : Commute (σ B * B⁻¹) B := (Subgroup.mem_center_iff.mp hc B).symm
    have hzB : Commute z (ι B) := hZcent z hz (ι B) (hιK B)
    refine ⟨mZ * mz, hZD.mul hmz, ?_⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨B ^ (mZ * mz), ?_, ?_⟩
    · change σ (B ^ (mZ * mz)) = B ^ (mZ * mz)
      have hσB : σ B = (σ B * B⁻¹) * B := by group
      rw [map_pow, hσB, hcB.mul_pow, pow_mul (σ B * B⁻¹) mZ mz, hcZ, one_pow, one_mul]
    · rw [Subgroup.coe_pow, hxB, hzB.mul_pow, map_pow, mul_comm mZ mz, pow_mul z mz mZ, hzm,
        one_pow, one_mul]
  have hodd : Odd N.index := by
    by_contra hne
    have h2 : 2 ∣ Nat.card (↥KF ⧸ N) := by
      rw [← Subgroup.index_eq_card]
      exact even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hne)
    obtain ⟨xb, hxb⟩ := exists_prime_orderOf_dvd_card' (p := 2) h2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    obtain ⟨m, hm, hxm⟩ := hpow x
    have hx1 : ((x : ↥KF ⧸ N)) ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hxm
    have hdvd := orderOf_dvd_of_pow_eq_one hx1
    rw [hxb] at hdvd
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hdvd)
  have hNq : CFSG.IsQuasisimple N := by
    have hI : CFSG.IsQuasisimple I := by
      have hker : (ι.comp Dσ.subtype).ker ≤ Subgroup.center Dσ := by
        intro A hA
        rw [Subgroup.mem_center_iff]
        intro A'
        have hAc : (A : D) ∈ Subgroup.center D := hιker hA
        exact Subtype.ext ((Subgroup.mem_center_iff.mp hAc) A')
      have h := CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_range_of_ker_le_center
        hDσ (ι.comp Dσ.subtype) hker
      have hrange : (ι.comp Dσ.subtype).range = I := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [hrange] at h
      exact h
    exact (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hIKF)).mpr hI
  have hg2' : IsPGroup 2 (Subgroup.zpowers (⟨g, hgK, hgF⟩ : ↥KF)) :=
    isPGroup_zpowers_of_pow_two_pow (k := k) (Subtype.ext hg2)
  have heO : (⟨e, heK, heF⟩ : ↥KF) ∈ primeResidual 2 ↥KF :=
    mem_primeResidual_two_of_inverted hg2' (Subtype.ext he3) (Subtype.ext hinv)
  have hgO : (⟨g, hgK, hgF⟩ : ↥KF) ∈ primeResidual 2 ↥KF :=
    pSubgroup_le_residual 2 _ hg2' (Subgroup.mem_zpowers _)
  have hle : primeResidual 2 ↥KF ≤ N :=
    primeResidual_le_normal_of_coprime_index 2 N (Nat.coprime_two_left.mpr hodd)
  have heq : primeResidual 2 ↥KF = N := by
    refine primeResidual_two_eq_of_normal_quasisimple hNq hodd (hle hgO) hg2'
      ⟨⟨e, heK, heF⟩, hle heO, ?_⟩
    intro hcomm
    have hc : g * e = e * g := congrArg Subtype.val hcomm
    have hee : e⁻¹ = e := by
      rw [← hinv]
      calc g * e * g⁻¹ = e * g * g⁻¹ := by rw [hc]
        _ = e := by group
    apply he1
    have h2 : e ^ 2 = 1 := by
      rw [pow_two]
      calc e * e = e * e⁻¹ := by rw [hee]
        _ = 1 := mul_inv_cancel e
    have h3 := he3
    calc e = e ^ 3 * (e ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  rw [heq]
  rw [Subgroup.map_subgroupOf_eq_of_le hIKF]


section Literal

open CFSG.HardMathSupport.Lang.E6Descent

variable {Ω : Type} [Field Ω] (Fr : Ω →+* Ω)
  (Hh : Subgroup (ModGL Tag.E6 Ω))

theorem mem_Rgrp_iff_of_mem_hypCentConn {x : ModGL Tag.E6 Ω}
    (hx : x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)))) :
    x ∈ TwistedDiag.Rgrp Ω Fr ↔ twistHom TwistTag.E6 Ω Fr x = x :=
  ⟨fun h => h.2, fun h => ⟨(closedIdentityComponent_le _ hx).1, h⟩⟩

theorem centralizer_le_normalizer_hypCentConnFixed :
    TwistedDiag.Rgrp Ω Fr ⊓ Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)) ≤
      Subgroup.normalizer ((closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
        Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr) :
          Set (ModGL Tag.E6 Ω)) := by
  intro x hx
  have hZ : x ∈ Subgroup.normalizer ((adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) : Set (ModGL Tag.E6 Ω)) := by
    apply Subgroup.inf_normalizer_le_normalizer_inf
    refine ⟨Subgroup.le_normalizer hx.1.1,
      Subgroup.le_normalizer hx.2⟩
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨normalizer_le_normalizer_closedIdentityComponent _ hZ,
      Subgroup.le_normalizer hx.1⟩

theorem centralizer_le_normalizer_jgeom :
    TwistedDiag.Rgrp Ω Fr ⊓ Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)) ≤
      Subgroup.normalizer ((primeResidual 2 ↥(closedIdentityComponent
        (adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓
          TwistedDiag.Rgrp Ω Fr)).map
            (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
              Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓
                TwistedDiag.Rgrp Ω Fr).subtype : Set (ModGL Tag.E6 Ω)) :=
  (centralizer_le_normalizer_hypCentConnFixed Fr Hh).trans
    (primeResidual_normalizer_le 2 (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr))

theorem mem_jgeom_of_two_pow_eq_one {g : ModGL Tag.E6 Ω}
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {k : ℕ} (hg2 : g ^ (2 ^ k) = 1) :
    g ∈ (primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype := by
  let KF := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
    Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr
  let gF : ↥KF := ⟨g, hgK, hgF⟩
  have hp : IsPGroup 2 (Subgroup.zpowers gF) :=
    isPGroup_zpowers_of_pow_two_pow (Subtype.ext hg2)
  exact ⟨gF, pSubgroup_le_residual 2 _ hp (Subgroup.mem_zpowers gF), rfl⟩

theorem three_dvd_card_jgeom
    [Finite ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)]
    {e g : ModGL Tag.E6 Ω}
    (heK : e ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (heF : e ∈ TwistedDiag.Rgrp Ω Fr) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {k : ℕ} (hg2 : g ^ (2 ^ k) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) :
    3 ∣ Nat.card ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype) := by
  rw [Subgroup.card_map_of_injective Subtype.val_injective]
  refine three_dvd_card_primeResidual_two_of_inverted (g := ⟨g, hgK, hgF⟩) (e := ⟨e, heK, heF⟩)
    (isPGroup_zpowers_of_pow_two_pow (k := k) (Subtype.ext hg2)) ?_ (Subtype.ext he3)
    (Subtype.ext hinv)
  intro h
  exact he1 (congrArg Subtype.val h)

theorem isQuasisimple_jgeom_of_isogeny
    [Finite ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)]
    {D : Type*} [Group D] (hDperf : Group.IsPerfect D) [Finite (Subgroup.center D)]
    (hZD : Odd (Nat.card (Subgroup.center D)))
    (ι : D →* ModGL Tag.E6 Ω)
    (hιK : ∀ x, ι x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hιker : ι.ker ≤ Subgroup.center D)
    (σ : D →* D) (hFι : ∀ x, twistHom TwistTag.E6 Ω Fr (ι x) = ι (σ x))
    (hDσ : CFSG.IsQuasisimple (σ.eqLocus (MonoidHom.id D)))
    {Zc : Subgroup (ModGL Tag.E6 Ω)}
    (hZcent : ∀ z ∈ Zc, ∀ x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))), z * x = x * z)
    (hFZ : ∀ z ∈ Zc, twistHom TwistTag.E6 Ω Fr z ∈ Zc)
    (hZodd : ∀ z ∈ Zc, ∃ m, Odd m ∧ z ^ m = 1)
    (hKdec : ∀ x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))), ∃ z ∈ Zc, ∃ B : D, x = z * ι B)
    {e g : ModGL Tag.E6 Ω}
    (heK : e ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (heF : e ∈ TwistedDiag.Rgrp Ω Fr) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {k : ℕ} (hg2 : g ^ (2 ^ k) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) :
    CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype) := by
  rw [primeResidual_two_eq_isogenyImage (fun x hx => mem_Rgrp_iff_of_mem_hypCentConn Fr Hh hx)
    hDperf hZD ι hιK hιker σ hFι hDσ hZcent hFZ hZodd hKdec heK heF he1 he3 hgK hgF hg2 hinv]
  have hker : (ι.comp (σ.eqLocus (MonoidHom.id D)).subtype).ker ≤
      Subgroup.center (σ.eqLocus (MonoidHom.id D)) := by
    intro A hA
    rw [Subgroup.mem_center_iff]
    intro A'
    have hAc : (A : D) ∈ Subgroup.center D := hιker hA
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hAc) A')
  have h := CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_range_of_ker_le_center
    hDσ (ι.comp (σ.eqLocus (MonoidHom.id D)).subtype) hker
  rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h

section RationalFrobenius

open CFSG.LieType.Chevalley


theorem twistHom_mem_hypCentConn
    {n : ℕ} {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = (2 ^ n) ^ 2) {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {Hh : Subgroup (ModGL TwistTag.E6.tag Ω)} (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    {x : ModGL TwistTag.E6.tag Ω}
    (hx : x ∈ closedIdentityComponent (adjointGroup TwistTag.E6.tag Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL TwistTag.E6.tag Ω)))) :
    twistHom TwistTag.E6 Ω Fr x ∈ closedIdentityComponent (adjointGroup TwistTag.E6.tag Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL TwistTag.E6.tag Ω))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap k Ω).injective 2
  have hFr' : Fr = iterateFrobenius Ω 2 n := RingHom.ext fun c => by
    rw [hFr, iterateFrobenius_def]
  have hF : ∀ y : ModGL TwistTag.E6.tag Ω, twistHom TwistTag.E6 Ω Fr y =
      frobTwistGL TwistTag.E6.tag Ω 2 n (diagramMap TwistTag.E6 Ω) y := by
    intro y
    rw [hFr']
    rfl
  have hZ : ∀ y ∈ adjointGroup TwistTag.E6.tag Ω ⊓ Subgroup.centralizer (Hh : Set (ModGL TwistTag.E6.tag Ω)),
      twistHom TwistTag.E6 Ω Fr y ∈ adjointGroup TwistTag.E6.tag Ω ⊓
        Subgroup.centralizer (Hh : Set (ModGL TwistTag.E6.tag Ω)) := by
    intro y hy
    refine ⟨twistHom_mem_adjointGroup TwistTag.E6 Ω Fr hy.1, ?_⟩
    change twistHom TwistTag.E6 Ω Fr y ∈ Subgroup.centralizer (Hh : Set (ModGL TwistTag.E6.tag Ω))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhF : twistHom TwistTag.E6 Ω Fr h = h := (hHF hh).2
    have hc := congrArg (twistHom TwistTag.E6 Ω Fr) (Subgroup.mem_centralizer_iff.mp hy.2 h hh)
    simpa only [map_mul, hhF] using hc
  rw [hF]
  exact frobTwistGL_mem_closedIdentityComponent (τ := TwistTag.E6.tag) 2 n (diagramMap TwistTag.E6 Ω)
    (fun y hy => by rw [← hF]; exact hZ y hy) hx


theorem map_hypCentConn_twistHom
    {n : ℕ} {k : Type} [Field k] [Finite k] (hk : Nat.card k = (2 ^ n) ^ 2)
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {Hh : Subgroup (ModGL TwistTag.E6.tag Ω)} (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr) :
    (closedIdentityComponent (adjointGroup TwistTag.E6.tag Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL TwistTag.E6.tag Ω)))).map (twistHom TwistTag.E6 Ω Fr) =
    closedIdentityComponent (adjointGroup TwistTag.E6.tag Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL TwistTag.E6.tag Ω))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap k Ω).injective 2
  have hFr' : Fr = iterateFrobenius Ω 2 n := RingHom.ext fun c => by
    rw [hFr, iterateFrobenius_def]
  have hP : diagramMap TwistTag.E6 Ω ^ 2 = 1 := diagramMap_pow_order TwistTag.E6 Ω
  have hPF : entrywiseFrobGL TwistTag.E6.tag Ω 2 n (diagramMap TwistTag.E6 Ω) =
      diagramMap TwistTag.E6 Ω := units_map_entrywiseHom_diagramMap (iterateFrobenius Ω 2 n)
  have hF : twistHom TwistTag.E6 Ω Fr =
      frobTwistGL TwistTag.E6.tag Ω 2 n (diagramMap TwistTag.E6 Ω) := by rw [hFr']; rfl
  rw [hF]
  exact map_frobTwistGL_eq_self_of_mapsTo 2 n hPF (by decide) hP
    (CFSG.RankThree.PartOne.KE.isAlgebraic_zmod_of_isAlgClosure (k := k))
    (fun x hx => by rw [← hF]; exact twistHom_mem_hypCentConn hk Fr hFr hHF hx)

theorem exists_twistHom_preimage_hypCentConn
    {n : ℕ} {k : Type} [Field k] [Finite k] (hk : Nat.card k = (2 ^ n) ^ 2)
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {Hh : Subgroup (ModGL TwistTag.E6.tag Ω)} (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    {x : ModGL TwistTag.E6.tag Ω}
    (hx : x ∈ closedIdentityComponent (adjointGroup TwistTag.E6.tag Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL TwistTag.E6.tag Ω)))) :
    ∃ y ∈ closedIdentityComponent (adjointGroup TwistTag.E6.tag Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL TwistTag.E6.tag Ω))), twistHom TwistTag.E6 Ω Fr y = x := by
  have hx' := hx
  rw [← map_hypCentConn_twistHom hk Fr hFr hHF] at hx'
  exact hx'

theorem map_center_hypCentConn_twistHom
    {n : ℕ} {k : Type} [Field k] [Finite k] (hk : Nat.card k = (2 ^ n) ^ 2)
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {Hh : Subgroup (ModGL TwistTag.E6.tag Ω)} (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr) :
    let Kc := closedIdentityComponent (adjointGroup TwistTag.E6.tag Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL TwistTag.E6.tag Ω)))
    (Kc ⊓ Subgroup.centralizer (Kc : Set (ModGL TwistTag.E6.tag Ω))).map
      (twistHom TwistTag.E6 Ω Fr) = Kc ⊓ Subgroup.centralizer (Kc : Set (ModGL TwistTag.E6.tag Ω)) := by
  intro Kc
  have hFZ : ∀ z ∈ Kc ⊓ Subgroup.centralizer (Kc : Set (ModGL TwistTag.E6.tag Ω)),
      twistHom TwistTag.E6 Ω Fr z ∈ Kc ⊓ Subgroup.centralizer (Kc : Set (ModGL TwistTag.E6.tag Ω)) := by
    intro z hz
    refine ⟨twistHom_mem_hypCentConn hk Fr hFr hHF hz.1, ?_⟩
    change twistHom TwistTag.E6 Ω Fr z ∈ Subgroup.centralizer (Kc : Set (ModGL TwistTag.E6.tag Ω))
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := exists_twistHom_preimage_hypCentConn hk Fr hFr hHF hx
    have hcomm := congrArg (twistHom TwistTag.E6 Ω Fr)
      (Subgroup.mem_centralizer_iff.mp hz.2 y hy)
    simpa only [map_mul] using hcomm
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hFZ z hz
  · intro z hz
    obtain ⟨y, hy, hyz⟩ := exists_twistHom_preimage_hypCentConn hk Fr hFr hHF hz.1
    refine ⟨y, ⟨hy, ?_⟩, hyz⟩
    change y ∈ Subgroup.centralizer (Kc : Set (ModGL TwistTag.E6.tag Ω))
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply twistHom_injective TwistTag.E6 Ω Fr
    rw [map_mul, map_mul, hyz]
    exact Subgroup.mem_centralizer_iff.mp hz.2 _
      (twistHom_mem_hypCentConn hk Fr hFr hHF hx)

theorem isQuasisimple_jgeom_of_rational_centralProduct
    {n : ℕ} {k : Type} [Field k] [Finite k] (hk : Nat.card k = (2 ^ n) ^ 2)
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {Hh : Subgroup (ModGL Tag.E6 Ω)} (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    [Finite ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)]
    {D : Type*} [Group D] (hDperf : Group.IsPerfect D) [Finite (Subgroup.center D)]
    (hZD : Odd (Nat.card (Subgroup.center D)))
    (ι : D →* ModGL Tag.E6 Ω)
    (hιK : ∀ x, ι x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hιker : ι.ker ≤ Subgroup.center D)
    (σ : D →* D) (hFι : ∀ x, twistHom TwistTag.E6 Ω Fr (ι x) = ι (σ x))
    (hDσ : CFSG.IsQuasisimple (σ.eqLocus (MonoidHom.id D)))
    {Zc : Subgroup (ModGL Tag.E6 Ω)}
    (hZcent : ∀ z ∈ Zc, ∀ x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))), z * x = x * z)
    (hZodd : ∀ z ∈ Zc, ∃ m, Odd m ∧ z ^ m = 1)
    (hKdec : ∀ x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))), ∃ z ∈ Zc, ∃ B : D, x = z * ι B)
    {e g : ModGL Tag.E6 Ω}
    (heK : e ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (heF : e ∈ TwistedDiag.Rgrp Ω Fr) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {t : ℕ} (hg2 : g ^ (2 ^ t) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) :
    CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype) := by
  let Kc := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
    Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)))
  let Z := Kc ⊓ Subgroup.centralizer (Kc : Set (ModGL Tag.E6 Ω))
  have hZK : ∀ z ∈ Z, ∀ x ∈ Kc, z * x = x * z := fun z hz x hx =>
    (Subgroup.mem_centralizer_iff.mp hz.2 x hx).symm
  have hZF : ∀ z ∈ Z, twistHom TwistTag.E6 Ω Fr z ∈ Z := by
    intro z hz
    have hz' : twistHom TwistTag.E6 Ω Fr z ∈ Z.map (twistHom TwistTag.E6 Ω Fr) :=
      ⟨z, hz, rfl⟩
    have hmap : Z.map (twistHom TwistTag.E6 Ω Fr) = Z := by
      with_unfolding_all exact map_center_hypCentConn_twistHom hk Fr hFr hHF
    rwa [hmap] at hz'
  have hZo : ∀ z ∈ Z, ∃ m, Odd m ∧ z ^ m = 1 := fun z hz =>
    exists_odd_pow_eq_one_of_centralProduct_central hDperf hZD ι hιK hιker hZcent hZodd hKdec
      hz.1 (hZK z hz)
  have hdec : ∀ x ∈ Kc, ∃ z ∈ Z, ∃ B : D, x = z * ι B := by
    intro x hx
    obtain ⟨z, hz, B, hB⟩ := hKdec x hx
    refine ⟨z, ⟨?_, ?_⟩, B, hB⟩
    · have h : x * (ι B)⁻¹ ∈ Kc := Kc.mul_mem hx (Kc.inv_mem (hιK B))
      rwa [hB, mul_inv_cancel_right] at h
    · change z ∈ Subgroup.centralizer (Kc : Set (ModGL Tag.E6 Ω))
      exact Subgroup.mem_centralizer_iff.mpr (fun y hy => (hZcent z hz y hy).symm)
  exact isQuasisimple_jgeom_of_isogeny Fr Hh hDperf hZD ι hιK hιker σ hFι hDσ
    hZK hZF hZo hdec heK heF he1 he3 hgK hgF hg2 hinv

open CFSG.RankThree.Classical2 in
theorem isQuasisimple_jgeom_of_isogeny_split
    [Finite ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)]
    {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k] [Finite k] [Algebra k Ω] [IsAlgClosure k Ω]
    (hk : Nat.card k = (2 ^ n) ^ 2) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    {m : ℕ} (hm : 2 ≤ m) (ι : SL(m, Ω) →* ModGL Tag.E6 Ω)
    (hιK : ∀ x, ι x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hιker : ι.ker ≤ Subgroup.center SL(m, Ω)) (X : GL (Fin m) Ω)
    (hFι : ∀ B, twistHom TwistTag.E6 Ω Fr (ι B) =
      ι (conjSLn X (Matrix.SpecialLinearGroup.map Fr B)))
    {Zc : Subgroup (ModGL Tag.E6 Ω)}
    (hZcent : ∀ z ∈ Zc, ∀ x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))), z * x = x * z)
    (hZodd : ∀ z ∈ Zc, ∃ m, Odd m ∧ z ^ m = 1)
    (hKdec : ∀ x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))), ∃ z ∈ Zc, ∃ B : SL(m, Ω), x = z * ι B)
    {e g : ModGL Tag.E6 Ω}
    (heK : e ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (heF : e ∈ TwistedDiag.Rgrp Ω Fr) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {t : ℕ} (hg2 : g ^ (2 ^ t) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) :
    CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap k Ω).injective 2
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hZfin : Finite (Subgroup.center SL(m, Ω)) :=
    (finite_odd_card_center_specialLinearGroup (by omega)).1
  have hq : m ≠ 2 ∨ 4 ≤ 2 ^ n :=
    Or.inr (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn))
  exact isQuasisimple_jgeom_of_rational_centralProduct hk Fr hFr hHF
    (isPerfect_specialLinearGroup_of_infinite hm)
    (finite_odd_card_center_specialLinearGroup (by omega)).2 ι hιK hιker
    ((conjSLn X).comp (Matrix.SpecialLinearGroup.map Fr)) hFι
    (isQuasisimple_eqLocus_conjSLn_frobenius_split (k' := k) Nat.prime_two (by omega) hm hq
      Fr hFr X).2
    hZcent hZodd hKdec heK heF he1 he3 hgK hgF hg2 hinv

open CFSG.RankThree.Classical2 in
theorem isQuasisimple_jgeom_of_isogeny_unitary
    [Finite ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)]
    {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k] [Finite k] [Algebra k Ω] [IsAlgClosure k Ω]
    (hk : Nat.card k = (2 ^ n) ^ 2) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    {m : ℕ} (hm : 2 ≤ m) (ι : SL(m, Ω) →* ModGL Tag.E6 Ω)
    (hιK : ∀ x, ι x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hιker : ι.ker ≤ Subgroup.center SL(m, Ω)) (X : GL (Fin m) Ω)
    (hFι : ∀ B, twistHom TwistTag.E6 Ω Fr (ι B) =
      ι (conjSLn X (invTransposeSL (Matrix.SpecialLinearGroup.map Fr B))))
    {Zc : Subgroup (ModGL Tag.E6 Ω)}
    (hZcent : ∀ z ∈ Zc, ∀ x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))), z * x = x * z)
    (hZodd : ∀ z ∈ Zc, ∃ m, Odd m ∧ z ^ m = 1)
    (hKdec : ∀ x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))), ∃ z ∈ Zc, ∃ B : SL(m, Ω), x = z * ι B)
    {e g : ModGL Tag.E6 Ω}
    (heK : e ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (heF : e ∈ TwistedDiag.Rgrp Ω Fr) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {t : ℕ} (hg2 : g ^ (2 ^ t) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) :
    CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype) := by
  by_cases hm2 : m = 2
  · subst m
    let J := Matrix.SpecialLinearGroup.toGL
      (CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin.jSL : SL(2, Ω))
    have hFι' : ∀ B, twistHom TwistTag.E6 Ω Fr (ι B) =
        ι (conjSLn (X * J) (Matrix.SpecialLinearGroup.map Fr B)) := by
      intro B
      rw [hFι, invTransposeSL_two_eq_conj]
      congr 1
      apply Subtype.ext
      rw [coe_conjSLn, coe_conjSLn, coe_conjSLn, Units.val_mul, _root_.mul_inv_rev, Units.val_mul]
      simp only [Matrix.mul_assoc]
      rfl
    exact isQuasisimple_jgeom_of_isogeny_split Fr Hh hn hk hFr hHF hm
      ι hιK hιker (X * J) hFι' hZcent hZodd hKdec heK heF he1 he3 hgK hgF hg2 hinv
  have hm3 : 3 ≤ m := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap k Ω).injective 2
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hZfin : Finite (Subgroup.center SL(m, Ω)) :=
    (finite_odd_card_center_specialLinearGroup (by omega)).1
  have hnq : (m, 2 ^ n) ≠ (3, 2) := fun h => by
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  exact isQuasisimple_jgeom_of_rational_centralProduct hk Fr hFr hHF
    (isPerfect_specialLinearGroup_of_infinite (by omega))
    (finite_odd_card_center_specialLinearGroup (by omega)).2 ι hιK hιker
    ((conjSLn X).comp (invTransposeSL.comp (Matrix.SpecialLinearGroup.map Fr))) hFι
    (isQuasisimple_eqLocus_conjSLn_frobenius_unitary (k' := k) Nat.prime_two (by omega) hm3 hnq
      Fr hFr X).2
    hZcent hZodd hKdec heK heF he1 he3 hgK hgF hg2 hinv

open CFSG.RankThree.Classical2 in
theorem isQuasisimple_jgeom_of_lift
    [Finite ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)]
    {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k] [Finite k] [Algebra k Ω] [IsAlgClosure k Ω]
    (hk : Nat.card k = (2 ^ n) ^ 2) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    {m : ℕ} (hm : 3 ≤ m) (ι : SL(m, Ω) →* ModGL Tag.E6 Ω)
    (hιK : ∀ x, ι x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hιker : ι.ker ≤ Subgroup.center SL(m, Ω)) (σ : SL(m, Ω) →* SL(m, Ω))
    (hFι : ∀ B, twistHom TwistTag.E6 Ω Fr (ι B) = ι (σ B)) (A₀ : GL (Fin m) Ω)
    (hσT : (∀ D : SL(m, Ω), (D : Matrix (Fin m) (Fin m) Ω).IsDiag →
        σ D = conjSLn A₀ (Matrix.SpecialLinearGroup.map Fr D)) ∨
      ∀ D : SL(m, Ω), (D : Matrix (Fin m) (Fin m) Ω).IsDiag →
        σ D = conjSLn A₀ (invTransposeSL (Matrix.SpecialLinearGroup.map Fr D)))
    {Zc : Subgroup (ModGL Tag.E6 Ω)}
    (hZcent : ∀ z ∈ Zc, ∀ x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))), z * x = x * z)
    (hZodd : ∀ z ∈ Zc, ∃ m, Odd m ∧ z ^ m = 1)
    (hKdec : ∀ x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))), ∃ z ∈ Zc, ∃ B : SL(m, Ω), x = z * ι B)
    {e g : ModGL Tag.E6 Ω}
    (heK : e ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (heF : e ∈ TwistedDiag.Rgrp Ω Fr) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {t : ℕ} (hg2 : g ^ (2 ^ t) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) :
    CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap k Ω).injective 2
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  rcases hσT with hσT | hσT
  · obtain ⟨A, hA⟩ := eq_conjSLn_comp_map_of_torus hm Fr hFr σ A₀ hσT
    exact isQuasisimple_jgeom_of_isogeny_split Fr Hh hn hk hFr hHF (by omega) ι hιK hιker A
      (fun B => by rw [hFι, hA, MonoidHom.comp_apply]) hZcent hZodd hKdec heK heF he1 he3
      hgK hgF hg2 hinv
  · obtain ⟨A, hA⟩ := eq_conjSLn_comp_invTranspose_of_torus hm Fr hFr σ A₀ hσT
    exact isQuasisimple_jgeom_of_isogeny_unitary Fr Hh hn hk hFr hHF (by omega) ι hιK hιker A
      (fun B => by rw [hFι, hA, MonoidHom.comp_apply, MonoidHom.comp_apply]) hZcent hZodd
      hKdec heK heF he1 he3 hgK hgF hg2 hinv

end RationalFrobenius

end Literal

section Recipe

open CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Classical2
  CFSG.LieType.Chevalley


theorem le_cgrp_of_perfect_rgrp
    {n : ℕ} (hn : 1 ≤ n) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = (2 ^ n) ^ 2) (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {P : Subgroup (ModGL Tag.E6 Ω)} (hP : P ≤ TwistedDiag.Rgrp Ω Fr)
    (hperf : ⁅P, P⁆ = P) : P ≤ TwistedDiag.Cgrp k σ.toRingHom Ω := by
  obtain ⟨-, -, hder, -⟩ := twisted_E6_full_rational_fixed_group_order
    Nat.prime_two hn k hk σ.toRingHom hσ Ω Fr hFr
  change P ≤ (graphFixedRootGroup TwistTag.E6 k σ.toRingHom).map
    (baseChangeGL (algebraMap k Ω))
  rw [← hder, ← hperf]
  exact Subgroup.commutator_mono hP hP

theorem exists_recipe_preimage_of_quasisimple_rgrp
    {n : ℕ} (hn : 1 ≤ n) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = (2 ^ n) ^ 2) (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {R : Type} [Group R] (ε : ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom) ≃* R)
    {P : Subgroup (ModGL Tag.E6 Ω)} (hP : P ≤ TwistedDiag.Rgrp Ω Fr)
    (hq : CFSG.IsQuasisimple P) :
    let ι : R →* ModGL Tag.E6 Ω := (baseChangeGL (τ := Tag.E6) (algebraMap k Ω)).comp
      ((graphFixedRootGroup TwistTag.E6 k σ.toRingHom).subtype.comp ε.symm.toMonoidHom)
    P ≤ ι.range ∧ CFSG.IsQuasisimple (P.comap ι) ∧
      ∃ e : ↥(P.comap ι) ≃* P, ∀ x, (e x : ModGL Tag.E6 Ω) = ι x := by
  classical
  dsimp only
  let ι : R →* ModGL Tag.E6 Ω := (baseChangeGL (τ := Tag.E6) (algebraMap k Ω)).comp
    ((graphFixedRootGroup TwistTag.E6 k σ.toRingHom).subtype.comp ε.symm.toMonoidHom)
  have hι : Function.Injective ι := (baseChangeGL_injective (algebraMap k Ω)).comp
    ((Subgroup.subtype_injective _).comp ε.symm.injective)
  have hιrange : ι.range = TwistedDiag.Cgrp k σ.toRingHom Ω := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(ε.symm x).1, (ε.symm x).2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      refine ⟨ε ⟨c, hc⟩, ?_⟩
      change baseChangeGL (τ := Tag.E6) (algebraMap k Ω) (ε.symm (ε ⟨c, hc⟩)).1 =
        baseChangeGL (τ := Tag.E6) (algebraMap k Ω) c
      rw [MulEquiv.symm_apply_apply]
  have hle : P ≤ ι.range := by
    rw [hιrange]
    exact le_cgrp_of_perfect_rgrp hn hk σ hσ Fr hFr hP (Subgroup.isPerfect_iff.mp hq.1)
  have hmap : (P.comap ι).map ι = P := Subgroup.map_comap_eq_self hle
  let e : ↥(P.comap ι) ≃* P := ((P.comap ι).equivMapOfInjective ι hι).trans
    (MulEquiv.subgroupCongr hmap)
  exact ⟨hle, hq.of_mulEquiv e, e, fun _ => rfl⟩

open CFSG.Assembly in
theorem isComponentOf_recipe_preimage_jgeom
    {n : ℕ} (hn : 1 ≤ n) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = (2 ^ n) ^ 2) (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {R : Type} [Group R] (ε : ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom) ≃* R)
    (Hh : Subgroup (ModGL Tag.E6 Ω)) :
    let Kc := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)))
    let KF := Kc ⊓ TwistedDiag.Rgrp Ω Fr
    let P := (primeResidual 2 ↥KF).map KF.subtype
    let ι : R →* ModGL Tag.E6 Ω := (baseChangeGL (τ := Tag.E6) (algebraMap k Ω)).comp
      ((graphFixedRootGroup TwistTag.E6 k σ.toRingHom).subtype.comp ε.symm.toMonoidHom)
    CFSG.IsQuasisimple P →
      IsComponentOf (P.comap ι) ((Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))).comap ι) ∧
      (P.comap ι).map ι = P := by
  classical
  dsimp only
  let Kc := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
    Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)))
  let KF := Kc ⊓ TwistedDiag.Rgrp Ω Fr
  let P := (primeResidual 2 ↥KF).map KF.subtype
  let ι : R →* ModGL Tag.E6 Ω := (baseChangeGL (τ := Tag.E6) (algebraMap k Ω)).comp
    ((graphFixedRootGroup TwistTag.E6 k σ.toRingHom).subtype.comp ε.symm.toMonoidHom)
  change CFSG.IsQuasisimple P → _
  intro hq
  have hPR : P ≤ TwistedDiag.Rgrp Ω Fr := (Subgroup.map_subtype_le _).trans inf_le_right
  have hPC : P ≤ Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)) := by
    intro x hx
    exact (closedIdentityComponent_le _ ((Subgroup.map_subtype_le _ hx).1)).2
  obtain ⟨hPrange, hJRq, -, -⟩ :=
    TwE6FixedComponent.exists_recipe_preimage_of_quasisimple_rgrp hn hk σ hσ Fr hFr ε hPR hq
  have hιR : ι.range ≤ TwistedDiag.Rgrp Ω Fr := by
    obtain ⟨-, -, hder, -⟩ := twisted_E6_full_rational_fixed_group_order
      Nat.prime_two hn k hk σ.toRingHom hσ Ω Fr hFr
    have hCR : TwistedDiag.Cgrp k σ.toRingHom Ω ≤ TwistedDiag.Rgrp Ω Fr := by
      change (graphFixedRootGroup TwistTag.E6 k σ.toRingHom).map
        (baseChangeGL (algebraMap k Ω)) ≤ twistedFixedGroup TwistTag.E6 Ω Fr
      rw [← hder]
      simpa only [sup_idem] using Subgroup.commutator_le_sup
        (twistedFixedGroup TwistTag.E6 Ω Fr) (twistedFixedGroup TwistTag.E6 Ω Fr)
    rintro _ ⟨r, rfl⟩
    exact hCR ⟨(ε.symm r).1, (ε.symm r).2, rfl⟩
  let C := (Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))).comap ι
  have hle : P.comap ι ≤ C := fun x hx => hPC hx
  have hnormal : ((P.comap ι).subgroupOf C).Normal := by
    constructor
    intro y hy x
    have hyP : ι (y : R) ∈ P := hy
    have hxR : ι (x : R) ∈ TwistedDiag.Rgrp Ω Fr := hιR ⟨x, rfl⟩
    have hxC : ι (x : R) ∈ Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)) := x.2
    have hN := TwE6FixedComponent.centralizer_le_normalizer_jgeom Fr Hh ⟨hxR, hxC⟩
    change ι ((x : R) * (y : R) * (x : R)⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hN (ι (y : R))).mp hyP
  refine ⟨⟨hle, IsSubnormal.step hle hnormal (IsSubnormal.refl C), ?_⟩, ?_⟩
  · exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hJRq
  · exact Subgroup.map_comap_eq_self hPrange

section OriginalActors

open CFSG.Assembly SCFourCover NoOffTwE6Three CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
  (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
  (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
    MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)

variable {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}
  (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
  {A : Subgroup (MulAut L')}
  (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l, φ (ψ l) = ψ (a l))

theorem ggHypCent_induced_recipe_eq
    {g : L'} (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    let ι : TwE6Delta.RecipeR K n →* ModGL Tag.E6 Ω :=
      (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)).comp
        ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp ε.symm.toMonoidHom)
    ggHypCent (TypeA.inducedSub ψ A) (ψ g) = (Subgroup.centralizer
      (((ggConjAut A hg).toMonoidHom.eqLocus (MonoidHom.id A)).map
        ((rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).subtype.comp
          (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).toMonoidHom) :
            Set (ModGL Tag.E6 Ω))).comap ι := by
  let ι : TwE6Delta.RecipeR K n →* ModGL Tag.E6 Ω :=
    (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)).comp
      ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp ε.symm.toMonoidHom)
  have hι : Function.Injective ι := (baseChangeGL_injective (algebraMap K Ω)).comp
    ((Subgroup.subtype_injective _).comp ε.symm.injective)
  let γ := recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
  let ρ : A →* ModGL Tag.E6 Ω :=
    (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).subtype.comp γ.toMonoidHom
  have hconj : ∀ (a : A) (l : L'), ι (ψ (a.1 l)) = ρ a * ι (ψ l) * (ρ a)⁻¹ := by
    intro a l
    let r : TwistedDiag.Rgrp Ω Fr :=
      ⟨γ a, rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε _ (γ a).2⟩
    have hact := recipeActorModelEquiv_apply hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a l
    have hfix : rgrpConjAut hn hK σ hσ Fr hFr r (ε.symm (ψ l)) =
        ε.symm (ψ (a.1 l)) := by
      apply ε.injective
      rw [← rgrpRecipeAut_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact hact
    change baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (ε.symm (ψ (a.1 l))).1 =
      r.1 * baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (ε.symm (ψ l)).1 * r.1⁻¹
    rw [← baseChange_rgrpConjAut hn hK σ hσ Fr hFr, hfix]
  exact ggHypCent_induced_eq_centralizer_comap hψ hker hperf
    (fun a ha => by obtain ⟨α, -, hα⟩ := hAI a ha; exact ⟨α, hα⟩) ι hι ρ hconj hg

theorem isComponentOf_induced_recipe_jgeom
    {g : L'} (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    let Hh := ((ggConjAut A hg).toMonoidHom.eqLocus (MonoidHom.id A)).map
      ((rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).subtype.comp
        (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).toMonoidHom)
    let Kc := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)))
    let KF := Kc ⊓ TwistedDiag.Rgrp Ω Fr
    let P := (primeResidual 2 ↥KF).map KF.subtype
    let ι : TwE6Delta.RecipeR K n →* ModGL Tag.E6 Ω :=
      (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)).comp
        ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp ε.symm.toMonoidHom)
    CFSG.IsQuasisimple P →
      IsComponentOf (P.comap ι) (ggHypCent (TypeA.inducedSub ψ A) (ψ g)) ∧
        (P.comap ι).map ι = P := by
  dsimp only
  intro hq
  rw [ggHypCent_induced_recipe_eq hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI hg]
  exact CFSG.StandardType.TwE6FixedComponent.isComponentOf_recipe_preimage_jgeom hn hK σ hσ Fr hFr ε _ hq


theorem jgeom_data_of_two_element
    [Finite L'] (hA : IsElemAbelian 3 A) {g : L'}
    (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L')))
    {m : ℕ} (hg2 : g ^ (2 ^ m) = 1) :
    let Hh := ((ggConjAut A hg).toMonoidHom.eqLocus (MonoidHom.id A)).map
      ((rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).subtype.comp
        (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).toMonoidHom)
    let Kc := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)))
    let KF := Kc ⊓ TwistedDiag.Rgrp Ω Fr
    let P := (primeResidual 2 ↥KF).map KF.subtype
    let ι : TwE6Delta.RecipeR K n →* ModGL Tag.E6 Ω :=
      (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)).comp
        ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp ε.symm.toMonoidHom)
    ι (ψ g) ∈ P := by
  have : Finite (MulAut L') := Finite.of_injective (fun a : MulAut L' => (a : L' → L'))
    (fun _ _ h => MulEquiv.ext (congrFun h))
  have : Finite A := inferInstance
  have hgK := recipeMatrixHom_mem_connected_fixed_subgroup_of_two_pow
    hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI hA (φ := ggConjAut A hg) hg rfl m hg2
  rw [rgrpModel_fixedHyperplane_eq hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI] at hgK
  have hgF := recipeMatrixHom_mem_Rgrp hn hK σ hσ Fr hFr ε (ψ := ψ) g
  exact TwE6FixedComponent.mem_jgeom_of_two_pow_eq_one Fr _ hgK hgF
    (by
      change recipeMatrixHom σ ε (ψ := ψ) g ^ (2 ^ m) = 1
      rw [← map_pow, hg2, map_one])

end OriginalActors

end Recipe

section RootTriple

open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem conjSL_diagUnitOne_uSL' {Ω : Type} [Field Ω] (a : Ωˣ) (c : Ω) :
    CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne a) (uSL c) =
      uSL ((a : Ω) * c) := by
  apply Subtype.ext
  rw [CFSG.RankThree.Classical.coe_conjSL, CFSG.RankThree.Classical.coe_diagUnitOne,
    CFSG.RankThree.Classical.coe_diagUnitOne_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, Matrix.mul_apply, Fin.sum_univ_two]

private theorem conjSL_diagUnitOne_vSL' {Ω : Type} [Field Ω] (a : Ωˣ) (c : Ω) :
    CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne a) (vSL c) =
      vSL (((a⁻¹ : Ωˣ) : Ω) * c) := by
  apply Subtype.ext
  rw [CFSG.RankThree.Classical.coe_conjSL, CFSG.RankThree.Classical.coe_diagUnitOne,
    CFSG.RankThree.Classical.coe_diagUnitOne_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vSL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem HSL_conj_apply {Ω : Type} [Field Ω] (v : Ωˣ) (X : SL2 Ω) :
    ((HSL v * X * (HSL v)⁻¹ : SL2 Ω) : Matrix (Fin 2) (Fin 2) Ω) 0 1 =
        (v : Ω) * (X : Matrix (Fin 2) (Fin 2) Ω) 0 1 * v ∧
      ((HSL v * X * (HSL v)⁻¹ : SL2 Ω) : Matrix (Fin 2) (Fin 2) Ω) 1 0 =
        ((v⁻¹ : Ωˣ) : Ω) * (X : Matrix (Fin 2) (Fin 2) Ω) 1 0 * ((v⁻¹ : Ωˣ) : Ω) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_HSL,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp

private theorem diag_of_HSL_conj_eq {Ω : Type} [Field Ω] [IsAlgClosed Ω] {X : SL2 Ω}
    (hX : ∀ u : Ωˣ, HSL u * X * (HSL u)⁻¹ = X) :
    (X : Matrix (Fin 2) (Fin 2) Ω) 0 1 = 0 ∧ (X : Matrix (Fin 2) (Fin 2) Ω) 1 0 = 0 := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset Ω)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨hx0, hx1, hxm⟩ := hx
  have hx2 : x * x - 1 ≠ 0 := by
    intro h
    have h' : (x - 1) * (x + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h' | h'
    · exact hx1 (by linear_combination h')
    · exact hxm (by linear_combination h')
  set u := Units.mk0 x hx0
  have e01 := (HSL_conj_apply u X).1
  have e10 := (HSL_conj_apply u⁻¹ X).2
  rw [hX] at e01 e10
  rw [inv_inv] at e10
  have hu : ((u : Ωˣ) : Ω) = x := rfl
  rw [hu] at e01 e10
  constructor
  · have : (X : Matrix (Fin 2) (Fin 2) Ω) 0 1 * (x * x - 1) = 0 := by linear_combination -e01
    exact (mul_eq_zero.1 this).resolve_right hx2
  · have : (X : Matrix (Fin 2) (Fin 2) Ω) 1 0 * (x * x - 1) = 0 := by linear_combination -e10
    exact (mul_eq_zero.1 this).resolve_right hx2

private theorem eq_HSL_of_diag {Ω : Type} [Field Ω] {X : SL2 Ω}
    (h01 : (X : Matrix (Fin 2) (Fin 2) Ω) 0 1 = 0)
    (h10 : (X : Matrix (Fin 2) (Fin 2) Ω) 1 0 = 0) :
    ∃ u : Ωˣ, X = HSL u := by
  have hdet : (X : Matrix (Fin 2) (Fin 2) Ω) 0 0 * (X : Matrix (Fin 2) (Fin 2) Ω) 1 1 = 1 := by
    have h := X.2
    rw [Matrix.det_fin_two, h01, h10, mul_zero, sub_zero] at h
    exact h
  refine ⟨Units.mkOfMulEqOne _ _ hdet, Subtype.ext ?_⟩
  rw [coe_HSL]
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact h01
  · exact h10
  · rfl

private theorem conj_eq_of_commute_mul {G : Type*} [Group G] {t p q : G}
    (ht : t * (p * q) = p * q * t) (hq : t * q = q * t) : t * p * t⁻¹ = p := by
  have h : t * p * q = p * t * q := by
    calc t * p * q = t * (p * q) := mul_assoc _ _ _
      _ = p * q * t := ht
      _ = p * (t * q) := by rw [mul_assoc, hq]
      _ = p * t * q := (mul_assoc _ _ _).symm
  rw [mul_right_cancel h, mul_inv_cancel_right]

private theorem conjSL_diagUnitOne_HSL {Ω : Type} [Field Ω] (a u : Ωˣ) :
    CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne a) (HSL u) = HSL u := by
  apply Subtype.ext
  rw [CFSG.RankThree.Classical.coe_conjSL, CFSG.RankThree.Classical.coe_diagUnitOne,
    CFSG.RankThree.Classical.coe_diagUnitOne_inv, coe_HSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

private theorem HSL_conj_eq_conjSL {Ω : Type} [Field Ω] (v : Ωˣ) (A : SL2 Ω) :
    HSL v * A * (HSL v)⁻¹ =
      CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne (v * v)) A := by
  apply Subtype.ext
  rw [CFSG.RankThree.Classical.coe_conjSL, CFSG.RankThree.Classical.coe_diagUnitOne,
    CFSG.RankThree.Classical.coe_diagUnitOne_inv]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_HSL,
    Matrix.adjugate_fin_two]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

private theorem conjSL_diagUnitOne_comm {Ω : Type} [Field Ω] (a b : Ωˣ) (A : SL2 Ω) :
    CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne a)
        (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne b) A) =
      CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne b)
        (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne a) A) := by
  rw [← CFSG.RankThree.Classical.conjSL_mul, ← CFSG.RankThree.Classical.conjSL_mul,
    CFSG.RankThree.Chevalley.diagUnitOne_mul, CFSG.RankThree.Chevalley.diagUnitOne_mul, mul_comm]

private theorem diag_of_conjSL_diagUnitOne_eq {Ω : Type} [Field Ω] {c : Ωˣ} (hc : c ≠ 1)
    {B : SL2 Ω}
    (hB : CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne c) B = B) :
    (B : Matrix (Fin 2) (Fin 2) Ω) 0 1 = 0 ∧ (B : Matrix (Fin 2) (Fin 2) Ω) 1 0 = 0 := by
  have h := congrArg (fun A : SL2 Ω => (A : Matrix (Fin 2) (Fin 2) Ω)) hB
  simp only [CFSG.RankThree.Classical.coe_conjSL, CFSG.RankThree.Classical.coe_diagUnitOne,
    CFSG.RankThree.Classical.coe_diagUnitOne_inv] at h
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h01 h10
  simp at h01 h10
  have hc' : (c : Ω) - 1 ≠ 0 := fun h' => hc (Units.ext (by simpa [sub_eq_zero] using h'))
  have hci : (c : Ω)⁻¹ - 1 ≠ 0 := by
    intro h'
    have h1 : (c : Ω)⁻¹ = 1 := by linear_combination h'
    exact hc' (by rw [inv_eq_one.1 h1, sub_self])
  constructor
  · have : (B : Matrix (Fin 2) (Fin 2) Ω) 0 1 * ((c : Ω) - 1) = 0 := by linear_combination h01
    exact (mul_eq_zero.1 this).resolve_right hc'
  · have : (B : Matrix (Fin 2) (Fin 2) Ω) 1 0 * ((c : Ω)⁻¹ - 1) = 0 := by
      linear_combination h10
    exact (mul_eq_zero.1 this).resolve_right hci

theorem eq_or_eq_inv_of_conj_rootDiagUnit {Ω : Type} [Field Ω] [IsAlgClosed Ω] (m : Fin Tag.E6.rank → ℤ)
    (R : ModGL Tag.E6 Ω) (θ : Ωˣ → Ωˣ)
    (h : ∀ u : Ωˣ, R * rootDiagUnit Tag.E6 (fun i => u ^ m i) * R⁻¹ =
      rootDiagUnit Tag.E6 (fun i => θ u ^ m i))
    {ℓ₁ : Label Tag.E6} (hℓ₁ : ∑ i, labelWt Tag.E6 ℓ₁ i * m i = 1) :
    (∀ u, θ u = u) ∨ ∀ u, θ u = u⁻¹ := by
  classical
  set w : Label Tag.E6 → ℤ := fun ℓ => ∑ i, labelWt Tag.E6 ℓ i * m i with hw
  have hχ : ∀ (u : Ωˣ) (ℓ : Label Tag.E6),
      rootChar (fun i => u ^ m i) (labelWt Tag.E6 ℓ) = u ^ w ℓ := by
    intro u ℓ
    simp only [rootChar, ← zpow_mul, hw]
    rw [Finset.prod_zpow_eq_zpow_sum]
    simp only [mul_comm]
  set R' : Module.End Ω (RootModule Tag.E6 Ω) := (R : Module.End Ω (RootModule Tag.E6 Ω))
  have key : ∀ (u : Ωˣ) (a b : Label Tag.E6),
      ((u ^ w b : Ωˣ) : Ω) * R' (Finsupp.single b 1) a =
        ((θ u ^ w a : Ωˣ) : Ω) * R' (Finsupp.single b 1) a := by
    intro u a b
    have e := congrArg (fun X : ModGL Tag.E6 Ω =>
      (X : Module.End Ω (RootModule Tag.E6 Ω)) (Finsupp.single b 1) a)
      (eq_mul_of_mul_inv_eq (h u))
    simp only [Units.val_mul, Module.End.mul_apply] at e
    change R' (rootDiag (fun i => u ^ m i) (Finsupp.single b 1)) a =
      rootDiag (fun i => θ u ^ m i) (R' (Finsupp.single b 1)) a at e
    rw [rootDiag_single, map_smul, Finsupp.smul_apply, smul_eq_mul,
      CFSG.SeitzReduction.F4Pilot.rootDiag_apply, hχ, hχ] at e
    exact e
  have hrow : ∃ b, R' (Finsupp.single b 1) ℓ₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ v : RootModule Tag.E6 Ω, R' v ℓ₁ = 0 := by
      intro v
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => rw [map_add, Finsupp.add_apply, hf, hg, add_zero]
      | single b r =>
        rw [← mul_one r, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, Finsupp.smul_apply,
          hcon b, smul_zero]
    have h1 := hall ((↑R⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) (Finsupp.single ℓ₁ 1))
    change ((R * R⁻¹ : ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω))
      (Finsupp.single ℓ₁ 1) ℓ₁ = 0 at h1
    rw [mul_inv_cancel, Units.val_one, Module.End.one_apply, Finsupp.single_eq_same] at h1
    exact one_ne_zero h1
  obtain ⟨b₀, hb₀⟩ := hrow
  have hθ : ∀ u, θ u = u ^ w b₀ := by
    intro u
    have e := key u ℓ₁ b₀
    have e' := mul_right_cancel₀ hb₀ e
    have hw1 : w ℓ₁ = 1 := hℓ₁
    rw [hw1, zpow_one] at e'
    exact (Units.ext e').symm
  have hcol : ∃ a, R' (Finsupp.single ℓ₁ 1) a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : R' (Finsupp.single ℓ₁ 1) = 0 := Finsupp.ext hcon
    have h1 := congrArg (↑R⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) h0
    change ((R⁻¹ * R : ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω))
      (Finsupp.single ℓ₁ 1) = _ at h1
    rw [inv_mul_cancel, Units.val_one, Module.End.one_apply, map_zero] at h1
    have h2 := congrArg (fun v : RootModule Tag.E6 Ω => v ℓ₁) h1
    simp only [Finsupp.single_eq_same, Finsupp.coe_zero, Pi.zero_apply] at h2
    exact one_ne_zero h2
  obtain ⟨a₀, ha₀⟩ := hcol
  have hk : ∀ u : Ωˣ, u ^ (1 - w b₀ * w a₀) = 1 := by
    intro u
    have e := mul_right_cancel₀ ha₀ (key u a₀ ℓ₁)
    have hw1 : w ℓ₁ = 1 := hℓ₁
    rw [hw1, zpow_one, hθ, ← zpow_mul] at e
    have e' : u = u ^ (w b₀ * w a₀) := Units.ext e
    rw [zpow_sub, zpow_one, ← e', mul_inv_cancel]
  have hk0 : 1 - w b₀ * w a₀ = 0 := by
    by_contra hne
    set N := (1 - w b₀ * w a₀).natAbs with hN
    have hNpos : 0 < N := Int.natAbs_pos.2 hne
    have hroot : ∀ x : Ω, x ≠ 0 → (Polynomial.X ^ N - 1 : Polynomial Ω).IsRoot x := by
      intro x hx
      have hu := hk (Units.mk0 x hx)
      have hu' : (Units.mk0 x hx) ^ N = 1 := by
        rcases Int.natAbs_eq (1 - w b₀ * w a₀) with h' | h'
        · rw [h', zpow_natCast] at hu; exact hu
        · rw [h', zpow_neg, zpow_natCast, inv_eq_one] at hu; exact hu
      have := congrArg (fun v : Ωˣ => (v : Ω)) hu'
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this
      simp [Polynomial.IsRoot, this]
    have hinf : ({x : Ω | (Polynomial.X ^ N - 1 : Polynomial Ω).IsRoot x}).Infinite :=
      ((Set.finite_singleton (0 : Ω)).infinite_compl).mono fun x hx => hroot x hx
    have h0 := Polynomial.eq_zero_of_infinite_isRoot _ hinf
    exact (Polynomial.X_pow_sub_C_ne_zero hNpos (1 : Ω)) (by simpa using h0)
  have hprod : w b₀ * w a₀ = 1 := by linarith
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hprod with h1 | h1
  · exact Or.inl fun u => by rw [hθ, h1, zpow_one]
  · exact Or.inr fun u => by rw [hθ, h1, zpow_neg, zpow_one]

variable
  {Ω : Type} [Field Ω]

@[expose] noncomputable def rootTripleHom (β : Fin 3 → Fin Tag.E6.rank → ℤ)
    (hβ : ∀ i, IsRoot .E6 (β i)) (horth : ∀ i j, i ≠ j → iform (β i) (β j) = 0)
    (s₁ s₂ : Ωˣ) : SL2 Ω →* ModGL Tag.E6 Ω where
  toFun A := rootSL2 .E6 Ω (β 0) A *
    rootSL2 .E6 Ω (β 1)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₁) A) *
    rootSL2 .E6 Ω (β 2)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₂) A)
  map_one' := by simp only [map_one, mul_one]
  map_mul' A B := by
    have c : ∀ i j, i ≠ j → ∀ A B : SL2 Ω,
        Commute (rootSL2 .E6 Ω (β i) A) (rootSL2 .E6 Ω (β j) B) := fun i j h A B =>
      commute_rootSL2_of_iform_eq_zero (Or.inr (Or.inl rfl)) (hβ i) (hβ j) (horth i j h) A B
    simp only [map_mul, mul_assoc]
    rw [(c 0 1 (by decide) _ _).left_comm, (c 1 2 (by decide) _ _).left_comm,
      (c 0 2 (by decide) _ _).left_comm]

theorem rootTripleHom_apply (β : Fin 3 → Fin Tag.E6.rank → ℤ) (hβ : ∀ i, IsRoot .E6 (β i))
    (horth : ∀ i j, i ≠ j → iform (β i) (β j) = 0) (s₁ s₂ : Ωˣ) (A : SL2 Ω) :
    rootTripleHom β hβ horth s₁ s₂ A = rootSL2 .E6 Ω (β 0) A *
      rootSL2 .E6 Ω (β 1)
        (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₁) A) *
      rootSL2 .E6 Ω (β 2)
        (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₂) A) :=
  rfl

theorem rootTripleHom_mem_closedIdentityComponent [IsAlgClosed Ω] (β : Fin 3 → Fin Tag.E6.rank → ℤ)
    (hβ : ∀ i, IsRoot .E6 (β i)) (horth : ∀ i j, i ≠ j → iform (β i) (β j) = 0)
    (s₁ s₂ : Ωˣ) {Hh : Subgroup (ModGL Tag.E6 Ω)}
    (hcomm : ∀ h ∈ Hh, ∀ t : Ω,
      h * rootTripleHom β hβ horth s₁ s₂ (uSL t) = rootTripleHom β hβ horth s₁ s₂ (uSL t) * h ∧
        h * rootTripleHom β hβ horth s₁ s₂ (vSL t) = rootTripleHom β hβ horth s₁ s₂ (vSL t) * h)
    (A : SL2 Ω) :
    rootTripleHom β hβ horth s₁ s₂ A ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) := by
  set ι := rootTripleHom (Ω := Ω) β hβ horth s₁ s₂ with hιdef
  have hZ : ∀ X, (∀ h ∈ Hh, h * ι X = ι X * h) →
      ι X ∈ adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)) := by
    intro X hX
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_iff.2 hX⟩
    rw [hιdef, rootTripleHom_apply]
    exact mul_mem (mul_mem (rootSL2_mem_adjointGroup _ _) (rootSL2_mem_adjointGroup _ _))
      (rootSL2_mem_adjointGroup _ _)
  have hU : ∀ t, ι (uSL t) ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) := by
    have hcurve : IsPolynomialCurve fun t : Ω => ι (uSL t) := by
      have h : (fun t : Ω => ι (uSL t)) = fun t =>
          pinnedX Tag.E6 Ω (β 0) ((Polynomial.C (((pinnedData Tag.E6 (β 0)).2.2 : ℤ) : Ω) *
            Polynomial.X).eval t) *
          pinnedX Tag.E6 Ω (β 1) ((Polynomial.C (((pinnedData Tag.E6 (β 1)).2.2 : ℤ) * (s₁ : Ω)) *
            Polynomial.X).eval t) *
          pinnedX Tag.E6 Ω (β 2) ((Polynomial.C (((pinnedData Tag.E6 (β 2)).2.2 : ℤ) * (s₂ : Ω)) *
            Polynomial.X).eval t) := by
        funext t
        simp only [hιdef, rootTripleHom_apply, conjSL_diagUnitOne_uSL', rootSL2_uSL_eq,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, zsmul_eq_mul, mul_assoc]
      rw [h]
      exact ((isPolynomialCurve_pinnedX _ _).mul (isPolynomialCurve_pinnedX _ _)).mul
        (isPolynomialCurve_pinnedX _ _)
    intro t
    refine mem_closedIdentityComponent_of_isPolynomialCurve hcurve
      (fun t => hZ _ fun h hh => (hcomm h hh t).1) (t₀ := 0) ?_ t
    rw [show (uSL (0 : Ω) : SL2 Ω) = 1 by ext i j; fin_cases i <;> fin_cases j <;> simp [uSL],
      map_one]
  have hV : ∀ t, ι (vSL t) ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) := by
    obtain ⟨ε₀, -, h₀⟩ := exists_rootSL2_vSL_eq (K := Ω) (hβ 0)
    obtain ⟨ε₁, -, h₁⟩ := exists_rootSL2_vSL_eq (K := Ω) (hβ 1)
    obtain ⟨ε₂, -, h₂⟩ := exists_rootSL2_vSL_eq (K := Ω) (hβ 2)
    have hcurve : IsPolynomialCurve fun t : Ω => ι (vSL t) := by
      have h : (fun t : Ω => ι (vSL t)) = fun t =>
          pinnedX Tag.E6 Ω (-β 0) ((Polynomial.C ε₀ * Polynomial.X).eval t) *
          pinnedX Tag.E6 Ω (-β 1) ((Polynomial.C (ε₁ * ((s₁⁻¹ : Ωˣ) : Ω)) * Polynomial.X).eval t) *
          pinnedX Tag.E6 Ω (-β 2)
            ((Polynomial.C (ε₂ * ((s₂⁻¹ : Ωˣ) : Ω)) * Polynomial.X).eval t) := by
        funext t
        simp only [hιdef, rootTripleHom_apply, conjSL_diagUnitOne_vSL', h₀, h₁, h₂,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_assoc]
      rw [h]
      exact ((isPolynomialCurve_pinnedX _ _).mul (isPolynomialCurve_pinnedX _ _)).mul
        (isPolynomialCurve_pinnedX _ _)
    intro t
    refine mem_closedIdentityComponent_of_isPolynomialCurve hcurve
      (fun t => hZ _ fun h hh => (hcomm h hh t).2) (t₀ := 0) ?_ t
    rw [show (vSL (0 : Ω) : SL2 Ω) = 1 by ext i j; fin_cases i <;> fin_cases j <;> simp [vSL],
      map_one]
  have hA : A ∈ Subgroup.closure (Set.range (sl2Upper Ω) ∪ Set.range (sl2Lower Ω)) := by
    rw [sl2_closure_upper_lower]
    exact Subgroup.mem_top A
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact hU c
    · exact hV c
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

theorem rootDiagUnit_commute_rootTripleHom (β : Fin 3 → Fin Tag.E6.rank → ℤ)
    (hβ : ∀ i, IsRoot .E6 (β i)) (horth : ∀ i j, i ≠ j → iform (β i) (β j) = 0)
    (s₁ s₂ : Ωˣ) (a : Fin Tag.E6.rank → Ωˣ) (ha : ∀ i, rootChar a (β i) = 1) (A : SL2 Ω) :
    rootDiagUnit Tag.E6 a * rootTripleHom β hβ horth s₁ s₂ A =
      rootTripleHom β hβ horth s₁ s₂ A * rootDiagUnit Tag.E6 a := by
  have h : ∀ i (A' : SL2 Ω), rootDiagUnit Tag.E6 a * rootSL2 .E6 Ω (β i) A' =
      rootSL2 .E6 Ω (β i) A' * rootDiagUnit Tag.E6 a := by
    intro i A'
    have hc := CFSG.RankThree.Chevalley.rootDiagUnit_conj_rootSL2 a (hβ i) A'
    rw [ha i, CFSG.RankThree.Chevalley.diagUnitOne_one, CFSG.RankThree.Classical.conjSL_one]
      at hc
    calc rootDiagUnit Tag.E6 a * rootSL2 .E6 Ω (β i) A' =
        (rootDiagUnit Tag.E6 a * rootSL2 .E6 Ω (β i) A' * (rootDiagUnit Tag.E6 a)⁻¹) *
          rootDiagUnit Tag.E6 a := by group
      _ = rootSL2 .E6 Ω (β i) A' * rootDiagUnit Tag.E6 a := by rw [hc]
  rw [rootTripleHom_apply]
  set A₁ := CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₁) A
  set A₂ := CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₂) A
  calc rootDiagUnit Tag.E6 a * (rootSL2 .E6 Ω (β 0) A * rootSL2 .E6 Ω (β 1) A₁ *
        rootSL2 .E6 Ω (β 2) A₂) =
      (rootDiagUnit Tag.E6 a * rootSL2 .E6 Ω (β 0) A) * rootSL2 .E6 Ω (β 1) A₁ *
        rootSL2 .E6 Ω (β 2) A₂ := by group
    _ = rootSL2 .E6 Ω (β 0) A * (rootDiagUnit Tag.E6 a * rootSL2 .E6 Ω (β 1) A₁) *
        rootSL2 .E6 Ω (β 2) A₂ := by rw [h 0]; group
    _ = rootSL2 .E6 Ω (β 0) A * rootSL2 .E6 Ω (β 1) A₁ *
        (rootDiagUnit Tag.E6 a * rootSL2 .E6 Ω (β 2) A₂) := by rw [h 1]; group
    _ = rootSL2 .E6 Ω (β 0) A * rootSL2 .E6 Ω (β 1) A₁ * rootSL2 .E6 Ω (β 2) A₂ *
        rootDiagUnit Tag.E6 a := by rw [h 2]; group

theorem commute_rootTripleHom_of_cycle (β : Fin 3 → Fin Tag.E6.rank → ℤ)
    (hβ : ∀ i, IsRoot .E6 (β i)) (horth : ∀ i j, i ≠ j → iform (β i) (β j) = 0)
    {n : ModGL Tag.E6 Ω} {s₁ t₂ t₃ : Ωˣ}
    (h₀ : ∀ A, n * rootSL2 .E6 Ω (β 0) A * n⁻¹ = rootSL2 .E6 Ω (β 1)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₁) A))
    (h₁ : ∀ A, n * rootSL2 .E6 Ω (β 1) A * n⁻¹ = rootSL2 .E6 Ω (β 2)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne t₂) A))
    (h₂ : ∀ A, n * rootSL2 .E6 Ω (β 2) A * n⁻¹ = rootSL2 .E6 Ω (β 0)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne t₃) A))
    (hn : n ^ 3 = 1) (A : SL2 Ω) :
    n * rootTripleHom β hβ horth s₁ (s₁ * t₂) A = rootTripleHom β hβ horth s₁ (s₁ * t₂) A * n := by
  have hX : ∀ (a b : Ωˣ) (B : SL2 Ω),
      CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne a)
        (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne b) B) =
      CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne (a * b)) B := by
    intro a b B
    rw [← CFSG.RankThree.Classical.conjSL_mul, CFSG.RankThree.Chevalley.diagUnitOne_mul]
  have hu : t₃ * t₂ * s₁ = 1 := by
    have h3 : ∀ B, rootSL2 .E6 Ω (β 0) B = rootSL2 .E6 Ω (β 0)
        (CFSG.RankThree.Classical.conjSL
          (CFSG.RankThree.Classical.diagUnitOne (t₃ * t₂ * s₁)) B) := by
      intro B
      have hn' : n * n * n = 1 := by rw [← pow_three']; exact hn
      have e : (n * n * n) * rootSL2 .E6 Ω (β 0) B * (n * n * n)⁻¹ =
          n * (n * (n * rootSL2 .E6 Ω (β 0) B * n⁻¹) * n⁻¹) * n⁻¹ := by group
      rw [hn', one_mul, inv_one, mul_one, h₀, h₁, h₂, hX, hX] at e
      exact e
    have h1 := CFSG.RankThree.Chevalley.rootSL2_injective_of_field (β 0) (h3 (uSL 1))
    rw [conjSL_diagUnitOne_uSL', mul_one] at h1
    have h2 := congrArg (fun B : SL2 Ω => (B : Matrix (Fin 2) (Fin 2) Ω) 0 1) h1
    simp only [uSL] at h2
    exact Units.ext (by simpa using h2.symm)
  have hcomm : ∀ i j, i ≠ j → ∀ A B : SL2 Ω,
      Commute (rootSL2 .E6 Ω (β i) A) (rootSL2 .E6 Ω (β j) B) := fun i j h A B =>
    commute_rootSL2_of_iform_eq_zero (Or.inr (Or.inl rfl)) (hβ i) (hβ j) (horth i j h) A B
  have key : n * rootTripleHom β hβ horth s₁ (s₁ * t₂) A * n⁻¹ =
      rootTripleHom β hβ horth s₁ (s₁ * t₂) A := by
    rw [rootTripleHom_apply]
    have e : ∀ x y z : ModGL Tag.E6 Ω, n * (x * y * z) * n⁻¹ =
        (n * x * n⁻¹) * (n * y * n⁻¹) * (n * z * n⁻¹) := fun x y z => by group
    rw [e, h₀, h₁, h₂, hX, hX]
    have ht : t₂ * s₁ = s₁ * t₂ := mul_comm _ _
    have ht' : t₃ * (s₁ * t₂) = 1 := by rw [← hu]; ac_rfl
    rw [ht, ht', CFSG.RankThree.Chevalley.diagUnitOne_one, CFSG.RankThree.Classical.conjSL_one,
      mul_assoc, (hcomm 2 0 (by decide) _ _).eq, ← mul_assoc,
      (hcomm 1 0 (by decide) _ _).eq]
  calc n * rootTripleHom β hβ horth s₁ (s₁ * t₂) A =
      (n * rootTripleHom β hβ horth s₁ (s₁ * t₂) A * n⁻¹) * n := by group
    _ = rootTripleHom β hβ horth s₁ (s₁ * t₂) A * n := by rw [key]

theorem diag_of_rootTriple_mem_torusGroup [IsAlgClosed Ω] (β : Fin 3 → Fin Tag.E6.rank → ℤ)
    (hβ : ∀ i, IsRoot .E6 (β i)) (horth : ∀ i j, i ≠ j → iform (β i) (β j) = 0)
    (B : Fin 3 → SL2 Ω)
    (h : rootSL2 .E6 Ω (β 0) (B 0) * rootSL2 .E6 Ω (β 1) (B 1) * rootSL2 .E6 Ω (β 2) (B 2) ∈
      torusGroup Tag.E6 Ω) (i : Fin 3) :
    (B i : Matrix (Fin 2) (Fin 2) Ω) 0 1 = 0 ∧ (B i : Matrix (Fin 2) (Fin 2) Ω) 1 0 = 0 := by
  have hc : ∀ i j, i ≠ j → ∀ A B : SL2 Ω,
      Commute (rootSL2 .E6 Ω (β i) A) (rootSL2 .E6 Ω (β j) B) := fun i j h A B =>
    commute_rootSL2_of_iform_eq_zero (Or.inr (Or.inl rfl)) (hβ i) (hβ j) (horth i j h) A B
  have hsplit : ∃ q : ModGL Tag.E6 Ω, rootSL2 .E6 Ω (β 0) (B 0) * rootSL2 .E6 Ω (β 1) (B 1) *
      rootSL2 .E6 Ω (β 2) (B 2) = rootSL2 .E6 Ω (β i) (B i) * q ∧
      ∀ A : SL2 Ω, rootSL2 .E6 Ω (β i) A * q = q * rootSL2 .E6 Ω (β i) A := by
    fin_cases i
    · exact ⟨rootSL2 .E6 Ω (β 1) (B 1) * rootSL2 .E6 Ω (β 2) (B 2), mul_assoc _ _ _,
        fun A => ((hc 0 1 (by decide) A _).mul_right (hc 0 2 (by decide) A _)).eq⟩
    · refine ⟨rootSL2 .E6 Ω (β 0) (B 0) * rootSL2 .E6 Ω (β 2) (B 2), ?_,
        fun A => ((hc 1 0 (by decide) A _).mul_right (hc 1 2 (by decide) A _)).eq⟩
      change _ = rootSL2 .E6 Ω (β 1) (B 1) * _
      rw [(hc 0 1 (by decide) _ _).eq]
      group
    · refine ⟨rootSL2 .E6 Ω (β 0) (B 0) * rootSL2 .E6 Ω (β 1) (B 1), ?_,
        fun A => ((hc 2 0 (by decide) A _).mul_right (hc 2 1 (by decide) A _)).eq⟩
      exact ((hc 2 0 (by decide) _ _).mul_right (hc 2 1 (by decide) _ _)).eq.symm
  obtain ⟨q, hq, hqc⟩ := hsplit
  refine diag_of_HSL_conj_eq fun u => CFSG.RankThree.Chevalley.rootSL2_injective_of_field (β i) ?_
  have ht : rootSL2 .E6 Ω (β i) (HSL u) ∈ torusGroup Tag.E6 Ω :=
    rootSL2_HSL_mem_torusGroup (hβ i) u
  have hcomm : rootSL2 .E6 Ω (β i) (HSL u) * (rootSL2 .E6 Ω (β 0) (B 0) *
      rootSL2 .E6 Ω (β 1) (B 1) * rootSL2 .E6 Ω (β 2) (B 2)) = (rootSL2 .E6 Ω (β 0) (B 0) *
      rootSL2 .E6 Ω (β 1) (B 1) * rootSL2 .E6 Ω (β 2) (B 2)) * rootSL2 .E6 Ω (β i) (HSL u) := by
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    obtain ⟨l', hl'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup h
    rw [hl, hl', ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  rw [hq] at hcomm
  have e := conj_eq_of_commute_mul hcomm (hqc (HSL u))
  rw [map_mul, map_mul, map_inv, e]

open CFSG.RankThree.PartOne.KE in
theorem exists_torus_mul_rootTripleHom_of_commute [IsAlgClosed Ω]
    (β : Fin 3 → Fin Tag.E6.rank → ℤ)
    (hβ : ∀ i, IsRoot .E6 (β i)) (horth : ∀ i j, i ≠ j → iform (β i) (β j) = 0)
    {n : ModGL Tag.E6 Ω} {s₁ t₂ t₃ : Ωˣ}
    (h₀ : ∀ A, n * rootSL2 .E6 Ω (β 0) A * n⁻¹ = rootSL2 .E6 Ω (β 1)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₁) A))
    (h₁ : ∀ A, n * rootSL2 .E6 Ω (β 1) A * n⁻¹ = rootSL2 .E6 Ω (β 2)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne t₂) A))
    (h₂ : ∀ A, n * rootSL2 .E6 Ω (β 2) A * n⁻¹ = rootSL2 .E6 Ω (β 0)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne t₃) A))
    (hn : n ^ 3 = 1) (hnT : ∀ t ∈ torusGroup Tag.E6 Ω, n * t * n⁻¹ ∈ torusGroup Tag.E6 Ω)
    {y : ModGL Tag.E6 Ω}
    (hy : y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (threeRootSet (β 0) (β 1) (β 2)))
    (hyn : n * y = y * n) :
    ∃ t ∈ torusGroup Tag.E6 Ω, n * t = t * n ∧
      ∃ A : SL2 Ω, y = t * rootTripleHom β hβ horth s₁ (s₁ * t₂) A := by
  have hc : ∀ i j, i ≠ j → ∀ A B : SL2 Ω,
      Commute (rootSL2 .E6 Ω (β i) A) (rootSL2 .E6 Ω (β j) B) := fun i j h A B =>
    commute_rootSL2_of_iform_eq_zero (Or.inr (Or.inl rfl)) (hβ i) (hβ j) (horth i j h) A B
  obtain ⟨b, A₀, A₁, A₂, rfl⟩ := exists_decomp (hc 0 1 (by decide)) (hc 0 2 (by decide))
    (hc 1 2 (by decide)) (hβ 0) (hβ 1) (hβ 2) hy
  set X₁ := CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₁) A₀
  set X₂ := CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne (s₁ * t₂)) A₀
  set C₁ := A₁ * X₁⁻¹ with hC₁
  set C₂ := A₂ * X₂⁻¹ with hC₂
  set d := rootDiagUnit Tag.E6 b
  set z := d * (rootSL2 .E6 Ω (β 1) C₁ * rootSL2 .E6 Ω (β 2) C₂) with hz
  have hy : d * (rootSL2 .E6 Ω (β 0) A₀ * rootSL2 .E6 Ω (β 1) A₁ * rootSL2 .E6 Ω (β 2) A₂) =
      z * rootTripleHom β hβ horth s₁ (s₁ * t₂) A₀ := by
    have e1 : rootSL2 .E6 Ω (β 1) A₁ = rootSL2 .E6 Ω (β 1) C₁ * rootSL2 .E6 Ω (β 1) X₁ := by
      rw [← map_mul, hC₁, inv_mul_cancel_right]
    have e2 : rootSL2 .E6 Ω (β 2) A₂ = rootSL2 .E6 Ω (β 2) C₂ * rootSL2 .E6 Ω (β 2) X₂ := by
      rw [← map_mul, hC₂, inv_mul_cancel_right]
    rw [rootTripleHom_apply, e1, e2, hz]
    simp only [mul_assoc]
    rw [(hc 0 1 (by decide) A₀ C₁).left_comm, (hc 1 2 (by decide) X₁ C₂).left_comm,
      (hc 0 2 (by decide) A₀ C₂).left_comm]
  have hιn := commute_rootTripleHom_of_cycle β hβ horth h₀ h₁ h₂ hn A₀
  have hzy : z = d * (rootSL2 .E6 Ω (β 0) A₀ * rootSL2 .E6 Ω (β 1) A₁ * rootSL2 .E6 Ω (β 2) A₂) *
      (rootTripleHom β hβ horth s₁ (s₁ * t₂) A₀)⁻¹ := by
    rw [hy, mul_inv_cancel_right]
  have hzn : n * z = z * n := by
    have h1 : Commute n (rootTripleHom β hβ horth s₁ (s₁ * t₂) A₀) := hιn
    have h2 : Commute n (d * (rootSL2 .E6 Ω (β 0) A₀ * rootSL2 .E6 Ω (β 1) A₁ *
        rootSL2 .E6 Ω (β 2) A₂)) := hyn
    rw [hzy]
    exact (h2.mul_right h1.inv_right).eq
  set C₁' := CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne t₂) C₁
    with hC₁'def
  set C₂' := CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne t₃) C₂
  have hconj : n * z * n⁻¹ = (n * d * n⁻¹) *
      (rootSL2 .E6 Ω (β 2) C₁' * rootSL2 .E6 Ω (β 0) C₂') := by
    rw [← h₁, ← h₂, hz]
    group
  clear_value C₁' C₂' z C₁ C₂
  have hzz : n * z * n⁻¹ = z := by rw [hzn, mul_inv_cancel_right]
  have hdd : d⁻¹ * (n * d * n⁻¹) = rootSL2 .E6 Ω (β 0) C₂'⁻¹ * rootSL2 .E6 Ω (β 1) C₁ *
      rootSL2 .E6 Ω (β 2) (C₂ * C₁'⁻¹) := by
    have e : (n * d * n⁻¹) * (rootSL2 .E6 Ω (β 2) C₁' * rootSL2 .E6 Ω (β 0) C₂') =
        d * (rootSL2 .E6 Ω (β 1) C₁ * rootSL2 .E6 Ω (β 2) C₂) := by
      rw [← hconj, hzz]
      exact hz
    rw [map_inv, map_mul, map_inv]
    have e' : d⁻¹ * (n * d * n⁻¹) = (rootSL2 .E6 Ω (β 1) C₁ * rootSL2 .E6 Ω (β 2) C₂) *
        (rootSL2 .E6 Ω (β 2) C₁' * rootSL2 .E6 Ω (β 0) C₂')⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, e, inv_mul_cancel_left]
    rw [e', mul_inv_rev]
    have k1 : Commute (rootSL2 .E6 Ω (β 0) C₂')⁻¹ (rootSL2 .E6 Ω (β 1) C₁) :=
      (hc 0 1 (by decide) _ _).inv_left
    have k2 : Commute (rootSL2 .E6 Ω (β 0) C₂')⁻¹ (rootSL2 .E6 Ω (β 2) C₂) :=
      (hc 0 2 (by decide) _ _).inv_left
    calc rootSL2 .E6 Ω (β 1) C₁ * rootSL2 .E6 Ω (β 2) C₂ *
          ((rootSL2 .E6 Ω (β 0) C₂')⁻¹ * (rootSL2 .E6 Ω (β 2) C₁')⁻¹)
        = rootSL2 .E6 Ω (β 1) C₁ * (rootSL2 .E6 Ω (β 2) C₂ * (rootSL2 .E6 Ω (β 0) C₂')⁻¹) *
            (rootSL2 .E6 Ω (β 2) C₁')⁻¹ := by group
      _ = rootSL2 .E6 Ω (β 1) C₁ * ((rootSL2 .E6 Ω (β 0) C₂')⁻¹ * rootSL2 .E6 Ω (β 2) C₂) *
            (rootSL2 .E6 Ω (β 2) C₁')⁻¹ := by rw [k2.eq]
      _ = (rootSL2 .E6 Ω (β 1) C₁ * (rootSL2 .E6 Ω (β 0) C₂')⁻¹) * rootSL2 .E6 Ω (β 2) C₂ *
            (rootSL2 .E6 Ω (β 2) C₁')⁻¹ := by group
      _ = (rootSL2 .E6 Ω (β 0) C₂')⁻¹ * rootSL2 .E6 Ω (β 1) C₁ * rootSL2 .E6 Ω (β 2) C₂ *
            (rootSL2 .E6 Ω (β 2) C₁')⁻¹ := by rw [k1.eq]
      _ = (rootSL2 .E6 Ω (β 0) C₂')⁻¹ * rootSL2 .E6 Ω (β 1) C₁ *
            (rootSL2 .E6 Ω (β 2) C₂ * (rootSL2 .E6 Ω (β 2) C₁')⁻¹) := by group
  have hdT : d⁻¹ * (n * d * n⁻¹) ∈ torusGroup Tag.E6 Ω :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (rootDiagUnit_mem_torusGroup b))
      (hnT _ (rootDiagUnit_mem_torusGroup b))
  rw [hdd] at hdT
  have hD := diag_of_rootTriple_mem_torusGroup β hβ horth ![C₂'⁻¹, C₁, C₂ * C₁'⁻¹] hdT
  obtain ⟨u₁, hu₁⟩ := eq_HSL_of_diag (hD 1).1 (hD 1).2
  obtain ⟨u₂, hu₂⟩ := eq_HSL_of_diag (hD 2).1 (hD 2).2
  have hC₁' : C₁' = HSL u₁ := by
    rw [hC₁'def, show C₁ = HSL u₁ from hu₁, conjSL_diagUnitOne_HSL]
  have hC₂ : C₂ = HSL u₂ * HSL u₁ := by
    have h : C₂ * C₁'⁻¹ = HSL u₂ := hu₂
    rw [hC₁'] at h
    rw [← h, inv_mul_cancel_right]
  refine ⟨z, ?_, hzn, A₀, hy⟩
  rw [hz, show C₁ = HSL u₁ from hu₁, hC₂, map_mul]
  exact Subgroup.mul_mem _ (rootDiagUnit_mem_torusGroup b)
    (Subgroup.mul_mem _ (rootSL2_HSL_mem_torusGroup (hβ 1) u₁)
      (Subgroup.mul_mem _ (rootSL2_HSL_mem_torusGroup (hβ 2) u₂)
        (rootSL2_HSL_mem_torusGroup (hβ 2) u₁)))

open CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.Torality in
theorem closedIdentityComponent_le_torus_mul_rootTripleHom [IsAlgClosed Ω]
    (β : Fin 3 → Fin Tag.E6.rank → ℤ)
    (hβ : ∀ i, IsRoot .E6 (β i)) (horth : ∀ i j, i ≠ j → iform (β i) (β j) = 0)
    {n : ModGL Tag.E6 Ω} {s₁ t₂ t₃ : Ωˣ}
    (h₀ : ∀ A, n * rootSL2 .E6 Ω (β 0) A * n⁻¹ = rootSL2 .E6 Ω (β 1)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₁) A))
    (h₁ : ∀ A, n * rootSL2 .E6 Ω (β 1) A * n⁻¹ = rootSL2 .E6 Ω (β 2)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne t₂) A))
    (h₂ : ∀ A, n * rootSL2 .E6 Ω (β 2) A * n⁻¹ = rootSL2 .E6 Ω (β 0)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne t₃) A))
    (hn : n ^ 3 = 1) (hnT : ∀ t ∈ torusGroup Tag.E6 Ω, n * t * n⁻¹ ∈ torusGroup Tag.E6 Ω)
    {ι₀ : Type} (a : ι₀ → Fin Tag.E6.rank → Ωˣ)
    (hker : familyKernel a = threeRootSet (β 0) (β 1) (β 2)) {Hh : Subgroup (ModGL Tag.E6 Ω)}
    (ha : ∀ i, rootDiagUnit Tag.E6 (a i) ∈ Hh) (hnH : n ∈ Hh) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)))) :
    ∃ t ∈ torusGroup Tag.E6 Ω, n * t = t * n ∧
      ∃ A : SL2 Ω, x = t * rootTripleHom β hβ horth s₁ (s₁ * t₂) A := by
  have h := closedIdentityComponent_le_familyGroup_inf_centralizer a ha hx
  have hy : x ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (threeRootSet (β 0) (β 1) (β 2)) := by
    have h1 : x ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (familyKernel a) := h.1
    rwa [hker] at h1
  exact exists_torus_mul_rootTripleHom_of_commute β hβ horth h₀ h₁ h₂ hn hnT hy
    (Subgroup.mem_centralizer_iff.1 h.2 n hnH)

theorem rootDiagUnit_conj_rootTripleHom_of_commute (β : Fin 3 → Fin Tag.E6.rank → ℤ)
    (hβ : ∀ i, IsRoot .E6 (β i)) (horth : ∀ i j, i ≠ j → iform (β i) (β j) = 0)
    {n : ModGL Tag.E6 Ω} {s₁ t₂ : Ωˣ}
    (h₀ : ∀ A, n * rootSL2 .E6 Ω (β 0) A * n⁻¹ = rootSL2 .E6 Ω (β 1)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₁) A))
    (h₁ : ∀ A, n * rootSL2 .E6 Ω (β 1) A * n⁻¹ = rootSL2 .E6 Ω (β 2)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne t₂) A))
    (b : Fin Tag.E6.rank → Ωˣ) (hbn : n * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * n)
    (A : SL2 Ω) :
    rootDiagUnit Tag.E6 b * rootTripleHom β hβ horth s₁ (s₁ * t₂) A *
        (rootDiagUnit Tag.E6 b)⁻¹ =
      rootTripleHom β hβ horth s₁ (s₁ * t₂)
        (CFSG.RankThree.Classical.conjSL
          (CFSG.RankThree.Classical.diagUnitOne (rootChar b (β 0))) A) := by
  have hd := fun i => CFSG.RankThree.Chevalley.rootDiagUnit_conj_rootSL2 (K := Ω) b (hβ i)
  have step : ∀ (i j : Fin 3) (s : Ωˣ),
      (∀ A, n * rootSL2 .E6 Ω (β i) A * n⁻¹ = rootSL2 .E6 Ω (β j)
        (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s) A)) →
      rootChar b (β j) = rootChar b (β i) := by
    intro i j s hij
    have e : rootSL2 .E6 Ω (β j) (CFSG.RankThree.Classical.conjSL
          (CFSG.RankThree.Classical.diagUnitOne (rootChar b (β j)))
          (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s) (uSL 1))) =
        rootSL2 .E6 Ω (β j) (CFSG.RankThree.Classical.conjSL
          (CFSG.RankThree.Classical.diagUnitOne s)
          (CFSG.RankThree.Classical.conjSL
            (CFSG.RankThree.Classical.diagUnitOne (rootChar b (β i))) (uSL 1))) := by
      rw [← hd j, ← hij, ← hij, ← hd i]
      have hb' : n * rootDiagUnit Tag.E6 b * n⁻¹ = rootDiagUnit Tag.E6 b := by
        rw [hbn, mul_inv_cancel_right]
      calc rootDiagUnit Tag.E6 b * (n * rootSL2 .E6 Ω (β i) (uSL 1) * n⁻¹) *
            (rootDiagUnit Tag.E6 b)⁻¹
          = (n * rootDiagUnit Tag.E6 b * n⁻¹) * (n * rootSL2 .E6 Ω (β i) (uSL 1) * n⁻¹) *
              (n * rootDiagUnit Tag.E6 b * n⁻¹)⁻¹ := by rw [hb']
        _ = n * (rootDiagUnit Tag.E6 b * rootSL2 .E6 Ω (β i) (uSL 1) *
              (rootDiagUnit Tag.E6 b)⁻¹) * n⁻¹ := by group
    have e2 := CFSG.RankThree.Chevalley.rootSL2_injective_of_field (β j) e
    rw [conjSL_diagUnitOne_uSL', conjSL_diagUnitOne_uSL', conjSL_diagUnitOne_uSL',
      conjSL_diagUnitOne_uSL'] at e2
    have e3 := congrArg (fun B : SL2 Ω => (B : Matrix (Fin 2) (Fin 2) Ω) 0 1) e2
    simp only [uSL, mul_one] at e3
    have e4 : ((rootChar b (β j) : Ωˣ) : Ω) * s = s * rootChar b (β i) := by simpa using e3
    exact Units.ext (mul_right_cancel₀ s.ne_zero (by rw [e4, mul_comm]))
  have c1 := step 0 1 s₁ h₀
  have c2 := (step 1 2 t₂ h₁).trans c1
  rw [rootTripleHom_apply, rootTripleHom_apply]
  have e : ∀ x y z : ModGL Tag.E6 Ω, rootDiagUnit Tag.E6 b * (x * y * z) *
      (rootDiagUnit Tag.E6 b)⁻¹ = (rootDiagUnit Tag.E6 b * x * (rootDiagUnit Tag.E6 b)⁻¹) *
        (rootDiagUnit Tag.E6 b * y * (rootDiagUnit Tag.E6 b)⁻¹) *
        (rootDiagUnit Tag.E6 b * z * (rootDiagUnit Tag.E6 b)⁻¹) := fun x y z => by group
  rw [e, hd 0, hd 1, hd 2, c1, c2, conjSL_diagUnitOne_comm (rootChar b (β 0)) s₁,
    conjSL_diagUnitOne_comm (rootChar b (β 0)) (s₁ * t₂)]

theorem exists_central_mul_of_torus_conj [IsAlgClosed Ω] {K : Subgroup (ModGL Tag.E6 Ω)}
    (ι : SL2 Ω →* ModGL Tag.E6 Ω) (hιK : ∀ A, ι A ∈ K)
    (hHSL : ∀ u : Ωˣ, ι (HSL u) ∈ torusGroup Tag.E6 Ω)
    (hdec : ∀ y ∈ K, ∃ b : Fin Tag.E6.rank → Ωˣ, ∃ c : Ωˣ,
      (∀ A, rootDiagUnit Tag.E6 b * ι A * (rootDiagUnit Tag.E6 b)⁻¹ =
        ι (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne c) A)) ∧
      ∃ A, y = rootDiagUnit Tag.E6 b * ι A)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ K) :
    ∃ z ∈ K, z ∈ torusGroup Tag.E6 Ω ∧ (∀ y ∈ K, z * y = y * z) ∧
      ∃ B : SL2 Ω, x = z * ι B := by
  obtain ⟨b, c, hbc, A, rfl⟩ := hdec x hx
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq ((c : Ωˣ) : Ω) two_pos
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact c.ne_zero (by rw [← hv]; ring)
  set u := Units.mk0 v hv0
  have huu : u * u = c := Units.ext (by rw [Units.val_mul]; simp [u, ← hv, sq])
  have hbT : rootDiagUnit Tag.E6 b ∈ torusGroup Tag.E6 Ω :=
    CFSG.LieType.Chevalley.rootDiagUnit_mem_torusGroup b
  have hzT : rootDiagUnit Tag.E6 b * (ι (HSL u))⁻¹ ∈ torusGroup Tag.E6 Ω :=
    Subgroup.mul_mem _ hbT (Subgroup.inv_mem _ (hHSL u))
  refine ⟨rootDiagUnit Tag.E6 b * (ι (HSL u))⁻¹, ?_, hzT, ?_, HSL u * A, ?_⟩
  · have hbK : rootDiagUnit Tag.E6 b ∈ K := by
      have h := Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hιK A))
      rwa [mul_inv_cancel_right] at h
    exact Subgroup.mul_mem _ hbK (Subgroup.inv_mem _ (hιK _))
  · intro y hy
    obtain ⟨b', -, -, A', rfl⟩ := hdec y hy
    have k1 : rootDiagUnit Tag.E6 b * (ι (HSL u))⁻¹ * rootDiagUnit Tag.E6 b' =
        rootDiagUnit Tag.E6 b' * (rootDiagUnit Tag.E6 b * (ι (HSL u))⁻¹) := by
      obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hzT
      rw [hl, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    have k2 : rootDiagUnit Tag.E6 b * (ι (HSL u))⁻¹ * ι A' =
        ι A' * (rootDiagUnit Tag.E6 b * (ι (HSL u))⁻¹) := by
      have hc := hbc ((HSL u)⁻¹ * A' * HSL u)
      have e1 : (HSL u)⁻¹ * A' * HSL u = HSL u⁻¹ * A' * (HSL u⁻¹)⁻¹ := by
        congr 1
        · congr 1
          apply Subtype.ext
          rw [Matrix.SpecialLinearGroup.coe_inv, coe_HSL, coe_HSL, Matrix.adjugate_fin_two]
          simp
        · apply Subtype.ext
          rw [Matrix.SpecialLinearGroup.coe_inv, coe_HSL, coe_HSL, Matrix.adjugate_fin_two]
          simp
      have e3 : CFSG.RankThree.Classical.conjSL
          (CFSG.RankThree.Classical.diagUnitOne c) ((HSL u)⁻¹ * A' * HSL u) = A' := by
        rw [e1, HSL_conj_eq_conjSL, ← CFSG.RankThree.Classical.conjSL_mul,
          CFSG.RankThree.Chevalley.diagUnitOne_mul, ← huu,
          show u * u * (u⁻¹ * u⁻¹) = 1 by group, CFSG.RankThree.Chevalley.diagUnitOne_one,
          CFSG.RankThree.Classical.conjSL_one]
      rw [e3, map_mul, map_mul, map_inv] at hc
      calc rootDiagUnit Tag.E6 b * (ι (HSL u))⁻¹ * ι A'
          = (rootDiagUnit Tag.E6 b * ((ι (HSL u))⁻¹ * ι A' * ι (HSL u)) *
              (rootDiagUnit Tag.E6 b)⁻¹) * (rootDiagUnit Tag.E6 b * (ι (HSL u))⁻¹) := by group
        _ = ι A' * (rootDiagUnit Tag.E6 b * (ι (HSL u))⁻¹) := by rw [hc]
    calc rootDiagUnit Tag.E6 b * (ι (HSL u))⁻¹ * (rootDiagUnit Tag.E6 b' * ι A')
        = (rootDiagUnit Tag.E6 b * (ι (HSL u))⁻¹ * rootDiagUnit Tag.E6 b') * ι A' := by group
      _ = rootDiagUnit Tag.E6 b' * (rootDiagUnit Tag.E6 b * (ι (HSL u))⁻¹ * ι A') := by
        rw [k1]; group
      _ = rootDiagUnit Tag.E6 b' * ι A' * (rootDiagUnit Tag.E6 b * (ι (HSL u))⁻¹) := by
        rw [k2]; group
  · show rootDiagUnit Tag.E6 b * ι A = rootDiagUnit Tag.E6 b * (ι (HSL u))⁻¹ * ι (HSL u * A)
    rw [map_mul]
    group

open CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.Torality in
theorem exists_central_mul_rootTripleHom [IsAlgClosed Ω]
    (β : Fin 3 → Fin Tag.E6.rank → ℤ)
    (hβ : ∀ i, IsRoot .E6 (β i)) (horth : ∀ i j, i ≠ j → iform (β i) (β j) = 0)
    {n : ModGL Tag.E6 Ω} {s₁ t₂ t₃ : Ωˣ}
    (h₀ : ∀ A, n * rootSL2 .E6 Ω (β 0) A * n⁻¹ = rootSL2 .E6 Ω (β 1)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₁) A))
    (h₁ : ∀ A, n * rootSL2 .E6 Ω (β 1) A * n⁻¹ = rootSL2 .E6 Ω (β 2)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne t₂) A))
    (h₂ : ∀ A, n * rootSL2 .E6 Ω (β 2) A * n⁻¹ = rootSL2 .E6 Ω (β 0)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne t₃) A))
    (hn : n ^ 3 = 1) (hnT : ∀ t ∈ torusGroup Tag.E6 Ω, n * t * n⁻¹ ∈ torusGroup Tag.E6 Ω)
    {ι₀ : Type} (a : ι₀ → Fin Tag.E6.rank → Ωˣ)
    (hker : familyKernel a = threeRootSet (β 0) (β 1) (β 2)) {Hh : Subgroup (ModGL Tag.E6 Ω)}
    (ha : ∀ i, rootDiagUnit Tag.E6 (a i) ∈ Hh) (hnH : n ∈ Hh)
    (hHι : ∀ h ∈ Hh, ∀ A, h * rootTripleHom β hβ horth s₁ (s₁ * t₂) A =
      rootTripleHom β hβ horth s₁ (s₁ * t₂) A * h) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω)))) :
    ∃ z ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
        Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))),
      z ∈ torusGroup Tag.E6 Ω ∧
      (∀ y ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
        Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))), z * y = y * z) ∧
      ∃ B : SL2 Ω, x = z * rootTripleHom β hβ horth s₁ (s₁ * t₂) B := by
  set ι := rootTripleHom β hβ horth s₁ (s₁ * t₂) with hιdef
  have hιK : ∀ A, ι A ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) := fun A =>
    rootTripleHom_mem_closedIdentityComponent β hβ horth s₁ (s₁ * t₂)
      (fun h hh t => ⟨hHι h hh _, hHι h hh _⟩) A
  have hHSL : ∀ u : Ωˣ, ι (HSL u) ∈ torusGroup Tag.E6 Ω := by
    intro u
    rw [hιdef, rootTripleHom_apply, conjSL_diagUnitOne_HSL, conjSL_diagUnitOne_HSL]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (rootSL2_HSL_mem_torusGroup (hβ 0) u)
      (rootSL2_HSL_mem_torusGroup (hβ 1) u)) (rootSL2_HSL_mem_torusGroup (hβ 2) u)
  refine exists_central_mul_of_torus_conj ι hιK hHSL (fun y hy => ?_) hx
  obtain ⟨t, htT, htn, A, rfl⟩ := closedIdentityComponent_le_torus_mul_rootTripleHom (s₁ := s₁)
    (t₂ := t₂) (t₃ := t₃) β hβ horth h₀ h₁ h₂ hn hnT a hker ha hnH hy
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htT
  exact ⟨b, rootChar b (β 0),
    fun A' => rootDiagUnit_conj_rootTripleHom_of_commute β hβ horth h₀ h₁ b htn A', A, rfl⟩

end RootTriple

section RationalCoordinatePoints

open WithConv CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.E6Descent

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
  (Fr : Ω →+* Ω) (Hh : Subgroup (ModGL TwistTag.E6.tag Ω))

end RationalCoordinatePoints

section RootTripleFrobenius

open CFSG.HardMathSupport.Lang.E6Descent CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem commutatorElement_mul_left_of_commute {G : Type*} [Group G] {z a y : G}
    (hza : Commute z a) (hzy : Commute z y) : ⁅z * a, y⁆ = ⁅a, y⁆ := by
  have h : Commute z ⁅a, y⁆ := by
    rw [commutatorElement_def]
    exact ((hza.mul_right hzy).mul_right hza.inv_right).mul_right hzy.inv_right
  have hzy' : z⁻¹ * y⁻¹ = y⁻¹ * z⁻¹ := hzy.inv_inv.eq
  calc ⁅z * a, y⁆ = z * a * y * a⁻¹ * (z⁻¹ * y⁻¹) := by
        rw [commutatorElement_def, mul_inv_rev]; group
    _ = z * ⁅a, y⁆ * z⁻¹ := by rw [hzy', commutatorElement_def]; group
    _ = ⁅a, y⁆ := by rw [h.eq, mul_inv_cancel_right]

private theorem commutatorElement_mul_right_of_commute {G : Type*} [Group G] {w a b : G}
    (hwa : Commute w a) (hwb : Commute w b) : ⁅a, w * b⁆ = ⁅a, b⁆ := by
  rw [← inv_inj, commutatorElement_inv, commutatorElement_inv,
    commutatorElement_mul_left_of_commute hwb hwa]

variable
  {Ω : Type} [Field Ω]

theorem twistHom_mem_range_of_central_mul {n : ℕ} {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = (2 ^ n) ^ 2) [Algebra k Ω] [IsAlgClosure k Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {Hh : Subgroup (ModGL Tag.E6 Ω)} (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    {m : ℕ} (hm : 2 ≤ m) (ι : SL(m, Ω) →* ModGL Tag.E6 Ω)
    (hιK : ∀ B, ι B ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hdec : ∀ x ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))), ∃ z ∈ closedIdentityComponent
        (adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))),
      (∀ y ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
        Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))), z * y = y * z) ∧ ∃ B, x = z * ι B)
    (B : SL(m, Ω)) : twistHom TwistTag.E6 Ω Fr (ι B) ∈ ι.range := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hperf : commutator (SL(m, Ω)) = ⊤ := Group.isPerfect_def.1
    (CFSG.RankThree.Classical2.isPerfect_specialLinearGroup_of_infinite (n := m) hm)
  set Φ : SL(m, Ω) →* ModGL Tag.E6 Ω := (twistHom TwistTag.E6 Ω Fr).comp ι with hΦ
  change Φ B ∈ ι.range
  have hB : B ∈ commutator (SL(m, Ω)) := hperf ▸ Subgroup.mem_top B
  rw [commutator_def, Subgroup.commutator_def] at hB
  induction hB using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, -, b, -, rfl⟩ := hx
    obtain ⟨za, hzaK, hza, a', ha'⟩ := hdec _ (twistHom_mem_hypCentConn hk Fr hFr hHF (hιK a))
    obtain ⟨zb, hzbK, hzb, b', hb'⟩ := hdec _ (twistHom_mem_hypCentConn hk Fr hFr hHF (hιK b))
    refine ⟨⁅a', b'⁆, ?_⟩
    calc ι ⁅a', b'⁆ = ⁅ι a', ι b'⁆ := map_commutatorElement ι a' b'
      _ = ⁅za * ι a', zb * ι b'⁆ := by
        rw [commutatorElement_mul_left_of_commute (hza _ (hιK a'))
          (hza _ (Subgroup.mul_mem _ hzbK (hιK b'))),
          commutatorElement_mul_right_of_commute ((hzb _ (hιK a')).symm.symm) (hzb _ (hιK b'))]
      _ = ⁅Φ a, Φ b⁆ := congrArg₂ (fun x y => ⁅x, y⁆) ha'.symm hb'.symm
      _ = Φ ⁅a, b⁆ := (map_commutatorElement Φ a b).symm
  | one => exact ⟨1, by rw [map_one, map_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' * y', by rw [map_mul, hx', hy', map_mul]⟩
  | inv x _ hx =>
    obtain ⟨x', hx'⟩ := hx
    exact ⟨x'⁻¹, by rw [map_inv, hx', map_inv]⟩

theorem twistHom_rootTriple_torus [IsAlgClosed Ω] (Fr : Ω →+* Ω) {q : ℕ} (hq : 0 < q)
    (hFr : ∀ c, Fr c = c ^ q) (ι : SL(2, Ω) →* ModGL Tag.E6 Ω) (g : ModGL Tag.E6 Ω)
    (m : Fin Tag.E6.rank → ℤ)
    (hιD : ∀ u : Ωˣ, ι (HSL u) = g⁻¹ * rootDiagUnit Tag.E6 (fun i => u ^ m i) * g)
    (hFD : ∀ s : Ωˣ, ∃ v : Ωˣ, twistHom TwistTag.E6 Ω Fr (ι (HSL s)) = ι (HSL v))
    {ℓ₁ : Label Tag.E6} (hℓ₁ : ∑ i, labelWt Tag.E6 ℓ₁ i * m i = 1) :
    (∀ s : Ωˣ, twistHom TwistTag.E6 Ω Fr (ι (HSL s)) = ι (HSL (s ^ q))) ∨
      ∀ s : Ωˣ, twistHom TwistTag.E6 Ω Fr (ι (HSL s)) = (ι (HSL (s ^ q)))⁻¹ := by
  classical
  set d : Ωˣ → ModGL Tag.E6 Ω := fun u => rootDiagUnit Tag.E6 (fun i => u ^ m i) with hd
  set P : ModGL Tag.E6 Ω := diagramMap TwistTag.E6 Ω with hP
  set R : ModGL Tag.E6 Ω := g * P * (Units.map (entrywiseHom Fr) g)⁻¹ with hR
  have hFdef : ∀ y : ModGL Tag.E6 Ω, twistHom TwistTag.E6 Ω Fr y =
      P * Units.map (entrywiseHom Fr) y * P⁻¹ := fun y => rfl
  have hF : ∀ s : Ωˣ, twistHom TwistTag.E6 Ω Fr (ι (HSL s)) = g⁻¹ * (R * d (s ^ q) * R⁻¹) * g := by
    intro s
    have e : rootDiagUnit Tag.E6 ((fun i => s ^ m i) ^ q) = d (s ^ q) := by
      show rootDiagUnit Tag.E6 _ = rootDiagUnit Tag.E6 _
      congr 1
      funext i
      rw [Pi.pow_apply, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [hFdef, hιD, map_mul, map_mul, map_inv,
      CFSG.HardMathSupport.Foote.Coordinator.entrywise_frob_rootDiagUnit' hFr, e, hR]
    group
    rfl
  have hroot : ∀ u : Ωˣ, ∃ s : Ωˣ, s ^ q = u := by
    intro u
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (u : Ω) hq
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by rw [← hx, zero_pow hq.ne'])
    exact ⟨Units.mk0 x hx0, Units.ext (by simp [hx])⟩
  have hθ : ∀ u : Ωˣ, ∃ v : Ωˣ, R * d u * R⁻¹ = d v := by
    intro u
    obtain ⟨s, rfl⟩ := hroot u
    obtain ⟨v, hv⟩ := hFD s
    refine ⟨v, ?_⟩
    have e := (hF s).symm.trans hv
    rw [hιD] at e
    have e' := congrArg (fun x => g * x * g⁻¹) e
    rw [show g * (g⁻¹ * (R * d (s ^ q) * R⁻¹) * g) * g⁻¹ = R * d (s ^ q) * R⁻¹ by group,
      show g * (g⁻¹ * rootDiagUnit Tag.E6 (fun i => v ^ m i) * g) * g⁻¹ =
        rootDiagUnit Tag.E6 (fun i => v ^ m i) by group] at e'
    exact e'
  choose θ hθ' using hθ
  rcases eq_or_eq_inv_of_conj_rootDiagUnit m R θ hθ' hℓ₁ with h | h
  · refine Or.inl fun s => ?_
    rw [hF, hθ', h, hιD]
  · have hdinv : ∀ u : Ωˣ, d u⁻¹ = (d u)⁻¹ := by
      intro u
      show rootDiagUnit Tag.E6 (fun i => u⁻¹ ^ m i) = (rootDiagUnit Tag.E6 (fun i => u ^ m i))⁻¹
      rw [CFSG.LieType.Chevalley.rootDiagUnit_inv]
      congr 1
      funext i
      simp
    refine Or.inr fun s => ?_
    rw [hF, hθ', h, hdinv, hιD, mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]

theorem conj_mem_closedIdentityComponent_iff {Hh : Subgroup (ModGL Tag.E6 Ω)}
    {y₀ : ModGL Tag.E6 Ω} (hy₀ : y₀ ∈ adjointGroup Tag.E6 Ω) (z : ModGL Tag.E6 Ω) :
    y₀ * z * y₀⁻¹ ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer
        ((Hh.map (MulAut.conj y₀).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) :
          Set (ModGL Tag.E6 Ω))) ↔
      z ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
        Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) := by
  rw [← CFSG.LieType.AlgebraicGroups.map_adjoint_centralizer_conj Hh hy₀,
    CFSG.LieType.AlgebraicGroups.closedIdentityComponent_map_conj]
  constructor
  · rintro ⟨w, hw, hwz⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwz
    have : w = z := by
      have h := congrArg (fun v => y₀⁻¹ * v * y₀) hwz
      rwa [show y₀⁻¹ * (y₀ * w * y₀⁻¹) * y₀ = w by group,
        show y₀⁻¹ * (y₀ * z * y₀⁻¹) * y₀ = z by group] at h
    exact this ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

open CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.Torality in
theorem isQuasisimple_jgeom_of_torusFrame {Fr : Ω →+* Ω} {Hh : Subgroup (ModGL Tag.E6 Ω)}
    [Finite ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)]
    {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k] [Finite k] [Algebra k Ω] [IsAlgClosure k Ω]
    (hk : Nat.card k = (2 ^ n) ^ 2) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    {y₀ : ModGL Tag.E6 Ω} (hy₀ : y₀ ∈ adjointGroup Tag.E6 Ω)
    (ι : SL(2, Ω) →* ModGL Tag.E6 Ω) (hιinj : Function.Injective ι)
    (hιK : ∀ A, ι A ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer
      ((Hh.map (MulAut.conj y₀).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω))))
    (m : Fin Tag.E6.rank → ℤ) (hγ : ∀ u : Ωˣ, ι (HSL u) = rootDiagUnit Tag.E6 (fun i => u ^ m i))
    {ℓ₁ : Label Tag.E6} (hℓ₁ : ∑ i, labelWt Tag.E6 ℓ₁ i * m i = 1)
    (hKT : ∀ z ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓ Subgroup.centralizer
      ((Hh.map (MulAut.conj y₀).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω))),
      ∃ b : Fin Tag.E6.rank → Ωˣ, ∃ c : Ωˣ,
        (∀ A, rootDiagUnit Tag.E6 b * ι A * (rootDiagUnit Tag.E6 b)⁻¹ =
          ι (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne c) A)) ∧
        ∃ A, z = rootDiagUnit Tag.E6 b * ι A)
    {e g : ModGL Tag.E6 Ω}
    (heK : e ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (heF : e ∈ TwistedDiag.Rgrp Ω Fr) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {t : ℕ} (hg2 : g ^ (2 ^ t) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) {be : Fin Tag.E6.rank → Ωˣ}
    (heT : y₀ * e * y₀⁻¹ = rootDiagUnit Tag.E6 be) {ce : Ωˣ}
    (hce : ∀ A, rootDiagUnit Tag.E6 be * ι A * (rootDiagUnit Tag.E6 be)⁻¹ =
      ι (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne ce) A)) :
    CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap k Ω).injective 2
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  set K := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
    Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) with hKdef
  set H' := Hh.map (MulAut.conj y₀).toMonoidHom with hH'
  set K' := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
    Subgroup.centralizer (H' : Set (ModGL Tag.E6 Ω))) with hK'def
  have hconj : ∀ z, y₀ * z * y₀⁻¹ ∈ K' ↔ z ∈ K := conj_mem_closedIdentityComponent_iff hy₀
  set ιa : SL(2, Ω) →* ModGL Tag.E6 Ω := (MulAut.conj y₀⁻¹).toMonoidHom.comp ι with hιa
  have hιa_apply : ∀ B, ιa B = y₀⁻¹ * ι B * y₀ := fun B => by
    simp only [hιa, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hιainj : Function.Injective ιa := by
    intro A B h
    rw [hιa_apply, hιa_apply] at h
    apply hιinj
    have h' := congrArg (fun v => y₀ * v * y₀⁻¹) h
    rwa [show y₀ * (y₀⁻¹ * ι A * y₀) * y₀⁻¹ = ι A by group,
      show y₀ * (y₀⁻¹ * ι B * y₀) * y₀⁻¹ = ι B by group] at h'
  have hιaK : ∀ B, ιa B ∈ K := by
    intro B
    rw [← hconj, hιa_apply, show y₀ * (y₀⁻¹ * ι B * y₀) * y₀⁻¹ = ι B by group]
    exact hιK B
  have hdec : ∀ z ∈ K, ∃ w ∈ K, (∀ v ∈ K, w * v = v * w) ∧
      y₀ * w * y₀⁻¹ ∈ torusGroup Tag.E6 Ω ∧ ∃ B, z = w * ιa B := by
    intro z hz
    obtain ⟨w', hw'K, hw'T, hw'c, B, hB⟩ := exists_central_mul_of_torus_conj ι hιK
      (fun u => by rw [hγ u]; exact CFSG.LieType.Chevalley.rootDiagUnit_mem_torusGroup _) hKT
      ((hconj z).2 hz)
    refine ⟨y₀⁻¹ * w' * y₀, ?_, ?_, ?_, B, ?_⟩
    · rw [← hconj, show y₀ * (y₀⁻¹ * w' * y₀) * y₀⁻¹ = w' by group]
      exact hw'K
    · intro v hv
      have hc := hw'c _ ((hconj v).2 hv)
      calc y₀⁻¹ * w' * y₀ * v = y₀⁻¹ * (w' * (y₀ * v * y₀⁻¹)) * y₀ := by group
        _ = y₀⁻¹ * ((y₀ * v * y₀⁻¹) * w') * y₀ := by rw [hc]
        _ = v * (y₀⁻¹ * w' * y₀) := by group
    · rw [show y₀ * (y₀⁻¹ * w' * y₀) * y₀⁻¹ = w' by group]
      exact hw'T
    · rw [hιa_apply]
      calc z = y₀⁻¹ * (y₀ * z * y₀⁻¹) * y₀ := by group
        _ = y₀⁻¹ * (w' * ι B) * y₀ := by rw [hB]
        _ = y₀⁻¹ * w' * y₀ * (y₀⁻¹ * ι B * y₀) := by group
  have hFι : ∀ B, twistHom TwistTag.E6 Ω Fr (ιa B) ∈ ιa.range :=
    twistHom_mem_range_of_central_mul hk Fr hFr hHF le_rfl ιa hιaK fun z hz => by
      obtain ⟨w, hwK, hwc, -, B, hB⟩ := hdec z hz
      exact ⟨w, hwK, hwc, B, hB⟩
  let e₀ : SL(2, Ω) ≃* ιa.range := MonoidHom.ofInjective hιainj
  let Fι : SL(2, Ω) →* ιa.range :=
    ((twistHom TwistTag.E6 Ω Fr).comp ιa).codRestrict ιa.range hFι
  let τ : SL(2, Ω) →* SL(2, Ω) := e₀.symm.toMonoidHom.comp Fι
  have hιτ : ∀ B, ιa (τ B) = twistHom TwistTag.E6 Ω Fr (ιa B) := fun B =>
    (MonoidHom.ofInjective_apply hιainj (x := e₀.symm (Fι B))).symm.trans
      (congrArg Subtype.val (e₀.apply_symm_apply (Fι B)))
  set b := be with hbdef
  have hb : y₀ * e * y₀⁻¹ = rootDiagUnit Tag.E6 b := heT
  set c := ce with hcdef
  have hconjι : ∀ A, rootDiagUnit Tag.E6 b * ι A * (rootDiagUnit Tag.E6 b)⁻¹ =
      ι (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne c) A) := hce
  have hc1 : c ≠ 1 := by
    intro hc
    have hcent : ∀ v ∈ K', rootDiagUnit Tag.E6 b * v = v * rootDiagUnit Tag.E6 b := by
      intro v hv
      obtain ⟨l, -, -, A, rfl⟩ := hKT v hv
      have k1 : rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 l =
          rootDiagUnit Tag.E6 l * rootDiagUnit Tag.E6 b := by
        rw [← CFSG.LieType.Chevalley.rootDiagUnit_mul,
          ← CFSG.LieType.Chevalley.rootDiagUnit_mul, mul_comm]
      have k2 : rootDiagUnit Tag.E6 b * ι A = ι A * rootDiagUnit Tag.E6 b := by
        have h := hconjι A
        rw [hc, CFSG.RankThree.Chevalley.diagUnitOne_one, CFSG.RankThree.Classical.conjSL_one]
          at h
        calc rootDiagUnit Tag.E6 b * ι A = (rootDiagUnit Tag.E6 b * ι A *
              (rootDiagUnit Tag.E6 b)⁻¹) * rootDiagUnit Tag.E6 b := by group
          _ = ι A * rootDiagUnit Tag.E6 b := by rw [h]
      calc rootDiagUnit Tag.E6 b * (rootDiagUnit Tag.E6 l * ι A)
          = (rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 l) * ι A := by group
        _ = rootDiagUnit Tag.E6 l * (rootDiagUnit Tag.E6 b * ι A) := by rw [k1]; group
        _ = rootDiagUnit Tag.E6 l * ι A * rootDiagUnit Tag.E6 b := by rw [k2]; group
    have hg' := hcent _ ((hconj g).2 hgK)
    rw [← hb] at hg'
    have hge : g * e = e * g := by
      have h := congrArg (fun v => y₀⁻¹ * v * y₀) hg'
      rw [show y₀⁻¹ * (y₀ * e * y₀⁻¹ * (y₀ * g * y₀⁻¹)) * y₀ = e * g by group,
        show y₀⁻¹ * (y₀ * g * y₀⁻¹ * (y₀ * e * y₀⁻¹)) * y₀ = g * e by group] at h
      exact h.symm
    have hee : e = e⁻¹ := by rw [← hinv, hge, mul_inv_cancel_right]
    apply he1
    have h2 : e ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [hee]
      exact mul_inv_cancel e
    calc e = e ^ 3 * (e ^ 2)⁻¹ := by group
      _ = 1 := by rw [he3, h2]; group
  have hFD : ∀ s : Ωˣ, ∃ v : Ωˣ, twistHom TwistTag.E6 Ω Fr (ιa (HSL s)) = ιa (HSL v) := by
    intro s
    obtain ⟨B, hB⟩ := hFι (HSL s)
    have h1 : ιa (HSL s) * e = e * ιa (HSL s) := by
      rw [hιa_apply, hγ]
      have k : rootDiagUnit Tag.E6 (fun i => s ^ m i) * (y₀ * e * y₀⁻¹) =
          (y₀ * e * y₀⁻¹) * rootDiagUnit Tag.E6 (fun i => s ^ m i) := by
        rw [hb, ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
          ← CFSG.LieType.Chevalley.rootDiagUnit_mul, mul_comm]
      calc y₀⁻¹ * rootDiagUnit Tag.E6 (fun i => s ^ m i) * y₀ * e
          = y₀⁻¹ * (rootDiagUnit Tag.E6 (fun i => s ^ m i) * (y₀ * e * y₀⁻¹)) * y₀ := by group
        _ = y₀⁻¹ * ((y₀ * e * y₀⁻¹) * rootDiagUnit Tag.E6 (fun i => s ^ m i)) * y₀ := by rw [k]
        _ = e * (y₀⁻¹ * rootDiagUnit Tag.E6 (fun i => s ^ m i) * y₀) := by group
    let F' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω := twistHom TwistTag.E6 Ω Fr
    have hFe : F' e = e := heF.2
    have h2 : ιa B * e = e * ιa B := by
      have h := congrArg F' h1
      rw [map_mul, map_mul, hFe] at h
      have hB' : ιa B = F' (ιa (HSL s)) := hB
      rw [hB']
      exact h
    have h3 : rootDiagUnit Tag.E6 b * ι B * (rootDiagUnit Tag.E6 b)⁻¹ = ι B := by
      rw [hιa_apply] at h2
      rw [← hb]
      have h := congrArg (fun v => y₀ * v * y₀⁻¹) h2
      rw [show y₀ * (y₀⁻¹ * ι B * y₀ * e) * y₀⁻¹ = ι B * (y₀ * e * y₀⁻¹) by group,
        show y₀ * (e * (y₀⁻¹ * ι B * y₀)) * y₀⁻¹ = (y₀ * e * y₀⁻¹) * ι B by group] at h
      rw [← h, mul_inv_cancel_right]
    rw [hconjι] at h3
    obtain ⟨d01, d10⟩ := diag_of_conjSL_diagUnitOne_eq hc1 (hιinj h3)
    obtain ⟨v, rfl⟩ := eq_HSL_of_diag d01 d10
    exact ⟨v, hB.symm⟩
  have hιD : ∀ u : Ωˣ, ιa (HSL u) = y₀⁻¹ * rootDiagUnit Tag.E6 (fun i => u ^ m i) * y₀ :=
    fun u => by rw [hιa_apply, hγ]
  have hFT := twistHom_rootTriple_torus Fr (show 0 < 2 ^ n by positivity) hFr ιa y₀ m hιD hFD hℓ₁
  have hT : (∀ s : Ωˣ, τ (sl2Diag Ω s) = sl2Diag Ω (s ^ 2 ^ n)) ∨
      ∀ s : Ωˣ, τ (sl2Diag Ω s) = (sl2Diag Ω (s ^ 2 ^ n))⁻¹ := by
    rcases hFT with h | h
    · exact Or.inl fun s => hιainj (by rw [hιτ]; exact h s)
    · exact Or.inr fun s => hιainj (by rw [hιτ, map_inv]; exact h s)
  obtain ⟨X, hX⟩ := CFSG.RankThree.Classical2.eq_conjSLn_comp_map_of_sl2Diag Fr hFr τ hT
  have hσ : ∀ B, twistHom TwistTag.E6 Ω Fr (ιa B) =
      ιa (CFSG.RankThree.Classical2.conjSLn X (Matrix.SpecialLinearGroup.map Fr B)) := by
    intro B
    rw [← hιτ, hX]
    rfl
  have hFrsurj : Function.Surjective Fr := by
    intro c
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq c (show 0 < 2 ^ n by positivity)
    exact ⟨r, by rw [hFr, hr]⟩
  let Φ : Ω ≃+* Ω := RingEquiv.ofBijective Fr ⟨Fr.injective, hFrsurj⟩
  have hτsurj : Function.Surjective τ := by
    intro B
    refine ⟨Matrix.SpecialLinearGroup.map (Φ.symm : Ω →+* Ω)
      (CFSG.RankThree.Classical2.conjSLn X⁻¹ B), ?_⟩
    rw [hX]
    apply Subtype.ext
    change ((CFSG.RankThree.Classical2.conjSLn X (Matrix.SpecialLinearGroup.map Fr
      (Matrix.SpecialLinearGroup.map (Φ.symm : Ω →+* Ω)
        (CFSG.RankThree.Classical2.conjSLn X⁻¹ B))) : SL(2, Ω)) : Matrix (Fin 2) (Fin 2) Ω) = B
    have hmap : Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map
        (Φ.symm : Ω →+* Ω) (CFSG.RankThree.Classical2.conjSLn X⁻¹ B)) =
        CFSG.RankThree.Classical2.conjSLn X⁻¹ B := by
      apply Subtype.ext
      ext i j
      change Fr (Φ.symm _) = _
      exact Φ.apply_symm_apply _
    rw [hmap, CFSG.RankThree.Classical2.coe_conjSLn, CFSG.RankThree.Classical2.coe_conjSLn,
      inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul,
      Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  let Zc : Subgroup (ModGL Tag.E6 Ω) := K ⊓ Subgroup.centralizer (K : Set (ModGL Tag.E6 Ω))
  have hZcent : ∀ z ∈ Zc, ∀ v ∈ K, z * v = v * z := fun z hz v hv =>
    (Subgroup.mem_centralizer_iff.1 hz.2 v hv).symm
  have _hFZ : ∀ z ∈ Zc, twistHom TwistTag.E6 Ω Fr z ∈ Zc := by
    intro z hz
    let F' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω := twistHom TwistTag.E6 Ω Fr
    have hFzK : F' z ∈ K := twistHom_mem_hypCentConn hk Fr hFr hHF hz.1
    show F' z ∈ Zc
    refine ⟨hFzK, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
    obtain ⟨w, hwK, hwc, -, B, rfl⟩ := hdec v hv
    obtain ⟨B', rfl⟩ := hτsurj B
    have k1 : F' z * ιa (τ B') = ιa (τ B') * F' z := by
      have h : ιa (τ B') = F' (ιa B') := hιτ B'
      rw [h, ← map_mul, ← map_mul, hZcent z hz _ (hιaK B')]
    have k2 : w * F' z = F' z * w := hwc _ hFzK
    calc w * ιa (τ B') * F' z = w * (F' z * ιa (τ B')) := by rw [mul_assoc, ← k1]
      _ = F' z * (w * ιa (τ B')) := by rw [← mul_assoc, k2, mul_assoc]
  have hZodd : ∀ z ∈ Zc, ∃ m, Odd m ∧ z ^ m = 1 := by
    intro z hz
    obtain ⟨w, hwK, hwc, hwT, B, rfl⟩ := hdec z hz.1
    have hBc : ∀ A, ιa B * ιa A = ιa A * ιa B := by
      intro A
      have h1 := hZcent _ hz (ιa A) (hιaK A)
      have h2 := hwc (ιa A) (hιaK A)
      have h3 : w * (ιa B * ιa A) = w * (ιa A * ιa B) := by
        calc w * (ιa B * ιa A) = w * ιa B * ιa A := (mul_assoc _ _ _).symm
          _ = ιa A * (w * ιa B) := h1
          _ = w * (ιa A * ιa B) := by rw [← mul_assoc, ← h2, mul_assoc]
      exact mul_left_cancel h3
    have hBcent : B ∈ Subgroup.center (SL(2, Ω)) := Subgroup.mem_center_iff.2 fun A =>
      hιainj (by rw [map_mul, map_mul]; exact (hBc A).symm)
    have hB1 : B = 1 := by
      obtain ⟨r, hr, hrB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hBcent
      have hr2 : r ^ 2 = 1 := by simpa [Fintype.card_fin] using hr
      have htwo : (2 : Ω) = 0 := CharTwo.two_eq_zero
      have hsq : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * htwo
      have hr1 : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
      apply Subtype.ext
      rw [← hrB, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
    subst hB1
    rw [map_one, mul_one]
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hwT
    obtain ⟨N, hNodd, hlN⟩ :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141e.exists_odd_pow_eq_one
        (K := k) (ringChar.eq k 2) l
    refine ⟨N, hNodd, ?_⟩
    have hl1 : l ^ N = 1 := funext hlN
    have hw1 : (y₀ * w * y₀⁻¹) ^ N = 1 := by
      rw [hl, ← CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_pow', hl1,
        CFSG.LieType.Chevalley.rootDiagUnit_one]
    rw [conj_pow, conj_eq_one_iff] at hw1
    exact hw1
  have hKdec : ∀ v ∈ K, ∃ z ∈ Zc, ∃ B : SL(2, Ω), v = z * ιa B := by
    intro v hv
    obtain ⟨w, hwK, hwc, -, B, hB⟩ := hdec v hv
    exact ⟨w, ⟨hwK, Subgroup.mem_centralizer_iff.2 fun u hu => (hwc u hu).symm⟩, B, hB⟩
  exact isQuasisimple_jgeom_of_isogeny_split Fr Hh hn hk hFr hHF le_rfl ιa hιaK
    (by rw [(MonoidHom.ker_eq_bot_iff ιa).mpr hιainj]; exact bot_le) X hσ hZcent hZodd
    hKdec heK heF he1 he3 hgK hgF hg2 hinv


open CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.Torality in
theorem isQuasisimple_jgeom_of_rootTriple {Fr : Ω →+* Ω} {Hh : Subgroup (ModGL Tag.E6 Ω)}
    [Finite ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)]
    {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k] [Finite k] [Algebra k Ω] [IsAlgClosure k Ω]
    (hk : Nat.card k = (2 ^ n) ^ 2) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    {y₀ : ModGL Tag.E6 Ω} (hy₀ : y₀ ∈ adjointGroup Tag.E6 Ω)
    (β : Fin 3 → Fin Tag.E6.rank → ℤ) (hβ : ∀ i, IsRoot .E6 (β i))
    (horth : ∀ i j, i ≠ j → iform (β i) (β j) = 0) {ℓ₁ : Label Tag.E6}
    (hℓ₁ : ∑ i, labelWt Tag.E6 ℓ₁ i * ∑ j, corootPair (β j) (Pi.single i 1) = 1)
    {x : ModGL Tag.E6 Ω} {s₁ t₂ t₃ : Ωˣ}
    (h₀ : ∀ A, x * rootSL2 .E6 Ω (β 0) A * x⁻¹ = rootSL2 .E6 Ω (β 1)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₁) A))
    (h₁ : ∀ A, x * rootSL2 .E6 Ω (β 1) A * x⁻¹ = rootSL2 .E6 Ω (β 2)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne t₂) A))
    (h₂ : ∀ A, x * rootSL2 .E6 Ω (β 2) A * x⁻¹ = rootSL2 .E6 Ω (β 0)
      (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne t₃) A))
    (hx3 : x ^ 3 = 1) (hxT : ∀ t ∈ torusGroup Tag.E6 Ω, x * t * x⁻¹ ∈ torusGroup Tag.E6 Ω)
    {ι₀ : Type} (a : ι₀ → Fin Tag.E6.rank → Ωˣ)
    (hker : familyKernel a = threeRootSet (β 0) (β 1) (β 2))
    (hHgen : Hh.map (MulAut.conj y₀).toMonoidHom =
      Subgroup.closure (Set.range (fun i => rootDiagUnit Tag.E6 (a i)) ∪ {x}))
    {e g : ModGL Tag.E6 Ω}
    (heK : e ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (heF : e ∈ TwistedDiag.Rgrp Ω Fr) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {t : ℕ} (hg2 : g ^ (2 ^ t) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) (heT : y₀ * e * y₀⁻¹ ∈ torusGroup Tag.E6 Ω) :
    CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap k Ω).injective 2
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  set H' := Hh.map (MulAut.conj y₀).toMonoidHom with hH'
  set K' := closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
    Subgroup.centralizer (H' : Set (ModGL Tag.E6 Ω))) with hK'def
  set ι := rootTripleHom β hβ horth s₁ (s₁ * t₂) with hιdef
  have ha : ∀ i, rootDiagUnit Tag.E6 (a i) ∈ H' := fun i => by
    rw [hHgen]
    exact Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  have hxH : x ∈ H' := by
    rw [hHgen]
    exact Subgroup.subset_closure (Or.inr rfl)
  have hachar : ∀ i j, rootChar (a i) (β j) = 1 := by
    intro i j
    have hj : β j ∈ familyKernel a := by
      rw [hker]
      fin_cases j <;> simp [threeRootSet]
    exact hj.2 i
  have hHι : ∀ h ∈ H', ∀ A, h * ι A = ι A * h := by
    intro h hh A
    rw [hHgen] at hh
    induction hh using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with ⟨i, rfl⟩ | hy
      · exact rootDiagUnit_commute_rootTripleHom β hβ horth s₁ (s₁ * t₂) (a i)
          (hachar i) A
      · rw [Set.mem_singleton_iff.1 hy]
        exact commute_rootTripleHom_of_cycle β hβ horth h₀ h₁ h₂ hx3 A
    | one => rw [one_mul, mul_one]
    | mul y z _ _ hy hz => rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]
    | inv y _ hy => exact (Commute.inv_left (hy : Commute y (ι A))).eq
  have hιK' : ∀ A, ι A ∈ K' := fun A =>
    rootTripleHom_mem_closedIdentityComponent β hβ horth s₁ (s₁ * t₂)
      (fun h hh t => ⟨hHι h hh _, hHι h hh _⟩) A
  set m : Fin Tag.E6.rank → ℤ := fun i => ∑ j, corootPair (β j) (Pi.single i 1) with hm
  have hγ : ∀ u : Ωˣ, ι (HSL u) = rootDiagUnit Tag.E6 (fun i => u ^ m i) := by
    intro u
    rw [hιdef, rootTripleHom_apply, conjSL_diagUnitOne_HSL, conjSL_diagUnitOne_HSL,
      rootSL2_HSL_eq (hβ 0), rootSL2_HSL_eq (hβ 1), rootSL2_HSL_eq (hβ 2),
      ← CFSG.LieType.Chevalley.rootDiagUnit_mul, ← CFSG.LieType.Chevalley.rootDiagUnit_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply, hm, Fin.sum_univ_three, zpow_add]
  have hιinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro A hA
    rw [MonoidHom.mem_ker] at hA
    have hT : rootSL2 .E6 Ω (β 0) A * rootSL2 .E6 Ω (β 1)
        (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₁) A) *
        rootSL2 .E6 Ω (β 2)
          (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne (s₁ * t₂)) A) ∈
        torusGroup Tag.E6 Ω := by
      rw [← rootTripleHom_apply β hβ horth s₁ (s₁ * t₂), ← hιdef, hA]
      exact Subgroup.one_mem _
    have hD := diag_of_rootTriple_mem_torusGroup β hβ horth
      ![A, CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s₁) A,
        CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne (s₁ * t₂)) A] hT 0
    obtain ⟨u, rfl⟩ := eq_HSL_of_diag hD.1 hD.2
    rw [hγ] at hA
    have h1 := congrArg (fun X : ModGL Tag.E6 Ω =>
      (X : Module.End Ω (RootModule Tag.E6 Ω)) (Finsupp.single ℓ₁ 1) ℓ₁) hA
    change rootDiag (fun i => u ^ m i) (Finsupp.single ℓ₁ 1) ℓ₁ = _ at h1
    rw [rootDiag_single, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
      Units.val_one, Module.End.one_apply, Finsupp.single_eq_same] at h1
    have h2 : rootChar (fun i => u ^ m i) (labelWt Tag.E6 ℓ₁) = u := by
      simp only [rootChar, ← zpow_mul]
      rw [Finset.prod_zpow_eq_zpow_sum]
      simp only [mul_comm (m _)]
      rw [show ∑ i, labelWt Tag.E6 ℓ₁ i * m i = 1 from hℓ₁, zpow_one]
    rw [h2] at h1
    have hu : u = 1 := Units.ext h1
    subst hu
    apply Subtype.ext
    rw [coe_HSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hKT : ∀ z ∈ K', ∃ b : Fin Tag.E6.rank → Ωˣ, ∃ c : Ωˣ,
      (∀ A, rootDiagUnit Tag.E6 b * ι A * (rootDiagUnit Tag.E6 b)⁻¹ =
        ι (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne c) A)) ∧
      ∃ A, z = rootDiagUnit Tag.E6 b * ι A := by
    intro z hz
    obtain ⟨t', ht'T, ht'n, A, rfl⟩ := closedIdentityComponent_le_torus_mul_rootTripleHom
      (s₁ := s₁) (t₂ := t₂) (t₃ := t₃) β hβ horth h₀ h₁ h₂ hx3 hxT a hker ha hxH hz
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht'T
    exact ⟨l, rootChar l (β 0),
      fun A' => rootDiagUnit_conj_rootTripleHom_of_commute β hβ horth h₀ h₁ l ht'n A', A, rfl⟩
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup heT
  have hex : x * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * x := by
    obtain ⟨h, hh, hhx⟩ := hxH
    have hec : h * e = e * h :=
      Subgroup.mem_centralizer_iff.1 (closedIdentityComponent_le _ heK).2 h hh
    rw [← hb, ← hhx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc y₀ * h * y₀⁻¹ * (y₀ * e * y₀⁻¹) = y₀ * (h * e) * y₀⁻¹ := by group
      _ = y₀ * (e * h) * y₀⁻¹ := by rw [hec]
      _ = y₀ * e * y₀⁻¹ * (y₀ * h * y₀⁻¹) := by group
  exact isQuasisimple_jgeom_of_torusFrame hn hk hFr hHF hy₀ ι hιinj hιK' m hγ hℓ₁ hKT heK heF he1
    he3 hgK hgF hg2 hinv hb
    (fun A => rootDiagUnit_conj_rootTripleHom_of_commute β hβ horth h₀ h₁ b hex A)

open CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType.NoOffTwE6Three in
theorem isQuasisimple_jgeom_of_monomial_orbit {Fr : Ω →+* Ω} {Hh : Subgroup (ModGL Tag.E6 Ω)}
    [Finite ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)]
    {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k] [Finite k] [Algebra k Ω] [IsAlgClosure k Ω]
    (hk : Nat.card k = (2 ^ n) ^ 2) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (hHF : Hh ≤ TwistedDiag.Rgrp Ω Fr)
    {y₀ : ModGL Tag.E6 Ω} (hy₀ : y₀ ∈ adjointGroup Tag.E6 Ω)
    {x : ModGL Tag.E6 Ω} (hxM : x ∈ monomialSubgroup Tag.E6 Ω) (hx3 : x ^ 3 = 1)
    {ζ : Ωˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) {H : Set (Fin Tag.E6.rank → ZMod 3)}
    (hHgen : Hh.map (MulAut.conj y₀).toMonoidHom = Subgroup.closure
      ((fun v => rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v)) '' H ∪ {x}))
    {β₀ : Fin Tag.E6.rank → ℤ} (hβ₀ : IsRoot .E6 β₀)
    (horth : ∀ i j : Fin 3, i ≠ j →
      iform (![β₀, weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ • β₀,
        weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ • weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ • β₀] i)
      (![β₀, weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ • β₀,
        weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ • weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ • β₀] j) = 0)
    (hker : ∀ α, (IsRoot .E6 α ∧ ∀ v ∈ H, pairFormE6 α v = 0) ↔
      α ∈ threeRootSet β₀ (weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ • β₀)
        (weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ • weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ • β₀))
    {ℓ₁ : Label Tag.E6}
    (hℓ₁ : ∑ i, labelWt Tag.E6 ℓ₁ i * ∑ j, corootPair (![β₀,
      weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ • β₀,
      weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ • weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ • β₀] j)
        (Pi.single i 1) = 1)
    {e g : ModGL Tag.E6 Ω}
    (heK : e ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (heF : e ∈ TwistedDiag.Rgrp Ω Fr) (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (hgK : g ∈ closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))))
    (hgF : g ∈ TwistedDiag.Rgrp Ω Fr) {t : ℕ} (hg2 : g ^ (2 ^ t) = 1)
    (hinv : g * e * g⁻¹ = e⁻¹) (heT : y₀ * e * y₀⁻¹ ∈ torusGroup Tag.E6 Ω) :
    CFSG.IsQuasisimple ((primeResidual 2 ↥(closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
      Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr)).map
        (closedIdentityComponent (adjointGroup Tag.E6 Ω ⊓
          Subgroup.centralizer (Hh : Set (ModGL Tag.E6 Ω))) ⊓ TwistedDiag.Rgrp Ω Fr).subtype) := by
  set w := weylQuotientHom Tag.E6 Ω ⟨x, hxM⟩ with hw
  set β : Fin 3 → Fin Tag.E6.rank → ℤ := ![β₀, w • β₀, w • w • β₀] with hβdef
  have hβ : ∀ i, IsRoot .E6 (β i) := by
    intro i
    fin_cases i
    · exact hβ₀
    · exact IsRoot.smul hβ₀ w
    · exact IsRoot.smul (IsRoot.smul hβ₀ w) w
  have hw3 : w • w • w • β₀ = β₀ := by
    have h : w ^ 3 = 1 := by
      rw [hw, ← map_pow]
      have : (⟨x, hxM⟩ : monomialSubgroup Tag.E6 Ω) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    rw [← mul_smul, ← mul_smul, show w * w * w = w ^ 3 by rw [pow_three, ← mul_assoc], h,
      one_smul]
  have hmaps := mapsRootLines_weylQuotientHom (R := Ω) ⟨x, hxM⟩
  obtain ⟨s₁, h₀⟩ := CFSG.RankThree.Chevalley.exists_conj_rootSL2_eq hxM hmaps (hβ 0)
    (show w • β 0 = β 1 from rfl)
  obtain ⟨t₂, h₁⟩ := CFSG.RankThree.Chevalley.exists_conj_rootSL2_eq hxM hmaps (hβ 1)
    (show w • β 1 = β 2 from rfl)
  obtain ⟨t₃, h₂⟩ := CFSG.RankThree.Chevalley.exists_conj_rootSL2_eq hxM hmaps (hβ 2)
    (show w • β 2 = β 0 from hw3)
  have hxT : ∀ t ∈ torusGroup Tag.E6 Ω, x * t * x⁻¹ ∈ torusGroup Tag.E6 Ω := fun t ht =>
    (Subgroup.mem_normalizer_iff.1 (mem_normalizer_torusGroup_of_mem_monomialSubgroup hxM) t).1 ht
  let a : H → Fin Tag.E6.rank → Ωˣ := fun v => TableBExc.E6Three.zetaVec ζ hζ (v : Fin Tag.E6.rank → ZMod 3)
  have hz : ∀ v α, rootChar (TableBExc.E6Three.zetaVec ζ hζ v) α = 1 ↔ pairFormE6 α v = 0 := by
    intro v α
    rw [NoOffE8Five.rootChar_zetaVec]
    constructor
    · intro h
      have h1 : Multiplicative.ofAdd (∑ j, ((α j : ℤ) : ZMod 3) * v j) = 1 :=
        (CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ) (by rw [h, map_one])
      simpa [pairFormE6] using congrArg Multiplicative.toAdd h1
    · intro h
      rw [show (∑ j, ((α j : ℤ) : ZMod 3) * v j) = 0 by simpa [pairFormE6] using h, ofAdd_zero,
        map_one]
  have hkerA : familyKernel a = threeRootSet (β 0) (β 1) (β 2) := by
    ext α
    show α ∈ familyKernel a ↔ α ∈ threeRootSet β₀ (w • β₀) (w • w • β₀)
    rw [← hker α]
    simp only [familyKernel, Set.mem_setOf_eq]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h v hv
      exact (hz v α).1 (h ⟨v, hv⟩)
    · intro h v
      exact (hz v α).2 (h v v.2)
  have hgen : Hh.map (MulAut.conj y₀).toMonoidHom =
      Subgroup.closure (Set.range (fun i => rootDiagUnit Tag.E6 (a i)) ∪ {x}) := by
    rw [hHgen]
    congr 2
    ext y
    simp only [Set.mem_image, Set.mem_range, Subtype.exists, a]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
  exact isQuasisimple_jgeom_of_rootTriple hn hk hFr hHF hy₀ β hβ horth hℓ₁ h₀ h₁ h₂ hx3 hxT a hkerA
    hgen heK heF he1 he3 hgK hgF hg2 hinv heT

end RootTripleFrobenius

section OriginalMonomialOrbit

open SCFourCover NoOffTwE6Three CFSG.Assembly CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
  (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
  (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
    MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
variable {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}
  (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
  {A : Subgroup (MulAut L')}
  (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l, φ (ψ l) = ψ (a l))

end OriginalMonomialOrbit

end CFSG.StandardType.TwE6FixedComponent

end
