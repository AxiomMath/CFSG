module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingInvolutionDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseReflectionPSL2FixedSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FixedFactorCentralizesSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearComponentSylowNormalizesK
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The aligned-Sylow decomposition in the PSL₂ branch

The paper re-chooses the ambient Sylow after fixing `M`. This module makes
that choice explicit: a Sylow subgroup `SM` of `M` is assumed to lie in the
fixed ambient Sylow `S`, and a Sylow subgroup `SE` of the component is
identified with `SM ∩ E`. Sylow maximality gives `SM = S ∩ M`, so the
prescribed-Sylow PSL₂ reflector lies in `S \ S0` without assuming `S ≤ E`.
The equations-(1)--(3) decomposition is then derived from that reflector.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u v

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ## Quotient and transport infrastructure -/

/-- The quotient image of an involution is an involution when the kernel has
odd order. -/
private theorem quotient_involution_of_involution
    {Q : Type u} [Group Q] [Finite Q]
    (N : Subgroup Q) [N.Normal] (hNodd : Odd (Nat.card N))
    {x : Q} (hx : IsInvolution x) :
    IsInvolution (QuotientGroup.mk' N x) := by
  constructor
  · intro hqx
    have hxN : x ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) x).mp hqx
    let xN : N := ⟨x, hxN⟩
    have hxNI : IsInvolution xN := by
      constructor
      · intro hone
        exact hx.1 (congrArg Subtype.val hone)
      · exact Subtype.ext hx.2
    have hxNOrder : orderOf xN = 2 :=
      orderOf_eq_prime hxNI.2 hxNI.1
    have htwo : 2 ∣ Nat.card N := by
      rw [← hxNOrder]
      exact orderOf_dvd_natCard xN
    exact hNodd.not_two_dvd_nat htwo
  · simpa using congrArg (QuotientGroup.mk' N) hx.2

/-- A subgroup centralizing `t` maps into the centralizer of its image under
an equivalence. -/
private theorem centralizer_map_le
    {Q : Type u} {S : Type v} [Group Q] [Group S]
    (e : Q ≃* S) {P : Subgroup Q} {t : Q}
    (hP : P ≤ Subgroup.centralizer ({t} : Set Q)) :
    P.map e.toMonoidHom ≤ Subgroup.centralizer ({e t} : Set S) := by
  intro y hy
  rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
  have hxcent : x ∈ Subgroup.centralizer ({t} : Set Q) := hP hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcomm : x * t = t * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hxcent
  calc
    (e.toMonoidHom x) * (e.toMonoidHom t) = e.toMonoidHom (x * t) := by
      rw [map_mul]
    _ = e.toMonoidHom (t * x) := by rw [hcomm]
    _ = (e.toMonoidHom t) * (e.toMonoidHom x) := by
      rw [map_mul]

/-- An involutive element of a quotient, lying in the image of a Sylow
`2`-subgroup, lifts to an involution in that Sylow subgroup when the quotient
kernel has odd order. -/
private theorem lift_involution_in_sylow_of_quotient
    {E : Type u} [Group E] [Finite E]
    (Z : Subgroup E) [Z.Normal] (hZodd : Odd (Nat.card Z))
    (P : Sylow 2 E) {sbar : E ⧸ Z}
    (hsbarP : sbar ∈
      (P.mapSurjective (QuotientGroup.mk'_surjective Z) : Subgroup (E ⧸ Z)))
    (hsbarI : IsInvolution sbar) :
    ∃ s : E, s ∈ (P : Subgroup E) ∧ QuotientGroup.mk' Z s = sbar ∧
      IsInvolution s := by
  classical
  let q : E →* E ⧸ Z := QuotientGroup.mk' Z
  rw [Sylow.coe_mapSurjective] at hsbarP
  rcases Subgroup.mem_map.mp hsbarP with ⟨s, hsP, hsq⟩
  have hs2Z : s ^ 2 ∈ Z := by
    apply (QuotientGroup.eq_one_iff (N := Z) (s ^ 2)).mp
    calc
      q (s ^ 2) = (q s) ^ 2 := by
        exact map_pow q s 2
      _ = sbar ^ 2 := by rw [hsq]
      _ = 1 := hsbarI.2
  have hs2odd : Odd (orderOf (s ^ 2)) := by
    exact Odd.of_dvd_nat hZodd (Subgroup.orderOf_dvd_natCard Z hs2Z)
  let sP : P := ⟨s, hsP⟩
  have hordP : ∃ k : ℕ, orderOf sP = 2 ^ k :=
    (IsPGroup.iff_orderOf.mp P.isPGroup') sP
  rcases hordP with ⟨k, hk⟩
  have hs2pow : orderOf (s ^ 2) ∣ 2 ^ k := by
    have hordSE : orderOf (s : E) = orderOf sP :=
      orderOf_injective (P : Subgroup E).subtype
        (P : Subgroup E).subtype_injective sP
    have hordS2 : orderOf (s ^ 2) = orderOf (sP ^ 2) :=
      orderOf_injective (P : Subgroup E).subtype
        (P : Subgroup E).subtype_injective (sP ^ 2)
    calc
      orderOf (s ^ 2) ∣ orderOf (s : E) := by
        rw [hordS2, hordSE]
        exact orderOf_pow_dvd (n := 2) (x := sP)
      _ = orderOf sP := hordSE
      _ = 2 ^ k := hk
  have hs2one : s ^ 2 = 1 := by
    have hord1 : orderOf (s ^ 2) = 1 := by
      rcases (Nat.dvd_prime_pow Nat.prime_two).mp hs2pow with ⟨n, _hn, hxeq⟩
      have hn0 : n = 0 := by
        by_contra hn0
        have h2dvd : 2 ∣ orderOf (s ^ 2) := by
          rw [hxeq]
          exact ⟨2 ^ (n - 1), by
            rw [show n = (n - 1) + 1 by omega, pow_succ']
            rfl⟩
        exact hs2odd.not_two_dvd_nat h2dvd
      simpa [hn0] using hxeq
    exact orderOf_eq_one_iff.mp hord1
  have hsne : s ≠ 1 := by
    intro hs1
    apply hsbarI.1
    calc
      sbar = q s := hsq.symm
      _ = 1 := by
        rw [hs1]
        simp [q]
  exact ⟨s, hsP, hsq, hsne, hs2one⟩

/-- Transport an endpoint reflected-torus package (carrying the image of
`t` in its torus) through an equivalence of the quotient models. -/
private theorem quotient_fixedSylow_transport_t
    {Q : Type u} {S : Type v} [Group Q] [Finite Q] [Group S] [Finite S]
    (e : Q ≃* S)
    (P : Sylow 2 Q) (t : Q)
    (hendpoint :
      ∃ T : Subgroup S, ∃ s : S,
        IsCyclic T ∧ e t ∈ T ∧
          s ∈ ((P.mapSurjective (f := e.toMonoidHom) e.surjective) :
            Subgroup S) ∧
          s ∉ T ∧ IsInvolution s ∧
            (P.mapSurjective (f := e.toMonoidHom) e.surjective :
              Subgroup S) ≤ T ⊔ Subgroup.zpowers s ∧
            Subgroup.normalizer (Subgroup.zpowers (e t) : Set S) =
              T ⊔ Subgroup.zpowers s ∧
            (∀ x : S, x ∈ T → s * x * s⁻¹ = x⁻¹) ∧
              ∀ X : Subgroup S,
                (∀ x : S, x ∈ X → Odd (orderOf x)) →
                  X ≤ Subgroup.centralizer ({e t} : Set S) → X ≤ T) :
    ∃ T : Subgroup Q, ∃ s : Q,
      IsCyclic T ∧ t ∈ T ∧ s ∈ (P : Subgroup Q) ∧ s ∉ T ∧ IsInvolution s ∧
        (P : Subgroup Q) ≤ T ⊔ Subgroup.zpowers s ∧
        Subgroup.normalizer (Subgroup.zpowers t : Set Q) =
          T ⊔ Subgroup.zpowers s ∧
        (∀ x : Q, x ∈ T → s * x * s⁻¹ = x⁻¹) ∧
          ∀ X : Subgroup Q,
            (∀ x : Q, x ∈ X → Odd (orderOf x)) →
              X ≤ Subgroup.centralizer ({t} : Set Q) → X ≤ T := by
  classical
  rcases hendpoint with ⟨TS, sS, hTcycS, heT, hsSP, hsSnotT, hsSI,
    hPdecompS, hnormalizerS, hinvS, hcontainS⟩
  let T : Subgroup Q := TS.map e.symm.toMonoidHom
  let s : Q := e.symm sS
  have hTcyc : IsCyclic T := by
    let eT : TS ≃* T :=
      Subgroup.equivMapOfInjective TS e.symm.toMonoidHom e.symm.injective
    exact (MulEquiv.isCyclic eT).mp hTcycS
  have htT : t ∈ T := by
    exact Subgroup.mem_map.mpr ⟨e t, heT, e.symm_apply_apply t⟩
  have hsP : s ∈ (P : Subgroup Q) := by
    change sS ∈ (P.map e.toMonoidHom : Subgroup S) at hsSP
    rcases Subgroup.mem_map.mp hsSP with ⟨p, hpP, hpeq⟩
    have hp_eq : p = s := by
      apply e.injective
      calc
        e p = sS := hpeq
        _ = e (e.symm sS) := by simp
    simpa [s, hp_eq] using hpP
  have hs_not_T : s ∉ T := by
    intro hsT
    rcases Subgroup.mem_map.mp hsT with ⟨y, hyTS, hyeq⟩
    have hy_eq : y = sS := by
      apply e.symm.injective
      calc
        e.symm y = s := hyeq
        _ = e.symm sS := rfl
    exact hsSnotT (by simpa [hy_eq] using hyTS)
  have hsI : IsInvolution s := by
    constructor
    · intro hs1
      apply hsSI.1
      have h : e.symm sS = 1 := by simpa [s] using hs1
      have hsS1 : sS = 1 := by
        have h' := congrArg e h
        simpa using h'
      exact hsS1
    · calc
        s ^ 2 = e.symm.toMonoidHom (sS ^ 2) := by
          simp [s, map_pow]
        _ = 1 := by
          rw [hsSI.2]
          simp
  have hjoin_map : (TS ⊔ Subgroup.zpowers sS).map e.symm.toMonoidHom =
      T ⊔ Subgroup.zpowers s := by
    dsimp [T, s]
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  have hPdecomp : (P : Subgroup Q) ≤ T ⊔ Subgroup.zpowers s := by
    intro x hx
    have hxS_P : e.toMonoidHom x ∈
        (P.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup S) := by
      change e.toMonoidHom x ∈ (P.map e.toMonoidHom : Subgroup S)
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hxS : e.toMonoidHom x ∈ TS ⊔ Subgroup.zpowers sS :=
      hPdecompS hxS_P
    have hxmap : e.symm.toMonoidHom (e.toMonoidHom x) ∈
        (TS ⊔ Subgroup.zpowers sS).map e.symm.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨e.toMonoidHom x, hxS, rfl⟩
    rw [hjoin_map] at hxmap
    simpa using hxmap
  have hZt_map :
      (Subgroup.zpowers (e t)).map e.symm.toMonoidHom =
        Subgroup.zpowers t := by
    rw [MonoidHom.map_zpowers]
    simp
  have hnormalizer_map :
      (Subgroup.normalizer (Subgroup.zpowers (e t) : Set S)).map
          e.symm.toMonoidHom =
        Subgroup.normalizer (Subgroup.zpowers t : Set Q) := by
    calc
      (Subgroup.normalizer (Subgroup.zpowers (e t) : Set S)).map
          e.symm.toMonoidHom =
          Subgroup.normalizer
            ((Subgroup.zpowers (e t)).map e.symm.toMonoidHom : Set Q) :=
        Subgroup.map_equiv_normalizer_eq (Subgroup.zpowers (e t)) e.symm
      _ = Subgroup.normalizer (Subgroup.zpowers t : Set Q) := by
        rw [hZt_map]
  have hnormalizer :
      Subgroup.normalizer (Subgroup.zpowers t : Set Q) =
        T ⊔ Subgroup.zpowers s := by
    calc
      Subgroup.normalizer (Subgroup.zpowers t : Set Q) =
          (Subgroup.normalizer (Subgroup.zpowers (e t) : Set S)).map
            e.symm.toMonoidHom := hnormalizer_map.symm
      _ = (TS ⊔ Subgroup.zpowers sS).map e.symm.toMonoidHom := by
        rw [hnormalizerS]
      _ = T ⊔ Subgroup.zpowers s := hjoin_map
  have hinvT : ∀ x : Q, x ∈ T → s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyTS, hx_eq⟩
    calc
      s * x * s⁻¹ = e.symm.toMonoidHom (sS * y * sS⁻¹) := by
        rw [← hx_eq]
        dsimp [s]
        rw [e.symm.map_mul, e.symm.map_mul, e.symm.map_inv]
      _ = e.symm.toMonoidHom (y⁻¹) := by rw [hinvS y hyTS]
      _ = (e.symm.toMonoidHom y)⁻¹ := by
        rw [e.symm.toMonoidHom.map_inv]
      _ = x⁻¹ := by rw [hx_eq]
  have hcontain : ∀ X : Subgroup Q,
      (∀ x : Q, x ∈ X → Odd (orderOf x)) →
        X ≤ Subgroup.centralizer ({t} : Set Q) → X ≤ T := by
    intro X hXodd hXcent x hx
    let XS : Subgroup S := X.map e.toMonoidHom
    have hXSodd : ∀ y : S, y ∈ XS → Odd (orderOf y) := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨x0, hx0, rfl⟩
      have hord : orderOf (e.toMonoidHom x0) = orderOf x0 :=
        (e.orderOf_eq x0)
      rw [hord]
      exact hXodd x0 hx0
    have hXScent : XS ≤ Subgroup.centralizer ({e t} : Set S) := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨x0, hx0, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : x0 * t = t * x0 :=
        Subgroup.mem_centralizer_singleton_iff.mp (hXcent hx0)
      calc
        (e.toMonoidHom x0) * (e.toMonoidHom t) =
            e.toMonoidHom (x0 * t) := by rw [map_mul]
        _ = e.toMonoidHom (t * x0) := by rw [hcomm]
        _ = (e.toMonoidHom t) * (e.toMonoidHom x0) := by rw [map_mul]
    have hXST : XS ≤ TS := hcontainS XS hXSodd hXScent
    have hxS : e.toMonoidHom x ∈ XS :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hxT : e.toMonoidHom x ∈ TS := hXST hxS
    exact Subgroup.mem_map.mpr ⟨e.toMonoidHom x, hxT, e.symm_apply_apply x⟩
  exact ⟨T, s, hTcyc, htT, hsP, hs_not_T, hsI, hPdecomp,
    hnormalizer, hinvT, hcontain⟩

/-! ## Odd-order and inverted-element infrastructure -/

/-- Every element of the odd core `U = O(H)` has odd order. -/
private theorem odd_order_of_mem_U
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : ∀ x : G, x ∈ c.U → Odd (orderOf x) := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, hxy⟩
  have hdvd : orderOf y ∣ Nat.card (pPrimeCore 2 c.H) :=
    Subgroup.orderOf_dvd_natCard (pPrimeCore 2 c.H) hy
  have hoddcard : Odd (Nat.card (pPrimeCore 2 c.H)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := c.H))
  have hoddY : Odd (orderOf y) := Odd.of_dvd_nat hoddcard hdvd
  have hordEq : orderOf (c.H.subtype y) = orderOf y :=
    orderOf_injective c.H.subtype c.H.subtype_injective y
  rw [← hxy, hordEq]
  exact hoddY

/-- The image of an element of odd order under a homomorphism has odd
order. -/
private theorem odd_order_of_map_of_odd_order {A : Type u} {B : Type v}
    [Group A] [Group B] (f : A →* B) {x : A} (hx : Odd (orderOf x)) :
    Odd (orderOf (f x)) :=
  Odd.of_dvd_nat hx (orderOf_map_dvd f x)

/-- An element of `U ∩ M` inverted by `s` lies in the component `E`: modulo
`E`, conjugation by `s` is trivial while inversion gives an element of order
two, and oddness of `U` forces that quotient image to be trivial. -/
private theorem mem_E_of_inverted
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (SM : Sylow 2 (↥w.M))
    (hSMcent : ((SM : Subgroup w.M).map w.M.subtype) ≤
      Subgroup.centralizer ({c.t} : Set G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E)
    {s : d.E} (hsSE : s ∈ (SE : Subgroup d.E))
    {y : G} (hyU : y ∈ c.U) (hyM : y ∈ w.M)
    (hyinv : (s : G) * y * (s : G)⁻¹ = y⁻¹) :
    y ∈ d.E := by
  classical
  let sG : G := s
  have hsmap : sG ∈ (SE : Subgroup d.E).map d.E.subtype :=
    Subgroup.mem_map.mpr ⟨s, hsSE, rfl⟩
  have hsSM : sG ∈ ((SM : Subgroup w.M).map w.M.subtype) := by
    rw [hSEamb] at hsmap
    exact hsmap.1
  have hsM : sG ∈ w.M := (Subgroup.map_subtype_le (SM : Subgroup w.M)) hsSM
  have hsH : sG ∈ c.H := by
    rw [c.H_eq_centralizer]
    exact hSMcent hsSM
  let Esub : Subgroup (↥w.M) := d.E.subgroupOf w.M
  have hEsubNormal : Esub.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := w.M) (N := d.E)
      (le_normalizer_of_isNormalIn d.E_normal)
  let : Esub.Normal := hEsubNormal
  let p : w.M →* w.M ⧸ Esub := QuotientGroup.mk' Esub
  let yM : w.M := ⟨y, hyM⟩
  let sM : w.M := ⟨sG, hsM⟩
  have hconjM : sM * yM * sM⁻¹ = yM⁻¹ := by
    apply Subtype.ext
    change sG * y * sG⁻¹ = y⁻¹
    exact hyinv
  have hsq : (p yM) ^ 2 = 1 := by
    have hp1 : p (sM * yM * sM⁻¹) = p yM := by
      calc
        p (sM * yM * sM⁻¹) = p sM * p yM * (p sM)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        _ = 1 * p yM * 1 := by
          have hs1 : p sM = 1 := by
            apply (QuotientGroup.eq_one_iff (N := Esub) sM).mpr
            exact Subgroup.mem_subgroupOf.mpr (s : d.E).2
          rw [hs1, one_mul, inv_one, mul_one]
        _ = p yM := by simp
    have hp2 : p (sM * yM * sM⁻¹) = (p yM)⁻¹ := by
      simpa using congrArg p hconjM
    have h : p yM = (p yM)⁻¹ := hp1.symm.trans hp2
    rw [pow_two]
    calc
      p yM * p yM = (p yM)⁻¹ * p yM := congrArg (fun z => z * p yM) h
      _ = 1 := by simp
  have hordY : Odd (orderOf y) := odd_order_of_mem_U c y hyU
  have hordYdiv : orderOf (p yM) ∣ orderOf y := by
    have h1 : orderOf (p yM) ∣ orderOf yM := orderOf_map_dvd p yM
    have h2 : orderOf yM = orderOf y :=
      (orderOf_injective w.M.subtype w.M.subtype_injective yM).symm
    rwa [h2] at h1
  have hordOdd : Odd (orderOf (p yM)) := Odd.of_dvd_nat hordY hordYdiv
  have hp1' : p yM = 1 := by
    have hdvd2 : orderOf (p yM) ∣ 2 :=
      (orderOf_dvd_iff_pow_eq_one (x := p yM) (n := 2)).2 hsq
    have hcop : Nat.Coprime 2 (orderOf y) := Nat.coprime_two_left.mpr hordY
    have hdvd1 : orderOf (p yM) ∣ 1 := by
      simpa [hcop.gcd_eq_one] using (Nat.dvd_gcd hdvd2 hordYdiv)
    exact (orderOf_eq_one_iff (x := p yM)).1 (Nat.dvd_one.mp hdvd1)
  have hyEsub : yM ∈ Esub :=
    (QuotientGroup.eq_one_iff (N := Esub) yM).mp hp1'
  exact (Subgroup.mem_subgroupOf.mp hyEsub)

/-- Powers of an element inverted by `s` are inverted by `s`. -/
private theorem zpow_inverted_of_generator_inverted
    {G : Type u} [Group G] {s z : G} (h : s * z * s⁻¹ = z⁻¹) (k : ℤ) :
    s * z ^ k * s⁻¹ = (z ^ k)⁻¹ := by
  calc
    s * z ^ k * s⁻¹ = (MulAut.conj s) (z ^ k) := (MulAut.conj_apply s (z ^ k)).symm
    _ = ((MulAut.conj s) z) ^ k := by rw [map_zpow]
    _ = (z⁻¹) ^ k := by rw [MulAut.conj_apply, h]
    _ = (z ^ k)⁻¹ := by
      rw [← zpow_neg]
      simp

/-- Membership in `centralizerIn X s`, unfolded as membership in `X` plus
fixing `s` by conjugation. -/
private theorem mem_centralizerIn_local {G : Type u} [Group G]
    (X : Subgroup G) (s x : G) :
    x ∈ centralizerIn X s ↔ x ∈ X ∧ s * x * s⁻¹ = x := by
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hcomm : s * x = x * s :=
      (Subgroup.mem_centralizer_iff.mp hx.2) s (by simp)
    rw [hcomm]
    group
  · rintro ⟨hxX, hxfix⟩
    refine ⟨hxX, ?_⟩
    change x ∈ Subgroup.centralizer ({s} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzs : z = s := by simpa using hz
    rw [hzs]
    exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hxfix)

/-! ## The aligned-Sylow decomposition -/

/-- With an explicitly aligned Sylow subgroup `SM ≤ S` and component Sylow
`SE = SM ∩ E`, choose the equation-(1)--(3) decomposition with a reflection
`s ∈ S \ S0`, without assuming the global containment `S ≤ E`. -/
public theorem secondCase_psl2_alignedSylow_decomposition
    {G : Type u} [Group G] [Finite G]
    (_hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (SM : Sylow 2 (↥w.M))
    (hSMleS : (SM : Subgroup w.M).map w.M.subtype ≤
      (c.S : Subgroup G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb_join : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E) :
    ((SM : Subgroup w.M).map w.M.subtype) ≤
        Subgroup.centralizer ({c.t} : Set G) ∧
      (SE : Subgroup d.E).map d.E.subtype =
        ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E ∧
        ∃ T : Subgroup (d.E ⧸ Subgroup.center d.E), ∃ s : d.E,
          let q : d.E →* d.E ⧸ Subgroup.center d.E :=
            QuotientGroup.mk' (Subgroup.center d.E)
          let qt : d.E ⧸ Subgroup.center d.E := q ⟨c.t, d.t_mem_E⟩
          let UEbar : Subgroup (d.E ⧸ Subgroup.center d.E) :=
            ((c.U ⊓ d.E).subgroupOf d.E).map q
          s ∈ (SE : Subgroup d.E) ∧ IsInvolution s ∧
            IsCyclic T ∧ qt ∈ T ∧ q s ∉ T ∧
            ((SE.mapSurjective
                (QuotientGroup.mk'_surjective (Subgroup.center d.E)) :
                Subgroup (d.E ⧸ Subgroup.center d.E)) ≤
              T ⊔ Subgroup.zpowers (q s)) ∧
            Subgroup.normalizer (Subgroup.zpowers qt :
              Set (d.E ⧸ Subgroup.center d.E)) =
              T ⊔ Subgroup.zpowers (q s) ∧
            BenderGlauberman.IsInvertedBy (q s) T ∧
            (∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
              (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X →
                Odd (orderOf x)) →
                X ≤ Subgroup.centralizer
                  ({qt} : Set (d.E ⧸ Subgroup.center d.E)) →
                X ≤ T) ∧
            UEbar ≤ T ∧
            IsCyclic UEbar ∧
            BenderGlauberman.IsInvertedBy (q s) UEbar ∧
            (s : G) ∈ (c.S : Subgroup G) ∧ (s : G) ∉ c.S0 ∧
            ∃ K B : Subgroup G,
              (K : Set G) =
                invertedElements (c.U ⊓ w.M) (s : G) ∧
              IsCyclic K ∧
              B = centralizerIn (c.U ⊓ w.M) (s : G) ∧
              B ≤ Subgroup.centralizer
                (((SE : Subgroup d.E).map d.E.subtype : Subgroup G) : Set G) ∧
              K ≤ d.E ∧
              (K.subgroupOf d.E).map
                  (QuotientGroup.mk' (Subgroup.center d.E)) = UEbar ∧
              (K.subgroupOf d.E) ⊓ Subgroup.center d.E = ⊥ ∧
              ((SE : Subgroup d.E).map d.E.subtype) ≤
                Subgroup.normalizer (K : Set G) ∧
              K ⊔ B = c.U ⊓ w.M ∧
              ∃ K0 F : Subgroup G,
                K0 = fittingSubgroupOf c.U ⊓ K ∧
                F = fittingSubgroupOf c.U ⊓ B ∧
                F = centralizerIn (fittingSubgroupOf c.U ⊓ w.M) (s : G) ∧
                K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M := by
  classical
  let Kfield : Type u := K
  have hKfield : IsOddPrimePower (Nat.card Kfield) := by
    simpa [Kfield] using hK
  have efield : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 Kfield) := by
    simpa [Kfield] using e
  -- (1) identify the prescribed Sylow data with the aligned intersections
  let Iamb : Subgroup G := (c.S : Subgroup G) ⊓ w.M
  let IM : Subgroup w.M := Iamb.subgroupOf w.M
  have hIMp : IsPGroup 2 IM := by
    have hIp : IsPGroup 2 Iamb := c.S.isPGroup'.to_inf_left
    exact hIp.comap_subtype
  have hSMleIM : (SM : Subgroup w.M) ≤ IM := by
    intro x hx
    apply Subgroup.mem_subgroupOf.mpr
    exact ⟨hSMleS (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩), x.2⟩
  have hIMeq : IM = (SM : Subgroup w.M) :=
    SM.is_maximal' hIMp hSMleIM
  have hSMamb : (SM : Subgroup w.M).map w.M.subtype =
      (c.S : Subgroup G) ⊓ w.M := by
    apply le_antisymm
    · exact le_inf hSMleS (Subgroup.map_subtype_le (SM : Subgroup w.M))
    · intro x hx
      let xM : w.M := ⟨x, hx.2⟩
      have hxIM : xM ∈ IM := Subgroup.mem_subgroupOf.mpr hx
      rw [hIMeq] at hxIM
      exact Subgroup.mem_map.mpr ⟨xM, hxIM, rfl⟩
  have hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      (c.S : Subgroup G) ⊓ d.E := by
    rw [hSEamb_join, hSMamb]
    apply le_antisymm
    · exact inf_le_inf inf_le_left le_rfl
    · intro x hx
      exact ⟨⟨hx.1, d.E_component.1 hx.2⟩, hx.2⟩
  have hSMcent : ((SM : Subgroup w.M).map w.M.subtype) ≤
      Subgroup.centralizer ({c.t} : Set G) := by
    rw [← c.H_eq_centralizer]
    exact hSMleS.trans (centralizerSetup_S_le_H c)
  -- (2) the quotient model and the prescribed Sylow subgroup
  let Q : Type u := d.E ⧸ Subgroup.center d.E
  let q : d.E →* Q := QuotientGroup.mk' (Subgroup.center d.E)
  let P : Sylow 2 Q :=
    SE.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center d.E))
  let tQ : Q := q ⟨c.t, d.t_mem_E⟩
  have hSEamb_le : (SE : Subgroup d.E).map d.E.subtype ≤
      Subgroup.centralizer ({c.t} : Set G) := by
    rw [hSEamb_join]
    exact le_trans inf_le_left hSMcent
  have htQ : IsInvolution tQ := by
    have htE : IsInvolution (⟨c.t, d.t_mem_E⟩ : d.E) := by
      constructor
      · intro h1
        exact c.t_involution.1 (congrArg Subtype.val h1)
      · apply Subtype.ext
        simpa [pow_two] using c.t_involution.2
    change IsInvolution (QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩)
    exact quotient_involution_of_involution (Subgroup.center d.E) d.center_odd htE
  have hPcentQ : (P : Subgroup Q) ≤
      Subgroup.centralizer ({tQ} : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Sylow.coe_mapSurjective] at hy
    rcases Subgroup.mem_map.mp hy with ⟨e0, he0, rfl⟩
    have he0Map : (e0 : G) ∈ (SE : Subgroup d.E).map d.E.subtype :=
      Subgroup.mem_map.mpr ⟨e0, he0, rfl⟩
    have he0C : (e0 : G) ∈ Subgroup.centralizer ({c.t} : Set G) :=
      hSEamb_le he0Map
    have hcomm : (e0 : G) * c.t = c.t * (e0 : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp he0C
    have hcommE : e0 * (⟨c.t, d.t_mem_E⟩ : d.E) =
        (⟨c.t, d.t_mem_E⟩ : d.E) * e0 := Subtype.ext hcomm
    calc
      q e0 * q (⟨c.t, d.t_mem_E⟩ : d.E) = q (e0 * (⟨c.t, d.t_mem_E⟩ : d.E)) := by
        exact (map_mul q e0 (⟨c.t, d.t_mem_E⟩ : d.E)).symm
      _ = q ((⟨c.t, d.t_mem_E⟩ : d.E) * e0) := by rw [hcommE]
      _ = q (⟨c.t, d.t_mem_E⟩ : d.E) * q e0 := by
        exact map_mul q (⟨c.t, d.t_mem_E⟩ : d.E) e0
  let PP : Sylow 2 (PSL2 K) :=
    P.mapSurjective (f := e.some.toMonoidHom) e.some.surjective
  have htP : IsInvolution (e.some tQ) := by
    constructor
    · intro h1
      apply htQ.1
      have h' := congrArg e.some.symm h1
      simpa using h'
    · simpa using congrArg e.some htQ.2
  have hPPcent : (PP : Subgroup (PSL2 K)) ≤
      Subgroup.centralizer ({e.some tQ} : Set (PSL2 K)) := by
    exact centralizer_map_le e.some hPcentQ
  -- (3) the reflected torus with a reflection in the prescribed Sylow
  obtain ⟨TS, sS, hTcycS, htTS, hsSP, hsSnotT, hsSI, hPdecompS,
      hnormalizerS, hinvS, hcontainS⟩ :=
    secondCase_reflection_psl2_torus_fixedSylow K hK PP htP hPPcent
  -- (4) transport to the quotient (the torus contains the image of `t`)
  obtain ⟨T, sbar, hTcyc, htT, hsbarP, hsbar_not_T, hsbarI, hPdecomp,
      hnormalizer, hinvT, hcontainT⟩ :=
    quotient_fixedSylow_transport_t e.some P tQ
      ⟨TS, sS, hTcycS, htTS, hsSP, hsSnotT, hsSI, hPdecompS,
        hnormalizerS, hinvS, hcontainS⟩
  -- (5) lift to the component: `s ∈ SE` with `q s = sbar`
  obtain ⟨s, hsSE, hqs, hsI⟩ := lift_involution_in_sylow_of_quotient
    (Subgroup.center d.E) d.center_odd SE (hsbarP := hsbarP) hsbarI
  -- (6) the ambient reflection status `s ∈ S \ S0`
  have hsS : (s : G) ∈ (c.S : Subgroup G) := by
    have hmap : (s : G) ∈ (SE : Subgroup d.E).map d.E.subtype :=
      Subgroup.mem_map.mpr ⟨s, hsSE, rfl⟩
    rw [hSEamb] at hmap
    exact hmap.1
  have hq_s_not_T : q s ∉ T := by
    intro hqT
    
    rw [hqs] at hqT
    exact hsbar_not_T hqT
  have hPdecomp_qs :
      (SE.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center d.E)) :
        Subgroup Q) ≤ T ⊔ Subgroup.zpowers (q s) := by
    change (P : Subgroup Q) ≤ T ⊔ Subgroup.zpowers (q s)
    rw [hqs]
    exact hPdecomp
  have hnormalizer_qs :
      Subgroup.normalizer (Subgroup.zpowers tQ : Set Q) =
        T ⊔ Subgroup.zpowers (q s) := by
    rw [hqs]
    exact hnormalizer
  have hsS0 : (s : G) ∉ c.S0 := by
    intro hs0
    have hstE : s ≠ ⟨c.t, d.t_mem_E⟩ := by
      intro hst
      have hqT : q s ∈ T := by
        rw [hst]
        exact htT
      exact hq_s_not_T hqT
    have hcardS0 : Nat.card ↥c.S0 = 2 ^ c.m := by
      have h1 : Nat.card ↥(c.S : Subgroup G) = 2 * 2 ^ c.m := by
        rcases c.dihedralEquiv with ⟨eS⟩
        calc
          Nat.card ↥(c.S : Subgroup G) = Nat.card (DihedralGroup (2 ^ c.m)) := by
            exact Nat.card_congr eS.toEquiv
          _ = 2 * 2 ^ c.m := by
            rw [Nat.card_eq_fintype_card]
            exact DihedralGroup.card
      have h2 : Nat.card ↥(c.S : Subgroup G) = 2 * Nat.card ↥c.S0 := c.S_index_two
      rw [h1] at h2
      
      have h2' : 2 ^ c.m = Nat.card ↥c.S0 :=
        Nat.mul_left_cancel (n := 2) (m := 2 ^ c.m) (k := Nat.card ↥c.S0) (by norm_num : 0 < 2) h2
      exact h2'.symm
    have huniq := unique_involution_of_cyclic_two_group c.S0_cyclic c.one_le_m hcardS0
    let sS0 : ↥c.S0 := ⟨(s : G), hs0⟩
    let tS0 : ↥c.S0 := ⟨c.t, c.t_mem_S0⟩
    have hs2 : sS0 ^ 2 = 1 := by
      apply Subtype.ext
      
      rw [pow_two]
      
      change (s : G) * (s : G) = 1
      simpa [pow_two] using congrArg Subtype.val hsI.2
    have ht2 : tS0 ^ 2 = 1 := by
      apply Subtype.ext
      
      rw [pow_two]
      
      change c.t * c.t = 1
      simpa [pow_two] using c.t_involution.2
    have hsne : sS0 ≠ 1 := by
      intro h1
      apply hsI.1
      
      apply Subtype.ext
      exact congrArg (fun z : ↥c.S0 => (z : G)) h1
    have htne : tS0 ≠ 1 := by
      intro h1
      apply c.t_involution.1
      exact congrArg (fun z : ↥c.S0 => (z : G)) h1
    have hstS0 : sS0 = tS0 :=
      huniq sS0 tS0 hsne hs2 htne ht2
    have hstG : (s : G) = c.t := congrArg (fun z : ↥c.S0 => (z : G)) hstS0
    exact hstE (Subtype.ext hstG)
  -- (7) the reflected-torus package of the lifted `s`
  have hU_le_centralizer : c.U ≤ Subgroup.centralizer ({c.t} : Set G) := by
    have hU_le_H : c.U ≤ c.H := by
      unfold CentralizerSetup.U
      unfold oddCoreOf
      exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
    rw [← c.H_eq_centralizer]
    exact hU_le_H
  let U0 : Subgroup d.E := (c.U ⊓ d.E).subgroupOf d.E
  let UEbar : Subgroup Q := U0.map q
  have hU0odd : ∀ x : d.E, x ∈ U0 → Odd (orderOf x) := by
    intro x hx
    have hxU : (x : G) ∈ c.U := (Subgroup.mem_subgroupOf.mp hx).1
    have hordG : Odd (orderOf (x : G)) := odd_order_of_mem_U c (x : G) hxU
    have hordEq : orderOf (x : G) = orderOf x :=
      orderOf_injective d.E.subtype d.E.subtype_injective x
    simpa [hordEq] using hordG
  have hUEbar_odd : ∀ y : Q, y ∈ UEbar → Odd (orderOf y) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hxU0, rfl⟩
    exact odd_order_of_map_of_odd_order q (hU0odd x hxU0)
  have hUEbar_centralizer : UEbar ≤
      Subgroup.centralizer ({q ⟨c.t, d.t_mem_E⟩} : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Subgroup.mem_map.mp hy with ⟨x, hxU0, rfl⟩
    have hxU : (x : G) ∈ c.U := (Subgroup.mem_subgroupOf.mp hxU0).1
    have hxcentG : (x : G) ∈ Subgroup.centralizer ({c.t} : Set G) :=
      hU_le_centralizer hxU
    have hcommG : (x : G) * c.t = c.t * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hxcentG
    have hcommE : x * (⟨c.t, d.t_mem_E⟩ : d.E) =
        (⟨c.t, d.t_mem_E⟩ : d.E) * x := Subtype.ext hcommG
    calc
      q x * q (⟨c.t, d.t_mem_E⟩ : d.E) =
          q (x * (⟨c.t, d.t_mem_E⟩ : d.E)) := (map_mul q x (⟨c.t, d.t_mem_E⟩ : d.E)).symm
      _ = q ((⟨c.t, d.t_mem_E⟩ : d.E) * x) := by rw [hcommE]
      _ = q (⟨c.t, d.t_mem_E⟩ : d.E) * q x := map_mul q (⟨c.t, d.t_mem_E⟩ : d.E) x
  have hUEbar_le_T : UEbar ≤ T :=
    hcontainT UEbar hUEbar_odd hUEbar_centralizer
  let : IsCyclic T := hTcyc
  have hUEbar_cyclic : IsCyclic UEbar :=
    Subgroup.isCyclic_of_le hUEbar_le_T
  have hUEbar_inverted : BenderGlauberman.IsInvertedBy (q s) UEbar := by
    intro y hy
    rw [hqs]
    exact hinvT y (hUEbar_le_T hy)
  have hT_inverted : BenderGlauberman.IsInvertedBy (q s) T := by
    intro y hy
    rw [hqs]
    exact hinvT y hy
  -- (8) equations (1)--(2): the inverted subgroup `K` and the fixed part `B`
  let X : Subgroup G := c.U ⊓ w.M
  let sG : G := s
  have hsmap : sG ∈ (SE : Subgroup d.E).map d.E.subtype :=
    Subgroup.mem_map.mpr ⟨s, hsSE, rfl⟩
  have hsSM : sG ∈ ((SM : Subgroup w.M).map w.M.subtype) := by
    rw [hSEamb_join] at hsmap
    exact hsmap.1
  have hsM : sG ∈ w.M := (Subgroup.map_subtype_le (SM : Subgroup w.M)) hsSM
  have hsH : sG ∈ c.H := by
    rw [c.H_eq_centralizer]
    exact hSMcent hsSM
  have hsIG : IsInvolution sG := by
    constructor
    · intro h1
      apply hsI.1
      apply Subtype.ext
      exact h1
    · simpa [sG, pow_two] using congrArg Subtype.val hsI.2
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (↥(oddCoreOf c.H)))
    exact odd_card_oddCoreOf c.H
  have hcopX : Nat.Coprime 2 (Nat.card (↥X)) := by
    have hoddX : Odd (Nat.card (↥X)) :=
      Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left)
    exact Nat.coprime_two_left.mpr hoddX
  have hsX : ∀ x : G, x ∈ X → sG * x * sG⁻¹ ∈ X := by
    intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    refine ⟨(centralizerSetup_U_isNormalIn_H c).2 sG hsH x hx.1, ?_⟩
    exact w.M.mul_mem (w.M.mul_mem hsM hx.2) (w.M.inv_mem hsM)
  -- cyclic generator of the quotient image and a lift
  have hcycUEbar : IsCyclic UEbar := hUEbar_cyclic
  let : IsCyclic UEbar := hcycUEbar
  obtain ⟨xbar, hxbar_gen⟩ := IsCyclic.exists_generator (α := UEbar)
  have hxbar_mem : (xbar : Q) ∈ UEbar := xbar.2
  rcases Subgroup.mem_map.mp hxbar_mem with ⟨xE, hxE, hxq⟩
  have hxU : (xE : G) ∈ c.U := (Subgroup.mem_subgroupOf.mp hxE).1
  -- the commutator `z` lies in `U ∩ Z(E)`
  let zE : d.E := s * xE * s⁻¹ * xE
  have hq_s_x_inv : q (s * xE * s⁻¹) = (q xE)⁻¹ := by
    calc
      q (s * xE * s⁻¹) = q s * q xE * (q s)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      _ = q s * (xbar : Q) * (q s)⁻¹ := by rw [hxq]
      _ = (xbar : Q)⁻¹ := hUEbar_inverted (xbar : Q) hxbar_mem
      _ = (q xE)⁻¹ := by rw [← hxq]
  have hqz : q zE = 1 := by
    calc
      q zE = q (s * xE * s⁻¹ * xE) := rfl
      _ = q (s * xE * s⁻¹) * q xE := by rw [map_mul]
      _ = (q xE)⁻¹ * q xE := by rw [hq_s_x_inv]
      _ = 1 := by simp
  have hzcenter : zE ∈ Subgroup.center d.E :=
    (QuotientGroup.eq_one_iff (N := Subgroup.center d.E) zE).mp hqz
  have hzU : (zE : G) ∈ c.U := by
    change sG * (xE : G) * sG⁻¹ * (xE : G) ∈ c.U
    exact c.U.mul_mem
      ((centralizerSetup_U_isNormalIn_H c).2 sG hsH (xE : G) hxU) hxU
  -- choose the odd square root of `z⁻¹` inside `U ∩ Z(E)`
  let ZU : Subgroup d.E := c.U.subgroupOf d.E ⊓ Subgroup.center d.E
  have hZUodd : Odd (Nat.card ZU) := by
    have hdvd : Nat.card ZU ∣ Nat.card (c.U.subgroupOf d.E) :=
      Subgroup.card_dvd_of_le inf_le_left
    have hoddUsub : Odd (Nat.card (c.U.subgroupOf d.E)) := by
      have hsub_eq : (c.U ⊓ d.E).subgroupOf d.E = c.U.subgroupOf d.E := by
        ext x
        simp [Subgroup.mem_subgroupOf]
      have hcard : Nat.card (c.U.subgroupOf d.E) =
          Nat.card (c.U ⊓ d.E : Subgroup G) := by
        rw [← hsub_eq]
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := c.U ⊓ d.E) (K := d.E)
            inf_le_right).toEquiv
      have hdvdU : Nat.card (c.U ⊓ d.E : Subgroup G) ∣ Nat.card c.U :=
        Subgroup.card_dvd_of_le inf_le_left
      rw [hcard]
      exact Odd.of_dvd_nat hUodd hdvdU
    exact Odd.of_dvd_nat hoddUsub hdvd
  have hcopZU : Nat.Coprime 2 (Nat.card ZU) := Nat.coprime_two_left.mpr hZUodd
  let zZU : ZU := ⟨zE, Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_subgroupOf.mpr hzU, hzcenter⟩⟩
  let cZU : ZU := Classical.choose
    ((sq_bijective_of_coprime_two (G := ZU) hcopZU).2 zZU⁻¹)
  have hc_sq : cZU ^ 2 = zZU⁻¹ :=
    Classical.choose_spec
      ((sq_bijective_of_coprime_two (G := ZU) hcopZU).2 zZU⁻¹)
  let cE : d.E := cZU
  let cG : G := cE
  let kE : d.E := xE * cE
  let kG : G := kE
  have hcU : (cE : G) ∈ c.U := Subgroup.mem_subgroupOf.mp cZU.2.1
  have hcCenter : cE ∈ Subgroup.center d.E := cZU.2.2
  have hkU : kG ∈ c.U := c.U.mul_mem hxU hcU
  have hkM : kG ∈ w.M := d.E_component.1 (kE : d.E).2
  have hkX : kG ∈ X := Subgroup.mem_inf.mpr ⟨hkU, hkM⟩
  have hq_c : q cE = 1 :=
    (QuotientGroup.eq_one_iff (N := Subgroup.center d.E) cE).mpr hcCenter
  have hqk : q kE = q xE := by
    calc
      q kE = q (xE * cE) := rfl
      _ = q xE * q cE := map_mul q xE cE
      _ = q xE * 1 := by rw [hq_c]
      _ = q xE := by simp
  have hqk_bar : q kE = (xbar : Q) := hqk.trans hxq
  -- the chosen lift `k` is inverted by `s`
  have hc_sqE : cE ^ 2 = zE⁻¹ :=
    congrArg (fun z : ZU => (z : d.E)) hc_sq
  have hc_sqG : cG ^ 2 = (zE : G)⁻¹ := by
    have h' : (cE : d.E) ^ 2 = (zE : d.E)⁻¹ := hc_sqE
    simpa [cG] using congrArg (fun z : d.E => (z : G)) h'
  have hz_c_inv : (zE : G) * cG = cG⁻¹ := by
    have h1 : (zE : G) * cG ^ 2 = 1 := by
      rw [hc_sqG]
      simp
    calc
      (zE : G) * cG = (zE : G) * (cG * cG) * cG⁻¹ := by group
      _ = (zE : G) * (cG ^ 2) * cG⁻¹ := by rw [← pow_two]
      _ = 1 * cG⁻¹ := by rw [h1]
      _ = cG⁻¹ := by simp
  have hcs : sG * cG = cG * sG := by
    have h := (Subgroup.mem_center_iff.mp hcCenter s)
    simpa [sG, cG] using congrArg Subtype.val h
  have hsx : sG * (xE : G) * sG⁻¹ = (zE : G) * (xE : G)⁻¹ := by
    have hz_def : (zE : G) = sG * (xE : G) * sG⁻¹ * (xE : G) := rfl
    calc
      sG * (xE : G) * sG⁻¹ =
          (sG * (xE : G) * sG⁻¹ * (xE : G)) * (xE : G)⁻¹ := by group
      _ = (zE : G) * (xE : G)⁻¹ := by rw [hz_def]
  have hcx : (xE : G) * cG = cG * (xE : G) := by
    have h := (Subgroup.mem_center_iff.mp hcCenter xE)
    simpa [cG] using congrArg Subtype.val h
  have hkinvG : sG * kG * sG⁻¹ = kG⁻¹ := by
    calc
      sG * kG * sG⁻¹ = sG * ((xE : G) * cG) * sG⁻¹ := by
        simp [kG, kE, cG]
      _ = (sG * (xE : G) * sG⁻¹) * (sG * cG * sG⁻¹) := by group
      _ = (sG * (xE : G) * sG⁻¹) * cG := by
        have hscc : sG * cG * sG⁻¹ = cG := by
          calc
            sG * cG * sG⁻¹ = (cG * sG) * sG⁻¹ := by rw [hcs]
            _ = cG := by simp
        rw [hscc]
      _ = ((zE : G) * (xE : G)⁻¹) * cG := by rw [hsx]
      _ = (zE : G) * ((xE : G)⁻¹ * cG) := by group
      _ = (zE : G) * (cG * (xE : G)⁻¹) := by
        have hxcinv : (xE : G)⁻¹ * cG = cG * (xE : G)⁻¹ := by
          calc
            (xE : G)⁻¹ * cG = (xE : G)⁻¹ * (cG * (xE : G)) * (xE : G)⁻¹ := by group
            _ = (xE : G)⁻¹ * ((xE : G) * cG) * (xE : G)⁻¹ := by rw [hcx]
            _ = cG * (xE : G)⁻¹ := by group
        rw [hxcinv]
      _ = ((zE : G) * cG) * (xE : G)⁻¹ := by group
      _ = cG⁻¹ * (xE : G)⁻¹ := by rw [hz_c_inv]
      _ = ((xE : G) * cG)⁻¹ := by group
      _ = kG⁻¹ := by simp [kG, kE, cG]
  -- the inverted set is exactly `K = ⟨k⟩`
  let K : Subgroup G := Subgroup.zpowers kG
  let B : Subgroup G := centralizerIn X sG
  have hK_le_X : K ≤ X := Subgroup.zpowers_le.mpr hkX
  have hK_eq : (K : Set G) = invertedElements X sG := by
    ext y
    constructor
    · intro hyK
      rw [invertedElements]
      exact ⟨hK_le_X hyK, by
        rcases Subgroup.mem_zpowers_iff.mp hyK with ⟨n, hn⟩
        subst y
        exact zpow_inverted_of_generator_inverted hkinvG n⟩
    · rintro ⟨hyX, hys⟩
      have hyU : y ∈ c.U := hyX.1
      have hyM : y ∈ w.M := hyX.2
      have hyE : y ∈ d.E :=
        mem_E_of_inverted c w d SM hSMcent SE hSEamb_join hsSE hyU hyM hys
      let yE : d.E := ⟨y, hyE⟩
      have hyE_mem_XE : yE ∈ U0 :=
        Subgroup.mem_subgroupOf.mpr ⟨hyU, hyE⟩
      have hqy_mem : q yE ∈ UEbar :=
        Subgroup.mem_map.mpr ⟨yE, hyE_mem_XE, rfl⟩
      let ybar : UEbar := ⟨q yE, hqy_mem⟩
      have hybar_gen := hxbar_gen ybar
      rcases Subgroup.mem_zpowers_iff.mp hybar_gen with ⟨n, hn⟩
      have hqy_pow : (xbar : Q) ^ n = q yE :=
        congrArg (fun z : UEbar => (z : Q)) hn
      have hqk_pow : q (kE ^ n) = q yE := by
        calc
          q (kE ^ n) = (q kE) ^ n := map_zpow q kE n
          _ = (xbar : Q) ^ n := by rw [hqk_bar]
          _ = q yE := hqy_pow
      let rE : d.E := yE * (kE ^ n)⁻¹
      have hq_r : q rE = 1 := by
        calc
          q rE = q (yE * (kE ^ n)⁻¹) := rfl
          _ = q yE * q ((kE ^ n)⁻¹) := map_mul q yE ((kE ^ n)⁻¹)
          _ = q yE * (q (kE ^ n))⁻¹ := by rw [map_inv]
          _ = q yE * (q yE)⁻¹ := by rw [hqk_pow]
          _ = 1 := by simp
      have hrcenter : rE ∈ Subgroup.center d.E :=
        (QuotientGroup.eq_one_iff (N := Subgroup.center d.E) rE).mp hq_r
      let rG : G := rE
      have hr_def : rG = y * kG ^ (-n) := by
        calc
          rG = (yE : G) * ((kE ^ n)⁻¹ : d.E) := rfl
          _ = y * (kG ^ n)⁻¹ := by simp [kG, kE, yE]
          _ = y * kG ^ (-n) := by rw [zpow_neg]
      have hrU : rG ∈ c.U := by
        rw [hr_def]
        exact c.U.mul_mem hyU (c.U.zpow_mem hkU (-n))
      have hs_fix : sG * rG * sG⁻¹ = rG := by
        have hcomm : sG * rG = rG * sG :=
          congrArg Subtype.val (Subgroup.mem_center_iff.mp hrcenter s)
        calc
          sG * rG * sG⁻¹ = (rG * sG) * sG⁻¹ := by rw [hcomm]
          _ = rG := by simp
      have hr_comm_y : y * rG = rG * y :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hrcenter yE)
      have hcomm_k_y : y * kG ^ (-n) = kG ^ (-n) * y := by
        have h' : y * (y * kG ^ (-n)) = (y * kG ^ (-n)) * y := by
          simpa [hr_def] using hr_comm_y
        calc
          y * kG ^ (-n) = y * y⁻¹ * (y * kG ^ (-n)) := by group
          _ = y⁻¹ * (y * (y * kG ^ (-n))) := by group
          _ = y⁻¹ * ((y * kG ^ (-n)) * y) := by rw [h']
          _ = kG ^ (-n) * y := by group
      have hk_neg_inv : sG * kG ^ (-n) * sG⁻¹ = (kG ^ (-n))⁻¹ :=
        zpow_inverted_of_generator_inverted hkinvG (-n)
      have hs_inv : sG * rG * sG⁻¹ = rG⁻¹ := by
        rw [hr_def]
        calc
          sG * (y * kG ^ (-n)) * sG⁻¹ =
              (sG * y * sG⁻¹) * (sG * kG ^ (-n) * sG⁻¹) := by group
          _ = y⁻¹ * (kG ^ (-n))⁻¹ := by rw [hys, hk_neg_inv]
          _ = (kG ^ (-n) * y)⁻¹ := by group
          _ = (y * kG ^ (-n))⁻¹ := by rw [hcomm_k_y]
      have hsq_r : rG ^ 2 = 1 := by
        have h : rG = rG⁻¹ := hs_fix.symm.trans hs_inv
        rw [pow_two]
        calc
          rG * rG = rG⁻¹ * rG := congrArg (fun z => z * rG) h
          _ = 1 := by simp
      have hrG_one : rG = 1 := by
        let rC : Subgroup.center d.E := ⟨rE, hrcenter⟩
        have hsq_rC : rC ^ 2 = 1 := by
          apply Subtype.ext
          apply Subtype.ext
          simpa [rG, pow_two] using hsq_r
        have hrC_one : rC = 1 :=
          eq_one_of_sq_eq_one_of_coprime_two (G := Subgroup.center d.E)
            (Nat.coprime_two_left.mpr d.center_odd) hsq_rC
        simpa [rG, rC] using congrArg Subtype.val hrC_one
      have h1 : y * kG ^ (-n) = 1 := by
        simpa [hr_def] using hrG_one
      have hy_eq : y = kG ^ n := by
        calc
          y = (y * kG ^ (-n)) * kG ^ n := by group
          _ = 1 * kG ^ n := by rw [h1]
          _ = kG ^ n := by simp
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, hy_eq.symm⟩
  have hK_cyc : IsCyclic K := by
    dsimp [K]
    infer_instance
  have hK_le_E : K ≤ d.E := by
    intro y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, hn⟩
    rw [← hn]
    simpa [kG] using d.E.zpow_mem kE.2 n
  have hK_map :
      (K.subgroupOf d.E).map q = UEbar := by
    apply le_antisymm
    · intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨xE, hxE, rfl⟩
      have hxK : (xE : G) ∈ K :=
        Subgroup.mem_subgroupOf.mp hxE
      rcases Subgroup.mem_zpowers_iff.mp hxK with ⟨n, hn⟩
      have hpowE : kE ^ n = xE := by
        apply Subtype.ext
        exact hn
      have hqpow : q xE = (xbar : Q) ^ n := by
        calc
          q xE = q (kE ^ n) := by rw [hpowE]
          _ = (q kE) ^ n := map_zpow q kE n
          _ = (xbar : Q) ^ n := by rw [hqk_bar]
      rw [hqpow]
      exact UEbar.zpow_mem xbar.2 n
    · intro y hy
      let ybar : UEbar := ⟨y, hy⟩
      rcases hxbar_gen ybar with ⟨n, hn⟩
      have hyq : (xbar : Q) ^ n = y :=
        congrArg (fun z : UEbar => (z : Q)) hn
      have hqpow : q (kE ^ n) = y := by
        calc
          q (kE ^ n) = (q kE) ^ n := map_zpow q kE n
          _ = (xbar : Q) ^ n := by rw [hqk_bar]
          _ = y := hyq
      have hkpow : (kE ^ n : G) ∈ K := by
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
      have hkpowE : kE ^ n ∈ K.subgroupOf d.E :=
        Subgroup.mem_subgroupOf.mpr hkpow
      exact Subgroup.mem_map.mpr ⟨kE ^ n, hkpowE, hqpow⟩
  have hK_center :
      (K.subgroupOf d.E) ⊓ Subgroup.center d.E = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    have hzK : (z : G) ∈ K :=
      Subgroup.mem_subgroupOf.mp hz.1
    have hzI : (z : G) ∈ invertedElements X sG := by
      rw [← hK_eq]
      exact hzK
    have hcomm : z * s = s * z :=
      (Subgroup.mem_center_iff.mp hz.2 s).symm
    have hfixE : s * z * s⁻¹ = z := by
      calc
        s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hcomm.symm]
        _ = z := by simp
    have hinvE : s * z * s⁻¹ = z⁻¹ := by
      apply Subtype.ext
      exact hzI.2
    have hzsq : z ^ 2 = 1 := by
      have hz_eq : z = z⁻¹ := hfixE.symm.trans hinvE
      rw [pow_two]
      calc
        z * z = z * z⁻¹ := congrArg (fun y => z * y) hz_eq
        _ = 1 := by simp
    let zc : Subgroup.center d.E := ⟨z, hz.2⟩
    have hzsqc : zc ^ 2 = 1 := by
      apply Subtype.ext
      exact hzsq
    have hzc_one : zc = 1 :=
      eq_one_of_sq_eq_one_of_coprime_two
        (G := Subgroup.center d.E)
        (Nat.coprime_two_left.mpr d.center_odd) hzsqc
    have hz_one : z = 1 := congrArg Subtype.val hzc_one
    simpa [hz_one]
  -- join `X = K ⊔ B` via Fact 1.5(ii) and normality of `K` in `X`
  have hKnormal : IsNormalIn K X :=
    (fact_1_5_iii_inverted_subgroup_abelian_normal (X := X) (s := sG)
      hsIG hcopX hsX (I := K) hK_eq).2.1
  have hB_le_X : B ≤ X := by
    intro x hx
    exact hx.1
  have hB_le_NK : B ≤ Subgroup.normalizer (K : Set G) := by
    intro b hbB
    exact le_normalizer_of_isNormalIn hKnormal (hB_le_X hbB)
  have hcarrier : (↑(K ⊔ B) : Set G) = (K : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K B hB_le_NK
  have hBK_eq : (B : Set G) * (K : Set G) = (K : Set G) * (B : Set G) :=
    Subgroup.set_mul_normalizer_comm (S := (B : Set G)) (N := K) hB_le_NK
  have hjoin : K ⊔ B = X := by
    apply le_antisymm
    · exact sup_le hK_le_X hB_le_X
    · intro x hx
      rcases fact_1_5_ii_decomposition (X := X) (s := sG) hsIG hcopX hsX x hx
        with ⟨c, hcB, i, hiI, hxi⟩
      have hiK : i ∈ K := by
        have : i ∈ invertedElements X sG := hiI
        rwa [← hK_eq] at this
      have hx_BK : x ∈ (B : Set G) * (K : Set G) :=
        ⟨c, hcB, i, hiK, hxi.symm⟩
      have hx_KB : x ∈ (K : Set G) * (B : Set G) := by
        rw [hBK_eq] at hx_BK
        exact hx_BK
      change x ∈ (↑(K ⊔ B) : Set G)
      rw [hcarrier]
      exact hx_KB
  -- (9) equations (3): the Fitting intersection `K0` and the fixed part `F`
  let FU : Subgroup G := fittingSubgroupOf c.U
  let Y : Subgroup G := FU ⊓ w.M
  let K0 : Subgroup G := FU ⊓ K
  let F : Subgroup G := FU ⊓ B
  have hFUnormalH : IsNormalIn (fittingSubgroupOf c.U) c.H := by
    change IsNormalIn ((fittingSubgroup (↥c.U)).map c.U.subtype) c.H
    exact map_characteristic_isNormalIn_of_isNormalIn
      (K := fittingSubgroup (↥c.U)) (hKchar := by infer_instance)
      (hHnormal := centralizerSetup_U_isNormalIn_H c)
  have hYleU : Y ≤ c.U := by
    intro y hy
    exact fittingSubgroupOf_le c.U hy.1
  have hoddY : Odd (Nat.card (↥Y)) :=
    Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le hYleU)
  have hcopY : Nat.Coprime 2 (Nat.card (↥Y)) :=
    Nat.coprime_two_left.mpr hoddY
  have hsY : ∀ y : G, y ∈ Y → sG * y * sG⁻¹ ∈ Y := by
    intro y hy
    rw [Subgroup.mem_inf] at hy ⊢
    refine ⟨hFUnormalH.2 sG hsH y hy.1, ?_⟩
    exact w.M.mul_mem (w.M.mul_mem hsM hy.2) (w.M.inv_mem hsM)
  have hK0_carrier : (K0 : Set G) = invertedElements Y sG := by
    ext y
    constructor
    · intro hyK0
      have hyFU : y ∈ FU := hyK0.1
      have hyK : y ∈ K := hyK0.2
      have hyI : y ∈ invertedElements X sG := by
        rw [← hK_eq]
        exact hyK
      rw [invertedElements] at hyI ⊢
      exact ⟨⟨hyFU, hyI.1.2⟩, hyI.2⟩
    · intro hyI
      rw [invertedElements] at hyI
      have hyFU : y ∈ FU := hyI.1.1
      have hyM : y ∈ w.M := hyI.1.2
      have hyX : y ∈ X :=
        Subgroup.mem_inf.mpr ⟨fittingSubgroupOf_le c.U hyFU, hyM⟩
      have hyK : y ∈ K := by
        change y ∈ (K : Set G)
        rw [hK_eq]
        rw [invertedElements]
        exact ⟨hyX, hyI.2⟩
      show y ∈ FU ⊓ K
      exact ⟨hyFU, hyK⟩
  have hF_eq : F = centralizerIn Y sG := by
    ext x
    constructor
    · intro hxF
      have hxB : x ∈ B := hxF.2
      have hxfix : sG * x * sG⁻¹ = x :=
        (mem_centralizerIn_local X sG x).mp (by simpa [B] using hxB) |>.2
      have hxM : x ∈ w.M :=
        (mem_centralizerIn_local X sG x).mp (by simpa [B] using hxB) |>.1 |>.2
      exact (mem_centralizerIn_local Y sG x).mpr ⟨⟨hxF.1, hxM⟩, hxfix⟩
    · intro hxC
      have hxY : x ∈ Y := (mem_centralizerIn_local Y sG x).mp hxC |>.1
      have hxfix : sG * x * sG⁻¹ = x :=
        (mem_centralizerIn_local Y sG x).mp hxC |>.2
      have hxU : x ∈ c.U := fittingSubgroupOf_le c.U hxY.1
      have hxB : x ∈ B := by
        simpa [B] using (mem_centralizerIn_local X sG x).mpr
          ⟨Subgroup.mem_inf.mpr ⟨hxU, hxY.2⟩, hxfix⟩
      exact Subgroup.mem_inf.mpr ⟨hxY.1, hxB⟩
  -- `K0 ⊔ F = Y` by Fact 1.5(ii)/(iii), exactly as for `K ⊔ B = X`
  have hK0_le_Y : K0 ≤ Y := by
    intro y hy
    have : y ∈ invertedElements Y sG := by
      rw [← hK0_carrier]
      exact hy
    rw [invertedElements] at this
    exact this.1
  have hF_le_Y : F ≤ Y := by
    intro x hx
    exact (mem_centralizerIn_local Y sG x).mp (by simpa [hF_eq] using hx) |>.1
  have hK0normal : IsNormalIn K0 Y :=
    (fact_1_5_iii_inverted_subgroup_abelian_normal (X := Y) (s := sG)
      hsIG hcopY hsY (I := K0) hK0_carrier).2.1
  have hF_le_NK0 : F ≤ Subgroup.normalizer (K0 : Set G) := by
    intro f hf
    exact le_normalizer_of_isNormalIn hK0normal (hF_le_Y hf)
  have hcarrierY : (↑(K0 ⊔ F) : Set G) = (K0 : Set G) * (F : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K0 F hF_le_NK0
  have hFK0_eq : (F : Set G) * (K0 : Set G) = (K0 : Set G) * (F : Set G) :=
    Subgroup.set_mul_normalizer_comm (S := (F : Set G)) (N := K0) hF_le_NK0
  have hjoinY : K0 ⊔ F = Y := by
    apply le_antisymm
    · exact sup_le hK0_le_Y hF_le_Y
    · intro y hyY
      rcases fact_1_5_ii_decomposition (X := Y) (s := sG) hsIG hcopY hsY y hyY
        with ⟨c, hcC, i, hiI, hyi⟩
      have hcF : c ∈ F := by
        rw [hF_eq]
        exact hcC
      have hiK0 : i ∈ K0 := by
        change i ∈ (K0 : Set G)
        rw [hK0_carrier]
        exact hiI
      have hy_FK0 : y ∈ (F : Set G) * (K0 : Set G) :=
        ⟨c, hcF, i, hiK0, hyi.symm⟩
      have hy_K0F : y ∈ (K0 : Set G) * (F : Set G) := by
        rw [hFK0_eq] at hy_FK0
        exact hy_FK0
      change y ∈ (↑(K0 ⊔ F) : Set G)
      rw [hcarrierY]
      exact hy_K0F
  have hK0_def : K0 = fittingSubgroupOf c.U ⊓ K := by
    change K0 = FU ⊓ K
    rfl
  have hF_def : F = fittingSubgroupOf c.U ⊓ B := by
    change F = FU ⊓ B
    rfl
  have hB_centSE : B ≤ Subgroup.centralizer
      (((SE : Subgroup d.E).map d.E.subtype : Subgroup G) : Set G) := by
    exact secondCase_psl2_fixed_factor_centralizes_componentSylow
      c w d Kfield hKfield efield SE hSEamb T s hsSE hsI hTcyc htT hq_s_not_T
      hPdecomp_qs hnormalizer_qs (by
        intro x hx
        exact hT_inverted x hx) B (by rfl)
  have hK_normSE : ((SE : Subgroup d.E).map d.E.subtype) ≤
      Subgroup.normalizer (K : Set G) := by
    exact secondCase_linear_componentSylow_le_normalizer_K
      c w d SM hSMleS SE hSEamb_join T s hsSE hsI hTcyc hq_s_not_T
      hPdecomp_qs (by
        intro x hx
        exact hT_inverted x hx) hUEbar_le_T hUEbar_odd
      hUEbar_inverted K B hK_eq hK_le_E hK_map hK_center (by rfl) hB_centSE
  refine ⟨hSMcent, hSEamb_join, T, s, hsSE, hsI, hTcyc, htT, hq_s_not_T,
    hPdecomp_qs, hnormalizer_qs, hT_inverted, hcontainT, hUEbar_le_T,
    hUEbar_cyclic, hUEbar_inverted,
    hsS, hsS0, K, B, hK_eq, hK_cyc, rfl, hB_centSE, hK_le_E, hK_map,
    hK_center, hK_normSE, hjoin, K0, F, hK0_def, hF_def, ?_,
    ?_⟩
  · simpa [FU, Y, sG] using hF_eq
  · simpa [FU, Y] using hjoinY

end CFSG.GorensteinWalter
