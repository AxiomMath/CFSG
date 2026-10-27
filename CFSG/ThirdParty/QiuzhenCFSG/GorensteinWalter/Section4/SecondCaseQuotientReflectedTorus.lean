module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseCentralizerSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseReflectionASevenFixedSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseReflectionPSL2FixedSylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: the common reflected-quotient package

This is the quotient-level package shared by equations (1)--(3) in Section 4.
Given the ambient Sylow subgroups from
`secondCase_centralizer_contains_sylow`, and either fixed-Sylow endpoint, we
produce a cyclic reflected torus `T` in `E / Z(E)` together with an
involution `s ∈ E` whose image is the reflection of that torus.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u v

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

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

/-- Transport an endpoint reflected-torus package through an equivalence of
the quotient models. -/
private theorem quotient_fixedSylow_transport
    {Q : Type u} {S : Type v} [Group Q] [Finite Q] [Group S] [Finite S]
    (e : Q ≃* S)
    (P : Sylow 2 Q) {t : Q}
    (hendpoint :
      ∃ T : Subgroup S, ∃ s : S,
        IsCyclic T ∧
          s ∈ (P.map e.toMonoidHom : Subgroup S) ∧
          s ∉ T ∧ IsInvolution s ∧
            (∀ x : S, x ∈ T → s * x * s⁻¹ = x⁻¹) ∧
              ∀ X : Subgroup S,
                (∀ x : S, x ∈ X → Odd (orderOf x)) →
                  X ≤ Subgroup.centralizer ({e t} : Set S) → X ≤ T) :
    ∃ T : Subgroup Q, ∃ s : Q,
      IsCyclic T ∧ s ∈ (P : Subgroup Q) ∧ s ∉ T ∧ IsInvolution s ∧
        (∀ x : Q, x ∈ T → s * x * s⁻¹ = x⁻¹) ∧
          ∀ X : Subgroup Q,
            (∀ x : Q, x ∈ X → Odd (orderOf x)) →
              X ≤ Subgroup.centralizer ({t} : Set Q) → X ≤ T := by
  classical
  rcases hendpoint with ⟨TS, sS, hTcycS, hsSP, hsSnotT, hsSI, hinvS, hcontainS⟩
  let T : Subgroup Q := TS.map e.symm.toMonoidHom
  let s : Q := e.symm sS
  have hTcyc : IsCyclic T := by
    let eT : TS ≃* T :=
      Subgroup.equivMapOfInjective TS e.symm.toMonoidHom e.symm.injective
    exact (MulEquiv.isCyclic eT).mp hTcycS
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
  exact ⟨T, s, hTcyc, hsP, hs_not_T, hsI, hinvT, hcontain⟩

/-- Assemble the ambient Sylow data and the transported quotient reflector
into the common reflected-quotient package. -/
private theorem assemble_common_package
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (SM : Sylow 2 (↥w.M))
    (hSMcent : ((SM : Subgroup w.M).map w.M.subtype) ≤
      Subgroup.centralizer ({c.t} : Set G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E)
    (T : Subgroup (d.E ⧸ Subgroup.center d.E))
    {sbar : d.E ⧸ Subgroup.center d.E}
    (hsbarP : sbar ∈
      (SE.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center d.E)) :
        Subgroup (d.E ⧸ Subgroup.center d.E)))
    (hTcyc : IsCyclic T) (hsbar_not_T : sbar ∉ T)
    (hsbarI : IsInvolution sbar)
    (hinvT : ∀ x : d.E ⧸ Subgroup.center d.E, x ∈ T →
      sbar * x * sbar⁻¹ = x⁻¹)
    (hcontainT : ∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
      (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X → Odd (orderOf x)) →
        X ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩} :
            Set (d.E ⧸ Subgroup.center d.E)) → X ≤ T) :
    ∃ SM : Sylow 2 (↥w.M),
      ((SM : Subgroup w.M).map w.M.subtype) ≤
        Subgroup.centralizer ({c.t} : Set G) ∧
      ∃ SE : Sylow 2 (↥d.E),
        (SE : Subgroup d.E).map d.E.subtype =
          ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E ∧
        ∃ T : Subgroup (d.E ⧸ Subgroup.center d.E),
          ∃ s : d.E,
            let q : d.E →* d.E ⧸ Subgroup.center d.E :=
              QuotientGroup.mk' (Subgroup.center d.E)
            IsCyclic T ∧ s ∈ (SE : Subgroup d.E) ∧ IsInvolution s ∧
              q s ∉ T ∧
              (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ T →
                q s * x * (q s)⁻¹ = x⁻¹) ∧
              ∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
                (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X →
                  Odd (orderOf x)) →
                  X ≤ Subgroup.centralizer
                    ({q ⟨c.t, d.t_mem_E⟩} :
                      Set (d.E ⧸ Subgroup.center d.E)) →
                    X ≤ T := by
  classical
  obtain ⟨s, hsSE, hqs, hsI⟩ := lift_involution_in_sylow_of_quotient
    (Subgroup.center d.E) d.center_odd SE (hsbarP := hsbarP) hsbarI
  refine ⟨SM, hSMcent, SE, hSEamb, T, s, hTcyc, hsSE, hsI, ?_, ?_,
    hcontainT⟩
  · rw [hqs]
    exact hsbar_not_T
  · intro x hx
    rw [hqs]
    exact hinvT x hx

/-- The common reflected-quotient package for the second case. -/
public theorem secondCase_quotient_reflected_torus_data
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) :
    ∃ SM : Sylow 2 (↥w.M),
      ((SM : Subgroup w.M).map w.M.subtype) ≤
        Subgroup.centralizer ({c.t} : Set G) ∧
      ∃ SE : Sylow 2 (↥d.E),
        (SE : Subgroup d.E).map d.E.subtype =
          ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E ∧
        ∃ T : Subgroup (d.E ⧸ Subgroup.center d.E),
          ∃ s : d.E,
            let q : d.E →* d.E ⧸ Subgroup.center d.E :=
              QuotientGroup.mk' (Subgroup.center d.E)
            IsCyclic T ∧ s ∈ (SE : Subgroup d.E) ∧ IsInvolution s ∧
              q s ∉ T ∧
              (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ T →
                q s * x * (q s)⁻¹ = x⁻¹) ∧
              ∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
                (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X →
                  Odd (orderOf x)) →
                  X ≤ Subgroup.centralizer
                    ({q ⟨c.t, d.t_mem_E⟩} :
                      Set (d.E ⧸ Subgroup.center d.E)) →
                    X ≤ T := by
  classical
  obtain ⟨SM, hSMcent, SE, hSEamb⟩ :=
    secondCase_centralizer_contains_sylow c w d
  let Q : Type u := d.E ⧸ Subgroup.center d.E
  let q : d.E →* Q := QuotientGroup.mk' (Subgroup.center d.E)
  let P : Sylow 2 Q :=
    SE.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center d.E))
  let tQ : Q := q ⟨c.t, d.t_mem_E⟩
  have hSEamb_le : (SE : Subgroup d.E).map d.E.subtype ≤
      Subgroup.centralizer ({c.t} : Set G) := by
    rw [hSEamb]
    exact le_trans inf_le_left hSMcent
  have htQ : IsInvolution tQ := by
    have htE : IsInvolution (⟨c.t, d.t_mem_E⟩ : d.E) := by
      constructor
      · intro h1
        exact c.t_involution.1 (congrArg Subtype.val h1)
      · apply Subtype.ext
        simpa [pow_two] using c.t_involution.2
    change IsInvolution
      (QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩)
    exact quotient_involution_of_involution (Subgroup.center d.E)
      d.center_odd htE
  have hPcentQ : (P : Subgroup Q) ≤
      Subgroup.centralizer ({tQ} : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Sylow.coe_mapSurjective] at hy
    rcases Subgroup.mem_map.mp hy with ⟨e, he, rfl⟩
    have heMap : (e : G) ∈ (SE : Subgroup d.E).map d.E.subtype :=
      Subgroup.mem_map.mpr ⟨e, he, rfl⟩
    have heC : (e : G) ∈ Subgroup.centralizer ({c.t} : Set G) :=
      hSEamb_le heMap
    have hcomm : (e : G) * c.t = c.t * (e : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp heC
    have hcommE : e * (⟨c.t, d.t_mem_E⟩ : d.E) =
        (⟨c.t, d.t_mem_E⟩ : d.E) * e := Subtype.ext hcomm
    calc
      q e * q (⟨c.t, d.t_mem_E⟩ : d.E) =
          q (e * (⟨c.t, d.t_mem_E⟩ : d.E)) := by
        exact (map_mul q e (⟨c.t, d.t_mem_E⟩ : d.E)).symm
      _ = q ((⟨c.t, d.t_mem_E⟩ : d.E) * e) := by rw [hcommE]
      _ = q (⟨c.t, d.t_mem_E⟩ : d.E) * q e := by
        exact map_mul q (⟨c.t, d.t_mem_E⟩ : d.E) e
  cases hmodel : d.model with
  | alternating eA =>
      let e : Q ≃* alternatingGroup (Fin 7) := eA.some
      let PA : Sylow 2 (alternatingGroup (Fin 7)) :=
        P.mapSurjective (f := e.toMonoidHom) e.toEquiv.surjective
      have htA : IsInvolution (e tQ) := by
        constructor
        · intro h1
          apply htQ.1
          have h' := congrArg e.symm h1
          simpa using h'
        · simpa using congrArg e htQ.2
      have hPAcent : (PA : Subgroup (alternatingGroup (Fin 7))) ≤
          Subgroup.centralizer ({e tQ} : Set (alternatingGroup (Fin 7))) := by
        exact centralizer_map_le e hPcentQ
      obtain ⟨TS, sS, hTcycS, hsSP, hsSnotT, hsSI, hinvS, hcontainS⟩ :=
        secondCase_reflection_a7_torus_fixedSylow PA htA hPAcent
      obtain ⟨T, sbar, hTcyc, hsbarP, hsbar_not_T, hsbarI, hinvT,
          hcontainT⟩ :=
        quotient_fixedSylow_transport e P
          ⟨TS, sS, hTcycS, hsSP, hsSnotT, hsSI, hinvS, hcontainS⟩
      exact assemble_common_package c w d SM hSMcent SE hSEamb T
        hsbarP hTcyc hsbar_not_T hsbarI hinvT hcontainT
  | projectiveSpecialLinear K hKprimePower eP =>
      let e : Q ≃* PSL2 K := eP.some
      let PP : Sylow 2 (PSL2 K) :=
        P.mapSurjective (f := e.toMonoidHom) e.toEquiv.surjective
      have htP : IsInvolution (e tQ) := by
        constructor
        · intro h1
          apply htQ.1
          have h' := congrArg e.symm h1
          simpa using h'
        · simpa using congrArg e htQ.2
      have hPPcent : (PP : Subgroup (PSL2 K)) ≤
          Subgroup.centralizer ({e tQ} : Set (PSL2 K)) := by
        exact centralizer_map_le e hPcentQ
      obtain ⟨TS, sS, hTcycS, htTS, hsSP, hsSnotT, hsSI, _hPdecompS,
          _hnormalizerS, hinvS, hcontainS⟩ :=
        secondCase_reflection_psl2_torus_fixedSylow K hKprimePower PP htP hPPcent
      obtain ⟨T, sbar, hTcyc, hsbarP, hsbar_not_T, hsbarI, hinvT,
          hcontainT⟩ :=
        quotient_fixedSylow_transport e P
          ⟨TS, sS, hTcycS, hsSP, hsSnotT, hsSI, hinvS, hcontainS⟩
      exact assemble_common_package c w d SM hSMcent SE hSEamb T
        hsbarP hTcyc hsbar_not_T hsbarI hinvT hcontainT

end CFSG.GorensteinWalter
