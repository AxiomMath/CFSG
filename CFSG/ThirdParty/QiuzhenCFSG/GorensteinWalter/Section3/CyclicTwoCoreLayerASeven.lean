module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCyclicTwoCoreInfra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourSelfCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotientNotTwoGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourQuotientOddKernel
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Forcing the cyclic first-case layer quotient to be A₇

Enlarge the component layer `E(M)` by the centralizing Klein four `V₁` and
apply the D-group classification to `R = E(M) V₁`.  The odd cyclic subgroup
survives modulo `O(R)`, while the Klein four survives because the kernel is
odd.  Thus the linear alternatives contradict the `PSL₂/PGL₂` Klein-four
centralizer endpoint.  In the surviving A₇ branch the perfect normal image
of `E(M)` is all of A₇, and the restricted kernel is exactly `O(E(M))`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem componentLayerOf_isPerfect_for_layerASeven
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) :
    Group.IsPerfect (↥(componentLayerOf M)) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm
  · exact (Subgroup.commutator_le_sup _ _).trans (sup_idem _).le
  · rw [componentLayerOf]
    apply sSup_le
    intro K hK
    have hKE : K ≤ componentLayerOf M := le_sSup hK
    have hKK : ⁅K, K⁆ = K :=
      Subgroup.isPerfect_iff.mp ((Group.isPerfect_def).2 hK.2.2.2.1)
    rw [← hKK]
    exact Subgroup.commutator_mono hKE hKE

private theorem no_kleinFour_cyclic_in_linear_model
    {H : Type u} [Group H] [Finite H]
    (A V : Subgroup H)
    (hAcyc : IsCyclic A) (hAne : A ≠ ⊥) (hAodd : Odd (Nat.card A))
    (hVK : IsKleinFour V)
    (hVcent : V ≤ Subgroup.centralizer (A : Set H))
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (hmodel : Nonempty (H ≃* PSL2 K) ∨ Nonempty (H ≃* PGL2 K)) :
    False := by
  rcases hmodel with hPSL | hPGL
  · rcases hPSL with ⟨e⟩
    let A0 : Subgroup (PSL2 K) := A.map e.toMonoidHom
    let V0 : Subgroup (PSL2 K) := V.map e.toMonoidHom
    let eA : A ≃* A0 := Subgroup.equivMapOfInjective A e.toMonoidHom e.injective
    have hA0cyc : IsCyclic A0 := eA.isCyclic.mp hAcyc
    have hA0ne : A0 ≠ ⊥ := by
      intro hbot
      exact hAne ((Subgroup.map_eq_bot_iff_of_injective
        (H := A) (f := e.toMonoidHom) e.injective).mp hbot)
    have hA0odd : Odd (Nat.card A0) := by
      rw [Subgroup.card_map_of_injective e.injective]
      exact hAodd
    have hV0K : IsKleinFour V0 :=
      isKleinFour_map_mulEquiv_cross V hVK e
    have hV0cent : V0 ≤ Subgroup.centralizer (A0 : Set (PSL2 K)) :=
      centralizer_map_le_of_mulEquiv e A V hVcent
    exact psl2_no_kleinFour_centralizes_odd_cyclic
      K hK A0 V0 hA0cyc hA0ne hA0odd hV0K hV0cent
  · rcases hPGL with ⟨e⟩
    let A0 : Subgroup (PGL2 K) := A.map e.toMonoidHom
    let V0 : Subgroup (PGL2 K) := V.map e.toMonoidHom
    let eA : A ≃* A0 := Subgroup.equivMapOfInjective A e.toMonoidHom e.injective
    have hA0cyc : IsCyclic A0 := eA.isCyclic.mp hAcyc
    have hA0ne : A0 ≠ ⊥ := by
      intro hbot
      exact hAne ((Subgroup.map_eq_bot_iff_of_injective
        (H := A) (f := e.toMonoidHom) e.injective).mp hbot)
    have hA0odd : Odd (Nat.card A0) := by
      rw [Subgroup.card_map_of_injective e.injective]
      exact hAodd
    have hV0K : IsKleinFour V0 :=
      isKleinFour_map_mulEquiv_cross V hVK e
    have hV0cent : V0 ≤ Subgroup.centralizer (A0 : Set (PGL2 K)) :=
      centralizer_map_le_of_mulEquiv e A V hVcent
    exact pgl2_no_kleinFour_centralizes_odd_cyclic
      K hK A0 V0 hA0cyc hA0ne hA0odd hV0K hV0cent

/-- In the cyclic two-core subcase, the quotient of the selected component
layer by its odd core is `A₇`; the full inverted odd and Klein-four package
is retained for the subsequent A₇ calculations. -/
public theorem firstCase_cyclic_layer_quotient_isASeven_of_od
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
    (od : FirstCaseOrientedPrimeData c) :
    ∃ hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B,
        ∃ fd : FirstCaseFourData c od.d,
          ∃ Q : Sylow od.p ↥od.d.bg.B,
            ∃ M : Subgroup G, ∃ X : Subgroup G,
              IsCoatom M ∧
                Subgroup.normalizer
                  (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M ∧
                  (c.S : Subgroup G) ≤ M ∧
                    fd.V2 ≤ componentLayerOf M ∧
                      X ≤ componentLayerOf M ∧ X ≠ ⊥ ∧ IsCyclic X ∧
                        IsPGroup od.p X ∧
                        X ≤ qCoreOf od.d.bg.U od.p ∧
                        BenderGlauberman.IsInvertedBy od.d.bg.t2 X ∧
                          X ≤ Subgroup.centralizer (fd.V1 : Set G) ∧
                            IsDGroup (↥(componentLayerOf M)) ∧
                              Nonempty ((componentLayerOf M) ⧸
                                pPrimeCore 2 (componentLayerOf M) ≃*
                                  alternatingGroup (Fin 7)) := by
  classical
  obtain ⟨hU, fd, Q, M, X, hMmax, hMN, hSM, hV2, hXleE, hXne,
    hXcyc, hXp, hXleP, hXinv, hXcent, hDE⟩ :=
    firstCase_cyclic_layer_inverted_and_DGroup_of_od hmin c hfirst hcyclic od
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let E : Subgroup G := componentLayerOf M
  let R : Subgroup G := E ⊔ fd.V1
  have hEleM : E ≤ M := (componentLayerOf_isNormalIn M).1
  have hV1leM : fd.V1 ≤ M := fd.V1_le_S.trans hSM
  have hRleM : R ≤ M := sup_le hEleM hV1leM
  have hRproper : R ≠ ⊤ := by
    intro htop
    have hMtop : M = ⊤ := le_antisymm le_top (by
      intro x hx
      exact hRleM (by simpa [htop] using hx))
    exact hMmax.1 hMtop
  have hDR : IsDGroup (↥R) := properSubgroups_areDGroups hmin R hRproper
  have hEleR : E ≤ R := le_sup_left
  have hV1leR : fd.V1 ≤ R := le_sup_right
  have hXleR : X ≤ R := hXleE.trans hEleR
  let O : Subgroup R := pPrimeCore 2 R
  let : O.Normal := by dsimp [O]; infer_instance
  let q : R →* R ⧸ O := QuotientGroup.mk' O
  let ER : Subgroup R := E.subgroupOf R
  let XR : Subgroup R := X.subgroupOf R
  let VR : Subgroup R := fd.V1.subgroupOf R
  let Ebar : Subgroup (R ⧸ O) := ER.map q
  let Xbar : Subgroup (R ⧸ O) := XR.map q
  let Vbar : Subgroup (R ⧸ O) := VR.map q
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥R))
  have hVRK : IsKleinFour VR := isKleinFour_subgroupOf hV1leR fd.V1_klein
  have hVbarK : IsKleinFour Vbar := by
    simpa [Vbar] using isKleinFour_map_quotient_of_odd_kernel O VR hOodd hVRK
  have hVbar2 : IsPGroup 2 Vbar := by
    apply IsPGroup.of_card (n := 2)
    rw [hVbarK.card_four]
    norm_num
  have hXRcyc : IsCyclic XR := isCyclic_subgroupOf hXleR hXcyc
  have hXbarcyc : IsCyclic Xbar := by
    let fX : XR →* Xbar :=
      (q.comp XR.subtype).codRestrict Xbar (fun x =>
        Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
    have hfX : Function.Surjective fX := by
      intro y
      rcases Subgroup.mem_map.mp y.2 with ⟨x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      exact Subtype.ext hxy
    let : IsCyclic XR := hXRcyc
    exact isCyclic_of_surjective fX hfX
  have hXRp : IsPGroup od.p XR :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXleR).symm
  have hXbarp : IsPGroup od.p Xbar := IsPGroup.map hXRp q
  have hpodd : Odd od.p :=
    od.p_prime.odd_of_ne_two (firstCase_oriented_p_odd c od)
  have hXbarodd : Odd (Nat.card Xbar) := by
    rcases hXbarp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hpodd.pow
  have hVbarcent : Vbar ≤ Subgroup.centralizer (Xbar : Set (R ⧸ O)) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases Subgroup.mem_map.mp hv with ⟨vR, hvR, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨xR, hxR, rfl⟩
    have hvG : (vR : G) ∈ fd.V1 := Subgroup.mem_subgroupOf.mp hvR
    have hxG : (xR : G) ∈ X := Subgroup.mem_subgroupOf.mp hxR
    have hcomm : (xR : G) * (vR : G) = (vR : G) * (xR : G) :=
      ((Subgroup.mem_centralizer_iff.mp (hXcent hxG)) (vR : G) hvG).symm
    have hcommR : xR * vR = vR * xR := Subtype.ext hcomm
    simpa using congrArg q hcommR
  have hEnormR : IsNormalIn E R := by
    refine ⟨hEleR, ?_⟩
    intro r hr e he
    exact (componentLayerOf_isNormalIn M).2 r (hRleM hr) e he
  have hERnormal : ER.Normal :=
    (Subgroup.normal_subgroupOf_iff hEleR).2
      (fun h k hh hk => hEnormR.2 k hk h hh)
  have hEne : E ≠ ⊥ := by
    intro hbot
    have hVbot : fd.V2 = ⊥ := le_bot_iff.mp (by simpa [E, hbot] using hV2)
    have hcard : Nat.card fd.V2 = 4 := fd.V2_klein.card_four
    rw [hVbot] at hcard
    norm_num at hcard
  have hERne : ER ≠ ⊥ := subgroupOf_ne_bot hEleR hEne
  have hEperf : Group.IsPerfect E := componentLayerOf_isPerfect_for_layerASeven M
  let eER : ER ≃* E := Subgroup.subgroupOfEquivOfLe hEleR
  have hERperf : Group.IsPerfect ER := by
    let : Group.IsPerfect E := hEperf
    exact Group.IsPerfect.ofSurjective
      (f := eER.symm.toMonoidHom) eER.symm.surjective
  have hOsolv : IsSolvable O := odd_order_theorem O hOodd
  have hEbarData : Ebar ≠ ⊥ ∧ Group.IsPerfect Ebar ∧
      Ebar.IsSubnormal := by
    have h := perfect_subnormal_image_le_normal_odd_index
      ER hERperf hERne hERnormal.isSubnormal O hOsolv
      (⊤ : Subgroup (R ⧸ O)) (by infer_instance) (by simp)
    simpa [Ebar] using ⟨h.1, h.2.1, h.2.2.1⟩
  have hXbarleEbar : Xbar ≤ Ebar := by
    exact Subgroup.map_mono (fun x hx => hXleE (Subgroup.mem_subgroupOf.mp hx))
  have hOmap_norm : ∀ e : G, e ∈ E →
      ∀ x : G, x ∈ O.map R.subtype → e * x * e⁻¹ ∈ O.map R.subtype := by
    intro e he x hx
    rcases Subgroup.mem_map.mp hx with ⟨o, ho, rfl⟩
    have heR : e ∈ R := hEleR he
    have hc := (inferInstance : O.Normal).conj_mem o ho (⟨e, heR⟩ : R)
    exact Subgroup.mem_map.mpr
      ⟨(⟨e, heR⟩ : R) * o * (⟨e, heR⟩ : R)⁻¹, hc, rfl⟩
  have hOcapE : O.map R.subtype ⊓ E ≤
      (pPrimeCore 2 (↥E)).map E.subtype :=
    firstCase_cyclic_componentLayer_ker_le_oddCore R E hEleR hOmap_norm
  have hXcapOE : X ⊓ (pPrimeCore 2 (↥E)).map E.subtype = ⊥ :=
    firstCase_cyclic_layer_inverted_inf_oddCore_eq_bot
      od fd hMmax hV2 hXleE hXne hXp hXinv
  have hXbarne : Xbar ≠ ⊥ := by
    intro hbot
    have hXRleO : XR ≤ O := by
      have hle : XR ≤ q.ker := (Subgroup.map_eq_bot_iff XR).mp hbot
      simpa [q, QuotientGroup.ker_mk'] using hle
    have hXleOE : X ≤ (pPrimeCore 2 (↥E)).map E.subtype := by
      intro x hx
      have hxR : x ∈ R := hXleR hx
      have hxXR : (⟨x, hxR⟩ : R) ∈ XR := Subgroup.mem_subgroupOf.mpr hx
      have hxO : (⟨x, hxR⟩ : R) ∈ O := hXRleO hxXR
      have hxOmap : x ∈ O.map R.subtype :=
        Subgroup.mem_map.mpr ⟨⟨x, hxR⟩, hxO, rfl⟩
      exact hOcapE ⟨hxOmap, hXleE hx⟩
    have hXbot : X = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hxinf : x ∈ X ⊓ (pPrimeCore 2 (↥E)).map E.subtype :=
        ⟨hx, hXleOE hx⟩
      rw [hXcapOE] at hxinf
      exact Subgroup.mem_bot.mp hxinf
    exact hXne hXbot
  have hA7Q : Nonempty ((R ⧸ O) ≃* alternatingGroup (Fin 7)) := by
    rcases hDR with ⟨_hSylow, htwo⟩ | ⟨_hSylow, hA7⟩ |
      ⟨_hSylow, K, hK, L, hLnormal, hLindex, hLmodel⟩
    · have hXbar2 : IsPGroup 2 Xbar := htwo.to_subgroup Xbar
      have hpne2 : od.p ≠ 2 := firstCase_oriented_p_odd c od
      have hcop : Nat.Coprime (Nat.card Xbar) (Nat.card Xbar) :=
        IsPGroup.coprime_card_of_ne od.p 2 hpne2
          Xbar Xbar hXbarp hXbar2
      have hcard1 : Nat.card Xbar = 1 :=
        hcop.eq_one_of_dvd (dvd_refl (Nat.card Xbar))
      have hcardpos : 1 < Nat.card Xbar :=
        (Subgroup.one_lt_card_iff_ne_bot Xbar).2 hXbarne
      omega
    · exact hA7
    · have hVbarleL : Vbar ≤ L :=
        subgroup_le_of_isPGroup_coindex_odd L hLnormal hLindex Vbar hVbar2
      have hEbarleL : Ebar ≤ L := by
        have h := perfect_subnormal_image_le_normal_odd_index
          ER hERperf hERne hERnormal.isSubnormal O hOsolv
          L hLnormal hLindex
        simpa [Ebar, O] using h.2.2.2
      have hXbarleL : Xbar ≤ L := hXbarleEbar.trans hEbarleL
      let XL : Subgroup L := Xbar.subgroupOf L
      let VL : Subgroup L := Vbar.subgroupOf L
      have hXLcyc : IsCyclic XL := isCyclic_subgroupOf hXbarleL hXbarcyc
      have hXLne : XL ≠ ⊥ := subgroupOf_ne_bot hXbarleL hXbarne
      have hXLodd : Odd (Nat.card XL) := subgroupOf_odd_card hXbarleL hXbarodd
      have hVLK : IsKleinFour VL := isKleinFour_subgroupOf hVbarleL hVbarK
      have hVLcent : VL ≤ Subgroup.centralizer (XL : Set L) :=
        centralizer_subgroupOf_le hXbarleL hVbarleL hVbarcent
      exact False.elim (no_kleinFour_cyclic_in_linear_model
        XL VL hXLcyc hXLne hXLodd hVLK hVLcent K hK hLmodel)
  obtain ⟨eQ⟩ := hA7Q
  have hEbarNormal : Ebar.Normal := by
    simpa [Ebar] using hERnormal.map q (QuotientGroup.mk'_surjective O)
  let E7 : Subgroup (alternatingGroup (Fin 7)) := Ebar.map eQ.toMonoidHom
  have hE7normal : E7.Normal := hEbarNormal.map eQ.toMonoidHom eQ.surjective
  have hE7ne : E7 ≠ ⊥ := by
    intro hbot
    apply hEbarData.1
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := Ebar) (f := eQ.toMonoidHom) eQ.injective).mp hbot
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
  have hE7top : E7 = ⊤ :=
    (@IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ E7 hE7normal).resolve_left hE7ne
  have hEbarTop : Ebar = ⊤ := by
    apply (Subgroup.map_injective (f := eQ.toMonoidHom) eQ.injective)
    simpa [E7] using hE7top
  let fE : E →* R ⧸ O := q.comp (Subgroup.inclusion hEleR)
  have hfErange : fE.range = Ebar := by
    change (q.comp (Subgroup.inclusion hEleR)).range = Ebar
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hfEsurj : Function.Surjective fE := by
    rw [← MonoidHom.range_eq_top, hfErange, hEbarTop]
  let OE : Subgroup E := pPrimeCore 2 E
  have hker_le : fE.ker ≤ OE := by
    intro e he
    have hq1 : q (Subgroup.inclusion hEleR e) = 1 :=
      MonoidHom.mem_ker.mp he
    have heO : Subgroup.inclusion hEleR e ∈ O :=
      (QuotientGroup.eq_one_iff (N := O) (Subgroup.inclusion hEleR e)).mp hq1
    have heOmap : (e : G) ∈ O.map R.subtype :=
      Subgroup.mem_map.mpr
        ⟨Subgroup.inclusion hEleR e, heO, Subgroup.coe_inclusion hEleR e⟩
    have heOEMap : (e : G) ∈ (pPrimeCore 2 (↥E)).map E.subtype :=
      hOcapE ⟨heOmap, e.2⟩
    rcases Subgroup.mem_map.mp heOEMap with ⟨y, hy, hye⟩
    have hyeq : y = e := Subtype.ext hye
    simpa [OE, hyeq] using hy
  let OEbar : Subgroup (R ⧸ O) := OE.map fE
  have hOEbarNormal : OEbar.Normal :=
    (inferInstance : OE.Normal).map fE hfEsurj
  have hOEbarOdd : Odd (Nat.card OEbar) :=
    Odd.of_dvd_nat
      (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥E)))
      (Subgroup.card_map_dvd OE fE)
  have hOEbarBot : OEbar = ⊥ := by
    let : IsSimpleGroup (R ⧸ O) := eQ.isSimpleGroup
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ OEbar hOEbarNormal with hbot | htop
    · exact hbot
    · exfalso
      have hQodd : Odd (Nat.card (R ⧸ O)) := by simpa [htop] using hOEbarOdd
      have hQcard : Nat.card (R ⧸ O) = 2520 := by
        rw [Nat.card_congr eQ.toEquiv, nat_card_alternatingGroup]
        norm_num
      rw [hQcard] at hQodd
      norm_num at hQodd
  have hOE_le_ker : OE ≤ fE.ker :=
    (Subgroup.map_eq_bot_iff OE).mp (by simpa [OEbar] using hOEbarBot)
  have hker : fE.ker = OE := le_antisymm hker_le hOE_le_ker
  let eKer : E ⧸ OE ≃* E ⧸ fE.ker :=
    QuotientGroup.quotientMulEquivOfEq hker.symm
  let eSurj : E ⧸ fE.ker ≃* R ⧸ O :=
    QuotientGroup.quotientKerEquivOfSurjective fE hfEsurj
  have hA7E : Nonempty (E ⧸ pPrimeCore 2 E ≃* alternatingGroup (Fin 7)) :=
    ⟨(eKer.trans eSurj).trans eQ⟩
  exact ⟨hU, fd, Q, M, X, hMmax, hMN, hSM, hV2, hXleE, hXne,
    hXcyc, hXp, hXleP, hXinv, hXcent, hDE, hA7E⟩

/-- In the cyclic two-core subcase, the quotient of the selected component
layer by its odd core is `A₇`; the full inverted odd and Klein-four package
is retained for the subsequent A₇ calculations. -/
public theorem firstCase_cyclic_layer_quotient_isASeven
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ od : FirstCaseOrientedPrimeData c,
      ∃ hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B,
        ∃ fd : FirstCaseFourData c od.d,
          ∃ Q : Sylow od.p ↥od.d.bg.B,
            ∃ M : Subgroup G, ∃ X : Subgroup G,
              IsCoatom M ∧
                Subgroup.normalizer
                  (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M ∧
                  (c.S : Subgroup G) ≤ M ∧
                    fd.V2 ≤ componentLayerOf M ∧
                      X ≤ componentLayerOf M ∧ X ≠ ⊥ ∧ IsCyclic X ∧
                        IsPGroup od.p X ∧
                        X ≤ qCoreOf od.d.bg.U od.p ∧
                        BenderGlauberman.IsInvertedBy od.d.bg.t2 X ∧
                          X ≤ Subgroup.centralizer (fd.V1 : Set G) ∧
                            IsDGroup (↥(componentLayerOf M)) ∧
                              Nonempty ((componentLayerOf M) ⧸
                                pPrimeCore 2 (componentLayerOf M) ≃*
                                  alternatingGroup (Fin 7)) := by
  classical
  have hHhat : c.Hhat = c.H := cyclicCore_hhat_eq hmin c hcyclic
  obtain ⟨od⟩ := exists_firstCaseOrientedPrimeData hmin c hfirst hHhat
  obtain ⟨hU, fd, Q, M, X, hMmax, hMN, hSM, hV2, hXleE, hXne,
    hXcyc, hXp, hXleP, hXinv, hXcent, hDE, hA7E⟩ :=
    firstCase_cyclic_layer_quotient_isASeven_of_od hmin c hfirst hcyclic od
  exact ⟨od, hU, fd, Q, M, X, hMmax, hMN, hSM, hV2, hXleE, hXne,
    hXcyc, hXp, hXleP, hXinv, hXcent, hDE, hA7E⟩

/-- In the cyclic two-core subcase the oriented prime of the given
oriented prime data is forced to be `3`. -/
public theorem firstCase_cyclic_oriented_prime_eq_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
    (od : FirstCaseOrientedPrimeData c) :
    od.p = 3 := by
  obtain ⟨_hU, fd, _Q, M, X, hMmax, _hMN, _hSM, hV2,
    hXleE, hXne, _hXcyc, hXp, _hXleP, hXinv, hXcent, _hDE, hA7⟩ :=
    firstCase_cyclic_layer_quotient_isASeven_of_od hmin c hfirst hcyclic od
  exact firstCase_cyclic_oriented_prime_eq_three_of_aSeven_layer
    hmin c hfirst hcyclic od fd M X hMmax hV2 hXleE hXne hXp hXinv hXcent hA7

/-- In the cyclic two-core subcase the forced A₇ layer quotient implies
that the oriented prime is `3`. -/
public theorem firstCase_cyclic_layer_p_eq_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ od : FirstCaseOrientedPrimeData c, od.p = 3 := by
  obtain ⟨od⟩ :=
    firstCase_cyclic_layer_quotient_isASeven hmin c hfirst hcyclic
  exact ⟨od, firstCase_cyclic_oriented_prime_eq_three
    hmin c hfirst hcyclic od⟩

end CFSG.GorensteinWalter
