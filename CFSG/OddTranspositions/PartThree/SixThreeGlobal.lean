module

public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.GroupTheory.PCore.SolvableRadical

import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Goldschmidt75.OddCore
import CFSG.OddTranspositions.SolvableTriangles
import CFSG.OddTranspositions.InvertMember
import CFSG.Timmesfeld.Bridge.RootClosureRankOne
import CFSG.Quasithin.Background.A3Structure36AQuasi
import CFSG.LocalAnalysis.WeakClosure81.FiveNineTwo
import CFSG.LocalAnalysis.ComponentClassification.SolvableRadical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43
import CFSG.Assembly.QuasithinDefs
import CFSG.CGT.Timmesfeld75.Cfg214Gen
import CFSG.CGT.Timmesfeld75.L2Real
import CFSG.Foundations
import CFSG.Goldschmidt75.Basic
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LargeExtraspecial.S9TIXC
import CFSG.LocalAnalysis.ComponentClassification.FixedCentralPreimage
import CFSG.LocalAnalysis.ComponentClassification.InvolutionDiagonal
import CFSG.LocalAnalysis.ComponentClassification.OddKernelNormalizers
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
import CFSG.LocalAnalysis.WeakClosure81.FiveDefs
import CFSG.LocalAnalysis.WeakClosure81.SevenThree
import CFSG.OddTranspositions.Blocks
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
import CFSG.Timmesfeld.Bridge.NoPolarConnected
import CFSG.Timmesfeld.Bridge.RootSets
import CFSG.Timmesfeld.Bridge.RootSetsGate
import CFSG.Timmesfeld.Bridge.RootSetsSyl
import CFSG.Timmesfeld.Bridge.RootSetsThird
import CFSG.Timmesfeld.Exceptional.CaseTwo

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

theorem isSolvable_comap_pCore_two_oddCore (G : Type*) [Group G] [Finite G] :
    Group.IsSolvable
      ((CFSG.pCore 2 (G ⧸ CFSG.oddCore G)).comap
        (QuotientGroup.mk' (CFSG.oddCore G))) := by
  let N := CFSG.oddCore G
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let Q : Subgroup (G ⧸ N) := CFSG.pCore 2 (G ⧸ N)
  let K : Subgroup G := Q.comap π
  change Group.IsSolvable K
  have hNodd : Odd (Nat.card N) := by
    change Odd (Nat.card (CFSG.Open.goldschmidtOddCore G))
    exact CFSG.Goldschmidt75.odd_card_oddCore
  have hNsolv : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  have hNleK : N ≤ K := by
    intro x hx
    change x ∈ Q.comap π
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Q.one_mem
  let ψ : K →* Q :=
    { toFun := fun x => ⟨π x, x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hψker : ψ.ker = N.subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      simpa [ψ, π, QuotientGroup.mk'_apply] using congrArg Subtype.val h
    · intro hx
      apply Subtype.ext
      simpa [ψ, π, QuotientGroup.mk'_apply] using (QuotientGroup.eq_one_iff (x : G)).mpr hx
  have hNsub : Group.IsSolvable (N.subgroupOf K) :=
    @Group.isSolvable_of_isSolvable_injective _ _ _ _
      (Subgroup.subgroupOfEquivOfLe hNleK).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hNleK).injective hNsolv
  have hQnil : Group.IsNilpotent Q :=
    (CFSG.pCore_isPGroup (p := 2) (G := G ⧸ N)).isNilpotent
  have hQsolv : Group.IsSolvable Q := @IsNilpotent.to_isSolvable Q _ hQnil
  exact @Group.isSolvable_of_ker_le_range _ _ _ _ _ _
    (N.subgroupOf K).subtype ψ
    (by rw [hψker, Subgroup.range_subtype]) hNsub hQsolv

theorem isTriangle_subgroup {G : Type*} [Group G] {D : Set G} {X : Subgroup G}
    {u w v : G} (huX : u ∈ X) (hwX : w ∈ X) (hvX : v ∈ X)
    (htri : IsTriangle D u w v) :
    IsTriangle {x : X | (x : G) ∈ D} ⟨u, huX⟩ ⟨w, hwX⟩ ⟨v, hvX⟩ := by
  refine ⟨htri.1, htri.2.1, htri.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro h
    exact htri.2.2.2.1 (congrArg Subtype.val h)
  · exact Subtype.ext htri.2.2.2.2.1
  · intro h
    exact htri.2.2.2.2.2.1 (congrArg Subtype.val h)
  · intro h
    exact htri.2.2.2.2.2.2 (congrArg Subtype.val h)

theorem orderOf_mul_eq_four_of_solvable_subgroup {G : Type*} [Group G] [Finite G] {D : Set G}
    (hD : IsOddTransp D) (hN : IsNormalSet D) {X : Subgroup G}
    (hsolv : Group.IsSolvable X) {u w v : G} (huX : u ∈ X) (hwX : w ∈ X) (hvX : v ∈ X)
    (htri : IsTriangle D u w v) : orderOf (u * v * w) = 4 := by
  let DX : Set X := {x | (x : G) ∈ D}
  have hoddX : IsOddTransp DX := hD.preimage X
  have hNX : IsNormalSet DX := fun g x hx => by
    simpa [DX] using hN (g : G) (x : G) hx
  have htriX : IsTriangle DX ⟨u, huX⟩ ⟨w, hwX⟩ ⟨v, hvX⟩ :=
    isTriangle_subgroup huX hwX hvX htri
  rcases htriX.orderOf_cases hoddX hNX with h1 | h4 | h3
  · exact absurd h1 (not_firstKind hNX hoddX hsolv htriX)
  · rw [← Subgroup.orderOf_coe
      (a := (⟨u, huX⟩ * ⟨v, hvX⟩ * ⟨w, hwX⟩ : X))] at h4
    simpa using h4
  · exact absurd h3 (not_thirdKind hNX hoddX hsolv htriX)

theorem not_isThirdKind_of_solvable_subgroup {G : Type*} [Group G] [Finite G] {D : Set G}
    (hD : IsOddTransp D) (hN : IsNormalSet D) {X : Subgroup G}
    (hsolv : Group.IsSolvable X) {u w v : G} (huX : u ∈ X) (hwX : w ∈ X) (hvX : v ∈ X)
    (htri : IsTriangle D u w v) : ¬ IsThirdKind u w v := by
  intro h3
  let DX : Set X := {x | (x : G) ∈ D}
  have hoddX : IsOddTransp DX := hD.preimage X
  have hNX : IsNormalSet DX := fun g x hx => by
    simpa [DX] using hN (g : G) (x : G) hx
  have htriX : IsTriangle DX ⟨u, huX⟩ ⟨w, hwX⟩ ⟨v, hvX⟩ :=
    isTriangle_subgroup huX hwX hvX htri
  have h3X : IsThirdKind (⟨u, huX⟩ : X) ⟨w, hwX⟩ ⟨v, hvX⟩ := by
    obtain ⟨n, hn, hn1, hord⟩ := h3
    refine ⟨n, hn, hn1, ?_⟩
    rw [← Subgroup.orderOf_coe
      (a := (⟨u, huX⟩ * ⟨v, hvX⟩ * ⟨w, hwX⟩ : X))]
    simpa using hord
  exact not_thirdKind hNX hoddX hsolv htriX h3X

theorem commute_pCore_of_no_distinct_conj {G : Type} [Group G] [Finite G] {D : Set G}
    (hS : Setup G D) {d : G} (hd : d ∈ D)
    (hiso : ∀ k ∈ (CFSG.pCore 2 (G ⧸ CFSG.oddCore G)).comap
        (QuotientGroup.mk' (CFSG.oddCore G)),
      k * d * k⁻¹ = d ∨ ¬ Commute (k * d * k⁻¹) d) :
    ∀ q ∈ CFSG.pCore 2 (G ⧸ CFSG.oddCore G),
      Commute (QuotientGroup.mk' (CFSG.oddCore G) d) q := by
  let N := CFSG.oddCore G
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let Q : Subgroup (G ⧸ N) := CFSG.pCore 2 (G ⧸ N)
  let K : Subgroup G := Q.comap π
  have hKnormal : K.Normal := Subgroup.Normal.comap inferInstance π
  have hisoK : ∀ k ∈ K, k * d * k⁻¹ = d ∨ ¬ Commute (k * d * k⁻¹) d := by
    simpa [K, Q, N, π] using hiso
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup
  intro q hq
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective N q
  have hkK : k ∈ K := by
    change k ∈ Q.comap π
    rw [Subgroup.mem_comap]
    rw [hk]
    exact hq
  have hconjD : k * d * k⁻¹ ∈ D := hS.conj_mem k hd
  have hcK : d * (k * d * k⁻¹) ∈ K := by
    have h1 : d * k * d⁻¹ ∈ K := hKnormal.conj_mem k hkK d
    have h2 : (d * k * d⁻¹) * k⁻¹ = d * (k * d * k⁻¹) := by
      rw [hS.oddT.inv_eq hd]
      group
    rw [← h2]
    exact K.mul_mem h1 (K.inv_mem hkK)
  have hcodd : Odd (orderOf (d * (k * d * k⁻¹))) := by
    rcases hisoK k hkK with heq | hnc
    · rw [heq, hS.oddT.mul_self_eq_one hd, orderOf_one]
      exact odd_one
    · exact hS.oddT.odd_of_not_commute hd hconjD (fun h => hnc h.symm)
  have hπcQ : π (d * (k * d * k⁻¹)) ∈ Q := hcK
  have hoddπc : Odd (orderOf (π (d * (k * d * k⁻¹)))) :=
    hcodd.of_dvd_nat (orderOf_map_dvd π _)
  have hπc1 : π (d * (k * d * k⁻¹)) = 1 :=
    CFSG.Timmesfeld.Bridge.OddTransp.eq_one_of_isPGroup_of_odd hQ2 hπcQ hoddπc
  have hd2 : π d * π d = 1 := by
    rw [← map_mul, hS.oddT.mul_self_eq_one hd, map_one]
  have hcomm : Commute (π d) (π k) := by
    show π d * π k = π k * π d
    have h1 : π d * π k * π d * (π k)⁻¹ = 1 := by
      simpa [map_mul, mul_assoc] using hπc1
    calc π d * π k = π d * π k * 1 := (mul_one _).symm
      _ = π d * π k * (π d * π d) := by rw [hd2]
      _ = (π d * π k * π d * (π k)⁻¹) * (π k * π d) := by group
      _ = 1 * (π k * π d) := by rw [h1]
      _ = π k * π d := one_mul _
  rw [← hk]
  exact hcomm

theorem solvableRadical_map_le_center_of_no_distinct_conj {G : Type} [Group G] [Finite G]
    {D : Set G} (hS : Setup G D) {d : G} (hd : d ∈ D)
    (hiso : ∀ k ∈ (CFSG.pCore 2 (G ⧸ CFSG.oddCore G)).comap
        (QuotientGroup.mk' (CFSG.oddCore G)),
      k * d * k⁻¹ = d ∨ ¬ Commute (k * d * k⁻¹) d) :
    (CFSG.solvableRadical G).map (QuotientGroup.mk' (CFSG.oddCore G)) ≤
      Subgroup.center (G ⧸ CFSG.oddCore G) := by
  let N := CFSG.oddCore G
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let Q : Subgroup (G ⧸ N) := CFSG.pCore 2 (G ⧸ N)
  have hO : CFSG.oddCore (G ⧸ N) = ⊥ := by
    change CFSG.Open.goldschmidtOddCore (G ⧸ CFSG.Open.goldschmidtOddCore G) = ⊥
    exact CFSG.Goldschmidt75.oddCore_quotient_eq_bot
  have hcent_d : ∀ q ∈ Q, Commute (π d) q :=
    commute_pCore_of_no_distinct_conj hS hd hiso
  have hcent_D : ∀ e ∈ D, ∀ q ∈ Q, Commute (π e) q := by
    intro e he q hq
    obtain ⟨g, hg⟩ := isConj_iff.mp (hS.isConj hd he)
    have hq' : (π g)⁻¹ * q * π g ∈ Q := by
      have h := (inferInstance : Q.Normal).conj_mem q hq (π g)⁻¹
      rw [inv_inv] at h
      exact h
    have hdcomm := hcent_d _ hq'
    have hconj := hdcomm.conj (π g)
    rw [← hg]
    simpa [map_mul, mul_assoc] using hconj
  have hQcenter : Q ≤ Subgroup.center (G ⧸ N) := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro g
    have hgen : Subgroup.closure (π '' D) = ⊤ := by
      rw [← MonoidHom.map_closure, hS.gen, Subgroup.map_top_of_surjective]
      exact QuotientGroup.mk'_surjective N
    have hg : g ∈ Subgroup.closure (π '' D) := by
      rw [hgen]
      exact Subgroup.mem_top g
    have hcomm := CFSG.Timmesfeld.Bridge.Asc72.commute_of_mem_closure
      (S := π '' D) (T := {q}) (fun x hx y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst y
        obtain ⟨e, he, rfl⟩ := hx
        exact hcent_D e he q hq) hg (Subgroup.subset_closure (Set.mem_singleton q))
    exact hcomm.eq
  have hF : CFSG.fittingSubgroup (G ⧸ N) ≤ Subgroup.center (G ⧸ N) := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    by_cases hp : p.1.1 = 2
    · rw [hp]
      exact hQcenter
    · have hodd : Odd (Nat.card (CFSG.pCore p.1.1 (G ⧸ N))) := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp
          (CFSG.pCore_isPGroup (p := p.1.1) (G := G ⧸ N))
        rw [hn]
        exact Odd.pow ((Nat.prime_of_mem_primeFactors p.1.2).odd_of_ne_two hp)
      have hle : CFSG.pCore p.1.1 (G ⧸ N) ≤ CFSG.oddCore (G ⧸ N) :=
        le_sSup ⟨CFSG.pCore_normal, hodd⟩
      rw [hO, le_bot_iff] at hle
      rw [hle]
      exact bot_le
  have hHsolv : CFSG.solvableRadical (G ⧸ N) ≤ Subgroup.center (G ⧸ N) :=
    CFSG.Quasithin.A36A.solvableRadical_le_center hF
  have hmap : (CFSG.solvableRadical G).map π ≤ CFSG.solvableRadical (G ⧸ N) := by
    have hRsolv : Group.IsSolvable (CFSG.solvableRadical G) :=
      CFSG.Quasithin.A3.solvableRadical_isSolvable
    have hsolv : Group.IsSolvable ((CFSG.solvableRadical G).map π) :=
      @Group.isSolvable_of_surjective _ _ _ _ _
        (π.subgroupMap_surjective (CFSG.solvableRadical G)) hRsolv
    have hRnorm : (CFSG.solvableRadical G).Normal :=
      Subgroup.sSup_normal _ fun _ hN => hN.1
    have hnorm : ((CFSG.solvableRadical G).map π).Normal :=
      hRnorm.map π (QuotientGroup.mk'_surjective N)
    exact CFSG.Quasithin.A3.le_solvableRadical hnorm hsolv
  simpa [N, π] using hmap.trans hHsolv

theorem isSolvable_closure_three_of_mem_sup {G : Type} [Group G] [Finite G]
    {d e v : G} (hd2 : d * d = 1) (he2 : e * e = 1)
    (hv : v ∈ (CFSG.pCore 2 (G ⧸ CFSG.oddCore G)).comap
        (QuotientGroup.mk' (CFSG.oddCore G)) ⊔
        Subgroup.closure ({d, e} : Set G)) :
    Group.IsSolvable (Subgroup.closure ({d, e, v} : Set G)) := by
  let K : Subgroup G := (CFSG.pCore 2 (G ⧸ CFSG.oddCore G)).comap
    (QuotientGroup.mk' (CFSG.oddCore G))
  let H : Subgroup G := Subgroup.closure ({d, e} : Set G)
  have hH : Group.IsSolvable H := by
    have hcl : Subgroup.closure ({d, e} : Set G) = Subgroup.zpowers d ⊔ Subgroup.zpowers e := by
      rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
        ← Subgroup.zpowers_eq_closure]
    rw [show H = Subgroup.zpowers d ⊔ Subgroup.zpowers e from hcl]
    exact CFSG.LocalAnalysis.WeakClosure81.isSolvable_sup_zpowers_of_mul_self_eq_one hd2 he2
  have hK : Group.IsSolvable K := isSolvable_comap_pCore_two_oddCore G
  have hNormK : K.Normal := Subgroup.Normal.comap inferInstance _
  have hKH : Group.IsSolvable (K ⊔ H : Subgroup G) :=
    @CFSG.ComponentClassification.SolvableRadical.solvable_sup G _ K H hNormK hK hH
  have hvKH : v ∈ K ⊔ H := by
    simpa [K, H] using hv
  have hle : Subgroup.closure ({d, e, v} : Set G) ≤ K ⊔ H := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact hvKH
  exact @Group.isSolvable_of_isSolvable_injective _ _ _ _
    (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle) hKH

theorem oddCore_le_center_of_commuting_K_conj {G : Type} [Group G] [Finite G] {D : Set G}
    (hS : Setup G D) {d e v : G} (hd : d ∈ D) (he : e ∈ D) (hvD : v ∈ D)
    (hne : d ≠ v) (hcomm : Commute d v)
    (hvconj : ∃ k ∈ (CFSG.pCore 2 (G ⧸ CFSG.oddCore G)).comap
        (QuotientGroup.mk' (CFSG.oddCore G)), v = k * d * k⁻¹)
    (hde_gt : 3 < orderOf (d * e))
    (hoddπde : Odd (orderOf (QuotientGroup.mk' (CFSG.oddCore G) d *
      QuotientGroup.mk' (CFSG.oddCore G) e)))
    (h5 : 5 ≤ orderOf (QuotientGroup.mk' (CFSG.oddCore G) d *
      QuotientGroup.mk' (CFSG.oddCore G) e)) :
    CFSG.oddCore G ≤ Subgroup.center G := by
  let N := CFSG.oddCore G
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let Q : Subgroup (G ⧸ N) := CFSG.pCore 2 (G ⧸ N)
  let σ : G →* (G ⧸ N) ⧸ Q := (QuotientGroup.mk' Q).comp π
  have hd2 : d * d = 1 := hS.oddT.mul_self_eq_one hd
  have he2 : e * e = 1 := hS.oddT.mul_self_eq_one he
  have hv2 : v * v = 1 := hS.oddT.mul_self_eq_one hvD
  have hde_nc : ¬ Commute d e := by
    intro hc
    have hsq : (d * e) ^ 2 = 1 := by
      rw [pow_two]
      calc d * e * (d * e) = d * (e * d) * e := by group
        _ = d * (d * e) * e := by rw [← hc.eq]
        _ = 1 := by rw [← mul_assoc, hd2, one_mul, he2]
    have hle : orderOf (d * e) ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hsq)
    omega
  obtain ⟨k, hkK, hv_eq⟩ := hvconj
  have hkπQ : π k ∈ Q := by
    simpa [N, π, Q] using hkK
  have hσk : σ k = 1 := by
    change QuotientGroup.mk' Q (π k) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hkπQ
  have hσv : σ v = σ d := by
    rw [hv_eq]
    simp [map_mul, hσk]
  have hσve : σ (v * e) = σ (d * e) := by
    rw [map_mul, map_mul, hσv]
  have horderσ : orderOf (σ (d * e)) = orderOf (π d * π e) := by
    have hσeq : σ (d * e) = QuotientGroup.mk' Q (π d * π e) := by
      simp [σ, map_mul]
    rw [hσeq]
    exact CFSG.Timmesfeld.Bridge.RootClosure.orderOf_mk_eq_of_odd
      (CFSG.pCore_isPGroup (p := 2) (G := G ⧸ N)) hoddπde
  have h5σ : 5 ≤ orderOf (σ (v * e)) := by
    rw [hσve, horderσ]
    exact h5
  have hve_nc : ¬ Commute v e := by
    intro hc
    have hsq : (v * e) ^ 2 = 1 := by
      rw [pow_two]
      calc v * e * (v * e) = v * (e * v) * e := by group
        _ = v * (v * e) * e := by rw [← hc.eq]
        _ = 1 := by rw [← mul_assoc, hv2, one_mul, he2]
    have hle : orderOf (v * e) ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hsq)
    have hleσ : orderOf (σ (v * e)) ≤ 2 :=
      (Nat.le_of_dvd (orderOf_pos _) (orderOf_map_dvd σ (v * e))).trans hle
    omega
  have htri : IsTriangle D d e v :=
    ⟨hd, hvD, he, hne, hcomm, hde_nc, hve_nc⟩
  have hv_sup : v ∈ (CFSG.pCore 2 (G ⧸ CFSG.oddCore G)).comap
      (QuotientGroup.mk' (CFSG.oddCore G)) ⊔ Subgroup.closure ({d, e} : Set G) := by
    rw [hv_eq]
    have hkd : k * d * k⁻¹ = (k * d * k⁻¹ * d⁻¹) * d := by group
    rw [hkd]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_)
      (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
    have hKnormal : ((CFSG.pCore 2 (G ⧸ CFSG.oddCore G)).comap
        (QuotientGroup.mk' (CFSG.oddCore G))).Normal :=
      Subgroup.Normal.comap inferInstance _
    have hdk : d * k⁻¹ * d⁻¹ ∈ (CFSG.pCore 2 (G ⧸ CFSG.oddCore G)).comap
        (QuotientGroup.mk' (CFSG.oddCore G)) :=
      hKnormal.conj_mem k⁻¹ (Subgroup.inv_mem _ hkK) d
    have : k * d * k⁻¹ * d⁻¹ = k * (d * k⁻¹ * d⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hkK hdk
  have hXsolv : Group.IsSolvable (Subgroup.closure ({d, e, v} : Set G)) :=
    isSolvable_closure_three_of_mem_sup hd2 he2 hv_sup
  have hdX : d ∈ Subgroup.closure ({d, e, v} : Set G) := Subgroup.subset_closure (by simp)
  have heX : e ∈ Subgroup.closure ({d, e, v} : Set G) := Subgroup.subset_closure (by simp)
  have hvX : v ∈ Subgroup.closure ({d, e, v} : Set G) := Subgroup.subset_closure (by simp)
  have h4 : orderOf (d * v * e) = 4 :=
    orderOf_mul_eq_four_of_solvable_subgroup hS.oddT hS.normal hXsolv hdX heX hvX htri
  have hno : ∀ x ∈ D, x ∈ Subgroup.closure ({d, e} : Set G) →
      IsTriangle D d x v → ¬ IsThirdKind d x v := by
    intro x hxD hxH htri_x
    have hxX : x ∈ Subgroup.closure ({d, e, v} : Set G) :=
      Subgroup.closure_mono (by
        intro y hy
        rcases hy with rfl | rfl <;> simp) hxH
    exact not_isThirdKind_of_solvable_subgroup hS.oddT hS.normal hXsolv hdX hxX hvX htri_x
  have hNodd : Odd (Nat.card N) := by
    change Odd (Nat.card (CFSG.Open.goldschmidtOddCore G))
    exact CFSG.Goldschmidt75.odd_card_oddCore
  exact CFSG.OddTranspositions.normal_le_center_of_secondKindTriangle' hS htri h4 hno hde_gt
    (inferInstance : N.Normal) hNodd

open CFSG.Timmesfeld.Bridge.Asc72 in
theorem sixThree {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D) :
    (∀ d ∈ D, ∀ e ∈ D,
      orderOf ((d : G ⧸ CFSG.oddCore G) * (e : G ⧸ CFSG.oddCore G)) ∈ ({1, 2, 3} : Set ℕ)) ∨
    (CFSG.solvableRadical G).map (QuotientGroup.mk' (CFSG.oddCore G)) ≤
      Subgroup.center (G ⧸ CFSG.oddCore G) ∨
    CFSG.oddCore G ≤ Subgroup.center G := by
  classical
  by_cases h1 : ∀ d ∈ D, ∀ e ∈ D,
    orderOf ((d : G ⧸ CFSG.oddCore G) * (e : G ⧸ CFSG.oddCore G)) ∈ ({1, 2, 3} : Set ℕ)
  · exact Or.inl h1
  · push Not at h1
    obtain ⟨d, hd, e, he, hbad⟩ := h1
    let N := CFSG.oddCore G
    let π : G →* G ⧸ N := QuotientGroup.mk' N
    have hbadπ : orderOf (π d * π e) ∉ ({1, 2, 3} : Set ℕ) := by
      simpa [π, QuotientGroup.mk'_apply] using hbad
    have hdiv : orderOf (π d * π e) ∣ orderOf (d * e) := by
      simpa [map_mul] using orderOf_map_dvd π (d * e)
    have hodd_de : Odd (orderOf (d * e)) := by
      rcases hS.oddT.2 d hd e he with h2 | hodd
      · rcases (Nat.dvd_prime Nat.prime_two).mp (hdiv.trans h2) with h | h
        · exact absurd (by rw [h]; simp) hbadπ
        · exact absurd (by rw [h]; simp) hbadπ
      · exact hodd
    have hoddπde : Odd (orderOf (π d * π e)) := hodd_de.of_dvd_nat hdiv
    have h5 : 5 ≤ orderOf (π d * π e) := by
      have hne1 : orderOf (π d * π e) ≠ 1 := fun h => hbadπ (by rw [h]; simp)
      have hne2 : orderOf (π d * π e) ≠ 2 := fun h => hbadπ (by rw [h]; simp)
      have hne3 : orderOf (π d * π e) ≠ 3 := fun h => hbadπ (by rw [h]; simp)
      obtain ⟨m, hm⟩ := hoddπde
      omega
    have hgt3 : 3 < orderOf (d * e) :=
      lt_of_lt_of_le (by norm_num : 3 < 5)
        (h5.trans (Nat.le_of_dvd (orderOf_pos (d * e)) hdiv))
    by_cases hB : ∃ k ∈ (CFSG.pCore 2 (G ⧸ CFSG.oddCore G)).comap
        (QuotientGroup.mk' (CFSG.oddCore G)),
        k * d * k⁻¹ ≠ d ∧ Commute (k * d * k⁻¹) d
    · obtain ⟨k, hk, hne, hcomm⟩ := hB
      have hvD : k * d * k⁻¹ ∈ D := hS.conj_mem k hd
      exact Or.inr (Or.inr (oddCore_le_center_of_commuting_K_conj hS hd he hvD
        (Ne.symm hne) hcomm.symm ⟨k, hk, rfl⟩ hgt3 hoddπde h5))
    · have hiso : ∀ k ∈ (CFSG.pCore 2 (G ⧸ CFSG.oddCore G)).comap
          (QuotientGroup.mk' (CFSG.oddCore G)),
          k * d * k⁻¹ = d ∨ ¬ Commute (k * d * k⁻¹) d := by
        intro k hk
        by_cases hkd : k * d * k⁻¹ = d
        · exact Or.inl hkd
        · exact Or.inr fun hc => hB ⟨k, hk, hkd, hc⟩
      exact Or.inr (Or.inl (solvableRadical_map_le_center_of_no_distinct_conj hS hd hiso))
