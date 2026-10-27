module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S77Basic
public import CFSG.Holt.H78.Bridge
import CFSG.GroupTheory.AltCommuteSwap
import CFSG.RankThree.GF2n.Tim81.Recog.GR
import CFSG.RankThree.GF2n.Tim81.Sec6.Basic
import CFSG.RankThree.GF2n.Tim81.Sec6.L2Extra
import CFSG.Timmesfeld.Bridge.RootStructR2Incidence
import CFSG.Holt.General.MinimalCounterexample

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open MulAction CFSG.Holt CFSG.Holt.General CFSG.Holt.H78
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {n f : ℕ}

theorem Sec6Hyp.jOddCore_eq_bot (hS : Sec6Hyp M V) (Ω : Type) [MulAction G Ω] :
    jOddCore G Ω = ⊥ := by
  have hroot := hS.sec5.toRootHyp
  have hdisj : Disjoint (jOddCore G Ω) V := by
    rw [disjoint_iff]
    refine le_bot_iff.mp ?_
    intro z hz
    obtain ⟨hzO, hzV⟩ := Subgroup.mem_inf.mp hz
    have hodd : Odd (orderOf z) :=
      odd_card_jOddCore.of_dvd_nat (Subgroup.orderOf_dvd_natCard (jOddCore G Ω) hzO)
    exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_isPGroup hroot.isPGroup_V hzV hodd)
  exact hS.eq_bot_of_normal_of_inf_eq_bot jOddCore_normal (disjoint_iff.mp hdisj)

theorem Sec7Hyp.gammaStab_ne_top (hS : Sec7Hyp M V n f) (h75 : Sec7.Stmt75 V)
    (hne : omegaSet V ≠ gammaAt V) : gammaStab V ≠ ⊤ := by
  intro htop
  apply hne
  refine Set.Subset.antisymm ?_ (gammaAt_subset_omegaSet V)
  intro B hB
  obtain ⟨g, -, rfl⟩ := hB
  exact (hS.toSec6Hyp.mem_gammaStab_iff h75).mp (htop ▸ Subgroup.mem_top g)

theorem Sec7Hyp.mem_gammaStab_of_conj_mem (hS : Sec7Hyp M V n f) (h75 : Sec7.Stmt75 V)
    (hH0 : ∀ B ∈ omegaSet V, ⁅V, B⁆ = ⊥ → B ∈ gammaAt V) {v x : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hx : x⁻¹ * v * x ∈ gammaStab V) : x ∈ gammaStab V := by
  have hroot := hS.sec5.toRootHyp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set y : G := x⁻¹ * v * x with hydef
  have hyV : y ∈ conjSubgroup x⁻¹ V := by
    rw [mem_conjSubgroup]
    simpa [y, mul_assoc] using hv
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) :=
    (hroot.isPGroup_V.map (MulAut.conj x⁻¹).toMonoidHom).to_le (Subgroup.zpowers_le.mpr hyV)
  have hstab : ∀ g ∈ Subgroup.zpowers y, ∀ C ∈ gammaAt V,
      C.map (MulAut.conj g).toMonoidHom ∈ gammaAt V := by
    intro g hg C hC
    have hgY : g ∈ gammaStab V := Subgroup.zpowers_le.mpr hx hg
    exact CFSG.Timmesfeld.ARS.conjSub_mem_of_mem_stabSet hgY hC
  have hodd : ¬ 2 ∣ (gammaAt V).ncard := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr (hS.toSec6Hyp.odd_ncard_gammaAt)
  obtain ⟨F₀, hF₀Γ, hF₀y⟩ :=
    CFSG.Timmesfeld.Bridge.exists_map_conj_eq_of_isPGroup (p := 2) hy2 hstab hodd
  have hyF : conjSubgroup y F₀ = F₀ := hF₀y y (Subgroup.mem_zpowers y)
  have hyF' : conjSubgroup (x⁻¹ * v * x) F₀ = F₀ := hydef ▸ hyF
  have hvN : v ∈ Subgroup.normalizer (conjSubgroup x F₀ : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq]
    calc conjSubgroup v (conjSubgroup x F₀) = conjSubgroup (v * x) F₀ :=
          conjSubgroup_conjSubgroup v x F₀
      _ = conjSubgroup (x * (x⁻¹ * v * x)) F₀ := by
          rw [show v * x = x * (x⁻¹ * v * x) by group]
      _ = conjSubgroup x (conjSubgroup (x⁻¹ * v * x) F₀) :=
          (conjSubgroup_conjSubgroup x (x⁻¹ * v * x) F₀).symm
      _ = conjSubgroup x F₀ := by rw [hyF']
  obtain ⟨g₀, -, hg₀⟩ := gammaAt_subset_omegaSet V hF₀Γ
  have hE : conjSubgroup x F₀ = conjSubgroup (x * g₀) V := by
    rw [hg₀, conjSubgroup_conjSubgroup]
  have hne : V ⊓ Subgroup.normalizer (conjSubgroup (x * g₀) V : Set G) ≠ ⊥ := by
    intro hbot
    have hmem : v ∈ V ⊓ Subgroup.normalizer (conjSubgroup (x * g₀) V : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hv, ?_⟩
      rwa [← hE]
    rw [hbot] at hmem
    exact hv1 (Subgroup.mem_bot.mp hmem)
  have hcomm := Tim78.commute_of_isRootTypeTI hroot.rootType (g := 1) (h := x * g₀) (by
    rwa [conjSubgroup_one])
  have hcommbot : ⁅V, conjSubgroup x F₀⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [hE] at hb
    exact (hcomm a (by rwa [conjSubgroup_one]) b hb).symm
  have hFxΓ : conjSubgroup x F₀ ∈ gammaAt V := by
    refine hH0 _ ?_ hcommbot
    rw [hE]
    exact ⟨x * g₀, Subgroup.mem_top _, rfl⟩
  have hF₀ω : F₀ ∈ omegaSet V := gammaAt_subset_omegaSet V hF₀Γ
  have hVω : V ∈ omegaSet V := ⟨1, Subgroup.mem_top 1, (conjSubgroup_one V).symm⟩
  have hΓF : gammaAt F₀ = gammaAt V := h75 F₀ hF₀Γ
  have hΓFx : gammaAt (conjSubgroup x F₀) = gammaAt V := h75 _ hFxΓ
  refine hS.toSec6Hyp.sec5.toRootHyp.toHyp.mem_gammaStab_iff_gammaAt_eq.mpr ?_
  calc gammaAt (conjSubgroup x V)
      = CFSG.Timmesfeld.ARS.conjSet (gammaAt V) x :=
        hS.toSec6Hyp.sec5.toRootHyp.toHyp.gammaAt_conj hVω x
    _ = CFSG.Timmesfeld.ARS.conjSet (gammaAt F₀) x := by rw [hΓF]
    _ = gammaAt (conjSubgroup x F₀) :=
        (hS.toSec6Hyp.sec5.toRootHyp.toHyp.gammaAt_conj hF₀ω x).symm
    _ = gammaAt V := hΓFx

theorem Sec7Hyp.smul_eq_iff (hS : Sec7Hyp M V n f) (h75 : Sec7.Stmt75 V)
    (hH0 : ∀ B ∈ omegaSet V, ⁅V, B⁆ = ⊥ → B ∈ gammaAt V) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (ω : G ⧸ gammaStab V) :
    v • ω = ω ↔ ω = ((1 : G) : G ⧸ gammaStab V) := by
  have hroot := hS.sec5.toRootHyp.toHyp
  have hvv : v * v = 1 := by simpa [pow_two] using hroot.elem.2 v hv
  constructor
  · intro hfix
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective ω
    rw [Quotient.smul_mk, QuotientGroup.eq (s := gammaStab V)] at hfix
    have h1 : x⁻¹ * v * x ∈ gammaStab V := by
      have hveq : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
      simpa [mul_inv_rev, hveq] using hfix
    have hxY : x ∈ gammaStab V := hS.mem_gammaStab_of_conj_mem h75 hH0 hv hv1 h1
    rw [QuotientGroup.eq (s := gammaStab V)]
    simpa using hxY
  · rintro rfl
    rw [Quotient.smul_mk, QuotientGroup.eq (s := gammaStab V)]
    have hvY : v ∈ gammaStab V := hroot.M_le_gammaStab (hroot.le_M hv)
    simpa using Subgroup.inv_mem _ hvY

theorem Sec7Hyp.normalCore_gammaStab (hS : Sec7Hyp M V n f) (h75 : Sec7.Stmt75 V)
    (hH0 : ∀ B ∈ omegaSet V, ⁅V, B⁆ = ⊥ → B ∈ gammaAt V)
    (hne : omegaSet V ≠ gammaAt V) : (gammaStab V).normalCore = ⊥ := by
  refine hS.toSec6Hyp.eq_bot_of_normal_of_inf_eq_bot (Subgroup.normalCore_normal _) ?_
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvcore, hvV⟩ := Subgroup.mem_inf.mp hv
  by_contra hv1
  have hx : ∃ x, x ∉ gammaStab V := by
    by_contra h
    apply hS.gammaStab_ne_top h75 hne
    rw [eq_top_iff]
    intro x _
    by_contra hx
    exact h ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hx
  have hmem : x⁻¹ * v * x ∈ gammaStab V := by
    have hconj := (Subgroup.normalCore_normal (gammaStab V)).conj_mem v hvcore x⁻¹
    exact Subgroup.normalCore_le (gammaStab V) (by simpa [mul_assoc] using hconj)
  exact hx (hS.mem_gammaStab_of_conj_mem h75 hH0 hvV hv1 hmem)

private theorem Pc_le_V_of_transitive (hS : Sec7Hyp M V n f)
    (hPY : Pc M V ≤ gammaStab V) (hMY : M ≤ gammaStab V)
    (hcore : (gammaStab V).normalCore = ⊥) {x₀ : G ⧸ gammaStab V}
    (hx₀ : x₀ ≠ ((1 : G) : G ⧸ gammaStab V))
    (hno : ∀ x y : G ⧸ gammaStab V, x ≠ ((1 : G) : G ⧸ gammaStab V) →
      y ≠ ((1 : G) : G ⧸ gammaStab V) → ∃ v ∈ V, v • x = y) :
    Pc M V ≤ V := by
  have hroot := hS.sec5.toRootHyp.toHyp
  intro p hp
  have hpbase : p • ((1 : G) : G ⧸ gammaStab V) = ((1 : G) : G ⧸ gammaStab V) := by
    rw [Quotient.smul_mk, QuotientGroup.eq (s := gammaStab V)]
    simpa using Subgroup.inv_mem _ (hPY hp)
  have hpx : p • x₀ ≠ ((1 : G) : G ⧸ gammaStab V) := by
    intro h
    apply hx₀
    have h2 : p⁻¹ • (p • x₀) = p⁻¹ • ((1 : G) : G ⧸ gammaStab V) := by rw [h]
    rw [inv_smul_smul] at h2
    have h3 : p⁻¹ • ((1 : G) : G ⧸ gammaStab V) = ((1 : G) : G ⧸ gammaStab V) := by
      conv_lhs => rw [← hpbase]
      rw [inv_smul_smul]
    rw [h2, h3]
  obtain ⟨v, hvV, hvx⟩ := hno x₀ (p • x₀) hx₀ hpx
  have hfix : (v⁻¹ * p) • x₀ = x₀ := by
    rw [mul_smul, ← hvx, inv_smul_smul]
  have hall : ∀ ω : G ⧸ gammaStab V, (v⁻¹ * p) • ω = ω := by
    intro ω
    by_cases hω : ω = ((1 : G) : G ⧸ gammaStab V)
    · rw [hω, Quotient.smul_mk, QuotientGroup.eq (s := gammaStab V)]
      simpa using Subgroup.inv_mem _ (Subgroup.mul_mem _
        (Subgroup.inv_mem _ (hMY (hroot.le_M hvV))) (hPY hp))
    · obtain ⟨u, huV, hux⟩ := hno x₀ ω hx₀ hω
      have hpu : p * u = u * p :=
        (Subgroup.mem_centralizer_iff.mp hp.2 u huV).symm
      have hvu : v⁻¹ * u = u * v⁻¹ :=
        hroot.commute_of_mem_conj (g := 1) (by rw [conjSubgroup_one]; exact Subgroup.inv_mem _ hvV)
          (by rw [conjSubgroup_one]; exact huV)
      have hcomm : (v⁻¹ * p) * u = u * (v⁻¹ * p) := by
        calc v⁻¹ * p * u = v⁻¹ * (p * u) := by group
          _ = v⁻¹ * (u * p) := by rw [hpu]
          _ = (v⁻¹ * u) * p := by group
          _ = (u * v⁻¹) * p := by rw [hvu]
          _ = u * (v⁻¹ * p) := by group
      calc (v⁻¹ * p) • ω = (v⁻¹ * p) • (u • x₀) := by rw [hux]
        _ = ((v⁻¹ * p) * u) • x₀ := (mul_smul _ _ _).symm
        _ = (u * (v⁻¹ * p)) • x₀ := by rw [hcomm]
        _ = u • ((v⁻¹ * p) • x₀) := mul_smul _ _ _
        _ = u • x₀ := by rw [hfix]
        _ = ω := hux
  have hmemcore : v⁻¹ * p ∈ (gammaStab V).normalCore := by
    rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker, MulAction.toPermHom_apply]
    exact Equiv.ext hall
  rw [hcore] at hmemcore
  have hvpinv : v⁻¹ * p = 1 := Subgroup.mem_bot.mp hmemcore
  have hpv : p = v := by
    have h2 := congrArg (fun z => v * z) hvpinv
    simpa [mul_assoc] using h2
  rw [hpv]
  exact hvV

theorem Sec7Hyp.exists_two_orbits (hS : Sec7Hyp M V n f) (h75 : Sec7.Stmt75 V)
    (hH0 : ∀ B ∈ omegaSet V, ⁅V, B⁆ = ⊥ → B ∈ gammaAt V)
    (hne : omegaSet V ≠ gammaAt V) :
    ∃ x y : G ⧸ gammaStab V, x ≠ ((1 : G) : G ⧸ gammaStab V) ∧
      y ≠ ((1 : G) : G ⧸ gammaStab V) ∧ ∀ v ∈ V, v • x ≠ y := by
  classical
  have hcore := hS.normalCore_gammaStab h75 hH0 hne
  have hroot := hS.sec5.toRootHyp.toHyp
  have hMY : M ≤ gammaStab V := hroot.M_le_gammaStab
  have hPY : Pc M V ≤ gammaStab V := hroot.Pc_le_M.trans hMY
  by_contra hno
  push Not at hno
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G ⧸ gammaStab V, x₀ ≠ ((1 : G) : G ⧸ gammaStab V) := by
    by_contra h
    push Not at h
    apply hS.gammaStab_ne_top h75 hne
    rw [eq_top_iff]
    intro g _
    by_contra hg
    have h1 : (QuotientGroup.mk g : G ⧸ gammaStab V) ≠ ((1 : G) : G ⧸ gammaStab V) := by
      intro h2
      apply hg
      have h3 := (QuotientGroup.eq (s := gammaStab V)).mp h2
      simpa using Subgroup.inv_mem _ h3
    exact h1 (h (QuotientGroup.mk g))
  have hPV : Pc M V ≤ V := Pc_le_V_of_transitive hS hPY hMY hcore hx₀ hno
  have hcard : Nat.card ↥(Pc M V) ≤ Nat.card ↥V := Subgroup.card_le_of_le hPV
  rw [hS.card_Pc, hS.card_V] at hcard
  have h2 : 1 < 2 ^ f := by
    have hf := hS.two_le
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle : (2 ^ f) ^ (2 * n + 1) ≤ (2 ^ f) ^ 1 := by simpa using hcard
  have := (Nat.pow_le_pow_iff_right h2).mp hle
  have := hS.four_le
  omega


theorem Sec7Hyp.exists_isHoltTriple_gammaStab (hS : Sec7Hyp M V n f) (h75 : Sec7.Stmt75 V)
    (hH0 : ∀ B ∈ omegaSet V, ⁅V, B⁆ = ⊥ → B ∈ gammaAt V) :
    ∃ z ∈ V, z ≠ 1 ∧
      IsHoltTriple G (G ⧸ gammaStab V) z ((1 : G) : G ⧸ gammaStab V) := by
  have hroot := hS.sec5.toRootHyp.toHyp
  obtain ⟨T, hTM, hQT⟩ := hroot.exists_sylow_le_M
  have hQne : inSubgroup (pCore 2) M ≠ ⊥ := by
    intro hbot
    exact hroot.ne_bot (le_bot_iff.mp (hroot.le_Q.trans_eq hbot))
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro hbot
    exact hQne (le_bot_iff.mp (hQT.trans_eq hbot))
  haveI : Nontrivial ↥(T : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot (T : Subgroup G)).mpr hTne
  haveI : Nontrivial ↥(Subgroup.center ↥(T : Subgroup G)) :=
    T.isPGroup'.center_nontrivial
  obtain ⟨w, hw1⟩ := exists_ne (1 : Subgroup.center ↥(T : Subgroup G))
  let z : G := (((w : Subgroup.center ↥(T : Subgroup G)) : ↥(T : Subgroup G)) : G)
  have hzT : z ∈ (T : Subgroup G) := ((w : Subgroup.center ↥(T : Subgroup G)) : ↥(T : Subgroup G)).2
  have hzCent : z ∈ Subgroup.centralizer ((T : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg (fun x : ↥(T : Subgroup G) => (x : G))
      (Subgroup.mem_center_iff.mp w.2 (⟨t, ht⟩ : ↥(T : Subgroup G)))
  have hzV : z ∈ V := hroot.center_sylow_le hTM T.isPGroup' hQT
    (Subgroup.mem_inf.mpr ⟨hzT, hzCent⟩)
  have hz1 : z ≠ 1 := by
    intro hz
    exact hw1 (Subtype.ext (Subtype.ext hz))
  have hz2 : z ^ 2 = 1 := hroot.elem.2 z hzV
  refine ⟨z, hzV, hz1, ?_⟩
  refine ⟨inferInstance, orderOf_eq_prime hz2 hz1, hS.smul_eq_iff h75 hH0 hzV hz1, ?_⟩
  refine ⟨T, hzT, ?_⟩
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact (Subgroup.mem_centralizer_iff.mp hzCent t ht).symm

private theorem false_of_inf_generalizedFitting_eq_bot
    (hS : Sec7Hyp M V n f) (D : HoltData G (G ⧸ gammaStab V)) (i : D.ι)
    (hFH : generalizedFitting G ≤ jHull G (G ⧸ gammaStab V))
    (hbot' : D.L i ⊓ generalizedFitting G = ⊥) : False := by
  have hO : jOddCore G (G ⧸ gammaStab V) = ⊥ := hS.toSec6Hyp.jOddCore_eq_bot _
  have hFnormal : (generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  haveI : (generalizedFitting G).Normal := hFnormal
  set F := generalizedFitting G with hFdef
  have hcent : D.L i ≤ Subgroup.centralizer (F : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hfH : f ∈ jHull G (G ⧸ gammaStab V) := hFH hf
    have hfl : f * l * f⁻¹ ∈ D.L i :=
      (Subgroup.mem_normalizer_iff.mp (D.le_normalizer i hfH) l).mp hl
    have hcommF : l * f⁻¹ * l⁻¹ ∈ F := hFnormal.conj_mem f⁻¹ (F.inv_mem hf) l
    have hmemL : (f * l * f⁻¹) * l⁻¹ ∈ D.L i :=
      (D.L i).mul_mem hfl ((D.L i).inv_mem hl)
    have hmemF : (f * l * f⁻¹) * l⁻¹ ∈ F := by
      rw [show (f * l * f⁻¹) * l⁻¹ = f * (l * f⁻¹ * l⁻¹) by group]
      exact F.mul_mem hf hcommF
    have hzero : (f * l * f⁻¹) * l⁻¹ = 1 := by
      have hmem := Subgroup.mem_inf.mpr ⟨hmemL, hmemF⟩
      rw [hbot'] at hmem
      exact Subgroup.mem_bot.mp hmem
    have h2 : f * l * f⁻¹ = l := by
      have h3 : (f * l * f⁻¹) * l⁻¹ = 1 := hzero
      rwa [mul_inv_eq_one] at h3
    calc f * l = (f * l * f⁻¹) * f := by group
      _ = l * f := by rw [h2]
  have hLleF : D.L i ≤ F := hcent.trans (CFSG.centralizer_generalizedFitting_le G)
  have hLbot : D.L i = ⊥ := by
    have h1 : D.L i ⊓ F = D.L i := inf_eq_left.mpr hLleF
    rwa [h1] at hbot'
  obtain ⟨a, b, hab⟩ := D.exists_mul_ne_mul_L hO i
  have ha : (a : G) = 1 := Subgroup.mem_bot.mp (hLbot ▸ a.2)
  have hb : (b : G) = 1 := Subgroup.mem_bot.mp (hLbot ▸ b.2)
  exact hab (by
    have ha' : a = 1 := Subtype.ext ha
    have hb' : b = 1 := Subtype.ext hb
    rw [ha', hb'])

theorem Sec7Hyp.generalizedFitting_le_L (hS : Sec7Hyp M V n f)
    (h75 : Sec7.Stmt75 V) (hH0 : ∀ B ∈ omegaSet V, ⁅V, B⁆ = ⊥ → B ∈ gammaAt V)
    (D : HoltData G (G ⧸ gammaStab V)) (i : D.ι) : generalizedFitting G ≤ D.L i := by
  classical
  have hroot := hS.sec5.toRootHyp
  have hO : jOddCore G (G ⧸ gammaStab V) = ⊥ := hS.toSec6Hyp.jOddCore_eq_bot _
  set F := generalizedFitting G with hFdef
  have hFnormal : F.Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  haveI : F.Normal := hFnormal
  have hVH : V ≤ jHull G (G ⧸ gammaStab V) := by
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]; exact Subgroup.one_mem _
    · refine mem_jHull_of_mem_longInv ⟨?_, ?_⟩
      · exact orderOf_eq_prime (by simpa [pow_two] using hroot.toHyp.elem.2 v hv) hv1
      · exact ⟨_, (hS.smul_eq_iff h75 hH0 hv hv1 _).mpr rfl,
          fun ω hω => (hS.smul_eq_iff h75 hH0 hv hv1 ω).mp hω⟩
  have hFH : F ≤ jHull G (G ⧸ gammaStab V) := by
    have hnc : Subgroup.normalClosure (V : Set G) = F :=
      hS.toSec6Hyp.normalClosure_eq hS.toSec6Hyp.stmt60
    rw [← hnc]
    exact Subgroup.normalClosure_le_normal fun v hv => hVH hv
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hVF : V ≤ F := by
      have hnc : Subgroup.normalClosure (V : Set G) = F :=
        hS.toSec6Hyp.normalClosure_eq hS.toSec6Hyp.stmt60
      rw [← hnc]
      exact Subgroup.le_normalClosure
    exact hroot.toHyp.ne_bot (le_bot_iff.mp (hVF.trans_eq hbot))
  haveI : IsSimpleGroup ↥F :=
    (hroot.toHyp.isSimpleGroup_generalizedFitting hS.sec5.toRootHyp.four_le_card).1
  haveI : ((D.L i).subgroupOf F).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
    intro f hf
    rw [mem_normalizer_iff_conjSubgroup_eq]
    have hfH : f ∈ jHull G (G ⧸ gammaStab V) := hFH hf
    have h1 : conjSubgroup f (D.L i) = D.L i :=
      mem_normalizer_iff_conjSubgroup_eq.mp (D.le_normalizer i hfH)
    have h2 : conjSubgroup f F = F :=
      mem_normalizer_iff_conjSubgroup_eq.mp (Subgroup.le_normalizer hf)
    rw [conjSubgroup_inf_eq_inf, h1, h2]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((D.L i).subgroupOf F) with hbot | htop
  · exfalso
    exact false_of_inf_generalizedFitting_eq_bot hS D i hFH
      (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hbot))
  · rwa [Subgroup.subgroupOf_eq_top] at htop

theorem Sec7Hyp.false_of_isNaturalSE (hS : Sec7Hyp M V n f)
    (h75 : Sec7.Stmt75 V) (hH0 : ∀ B ∈ omegaSet V, ⁅V, B⁆ = ⊥ → B ∈ gammaAt V)
    (D : HoltData G (G ⧸ gammaStab V)) {i₀ : D.ι} (hι : ∀ i, i = i₀)
    (hM : IsNaturalSE (D.M i₀)) : False := by
  classical
  have hroot := hS.sec5.toRootHyp.toHyp
  have hO : jOddCore G (G ⧸ gammaStab V) = ⊥ := hS.toSec6Hyp.jOddCore_eq_bot _
  obtain ⟨n', i', e', hA⟩ := D.isBenderAction_L hO hι hM
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer ((1 : G) : G ⧸ gammaStab V)
  obtain ⟨U, hU⟩ := hS.toSec6Hyp.ne
  obtain ⟨U', hU', hUU'⟩ := hS.toSec6Hyp.exists_isL2Gen hU
  have hMY : M ≤ gammaStab V := hroot.M_le_gammaStab
  have hFL : generalizedFitting G ≤ D.L i₀ := hS.generalizedFitting_le_L h75 hH0 D i₀
  have hUF : U ≤ generalizedFitting G := by
    obtain ⟨g, rfl, -⟩ := hU
    rw [← hS.toSec6Hyp.normalClosure_eq hS.toSec6Hyp.stmt60]
    rintro x ⟨v, hv, rfl⟩
    simpa [MulAut.conj_apply] using
      Subgroup.normalClosure_normal.conj_mem v (Subgroup.subset_normalClosure hv) g
  have hU'F : U' ≤ generalizedFitting G := by
    obtain ⟨g, rfl, -⟩ := hU'
    rw [← hS.toSec6Hyp.normalClosure_eq hS.toSec6Hyp.stmt60]
    rintro x ⟨v, hv, rfl⟩
    simpa [MulAut.conj_apply] using
      Subgroup.normalClosure_normal.conj_mem v (Subgroup.subset_normalClosure hv) g
  have hUL : U ≤ D.L i₀ := hUF.trans hFL
  have hU'L : U' ≤ D.L i₀ := hU'F.trans hFL
  have hUY : U ≤ gammaStab V := (hS.sec5.le_M_of_mem_sigmaSet hU).1.trans hMY
  have hU'Y : U' ≤ gammaStab V := (hS.sec5.le_M_of_mem_sigmaSet hU').1.trans hMY
  have hU2 : IsPGroup 2 U := by
    obtain ⟨g, rfl, -⟩ := hU
    exact hroot.isPGroup_V.map (MulAut.conj g).toMonoidHom
  have hU'2 : IsPGroup 2 U' := by
    obtain ⟨g, rfl, -⟩ := hU'
    exact hroot.isPGroup_V.map (MulAut.conj g).toMonoidHom
  have hUstab : U.subgroupOf (D.L i₀) ≤
      stabilizer (D.L i₀) ((1 : G) : G ⧸ gammaStab V) := by
    rw [← MulAction.stabilizer_subgroupOf, MulAction.stabilizer_quotient]
    exact Subgroup.subgroupOf_mono _ hUY
  have hU'stab : U'.subgroupOf (D.L i₀) ≤
      stabilizer (D.L i₀) ((1 : G) : G ⧸ gammaStab V) := by
    rw [← MulAction.stabilizer_subgroupOf, MulAction.stabilizer_quotient]
    exact Subgroup.subgroupOf_mono _ hU'Y
  have hUQ : U.subgroupOf (D.L i₀) ≤ (Q : Subgroup ↥(D.L i₀)) :=
    hA.le_sylow_of_isPGroup hQ (hU2.comap_subtype) hUstab
  have hU'Q : U'.subgroupOf (D.L i₀) ≤ (Q : Subgroup ↥(D.L i₀)) :=
    hA.le_sylow_of_isPGroup hQ (hU'2.comap_subtype) hU'stab
  have hsup : U ⊔ U' ≤ ((Q : Subgroup ↥(D.L i₀)).map (D.L i₀).subtype) := by
    refine sup_le ?_ ?_
    · calc U = (U.subgroupOf (D.L i₀)).map (D.L i₀).subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hUL).symm
        _ ≤ _ := Subgroup.map_mono hUQ
    · calc U' = (U'.subgroupOf (D.L i₀)).map (D.L i₀).subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hU'L).symm
        _ ≤ _ := Subgroup.map_mono hU'Q
  exact hUU'.not_isPGroup (Q.isPGroup'.map (D.L i₀).subtype |>.to_le hsup)

private theorem exists_two_ne_one (hroot : RootHyp M V) :
    ∃ v w : G, v ∈ V ∧ w ∈ V ∧ v ≠ 1 ∧ w ≠ 1 ∧ w ≠ v := by
  obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hroot.ne_bot
  have hvV : (v : G) ∈ V := v.2
  have hzv : Subgroup.zpowers (v : G) ≤ V := Subgroup.zpowers_le.mpr hvV
  have hv1' : (v : G) ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hcard2 : Nat.card (Subgroup.zpowers (v : G)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by simpa [pow_two] using hroot.elem.2 (v : G) hvV) hv1'
  have hne' : Subgroup.zpowers (v : G) ≠ V := by
    intro heq
    have h2 : Nat.card V = 2 := by rw [← heq, hcard2]
    have h4 := hroot.four_le_card
    omega
  have hssub : (Subgroup.zpowers (v : G) : Set G) ⊂ (V : Set G) := by
    rw [Set.ssubset_iff_subset_ne]
    exact ⟨hzv, fun h => hne' (Subgroup.ext (Set.ext_iff.mp h))⟩
  obtain ⟨w, hwV, hwz⟩ := Set.exists_of_ssubset hssub
  refine ⟨(v : G), w, hvV, hwV, hv1', ?_, ?_⟩
  · intro hw1'
    exact hwz (hw1' ▸ Subgroup.one_mem _)
  · intro hwv
    exact hwz (hwv ▸ Subgroup.mem_zpowers (v : G))

private theorem exists_alt_perm [Fintype (G ⧸ gammaStab V)] [DecidableEq (G ⧸ gammaStab V)]
    (hS : Sec7Hyp M V n f) (h75 : Sec7.Stmt75 V)
    (hH0 : ∀ B ∈ omegaSet V, ⁅V, B⁆ = ⊥ → B ∈ gammaAt V)
    (hAinj : Function.Injective (MulAction.toPermHom G (G ⧸ gammaStab V)))
    {x y : G ⧸ gammaStab V} (hx : x ≠ ((1 : G) : G ⧸ gammaStab V))
    (hy : y ≠ ((1 : G) : G ⧸ gammaStab V))
    (hxy : ∀ v ∈ V, v • x ≠ y) {v w : G} (hvV : v ∈ V) (hwV : w ∈ V) (hv1 : v ≠ 1)
    (hw1 : w ≠ 1) (hwv : w ≠ v) :
    ∃ p : Equiv.Perm (G ⧸ gammaStab V), p ∈ alternatingGroup (G ⧸ gammaStab V) ∧
      p * MulAction.toPermHom G (G ⧸ gammaStab V) v =
        MulAction.toPermHom G (G ⧸ gammaStab V) v * p ∧
      p * MulAction.toPermHom G (G ⧸ gammaStab V) w * p⁻¹ ∉
        V.map (MulAction.toPermHom G (G ⧸ gammaStab V)) := by
  have hroot := hS.sec5.toRootHyp.toHyp
  let A : G →* Equiv.Perm (G ⧸ gammaStab V) := MulAction.toPermHom G (G ⧸ gammaStab V)
  set E : Subgroup (Equiv.Perm (G ⧸ gammaStab V)) := V.map A with hEdef
  have haE : A v ∈ E := Subgroup.mem_map_of_mem A hvV
  have hbE : A w ∈ E := Subgroup.mem_map_of_mem A hwV
  have ha1 : A v ≠ 1 := fun h => hv1 (hAinj (by rw [h, map_one]))
  have hb1 : A w ≠ 1 := fun h => hw1 (hAinj (by rw [h, map_one]))
  have hba : A w ≠ A v := fun h => hwv (hAinj h)
  have haa : A v * A v = 1 := by
    rw [← map_mul, show v * v = 1 by simpa [pow_two] using hroot.elem.2 v hvV, map_one]
  have hreg : ∀ e ∈ E, e x = x → e = 1 := by
    intro e he hex
    obtain ⟨u, huV, rfl⟩ := Subgroup.mem_map.mp he
    by_cases hu1 : u = 1
    · rw [hu1, map_one]
    · exact absurd ((hS.smul_eq_iff h75 hH0 huV hu1 x).mp hex) hx
  have hreg' : ∀ e ∈ E, e y = y → e = 1 := by
    intro e he hey
    obtain ⟨u, huV, rfl⟩ := Subgroup.mem_map.mp he
    by_cases hu1 : u = 1
    · rw [hu1, map_one]
    · exact absurd ((hS.smul_eq_iff h75 hH0 huV hu1 y).mp hey) hy
  have hno : ∀ e ∈ E, e x ≠ y := by
    intro e he
    obtain ⟨u, huV, rfl⟩ := Subgroup.mem_map.mp he
    exact hxy u huV
  exact CFSG.GroupTheory.exists_mem_alternatingGroup_commute_conj_notMem haE ha1 haa hbE hb1 hba
    hreg hreg' hno

theorem Sec7Hyp.false_of_alternating (hS : Sec7Hyp M V n f) (h75 : Sec7.Stmt75 V)
    (hH0 : ∀ B ∈ omegaSet V, ⁅V, B⁆ = ⊥ → B ∈ gammaAt V)
    (hne : omegaSet V ≠ gammaAt V) (D : HoltData G (G ⧸ gammaStab V)) {i₀ : D.ι}
    (hι : ∀ i, i = i₀) (hA : D.M i₀ = alternatingGroup (D.Ψc i₀)) : False := by
  classical
  have hroot := hS.sec5.toRootHyp.toHyp
  have hO : jOddCore G (G ⧸ gammaStab V) = ⊥ := hS.toSec6Hyp.jOddCore_eq_bot _
  have hcore : (gammaStab V).normalCore = ⊥ := hS.normalCore_gammaStab h75 hH0 hne
  haveI : FaithfulSMul G (G ⧸ gammaStab V) := by
    apply faithfulSMul_of_ker_eq_bot
    rw [← Subgroup.normalCore_eq_ker]
    exact hcore
  haveI : Fintype (G ⧸ gammaStab V) := Fintype.ofFinite _
  haveI : DecidableEq (G ⧸ gammaStab V) := Classical.decEq _
  let A : G →* Equiv.Perm (G ⧸ gammaStab V) := MulAction.toPermHom G (G ⧸ gammaStab V)
  have hAker : A.ker = ⊥ := by
    have h1 : A.ker = (gammaStab V).normalCore :=
      (Subgroup.normalCore_eq_ker (gammaStab V)).symm
    rw [h1, hcore]
  have hAinj : Function.Injective A := (MonoidHom.ker_eq_bot_iff A).mp hAker
  obtain ⟨x, y, hx, hy, hxy⟩ := hS.exists_two_orbits h75 hH0 hne
  obtain ⟨v, w, hvV, hwV, hv1, hw1, hwv⟩ := exists_two_ne_one hS.sec5.toRootHyp
  obtain ⟨p, hpalt, hpcomm, hpE⟩ :=
    exists_alt_perm hS h75 hH0 hAinj hx hy hxy hvV hwV hv1 hw1 hwv
  have halt := D.alternatingGroup_le_range_L hO hι hA
  obtain ⟨l, hl⟩ := halt hpalt
  have hlA : A (l : G) = p := by
    ext ω
    have h := congrArg (fun f : Equiv.Perm (G ⧸ gammaStab V) => f ω) hl
    simpa [A, MulAction.toPermHom_apply, MulAction.toPerm_apply, Subgroup.smul_def] using h
  have hlv : (l : G) * v = v * (l : G) := by
    apply hAinj
    rw [map_mul, map_mul, hlA]
    exact hpcomm
  have hlM : (l : G) ∈ M := by
    refine hroot.centralizer_le_M hvV hv1 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hlv.symm
  have hlN : (l : G) ∈ Subgroup.normalizer (V : Set G) := by
    rw [hroot.normalizer_eq]
    exact hlM
  have hlwV : (l : G) * w * (l : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hlN w).mp hwV
  refine hpE ?_
  have h1 : p * A w * p⁻¹ = A ((l : G) * w * (l : G)⁻¹) := by
    rw [map_mul, map_mul, map_inv, hlA]
  rw [h1]
  exact Subgroup.mem_map_of_mem A hlwV

theorem Sec7Hyp.stmt77a (hS : Sec7Hyp M V n f)
    (h75 : Sec7.Stmt75 V) (hHolt : HoltTheorem1) : Sec7.Stmt77a V := by
  rw [Sec7.Stmt77a]
  intro hne
  by_contra hno
  push Not at hno
  have hH0 : ∀ B ∈ omegaSet V, ⁅V, B⁆ = ⊥ → B ∈ gammaAt V := by
    intro B hB hcomm
    by_contra hΓ
    exact absurd hcomm (hno B hB hΓ)
  have hcore : (gammaStab V).normalCore = ⊥ := hS.normalCore_gammaStab h75 hH0 hne
  haveI : FaithfulSMul G (G ⧸ gammaStab V) := by
    apply faithfulSMul_of_ker_eq_bot
    rw [← Subgroup.normalCore_eq_ker]
    exact hcore
  obtain ⟨z, hzV, hz1, hT⟩ := hS.exists_isHoltTriple_gammaStab h75 hH0
  have h3 : 3 ≤ Nat.card (G ⧸ gammaStab V) := IsHoltTriple.three_le_card hT
  have hstar : IsStarGroup G (G ⧸ gammaStab V) := IsHoltTriple.isStarGroup hT h3
  obtain ⟨D⟩ := hHolt G (G ⧸ gammaStab V) hstar
  have hO : jOddCore G (G ⧸ gammaStab V) = ⊥ := hS.toSec6Hyp.jOddCore_eq_bot _
  haveI : Nontrivial (G ⧸ gammaStab V) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hFne : generalizedFitting G ≠ ⊥ := by
    intro hbot
    have hVF : V ≤ generalizedFitting G := by
      have hnc : Subgroup.normalClosure (V : Set G) = generalizedFitting G :=
        hS.toSec6Hyp.normalClosure_eq hS.toSec6Hyp.stmt60
      rw [← hnc]
      exact Subgroup.le_normalClosure
    exact hS.sec5.toRootHyp.toHyp.ne_bot (le_bot_iff.mp (hVF.trans_eq hbot))
  obtain ⟨i₀, hι⟩ := D.exists_forall_eq_of_le_L hO hFne
    (fun i => hS.generalizedFitting_le_L h75 hH0 D i)
  rcases D.factor i₀ with ⟨hAlt, -⟩ | hSE
  · exact hS.false_of_alternating h75 hH0 hne D hι hAlt
  · exact hS.false_of_isNaturalSE h75 hH0 D hι hSE

end CFSG.RankThree.GF2n.Tim81
