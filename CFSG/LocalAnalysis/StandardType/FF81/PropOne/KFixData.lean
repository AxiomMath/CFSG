module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.CenBDecomp
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.XqBasic
public import CFSG.Mathlib.GroupTheory.LayerFixedJ

import CFSG.Mathlib.GroupTheory.CoprimeFixedLift
import CFSG.Adapters.LieModelSimple
import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.StandardType.FF81.PropOne.JSylow
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

private theorem mem_map_subtype_iff {G : Type*} [Group G] {H : Subgroup G}
    {M : Subgroup ↥H} {m : ↥H} : (m : G) ∈ M.map H.subtype ↔ m ∈ M := by
  constructor
  · intro h
    obtain ⟨m', hm', hm'eq⟩ := Subgroup.mem_map.mp h
    have : m' = m := Subtype.ext hm'eq
    rwa [this] at hm'
  · intro h
    exact Subgroup.mem_map_of_mem H.subtype h

private theorem card_subgroupOf_eq {G : Type*} [Group G] {H K : Subgroup G} (h : K ≤ H) :
    Nat.card (K.subgroupOf H) = Nat.card K :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem exists_kfixData {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J B₂ A R : Subgroup G}
    (hJ : JData n L z J) (hR : RData b z J B₂ A R) :
    ∃ (β : MulAut (Xq R)) (u : Xq R) (O J' : Subgroup (Xq R)),
      CFSG.LayerFixed.FixData β u O J' ∧
      (∀ x x' : ↥(Subgroup.centralizer (R : Set G)), (x' : G) = b * (x : G) * b⁻¹ →
        β (QuotientGroup.mk x) = QuotientGroup.mk x') ∧
      (∀ y : ↥(Subgroup.centralizer (R : Set G)), (y : G) ∈ J → (QuotientGroup.mk y : Xq R) ∈ J') ∧
      (StatedClassicalModel ↥J' .PSL 4 2 1 ∨ StatedClassicalModel ↥J' .PSL 5 2 1) := by
  obtain ⟨β, hβ3, hβcompat⟩ := exists_betaX h hR
  obtain ⟨O₀, hO₀_le, hO₀_cenL, hO₀_cop, hO₀_dec⟩ := cen_b_decomp h hJ hR
  let H : Subgroup G := Subgroup.centralizer (R : Set G)
  let M : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let Mg : Subgroup G := M.map H.subtype
  let π : ↥H →* Xq R := QuotientGroup.mk' M
  have hcommB : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext_iff.mp
      (hR.b2.abel.1.is_comm.comm (⟨x, hx⟩ : ↥B₂) (⟨y, hy⟩ : ↥B₂))
  have hb₁B₂ : GGFF.zs z 0 ∈ B₂ :=
    hR.b2.B₁_le (Subgroup.subset_closure (Set.mem_range_self 0))
  have hb₁H : GGFF.zs z 0 ∈ H := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact hcommB r (hR.le hr) (GGFF.zs z 0) hb₁B₂
  have hb₁_ne_one : GGFF.zs z 0 ≠ 1 :=
    fun h1 => h.model.z_ne_one 0 (Subtype.ext h1)
  have hb₁3 : GGFF.zs z 0 ^ 3 = 1 := by
    simpa using congrArg Subtype.val (h.model.pow_z 0)
  have hb3 : b ^ 3 = 1 := by
    rw [← h.hypA.ord]
    exact pow_orderOf_eq_one b
  have hb_comm_b₁ : b * GGFF.zs z 0 = GGFF.zs z 0 * b :=
    Subgroup.mem_centralizer_iff.mp (h.hypA.le (z 0).2) b (Set.mem_singleton b)
  have hJ_le_H : J ≤ H := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact hR.cenJ r hr y hy
  have hO₀_le_H : O₀ ≤ H := hO₀_le.trans inf_le_right
  have hJsimple : IsSimpleGroup ↥J :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hJ.model
  have h9dvd : 3 ∣ Nat.card J := by
    have h9 : Nat.card (bOne z ⊓ J : Subgroup G) = 9 := (sylow_B₁_inf_J h hJ).2.1
    have hdvd : Nat.card (bOne z ⊓ J : Subgroup G) ∣ Nat.card J :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [h9] at hdvd
    exact dvd_trans (by norm_num : 3 ∣ 9) hdvd
  have hJ_ne_bot : J ≠ ⊥ := by
    intro hbot
    have : Nat.card J = 1 := by rw [hbot, Subgroup.card_bot]
    rw [this] at h9dvd
    norm_num at h9dvd
  have hb_nor_Mg : ∀ m ∈ Mg, b * m * b⁻¹ ∈ Mg := by
    intro m hm
    obtain ⟨m', hm'M, hm'eq⟩ := Subgroup.mem_map.mp hm
    obtain ⟨m'', hm''val, hm''β⟩ := hβcompat m'
    have h1 : (QuotientGroup.mk m' : Xq R) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact hm'M
    have h2 : (QuotientGroup.mk m'' : Xq R) = 1 := by
      rw [← hm''β, h1, map_one]
    have hm''M : m'' ∈ M :=
      (QuotientGroup.eq_one_iff (N := M) (m'' : ↥H)).mp h2
    rw [← hm'eq]
    change b * (m' : G) * b⁻¹ ∈ Mg
    rw [← hm''val]
    exact Subgroup.mem_map_of_mem H.subtype hm''M
  have hMg_card : Nat.card Mg = Nat.card M :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hMg_cop : ¬ 3 ∣ Nat.card Mg := by
    rw [hMg_card]
    exact (Nat.prime_three.coprime_iff_not_dvd).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H))
  have hJM_bot : J.subgroupOf H ⊓ M = ⊥ := by
    have hDnorm : (M.subgroupOf (J.subgroupOf H)).Normal :=
      (inferInstance : M.Normal).subgroupOf _
    have hsimple : IsSimpleGroup ↥(J.subgroupOf H) :=
      (Subgroup.subgroupOfEquivOfLe hJ_le_H).isSimpleGroup_congr.mpr hJsimple
    rcases @Subgroup.Normal.eq_bot_or_eq_top (↥(J.subgroupOf H)) inferInstance hsimple
      (M.subgroupOf (J.subgroupOf H)) hDnorm with hbot | htop
    · apply le_antisymm _ bot_le
      intro x hx
      rw [Subgroup.mem_bot]
      have hxJ : x ∈ J.subgroupOf H := (Subgroup.mem_inf.mp hx).1
      have hxM : x ∈ M := (Subgroup.mem_inf.mp hx).2
      have hmem : (⟨x, hxJ⟩ : ↥(J.subgroupOf H)) ∈ M.subgroupOf (J.subgroupOf H) := by
        rw [Subgroup.mem_subgroupOf]
        exact hxM
      rw [hbot] at hmem
      exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem)
    · exfalso
      have hJM_le_Mg : J ≤ Mg := by
        intro x hxJ
        have hxJH : (⟨x, hJ_le_H hxJ⟩ : ↥H) ∈ J.subgroupOf H := by
          rw [Subgroup.mem_subgroupOf]
          exact hxJ
        have hxM : (⟨x, hJ_le_H hxJ⟩ : ↥H) ∈ M := by
          have hmem : (⟨⟨x, hJ_le_H hxJ⟩, hxJH⟩ : ↥(J.subgroupOf H)) ∈
              M.subgroupOf (J.subgroupOf H) := by rw [htop]; trivial
          rwa [Subgroup.mem_subgroupOf] at hmem
        have hxMg : H.subtype ⟨x, hJ_le_H hxJ⟩ ∈ Mg :=
          Subgroup.mem_map_of_mem H.subtype hxM
        exact hxMg
      exact hMg_cop (dvd_trans h9dvd (Subgroup.card_dvd_of_le hJM_le_Mg))
  have hπJ_inj : Function.Injective (π.subgroupMap (J.subgroupOf H)) := by
    intro a b hab
    have hq : (QuotientGroup.mk (a : ↥H) : Xq R) = QuotientGroup.mk (b : ↥H) :=
      congrArg Subtype.val hab
    have hmemM : (a : ↥H)⁻¹ * (b : ↥H) ∈ M := QuotientGroup.eq.mp hq
    have hmemJ : (a : ↥H)⁻¹ * (b : ↥H) ∈ J.subgroupOf H :=
      (J.subgroupOf H).mul_mem ((J.subgroupOf H).inv_mem a.2) b.2
    have hab1 : (a : ↥H)⁻¹ * (b : ↥H) = 1 := by
      have := Subgroup.mem_inf.mpr ⟨hmemJ, hmemM⟩
      rw [hJM_bot] at this
      exact Subgroup.mem_bot.mp this
    have hab' : (a : ↥H) = (b : ↥H) := by
      calc (a : ↥H) = (a : ↥H) * ((a : ↥H)⁻¹ * (b : ↥H)) := by rw [hab1, mul_one]
        _ = (b : ↥H) := by group
    exact Subtype.ext hab'
  let J' : Subgroup (Xq R) := (J.subgroupOf H).map π
  let eJ : ↥(J.subgroupOf H) ≃* ↥J' := MulEquiv.ofBijective _
    ⟨hπJ_inj, MonoidHom.subgroupMap_surjective π (J.subgroupOf H)⟩
  let eJJ' : ↥J ≃* ↥J' := (Subgroup.subgroupOfEquivOfLe hJ_le_H).symm.trans eJ
  have hfix : ∀ x : Xq R, β x = x → ∃ i : ℕ, ∃ o ∈ (O₀.subgroupOf H).map π,
      ∃ y ∈ (J.subgroupOf H).map π, x = π ⟨GGFF.zs z 0, hb₁H⟩ ^ i * o * y := by
    intro x hx
    obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective M x
    change (QuotientGroup.mk x₀ : Xq R) = x at hx₀
    obtain ⟨x₁, hx₁val, hx₁β⟩ := hβcompat x₀
    have hx₁x₀ : (QuotientGroup.mk x₁ : Xq R) = QuotientGroup.mk x₀ := by
      rw [← hx₁β, hx₀, hx]
    have hx₀x₁ : x₀⁻¹ * x₁ ∈ M := by
      have := QuotientGroup.eq.mp hx₁x₀
      simpa [mul_inv_rev] using M.inv_mem this
    have hx₀x₁_G : (x₀ : G)⁻¹ * (b * (x₀ : G) * b⁻¹) ∈ Mg := by
      have hmem : (x₀ : G)⁻¹ * (x₁ : G) ∈ Mg := by
        change ((x₀⁻¹ * x₁ : ↥H) : G) ∈ Mg
        exact mem_map_subtype_iff.mpr hx₀x₁
      rwa [hx₁val] at hmem
    obtain ⟨m, hmMg, hmfix⟩ :=
      CFSG.CoprimeFixedLift.exists_fixed_mul_mem hb3 hMg_cop hb_nor_Mg hx₀x₁_G
    obtain ⟨mₕ, hmₕM, hmₕval⟩ := Subgroup.mem_map.mp hmMg
    have hmₕπ : π mₕ = 1 := by
      change (QuotientGroup.mk mₕ : Xq R) = 1
      rw [QuotientGroup.eq_one_iff]
      exact hmₕM
    have hfix_m : b * ((x₀ * mₕ : ↥H) : G) * b⁻¹ = ((x₀ * mₕ : ↥H) : G) := by
      change b * ((x₀ : G) * (mₕ : G)) * b⁻¹ = (x₀ : G) * (mₕ : G)
      rw [show (mₕ : G) = m from hmₕval]
      exact hmfix
    have hbg : b * ((x₀ * mₕ : ↥H) : G) = ((x₀ * mₕ : ↥H) : G) * b := by
      calc b * ((x₀ * mₕ : ↥H) : G)
          = (b * ((x₀ * mₕ : ↥H) : G) * b⁻¹) * b := by group
        _ = ((x₀ * mₕ : ↥H) : G) * b := by rw [hfix_m]
    have hx₀mₕ_mem : ((x₀ * mₕ : ↥H) : G) ∈
        Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (R : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨?_, (x₀ * mₕ).2⟩
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      rw [Set.mem_singleton_iff] at hc
      subst hc
      exact hbg
    obtain ⟨i, o, hoO₀, y, hyJ, hdec⟩ := hO₀_dec ((x₀ * mₕ : ↥H) : G) hx₀mₕ_mem
    have hoH : o ∈ H := hO₀_le_H hoO₀
    have hyH : y ∈ H := hJ_le_H hyJ
    have hdecH : (x₀ * mₕ : ↥H) =
        (⟨GGFF.zs z 0, hb₁H⟩ : ↥H) ^ i * ⟨o, hoH⟩ * ⟨y, hyH⟩ := by
      apply Subtype.ext
      change ((x₀ * mₕ : ↥H) : G) = GGFF.zs z 0 ^ i * o * y
      rw [hdec]
    refine ⟨i, π ⟨o, hoH⟩, ?_, π ⟨y, hyH⟩, ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem π (by rw [Subgroup.mem_subgroupOf]; exact hoO₀)
    · exact Subgroup.mem_map_of_mem π (by rw [Subgroup.mem_subgroupOf]; exact hyJ)
    · calc x = π x₀ := hx₀.symm
        _ = π x₀ * 1 := (mul_one _).symm
        _ = π x₀ * π mₕ := by rw [hmₕπ]
        _ = π (x₀ * mₕ) := (map_mul π x₀ mₕ).symm
        _ = π ((⟨GGFF.zs z 0, hb₁H⟩ : ↥H) ^ i * ⟨o, hoH⟩ * ⟨y, hyH⟩) := by rw [hdecH]
        _ = π (⟨GGFF.zs z 0, hb₁H⟩ : ↥H) ^ i * π ⟨o, hoH⟩ * π ⟨y, hyH⟩ := by
              rw [map_mul, map_mul, map_pow]
  refine ⟨β, π ⟨GGFF.zs z 0, hb₁H⟩, (O₀.subgroupOf H).map π, (J.subgroupOf H).map π,
    ?_, ?_, ?_, ?_⟩
  · refine
      { pow := hβ3
        u_mem := ?_
        u_ne := ?_
        u_pow := ?_
        fix_u := ?_
        fix := hfix
        fix_O := ?_
        fix_J := ?_
        coprime := ?_
        comm := ?_
        simple := ?_
        nonab := ?_
        three_dvd := ?_ }
    · rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective M g
      change π w * π ⟨GGFF.zs z 0, hb₁H⟩ = π ⟨GGFF.zs z 0, hb₁H⟩ * π w
      rw [← map_mul, ← map_mul]
      have hw : w * ⟨GGFF.zs z 0, hb₁H⟩ = ⟨GGFF.zs z 0, hb₁H⟩ * w := by
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp w.2 (GGFF.zs z 0) hR.b₁_mem).symm
      rw [hw]
    · intro h1
      have hmM : (⟨GGFF.zs z 0, hb₁H⟩ : ↥H) ∈ M :=
        (QuotientGroup.eq_one_iff (N := M) (⟨GGFF.zs z 0, hb₁H⟩ : ↥H)).mp h1
      have hdvd : orderOf (⟨GGFF.zs z 0, hb₁H⟩ : ↥H) ∣ Nat.card M :=
        Subgroup.orderOf_dvd_natCard M hmM
      have hord : orderOf (⟨GGFF.zs z 0, hb₁H⟩ : ↥H) = 3 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime hb₁3 hb₁_ne_one
      rw [hord] at hdvd
      exact (Nat.prime_three.coprime_iff_not_dvd).mp
        (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H)) hdvd
    · change (QuotientGroup.mk (⟨GGFF.zs z 0, hb₁H⟩ : ↥H) : Xq R) ^ 3 = 1
      change π (⟨GGFF.zs z 0, hb₁H⟩ : ↥H) ^ 3 = 1
      rw [← map_pow]
      have : (⟨GGFF.zs z 0, hb₁H⟩ : ↥H) ^ 3 = 1 := Subtype.ext hb₁3
      rw [this, map_one]
    · obtain ⟨m', hm'val, hm'β⟩ := hβcompat ⟨GGFF.zs z 0, hb₁H⟩
      have hmm' : m' = ⟨GGFF.zs z 0, hb₁H⟩ := by
        apply Subtype.ext
        rw [hm'val, hb_comm_b₁]
        group
      change β (QuotientGroup.mk (⟨GGFF.zs z 0, hb₁H⟩ : ↥H)) =
        QuotientGroup.mk (⟨GGFF.zs z 0, hb₁H⟩ : ↥H)
      rw [hm'β, hmm']
    · intro o ho
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp ho
      have hmO₀ : (m : G) ∈ O₀ := Subgroup.mem_subgroupOf.mp hm
      have hmb : b * (m : G) * b⁻¹ = (m : G) := by
        have hcb : (m : G) ∈ Subgroup.centralizer ({b} : Set G) :=
          (Subgroup.mem_inf.mp (hO₀_le hmO₀)).1
        have := Subgroup.mem_centralizer_iff.mp hcb b (Set.mem_singleton b)
        rw [this]
        group
      obtain ⟨m', hm'val, hm'β⟩ := hβcompat m
      have hmm' : m' = m := by
        apply Subtype.ext
        rw [hm'val, hmb]
      change β (QuotientGroup.mk m) = QuotientGroup.mk m
      rw [hm'β, hmm']
    · intro o ho
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp ho
      have hmJ : (m : G) ∈ J := Subgroup.mem_subgroupOf.mp hm
      have hmb : b * (m : G) * b⁻¹ = (m : G) := by
        have hcb : (m : G) ∈ Subgroup.centralizer ({b} : Set G) := h.hypA.le (hJ.le hmJ)
        have := Subgroup.mem_centralizer_iff.mp hcb b (Set.mem_singleton b)
        rw [this]
        group
      obtain ⟨m', hm'val, hm'β⟩ := hβcompat m
      have hmm' : m' = m := by
        apply Subtype.ext
        rw [hm'val, hmb]
      change β (QuotientGroup.mk m) = QuotientGroup.mk m
      rw [hm'β, hmm']
    · intro h3
      have hdvd : 3 ∣ Nat.card (O₀.subgroupOf H) :=
        h3.trans (Subgroup.card_map_dvd (O₀.subgroupOf H) π)
      rw [card_subgroupOf_eq hO₀_le_H] at hdvd
      exact hO₀_cop hdvd
    · intro o ho y hy
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp ho
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
      have hmO₀ : (m : G) ∈ O₀ := Subgroup.mem_subgroupOf.mp hm
      have hnJ : (n : G) ∈ J := Subgroup.mem_subgroupOf.mp hn
      change π m * π n = π n * π m
      rw [← map_mul, ← map_mul]
      have hmn : m * n = n * m := by
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp (hO₀_cenL hmO₀) (n : G) (hJ.le hnJ)).symm
      rw [hmn]
    · exact eJJ'.symm.isSimpleGroup_congr.mpr hJsimple
    · have hJ_nonab : ∃ x : ↥J, ∃ y : ↥J, x * y ≠ y * x := by
        by_contra hcon
        push Not at hcon
        have hcenter : Subgroup.center ↥J = ⊥ := by
          apply le_antisymm _ bot_le
          intro x hx
          rw [Subgroup.mem_bot]
          apply Subtype.ext
          exact center_J h hJ x.1 x.2 fun y hy =>
            (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩)).symm
        have hJbot : J = ⊥ := by
          apply le_antisymm _ bot_le
          intro x hx
          rw [Subgroup.mem_bot]
          have hxZ : (⟨x, hx⟩ : ↥J) ∈ Subgroup.center ↥J :=
            Subgroup.mem_center_iff.mpr fun g => (hcon ⟨x, hx⟩ g).symm
          rw [hcenter] at hxZ
          exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hxZ)
        exact hJ_ne_bot hJbot
      obtain ⟨x, y, hxy⟩ := hJ_nonab
      refine ⟨(eJJ' x : ↥J'), (eJJ' x).2, (eJJ' y : ↥J'), (eJJ' y).2, ?_⟩
      intro heq
      apply hxy
      apply eJJ'.injective
      rw [map_mul, map_mul]
      exact Subtype.ext heq
    · rw [← Nat.card_congr eJJ'.toEquiv]
      exact h9dvd
  · intro x x' hx'
    obtain ⟨x'', hx''val, hx''β⟩ := hβcompat x
    have hxx : x'' = x' := by
      apply Subtype.ext
      rw [hx''val, hx']
    rw [hx''β, hxx]
  · intro y hy
    have hyH : y ∈ J.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact hy
    exact Subgroup.mem_map_of_mem π hyH
  · rcases h.hypA.n_cases with rfl | rfl
    · left
      simpa only [show (5 : ℕ) - 1 = 4 by norm_num] using
        CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJJ' hJ.model
    · right
      simpa only [show (6 : ℕ) - 1 = 5 by norm_num] using
        CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJJ' hJ.model

end CFSG.StandardType.FF81.PropOne

end
