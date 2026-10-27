module

public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.Quasithin.SteinbergBMPerfectSubnormalSignalizer
public import CFSG.GroupTheory.ThompsonAxB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.PGroupQuotientOfPPrimeElements
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open scoped commutatorElement

theorem pCore_le_center_of_isQuasisimple_thetaQuotient {K : Type*} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hq : IsQuasisimple (K ⧸ aschbacherSolvableCore p K)) :
    pCore p K ≤ Subgroup.center K := by
  have : Fact p.Prime := ⟨hp⟩
  set N := aschbacherSolvableCore p K
  set Q := K ⧸ N
  set π := QuotientGroup.mk' N
  set O := pCore p K
  obtain ⟨-, hsimple, a₀, b₀, hab₀⟩ := hq
  have := hsimple
  set σ := QuotientGroup.mk' (Subgroup.center Q)
  have hOσ : (O.map π).map σ = ⊥ := by
    have hn : ((O.map π).map σ).Normal :=
      ((pCore_normal (p := p) (G := K)).map π (QuotientGroup.mk'_surjective N)).map σ
        (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((O.map π).map σ) with h | h
    · exact h
    · exfalso
      have hpg : IsPGroup p ((O.map π).map σ) := (pCore_isPGroup.map π).map σ
      rw [h] at hpg
      have hpg' : IsPGroup p (Q ⧸ Subgroup.center Q) := hpg.of_equiv Subgroup.topEquiv
      have := hpg'.isNilpotent
      have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := Q ⧸ Subgroup.center Q)).mpr
        inferInstance
      exact hab₀ (hcomm a₀ b₀)
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro k
  have hc : ⁅o, k⁆ ∈ N := by
    have hπo : π o ∈ Subgroup.center Q := by
      have hmem : σ (π o) ∈ (O.map π).map σ := ⟨π o, ⟨o, ho, rfl⟩, rfl⟩
      rw [hOσ, Subgroup.mem_bot] at hmem
      rw [← QuotientGroup.ker_mk' (Subgroup.center Q)]
      exact hmem
    rw [← QuotientGroup.eq_one_iff (N := N), ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hπo (π k)).symm
  have hcO : ⁅o, k⁆ ∈ O := by
    have := mul_mem ho ((pCore_normal (p := p) (G := K)).conj_mem o⁻¹ (inv_mem ho) k)
    simpa [commutatorElement_def, mul_assoc] using this
  have hdis : Disjoint O N := by
    rw [Subgroup.disjoint_def]
    intro z hzO hzN
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := K)) ⟨z, hzO⟩
    have hz : z ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hdvd : orderOf z ∣ p ^ n := orderOf_dvd_of_pow_eq_one hz
    have hNp := (solvable_prime_complement_core_characterization (H := K) hp).2.2.1
    have hcop : Nat.Coprime (orderOf z) (Nat.card N) :=
      Nat.Coprime.coprime_dvd_left hdvd
        (Nat.Coprime.pow_left n ((hp.coprime_iff_not_dvd).mpr hNp))
    rw [← orderOf_eq_one_iff]
    exact Nat.Coprime.eq_one_of_dvd hcop (Subgroup.orderOf_dvd_natCard N hzN)
  have h1 : ⁅o, k⁆ = 1 := Subgroup.disjoint_def.mp hdis hcO hc
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem local_theta_components_centralize_normal_aux {H : Type*} [Group H]
    [Finite H] {p : ℕ} (hp : p.Prime) {x : H} (hx : ∃ n : ℕ, orderOf x = p ^ n)
    {C : Subgroup H} (hC : C = Subgroup.centralizer ({x} : Set H)) {Y : Subgroup C}
    (hY : Y ∈ thetaComponents p C) {R : Subgroup H} (hRn : R.Normal) (hR : IsPGroup p R) :
    pCore p Y ≤ Subgroup.center Y ∧ ⁅Y.map C.subtype, R⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hOZ : pCore p Y ≤ Subgroup.center Y :=
    pCore_le_center_of_isQuasisimple_thetaQuotient hp hY.2.2
  refine ⟨hOZ, ?_⟩
  set R' : Subgroup C := R.subgroupOf C
  have hR'p : IsPGroup p R' := hR.comap_of_injective _ C.subtype_injective
  have hR'n : R'.Normal := hRn.comap C.subtype
  have hYperf : ⁅Y, Y⁆ = Y := Subgroup.isPerfect_iff.mp hY.1
  obtain ⟨-, hYR'⟩ := Quasithin.SteinbergBM.perfect_subnormal_p_signalizer_action hp hYperf
    hY.2.1 hR'p ((Subgroup.normalizer_eq_top (H := R')).ge.trans' le_top)
  have hYR'Z : ⁅Y, R'⁆ ≤ (Subgroup.center Y).map Y.subtype :=
    hYR'.trans (Subgroup.map_mono hOZ)
  have hYR'bot : ⁅Y, R'⁆ = ⊥ := by
    refine LocalCores.perfect_double_commutator hY.1 ?_
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro c hc y hy
    obtain ⟨z, hz, rfl⟩ := hYR'Z hc
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩).symm
  have hcentr : ∀ y : Y, ¬ p ∣ orderOf y → ((y : C) : H) ∈ Subgroup.centralizer (R : Set H) := by
    intro y hy
    set yH : H := ((y : C) : H)
    have hyx : yH * x = x * yH := by
      have h : yH ∈ Subgroup.centralizer ({x} : Set H) := by
        rw [← hC]
        exact (y : C).2
      exact Subgroup.mem_centralizer_singleton_iff.mp h
    have hoy : orderOf yH = orderOf y := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    let α : Subgroup.zpowers yH →* MulAut R :=
      (MulAut.conjNormal (H := R)).comp (Subgroup.zpowers yH).subtype
    let β : Subgroup.zpowers x →* MulAut R :=
      (MulAut.conjNormal (H := R)).comp (Subgroup.zpowers x).subtype
    have hαapp : ∀ (a : Subgroup.zpowers yH) (r : R), ((α a r : R) : H) = a * r * (a : H)⁻¹ :=
      fun _ _ => rfl
    have hβapp : ∀ (b : Subgroup.zpowers x) (r : R), ((β b r : R) : H) = b * r * (b : H)⁻¹ :=
      fun _ _ => rfl
    have hAp : ¬ p ∣ Nat.card (Subgroup.zpowers yH) := by rwa [Nat.card_zpowers, hoy]
    have hBp : IsPGroup p (Subgroup.zpowers x) := by
      obtain ⟨n, hn⟩ := hx
      exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
    have hab : ∀ (a : Subgroup.zpowers yH) (b : Subgroup.zpowers x),
        (a : H) * (b : H) = (b : H) * (a : H) := by
      intro a b
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      rw [← hi, ← hj]
      exact ((Commute.zpow_zpow (show Commute yH x from hyx) i j))
    have hcomm : ∀ a b, α a * β b = β b * α a := by
      intro a b
      ext r
      simp only [MulAut.mul_apply]
      rw [hαapp, hβapp, hβapp, hαapp]
      have h1 := hab a b
      calc (a : H) * ((b : H) * (r : H) * (b : H)⁻¹) * (a : H)⁻¹
          = ((a : H) * (b : H)) * r * ((a : H) * (b : H))⁻¹ := by group
        _ = ((b : H) * (a : H)) * r * ((b : H) * (a : H))⁻¹ := by rw [h1]
        _ = (b : H) * ((a : H) * (r : H) * (a : H)⁻¹) * (b : H)⁻¹ := by group
    have hfix : ∀ a r, (∀ b, β b r = r) → α a r = r := by
      intro a r hr
      have hrx : (r : H) ∈ C := by
        have h := congrArg Subtype.val (hr ⟨x, Subgroup.mem_zpowers x⟩)
        rw [hβapp] at h
        rw [hC, Subgroup.mem_centralizer_singleton_iff]
        calc (r : H) * x = x * r * x⁻¹ * x := by rw [h]
          _ = x * r := by group
      have hrR' : (⟨r, hrx⟩ : C) ∈ R' := r.2
      have hyr : (y : C) * ⟨r, hrx⟩ = ⟨r, hrx⟩ * (y : C) := by
        have h := Subgroup.commutator_mem_commutator y.2 hrR'
        rw [hYR'bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
        exact h
      have hyr' : yH * r = r * yH := congrArg Subtype.val hyr
      apply Subtype.ext
      rw [hαapp]
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      rw [← hi]
      have : Commute (yH ^ i) (r : H) := (show Commute yH r from hyr').zpow_left i
      rw [this.eq]
      group
    have hall := GroupTheory.thompson_A_times_B (hR := hR) hAp hBp α β hcomm hfix
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h := congrArg (fun φ : MulAut R => ((φ ⟨r, hr⟩ : R) : H))
      (hall ⟨yH, Subgroup.mem_zpowers yH⟩)
    simp only [MulAut.one_apply] at h
    rw [hαapp] at h
    calc r * yH = yH * r * yH⁻¹ * yH := by rw [h]
      _ = yH * r := by group
  set N : Subgroup Y :=
    (Subgroup.centralizer (R : Set H)).comap (C.subtype.comp Y.subtype) with hN
  have : (Subgroup.centralizer (R : Set H)).Normal := Subgroup.normal_centralizer (H := R)
  have hNn : N.Normal := Subgroup.Normal.comap inferInstance _
  have hNall : ∀ y : Y, ¬ p ∣ orderOf y → y ∈ N := fun y hy => hcentr y hy
  have hQp := Glauberman.isPGroup_quotient_of_pPrime_order_elements_mem N hNall
  have : Group.IsNilpotent (Y ⧸ N) := hQp.isNilpotent
  have hperf : Group.IsPerfect Y := hY.1
  have hQperf : ⁅(⊤ : Subgroup (Y ⧸ N)), (⊤ : Subgroup (Y ⧸ N))⁆ = ⊤ := by
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hQbot := Quasithin.SteinbergBM.eq_bot_of_commutator_self_eq_of_isSolvable hQperf
  rw [eq_bot_iff, Subgroup.commutator_le]
  rintro _ ⟨y, hy, rfl⟩ r hr
  have hyN : (⟨y, hy⟩ : Y) ∈ N := by
    rw [← QuotientGroup.eq_one_iff (N := N)]
    have : ((⟨y, hy⟩ : Y) : Y ⧸ N) ∈ (⊤ : Subgroup (Y ⧸ N)) := Subgroup.mem_top _
    rwa [hQbot, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_iff.mp hyN r hr).symm

theorem local_theta_components_centralize_normal_defining_prime_subgroups {H : Type*} [Group H]
    [Finite H] {p : ℕ} (hp : p.Prime) {x : H} (hx : ∃ n : ℕ, orderOf x = p ^ n)
    {Y : Subgroup (Subgroup.centralizer ({x} : Set H))}
    (hY : Y ∈ thetaComponents p (Subgroup.centralizer ({x} : Set H))) {R : Subgroup H}
    (hRn : R.Normal) (hR : IsPGroup p R) :
    pCore p Y ≤ Subgroup.center Y ∧
      ⁅Y.map (Subgroup.centralizer ({x} : Set H)).subtype, R⁆ = ⊥ :=
  local_theta_components_centralize_normal_aux hp hx rfl hY hRn hR

end CFSG.RankThree.GroupTheory.SteinbergBY
