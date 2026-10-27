module

public import CFSG.GH74.Uniqueness.Section163Gen
public import CFSG.RankThree.GF2n.Tim79aSec23One

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

private theorem eq_one_of_mem_of_mem_of_odd {K : Type*} [Group K] {P N : Subgroup K}
    (hN : Odd (Nat.card N)) (hP : IsPGroup 2 P) {x : K} (hxP : x ∈ P) (hxN : x ∈ N) :
    x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have h1 : orderOf x ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    simpa using congrArg Subtype.val hk
  have h2 : orderOf x ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
    simpa [Subgroup.orderOf_mk] using this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2))

theorem centralizes_of_isTI_of_kleinFour {K : Type*} [Group K] [Finite K] {P N : Subgroup K}
    [N.Normal] (hN : Odd (Nat.card N)) (hP : IsPGroup 2 P)
    (hTI : ∀ k : K, P ⊓ conjSubgroup k P = ⊥ ∨ k ∈ Subgroup.normalizer (P : Set K))
    {a b : K} (ha : a ∈ P) (hb : b ∈ P) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    N ≤ Subgroup.centralizer (P : Set K) := by
  have hY4 : Nat.card (CFSG.GH74.Uniqueness.fourSub a b ha2 hb2 hab) = 4 :=
    CFSG.GH74.Uniqueness.card_fourSub ha1 hb1 hne
  have hYP : CFSG.GH74.Uniqueness.fourSub a b ha2 hb2 hab ≤ P :=
    CFSG.GH74.Uniqueness.fourSub_le ha hb
  have hYN : CFSG.GH74.Uniqueness.fourSub a b ha2 hb2 hab ≤
      Subgroup.normalizer (N : Set K) := fun y _ => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top y
  refine CFSG.GH74.Uniqueness.le_of_inf_centralizer_le_of_four hN hY4
    CFSG.GH74.Uniqueness.mul_self_of_mem_fourSub hYN fun w hw hw1 n hn => ?_
  obtain ⟨hnw, hnN⟩ := Subgroup.mem_inf.mp hn
  have hnw' : n * w = w * n := Subgroup.mem_centralizer_singleton_iff.mp hnw
  have hnP : n ∈ Subgroup.normalizer (P : Set K) := by
    rcases hTI n with hbot | hmem
    · exfalso
      have hw' : w ∈ P ⊓ conjSubgroup n P := by
        refine ⟨hYP hw, mem_conjSubgroup.mpr ?_⟩
        have : n⁻¹ * w * n = w := by
          calc n⁻¹ * w * n = n⁻¹ * (w * n) := by group
            _ = n⁻¹ * (n * w) := by rw [hnw']
            _ = w := by group
        rw [this]
        exact hYP hw
      rw [hbot, Subgroup.mem_bot] at hw'
      exact hw1 hw'
    · exact hmem
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hP1 : n * p * n⁻¹ * p⁻¹ ∈ P :=
    P.mul_mem ((Subgroup.mem_normalizer_iff.mp hnP p).mp hp) (P.inv_mem hp)
  have hN1 : n * p * n⁻¹ * p⁻¹ ∈ N := by
    have h := N.mul_mem hnN (Subgroup.Normal.conj_mem ‹N.Normal› _ (N.inv_mem hnN) p)
    simpa [mul_assoc] using h
  have h1 := eq_one_of_mem_of_mem_of_odd hN hP hP1 hN1
  have h2 : n * p * n⁻¹ = p := mul_inv_eq_one.mp h1
  calc p * n = n * p * n⁻¹ * n := by rw [h2]
    _ = n * p := by group

section ActionOnW

private def actW {G : Type} [Group G] (V H : Subgroup G) :
    ↥H →* MulAut ↥((wOf V H).subgroupOf H) :=
  MulAut.conjNormal

private abbrev ActImage {G : Type} [Group G] (V H : Subgroup G) : Type := ↥(actW V H).range

private def actPi {G : Type} [Group G] (V H : Subgroup G) : ↥H →* ActImage V H :=
  (actW V H).rangeRestrict

private theorem actPi_surjective {G : Type} [Group G] (V H : Subgroup G) :
    Function.Surjective (actPi V H) :=
  (actW V H).rangeRestrict_surjective

private theorem actPi_eq_iff {G : Type} [Group G] {V H : Subgroup G} {x y : ↥H} :
    actPi V H x = actPi V H y ↔
      ∀ w ∈ wOf V H, (x : G) * w * (x : G)⁻¹ = (y : G) * w * (y : G)⁻¹ := by
  constructor
  · intro h w hw
    have h1 : actW V H x = actW V H y := congrArg Subtype.val h
    have h2 := congrArg (fun f : MulAut ↥((wOf V H).subgroupOf H) =>
      (((f ⟨⟨w, wOf_le_H V H hw⟩, Subgroup.mem_subgroupOf.mpr hw⟩ : ↥((wOf V H).subgroupOf H))
        : ↥H) : G)) h1
    simpa [actW, MulAut.conjNormal_apply] using h2
  · intro h
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    apply Subtype.ext
    simp only [actW, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    exact h _ (Subgroup.mem_subgroupOf.mp w.2)

private theorem actPi_eq_one_iff {G : Type} [Group G] {V H : Subgroup G} {x : ↥H} :
    actPi V H x = 1 ↔ ∀ w ∈ wOf V H, (x : G) * w = w * (x : G) := by
  have h1 : actPi V H x = 1 ↔ actPi V H x = actPi V H 1 := by rw [map_one]
  rw [h1, actPi_eq_iff]
  refine forall₂_congr fun _ _ => ?_
  simp only [Subgroup.coe_one, one_mul, inv_one, mul_one]
  constructor
  · intro h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  · intro h
    rw [h, mul_inv_cancel_right]

private theorem actPi_comm_of_comm {G : Type} [Group G] {V H : Subgroup G} {a b : ↥H}
    (h : (a : G) * b = b * a) : actPi V H a * actPi V H b = actPi V H b * actPi V H a := by
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h

end ActionOnW

namespace MinCex

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G] (hc : MinCex M V Q P H)
include hc

private theorem actPi_eq_one_of_mem_wOf {x : ↥H} (hx : (x : G) ∈ wOf V H) : actPi V H x = 1 :=
  actPi_eq_one_iff.mpr fun _ hw => hc.wOf_isElemAbelian.comm hx hw

private theorem exists_actLift :
    ∃ φ : Hbar V H →* ActImage V H, ∀ x : ↥H, φ (piBar V H x) = actPi V H x := by
  have hle : (wOf V H).subgroupOf H ≤ (actPi V H).ker := fun _ hx =>
    (actPi V H).mem_ker.mpr (hc.actPi_eq_one_of_mem_wOf (Subgroup.mem_subgroupOf.mp hx))
  exact ⟨QuotientGroup.lift _ (actPi V H) hle, fun x => QuotientGroup.lift_mk _ hle x⟩

private theorem isPGroup_actPi_P : IsPGroup 2 ↥((P.subgroupOf H).map (actPi V H)) :=
  IsPGroup.map hc.isPGroup_P.comap_subtype _

private theorem actPi_TI
    (hTI : ∀ g ∈ H, conjSubgroup g V ≠ V → ∀ x ∈ P, ∀ y ∈ conjSubgroup g P,
      (∀ w ∈ wOf V H, x * w * x⁻¹ = y * w * y⁻¹) → ∀ w ∈ wOf V H, x * w = w * x)
    (k : ActImage V H) :
    (P.subgroupOf H).map (actPi V H) ⊓ conjSubgroup k ((P.subgroupOf H).map (actPi V H)) = ⊥ ∨
      k ∈ Subgroup.normalizer (((P.subgroupOf H).map (actPi V H) : Subgroup (ActImage V H)) :
        Set (ActImage V H)) := by
  obtain ⟨h, rfl⟩ := actPi_surjective V H k
  by_cases hV : conjSubgroup (h : G) V = V
  · right
    have hM : (h : G) ∈ M := hc.normalizer_eq ▸ mem_normalizer_iff_conjSubgroup_eq.mpr hV
    have key : ∀ h' : ↥H, (h' : G) ∈ Subgroup.normalizer (P : Set G) →
        ∀ z ∈ (P.subgroupOf H).map (actPi V H),
          actPi V H h' * z * (actPi V H h')⁻¹ ∈ (P.subgroupOf H).map (actPi V H) := by
      intro h' hh' z hz
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
      refine Subgroup.mem_map.mpr ⟨h' * x * h'⁻¹, ?_, by simp [map_mul, map_inv]⟩
      rw [Subgroup.mem_subgroupOf]
      simpa using (Subgroup.mem_normalizer_iff.mp hh' (x : G)).mp (Subgroup.mem_subgroupOf.mp hx)
    have hP : (h : G) ∈ Subgroup.normalizer (P : Set G) := hc.M_le_normalizer_P hM
    have hPinv : ((h⁻¹ : ↥H) : G) ∈ Subgroup.normalizer (P : Set G) := by
      rw [Subgroup.coe_inv]
      exact Subgroup.inv_mem _ hP
    refine Subgroup.mem_normalizer_iff.mpr fun z => ⟨key h hP z, fun hz => ?_⟩
    have := key h⁻¹ hPinv _ hz
    rw [map_inv] at this
    have e : (actPi V H h)⁻¹ * (actPi V H h * z * (actPi V H h)⁻¹) * ((actPi V H h)⁻¹)⁻¹ = z := by
      group
    rwa [e] at this
  · left
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzP, hzc⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hzP
    rw [mem_conjSubgroup] at hzc
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hzc
    have hxy : actPi V H x = actPi V H (h * y * h⁻¹) := by
      rw [map_mul, map_mul, map_inv, hyz]
      group
    have hyc : (h : G) * y * (h : G)⁻¹ ∈ conjSubgroup (h : G) P := by
      rw [mem_conjSubgroup]
      have e : (h : G)⁻¹ * ((h : G) * y * (h : G)⁻¹) * (h : G) = y := by group
      rw [e]
      exact Subgroup.mem_subgroupOf.mp hy
    have hxy' : ∀ w ∈ wOf V H, (x : G) * w * (x : G)⁻¹ =
        ((h : G) * y * (h : G)⁻¹) * w * ((h : G) * y * (h : G)⁻¹)⁻¹ := by
      simpa using actPi_eq_iff.mp hxy
    exact Subgroup.mem_bot.mpr (actPi_eq_one_iff.mpr
      (hTI (h : G) h.2 hV (x : G) (Subgroup.mem_subgroupOf.mp hx) _ hyc hxy'))

private theorem actPi_commute_of_central
    (hX : barOf V H (xOf V H) = oddCoreX V H ⊔ barOf V H V)
    {φ : Hbar V H →* ActImage V H} (hφ : ∀ x : ↥H, φ (piBar V H x) = actPi V H x)
    (hN : (oddCoreX V H).map φ ≤ Subgroup.centralizer
      (((P.subgroupOf H).map (actPi V H) : Subgroup (ActImage V H)) : Set (ActImage V H)))
    {v : ↥H} (hv : (v : G) ∈ V) (h : ↥H) :
    Commute (actPi V H h) (actPi V H v) := by
  haveI := normal_oddCoreX V H
  have hhX : (h : G) ∈ xOf V H ⊔ P := by rw [hc.xOf_sup_P_eq_H]; exact h.2
  obtain ⟨x, hx, p, hp, hxp⟩ := exists_mul_of_mem_sup
    (fun _ hp => H_le_normalizer_xOf V H (hc.PleH hp)) hhX
  have hxH : x ∈ H := xOf_le_H hc.V_le_H hx
  have hpH : p ∈ H := hc.PleH hp
  have hh : h = ⟨x, hxH⟩ * ⟨p, hpH⟩ := Subtype.ext hxp
  have hpv : Commute (actPi V H ⟨p, hpH⟩) (actPi V H v) :=
    actPi_comm_of_comm (hc.commute_of_mem_P hp hv).symm
  have hxb : piBar V H ⟨x, hxH⟩ ∈ oddCoreX V H ⊔ barOf V H V := by
    rw [← hX]
    exact mem_barOf_iff.mpr ⟨⟨x, hxH⟩, hx, rfl⟩
  obtain ⟨o, ho, _, hu, hou⟩ := Subgroup.mem_sup_of_normal_left.mp hxb
  obtain ⟨v', hv', rfl⟩ := mem_barOf_iff.mp hu
  have hxπ : actPi V H ⟨x, hxH⟩ = φ o * actPi V H v' := by
    rw [← hφ, ← hou, map_mul, hφ]
  have hvPt : actPi V H v ∈ (P.subgroupOf H).map (actPi V H) :=
    Subgroup.mem_map.mpr ⟨v, Subgroup.mem_subgroupOf.mpr (hc.V_le_P hv), rfl⟩
  have hov : Commute (φ o) (actPi V H v) :=
    (Subgroup.mem_centralizer_iff.mp (hN (Subgroup.mem_map.mpr ⟨o, ho, rfl⟩)) _ hvPt).symm
  have hv'v : Commute (actPi V H v') (actPi V H v) :=
    actPi_comm_of_comm (hc.elemAb.comm hv' hv)
  rw [hh, map_mul, hxπ]
  exact (hov.mul_left hv'v).mul_left hpv

theorem act_eq_of_sq_central (hq : Nat.card (barOf V H V) = 2)
    (hX : barOf V H (xOf V H) = oddCoreX V H ⊔ barOf V H V)
    (hEx : ∃ g ∈ H, conjSubgroup g V ≠ V)
    (hTI : ∀ g ∈ H, conjSubgroup g V ≠ V → ∀ x ∈ P, ∀ y ∈ conjSubgroup g P,
      (∀ w ∈ wOf V H, x * w * x⁻¹ = y * w * y⁻¹) → ∀ w ∈ wOf V H, x * w = w * x)
    (hfree : ∀ g ∈ H, conjSubgroup g V ≠ V → ∀ v ∈ V, v ∉ wOf V H →
      ∀ b ∈ conjSubgroup g V, b ≠ 1 → v * b ≠ b * v)
    {t : G} (ht : t ∈ P) (ht2 : ∀ w ∈ wOf V H, t * t * w = w * (t * t)) :
    ∃ v ∈ V, ∀ w ∈ wOf V H, t * w * t⁻¹ = v * w * v⁻¹ := by
  have _ := hq
  by_contra hcon
  push Not at hcon
  obtain ⟨φ, hφ⟩ := hc.exists_actLift
  obtain ⟨v₀, hv₀V, hv₀W⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
  have hv₀H : v₀ ∈ H := hc.V_le_H hv₀V
  have htH : t ∈ H := hc.PleH ht
  obtain ⟨g₀, hg₀H, hg₀V⟩ := hEx
  obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hc.conj_inf_wOf_ne_bot hg₀H)
  obtain ⟨hb₀U, hb₀W⟩ := Subgroup.mem_inf.mp hb₀
  have hb₀1' : b₀ ≠ 1 := fun h => hb₀1 (Subtype.ext h)
  have hfree₀ := hfree g₀ hg₀H hg₀V v₀ hv₀V hv₀W b₀ hb₀U hb₀1'
  set v₀' : ↥H := ⟨v₀, hv₀H⟩
  set t' : ↥H := ⟨t, htH⟩
  have haPt : actPi V H v₀' ∈ (P.subgroupOf H).map (actPi V H) :=
    Subgroup.mem_map.mpr ⟨v₀', Subgroup.mem_subgroupOf.mpr (hc.V_le_P hv₀V), rfl⟩
  have hbPt : actPi V H t' ∈ (P.subgroupOf H).map (actPi V H) :=
    Subgroup.mem_map.mpr ⟨t', Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have ha1 : actPi V H v₀' ≠ 1 := fun h => hfree₀ (actPi_eq_one_iff.mp h b₀ hb₀W)
  have hb1 : actPi V H t' ≠ 1 := fun h => by
    obtain ⟨w, hw, hne⟩ := hcon 1 V.one_mem
    apply hne
    have := actPi_eq_one_iff.mp h w hw
    simp only [inv_one, one_mul, mul_one]
    exact mul_inv_eq_iff_eq_mul.mpr this
  have ha2 : actPi V H v₀' * actPi V H v₀' = 1 := by
    rw [← map_mul]
    have : v₀' * v₀' = 1 := Subtype.ext (hc.elemAb.mul_self_eq_one hv₀V)
    rw [this, map_one]
  have hb2 : actPi V H t' * actPi V H t' = 1 := by
    rw [← map_mul]
    exact actPi_eq_one_iff.mpr ht2
  have hab : actPi V H v₀' * actPi V H t' = actPi V H t' * actPi V H v₀' :=
    actPi_comm_of_comm (hc.commute_of_mem_P ht hv₀V)
  have hne : actPi V H v₀' ≠ actPi V H t' := fun h => by
    obtain ⟨w, hw, hne⟩ := hcon v₀ hv₀V
    exact hne (actPi_eq_iff.mp h w hw).symm
  haveI : ((oddCoreX V H).map φ).Normal := by
    refine (normal_oddCoreX V H).map φ ?_
    intro k
    obtain ⟨x, rfl⟩ := actPi_surjective V H k
    exact ⟨piBar V H x, hφ x⟩
  have hNodd : Odd (Nat.card ((oddCoreX V H).map φ)) :=
    Odd.of_dvd_nat (odd_card_oddCoreX V H) (Subgroup.card_map_dvd _ _)
  have hNC := centralizes_of_isTI_of_kleinFour (K := ActImage V H)
    (P := (P.subgroupOf H).map (actPi V H)) (N := (oddCoreX V H).map φ) hNodd
    hc.isPGroup_actPi_P (hc.actPi_TI hTI) haPt hbPt ha2 hb2 hab ha1 hb1 hne
  have hg := (hc.actPi_commute_of_central hX hφ hNC (v := v₀') hv₀V ⟨g₀, hg₀H⟩).eq
  have hconj : actPi V H (⟨g₀, hg₀H⟩ * v₀' * ⟨g₀, hg₀H⟩⁻¹) = actPi V H v₀' := by
    rw [map_mul, map_mul, map_inv, hg]
    group
  have hact : (g₀ * v₀ * g₀⁻¹) * b₀ * (g₀ * v₀ * g₀⁻¹)⁻¹ = v₀ * b₀ * v₀⁻¹ :=
    actPi_eq_iff.mp hconj b₀ hb₀W
  have hu₀ : g₀ * v₀ * g₀⁻¹ ∈ conjSubgroup g₀ V := by
    rw [mem_conjSubgroup]
    have e : g₀⁻¹ * (g₀ * v₀ * g₀⁻¹) * g₀ = v₀ := by group
    rw [e]
    exact hv₀V
  have hcb : (g₀ * v₀ * g₀⁻¹) * b₀ = b₀ * (g₀ * v₀ * g₀⁻¹) :=
    (isElemAbelian_conjSubgroup hc.elemAb g₀).comm hu₀ hb₀U
  have h1 : (g₀ * v₀ * g₀⁻¹) * b₀ * (g₀ * v₀ * g₀⁻¹)⁻¹ = b₀ := by
    rw [hcb]
    group
  exact hfree₀ (mul_inv_eq_iff_eq_mul.mp (hact.symm.trans h1))

end MinCex

end CFSG.RankThree.GF2n.Tim79a
