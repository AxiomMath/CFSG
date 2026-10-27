module

public import CFSG.RankThree.PartTwo.Sec12.Item125Basic
public import CFSG.RankThree.PartTwo.KFacts.KS12OrderNine
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev thetaBarAct (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
  (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom

theorem thetaBarAct_mk {L : Subgroup G} (g : Subgroup.normalizer (L : Set G)) (y : L) :
    thetaBarAct L g (QuotientGroup.mk' (aschbacherSolvableCore 3 L) y) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) (L.normalizerMonoidHom g y) :=
  rfl

theorem mem_thetaQuotCentralizer_iff_thetaBarAct {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    x ∈ Sec4.thetaQuotCentralizer L ↔ thetaBarAct L ⟨x, hx⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro h1
    exact ⟨⟨x, hx⟩, h1, rfl⟩

theorem thetaBarAct_of_mem {L : Subgroup G} {l : G} (hl : l ∈ L) :
    thetaBarAct L ⟨l, Subgroup.le_normalizer hl⟩ =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l, hl⟩) := by
  ext yb
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) yb
  rw [thetaBarAct_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

omit [Finite G] in
theorem mem_center_of_conj_eq_one {X : Type*} [Group X] {a : X} (h : MulAut.conj a = 1) :
    a ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 := congrArg (fun σ : MulAut X => σ y) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc y * a = (a * y * a⁻¹) * a := by rw [h1]
    _ = a * y := by group

omit [Finite G] in
theorem conj_eq_one_of_mem_center {X : Type*} [Group X] {a : X} (h : a ∈ Subgroup.center X) :
    MulAut.conj a = 1 := by
  ext y
  rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp h y, mul_inv_cancel_right]

theorem exists_lift_fixed {L E : Subgroup G} (hE3 : IsPGroup 3 E)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) (yb : L ⧸ aschbacherSolvableCore 3 L)
    (hfix : ∀ d (hd : d ∈ E), thetaBarAct L ⟨d, hEN hd⟩ yb = yb) :
    ∃ y : L, QuotientGroup.mk' (aschbacherSolvableCore 3 L) y = yb ∧
      ∀ d ∈ E, d * (y : G) * d⁻¹ = y := by
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) yb
  have hfix' : ∀ d ∈ E, (y₀ : G)⁻¹ * (d * y₀ * d⁻¹) ∈
      inSubgroup (aschbacherSolvableCore 3) L := by
    intro d hd
    have h1 := (hfix d hd).symm
    rw [thetaBarAct_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    exact ⟨_, h1, rfl⟩
  obtain ⟨n, hn, hn'⟩ := exists_fixed_lift hE3 hEN hfix'
  refine ⟨⟨y₀ * n, L.mul_mem y₀.2 (Subgroup.map_subtype_le _ hn)⟩, ?_, hn'⟩
  obtain ⟨n', hn'N, rfl⟩ := hn
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have h1 : ∀ h, (⟨(y₀ : G) * L.subtype n', h⟩ : L)⁻¹ * y₀ = n'⁻¹ := fun h =>
    Subtype.ext (by simp)
  rw [h1]
  exact inv_mem hn'N

theorem eq_of_card_nine_lt {E S T : Subgroup G} (hE : Nat.card E = 27) (hSE : S ≤ E)
    (hTS : T ≤ S) (hT : Nat.card T = 9) {x : G} (hxS : x ∈ S) (hxT : x ∉ T) : S = E := by
  have hdvd : Nat.card S ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE]
    exact Subgroup.card_dvd_of_le hSE
  have h9 : 9 ∣ Nat.card S := hT ▸ Subgroup.card_dvd_of_le hTS
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  refine Subgroup.eq_of_le_of_card_ge hSE ?_
  interval_cases k
  · rw [hk] at h9
    norm_num at h9
  · rw [hk] at h9
    norm_num at h9
  · exfalso
    have hST : T = S := Subgroup.eq_of_le_of_card_ge hTS (by rw [hk, hT]; norm_num)
    exact hxT (hST ▸ hxS)
  · rw [hk, hE]
    norm_num

theorem false_of_card_inf_L_eq_three (hK9 : KFacts.KS12OrderNine)
    (hFE : partTwoF G = partTwoE G) {c : G} {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c)
    (hcL : c ∈ L) (hc1 : c ≠ 1)
    (hty : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {E : Subgroup G} (hE : Late.IsE27 E) (hEL : E ≤ lcBar c L) (hcE : c ∈ E)
    (hB9 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9)
    (hEL3 : Nat.card (E ⊓ L : Subgroup G) = 3) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 L with hN
  set π := QuotientGroup.mk' N with hπ
  have hX := isQuasisimple_thetaQuot_of_mem hL
  have hperf : commutator (L ⧸ N) = ⊤ := by
    have h := hX.1
    rwa [Group.isPerfect_def] at h
  have hZ : Nat.card (Subgroup.center (L ⧸ N)) = 3 := by
    rcases hty with hSL | hA6 | hA7 | hM22
    · exact card_center_eq_three_of_isSLThreePi hSL
    · exact hA6.1
    · exact hA7.1
    · exact hM22.1
  have hev := KFacts.two_dvd_card_of_item122_type hty
  have hexpE : ∀ x ∈ E, x ^ 3 = 1 := hE.1.2
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hexpE x x.2)⟩
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEL.trans (lcBar_le_normalizer hL)
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexpE c hcE) hc1
  have hELc : E ⊓ L = Subgroup.zpowers c :=
    (Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (show c ∈ E ⊓ L from Subgroup.mem_inf.mpr ⟨hcE, hcL⟩))
      (by rw [hEL3, Nat.card_zpowers, hc3])).symm
  have hELC : ∀ w ∈ E, ∀ hwL : w ∈ L, π ⟨w, hwL⟩ ∈ Subgroup.center (L ⧸ N) := by
    intro w hwE hwL
    have hw : w ∈ Subgroup.zpowers c := by
      rw [← hELc]
      exact Subgroup.mem_inf.mpr ⟨hwE, hwL⟩
    have hcC : Subgroup.zpowers c ≤ Sec4.thetaQuotCentralizer L :=
      Subgroup.zpowers_le.mpr (mem_thetaQuotCentralizer_of_central hcL hLc)
    exact mk_mem_center_of_mem_thetaQuotCentralizer (hcC hw)
  obtain ⟨e, heE, heC⟩ : ∃ e ∈ E, e ∉ Sec4.thetaQuotCentralizer L := by
    by_contra hcon
    push Not at hcon
    have h1 : E ⊓ Sec4.thetaQuotCentralizer L = E := inf_eq_left.mpr hcon
    rw [h1, hE.2] at hB9
    norm_num at hB9
  obtain ⟨l, hl, z, hz, hlz⟩ := exists_mul_of_mem_lcBar hL (hEL heE)
  set xb : L ⧸ N := π ⟨l, hl⟩ with hxb
  have hφe : thetaBarAct L ⟨e, hEN heE⟩ = MulAut.conj xb := by
    have hzN := thetaQuotCentralizer_le_normalizer' L hz
    have h1 : (⟨e, hEN heE⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨l, Subgroup.le_normalizer hl⟩ * ⟨z, hzN⟩ := Subtype.ext hlz
    rw [h1, map_mul, thetaBarAct_of_mem hl, (mem_thetaQuotCentralizer_iff_thetaBarAct hzN).mp hz,
      mul_one]
  have hBN : Subgroup.zpowers e ≤
      Subgroup.normalizer ((E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun b hb => ?_
    rw [hcommE e heE b hb.1, mul_inv_cancel_right]
    exact hb
  have hEsup : Subgroup.zpowers e ⊔ (E ⊓ Sec4.thetaQuotCentralizer L) = E :=
    eq_of_card_nine_lt hE.2 (sup_le (Subgroup.zpowers_le.mpr heE) inf_le_left) le_sup_right hB9
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers e)) fun h => heC h.2
  have hact : ∀ g (hg : g ∈ E), ∃ k : ℤ, thetaBarAct L ⟨g, hEN hg⟩ = MulAut.conj (xb ^ k) := by
    intro g hg
    have hg' : g ∈ ((Subgroup.zpowers e ⊔ (E ⊓ Sec4.thetaQuotCentralizer L) : Subgroup G) :
        Set G) := by
      rw [hEsup]
      exact hg
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBN] at hg'
    obtain ⟨w, hw, b, hb, hwb⟩ := hg'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    refine ⟨k, ?_⟩
    have hbN := thetaQuotCentralizer_le_normalizer' L hb.2
    have h1 : (⟨g, hEN hg⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨e, hEN heE⟩ : Subgroup.normalizer (L : Set G)) ^ k * ⟨b, hbN⟩ :=
      Subtype.ext (by change g = _; rw [← hwb]; simp)
    rw [h1, map_mul, map_zpow, hφe, (mem_thetaQuotCentralizer_iff_thetaBarAct hbN).mp hb.2,
      mul_one, map_zpow]
  have hfixb : ∀ yb : L ⧸ N, yb * xb = xb * yb →
      ∀ g (hg : g ∈ E), thetaBarAct L ⟨g, hEN hg⟩ yb = yb := by
    intro yb hyb g hg
    obtain ⟨k, hk⟩ := hact g hg
    have hc : Commute (xb ^ k) yb := Commute.zpow_left hyb.symm k
    rw [hk, MulAut.conj_apply, hc.eq, mul_inv_cancel_right]
  have hxZ : xb ∉ Subgroup.center (L ⧸ N) := by
    intro hxZ
    apply heC
    rw [mem_thetaQuotCentralizer_iff_thetaBarAct (hEN heE), hφe]
    exact conj_eq_one_of_mem_center hxZ
  have hx3Z : xb ^ 3 ∈ Subgroup.center (L ⧸ N) := by
    have h1 : (⟨e, hEN heE⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hexpE e heE)
    have h2 := congrArg (thetaBarAct L) h1
    rw [map_pow, map_one, hφe, ← map_pow] at h2
    exact mem_center_of_conj_eq_one h2
  have hx9 : xb ^ 9 = 1 := by
    have h1 : (⟨xb ^ 3, hx3Z⟩ : Subgroup.center (L ⧸ N)) ^ 3 = 1 := by
      have h0 : (⟨xb ^ 3, hx3Z⟩ : Subgroup.center (L ⧸ N)) ^
          Nat.card (Subgroup.center (L ⧸ N)) = 1 := pow_card_eq_one'
      rwa [hZ] at h0
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rw [← pow_mul] at h2
    exact h2
  have hord : orderOf xb = 3 ∨ orderOf xb = 9 := by
    have hd : orderOf xb ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one hx9
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    interval_cases k
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hxZ (hk ▸ Subgroup.one_mem _)
    · left
      rw [hk, pow_one]
    · right
      rw [hk]
      norm_num
  rcases hord with h3 | h9
  ·
    obtain ⟨y, hy, hyfix⟩ := exists_lift_fixed hE3 hEN xb (hfixb xb rfl)
    obtain ⟨m, hm, hym⟩ := exists_pow_orderOf_three (y := y) (by rw [hy]; exact h3)
    obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm (by norm_num : 1 < 3)
    have hx3 : xb ^ 3 = 1 := by
      have h1 := pow_orderOf_eq_one xb
      rwa [h3] at h1
    set v : L := (y ^ m) ^ r with hv
    have hvx : π v = xb := by
      rw [hv, map_pow, map_pow, hy, ← pow_mul, pow_eq_pow_mod (m * r) hx3, hr, pow_one]
    have hvN : (v : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer v.2
    have hφv : thetaBarAct L ⟨v, hvN⟩ = MulAut.conj xb := by
      rw [← hvx]
      exact thetaBarAct_of_mem v.2
    have hvE : ∀ d ∈ E, d * (v : G) = v * d := by
      intro d hd
      have h1 : d * (y : G) = y * d := by
        calc d * (y : G) = (d * y * d⁻¹) * d := by group
          _ = y * d := by rw [hyfix d hd]
      have hc : Commute d (y : G) := h1
      have := ((hc.pow_right m).pow_right r).eq
      simpa [hv] using this
    set u : G := e * (v : G)⁻¹ with hu
    have huN : u ∈ Subgroup.normalizer (L : Set G) := mul_mem (hEN heE) (inv_mem hvN)
    have huC : u ∈ Sec4.thetaQuotCentralizer L := by
      rw [mem_thetaQuotCentralizer_iff_thetaBarAct huN]
      have h1 : (⟨u, huN⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨e, hEN heE⟩ * (⟨v, hvN⟩ : Subgroup.normalizer (L : Set G))⁻¹ := Subtype.ext rfl
      rw [h1, map_mul, map_inv, hφe, hφv, mul_inv_cancel]
    have huE : ∀ d ∈ E, d * u = u * d := by
      intro d hd
      have h1 : d * (v : G)⁻¹ = (v : G)⁻¹ * d := by
        have hc : Commute d (v : G) := hvE d hd
        exact hc.inv_right.eq
      calc d * u = (d * e) * (v : G)⁻¹ := by rw [hu, mul_assoc]
        _ = (e * d) * (v : G)⁻¹ := by rw [hcommE d hd e heE]
        _ = e * (d * (v : G)⁻¹) := by rw [mul_assoc]
        _ = e * ((v : G)⁻¹ * d) := by rw [h1]
        _ = u * d := by rw [hu, mul_assoc]
    have hu3 : u ^ 3 = 1 := by
      have hc : Commute e (v : G)⁻¹ := Commute.inv_right (hvE e heE)
      have hv3 : ((v : G)) ^ 3 = 1 := by
        have h1 := pow_orderOf_eq_one (y ^ m)
        rw [hym] at h1
        have h2 : v ^ 3 = 1 := by rw [hv, ← pow_mul, mul_comm, pow_mul, h1, one_pow]
        have h3 := congrArg Subtype.val h2
        simpa using h3
      rw [hu, hc.mul_pow, hexpE e heE, one_mul, inv_pow, hv3, inv_one]
    have huE' : u ∉ E := by
      intro huE'
      have hvE' : (v : G) ∈ E := by
        have : (v : G) = u⁻¹ * e := by rw [hu]; group
        rw [this]
        exact E.mul_mem (E.inv_mem huE') heE
      have h1 := hELC _ hvE' v.2
      rw [show (⟨(v : G), v.2⟩ : L) = v from rfl, hvx] at h1
      exact hxZ h1
    have hu1 : orderOf u = 3 := orderOf_eq_prime hu3 fun h => huE' (h ▸ E.one_mem)
    have hucent : u ∈ Subgroup.centralizer
        ((E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact huE b hb.1
    have hBc : IsMulCommutative (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) :=
      ⟨⟨fun a b => Subtype.ext (hcommE a a.2.1 b b.2.1)⟩⟩
    obtain ⟨hDcard, hDc, hDe⟩ := card_sup_zpowers_of_disjoint hucent hBc
      (fun x hx => hexpE x hx.1) hu1 (inf_zpowers_eq_bot_of_not_mem hu1 fun h => huE' h.1)
    exact false_of_E27_le_thetaQuotCentralizer hFE hperf hZ hev ⟨hDc, hDe⟩
      (by rw [hDcard, hB9]) (sup_le inf_le_right (Subgroup.zpowers_le.mpr huC))
  ·
    obtain ⟨⟨wb, hwb3, hwbZ, hwbx⟩, tb, htb2, htbx⟩ := hK9 (L ⧸ N) hX hty xb h9 hx3Z
    obtain ⟨y, hy, hyfix⟩ := exists_lift_fixed hE3 hEN wb (hfixb wb hwbx)
    obtain ⟨m, hm, hym⟩ := exists_pow_orderOf_three (y := y) (by rw [hy]; exact hwb3)
    have hπym : π (y ^ m) ∉ Subgroup.center (L ⧸ N) := by
      intro hc
      apply hwbZ
      obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm (by norm_num : 1 < 3)
      have hw3 := pow_orderOf_eq_one wb
      rw [hwb3] at hw3
      have h1 : wb = (π (y ^ m)) ^ r := by
        rw [map_pow, hy, ← pow_mul, pow_eq_pow_mod (m * r) hw3, hr, pow_one]
      rw [h1]
      exact Subgroup.pow_mem _ hc r
    have hwc : ((y ^ m : L) : G) ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 : d * (y : G) = y * d := by
        calc d * (y : G) = (d * y * d⁻¹) * d := by group
          _ = y * d := by rw [hyfix d hd]
      have hc : Commute d (y : G) := h1
      have := (hc.pow_right m).eq
      rw [Subgroup.coe_pow]
      exact this
    have hw3 : orderOf ((y ^ m : L) : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hym
    have hwE : ((y ^ m : L) : G) ∉ E := fun h => hπym (hELC _ h (y ^ m).2)
    obtain ⟨t, ht, htfix⟩ := exists_lift_fixed hE3 hEN tb (hfixb tb htbx)
    have hEt : ∀ d ∈ E, d * (t : G) = t * d := fun d hd => by
      calc d * (t : G) = (d * t * d⁻¹) * d := by group
        _ = t * d := by rw [htfix d hd]
    obtain ⟨U, hU0, hU2, hEU⟩ := exists_two_subgroup_of_centralizes hE3 hEN hEt
      (by rw [ht]; exact htb2)
    exact false_of_le_E81 hFE hE.1 hE.2 hU0 hU2 hEU hwc hw3 hwE

end CFSG.RankThree.PartTwo.Sec12
