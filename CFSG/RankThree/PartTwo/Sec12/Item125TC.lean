module

public import CFSG.RankThree.PartTwo.Sec12.Item125NonCentral
public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJStatements
public import CFSG.RankThree.PartTwo.KFacts.KS12ClassExp
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.KFacts.K412TripleCover

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item125DiagTC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12StdBar G A c L →
    (Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) →
    ∀ E : Subgroup G, Late.IsE27 E → E ≤ lcBar c L → c ∈ E →
      Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 →
      Nat.card (E ⊓ L : Subgroup G) = 3 →
      (∀ e ∈ E, ∃ l ∈ L, ∃ z ∈ Sec4.thetaQuotCentralizer L,
        e = l * z ∧ l ^ 3 = 1 ∧ l * z = z * l) →
      Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)

namespace Item125BarTC

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_eq_of_mk_pow_three {L : Subgroup G} (y : L)
    (hy : QuotientGroup.mk' (aschbacherSolvableCore 3 L) y ^ 3 = 1) :
    ∃ n : ℕ, (y ^ n) ^ 3 = 1 ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) (y ^ n) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 L) y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, m, hm, hym, -⟩ := exists_threePart y
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm (by norm_num : 1 < 3)
  refine ⟨m * r, ?_, ?_⟩
  · have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ((y ^ (m * r)) ^ 3) = 1 := by
      rw [map_pow, map_pow, ← pow_mul, mul_comm, pow_mul, hy, one_pow]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h3 : ((⟨_, h1⟩ : aschbacherSolvableCore 3 L) : L) ^ 3 ^ k = 1 := by
      change ((y ^ (m * r)) ^ 3) ^ 3 ^ k = 1
      rw [← pow_mul, ← pow_mul, show m * r * (3 * 3 ^ k) = m * 3 ^ k * (3 * r) by ring,
        pow_mul y (m * 3 ^ k) (3 * r), pow_mul y m (3 ^ k), hym, one_pow]
    have hdvd : orderOf (⟨_, h1⟩ : aschbacherSolvableCore 3 L) ∣ 3 ^ k := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one h3
    have hcop : Nat.Coprime (orderOf (⟨_, h1⟩ : aschbacherSolvableCore 3 L)) 3 := by
      have hd := orderOf_dvd_natCard (⟨_, h1⟩ : aschbacherSolvableCore 3 L)
      exact Nat.Coprime.coprime_dvd_left hd
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
          three_not_dvd_card_aschbacherSolvableCore).symm
    have h1' : orderOf (⟨_, h1⟩ : aschbacherSolvableCore 3 L) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) hdvd
    rw [orderOf_eq_one_iff] at h1'
    exact congrArg Subtype.val h1'
  · rw [map_pow, pow_eq_pow_mod (m * r) hy, hr, pow_one]

theorem exists_lift_pow_three {L E' : Subgroup G} (hE'3 : IsPGroup 3 E')
    (hE'N : E' ≤ Subgroup.normalizer (L : Set G)) (xb : L ⧸ aschbacherSolvableCore 3 L)
    (hxb : xb ^ 3 = 1) (hfix : ∀ d (hd : d ∈ E'), thetaBarAct L ⟨d, hE'N hd⟩ xb = xb) :
    ∃ l : L, QuotientGroup.mk' (aschbacherSolvableCore 3 L) l = xb ∧ (l : G) ^ 3 = 1 ∧
      ∀ d ∈ E', d * (l : G) = l * d := by
  obtain ⟨y, hy, hyfix⟩ := exists_lift_fixed hE'3 hE'N xb hfix
  obtain ⟨n, hn3, hnπ⟩ := exists_pow_eq_of_mk_pow_three y (by rw [hy, hxb])
  refine ⟨y ^ n, by rw [hnπ, hy], by rw [← Subgroup.coe_pow, hn3, Subgroup.coe_one],
    fun d hd => ?_⟩
  have h1 : Commute d (y : G) := by
    change d * y = y * d
    calc d * (y : G) = (d * y * d⁻¹) * d := by group
      _ = y * d := by rw [hyfix d hd]
  rw [Subgroup.coe_pow]
  exact (h1.pow_right n).eq

theorem thetaBarAct_eq_conj {L : Subgroup G} {e l z : G} (hl : l ∈ L)
    (hz : z ∈ Sec4.thetaQuotCentralizer L) (hlz : e = l * z)
    (heN : e ∈ Subgroup.normalizer (L : Set G)) :
    thetaBarAct L ⟨e, heN⟩ =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l, hl⟩) := by
  have hzN := thetaQuotCentralizer_le_normalizer' L hz
  have h1 : (⟨e, heN⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨l, Subgroup.le_normalizer hl⟩ * ⟨z, hzN⟩ := Subtype.ext hlz
  rw [h1, map_mul, thetaBarAct_of_mem hl, (mem_thetaQuotCentralizer_iff_thetaBarAct hzN).mp hz,
    mul_one]

theorem mk_pow_three_eq_one {L : Subgroup G}
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hexp3 : ∀ x : L ⧸ aschbacherSolvableCore 3 L, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ^ 3 = 1)
    {e : G} (heN : e ∈ Subgroup.normalizer (L : Set G)) (he3 : e ^ 3 = 1)
    {xb : L ⧸ aschbacherSolvableCore 3 L} (h : thetaBarAct L ⟨e, heN⟩ = MulAut.conj xb) :
    xb ^ 3 = 1 := by
  have h1 : (⟨e, heN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using he3)
  have h2 := congrArg (thetaBarAct L) h1
  rw [map_pow, map_one, h, ← map_pow] at h2
  have hx3Z := mem_center_of_conj_eq_one h2
  refine hexp3 xb ⟨2, ?_⟩
  have h3 : (⟨xb ^ 3, hx3Z⟩ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) ^ 3 = 1 := by
    have h0 := pow_card_eq_one' (x := (⟨xb ^ 3, hx3Z⟩ :
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)))
    rwa [hZ] at h0
  have h4 := congrArg Subtype.val h3
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h4
  rw [← pow_mul] at h4
  exact h4

theorem exists_decomp_of_mem_lcBar {c : G} {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hexp3 : ∀ x : L ⧸ aschbacherSolvableCore 3 L, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ^ 3 = 1)
    {e : G} (he : e ∈ lcBar c L) (he3 : e ^ 3 = 1) :
    ∃ l ∈ L, ∃ z ∈ Sec4.thetaQuotCentralizer L, e = l * z ∧ l ^ 3 = 1 ∧ l * z = z * l := by
  obtain ⟨l₀, hl₀, z₀, hz₀, hlz⟩ := exists_mul_of_mem_lcBar hL he
  have heN := lcBar_le_normalizer hL he
  have hφ := thetaBarAct_eq_conj hl₀ hz₀ hlz heN
  set xb := QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l₀, hl₀⟩ with hxb
  have hxb3 := mk_pow_three_eq_one hZ hexp3 heN he3 hφ
  have hE'3 : IsPGroup 3 (Subgroup.zpowers e) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one he3) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hE'N : Subgroup.zpowers e ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr heN
  have hfix : ∀ d (hd : d ∈ Subgroup.zpowers e), thetaBarAct L ⟨d, hE'N hd⟩ xb = xb := by
    intro d hd
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    have h1 : (⟨e ^ n, hE'N hd⟩ : Subgroup.normalizer (L : Set G)) = ⟨e, heN⟩ ^ n :=
      Subtype.ext (by simp)
    rw [h1, map_zpow, hφ, ← map_zpow, MulAut.conj_apply,
      (Commute.zpow_left (Commute.refl xb) n).eq, mul_inv_cancel_right]
  obtain ⟨l, hlπ, hl3, hlc⟩ := exists_lift_pow_three hE'3 hE'N xb hxb3 hfix
  have hzN : (l : G)⁻¹ * e ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer l.2)) heN
  refine ⟨l, l.2, (l : G)⁻¹ * e, ?_, by group, hl3, ?_⟩
  · rw [mem_thetaQuotCentralizer_iff_thetaBarAct hzN]
    have h1 : (⟨(l : G)⁻¹ * e, hzN⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨l, Subgroup.le_normalizer l.2⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨e, heN⟩ :=
      Subtype.ext rfl
    rw [h1, map_mul, map_inv, thetaBarAct_of_mem l.2, hφ]
    have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨(l : G), l.2⟩ = xb := hlπ
    rw [h2, inv_mul_cancel]
  · have hle := hlc e (Subgroup.mem_zpowers e)
    calc (l : G) * ((l : G)⁻¹ * e) = (l : G)⁻¹ * (l * e) := by group
      _ = (l : G)⁻¹ * (e * l) := by rw [hle]
      _ = (l : G)⁻¹ * e * l := by group

theorem card_le_nine {L : Subgroup G}
    (hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hcard : ∃ m : ℕ, ¬ 3 ∣ m ∧ Nat.card (L ⧸ aschbacherSolvableCore 3 L) = 27 * m)
    {S : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hS : IsMulCommutative S)
    (hS3 : ∀ x ∈ S, x ^ 3 = 1) : Nat.card S ≤ 9 := by
  obtain ⟨m, hm, hcardm⟩ := hcard
  exact KFacts.K412.card_le_nine_of_three_part hperf le_rfl hZ hm hcardm
    (fun x hx y hy => congrArg Subtype.val (hS.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hS3

theorem false_of_isE27_le {L F : Subgroup G}
    (hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hcard : ∃ m : ℕ, ¬ 3 ∣ m ∧ Nat.card (L ⧸ aschbacherSolvableCore 3 L) = 27 * m)
    (hF : Late.IsE27 F) (hFL : F ≤ L) : False := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  set F' : Subgroup L := F.subgroupOf L with hF'
  have hF'27 : Nat.card F' = 27 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFL).toEquiv).trans hF.2
  have hF'3 : IsPGroup 3 F' := IsPGroup.of_card (n := 3) (by rw [hF'27]; norm_num)
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hF'3
  have hS27 : Nat.card (F'.map π) = 27 := by
    rw [← hF'27]
    change Nat.card (↑(F'.map π) : Set (L ⧸ aschbacherSolvableCore 3 L)) = Nat.card (F' : Set L)
    rw [Subgroup.coe_map, Nat.card_image_of_injOn hinj]
  have hle := card_le_nine hperf hZ hcard (S := F'.map π) ⟨⟨fun u v => by
      obtain ⟨u', hu', hu⟩ := Subgroup.mem_map.mp u.2
      obtain ⟨v', hv', hv⟩ := Subgroup.mem_map.mp v.2
      apply Subtype.ext
      change (u : L ⧸ aschbacherSolvableCore 3 L) * v = v * u
      rw [← hu, ← hv, ← map_mul, ← map_mul]
      congr 1
      have h := hF.1.1.is_comm.comm (⟨u', Subgroup.mem_subgroupOf.mp hu'⟩ : F)
        ⟨v', Subgroup.mem_subgroupOf.mp hv'⟩
      exact Subtype.ext (congrArg Subtype.val h : (u' : G) * v' = v' * u')⟩⟩
    (by
      rintro _ ⟨u, hu, rfl⟩
      rw [← map_pow]
      have : u ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow]
        exact hF.1.2 _ (Subgroup.mem_subgroupOf.mp hu))
      rw [this, map_one])
  rw [hS27] at hle
  norm_num at hle

theorem false_of_card_inf_L_eq_three_of_pow (hFE : partTwoF G = partTwoE G) {c : G}
    {L : Subgroup G}
    (hexp3 : ∀ x : L ⧸ aschbacherSolvableCore 3 L, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ^ 3 = 1)
    (hL : L ∈ thetaComponentsAt 3 c) (hcL : c ∈ L) (hc1 : c ≠ 1)
    (hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hev : 2 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L))
    {E : Subgroup G} (hE : Late.IsE27 E) (hEL : E ≤ lcBar c L) (hcE : c ∈ E)
    (hB9 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9)
    (hEL3 : Nat.card (E ⊓ L : Subgroup G) = 3) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 L with hN
  set π := QuotientGroup.mk' N with hπ
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
  have hφe : thetaBarAct L ⟨e, hEN heE⟩ = MulAut.conj xb :=
    thetaBarAct_eq_conj hl hz hlz (hEN heE)
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
  have hfix : ∀ g (hg : g ∈ E), thetaBarAct L ⟨g, hEN hg⟩ xb = xb := by
    intro g hg
    obtain ⟨k, hk⟩ := hact g hg
    rw [hk, MulAut.conj_apply, (Commute.zpow_left (Commute.refl xb) k).eq, mul_inv_cancel_right]
  have hxZ : xb ∉ Subgroup.center (L ⧸ N) := by
    intro hxZ
    apply heC
    rw [mem_thetaQuotCentralizer_iff_thetaBarAct (hEN heE), hφe]
    exact conj_eq_one_of_mem_center hxZ
  have hx3 := mk_pow_three_eq_one hZ hexp3 (hEN heE) (hexpE e heE) hφe
  obtain ⟨v, hvx, hv3, hvE⟩ := exists_lift_pow_three hE3 hEN xb hx3 hfix
  have hvN : (v : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer v.2
  have hφv : thetaBarAct L ⟨v, hvN⟩ = MulAut.conj xb := by
    rw [← hvx]
    exact thetaBarAct_of_mem v.2
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

theorem false_of_card_inf_L_eq_nine {c : G} {L : Subgroup G}
    (hexp3 : ∀ x : L ⧸ aschbacherSolvableCore 3 L, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ^ 3 = 1)
    (hcard : ∃ m : ℕ, ¬ 3 ∣ m ∧ Nat.card (L ⧸ aschbacherSolvableCore 3 L) = 27 * m)
    (hL : L ∈ thetaComponentsAt 3 c) (hcL : c ∈ L) (hc1 : c ≠ 1)
    (hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤)
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    {E : Subgroup G} (hE : Late.IsE27 E) (hEL : E ≤ lcBar c L) (hcE : c ∈ E)
    (hB3 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3)
    (hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 L with hN
  set π := QuotientGroup.mk' N with hπ
  have hexpE : ∀ x ∈ E, x ^ 3 = 1 := hE.1.2
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEL.trans (lcBar_le_normalizer hL)
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexpE c hcE) hc1
  set T := E ⊓ L with hTdef
  have hTe : CFSG.Assembly.IsElemAbelian 3 T :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommE _ a.2.1 _ b.2.1)⟩⟩, fun x hx => hexpE x hx.1⟩
  have hcT : c ∈ T := ⟨hcE, hcL⟩
  obtain ⟨hTbe, hTb9, -⟩ :=
    Gap125NonCentralBar.thetaImage_facts hL hcL hc1 hZ hTe hEL9 inf_le_right hcT
  set Tb := (T.subgroupOf L).map π with hTbdef
  have hBc : E ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (show c ∈ E ⊓ _ from
      ⟨hcE, mem_thetaQuotCentralizer_of_central hcL hLc⟩))
      (by rw [hB3, Nat.card_zpowers, hc3])).symm
  obtain ⟨e, heE, heL⟩ : ∃ e ∈ E, e ∉ L := by
    by_contra hcon
    push Not at hcon
    have h1 : E ⊓ L = E := inf_eq_left.mpr hcon
    rw [hTdef, h1, hE.2] at hEL9
    norm_num at hEL9
  obtain ⟨l, hl, z, hz, hlz⟩ := exists_mul_of_mem_lcBar hL (hEL heE)
  set xb : L ⧸ N := π ⟨l, hl⟩ with hxb
  have hφe : thetaBarAct L ⟨e, hEN heE⟩ = MulAut.conj xb :=
    thetaBarAct_eq_conj hl hz hlz (hEN heE)
  have hx3 := mk_pow_three_eq_one hZ hexp3 (hEN heE) (hexpE e heE) hφe
  have hxc : xb ∈ Subgroup.centralizer (Tb : Set (L ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    have htE : (t : G) ∈ E := (Subgroup.mem_subgroupOf.mp ht).1
    have h1 : thetaBarAct L ⟨e, hEN heE⟩ (π t) = π t := by
      rw [thetaBarAct_mk]
      congr 1
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe, hcommE e heE _ htE, mul_inv_cancel_right]
    rw [hφe, MulAut.conj_apply] at h1
    calc π t * xb = (xb * π t * xb⁻¹) * xb := by rw [h1]
      _ = xb * π t := by group
  have hxT : xb ∉ Tb := by
    rintro ⟨t, ht, htx⟩
    have htE : (t : G) ∈ E := (Subgroup.mem_subgroupOf.mp ht).1
    have htN : (t : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer t.2
    have hetN : e * (t : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem (hEN heE) (inv_mem htN)
    have hetC : e * (t : G)⁻¹ ∈ Sec4.thetaQuotCentralizer L := by
      rw [mem_thetaQuotCentralizer_iff_thetaBarAct hetN]
      have h1 : (⟨e * (t : G)⁻¹, hetN⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨e, hEN heE⟩ * (⟨t, htN⟩ : Subgroup.normalizer (L : Set G))⁻¹ := Subtype.ext rfl
      rw [h1, map_mul, map_inv, hφe, thetaBarAct_of_mem t.2]
      have h2 : QuotientGroup.mk' N ⟨(t : G), t.2⟩ = xb := htx
      rw [h2, mul_inv_cancel]
    have h1 : e * (t : G)⁻¹ ∈ Subgroup.zpowers c := by
      rw [← hBc]
      exact ⟨E.mul_mem heE (E.inv_mem htE), hetC⟩
    have h2 : e * (t : G)⁻¹ ∈ L := Subgroup.zpowers_le.mpr hcL h1
    apply heL
    have : e = e * (t : G)⁻¹ * t := by group
    rw [this]
    exact L.mul_mem h2 t.2
  have hxo : orderOf xb = 3 := orderOf_eq_prime hx3 fun h1 => hxT (h1 ▸ Tb.one_mem)
  obtain ⟨hScard, hSc, hSe⟩ := card_sup_zpowers_of_disjoint hxc hTbe.1 hTbe.2 hxo
    (inf_zpowers_eq_bot_of_not_mem hxo hxT)
  have hle := card_le_nine hperf hZ hcard hSc hSe
  rw [hScard, hTb9] at hle
  norm_num at hle

end Item125BarTC

open Item125BarTC in
theorem item125BarTC_of
    (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves) (hG1 : Gap125NonCentralBar)
    (hD : Item125DiagTC) : Item125BarTC := by
  intro G _ _ A c L h hty E hE hEL hcE
  have hty' : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22 :=
    Or.inr hty
  have hL := h.mem_thetaComponentsAt
  have hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
    rcases hty with hA6 | hA7 | hM22
    · exact hA6.1
    · exact hA7.1
    · exact hM22.1
  have hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤ := by
    have h1 := (isQuasisimple_thetaQuot_of_mem hL).1
    rwa [Group.isPerfect_def] at h1
  have hev := KFacts.two_dvd_card_of_item122_type hty'
  have hexp3 := KFacts.pow_three_eq_one_of_isTripleCover hty
  have hcard := KFacts.exists_card_eq_of_isTripleCover hty
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcC : c ∈ E ⊓ Sec4.thetaQuotCentralizer L :=
    ⟨hcE, mem_thetaQuotCentralizer_of_central h.mem_L hLc⟩
  have hcEL : c ∈ E ⊓ L := ⟨hcE, h.mem_L⟩
  have hdvd : ∀ S : Subgroup G, S ≤ E → Nat.card S ∣ 3 ^ 3 := fun S hS => by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2]
    exact Subgroup.card_dvd_of_le hS
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd _ inf_le_left)
  obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hdvd (E ⊓ L) inf_le_left)
  interval_cases k
  ·
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact absurd (hk ▸ hcC) (by simpa using h.ne_one)
  ·
    have hB3 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 := by
      rw [hk, pow_one]
    interval_cases j
    · rw [pow_zero, Subgroup.card_eq_one] at hj
      exact absurd (hj ▸ hcEL) (by simpa using h.ne_one)
    ·
      exact hD G A c L h hty E hE hEL hcE hB3 (by rw [hj, pow_one]) fun e he =>
        exists_decomp_of_mem_lcBar hL hZ hexp3 (hEL he) (hE.1.2 e he)
    ·
      exact (false_of_card_inf_L_eq_nine hexp3 hcard hL h.mem_L h.ne_one hperf hZ hE hEL hcE
        hB3 (by rw [hj]; norm_num)).elim
    ·
      exfalso
      have hEL' : E ⊓ L = E :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hj, hE.2]; norm_num)
      exact false_of_isE27_le hperf hZ hcard hE (hEL' ▸ inf_le_right)
  ·
    have hB9 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9 := by
      rw [hk]
      norm_num
    interval_cases j
    · rw [pow_zero, Subgroup.card_eq_one] at hj
      exact absurd (hj ▸ hcEL) (by simpa using h.ne_one)
    · exact (false_of_card_inf_L_eq_three_of_pow h.partTwoF_eq hexp3 hL h.mem_L h.ne_one hperf hZ
        hev hE hEL hcE hB9 (by rw [hj, pow_one])).elim
    ·
      have hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9 := by
        rw [hj]
        norm_num
      by_contra hU
      obtain ⟨P, hP, hPB⟩ := hG1 G A c L h hty' E hE hEL hcE hB9 hEL9 hU
      have hbar : Sec12StdBar G E c L :=
        { toPartTwoStanding := h.toPartTwoStanding
          partTwoF_eq := h.partTwoF_eq
          isE27 := hE
          mem_A := hcE
          ne_one := h.ne_one
          mem_thetaComponentsAt := hL
          mem_L := h.mem_L
          card_B := hB9
          sup_eq := sup_eq_of_card_inf_nine hE hZ hB9 hEL9
          exists_sylow := ⟨P, hP, hPB⟩ }
      exact hU (normalizer_le_of_sec12StdBar_of_list h45 hK2 hbar hty')
    ·
      exfalso
      have hEL' : E ⊓ L = E :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hj, hE.2]; norm_num)
      have hB3 : IsPGroup 3 (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := fun x =>
        ⟨1, Subtype.ext (by simpa using hE.1.2 x x.2.1)⟩
      have h1 := card_inf_le_card_center_of_le_thetaQuotCentralizer hB3 inf_le_right (L := L)
      have h2 : E ⊓ Sec4.thetaQuotCentralizer L ⊓ L = E ⊓ Sec4.thetaQuotCentralizer L :=
        inf_eq_left.mpr (inf_le_left.trans (hEL' ▸ inf_le_right))
      rw [h2, hB9, hZ] at h1
      norm_num at h1
  ·
    exfalso
    have hEC : E ⊓ Sec4.thetaQuotCentralizer L = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hE.2]; norm_num)
    exact false_of_E27_le_thetaQuotCentralizer h.partTwoF_eq hperf hZ hev hE.1 hE.2
      (hEC ▸ inf_le_right)

section Unconditional

theorem item125BarTC_of_item125DiagTC
    (hD : Item125DiagTC) : Item125BarTC :=
  item125BarTC_of Sec4.rank3II_4_5 KFacts.ks12NormalizerMoves gap125NonCentralBar hD

end Unconditional

end CFSG.RankThree.PartTwo.Sec12
