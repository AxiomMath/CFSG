module

public import CFSG.Quasithin.Background.C35Setup
public import CFSG.Quasithin.Background.F918Z4c1Sz
public import CFSG.RankThree.PartOne.KFOUT3.SLCard
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.C35

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise

theorem eq_of_two_pow_mul_odd {a b u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : ¬ 2 ∣ u := fun ⟨k, hk⟩ => by obtain ⟨j, hj⟩ := hu; omega
  have hv2 : ¬ 2 ∣ v := fun ⟨k, hk⟩ => by obtain ⟨j, hj⟩ := hv; omega
  have h2 := congrArg (padicValNat 2) h
  rw [padicValNat.mul (by positivity) (by rintro rfl; exact hu2 (dvd_zero 2)),
    padicValNat.mul (by positivity) (by rintro rfl; exact hv2 (dvd_zero 2)),
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hu2,
    padicValNat.eq_zero_of_not_dvd hv2] at h2
  simpa using h2

theorem odd_pow_sub_one {a k : ℕ} (ha : Even a) (hk : 0 < k) (ha1 : 1 ≤ a) : Odd (a ^ k - 1) := by
  have : Even (a ^ k) := Nat.even_pow.mpr ⟨ha, hk.ne'⟩
  have h1 : 1 ≤ a ^ k := Nat.one_le_pow _ _ ha1
  obtain ⟨j, hj⟩ := this
  exact ⟨j - 1, by omega⟩

theorem psl2_ne_sl3 {m n : ℕ} (hn : 1 < n) :
    2 ^ m * (4 ^ m - 1) ≠ ((2 ^ n) ^ 3 - 1) * (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) := by
  intro h
  have hq : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
  have hev : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hq1 : 1 ≤ 2 ^ n := by omega
  have hq3 : 64 ≤ (2 ^ n) ^ 3 := (Nat.pow_le_pow_left hq 3).trans' (by norm_num)
  have hq2 : 16 ≤ (2 ^ n) ^ 2 := (Nat.pow_le_pow_left hq 2).trans' (by norm_num)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [pow_zero, Nat.sub_self, mul_zero] at h
    have : 0 < ((2 ^ n) ^ 3 - 1) * (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    omega
  · have hodd1 : Odd (4 ^ m - 1) := odd_pow_sub_one (by decide) hm (by norm_num)
    have hodd2 : Odd (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) :=
      (odd_pow_sub_one hev (by norm_num) hq1).mul (odd_pow_sub_one hev (by norm_num) hq1)
    have h' : 2 ^ m * (4 ^ m - 1) = 2 ^ (3 * n) * (((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1)) := by
      rw [h, mul_comm 3 n, pow_mul]
      ring
    have hm3 := eq_of_two_pow_mul_odd hodd1 hodd2 h'
    subst hm3
    have e1 : (2 : ℕ) ^ (3 * n) = (2 ^ n) ^ 3 := by rw [mul_comm, pow_mul]
    have e2 : (4 : ℕ) ^ (3 * n) = ((2 ^ n) ^ 3) ^ 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul]
      ring_nf
    rw [e1, e2] at h
    set q := 2 ^ n with hqdef
    have hpos : 0 < q ^ 3 := by positivity
    have hc : (q ^ 3) ^ 2 - 1 = (q ^ 3 - 1) * (q ^ 2 - 1) :=
      Nat.eq_of_mul_eq_mul_left hpos (by rw [h]; ring)
    have h6 : 1 ≤ (q ^ 3) ^ 2 := Nat.one_le_pow _ _ hpos
    zify [h6, (by omega : 1 ≤ q ^ 3), (by omega : 1 ≤ q ^ 2)] at hc
    nlinarith [hc, hq, pow_pos (show (0:ℤ) < q by positivity) 5]

theorem psl2_ne_const {m N : ℕ} (hN : N = 2520 ∨ N = 20160 ∨ N = 979200 ∨ N = 9999360) :
    2 ^ m * (4 ^ m - 1) ≠ N := by
  intro h
  have hle : 2 ^ m ≤ 9999360 := by
    have h1 : 2 ^ m ≤ N := Nat.le_of_dvd (by omega) ⟨_, h.symm⟩
    omega
  have hm : m < 24 := by
    by_contra hm'
    have : 2 ^ 24 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases m <;> rcases hN with rfl | rfl | rfl | rfl <;> norm_num at h

theorem not_three_dvd_card_sz {m : ℕ} (hm : Odd m) :
    ¬ 3 ∣ ((2 ^ m) ^ 2 + 1) * (2 ^ m) ^ 2 * (2 ^ m - 1) := by
  obtain ⟨k, rfl⟩ := hm
  have ha : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ (2 * k + 1) = 3 * q + 2 := ⟨2 ^ (2 * k + 1) / 3, by omega⟩
  rw [hq, show 3 * q + 2 - 1 = 3 * q + 1 by omega, Nat.dvd_iff_mod_eq_zero]
  simp [Nat.mul_mod, Nat.add_mod, Nat.pow_mod]

theorem levi_card_ne {Y : Type} [Group Y]
    (hY : (∃ m : ℕ, 2 ≤ m ∧ IsPSL 2 2 m Y) ∨ (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsSz m Y) ∨
      IsPSL 3 2 1 Y)
    {c : ℕ} (hc : c = 2520 ∨ c = 20160 ∨ c = 979200 ∨ c = 9999360 ∨
      ∃ n : ℕ, 1 < n ∧ c = ((2 ^ n) ^ 3 - 1) * (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1)) :
    Nat.card Y ≠ c := by
  rcases hY with ⟨m, -, hY⟩ | ⟨m, hm, -, hY⟩ | hY
  · rw [C48.card_psl_two_two hY]
    rcases hc with hc | hc | hc | hc | ⟨n, hn, rfl⟩
    · exact psl2_ne_const (Or.inl hc)
    · exact psl2_ne_const (Or.inr (Or.inl hc))
    · exact psl2_ne_const (Or.inr (Or.inr (Or.inl hc)))
    · exact psl2_ne_const (Or.inr (Or.inr (Or.inr hc)))
    · exact psl2_ne_sl3 hn
  · rw [card_of_isSz hY]
    intro h
    apply not_three_dvd_card_sz hm
    rw [h]
    rcases hc with rfl | rfl | rfl | rfl | ⟨n, hn, rfl⟩
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · apply Dvd.dvd.mul_left
      have h4 : (2 ^ n) ^ 2 = 4 ^ n := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [h4, Nat.dvd_iff_mod_eq_zero]
      have h41 : 4 ^ n % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
      omega
  · have h168 : Nat.card Y = 168 := by
      obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hY
      rw [Nat.card_congr e.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3), hF]
      decide
    rw [h168]
    rcases hc with rfl | rfl | rfl | rfl | ⟨n, hn, rfl⟩
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · have hq : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
      have hq3 : 64 ≤ (2 ^ n) ^ 3 := (Nat.pow_le_pow_left hq 3).trans' (by norm_num)
      have hq2 : 16 ≤ (2 ^ n) ^ 2 := (Nat.pow_le_pow_left hq 2).trans' (by norm_num)
      have : 63 * 64 * 15 ≤ ((2 ^ n) ^ 3 - 1) * (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) hq3) (by omega)
      omega

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

omit [Finite G] in
theorem card_modO2_of_isAltBlockType {X : Subgroup G} {m : ℕ} (h : IsAltBlockType X m) :
    Nat.card (ModO2 X) = Nat.card (alternatingGroup (Fin m)) := by
  obtain ⟨-, α, hαs, hαk, -⟩ := h
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hαs)).toEquiv

omit [Finite G] in
theorem card_modO2_of_isSp4Block {X : Subgroup G} (h : IsSp4Block X) :
    Nat.card (ModO2 X) = 979200 := by
  obtain ⟨-, F, _, _, hF, α, hαs, hαk, -⟩ := h
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hαs)).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_eq_fintype_card, hF]
  decide

theorem card_statedSL_three {F : Type} [Field F] [Fintype F] :
    Nat.card ↥(StatedSL 3 F) =
      (Fintype.card F ^ 3 - 1) * Fintype.card F ^ 3 * (Fintype.card F ^ 2 - 1) := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv,
    CFSG.RankThree.PartOne.KFOUT3.card_SL3_eq, Nat.card_eq_fintype_card]

theorem not_isPGroup_of_perfect {D : Subgroup G} (hne : D ≠ ⊥) (hperf : ⁅D, D⁆ = D) :
    ¬ IsPGroup 2 ↥D := by
  intro hp
  have : Group.IsNilpotent ↥D := hp.isNilpotent
  have : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).mpr hne
  have : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr hperf
  exact Group.IsPerfect.not_isNilpotent ↥D inferInstance

theorem le_pCore_or_eq_top {X : Subgroup G} (hX : ⁅X, X⁆ = X) (hS : IsSimpleGroup (ModO2 X))
    (N : Subgroup ↥X) [N.Normal] : N ≤ CFSG.pCore 2 ↥X ∨ N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hρdef
  have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hker : ρ.ker = CFSG.pCore 2 ↥X := QuotientGroup.ker_mk' _
  have : (N.map ρ).Normal := Subgroup.Normal.map inferInstance ρ hρ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map ρ) with hb | ht
  · left
    rw [← hker]
    exact (Subgroup.map_eq_bot_iff _).mp hb
  · right
    have h2 : IsPGroup 2 (↥X ⧸ N) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
      obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp (ht ▸ Subgroup.mem_top (ρ x))
      have hp : d⁻¹ * x ∈ CFSG.pCore 2 ↥X := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥X) (p := 2)) ⟨_, hp⟩
      refine ⟨k, ?_⟩
      have hk' : (d⁻¹ * x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hdN : QuotientGroup.mk' N d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
      have hx : QuotientGroup.mk' N x = QuotientGroup.mk' N (d⁻¹ * x) := by
        rw [map_mul, map_inv, hdN, inv_one, one_mul]
      rw [hx, ← map_pow, hk', map_one]
    exact C48.eq_top_of_isPGroup_quotient hX N h2

theorem eq_of_le_normalizer {X D : Subgroup G} (hDX : D ≤ X)
    (hXN : X ≤ Subgroup.normalizer (D : Set G)) (hD : ⁅D, D⁆ = D) (hDne : D ≠ ⊥)
    (hX : ⁅X, X⁆ = X) (hS : IsSimpleGroup (ModO2 X)) : D = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (D.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDX).mpr hXN
  rcases le_pCore_or_eq_top hX hS (D.subgroupOf X) with hle | htop
  · exfalso
    have hp : IsPGroup 2 ↥(D.subgroupOf X) :=
      (CFSG.pCore_isPGroup (G := ↥X) (p := 2)).to_le hle
    exact not_isPGroup_of_perfect hDne hD
      (hp.of_equiv (Subgroup.subgroupOfEquivOfLe hDX))
  · exact le_antisymm hDX fun x hx =>
      Subgroup.mem_subgroupOf.mp (htop ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥X))

theorem mem_cComp_self_of_simple {X : Subgroup G} (hne : X ≠ ⊥) (hX : ⁅X, X⁆ = X)
    (hS : IsSimpleGroup (ModO2 X)) : X ∈ cComp X := by
  refine ⟨hne, hX, IsSubnormal.refl X, fun K' hlt hK'ne hK'perf hsub => ?_⟩
  obtain ⟨P, hPX, hPn, hK'P⟩ := A3.subnormal_exists_normal_of_lt hsub hlt
  have : (P.subgroupOf X).Normal := hPn
  rcases le_pCore_or_eq_top hX hS (P.subgroupOf X) with hle | htop
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥P := ((CFSG.pCore_isPGroup (G := ↥X) (p := 2)).to_le hle).of_equiv
      (Subgroup.subgroupOfEquivOfLe hPX.le)
    exact not_isPGroup_of_perfect hK'ne hK'perf (hp.to_le hK'P)
  · exact hPX.ne (le_antisymm hPX.le fun x hx =>
      Subgroup.mem_subgroupOf.mp (htop ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥X)))

omit [Finite G] in
theorem mem_cComp_sup {X T : Subgroup G} (hX : X ∈ cComp X)
    (hT : T ≤ Subgroup.normalizer (X : Set G)) : X ∈ cComp (X ⊔ T) :=
  cComp_mem_of_subnormal (A3.subnormal_of_normal le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hT))) hX

omit [Finite G] in
theorem isQuasisimple_modO2 {X : Subgroup G} (hX : ⁅X, X⁆ = X) (hS : IsSimpleGroup (ModO2 X)) :
    CFSG.IsQuasisimple (ModO2 X) := by
  have hP : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hX
  have hQ : Group.IsPerfect (ModO2 X) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have : IsSimpleGroup (ModO2 X ⧸ (⊥ : Subgroup (ModO2 X))) :=
    (QuotientGroup.quotientBot (G := ModO2 X)).isSimpleGroup
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient ⊥ bot_le hQ this ?_
  by_contra hall
  push Not at hall
  have hcomm : ∀ a b : ModO2 X, a * b = b * a := fun a b => by
    have := hall (a : ModO2 X ⧸ (⊥ : Subgroup (ModO2 X))) (b : ModO2 X ⧸ (⊥ : Subgroup (ModO2 X)))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_bot,
      inv_mul_eq_one] at this
    exact this
  have : IsMulCommutative (ModO2 X) := ⟨⟨hcomm⟩⟩
  have : Subsingleton (ModO2 X) := Group.IsPerfect.subsingleton_of_isMulCommutative
  exact (not_subsingleton (ModO2 X)) this

theorem T_le_normalizer_R (h : HypC28 H R M L V) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hRT : R ≤ T) : T ≤ Subgroup.normalizer (R : Set G) := by
  have hMC := centralizerSection_normal (le_normalizer_conjClosure L M)
  have hmax := (A4.isSylowTwoOf_iff_maximal.mp h.sylow).2.2
  have heq : T ⊓ centralizerSection M (conjClosure L M) (pCoreOf 2 (conjClosure L M)) = R :=
    le_antisymm (hmax _ inf_le_right (hT.2.1.to_le inf_le_left) (le_inf hRT h.sylow.1))
      (le_inf hRT h.sylow.1)
  intro t ht
  rw [← heq]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hMC (hT.1 ht)⟩

omit [Finite G] in
theorem le_normalizer_Y {T : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hTR : T ≤ Subgroup.normalizer (R : Set G)) :
    T ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  intro t ht
  have htRK : t ∈ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTR ht, hTK ht⟩
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hTK ht, normalizer_le_normalizer_normalizer _ htRK⟩

theorem le_normalizer_R_of_inner (h22 : ASC22One G) (h : HypC28 H R M L V)
    (hK : CFSG.Open.IsComponentOf K H) (hHN : H ≤ Subgroup.normalizer (K : Set G))
    (hb : C31Basic H R M L V K)
    (hinn : ∀ g ∈ Subgroup.normalizer (K : Set G) ⊓ Subgroup.normalizer
        ((K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) : Subgroup G) : Set G),
      ∃ k ∈ K, ∀ x ∈ K, (g * x * g⁻¹)⁻¹ * (k * x * k⁻¹) ∈ centerOf K) :
    K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) ≤
      Subgroup.normalizer (R : Set G) := by
  have hO : pCoreOf 2 K = centerOf K := pCoreOf_eq_centerOf hK hb.2.2
  have hZR : centerOf K ≤ R ⊓ K := centerOf_le_inf h hK hHN hb.2.2
  have hset := h22 H R K h.sqtk (c2_9_two h).2 (F918V3S3.mem_cComp_of_isComponentOf hK)
  have hdec : ∀ r ∈ R, ∃ a ∈ R ⊓ K, ∃ c ∈ centralizerSection R K (pCoreOf 2 K), a * c = r := by
    intro r hr
    have hrK : r ∈ Subgroup.normalizer (K : Set G) := hb.2.1 (h.le_M hr)
    obtain ⟨k, hk, hinnk⟩ := hinn r ⟨hrK, R_le_normalizer_Y h hb hr⟩
    have hkN : k⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.inv_mem _ (Subgroup.le_normalizer hk)
    have hmem : r ∈ (R : Set G) ∩
        ((K : Set G) * (centralizerSection H K (pCoreOf 2 K) : Set G)) := by
      refine ⟨hr, k, hk, k⁻¹ * r, ⟨H.mul_mem (H.inv_mem (hK.1 hk)) (h.le_H (h.le_M hr)),
        Subgroup.mul_mem _ hkN hrK, ?_, fun x hx => ?_⟩, by group⟩
      · rw [hO]
        exact normalizer_le_normalizer_centerOf K (Subgroup.mul_mem _ hkN hrK)
      · rw [hO]
        have hz := hinnk x⁻¹ (K.inv_mem hx)
        have heq : x * (k⁻¹ * r) * x⁻¹ * (k⁻¹ * r)⁻¹ =
            k⁻¹ * ((r * x⁻¹ * r⁻¹)⁻¹ * (k * x⁻¹ * k⁻¹))⁻¹ * k⁻¹⁻¹ := by group
        rw [heq]
        exact conj_mem_centerOf hkN (Subgroup.inv_mem _ hz)
    rw [hset] at hmem
    obtain ⟨a, ha, c, hc, hac⟩ := hmem
    exact ⟨a, ha, c, hc, hac⟩
  have hconj : ∀ y ∈ K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G), ∀ r ∈ R,
      y * r * y⁻¹ ∈ R := by
    intro y hy r hr
    obtain ⟨a, ha, c, hc, rfl⟩ := hdec r hr
    have hya : y * a * y⁻¹ ∈ R ⊓ K := (Subgroup.mem_normalizer_iff.mp hy.2 a).mp ha
    have hyc : y * c * y⁻¹ * c⁻¹ ∈ R := by
      have := hc.2.2.2 y hy.1
      rw [hO] at this
      exact (hZR this).1
    have heq : y * (a * c) * y⁻¹ = (y * a * y⁻¹) * ((y * c * y⁻¹ * c⁻¹) * c) := by group
    rw [heq]
    exact R.mul_mem hya.1 (R.mul_mem hyc hc.1)
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨hconj y hy n, fun hn => ?_⟩
  have := hconj y⁻¹ (Subgroup.inv_mem _ hy) _ hn
  simpa [mul_assoc] using this

theorem eq_perfectCore_Y (hC41 : ASC41Statement G)
    (h22one : ASC22One G) (h22two : ASC22Two G) (h22four : ASC22Four G) (hA3 : A3Orbits G)
    (hInsp : InspC35) (h : HypC28 H R M L V) (hK : CFSG.Open.IsComponentOf K H)
    (hHN : H ≤ Subgroup.normalizer (K : Set G)) (hb : C31Basic H R M L V K)
    (ht : C31Lie2Types (↥K ⧸ Subgroup.center ↥K)) :
    conjClosure L M = perfectCore (K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G)) := by
  set Y := K ⊓ Subgroup.normalizer ((R ⊓ K : Subgroup G) : Set G) with hYdef
  have hM0perf := C2Nine.perfect_conjClosure_of_hyp h
  have hM0Y : conjClosure L M ≤ Y := le_Y h hb
  have hM0X : conjClosure L M ≤ perfectCore Y := le_perfectCore_of_perfect hM0Y hM0perf
  have hM0ne : conjClosure L M ≠ ⊥ := fun h0 => h.V_ne (eq_bot_iff.mpr (h0 ▸ h.V_le))
  have hXne : perfectCore Y ≠ ⊥ := fun h0 => hM0ne (eq_bot_iff.mpr (h0 ▸ hM0X))
  have hXperf : ⁅perfectCore Y, perfectCore Y⁆ = perfectCore Y := perfectCore_perfect Y
  obtain ⟨hchar, htypes, hL4⟩ := hInsp.levi G K Y hK.2.2 hb.2.2 ht
    (isParabolic2_Y h22four h hK hHN hb ht) (Y_ne h22two h hK hb) hXne
  have hS : IsSimpleGroup (ModO2 (perfectCore Y)) := by
    rcases htypes with ⟨m, -, hm⟩ | ⟨m, -, -, hm⟩ | hm | hm
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 m hm).2
    · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 m hm).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hm).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 4 2 1 hm).2
  have hnormal : perfectCore Y ≤ Subgroup.normalizer (conjClosure L M : Set G) →
      conjClosure L M = perfectCore Y :=
    fun hXN => eq_of_le_normalizer hM0X hXN hM0perf hM0ne hXperf hS
  by_cases h4 : IsPSL 4 2 1 (ModO2 (perfectCore Y))
  ·
    obtain ⟨-, -, hinn⟩ := hL4 h4
    apply hnormal
    have hYR := le_normalizer_R_of_inner h22one h hK hHN hb hinn
    have hYM : Y ≤ M := (le_inf (inf_le_left.trans hK.1) hYR).trans (C2Nine.inf_normalizer_le_M h)
    exact (perfectCore_le Y).trans (hYM.trans (le_normalizer_conjClosure L M))
  ·
    by_contra hne
    have htypes' : (∃ m : ℕ, 2 ≤ m ∧ IsPSL 2 2 m (ModO2 (perfectCore Y))) ∨
        (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsSz m (ModO2 (perfectCore Y))) ∨
        IsPSL 3 2 1 (ModO2 (perfectCore Y)) := by
      rcases htypes with h1 | h2 | h3 | h4'
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h3)
      · exact absurd h4' h4
    obtain ⟨T, hT, hRT⟩ := CFSG.QuasithinUnique.EscapingLocal.exists_isSylowTwoOf_ge h.le_M h.pgroup
    have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.1.trans hb.2.1
    have hTX : T ≤ Subgroup.normalizer (perfectCore Y : Set G) :=
      (le_normalizer_Y hTK (T_le_normalizer_R h hT hRT)).trans
        (normalizer_le_normalizer_perfectCore Y)
    have hX'H : perfectCore Y ⊔ T ≤ H :=
      sup_le ((perfectCore_le Y).trans (inf_le_left.trans hK.1)) (hT.1.trans h.le_H)
    have h' := c2_9_three hA3 h hT hRT (sup_le_sup_right hM0X T) hX'H
    have hXc : perfectCore Y ∈ cComp (perfectCore Y ⊔ T) :=
      mem_cComp_sup (mem_cComp_self_of_simple hXne hXperf hS) hTX
    have hXM : ¬ perfectCore Y ≤ M ⊓ (perfectCore Y ⊔ T) := fun hle =>
      hne (hnormal ((hle.trans inf_le_left).trans (le_normalizer_conjClosure L M)))
    obtain ⟨-, -, -, hcase⟩ := hC41 _ R _ L V _ h' hXc hchar (isQuasisimple_modO2 hXperf hS) hXM
    refine levi_card_ne htypes' (c := Nat.card (ModO2 (perfectCore Y))) ?_ rfl
    rcases hcase with ⟨n, hn, -, -, hblk, -, -⟩ | ⟨hblk, -⟩ | ⟨n, F, _, _, hn, hF, ⟨e⟩, -⟩ |
        ⟨h45, -⟩
    · rw [card_modO2_of_isAltBlockType hblk, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rcases hn with rfl | rfl
      · left; decide
      · right; left; decide
    · rw [card_modO2_of_isSp4Block hblk]
      right; right; left; rfl
    · rw [Nat.card_congr e.toEquiv, card_statedSL_three, hF]
      right; right; right; right
      exact ⟨n, hn, rfl⟩
    · rcases h45 with ⟨-, F, _, _, hF, ⟨e⟩⟩ | ⟨-, F, _, _, hF, ⟨e⟩⟩
      · rw [Nat.card_congr e.toEquiv,
          CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 4), hF]
        right; left; decide
      · rw [Nat.card_congr e.toEquiv,
          CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 5), hF]
        right; right; right; left; decide

end CFSG.Quasithin.C35
