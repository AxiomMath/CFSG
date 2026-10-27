module

public import CFSG.Walter.ReeOrder.JT.Section7C

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups

theorem isSquare_zmod_three (z : ZMod 3) (hz : IsSquare z) : z = 0 ∨ z = 1 := by
  revert z
  decide

theorem two_zmod_three : ((2 : ℕ) : ZMod 3) ≠ 0 ∧ ((2 : ℕ) : ZMod 3) ≠ 1 := by decide

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem prime_mod_twelve
    {r : ℕ} [hr : Fact r.Prime] (hrq : r ∣ (h.q - 1) / 2) :
    7 ≤ r ∧ ((r % 4 = 1 ∧ r % 3 = 1) ∨ (r % 4 = 3 ∧ r % 3 = 2)) := by
  obtain ⟨n, -, hn⟩ := lemma_4_1 h (h.p_ne_two_of_eq_three hp3) ⟨h.f, by rw [JTHyp.q_eq, hp3]⟩
  have hq8 := h.q_mod_eight_of_eq_three hp3
  have h5 := h.q_mod_five hp3
  have hrq1 : r ∣ h.q - 1 := hrq.trans (Nat.div_dvd_of_dvd (by omega))
  have hq1 : 1 ≤ h.q := by omega
  have hr2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hrq
    omega
  have hr3 : r ≠ 3 := by
    rintro rfl
    have h3q := h.three_dvd_q hp3
    obtain ⟨k, hk⟩ := hrq1
    omega
  have hr5 : r ≠ 5 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hrq1
    omega
  have hr7 : 7 ≤ r := by
    have h2 := hr.out.two_le
    by_contra hlt
    rcases (by omega : r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6) with h1 | h1 | h1 | h1 | h1
    · exact hr2 h1
    · exact hr3 h1
    · exact absurd (h1 ▸ hr.out) (by norm_num)
    · exact hr5 h1
    · exact absurd (h1 ▸ hr.out) (by norm_num)
  have h3sq : IsSquare ((3 : ℕ) : ZMod r) := by
    have h1 : ((3 : ℕ) : ZMod r) ^ (2 * n + 1) = 1 := by
      have : ((h.q - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hrq1
      rw [Nat.cast_sub hq1, sub_eq_zero, hn, Nat.cast_pow, Nat.cast_one] at this
      exact this
    refine ⟨((3 : ℕ) : ZMod r) ^ (n + 1), ?_⟩
    calc ((3 : ℕ) : ZMod r) = ((3 : ℕ) : ZMod r) ^ (2 * n + 1) * ((3 : ℕ) : ZMod r) := by
          rw [h1, one_mul]
      _ = ((3 : ℕ) : ZMod r) ^ (n + 1) * ((3 : ℕ) : ZMod r) ^ (n + 1) := by ring
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrmod : ((r % 3 : ℕ) : ZMod 3) = (r : ZMod 3) := ZMod.natCast_mod r 3
  have hr3' : r % 3 ≠ 0 := by
    intro h0
    apply hr3
    have h3 : 3 ∣ r := Nat.dvd_of_mod_eq_zero h0
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr.out).mp h3).symm
  have h4 : r % 4 = 1 ∨ r % 4 = 3 := by
    have := Nat.odd_iff.mp (hr.out.odd_of_ne_two hr2)
    omega
  refine ⟨hr7, ?_⟩
  rcases h4 with h4 | h4
  · have hsq := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := r) (q := 3) h4
      (by norm_num)).mp h3sq
    refine Or.inl ⟨h4, ?_⟩
    rcases (by omega : r % 3 = 1 ∨ r % 3 = 2) with h1 | h1
    · exact h1
    · exfalso
      rw [← hrmod, h1] at hsq
      rcases isSquare_zmod_three _ hsq with h0 | h0
      · exact two_zmod_three.1 h0
      · exact two_zmod_three.2 h0
  · have hsq := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := r) (q := 3) h4
      (by norm_num) (by omega)).mp h3sq
    refine Or.inr ⟨h4, ?_⟩
    rcases (by omega : r % 3 = 1 ∨ r % 3 = 2) with h1 | h1
    · exfalso
      apply hsq
      rw [← hrmod, h1]
      exact ⟨1, by norm_num⟩
    · exact h1

end JTHyp

theorem card_comap_mk' {K : Type*} [Group K] [Finite K] (L : Subgroup K) [L.Normal]
    (X : Subgroup (K ⧸ L)) :
    Nat.card (X.comap (QuotientGroup.mk' L)) = Nat.card X * Nat.card L := by
  have hidx := Subgroup.index_comap_of_surjective X (QuotientGroup.mk'_surjective L)
  have h1 := Subgroup.card_mul_index (X.comap (QuotientGroup.mk' L))
  have h2 := Subgroup.card_mul_index X
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup L
  rw [hidx] at h1
  have hpos : 0 < X.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [← h2] at h3
  have : Nat.card (X.comap (QuotientGroup.mk' L)) * X.index =
      Nat.card X * Nat.card L * X.index := by
    rw [h1, h3]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem lemma_7_5
    {r : ℕ} [hr : Fact r.Prime] (hrq : r ∣ (h.q - 1) / 2) :
    ¬ IsInvolved PSL(2, GaloisField r 1) G := by
  classical
  rintro ⟨K, L, hL, ⟨e⟩⟩
  obtain ⟨hr7, hr12⟩ := h.prime_mod_twelve hp3 hrq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := K ⧸ L
  set φ : K →* A := QuotientGroup.mk' L with hφdef
  have e' : (⊤ : Subgroup A) ≃* PSL(2, GaloisField r 1) := Subgroup.topEquiv.trans e
  have hF := psl2Facts (⊤ : Subgroup A) e' (by omega) (by rw [pow_one]; omega)
  obtain ⟨U₀, v, hU₀, -⟩ := hF.odd_torus
  have hv2 : orderOf v = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hU₀.w_mul_self)
      (fun h0 => hU₀.w_not_mem (h0 ▸ U₀.one_mem))
  obtain ⟨U, w, hU, hvU, hUcard⟩ := hF.even_torus v (Subgroup.mem_top v) hv2
  rw [pow_one] at hUcard
  have h3U : 3 ∣ Nat.card U := by
    rcases hUcard with ⟨h4, h2⟩ | ⟨h4, h2⟩ <;> rcases hr12 with ⟨h4', h3'⟩ | ⟨h4', h3'⟩ <;> omega
  obtain ⟨⟨ab, habU⟩, hab⟩ := exists_prime_orderOf_dvd_card' (G := U) 3 h3U
  have hab3 : orderOf ab = 3 := by rw [← hab, Subgroup.orderOf_mk]
  have hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    have := hU.cyclic
    intro x hx y hy
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := U)).mul_comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hvv : v * v = 1 := by rw [← pow_two, ← hv2, pow_orderOf_eq_one]
  have hww := hU.w_mul_self
  have hv1 : v ≠ 1 := fun h0 => by rw [h0, orderOf_one] at hv2; omega
  have hw1 : w ≠ 1 := fun h0 => hU.w_not_mem (h0 ▸ U.one_mem)
  have hvw : Commute v w := by
    have h1 := hU.inv v hvU
    rw [inv_eq_of_mul_eq_one_right hvv] at h1
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    rw [hwinv] at h1
    change v * w = w * v
    calc v * w = (w * v * w) * w := by rw [h1]
      _ = w * v * (w * w) := by group
      _ = w * v := by rw [hww, mul_one]
  have hvwne : v ≠ w := fun h0 => hU.w_not_mem (h0 ▸ hvU)
  set Wb := GorensteinWalter.kleinFourOfCommutingInvolutions v w hvv hww hvw with hWbdef
  have hWb : IsKleinFour Wb := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    _ _ _ _ hv1 hw1 hvwne hvw
  have hmemW : ∀ z, z ∈ Wb ↔ z = v * w ∨ z = v ∨ z = w ∨ z = 1 := fun z => Iff.rfl
  set Pb := Subgroup.zpowers ab with hPbdef
  have hvN : v ∈ Subgroup.normalizer (Pb : Set A) :=
    mem_normalizer_zpowers_of_commute (hUab v hvU ab habU)
  have hwN : w ∈ Subgroup.normalizer (Pb : Set A) := by
    refine (conj_smul_eq_iff (K := Pb)).mp ?_
    change (Subgroup.zpowers ab).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers ab
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (w * ab * w⁻¹) = Subgroup.zpowers ab
    rw [hU.inv ab habU, Subgroup.zpowers_inv]
  have hWN : Wb ≤ Subgroup.normalizer (Pb : Set A) := fun z hz => by
    rcases (hmemW z).mp hz with rfl | rfl | rfl | rfl
    · exact Subgroup.mul_mem _ hvN hwN
    · exact hvN
    · exact hwN
    · exact Subgroup.one_mem _
  have hdisjb : Disjoint Wb Pb := by
    rw [Subgroup.disjoint_def]
    intro z hzW hzP
    have h1 : orderOf z ∣ 4 := hWb.card_four ▸ Subgroup.orderOf_dvd_natCard _ hzW
    have h2 : orderOf z ∣ 3 := hab3 ▸ orderOf_dvd_of_mem_zpowers hzP
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num) h1 h2)
  set Xb := Wb ⊔ Pb with hXbdef
  have hXbcard : Nat.card Xb = 12 := by
    rw [hXbdef, card_sup_eq_mul_of_disjoint hWN hdisjb, hWb.card_four, Nat.card_zpowers, hab3]
  have hXbN : Xb ≤ Subgroup.normalizer (Pb : Set A) := sup_le hWN Subgroup.le_normalizer
  set S₀ := Pb.comap φ with hS₀def
  set Y := Xb.comap φ with hYdef
  have hS₀card : Nat.card S₀ = 3 * Nat.card L := by
    rw [hS₀def, card_comap_mk', Nat.card_zpowers, hab3]
  have hYcard : Nat.card Y = 12 * Nat.card L := by
    rw [hYdef, card_comap_mk', hXbcard]
  have hS₀Y : S₀ ≤ Y := Subgroup.comap_mono le_sup_right
  have hS₀n : (S₀.subgroupOf Y).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hS₀Y).mpr fun y hy => ?_
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    change φ (y * z * y⁻¹) ∈ Pb
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hXbN hy) (φ z)).mp hz
  set N₀ := S₀.subgroupOf Y with hN₀def
  obtain ⟨P⟩ : Nonempty (Sylow 3 N₀) := inferInstance
  have hfr := Sylow.normalizer_sup_eq_top P
  have hdiv := card_quotient_dvd_of_sup_eq_top hfr
  have hN₀card : Nat.card N₀ = 3 * Nat.card L := by
    rw [hN₀def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀Y).toEquiv, hS₀card]
  have hquot : Nat.card (Y ⧸ N₀) = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N₀
    rw [hN₀card, hYcard] at h1
    have hpos : 0 < Nat.card L := Nat.card_pos
    have : 12 * Nat.card L = 4 * (3 * Nat.card L) := by ring
    rw [this] at h1
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) h1).symm
  rw [hquot] at hdiv
  set E := (P : Subgroup N₀).map N₀.subtype with hEdef
  obtain ⟨W₀, hW₀⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := Subgroup.normalizer (E : Set Y)) 2 (n := 2) (by norm_num; exact hdiv)
  set W' := ((W₀.map (Subgroup.normalizer (E : Set Y)).subtype).map Y.subtype).map K.subtype
    with hW'def
  set P' := (E.map Y.subtype).map K.subtype with hP'def
  have hW'card : Nat.card W' = 4 := by
    rw [hW'def, Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective Y.subtype_injective,
      Subgroup.card_map_of_injective (Subgroup.normalizer (E : Set Y)).subtype_injective, hW₀]
    norm_num
  have hW'N : W' ≤ Subgroup.normalizer (P' : Set G) := by
    rw [hW'def, hP'def]
    refine (Subgroup.map_mono ?_).trans (map_normalizer_le (E.map Y.subtype))
    exact (Subgroup.map_mono (Subgroup.map_subtype_le W₀)).trans (map_normalizer_le E)
  have hP'3 : IsPGroup 3 P' := ((P.isPGroup'.map _).map _).map _
  have hP'card : Nat.card P' = Nat.card (P : Subgroup N₀) := by
    rw [hP'def, Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective Y.subtype_injective, hEdef,
      Subgroup.card_map_of_injective N₀.subtype_injective]
  have hP3 : 3 ∣ Nat.card (P : Subgroup N₀) := by
    have := Sylow.pow_dvd_card_of_pow_dvd_card P (n := 1) (by
      rw [pow_one, hN₀card]; exact dvd_mul_right 3 _)
    rwa [pow_one] at this
  have hbot := h.eq_bot_of_isPGroup_three_of_le_normalizer hp3 hP'3
    (IsPGroup.of_card (n := 2) (by rw [hW'card]; norm_num)) (by rw [hW'card]) hW'N
  rw [hbot, Subgroup.card_bot] at hP'card
  rw [← hP'card] at hP3
  omega

end JTHyp

end CFSG.Walter.JT
