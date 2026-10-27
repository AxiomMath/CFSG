module

public import CFSG.Walter.J1.HStruct

public section

namespace CFSG.Walter.J1

section General

variable {K : Type*} [Group K] [Finite K]

theorem ncard_orderOf_eq_prime {p : ℕ} [Fact p.Prime] (hP : ∀ P : Sylow p K, Nat.card P = p) :
    {x : K | orderOf x = p}.ncard = Nat.card (Sylow p K) * (p - 1) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (Sylow p K) := Fintype.ofFinite _
  have hpp : p.Prime := Fact.out
  set t : Sylow p K → Finset K := fun P => (Finset.univ.filter (· ∈ P)).erase 1
  have hset : {x : K | orderOf x = p}.toFinset = (Finset.univ : Finset (Sylow p K)).biUnion t := by
    ext x
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_biUnion, Finset.mem_univ,
      true_and, t, Finset.mem_erase, Finset.mem_filter]
    constructor
    · intro hx
      have hZ : IsPGroup p (Subgroup.zpowers x) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
      obtain ⟨P, hP⟩ := hZ.exists_le_sylow
      refine ⟨P, fun h1 => ?_, hP (Subgroup.mem_zpowers x)⟩
      rw [h1, orderOf_one] at hx
      exact hpp.one_lt.ne hx
    · rintro ⟨P, hx1, hxP⟩
      have hdvd : orderOf x ∣ p := by
        rw [← hP P, ← Subgroup.orderOf_mk x hxP]
        exact orderOf_dvd_natCard _
      rcases (Nat.dvd_prime hpp).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hx1
      · exact h1
  have hdisj : ((Finset.univ : Finset (Sylow p K)) : Set (Sylow p K)).PairwiseDisjoint t := by
    intro P _ P' _ hPP'
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [t, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    apply hPP'
    apply Sylow.ext
    rw [eq_zpowers_of_card_prime hpp (hP P) hx.2 hx.1,
      eq_zpowers_of_card_prime hpp (hP P') hx'.2 hx'.1]
  rw [Set.ncard_eq_toFinset_card', hset, Finset.card_biUnion hdisj]
  have hcard : ∀ P : Sylow p K, (t P).card = p - 1 := by
    intro P
    simp only [t]
    rw [Finset.card_erase_of_mem (by simp)]
    have h1 : (Finset.univ.filter (· ∈ P)).card = Nat.card P := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp; rfl))
    rw [h1, hP P]
  rw [Finset.sum_congr rfl (fun P _ => hcard P), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.card_eq_fintype_card]

theorem mem_normalizer_zpowers_iff {x y : K} :
    x ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup K) : Set K) ↔
      x * y * x⁻¹ ∈ Subgroup.zpowers y := by
  constructor
  · intro hx
    exact (Subgroup.mem_normalizer_iff.mp hx y).mp (Subgroup.mem_zpowers y)
  · intro hx
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨k, rfl⟩ := hz
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hx k

end General

theorem coe_mem_zpowers_iff {G : Type*} [Group G] {L : Subgroup G} {y z : L} :
    (z : G) ∈ Subgroup.zpowers (y : G) ↔ z ∈ Subgroup.zpowers y := by
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem eq_one_of_mem_sylow_of_normalizes (Q : Sylow 2 G) {y s : G}
    (hyN : y ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)) (hy : orderOf y = 7)
    (hsQ : s ∈ Q) (hsy : s * y * s⁻¹ ∈ Subgroup.zpowers y) : s = 1 := by
  set c := s * y * s⁻¹ * y⁻¹
  have hcy : c ∈ Subgroup.zpowers y := Subgroup.mul_mem _ hsy (Subgroup.inv_mem _
    (Subgroup.mem_zpowers y))
  have hcQ : c ∈ (Q : Subgroup G) := by
    have : y * s⁻¹ * y⁻¹ ∈ (Q : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp hyN _).mp (Subgroup.inv_mem _ hsQ)
    rw [show c = s * (y * s⁻¹ * y⁻¹) by simp only [c]; group]
    exact Subgroup.mul_mem _ hsQ this
  have hc7 : orderOf c ∣ 7 := by
    have := Subgroup.orderOf_dvd_natCard _ hcy
    rwa [Nat.card_zpowers, hy] at this
  have hc2 : orderOf c ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h.mul_self_of_mem_sylow' Q hcQ)
  have hc1 : c = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 7 2) hc7 hc2
  have hcomm : y * s = s * y := by
    have : s * y * s⁻¹ = y := by rw [← mul_inv_eq_one]; exact hc1
    calc y * s = s * y * s⁻¹ * s := by rw [this]
      _ = s * y := by group
  by_contra hs1
  have hs2 : orderOf s = 2 := orderOf_eq_two_iff.mpr ⟨h.mul_self_of_mem_sylow' Q hsQ, hs1⟩
  have := h.eq_one_of_coprime_of_commute (x := s) (y := y) (by rw [hy]; norm_num)
    (Or.inl hs2) hcomm
  rw [this, orderOf_one] at hy
  omega

include h in
theorem card_sylow_seven_H (Q : Sylow 2 G)
    (P : Sylow 7 (Subgroup.normalizer ((Q : Subgroup G) : Set G))) : Nat.card P = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have h1 : 7 ^ k ∣ 168 := by
    rw [← hk, ← h.card_normalizer_sylow'' Q]
    exact Subgroup.card_subgroup_dvd_card _
  have h2 : 7 ∣ 7 ^ k := by
    rw [← hk]
    have := Sylow.pow_dvd_card_of_pow_dvd_card P (n := 1) (by
      rw [h.card_normalizer_sylow'' Q]; norm_num)
    simpa using this
  rw [hk]
  have hk2 : k < 2 := by
    by_contra hk2
    push Not at hk2
    have : 7 ^ 2 ∣ 168 := (pow_dvd_pow 7 hk2).trans h1
    norm_num at this
  interval_cases k <;> simp_all

include h in
theorem card_sylow_seven (Q : Sylow 2 G) :
    Nat.card (Sylow 7 (Subgroup.normalizer ((Q : Subgroup G) : Set G))) = 8 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set H := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  have hmod := card_sylow_modEq_one 7 H
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 7 H))
  have hdvd := Sylow.card_dvd_index P
  have hidx : (P : Subgroup H).index = 24 := by
    have := (P : Subgroup H).card_mul_index
    rw [h.card_sylow_seven_H Q P, h.card_normalizer_sylow'' Q] at this
    omega
  rw [hidx] at hdvd
  have hmem : Nat.card (Sylow 7 H) ∈ Nat.divisors 24 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have : Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} := by decide
  rw [this] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  unfold Nat.ModEq at hmod
  have hne1 : Nat.card (Sylow 7 H) ≠ 1 := by
    intro h1
    have : Subsingleton (Sylow 7 H) := (Nat.card_eq_one_iff_unique.mp h1).1
    have hPn := Sylow.normal_of_subsingleton P
    obtain ⟨y, hyP, hy1⟩ := exists_ne_one_of_card (h.card_sylow_seven_H Q P) (by norm_num)
    obtain ⟨a, haQ, -, -, ha, -⟩ := h.exists_four_of_sylow Q
    have haH : a ∈ H := Subgroup.le_normalizer haQ
    have hy7 : orderOf (y : G) = 7 := by
      have hdvd7 : orderOf y ∣ 7 := by
        rw [← h.card_sylow_seven_H Q P, ← Subgroup.orderOf_mk y hyP]
        exact orderOf_dvd_natCard _
      rw [Subgroup.orderOf_coe]
      rcases (Nat.dvd_prime (by norm_num)).mp hdvd7 with h0 | h0
      · exact absurd (orderOf_eq_one_iff.mp h0) hy1
      · exact h0
    have hay : a * y * a⁻¹ ∈ Subgroup.zpowers (y : G) := by
      have h3 : (⟨a, haH⟩ : H) * y * (⟨a, haH⟩ : H)⁻¹ ∈ (P : Subgroup H) :=
        hPn.conj_mem y hyP _
      rw [eq_zpowers_of_card_prime (by norm_num) (h.card_sylow_seven_H Q P) hyP hy1] at h3
      exact coe_mem_zpowers_iff.mpr h3
    have := h.eq_one_of_mem_sylow_of_normalizes Q y.2 hy7 haQ hay
    exact (orderOf_eq_two_iff.mp ha).2 this
  rcases hmem with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 <;> rw [h0] at hmod hne1 ⊢ <;> omega

include h in
theorem card_normalizer_sylow_seven (Q : Sylow 2 G)
    (P : Sylow 7 (Subgroup.normalizer ((Q : Subgroup G) : Set G))) :
    Nat.card (Subgroup.normalizer (((P : Subgroup (Subgroup.normalizer
      ((Q : Subgroup G) : Set G)))) : Set (Subgroup.normalizer ((Q : Subgroup G) : Set G)))) =
      21 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h1 := Sylow.card_eq_index_normalizer P
  rw [h.card_sylow_seven Q] at h1
  have := (Subgroup.normalizer (((P : Subgroup (Subgroup.normalizer
    ((Q : Subgroup G) : Set G)))) : Set (Subgroup.normalizer
      ((Q : Subgroup G) : Set G)))).card_mul_index
  have h2 : (Subgroup.normalizer (((P : Subgroup (Subgroup.normalizer
      ((Q : Subgroup G) : Set G)))) : Set (Subgroup.normalizer
        ((Q : Subgroup G) : Set G)))).index = 8 := h1.symm
  rw [h2, h.card_normalizer_sylow'' Q] at this
  omega

include h in
theorem ncard_orderOf_seven (Q : Sylow 2 G) :
    {y : G | y ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) ∧ orderOf y = 7}.ncard = 48 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set H := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  have h1 := ncard_orderOf_eq_prime (K := H) (p := 7) (h.card_sylow_seven_H Q)
  rw [h.card_sylow_seven Q] at h1
  have hset : {y : G | y ∈ H ∧ orderOf y = 7} = Subtype.val '' {x : H | orderOf x = 7} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hy, hy7⟩
      exact ⟨⟨y, hy⟩, by rw [Subgroup.orderOf_mk]; exact hy7, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective, h1]

include h in
theorem exists_sylow_seven_eq (Q : Sylow 2 G) {y : G}
    (hyH : y ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)) (hy : orderOf y = 7) :
    ∃ P : Sylow 7 (Subgroup.normalizer ((Q : Subgroup G) : Set G)),
      (P : Subgroup (Subgroup.normalizer ((Q : Subgroup G) : Set G))) =
        Subgroup.zpowers ⟨y, hyH⟩ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hZ : IsPGroup 7 (Subgroup.zpowers (⟨y, hyH⟩ :
      Subgroup.normalizer ((Q : Subgroup G) : Set G))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hy, pow_one])
  obtain ⟨P, hP⟩ := hZ.exists_le_sylow
  refine ⟨P, (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
  rw [h.card_sylow_seven_H Q P, Nat.card_zpowers, Subgroup.orderOf_mk, hy]

include h in
theorem ncard_normalizer_three (Q : Sylow 2 G) {y : G}
    (hyH : y ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)) (hy : orderOf y = 7) :
    {x : G | x ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) ∧
      x * y * x⁻¹ ∈ Subgroup.zpowers y ∧ orderOf x = 3}.ncard = 14 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set H := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  obtain ⟨P, hP⟩ := h.exists_sylow_seven_eq Q hyH hy
  set N := Subgroup.normalizer ((P : Subgroup H) : Set H)
  have hN21 : Nat.card N = 21 := h.card_normalizer_sylow_seven Q P
  have hmemN : ∀ x : H, x ∈ N ↔ (x : G) * y * (x : G)⁻¹ ∈ Subgroup.zpowers y := by
    intro x
    change x ∈ Subgroup.normalizer ((P : Subgroup H) : Set H) ↔ _
    rw [hP, mem_normalizer_zpowers_iff]
    exact (coe_mem_zpowers_iff (y := (⟨y, hyH⟩ : H)) (z := x * ⟨y, hyH⟩ * x⁻¹)).symm
  have hord : ∀ x : H, x ∈ N → (x ∉ (P : Subgroup H) ↔ orderOf x = 3) := by
    intro x hxN
    constructor
    · intro hxP
      rcases h.orderOf_mem_normalizer Q x.2 with h0 | h0 | h0 | h0 | h0 <;>
        rw [Subgroup.orderOf_coe] at h0
      · exact absurd ((orderOf_eq_one_iff.mp h0) ▸ (P : Subgroup H).one_mem) hxP
      · exfalso
        have := h.eq_one_of_mem_sylow_of_normalizes Q hyH hy
          (mem_sylow_of_orderOf_eq_two Q x.2 (by rw [Subgroup.orderOf_coe, h0]))
          ((hmemN x).mp hxN)
        rw [show x = 1 from Subtype.ext this, orderOf_one] at h0
        omega
      · exact h0
      · exfalso
        set s := x ^ 3
        have hs : orderOf s = 2 := by
          rw [orderOf_pow_of_dvd (by norm_num) (by rw [h0]; norm_num), h0]
        have hsN : s ∈ N := N.pow_mem hxN 3
        have := h.eq_one_of_mem_sylow_of_normalizes Q hyH hy
          (mem_sylow_of_orderOf_eq_two Q s.2 (by rw [Subgroup.orderOf_coe, hs]))
          ((hmemN s).mp hsN)
        rw [show s = 1 from Subtype.ext this, orderOf_one] at hs
        omega
      · exfalso
        apply hxP
        have hZ : IsPGroup 7 (Subgroup.zpowers x) :=
          IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h0, pow_one])
        have hR := IsPGroup.to_sup_of_normal_left' P.isPGroup' hZ ((Subgroup.zpowers_le).mpr hxN)
        have heq := P.is_maximal' hR le_sup_left
        rw [← heq]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    · intro hx3 hxP
      have hdvd : orderOf x ∣ 7 := by
        rw [← h.card_sylow_seven_H Q P, ← Subgroup.orderOf_mk x hxP]
        exact orderOf_dvd_natCard _
      rw [hx3] at hdvd
      norm_num at hdvd
  have hcount : {x : H | x ∈ N ∧ orderOf x = 3}.ncard = 14 := by
    have hset : {x : H | x ∈ N ∧ orderOf x = 3} = (N : Set H) \ ((P : Subgroup H) : Set H) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe]
      constructor
      · rintro ⟨hxN, hx3⟩
        exact ⟨hxN, (hord x hxN).mpr hx3⟩
      · rintro ⟨hxN, hxP⟩
        exact ⟨hxN, (hord x hxN).mp hxP⟩
    have hPN : ((P : Subgroup H) : Set H) ⊆ (N : Set H) := fun x hx =>
      Subgroup.le_normalizer hx
    rw [hset, Set.ncard_sdiff hPN, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, SetLike.coe_sort_coe, hN21, h.card_sylow_seven_H Q P]
  have hset : {x : G | x ∈ H ∧ x * y * x⁻¹ ∈ Subgroup.zpowers y ∧ orderOf x = 3} =
      Subtype.val '' {x : H | x ∈ N ∧ orderOf x = 3} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hxH, hxy, hx3⟩
      exact ⟨⟨x, hxH⟩, ⟨(hmemN _).mpr hxy, by rw [Subgroup.orderOf_mk]; exact hx3⟩, rfl⟩
    · rintro ⟨x, ⟨hxN, hx3⟩, rfl⟩
      exact ⟨x.2, (hmemN x).mp hxN, by rw [Subgroup.orderOf_coe]; exact hx3⟩
  rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective, hcount]

include h in
theorem exists_conj_seven (Q : Sylow 2 G) {y y' : G}
    (hy : y ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G))
    (hy' : y' ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G)) (h7 : orderOf y = 7)
    (h7' : orderOf y' = 7) :
    ∃ g ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G),
      g * y * g⁻¹ ∈ Subgroup.zpowers y' := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := h.exists_sylow_seven_eq Q hy h7
  obtain ⟨P', hP'⟩ := h.exists_sylow_seven_eq Q hy' h7'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Subgroup.normalizer ((Q : Subgroup G) : Set G)) P P'
  refine ⟨g, g.2, ?_⟩
  have h1 : (⟨y, hy⟩ : Subgroup.normalizer ((Q : Subgroup G) : Set G)) ∈
      (P : Subgroup (Subgroup.normalizer ((Q : Subgroup G) : Set G))) :=
    hP ▸ Subgroup.mem_zpowers _
  have h2 : g * ⟨y, hy⟩ * g⁻¹ ∈
      (P' : Subgroup (Subgroup.normalizer ((Q : Subgroup G) : Set G))) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ h1
  rw [hP'] at h2
  exact coe_mem_zpowers_iff.mpr h2

end JankoHyp

end CFSG.Walter.J1
