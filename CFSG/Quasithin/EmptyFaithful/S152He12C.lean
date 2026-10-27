module

public import CFSG.Quasithin.EmptyFaithful.S152He12B
public import CFSG.Quasithin.EmptyFaithful.S152L27A

public section

namespace CFSG.Quasithin

namespace He12

section Abstract

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem exists_lift_orderOf_three {Q : Subgroup Y} [Q.Normal] (hQ : IsPGroup 2 Q) {x : Y ⧸ Q}
    (hx : orderOf x = 3) : ∃ y : Y, orderOf y = 3 ∧ (y : Y ⧸ Q) = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective x
  have h3 : ((y₀ : Y ⧸ Q)) ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
  have hy3 : y₀ ^ 3 ∈ Q := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact h3
  obtain ⟨j, hj⟩ := hQ ⟨y₀ ^ 3, hy3⟩
  have hj' : y₀ ^ (3 * 2 ^ j) = 1 := by
    have := congrArg (fun z : Q => (z : Y)) hj
    simpa [pow_mul] using this
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (Nat.Coprime.pow_left j (by norm_num : Nat.Coprime 2 3)) (by norm_num : 1 < 3)
  have hq : ((y₀ ^ (2 ^ j * m) : Y) : Y ⧸ Q) = (y₀ : Y ⧸ Q) := by
    rw [QuotientGroup.mk_pow, pow_eq_pow_mod _ h3, hm, pow_one]
  have h1 : (y₀ ^ (2 ^ j * m)) ^ 3 = 1 := by
    calc (y₀ ^ (2 ^ j * m)) ^ 3 = y₀ ^ (2 ^ j * m * 3) := (pow_mul _ _ _).symm
      _ = y₀ ^ ((3 * 2 ^ j) * m) := by ring_nf
      _ = (y₀ ^ (3 * 2 ^ j)) ^ m := pow_mul _ _ _
      _ = 1 := by rw [hj', one_pow]
  have h2 : y₀ ^ (2 ^ j * m) ≠ 1 := by
    intro h
    rw [h] at hq
    have h' : (1 : Y ⧸ Q) = (y₀ : Y ⧸ Q) := by simpa using hq
    rw [← h', orderOf_one] at hx
    omega
  exact ⟨y₀ ^ (2 ^ j * m), orderOf_eq_prime h1 h2, hq⟩

theorem exists_threeComplement_caseI {K : Subgroup Y} (hK : K.Normal)
    (hFa : ∀ x : Y, orderOf x = 3 → x ∈ K) :
    ∃ (Ct W₀ : Subgroup Y) (k : ℕ), W₀.Normal ∧ ¬ 3 ∣ Nat.card W₀ ∧
      (∀ y : Y, y ∈ Ct ↔ ∀ z ∈ K, y * z * y⁻¹ * z⁻¹ ∈ CFSG.pCore 2 Y) ∧
      ∀ y ∈ Ct, y ^ 3 ^ k ∈ W₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := CFSG.pCore 2 Y with hQdef
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have : Q.Normal := CFSG.pCore_normal
  let π : Y →* Y ⧸ Q := QuotientGroup.mk' Q
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Q
  set K' : Subgroup (Y ⧸ Q) := K.map π with hK'def
  have hK'n : K'.Normal := hK.map π hπ
  have hFa' : ∀ x : Y ⧸ Q, orderOf x = 3 → x ∈ K' := by
    intro x hx
    obtain ⟨y, hy3, rfl⟩ := exists_lift_orderOf_three hQ2 hx
    exact ⟨y, hFa y hy3, rfl⟩
  set C : Subgroup (Y ⧸ Q) := Subgroup.centralizer (K' : Set (Y ⧸ Q)) with hCdef
  have hCn : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : g⁻¹ * z * g ∈ K' := by
      have := hK'n.conj_mem z hz g⁻¹
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hz'
    calc z * (g * c * g⁻¹) = g * ((g⁻¹ * z * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * z * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * z := by group
  have hcen : ∀ y : C, orderOf y = 3 → y ∈ Subgroup.center C := by
    intro y hy
    have hy' : orderOf (y : Y ⧸ Q) = 3 := (Subgroup.orderOf_coe y).trans hy
    have hyK : (y : Y ⧸ Q) ∈ K' := hFa' _ hy'
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp c.2 _ hyK).symm
  obtain ⟨N₃, hN₃⟩ := exists_normal_threeComplement hcen
  obtain ⟨hN₃n, hN₃cop, k, hk⟩ := hN₃
  have hN₃c : N₃.Characteristic :=
    (CFSG.GroupTheory.frobenius_normal_p_complement 3).2.2 N₃ ⟨hN₃n, hN₃cop, k, hk⟩
  have hWn : (N₃.map C.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hCmem : ∀ y : Y, π y ∈ C ↔ ∀ z ∈ K, y * z * y⁻¹ * z⁻¹ ∈ Q := by
    intro y
    constructor
    · intro hy z hz
      have h1 := Subgroup.mem_centralizer_iff.mp hy (π z) ⟨z, hz, rfl⟩
      rw [← QuotientGroup.eq_one_iff]
      show π (y * z * y⁻¹ * z⁻¹) = 1
      simp only [map_mul, map_inv]
      calc π y * π z * (π y)⁻¹ * (π z)⁻¹ = (π z * π y) * (π y)⁻¹ * (π z)⁻¹ := by rw [h1]
        _ = 1 := by group
    · intro hy
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨z, hz, rfl⟩
      have h := (QuotientGroup.eq_one_iff _).mpr (hy z hz)
      have h' : π (y * z * y⁻¹ * z⁻¹) = 1 := h
      simp only [map_mul, map_inv] at h'
      calc π z * π y = (π y * π z * (π y)⁻¹ * (π z)⁻¹) * (π z * π y) := by
            rw [h']; simp
        _ = π y * π z := by group
  refine ⟨C.comap π, (N₃.map C.subtype).comap π, k, hWn.comap π, ?_, fun y => hCmem y, ?_⟩
  ·
    intro hd
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥((N₃.map C.subtype).comap π)) 3 hd
    have hu3 : orderOf (u : Y) = 3 := by rw [Subgroup.orderOf_coe]; exact hu
    have huW : π (u : Y) ∈ N₃.map C.subtype := u.2
    obtain ⟨n, hn, hnu⟩ := huW
    have hn3 : orderOf n ∣ 3 := by
      have h1 : orderOf (n : C) = orderOf (π (u : Y)) := by
        rw [← Subgroup.orderOf_coe, ← hnu]; rfl
      rw [h1, ← hu3]
      exact orderOf_map_dvd π _
    have hnc : orderOf n ∣ Nat.card N₃ := Subgroup.orderOf_dvd_natCard N₃ hn
    have h1n : orderOf n = 1 := by
      have hcop' : Nat.Coprime (orderOf n) 3 :=
        Nat.Coprime.coprime_dvd_left hnc hN₃cop
      exact Nat.Coprime.eq_one_of_dvd hcop' hn3
    have hn1 : n = 1 := orderOf_eq_one_iff.mp h1n
    have hπu : π (u : Y) = 1 := by rw [← hnu, hn1]; rfl
    have huQ : (u : Y) ∈ Q := (QuotientGroup.eq_one_iff _).mp hπu
    have := eq_one_of_odd_of_mem_pGroup hQ2 huQ (by rw [hu3]; decide)
    rw [this, orderOf_one] at hu3
    omega
  · intro y hy
    have hyC : π y ∈ C := hy
    have h1 : (⟨π y, hyC⟩ : C) ^ N₃.index ∈ N₃ := Subgroup.pow_index_mem N₃ _
    rw [hk] at h1
    show π (y ^ 3 ^ k) ∈ N₃.map C.subtype
    rw [map_pow]
    exact ⟨_, h1, by simp⟩

end Abstract

end He12

end CFSG.Quasithin
