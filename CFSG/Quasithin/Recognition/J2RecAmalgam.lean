module

public import CFSG.Quasithin.Recognition.J2RecDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem subgroup_eq_top_of_fifteen_dvd {A : Type*} [Group A] [Finite A] [IsSimpleGroup A]
    (hA : Nat.card A = 60) {X : Subgroup A} (hX : 15 ∣ Nat.card X) : X = ⊤ := by
  by_contra hne
  have hidx : X.index ≤ 4 := by
    have h := Subgroup.card_mul_index X
    rw [hA] at h
    obtain ⟨k, hk⟩ := hX
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have := Nat.card_pos (α := X); omega
      · exact hk0
    rw [hk] at h
    have h' : k * X.index = 4 := by nlinarith
    have : X.index ∣ 4 := Dvd.intro_left k h'
    exact Nat.le_of_dvd (by norm_num) this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.toPermHom A (A ⧸ X)).ker with h | h
  · have hinj : Function.Injective (MulAction.toPermHom A (A ⧸ X)) :=
      (MonoidHom.ker_eq_bot_iff _).mp h
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [hA, Nat.card_perm] at h1
    have h2 : Nat.card (A ⧸ X) = X.index := rfl
    rw [h2] at h1
    have h3 : Nat.factorial X.index ≤ 24 := by
      calc Nat.factorial X.index ≤ Nat.factorial 4 := Nat.factorial_le hidx
        _ = 24 := by decide
    omega
  · apply hne
    rw [eq_top_iff]
    intro g _
    have hg : g ∈ (MulAction.toPermHom A (A ⧸ X)).ker := by rw [h]; trivial
    have h2 : g • ((1 : A) : A ⧸ X) = ((1 : A) : A ⧸ X) :=
      congrArg (fun f => f (QuotientGroup.mk (1 : A) : A ⧸ X)) (MonoidHom.mem_ker.mp hg)
    have h3 : ((g : A) : A ⧸ X) = ((1 : A) : A ⧸ X) := by
      simpa [MulAction.Quotient.smul_mk] using h2
    have h4 := QuotientGroup.eq.mp h3
    simpa using X.inv_mem h4

private theorem not_mem_pCoreOf_of_prime_order {G : Type} [Group G] [Finite G] (H : Subgroup G)
    {w : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hwp : w ^ p = 1) (hw1 : w ≠ 1) :
    w ∉ pCoreOf 2 H := by
  intro hw
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hQ := pCoreOf_isPGroup 2 H
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQ ⟨w, hw⟩
  have hord : orderOf (⟨w, hw⟩ : ↥(pCoreOf 2 H)) = p := by
    have : orderOf w = p := orderOf_eq_prime hwp hw1
    rw [← this]
    exact Subgroup.orderOf_mk w hw
  rw [hord] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact hp.one_lt.ne' (by simpa using hk)
  · have h2 : 2 ∣ p := by rw [hk]; exact dvd_pow_self 2 hk0.ne'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm

theorem IsTypeH2.centralizer_le_of_orders {G : Type} [Group G] [Finite G] {z : G}
    (h : IsTypeH2 G z) {K : Subgroup G}
    (hQK : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≤ K) {w₃ w₅ : G} (h3K : w₃ ∈ K)
    (h5K : w₅ ∈ K) (h3c : w₃ * z = z * w₃) (h5c : w₅ * z = z * w₅) (h3o : w₃ ^ 3 = 1)
    (h3 : w₃ ≠ 1) (h5o : w₅ ^ 5 = 1) (h5 : w₅ ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ K := by
  set P1 := Subgroup.centralizer ({z} : Set G) with hP1
  obtain ⟨e⟩ := h.quot
  let u3 : ↥P1 := ⟨w₃, Subgroup.mem_centralizer_singleton_iff.mpr h3c⟩
  let u5 : ↥P1 := ⟨w₅, Subgroup.mem_centralizer_singleton_iff.mpr h5c⟩
  let π : ↥P1 →* OTwoQuot P1 := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥P1)
  set X : Subgroup (OTwoQuot P1) := (K.subgroupOf P1).map π with hX
  set Y : Subgroup (alternatingGroup (Fin 5)) := X.map e.toMonoidHom with hY
  have hu3X : π u3 ∈ X := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr h3K)
  have hu5X : π u5 ∈ X := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr h5K)
  have hnot : ∀ {w : G} (hw : w ∈ P1) {p : ℕ}, p.Prime → p ≠ 2 → w ^ p = 1 → w ≠ 1 →
      π ⟨w, hw⟩ ≠ 1 := by
    intro w hw p hp hp2 hwp hw1 hπ
    have hmem : (⟨w, hw⟩ : ↥P1) ∈ CFSG.Open.pCore 2 ↥P1 := (QuotientGroup.eq_one_iff _).mp hπ
    exact not_mem_pCoreOf_of_prime_order P1 hp hp2 hwp hw1
      (Subgroup.mem_map.mpr ⟨⟨w, hw⟩, hmem, rfl⟩)
  have hord3 : orderOf (e (π u3)) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← map_pow]
      have : u3 ^ 3 = 1 := Subtype.ext (by simpa using h3o)
      rw [this, map_one, map_one]
    · intro h1
      exact hnot (Subgroup.mem_centralizer_singleton_iff.mpr h3c) Nat.prime_three (by norm_num) h3o
        h3 (e.injective (by rw [h1, map_one]))
  have hord5 : orderOf (e (π u5)) = 5 := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← map_pow]
      have : u5 ^ 5 = 1 := Subtype.ext (by simpa using h5o)
      rw [this, map_one, map_one]
    · intro h1
      exact hnot (Subgroup.mem_centralizer_singleton_iff.mpr h5c) (by norm_num) (by norm_num) h5o
        h5 (e.injective (by rw [h1, map_one]))
  have hd3 : 3 ∣ Nat.card Y := by
    have := Subgroup.orderOf_dvd_natCard Y
      (show e (π u3) ∈ Y from Subgroup.mem_map_of_mem e.toMonoidHom hu3X)
    rwa [hord3] at this
  have hd5 : 5 ∣ Nat.card Y := by
    have := Subgroup.orderOf_dvd_natCard Y
      (show e (π u5) ∈ Y from Subgroup.mem_map_of_mem e.toMonoidHom hu5X)
    rwa [hord5] at this
  have hd15 : 15 ∣ Nat.card Y := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) hd3 hd5
    simpa using this
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hYtop : Y = ⊤ := subgroup_eq_top_of_fifteen_dvd h60 hd15
  have hXtop : ∀ a : OTwoQuot P1, a ∈ X := by
    intro a
    have : e a ∈ Y := by rw [hYtop]; trivial
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp this
    have : b = a := e.injective hba
    rw [← this]; exact hb
  intro p hp
  obtain ⟨k, hk, hkp⟩ := Subgroup.mem_map.mp (hXtop (π ⟨p, hp⟩))
  have hmem : k⁻¹ * ⟨p, hp⟩ ∈ CFSG.Open.pCore 2 ↥P1 := QuotientGroup.eq.mp hkp
  have hQ : ((k⁻¹ * ⟨p, hp⟩ : ↥P1) : G) ∈ pCoreOf 2 P1 :=
    Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  have : (k : G) * ((k⁻¹ * ⟨p, hp⟩ : ↥P1) : G) = p := by
    simp
  rw [← this]
  exact K.mul_mem hkK (hQK hQ)

end CFSG.Quasithin
