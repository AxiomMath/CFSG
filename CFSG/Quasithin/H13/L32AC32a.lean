module

public import CFSG.Quasithin.H13.L32A58a
public import CFSG.Quasithin.H13.L32AC33c
public import CFSG.Quasithin.H13.L32AC47k

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.Family

theorem sl3_exists_comm : ∀ k : A6.SL3.S, k ^ 3 = 1 → k ≠ 1 →
    ∃ u : A6.SL3.S, (A6.SL3.InX1 u ∧ A6.SL3.InX2 u) ∧ (k * u * k⁻¹ * u⁻¹) ^ 3 = 1 ∧
      k * u * k⁻¹ * u⁻¹ ≠ 1 := by
  decide +kernel

section Generic

variable {Y : Type} [Group Y]

theorem exists_comm_three_of_sylow [Finite Y] (E : Y ≃* A6.SL3.S) {P : Subgroup Y}
    (hP2 : IsPGroup 2 ↥P) (hPi : ¬ 2 ∣ P.index) {k : Y} (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) :
    ∃ s ∈ P, (k * s * k⁻¹ * s⁻¹) ^ 3 = 1 ∧ k * s * k⁻¹ * s⁻¹ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD2 : IsPGroup 2 ↥A6.SL3.P0 :=
    IsPGroup.of_card (A6.SL3.card_P0.trans (by norm_num : (8 : ℕ) = 2 ^ 3))
  have hDi : ¬ 2 ∣ A6.SL3.P0.index := by
    have h := A6.SL3.P0.card_mul_index
    rw [A6.SL3.card_P0, A6.SL3.card_S] at h
    have h21 : A6.SL3.P0.index = 21 := by omega
    rw [h21]
    decide
  obtain ⟨h, hh⟩ := exists_conj_map_eq_of_sylow E.toMonoidHom E.surjective hP2 hPi hD2 hDi
  let φ : Y →* A6.SL3.S := (MulAut.conj h⁻¹).toMonoidHom.comp E.toMonoidHom
  have hφ : Function.Injective φ := (MulAut.conj h⁻¹).injective.comp E.injective
  have hk'3 : φ k ^ 3 = 1 := by rw [← map_pow, hk3, map_one]
  have hk'1 : φ k ≠ 1 := fun h1 => hk1 (hφ (h1.trans (map_one φ).symm))
  obtain ⟨u, hu, hu3, hu1⟩ := sl3_exists_comm (φ k) hk'3 hk'1
  have huP : u ∈ (P.map E.toMonoidHom).map (MulAut.conj h⁻¹).toMonoidHom := by
    rw [hh]
    exact hu
  obtain ⟨_, ⟨s, hs, rfl⟩, hsu⟩ := huP
  have hus : u = φ s := hsu.symm
  refine ⟨s, hs, ?_, ?_⟩
  · apply hφ
    rw [map_pow, map_mul, map_mul, map_mul, map_inv, map_inv, ← hus, hu3, map_one]
  · intro h1
    apply hu1
    rw [hus, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h1, map_one]

theorem eq_one_of_mem_of_commute {N : Subgroup Y} (hZ : Subgroup.center ↥N = ⊥) {z : Y}
    (hzN : z ∈ N) (hz : ∀ n ∈ N, z * n = n * z) : z = 1 := by
  have h1 : (⟨z, hzN⟩ : ↥N) ∈ Subgroup.center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hz g g.2).symm
  rw [hZ, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1

theorem exists_inner_of_gl32 {N : Subgroup Y} (E : ↥N ≃* GL32) {y : Y}
    (hyN : y ∈ Subgroup.normalizer (N : Set Y)) (hy3 : y ^ 3 = 1) :
    ∃ k ∈ N, k ^ 3 = 1 ∧ ∀ n ∈ N, y * n * y⁻¹ = k * n * k⁻¹ := by
  have hNM : N ≤ Subgroup.normalizer (N : Set Y) := Subgroup.le_normalizer
  let E' : ↥(N.subgroupOf (Subgroup.normalizer (N : Set Y))) ≃* GL32 :=
    (Subgroup.subgroupOfEquivOfLe hNM).trans E
  let α : MulAut ↥(N.subgroupOf (Subgroup.normalizer (N : Set Y))) :=
    MulAut.conjNormal (⟨y, hyN⟩ : ↥(Subgroup.normalizer (N : Set Y)))
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (N : Set Y))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hy3)
    show (MulAut.conjNormal (⟨y, hyN⟩ : ↥(Subgroup.normalizer (N : Set Y)))) ^ 3 = 1
    rw [← map_pow, h1, map_one]
  obtain ⟨c, hc⟩ := G58.exists_conj_of_pow_three E' α hα3
  refine ⟨((c : ↥(Subgroup.normalizer (N : Set Y))) : Y), Subgroup.mem_subgroupOf.mp c.2, ?_,
    fun n hn => ?_⟩
  · have hcen : c ^ 3 ∈ Subgroup.center ↥(N.subgroupOf (Subgroup.normalizer (N : Set Y))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : MulAut.conj (c ^ 3) = 1 := by rw [map_pow, ← hc, hα3]
      have h2 := congrArg (fun φ : MulAut _ => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * c ^ 3 = c ^ 3 * g * (c ^ 3)⁻¹ * c ^ 3 := by rw [h2]
        _ = c ^ 3 * g := by group
    rw [G58.center_eq_bot_of_gl32 E', Subgroup.mem_bot] at hcen
    have h3 := congrArg (fun z : ↥(N.subgroupOf (Subgroup.normalizer (N : Set Y))) =>
      ((z : ↥(Subgroup.normalizer (N : Set Y))) : Y)) hcen
    simpa using h3
  · have h1 := congrArg (fun φ : MulAut ↥(N.subgroupOf (Subgroup.normalizer (N : Set Y))) =>
      ((φ ⟨⟨n, hNM hn⟩, Subgroup.mem_subgroupOf.mpr hn⟩ :
        ↥(Subgroup.normalizer (N : Set Y))) : Y)) hc
    simp only [α, MulAut.conjNormal_apply, MulAut.conj_apply] at h1
    simpa using h1

theorem eq_one_of_centralizes_two [Finite Y] (hm : Open.pRank 3 (⊤ : Subgroup Y) ≤ 2)
    {N₁ N₂ : Subgroup Y} (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hZ₁ : Subgroup.center ↥N₁ = ⊥) (hZ₂ : Subgroup.center ↥N₂ = ⊥)
    (h3₁ : 3 ∣ Nat.card ↥N₁) (h3₂ : 3 ∣ Nat.card ↥N₂) {y : Y}
    (hy₁ : ∀ n ∈ N₁, y * n = n * y) (hy₂ : ∀ n ∈ N₂, y * n = n * y) (hy3 : y ^ 3 = 1) :
    y = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hy1
  obtain ⟨a', ha'⟩ := exists_prime_orderOf_dvd_card' (G := ↥N₁) 3 h3₁
  obtain ⟨b', hb'⟩ := exists_prime_orderOf_dvd_card' (G := ↥N₂) 3 h3₂
  have ha3 : (a' : Y) ^ 3 = 1 := by
    rw [← ha', ← Subgroup.orderOf_coe]
    exact pow_orderOf_eq_one _
  have hb3 : (b' : Y) ^ 3 = 1 := by
    rw [← hb', ← Subgroup.orderOf_coe]
    exact pow_orderOf_eq_one _
  have ha1 : (a' : Y) ≠ 1 := fun h => by
    have : a' = 1 := Subtype.ext h
    rw [this, orderOf_one] at ha'
    omega
  have hb1 : (b' : Y) ≠ 1 := fun h => by
    have : b' = 1 := Subtype.ext h
    rw [this, orderOf_one] at hb'
    omega
  have hab : (a' : Y) * b' = b' * a' := hc _ a'.2 _ b'.2
  have hbn : Subgroup.zpowers (b' : Y) ≤ Subgroup.normalizer
      ((Subgroup.zpowers (a' : Y) : Subgroup Y) : Set Y) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem_fin fun z hz => ?_
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h1 : Commute (b' : Y) ((a' : Y) ^ i) := (Commute.zpow_right hab.symm i)
    rw [h1.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ i
  refine absurd (F6.three_le_pRank_of_commute (x₁ := y) (x₂ := (a' : Y)) (x₃ := (b' : Y))
    (C₁ := Subgroup.zpowers (a' : Y) ⊔ Subgroup.zpowers (b' : Y))
    (C₂ := Subgroup.centralizer (N₁ : Set Y)) (C₃ := Subgroup.centralizer (N₂ : Set Y))
    (hy₁ _ a'.2) (hy₂ _ b'.2) hab ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by omega)
  · intro hyC
    obtain ⟨p, hp, q, hq, hpq⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hbn).mp hyC
    have hpN : p ∈ N₁ := (Subgroup.zpowers_le.mpr a'.2) hp
    have hqN : q ∈ N₂ := (Subgroup.zpowers_le.mpr b'.2) hq
    have hp1 : p = 1 := by
      refine eq_one_of_mem_of_commute hZ₁ hpN fun n hn => ?_
      have h1 : p = y * q⁻¹ := by rw [hpq]; group
      have h2 : q⁻¹ * n = n * q⁻¹ := (hc n hn _ (inv_mem hqN)).symm
      calc p * n = y * (q⁻¹ * n) := by rw [h1]; group
        _ = y * (n * q⁻¹) := by rw [h2]
        _ = (y * n) * q⁻¹ := by group
        _ = n * (y * q⁻¹) := by rw [hy₁ n hn]; group
        _ = n * p := by rw [← h1]
    rw [hp1, one_mul] at hpq
    rw [hpq] at hy₂
    exact hy1 (hpq.trans (eq_one_of_mem_of_commute hZ₂ hqN hy₂))
  · intro haC
    exact ha1 (eq_one_of_mem_of_commute hZ₁ a'.2 fun n hn =>
      (Subgroup.mem_centralizer_iff.mp haC n hn).symm)
  · intro hbC
    exact hb1 (eq_one_of_mem_of_commute hZ₂ b'.2 fun n hn =>
      (Subgroup.mem_centralizer_iff.mp hbC n hn).symm)
  · rw [hy3]
    exact one_mem _
  · rw [ha3]
    exact one_mem _
  · rw [hb3]
    exact one_mem _
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · exact Subgroup.mem_centralizer_iff.mpr fun n hn => (hy₁ n hn).symm
  · exact Subgroup.mem_centralizer_iff.mpr fun n hn => hc n hn _ b'.2
  · exact Subgroup.mem_centralizer_iff.mpr fun n hn => (hy₂ n hn).symm
  · exact Subgroup.mem_centralizer_iff.mpr fun n hn => (hc _ a'.2 n hn).symm

theorem nine_dvd_card [Finite Y] {A N : Subgroup Y} {u c : Y} (huA : u ∈ A)
    (huN : u ∈ Subgroup.normalizer (N : Set Y)) (hu3 : u ^ 3 = 1) (hun : u ∉ N) (hcA : c ∈ A)
    (hcN : c ∈ N) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) : 9 ∣ Nat.card ↥A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBN : A ⊓ Subgroup.normalizer (N : Set Y) ≤
      Subgroup.normalizer ((A ⊓ Subgroup.normalizer (N : Set Y) ⊓ N : Subgroup Y) : Set Y) :=
    fun b hb => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hb, hb.2⟩
  have : ((A ⊓ Subgroup.normalizer (N : Set Y) ⊓ N).subgroupOf
      (A ⊓ Subgroup.normalizer (N : Set Y))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hBN
  have h1 : 3 ∣ Nat.card ↥(A ⊓ Subgroup.normalizer (N : Set Y) ⊓ N) := by
    have hcB : c ∈ A ⊓ Subgroup.normalizer (N : Set Y) ⊓ N :=
      ⟨⟨hcA, Subgroup.le_normalizer hcN⟩, hcN⟩
    rw [← orderOf_eq_prime hc3 hc1]
    exact Subgroup.orderOf_dvd_natCard _ hcB
  have h2 : 3 ∣ Nat.card (↥(A ⊓ Subgroup.normalizer (N : Set Y)) ⧸
      (A ⊓ Subgroup.normalizer (N : Set Y) ⊓ N).subgroupOf
        (A ⊓ Subgroup.normalizer (N : Set Y))) := by
    have hq3 : (QuotientGroup.mk (⟨u, ⟨huA, huN⟩⟩ : ↥(A ⊓ Subgroup.normalizer (N : Set Y))) :
        ↥(A ⊓ Subgroup.normalizer (N : Set Y)) ⧸
          (A ⊓ Subgroup.normalizer (N : Set Y) ⊓ N).subgroupOf
            (A ⊓ Subgroup.normalizer (N : Set Y))) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨u, ⟨huA, huN⟩⟩ : ↥(A ⊓ Subgroup.normalizer (N : Set Y))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hu3)
      rw [this, QuotientGroup.mk_one]
    have hq1 : (QuotientGroup.mk (⟨u, ⟨huA, huN⟩⟩ : ↥(A ⊓ Subgroup.normalizer (N : Set Y))) :
        ↥(A ⊓ Subgroup.normalizer (N : Set Y)) ⧸
          (A ⊓ Subgroup.normalizer (N : Set Y) ⊓ N).subgroupOf
            (A ⊓ Subgroup.normalizer (N : Set Y))) ≠ 1 := fun h =>
      hun (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)).2
    rw [← orderOf_eq_prime hq3 hq1]
    exact orderOf_dvd_natCard _
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((A ⊓ Subgroup.normalizer (N : Set Y) ⊓ N).subgroupOf (A ⊓ Subgroup.normalizer (N : Set Y)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hcard
  have h9 : 9 ∣ Nat.card ↥(A ⊓ Subgroup.normalizer (N : Set Y)) := by
    rw [hcard, show (9 : ℕ) = 3 * 3 by norm_num]
    exact Nat.mul_dvd_mul h2 h1
  exact h9.trans (Subgroup.card_dvd_of_le inf_le_left)

end Generic

variable {G : Type} [Group G] {T L V H : Subgroup G}

theorem card_modO2Image_dvd_card {A : Subgroup G} :
    Nat.card ↥(modO2Image H A) ∣ Nat.card ↥A := by
  refine (Subgroup.card_map_dvd (A.subgroupOf H) (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).trans ?_
  refine Subgroup.card_dvd_of_injective (MonoidHom.codRestrict
    (H.subtype.comp (A.subgroupOf H).subtype) A fun x => Subgroup.mem_subgroupOf.mp x.2) ?_
  intro x y hxy
  have h1 := congrArg (fun z : ↥A => (z : G)) hxy
  exact Subtype.ext (Subtype.ext h1)

variable [Finite G]

theorem pRank_three_star_le_two (S : Setting147 G T L V H) :
    Open.pRank 3 (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥H) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hq := CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.pCore 2 ↥H) hN
  have hsq : CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) ≤ 2 :=
    stronglyQuasithin_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hz.1.2 3 Nat.prime_three (by norm_num)
  omega

end CFSG.Quasithin.H13.L32A.C
