module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
import CFSG.GroupTheory.OddPrimeDvdOddOrderClosure
import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem conj_conj_eq_self {G : Type*} [Group G] {u : G} (hu : u * u = 1) (t : G) :
    u * (u * t * u⁻¹) * u⁻¹ = t := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu
  rw [huinv]
  calc u * (u * t * u) * u = (u * u) * t * (u * u) := by group
    _ = t := by rw [hu, one_mul, mul_one]

private theorem oUpperTwo_le_of_index_two {S : Type} [Group S] [Finite S]
    (hS : Nat.card S = 6) {N : Subgroup S}
    (hidx : N.index = 2) : S17.oUpperTwo (⊤ : Subgroup S) ≤ N := by
  rw [S17.oUpperTwo_eq_closure]
  refine (Subgroup.closure_le N).mpr ?_
  rintro x ⟨-, hodd⟩
  have hdvd6 : orderOf x ∣ 6 := by
    rw [← hS]
    exact orderOf_dvd_natCard x
  have hdvd3 : orderOf x ∣ 3 :=
    Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hodd) (by simpa using hdvd6)
  have hx3 : x ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd3
  have hx : x = (x ^ 2)⁻¹ := by
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 * (x ^ 2)⁻¹ := by rw [hx3]
      _ = (x ^ 2)⁻¹ := by rw [one_mul]
  rw [hx]
  exact N.inv_mem (Subgroup.sq_mem_of_index_two hidx x)

theorem card_oUpperTwo_of_card_six {S : Type} [Group S] [Finite S] (hS : Nat.card S = 6) :
    Nat.card (S17.oUpperTwo (⊤ : Subgroup S)) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hTcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := S) 3 (n := 1) (by rw [hS]; norm_num)
  have hTcard3 : Nat.card T = 3 := by simpa using hTcard
  have hTindex : T.index = 2 := by
    have h := T.card_mul_index
    rw [hTcard3, hS] at h
    omega
  have hle : S17.oUpperTwo (⊤ : Subgroup S) ≤ T := oUpperTwo_le_of_index_two hS hTindex
  have hdvd : Nat.card (S17.oUpperTwo (⊤ : Subgroup S)) ∣ 3 := by
    rw [← hTcard3]
    exact Subgroup.card_dvd_of_le hle
  have h3dvd : 3 ∣ Nat.card (S17.oUpperTwo (⊤ : Subgroup S)) := by
    rw [S17.oUpperTwo_eq_closure, ← CFSG.GroupTheory.oddOrderClosure_eq_closure]
    refine CFSG.GroupTheory.odd_prime_dvd_card_oUpperTwo (p := 3) (G := S)
      Nat.prime_three (by norm_num) (H := ⊤) ?_
    rw [Subgroup.card_top, hS]
    norm_num
  exact Nat.dvd_antisymm hdvd h3dvd

theorem oUpperTwo_le_of_normal_of_card_six {S : Type} [Group S] [Finite S] (hS : Nat.card S = 6)
    (hnc : ∃ a b : S, a * b ≠ b * a) {N : Subgroup S} (hN : N.Normal) (hne : N ≠ ⊥) :
    S17.oUpperTwo (⊤ : Subgroup S) ≤ N := by
  haveI : N.Normal := hN
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNcard_dvd : Nat.card N ∣ 6 := by
    rw [← hS]
    exact Subgroup.card_subgroup_dvd_card N
  have hNle : Nat.card N ≤ 6 := Nat.le_of_dvd (by norm_num) hNcard_dvd
  have hle : 0 < Nat.card N := Nat.card_pos
  interval_cases hcard : Nat.card N
  · exact absurd (Subgroup.eq_bot_of_card_eq N hcard) hne
  · exfalso
    have hNcenter : N ≤ Subgroup.center S := by
      intro n hn
      rw [Subgroup.mem_center_iff]
      intro g
      by_cases hn1 : n = 1
      · rw [hn1, mul_one, one_mul]
      · have hconj : g * n * g⁻¹ ∈ N := hN.conj_mem n hn g
        have hconj_ne : g * n * g⁻¹ ≠ 1 := by
          intro h
          apply hn1
          calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
            _ = g⁻¹ * 1 * g := by rw [h]
            _ = 1 := by group
        have hNncard : (N : Set S).ncard = 2 := by
          rw [← Nat.card_coe_set_eq]
          exact hcard
        have hNset : ({1, n} : Set S) = (N : Set S) := by
          refine Set.eq_of_subset_of_ncard_le ?_ ?_
          · intro x hx
            rcases hx with rfl | rfl
            · exact N.one_mem
            · exact hn
          · rw [hNncard, Set.ncard_pair (Ne.symm hn1)]
        have hconj' : g * n * g⁻¹ ∈ ({1, n} : Set S) := hNset.symm ▸ hconj
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hconj'
        rcases hconj' with h | h
        · exact absurd h hconj_ne
        · calc g * n = (g * n * g⁻¹) * g := by group
            _ = n * g := by rw [h]
    have hquotcard : Nat.card (S ⧸ N) = 3 := by
      have h := N.card_mul_index
      rw [hcard, hS] at h
      have hNindex : N.index = 3 := by omega
      rw [← Subgroup.index_eq_card, hNindex]
    haveI : IsCyclic (S ⧸ N) := isCyclic_of_prime_card hquotcard
    haveI : IsMulCommutative S :=
      MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' N)
        (by rw [QuotientGroup.ker_mk']; exact hNcenter)
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (mul_comm' a b)
  · refine oUpperTwo_le_of_index_two hS ?_
    have h := N.card_mul_index
    rw [hcard, hS] at h
    omega
  · norm_num at hNcard_dvd
  · norm_num at hNcard_dvd
  · have htop : N = ⊤ := Subgroup.eq_top_of_card_eq N (by rw [hcard, hS])
    rw [htop]
    exact le_top

theorem opp_top_of_card_eighteen {G : Type} [Group G] [Finite G] (hG : Nat.card G = 18)
    {C : Subgroup G} (hC : C ≤ Subgroup.center G) (hC3 : Nat.card C = 3)
    (hnc : ∃ a b : G, a * b * a⁻¹ * b⁻¹ ∉ C) :
    Nat.card (Opp 2 (⊤ : Subgroup G)) = 6 ∧
      ∃ a ∈ Opp 2 (⊤ : Subgroup G), ∃ b ∈ Opp 2 (⊤ : Subgroup G), a * b ≠ b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hTcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := G) 3 (n := 2) (by rw [hG]; norm_num)
  have hTcard9 : Nat.card T = 9 := by simpa using hTcard
  have hTindex : T.index = 2 := by
    have h := T.card_mul_index
    rw [hTcard9, hG] at h
    omega
  have hTnormal : T.Normal := Subgroup.normal_of_index_eq_two hTindex
  have hTabelian : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := ↥T)
      (by rw [hTcard9]; norm_num)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h
  obtain ⟨u, hu2⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (by rw [hG]; norm_num)
  have hu2' : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
  have huT : u ∉ T := by
    intro hu
    have h9 : orderOf u ∣ Nat.card T := T.orderOf_dvd_natCard hu
    rw [hTcard9] at h9
    have h2 : orderOf u ∣ 2 := by rw [hu2]
    have hg : orderOf u ∣ 1 := by
      have := Nat.dvd_gcd h2 h9
      rwa [show Nat.gcd 2 9 = 1 by norm_num] at this
    have hu1 : u ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hu2
      norm_num at hu2
    exact absurd (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)) hu1
  have hGT : T ⊔ Subgroup.zpowers u = ⊤ := by
    have hlt : T < T ⊔ Subgroup.zpowers u := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro heq
      apply huT
      have hmem : u ∈ T ⊔ Subgroup.zpowers u :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
      rwa [← heq] at hmem
    have hcard_gt : 9 < Nat.card ↥(T ⊔ Subgroup.zpowers u) := by
      rw [← hTcard9]
      by_contra hcon
      exact hlt.ne (Subgroup.eq_of_le_of_card_ge le_sup_left (not_lt.mp hcon))
    have hdvd1 : Nat.card T ∣ Nat.card ↥(T ⊔ Subgroup.zpowers u) :=
      Subgroup.card_dvd_of_le le_sup_left
    have hdvd2 : Nat.card ↥(T ⊔ Subgroup.zpowers u) ∣ Nat.card G :=
      Subgroup.card_subgroup_dvd_card _
    rw [hTcard9] at hdvd1
    rw [hG] at hdvd2
    have hle18 : Nat.card ↥(T ⊔ Subgroup.zpowers u) ≤ 18 :=
      Nat.le_of_dvd (by norm_num) hdvd2
    have hc18 : Nat.card ↥(T ⊔ Subgroup.zpowers u) = 18 := by
      generalize Nat.card ↥(T ⊔ Subgroup.zpowers u) = c at hdvd1 hdvd2 hcard_gt hle18 ⊢
      interval_cases c <;> omega
    apply Subgroup.eq_top_of_card_eq
    rw [hc18, hG]
  have hcoset : ∀ g : G, g ∈ T ∨ ∃ t ∈ T, g = t * u := by
    intro g
    by_cases hg : g ∈ T
    · exact Or.inl hg
    · right
      have hgu : g * u ∈ T := by
        rw [Subgroup.mul_mem_iff_of_index_two hTindex]
        exact ⟨fun h => absurd h hg, fun h => absurd h huT⟩
      exact ⟨g * u, hgu, by rw [mul_assoc, hu2', mul_one]⟩
  have hnontriv : ∃ t ∈ T, u * t * u⁻¹ ≠ t := by
    by_contra hcon
    push Not at hcon
    have hut : ∀ t ∈ T, u * t = t * u := by
      intro t ht
      calc u * t = (u * t * u⁻¹) * u := by group
        _ = t * u := by rw [hcon t ht]
    have hTcenter : T ≤ Subgroup.center G := by
      intro t ht
      rw [Subgroup.mem_center_iff]
      intro g
      rcases hcoset g with hgT | ⟨s, hsT, rfl⟩
      · exact hTabelian g hgT t ht
      · calc (s * u) * t = s * (u * t) := by group
          _ = s * (t * u) := by rw [hut t ht]
          _ = (s * t) * u := by group
          _ = (t * s) * u := by rw [← hTabelian t ht s hsT]
          _ = t * (s * u) := by group
    have hucenter : u ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      rcases hcoset g with hgT | ⟨s, hsT, rfl⟩
      · exact (hut g hgT).symm
      · have h1 : (s * u) * u = s := by rw [mul_assoc, hu2', mul_one]
        have h2 : u * (s * u) = s := by
          calc u * (s * u) = (u * s) * u := by group
            _ = (s * u) * u := by rw [hut s hsT]
            _ = s := h1
        exact h1.trans h2.symm
    have hcenterTop : Subgroup.center G = ⊤ := by
      apply le_antisymm le_top
      rw [← hGT]
      exact sup_le hTcenter (Subgroup.zpowers_le.mpr hucenter)
    haveI : IsMulCommutative G := Subgroup.center_eq_top_iff.mp hcenterTop
    obtain ⟨a, b, hab⟩ := hnc
    refine hab ?_
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := by rw [mul_comm' a b]; group
    rw [h1]
    exact C.one_mem
  let D : Subgroup G :=
    { carrier := {t : G | t ∈ T ∧ u * t * u⁻¹ = t⁻¹}
      mul_mem' := by
        intro a b ha hb
        obtain ⟨haT, haα⟩ := ha
        obtain ⟨hbT, hbα⟩ := hb
        refine ⟨T.mul_mem haT hbT, ?_⟩
        show u * (a * b) * u⁻¹ = (a * b)⁻¹
        rw [show u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) by group, haα, hbα]
        rw [mul_inv_rev]
        have hcomm' : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
          calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
            _ = (a * b)⁻¹ := by rw [← hTabelian a haT b hbT]
            _ = b⁻¹ * a⁻¹ := by group
        exact hcomm'
      one_mem' := by
        refine ⟨T.one_mem, ?_⟩
        show u * 1 * u⁻¹ = (1 : G)⁻¹
        group
      inv_mem' := by
        intro a ha
        obtain ⟨haT, haα⟩ := ha
        refine ⟨T.inv_mem haT, ?_⟩
        show u * a⁻¹ * u⁻¹ = (a⁻¹)⁻¹
        calc u * a⁻¹ * u⁻¹ = (u * a * u⁻¹)⁻¹ := by group
          _ = (a⁻¹)⁻¹ := by rw [haα] }
  have hDleT : D ≤ T := fun d hd => hd.1
  have hDne : D ≠ ⊥ := by
    intro hbot
    obtain ⟨t, htT, htne⟩ := hnontriv
    have hsD : (u * t * u⁻¹) * t⁻¹ ∈ D := by
      refine ⟨T.mul_mem (hTnormal.conj_mem t htT u) (T.inv_mem htT), ?_⟩
      show u * ((u * t * u⁻¹) * t⁻¹) * u⁻¹ = ((u * t * u⁻¹) * t⁻¹)⁻¹
      rw [show u * ((u * t * u⁻¹) * t⁻¹) * u⁻¹
            = (u * (u * t * u⁻¹) * u⁻¹) * (u * t⁻¹ * u⁻¹) by group,
          conj_conj_eq_self hu2' t]
      group
    have hsne : (u * t * u⁻¹) * t⁻¹ ≠ 1 := by
      intro h
      apply htne
      calc u * t * u⁻¹ = ((u * t * u⁻¹) * t⁻¹) * t := by group
        _ = 1 * t := by rw [h]
        _ = t := one_mul _
    rw [hbot] at hsD
    exact hsne (Subgroup.mem_bot.mp hsD)
  have hDne1 : Nat.card D ≠ 1 := fun h => hDne (Subgroup.eq_bot_of_card_eq D h)
  have hCT : C ≤ T := by
    intro c hc
    have hc3C : (⟨c, hc⟩ : C) ^ 3 = 1 := by
      have hdvd : orderOf (⟨c, hc⟩ : C) ∣ 3 := by
        rw [← hC3]
        exact orderOf_dvd_natCard _
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hc3 : c ^ 3 = 1 := by
      have := congrArg (Subtype.val) hc3C
      simpa using this
    have hc2T : c ^ 2 ∈ T := Subgroup.sq_mem_of_index_two hTindex c
    have hceq : c = (c ^ 2)⁻¹ := by
      calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
        _ = 1 * (c ^ 2)⁻¹ := by rw [hc3]
        _ = (c ^ 2)⁻¹ := by rw [one_mul]
    rw [hceq]
    exact T.inv_mem hc2T
  have hCD : C ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    obtain ⟨hcC, hcD⟩ := hc
    obtain ⟨hcT, hcα⟩ := hcD
    have hc_central : u * c * u⁻¹ = c := by
      have hcent : c ∈ Subgroup.center G := hC hcC
      have hcu : u * c = c * u := (Subgroup.mem_center_iff.mp hcent) u
      calc u * c * u⁻¹ = (c * u) * u⁻¹ := by rw [hcu]
        _ = c := by rw [mul_assoc, mul_inv_cancel, mul_one]
    have hcinv : c = c⁻¹ := by rw [← hcα, hc_central]
    have hc2 : c * c = 1 := (eq_inv_iff_mul_eq_one).mp hcinv
    have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hc2)
    have h3 : orderOf c ∣ 3 := by
      have h := orderOf_dvd_natCard (⟨c, hcC⟩ : C)
      rw [hC3] at h
      rwa [← Subgroup.orderOf_coe (⟨c, hcC⟩ : C)] at h
    have hone : orderOf c = 1 := by
      have := Nat.dvd_gcd h2 h3
      rwa [show Nat.gcd 2 3 = 1 by norm_num, Nat.dvd_one] at this
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)
  have hTu : T ⊓ Subgroup.zpowers u = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxT, hxu⟩ := hx
    have hx2 : orderOf x ∣ 2 := by
      have h := (Subgroup.zpowers u).orderOf_dvd_natCard hxu
      rwa [Nat.card_zpowers, hu2] at h
    have hx9 : orderOf x ∣ 9 := by
      have h := T.orderOf_dvd_natCard hxT
      rwa [hTcard9] at h
    have hone : orderOf x = 1 := by
      have := Nat.dvd_gcd hx2 hx9
      rwa [show Nat.gcd 2 9 = 1 by norm_num, Nat.dvd_one] at this
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)
  have hDu : D ⊓ Subgroup.zpowers u = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : x ∈ T ⊓ Subgroup.zpowers u := ⟨hDleT hx.1, hx.2⟩
    rw [hTu] at hx'
    exact Subgroup.mem_bot.mp hx'
  have hDnormC : D ≤ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro d hd c hc
    have heq : d * c * d⁻¹ = c := by
      calc d * c * d⁻¹ = (d * c) * d⁻¹ := by group
        _ = (c * d) * d⁻¹ := by rw [hTabelian d (hDleT hd) c (hCT hc)]
        _ = c := by rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [heq]
    exact hc
  have hcardCD : Nat.card (C ⊔ D : Subgroup G) = 3 * Nat.card D := by
    have h := CFSG.GH74.GLS.Stage1.Thm3.Sec4.M.card_sup_mul_card_inf
      (A := C) (B := D) hDnormC
    rw [hCD, Subgroup.card_bot, mul_one, hC3] at h
    exact h
  have hDsupDvd : Nat.card (C ⊔ D : Subgroup G) ∣ 9 := by
    rw [← hTcard9]
    exact Subgroup.card_dvd_of_le (sup_le hCT hDleT)
  have hDle3 : Nat.card D ≤ 3 := by
    have hle9 : Nat.card (C ⊔ D : Subgroup G) ≤ 9 := Nat.le_of_dvd (by norm_num) hDsupDvd
    omega
  have hDdvd : Nat.card D ∣ 9 := by
    rw [← hTcard9]
    exact Subgroup.card_dvd_of_le hDleT
  have hD3 : Nat.card D = 3 := by
    obtain ⟨k, hk2, hk⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three (m := 2)).1 (by simpa using hDdvd)
    have hkpos : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero] at hk
      exact hDne1 hk
    have hkle1 : k ≤ 1 := by
      have hpow : 3 ^ k ≤ 3 ^ 1 := by rw [pow_one, ← hk]; exact hDle3
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpow
    have hk1 : k = 1 := by omega
    rw [hk, hk1]
    norm_num
  have mem_opp_of_sq_eq_one : ∀ {x : G}, x * x = 1 → x ∈ Opp 2 (⊤ : Subgroup G) := by
    intro x hx
    change x ∈ Subgroup.closure {y : G | y ∈ (⊤ : Subgroup G) ∧ ∃ k, orderOf y = 2 ^ k}
    apply Subgroup.subset_closure
    refine ⟨trivial, ?_⟩
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    obtain ⟨j, -, hj⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two (m := 1)).1 (by simpa using hdvd)
    exact ⟨j, hj⟩
  have huOpp : u ∈ Opp 2 (⊤ : Subgroup G) := mem_opp_of_sq_eq_one hu2'
  have hDle : D ≤ Opp 2 (⊤ : Subgroup G) := by
    intro d hd
    have hud : u * d = d⁻¹ * u := by
      calc u * d = (u * d * u⁻¹) * u := by group
        _ = d⁻¹ * u := by rw [hd.2]
    have hdu_sq : (d * u) * (d * u) = 1 := by
      calc (d * u) * (d * u) = d * (u * d) * u := by group
        _ = d * (d⁻¹ * u) * u := by rw [hud]
        _ = (d * d⁻¹) * (u * u) := by group
        _ = 1 := by rw [mul_inv_cancel, hu2', mul_one]
    have hduOpp : d * u ∈ Opp 2 (⊤ : Subgroup G) := mem_opp_of_sq_eq_one hdu_sq
    have hmem : (d * u) * u ∈ Opp 2 (⊤ : Subgroup G) :=
      (Opp 2 (⊤ : Subgroup G)).mul_mem hduOpp huOpp
    rwa [mul_assoc, hu2', mul_one] at hmem
  have hule : Subgroup.zpowers u ≤ Opp 2 (⊤ : Subgroup G) :=
    Subgroup.zpowers_le.mpr huOpp
  have hOppLe : Opp 2 (⊤ : Subgroup G) ≤ D ⊔ Subgroup.zpowers u := by
    change Subgroup.closure {y : G | y ∈ (⊤ : Subgroup G) ∧ ∃ k, orderOf y = 2 ^ k} ≤
      D ⊔ Subgroup.zpowers u
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    obtain ⟨-, ⟨k, hk⟩⟩ := hx
    rcases hcoset x with hxT | ⟨t, htT, rfl⟩
    · have hx9 : 2 ^ k ∣ 9 := by
        rw [← hk, ← hTcard9]
        exact T.orderOf_dvd_natCard hxT
      have hcop : Nat.Coprime (2 ^ k) 9 :=
        (Nat.coprime_two_left.mpr (by norm_num : Odd 9)).pow_left k
      have hpow1 : 2 ^ k = 1 := by
        have h := hcop.dvd_of_dvd_mul_left (show 2 ^ k ∣ 9 * 1 by simpa using hx9)
        rwa [Nat.dvd_one] at h
      have hone : orderOf x = 1 := by rw [hk, hpow1]
      have hx1 : x = 1 := orderOf_eq_one_iff.mp hone
      rw [hx1]
      exact Subgroup.mem_sup_left D.one_mem
    · have hdvd18 : 2 ^ k ∣ 18 := by
        rw [← hk, ← hG]
        exact orderOf_dvd_natCard (t * u)
      have hcop : Nat.Coprime (2 ^ k) 9 :=
        (Nat.coprime_two_left.mpr (by norm_num : Odd 9)).pow_left k
      have hdvd2 : 2 ^ k ∣ 2 :=
        Nat.Coprime.dvd_of_dvd_mul_left hcop
          (by rw [show 9 * 2 = 18 by norm_num]; exact hdvd18)
      have hsq : (t * u) * (t * u) = 1 := by
        have hdvd : orderOf (t * u) ∣ 2 := by rw [hk]; exact hdvd2
        rw [← pow_two]
        exact orderOf_dvd_iff_pow_eq_one.mp hdvd
      have htD : t ∈ D := by
        refine ⟨htT, ?_⟩
        have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2'
        rw [huinv]
        calc u * t * u = t⁻¹ * ((t * u) * (t * u)) := by group
          _ = t⁻¹ * 1 := by rw [hsq]
          _ = t⁻¹ := by rw [mul_one]
      exact Subgroup.mul_mem_sup htD (Subgroup.mem_zpowers u)
  have hOppGe : D ⊔ Subgroup.zpowers u ≤ Opp 2 (⊤ : Subgroup G) := sup_le hDle hule
  have hOppEq : Opp 2 (⊤ : Subgroup G) = D ⊔ Subgroup.zpowers u :=
    le_antisymm hOppLe hOppGe
  have hDnormu : Subgroup.zpowers u ≤ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_set_normalizer_iff]
    intro d
    constructor
    · intro hd
      rw [hd.2]
      exact D.inv_mem hd
    · intro hd
      have hde : u * (u * d * u⁻¹) * u⁻¹ = d := conj_conj_eq_self hu2' d
      rw [← hde, hd.2]
      exact D.inv_mem hd
  have hDsup_card : Nat.card (D ⊔ Subgroup.zpowers u : Subgroup G) = 6 := by
    have hcard := CFSG.GH74.GLS.Stage1.Thm3.Sec4.M.card_sup_mul_card_inf
      (A := D) (B := Subgroup.zpowers u) hDnormu
    rw [hDu, Subgroup.card_bot, mul_one, hD3, Nat.card_zpowers, hu2] at hcard
    norm_num at hcard
    exact hcard
  obtain ⟨d, hd3⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 3 (by rw [hD3])
  have hdD : (d : G) ∈ D := d.2
  have hd_ne : (d : G) ≠ 1 := by
    intro h
    have hd_eq : d = 1 := Subtype.ext h
    rw [hd_eq, orderOf_one] at hd3
    omega
  have hdu_sq : ((d : G) * u) * ((d : G) * u) = 1 := by
    have hud : u * (d : G) = (d : G)⁻¹ * u := by
      calc u * (d : G) = (u * (d : G) * u⁻¹) * u := by group
        _ = (d : G)⁻¹ * u := by rw [hdD.2]
    calc ((d : G) * u) * ((d : G) * u) = (d : G) * (u * (d : G)) * u := by group
      _ = (d : G) * ((d : G)⁻¹ * u) * u := by rw [hud]
      _ = ((d : G) * (d : G)⁻¹) * (u * u) := by group
      _ = 1 := by rw [mul_inv_cancel, hu2', mul_one]
  have hduOpp : (d : G) * u ∈ Opp 2 (⊤ : Subgroup G) := mem_opp_of_sq_eq_one hdu_sq
  have hneq : u * ((d : G) * u) ≠ ((d : G) * u) * u := by
    have hL : u * ((d : G) * u) = (d : G)⁻¹ := by
      have hud : u * (d : G) = (d : G)⁻¹ * u := by
        calc u * (d : G) = (u * (d : G) * u⁻¹) * u := by group
          _ = (d : G)⁻¹ * u := by rw [hdD.2]
      calc u * ((d : G) * u) = (u * (d : G)) * u := by group
        _ = ((d : G)⁻¹ * u) * u := by rw [hud]
        _ = (d : G)⁻¹ := by rw [mul_assoc, hu2', mul_one]
    have hR : ((d : G) * u) * u = (d : G) := by rw [mul_assoc, hu2', mul_one]
    intro h
    have hdeq : (d : G)⁻¹ = (d : G) := by rw [← hL, h, hR]
    have hd2 : (d : G) * (d : G) = 1 := (eq_inv_iff_mul_eq_one).mp hdeq.symm
    have hdord2 : orderOf (d : G) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hd2)
    have hdord3 : orderOf (d : G) ∣ 3 := by
      have h := orderOf_dvd_natCard d
      rw [hD3] at h
      rwa [← Subgroup.orderOf_coe d] at h
    have hone : orderOf (d : G) = 1 := by
      have := Nat.dvd_gcd hdord2 hdord3
      rwa [show Nat.gcd 2 3 = 1 by norm_num, Nat.dvd_one] at this
    exact hd_ne (orderOf_eq_one_iff.mp hone)
  refine ⟨?_, u, huOpp, (d : G) * u, hduOpp, hneq⟩
  rw [hOppEq]
  exact hDsup_card

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
