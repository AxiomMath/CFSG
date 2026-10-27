module

public import CFSG.Quasithin.H13.L32NKGSp6Conj

public section

namespace CFSG.Quasithin.H13.KGSp6

open CFSG.KGroups.Sp6

theorem n0List_length : n0List.length = 42 := by decide

theorem n0List_nodup : n0List.Nodup := by decide

theorem n0List_valid : ∀ n ∈ n0List, KGCert.ValidC n := by
  unfold KGCert.ValidC
  decide

theorem colsOf_mem_n0List (h2 : normCheck 64 s0 n0List = true) {x : Mat6ˣ} (hx : x ∈ SpU)
    (hn : x * s0u * x⁻¹ ∈ Subgroup.zpowers s0u) : colsOf (x : Mat6) ∈ n0List := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn
  have hord := orderOf_s0u
  have hk' : s0u ^ (k % 7) = x * s0u * x⁻¹ := by
    have := zpow_mod_orderOf s0u k
    rw [hord] at this
    rw [← hk]
    exact_mod_cast this
  have hne : (k % 7).toNat ≠ 0 := by
    intro h0
    have hk0 : k % 7 = 0 := by
      have := Int.emod_nonneg k (by norm_num : (7 : ℤ) ≠ 0)
      omega
    rw [hk0, zpow_zero] at hk'
    have h1 : s0u = 1 := by
      have h2 := mul_inv_eq_one.1 hk'.symm
      exact mul_left_cancel (a := x) (by rw [h2, mul_one])
    have := orderOf_s0u
    rw [h1, orderOf_one] at this
    omega
  set j := (k % 7).toNat with hj
  have hjle : j < 7 := by omega
  have hkj : s0u ^ (k % 7) = s0u ^ j := by
    have h7 : k % 7 = (j : ℤ) := by
      have := Int.emod_nonneg k (by norm_num : (7 : ℤ) ≠ 0)
      omega
    rw [h7, zpow_natCast]
  have hmat : (x : Mat6) * KGCert.decodeC s0 = KGCert.decodeC (powC s0 j) * (x : Mat6) := by
    have h := congrArg Units.val (show s0u ^ j * x = x * s0u by
      rw [← hkj, hk']
      exact inv_mul_cancel_right _ _)
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, coe_s0u] at h
    rw [decodeC_powC validC_s0]
    exact h.symm
  have hxv := validC_colsOf (x : Mat6)
  have hlist : mulC (colsOf (x : Mat6)) s0 = mulC (powC s0 j) (colsOf (x : Mat6)) := by
    apply KGCert.decodeC_injOn (by rw [mulC_eq]; exact KGCert.validC_mulC hxv validC_s0)
      (by rw [mulC_eq]; exact KGCert.validC_mulC (validC_powC validC_s0 j) hxv)
    rw [mulC_eq, KGCert.decodeC_mulC _ _ validC_s0.1, KGCert.decodeC_mulC _ _ hxv.1,
      decodeC_colsOf, decodeC_powC validC_s0]
    rw [← decodeC_powC validC_s0]
    exact hmat
  refine mem_of_normCheck h2 (colsOf_mem_spLeaves hx) ?_
  rw [List.any_eq_true]
  refine ⟨powC s0 j, ?_, ?_⟩
  · rw [List.mem_map]
    exact ⟨j - 1, List.mem_range.2 (by omega), by rw [Nat.sub_add_cancel (by omega)]⟩
  · rw [beq_iff_eq]
    exact hlist


theorem n0List_decodeC_nodup : (n0List.map KGCert.decodeC).Nodup :=
  n0List_nodup.map_on fun x hx y hy h =>
    KGCert.decodeC_injOn (n0List_valid x hx) (n0List_valid y hy) h

theorem n0List_le (h2 : normCheck 64 s0 n0List = true) {Γ₁ : Subgroup Mat6ˣ} (hΓ₁ : Γ₁ ≤ SpU)
    (hcard : Nat.card Γ₁ = 12096) (hP0 : Subgroup.zpowers s0u ≤ Γ₁) :
    ∀ n ∈ n0List, ∃ u ∈ Γ₁, (u : Mat6) = KGCert.decodeC n := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfac : (Nat.card Γ₁).factorization 7 = 1 := by
    rw [hcard]
    exact factorization_seven_b
  let P0' : Subgroup Γ₁ := (Subgroup.zpowers s0u).subgroupOf Γ₁
  have hP0card : Nat.card P0' = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP0).toEquiv, Nat.card_zpowers, orderOf_s0u]
  let P : Sylow 7 Γ₁ := Sylow.ofCard P0' (by rw [hP0card, hfac, pow_one])
  let N : Subgroup Γ₁ := Subgroup.normalizer ((P : Subgroup Γ₁) : Set Γ₁)
  have hmod := card_sylow_modEq_one 7 Γ₁
  have hidx := Sylow.card_eq_index_normalizer P
  have hprod := Subgroup.card_mul_index N
  let f : N → Mat6 := fun y => ((y.1 : Γ₁) : Mat6ˣ).val
  have hf : ∀ y : N, colsOf (f y) ∈ n0List := by
    intro y
    have hs : (⟨s0u, hP0 (Subgroup.mem_zpowers s0u)⟩ : Γ₁) ∈ (P : Subgroup Γ₁) :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers s0u)
    have h3 := (Subgroup.mem_normalizer_iff.1 y.2 _).1 hs
    have h4 := Subgroup.mem_subgroupOf.1 h3
    exact colsOf_mem_n0List h2 (hΓ₁ y.1.2) h4
  have hfinj : Function.Injective f := fun y z h =>
    Subtype.ext (Subtype.ext (Units.ext h))
  let NF : Finset Mat6 := (n0List.map KGCert.decodeC).toFinset
  have hNFcard : NF.card = 42 := by
    rw [List.toFinset_card_of_nodup n0List_decodeC_nodup, List.length_map, n0List_length]
  have hsub : ∀ y : N, f y ∈ NF := by
    intro y
    have := hf y
    simp only [NF, List.mem_toFinset, List.mem_map]
    exact ⟨colsOf (f y), this, decodeC_colsOf _⟩
  have : Fintype N := Fintype.ofFinite N
  have hNle : Nat.card N ≤ 42 := by
    rw [← hNFcard, Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact Finset.card_le_card_of_injOn f (fun y _ => hsub y) (fun y _ z _ h => hfinj h)
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.card N := ⟨_, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, i = Nat.card (Sylow 7 Γ₁) := ⟨_, rfl⟩
  have hi1 : i % 7 = 1 := by
    have := hmod
    rw [← hi] at this
    exact this
  have hi2 : N.index = i := by
    rw [hi, hidx]
    rfl
  have hmi : i * m = 12096 := by
    rw [← hi2, hm, mul_comm]
    exact hprod.trans hcard
  have hm42 : m = 42 := by
    have hm' : m ≤ 42 := hm ▸ hNle
    interval_cases m <;> omega
  have himg : Finset.univ.image f = NF := by
    refine Finset.eq_of_subset_of_card_le (fun M hM => ?_) ?_
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hM
      exact hsub y
    · rw [hNFcard, Finset.card_image_of_injective _ hfinj, Finset.card_univ,
        ← Nat.card_eq_fintype_card, ← hm, hm42]
  intro n hn
  have hmem : KGCert.decodeC n ∈ NF := by
    simp only [NF, List.mem_toFinset, List.mem_map]
    exact ⟨n, hn, rfl⟩
  rw [← himg] at hmem
  obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hmem
  exact ⟨(y.1 : Mat6ˣ), y.1.2, hy⟩

end CFSG.Quasithin.H13.KGSp6
