module

public import CFSG.Sporadic.Co2Smith.GlRootD1Card

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {G : Type*} [Group G] {z : G}
  {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G} {α : Cz}

theorem chartT_inv
    (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz)
    {y : K} (hy : y ∈ Ax25) : chartT φ ρ y⁻¹ = (chartT φ ρ y)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← chartT_mul hm hφz hy (Ax25.inv_mem hy), mul_inv_cancel, chartT_one hm hφz]

@[expose] noncomputable def chartN
    (hm : SmithC0Marking φ α ρ)
    (hφz : φ (zC z) = zCz) : Subgroup K where
  carrier := {y | y ∈ Ax25 ∧ chartT φ ρ y ∈ Qx25}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨Ax25.mul_mem ha hb, by rw [chartT_mul hm hφz ha hb]; exact Qx25.mul_mem ha' hb'⟩
  one_mem' := ⟨Ax25.one_mem, by rw [chartT_one hm hφz]; exact Qx25.one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨Ax25.inv_mem ha, by rw [chartT_inv hm hφz ha]; exact Qx25.inv_mem ha'⟩

theorem chartN_conj_mem
    (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz)
    {a : K} (ha : a ∈ Ax25) {y : K} (hy : y ∈ chartN hm hφz) : a * y * a⁻¹ ∈ chartN hm hφz := by
  obtain ⟨hyA, hyQ⟩ := hy
  refine ⟨Ax25.mul_mem (Ax25.mul_mem ha hyA) (Ax25.inv_mem ha), ?_⟩
  rw [chartT_mul hm hφz (Ax25.mul_mem ha hyA) (Ax25.inv_mem ha), chartT_mul hm hφz ha hyA,
    chartT_inv hm hφz ha]
  exact Qx25_conj_mem (chartT_mem hm hφz ha) hyQ

theorem natCard_chartN
    (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) : Nat.card (chartN hm hφz) = 128 := by
  rw [← natCard_Qx25]
  refine Nat.card_congr
    { toFun := fun y => ⟨chartT φ ρ y, y.2.2⟩
      invFun := fun q => ⟨chartT φ ρ q, chartT_mem hm hφz (Qx25_le_Ax25 q.2), by
        rw [chartT_chartT hm hφz (Qx25_le_Ax25 q.2)]
        exact q.2⟩
      left_inv := fun y => Subtype.ext (chartT_chartT hm hφz y.2.1)
      right_inv := fun q => Subtype.ext (chartT_chartT hm hφz (Qx25_le_Ax25 q.2)) }

theorem z0_mem_Ax25 :
    z0 ∈ Ax25 :=
  mem_Ax25.2 ⟨z0_mem_Cz, (comm_of_mem_Cz x25K_mem_Cz).symm⟩

theorem x25K_mem_Ax25 :
    x25K ∈ Ax25 :=
  mem_Ax25.2 ⟨x25K_mem_Cz, rfl⟩

theorem z0_mem_C0c : z0 ∈ C0c :=
  x16K_eq ▸ x16K_mem_C0c

theorem z0_mem_Qx25 :
    z0 ∈ Qx25 :=
  mem_Qx25.2 ⟨z0_mem_Qsub, (comm_of_mem_Cz x25K_mem_Cz).symm⟩

theorem x25K_not_mem_Qsub :
    x25K ∉ Qsub := by
  intro h
  have := ((mem_Qsub_iff_rows x25K_val d1Elt_spec.2.2.2.1 d1Elt_spec.2.2.1).1 h).2
  rw [d1Elt_spec.2.2.2.2.1] at this
  exact absurd this (by decide)

theorem x25K_mem_chartN
    (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) :
    x25K ∈ chartN hm hφz := by
  refine ⟨x25K_mem_Ax25, ?_⟩
  rw [chartT_of_mem_C0c hm hφz x25K_mem_Ax25 x25K_mem_C0c, conj_x25K_δ1hK]
  exact z0_mem_Qx25

theorem z0_not_mem_chartN
    (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) :
    z0 ∉ chartN hm hφz := by
  rintro ⟨-, h⟩
  rw [chartT_of_mem_C0c hm hφz z0_mem_Ax25 z0_mem_C0c, ← x16K_eq] at h
  exact x25K_not_mem_Qsub (mem_Qx25.1 h).1

theorem q4K_mem_Qx25 (j : ℕ) :
    q4K j ∈ Qx25 := by
  have hr : (if j < 2 then 1 else 2) < 4 := by split_ifs <;> norm_num
  have ht : j % 2 + 1 < 4 := by have := Nat.mod_lt j (by norm_num : 0 < 2); omega
  refine mem_Qx25.2 ⟨xRootK_mem_Qsub hr ht, ?_⟩
  rw [← xLongK_one]
  exact xRootK_comm_of_inChart (by omega) (by norm_num) (by split_ifs <;> decide) ht

theorem Qx25_inf_F0c_le : Qx25 ⊓ F0c 1 ≤ X0g :=
  fun _ hx => ⟨hx.1.1, hx.2.2⟩

theorem inf_Qx25_le_X0g_of_normal
    {N : Subgroup K}
    (hN : ∀ {a : K}, a ∈ Ax25 → ∀ {y : K}, y ∈ N → a * y * a⁻¹ ∈ N) (hz : z0 ∉ N) :
    N ⊓ Qx25 ≤ X0g :=
  d1_lam1 _ inf_le_right (fun _ hx j => ⟨hN (d1Gk_mem j) hx.1,
    Qx25_conj_mem (d1Gk_mem j) hx.2⟩) fun h => hz h.1

theorem le_W25_of_normal
    {N : Subgroup K}
    (hNA : N ≤ Ax25) (hN : ∀ {a : K}, a ∈ Ax25 → ∀ {y : K}, y ∈ N → a * y * a⁻¹ ∈ N)
    (hz : z0 ∉ N) : N ≤ W25 := by
  intro y hy
  refine ⟨hNA hy, fun j _ => inf_Qx25_le_X0g_of_normal hN hz ⟨?_, ?_⟩⟩
  · have hq : (q4K j)⁻¹ = q4K j := inv_eq_of_mul_eq_one_right (q4K_mul_self j)
    have h := hN (Qx25_le_Ax25 (q4K_mem_Qx25 j)) (N.inv_mem hy)
    rw [hq] at h
    rw [show y * q4K j * y⁻¹ * q4K j = y * (q4K j * y⁻¹ * q4K j) by group]
    exact N.mul_mem hy h
  · exact Qx25.mul_mem (Qx25_conj_mem (hNA hy) (q4K_mem_Qx25 j)) (q4K_mem_Qx25 j)

theorem F0c_le_W25 :
    F0c 1 ≤ W25 := by
  intro f hf
  have hfA := F0c_one_le_Ax25 hf
  refine ⟨hfA, fun j _ => Qx25_inf_F0c_le ⟨?_, ?_⟩⟩
  · exact Qx25.mul_mem (Qx25_conj_mem hfA (q4K_mem_Qx25 j)) (q4K_mem_Qx25 j)
  · have hq : (q4K j)⁻¹ = q4K j := inv_eq_of_mul_eq_one_right (q4K_mul_self j)
    have h := F0c_one_conj_mem (Qx25_le_Ax25 (q4K_mem_Qx25 j)) ((F0c 1).inv_mem hf)
    rw [hq] at h
    rw [show f * q4K j * f⁻¹ * q4K j = f * (q4K j * f⁻¹ * q4K j) by group]
    exact (F0c 1).mul_mem hf h

theorem ncard_B8_le : (B8 : Set K).ncard ≤ 8 := by
  have hsub : (B8 : Set K) ⊆ (fun t => xRootK 0 t) '' {t | t < 4} ∪
      (fun t => x25K * xRootK 0 t) '' {t | t < 4} := by
    rintro g ⟨t, ht, rfl | rfl⟩
    · exact Or.inl ⟨t, ht, rfl⟩
    · exact Or.inr ⟨t, ht, rfl⟩
  have h4 : ({t | t < 4} : Set ℕ).ncard = 4 := by
    rw [show ({t | t < 4} : Set ℕ) = ↑(Finset.range 4) by ext; simp, Set.ncard_coe_finset,
      Finset.card_range]
  have hfin : ({t | t < 4} : Set ℕ).Finite := Set.finite_lt_nat 4
  calc (B8 : Set K).ncard
      ≤ ((fun t => xRootK 0 t) '' {t | t < 4} ∪
          (fun t => x25K * xRootK 0 t) '' {t | t < 4}).ncard :=
        Set.ncard_le_ncard hsub ((hfin.image _).union (hfin.image _))
    _ ≤ ((fun t => xRootK 0 t) '' {t | t < 4}).ncard +
          ((fun t => x25K * xRootK 0 t) '' {t | t < 4}).ncard :=
        Set.ncard_union_le _ _
    _ ≤ ({t | t < 4} : Set ℕ).ncard + ({t | t < 4} : Set ℕ).ncard :=
        Nat.add_le_add (Set.ncard_image_le hfin) (Set.ncard_image_le hfin)
    _ = 8 := by rw [h4]

theorem F0c_one_eq_of_normal
    {N : Subgroup K}
    (hNA : N ≤ Ax25) (hN : ∀ {a : K}, a ∈ Ax25 → ∀ {y : K}, y ∈ N → a * y * a⁻¹ ∈ N)
    (hcard : Nat.card N = 128) (hx : x25K ∈ N) (hz : z0 ∉ N) : F0c 1 = N := by
  have hF : Nat.card (F0c 1) = 128 := card_F0c (by decide)
  rcases d1_lam2 (N ⊓ F0c 1) inf_le_right (fun _ hx j =>
      ⟨hN (d1Gk_mem j) hx.1, F0c_one_conj_mem (d1Gk_mem j) hx.2⟩)
      ⟨hx, xLongK_mem_F0c (k := 1) (by decide)⟩ with h | h
  · exfalso
    have hS : Nat.card (N ⊓ F0c 1 : Subgroup K) ≤ 8 := by
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      exact (Set.ncard_le_ncard (fun s hs => h s hs) (Set.toFinite _)).trans ncard_B8_le
    have h1 := card_mul_relIndex_of_le (le_W25_of_normal hNA hN hz)
    have h2 := card_mul_relIndex_of_le (inf_le_right : N ⊓ F0c 1 ≤ F0c 1)
    have h3 : (N ⊓ F0c 1).relIndex (F0c 1) = N.relIndex (F0c 1) := inf_relIndex_right _ _
    have hW := natCard_W25_le
    have hpos : 0 < Nat.card W25 := Nat.card_pos
    have h4 : N.relIndex (F0c 1) ≤ N.relIndex W25 :=
      relIndex_le_of_le_right F0c_le_W25 (fun h0 => by rw [h0, mul_zero] at h1; omega)
    rw [hcard] at h1
    rw [hF, h3] at h2
    have h5 : N.relIndex W25 ≤ 8 := by omega
    have h6 := Nat.mul_le_mul hS (h4.trans h5)
    omega
  · exact Subgroup.eq_of_le_of_card_ge (h.trans inf_le_left) (by rw [hcard, hF])

theorem chartN_eq
    (hm : SmithC0Marking φ α ρ)
    (hφz : φ (zC z) = zCz) : F0c 1 = chartN hm hφz :=
  F0c_one_eq_of_normal (fun _ hy => hy.1) (fun ha _ hy => chartN_conj_mem hm hφz ha hy)
    (natCard_chartN hm hφz) (x25K_mem_chartN hm hφz) (z0_not_mem_chartN hm hφz)

theorem chartT_mem_Qx25
    (hm : SmithC0Marking φ α ρ)
    (hφz : φ (zC z) = zCz) {f : K} (hf : f ∈ F0c 1) : chartT φ ρ f ∈ Qx25 := by
  rw [chartN_eq hm hφz] at hf
  exact hf.2

theorem chartT_mem_F0c
    (hm : SmithC0Marking φ α ρ)
    (hφz : φ (zC z) = zCz) {q : K} (hq : q ∈ Qx25) : chartT φ ρ q ∈ F0c 1 := by
  rw [chartN_eq hm hφz]
  refine ⟨chartT_mem hm hφz (Qx25_le_Ax25 hq), ?_⟩
  rw [chartT_chartT hm hφz (Qx25_le_Ax25 hq)]
  exact hq

theorem chartT_mem_X0g
    (hm : SmithC0Marking φ α ρ)
    (hφz : φ (zC z) = zCz) {x : K} (hx : x ∈ X0g) : chartT φ ρ x ∈ X0g :=
  Qx25_inf_F0c_le ⟨chartT_mem_Qx25 hm hφz (X0g_le_F0c hx),
    chartT_mem_F0c hm hφz (X0g_le_Qx25 hx)⟩

end CFSG.Sporadic.Co2Smith
