module

public import CFSG.Quasithin.H13.L32NKGSp6Norm

public section

namespace CFSG.Quasithin.H13.KGSp6

open CFSG.KGroups.Sp6

theorem pow_of_five {z : List ℕ} (hz : KGCert.ValidC z) (h : five z = true) :
    (KGCert.decodeC z) ^ 6 ≠ 1 ∧ ((KGCert.decodeC z) ^ 6) ^ 5 = 1 := by
  simp only [five, mulC_eq, oneC_eq, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨hne, hfive⟩ := h
  have hz2 : KGCert.ValidC (KGCert.mulC z z) := KGCert.validC_mulC hz hz
  have hz3 : KGCert.ValidC (KGCert.mulC (KGCert.mulC z z) z) := KGCert.validC_mulC hz2 hz
  have hd2 : KGCert.decodeC (KGCert.mulC z z) = KGCert.decodeC z * KGCert.decodeC z := by
    rw [KGCert.decodeC_mulC _ _ hz.1]
  have hd3 : KGCert.decodeC (KGCert.mulC (KGCert.mulC z z) z) =
      KGCert.decodeC z * KGCert.decodeC z * KGCert.decodeC z := by
    rw [KGCert.decodeC_mulC _ _ hz.1, hd2]
  set y := KGCert.mulC (KGCert.mulC (KGCert.mulC z z) z) (KGCert.mulC (KGCert.mulC z z) z)
    with hydef
  have hy : KGCert.ValidC y := KGCert.validC_mulC hz3 hz3
  have hd6 : KGCert.decodeC y = (KGCert.decodeC z) ^ 6 := by
    rw [hydef, KGCert.decodeC_mulC _ _ hz3.1, hd3]
    simp only [pow_succ, pow_zero, one_mul, Matrix.mul_assoc]
  have hyy : KGCert.ValidC (KGCert.mulC y y) := KGCert.validC_mulC hy hy
  have hy4 : KGCert.ValidC (KGCert.mulC (KGCert.mulC y y) (KGCert.mulC y y)) :=
    KGCert.validC_mulC hyy hyy
  refine ⟨fun h1 => hne ?_, ?_⟩
  · apply KGCert.decodeC_injOn hy KGCert.validC_oneC
    rw [hd6, h1, KGCert.decodeC_oneC]
  · have h5 := congrArg KGCert.decodeC hfive
    rw [KGCert.decodeC_mulC _ _ hy4.1, KGCert.decodeC_mulC _ _ hyy.1,
      KGCert.decodeC_mulC _ _ hy.1, hd6, KGCert.decodeC_oneC] at h5
    rw [← h5]
    simp only [pow_succ, pow_zero, one_mul, Matrix.mul_assoc]


theorem no_witness {Γ₁ : Subgroup Mat6ˣ} (hcard : Nat.card Γ₁ = 12096)
    (hN : ∀ n ∈ n0List, ∃ u ∈ Γ₁, (u : Mat6) = KGCert.decodeC n) {u : Mat6ˣ} (hu : u ∈ Γ₁) :
    ∀ n ∈ n0List, five (mulC (colsOf (u : Mat6)) n) = false := by
  intro n hn
  by_contra hfive
  have hfive' : five (mulC (colsOf (u : Mat6)) n) = true := by simpa using hfive
  obtain ⟨n', hn'Γ, hn'⟩ := hN n hn
  have hxv := validC_colsOf (u : Mat6)
  have hnv := n0List_valid n hn
  have hz : KGCert.ValidC (mulC (colsOf (u : Mat6)) n) := by
    rw [mulC_eq]
    exact KGCert.validC_mulC hxv hnv
  obtain ⟨hne, hpow⟩ := pow_of_five hz hfive'
  have hzmat : KGCert.decodeC (mulC (colsOf (u : Mat6)) n) = ((u * n' : Mat6ˣ) : Mat6) := by
    rw [mulC_eq, KGCert.decodeC_mulC _ _ hnv.1, decodeC_colsOf, Units.val_mul, hn']
  rw [hzmat] at hne hpow
  have hwΓ : (u * n') ^ 6 ∈ Γ₁ := Subgroup.pow_mem _ (Γ₁.mul_mem hu hn'Γ) 6
  have hw5 : ((u * n') ^ 6) ^ 5 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    exact hpow
  have hw1 : (u * n') ^ 6 ≠ 1 := by
    intro h
    apply hne
    have := congrArg Units.val h
    rwa [Units.val_pow_eq_pow_val] at this
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf ((u * n') ^ 6) = 5 := orderOf_eq_prime hw5 hw1
  have hdvd := orderOf_dvd_natCard (⟨(u * n') ^ 6, hwΓ⟩ : Γ₁)
  rw [Subgroup.orderOf_mk, hord, hcard] at hdvd
  omega


theorem ncard_diff_le
    (h3 : witCheck 64 KGCert.g22Elems n0List 6047 = true) {Γ₁ : Subgroup Mat6ˣ} (hΓ₁ : Γ₁ ≤ SpU)
    (hcard : Nat.card Γ₁ = 12096) (hN : ∀ n ∈ n0List, ∃ u ∈ Γ₁, (u : Mat6) = KGCert.decodeC n) :
    ((Γ₁ : Set Mat6ˣ) \ (Gsub : Set Mat6ˣ)).ncard ≤ 6047 := by
  classical
  have hP := countP_le_of_witCheck h3
  rw [List.countP_eq_length_filter] at hP
  have himg : (fun u : Mat6ˣ => colsOf (u : Mat6)) '' ((Γ₁ : Set Mat6ˣ) \ (Gsub : Set Mat6ˣ)) ⊆
      ↑(((spLeaves 64).filter fun x => !KGCert.g22Elems.contains x &&
        !n0List.any fun n => five (mulC x n))).toFinset := by
    rintro _ ⟨u, ⟨huΓ, huG⟩, rfl⟩
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter]
    refine ⟨colsOf_mem_spLeaves (hΓ₁ huΓ), ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, ?_⟩
    · have hm : ¬ (colsOf (u : Mat6) ∈ KGCert.g22Elems) := fun hm =>
        huG ((KGCert.mem_g22Mats_iff _).2 ⟨_, hm, decodeC_colsOf _⟩)
      simpa [List.contains_iff_mem] using hm
    · have := no_witness hcard hN huΓ
      rw [List.any_eq_false]
      intro n hn
      simp [this n hn]
  have hinj : Function.Injective fun u : Mat6ˣ => colsOf (u : Mat6) := colsOf_injective
  calc ((Γ₁ : Set Mat6ˣ) \ (Gsub : Set Mat6ˣ)).ncard
      = ((fun u : Mat6ˣ => colsOf (u : Mat6)) '' ((Γ₁ : Set Mat6ˣ) \ (Gsub : Set Mat6ˣ))).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ (↑(((spLeaves 64).filter fun x => !KGCert.g22Elems.contains x &&
        !n0List.any fun n => five (mulC x n))).toFinset : Set (List ℕ)).ncard :=
        Set.ncard_le_ncard himg (Finset.finite_toSet _)
    _ ≤ 6047 := by
        rw [Set.ncard_coe_finset]
        exact (List.toFinset_card_le _).trans hP

theorem le_ncard_diff {Γ₁ : Subgroup Mat6ˣ} (hcard : Nat.card Γ₁ = 12096) (hnle : ¬ Γ₁ ≤ Gsub) :
    6048 ≤ ((Γ₁ : Set Mat6ˣ) \ (Gsub : Set Mat6ˣ)).ncard := by
  have hrel : Gsub.relIndex Γ₁ ≠ 1 := fun h => hnle (Subgroup.relIndex_eq_one.1 h)
  have hmul := Subgroup.relIndex_mul_card Gsub Γ₁
  rw [hcard] at hmul
  have h2 : 2 ≤ Gsub.relIndex Γ₁ := by
    rcases Nat.lt_or_ge (Gsub.relIndex Γ₁) 2 with h | h
    · interval_cases hr : Gsub.relIndex Γ₁
      · simp at hmul
      · exact absurd rfl hrel
    · exact h
  have h3 : 2 * Nat.card ↥(Gsub ⊓ Γ₁) ≤ Gsub.relIndex Γ₁ * Nat.card ↥(Gsub ⊓ Γ₁) :=
    Nat.mul_le_mul_right _ h2
  have hint : ((Γ₁ : Set Mat6ˣ) ∩ (Gsub : Set Mat6ˣ)).ncard = Nat.card ↥(Gsub ⊓ Γ₁) := by
    rw [← Nat.card_coe_set_eq, inf_comm]
    rfl
  have hsum := Set.ncard_inter_add_ncard_sdiff_eq_ncard (Γ₁ : Set Mat6ˣ) (Gsub : Set Mat6ˣ)
    (Set.toFinite _)
  have hΓ : (Γ₁ : Set Mat6ˣ).ncard = 12096 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  omega


theorem eq_Gsub (h2 : normCheck 64 s0 n0List = true)
    (h3 : witCheck 64 KGCert.g22Elems n0List 6047 = true) {Γ₁ : Subgroup Mat6ˣ}
    (hΓ₁ : Γ₁ ≤ SpU) (hcard : Nat.card Γ₁ = 12096) (hP0 : Subgroup.zpowers s0u ≤ Γ₁) :
    Γ₁ = Gsub := by
  have hN := n0List_le h2 hΓ₁ hcard hP0
  have hle : Γ₁ ≤ Gsub := by
    by_contra hnle
    have h1' := le_ncard_diff hcard hnle
    have h2' := ncard_diff_le h3 hΓ₁ hcard hN
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_Gsub, hcard])

end CFSG.Quasithin.H13.KGSp6
