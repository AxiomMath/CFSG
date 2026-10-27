module

public import Certificates.Certificate7194
public import CFSG.Quasithin.H13.L32NO3Model3
public import CFSG.Quasithin.H13.L32NM22Model2

public section

namespace CFSG.Quasithin.H13.Q1447Cert

open Mat8Cert L1442M

theorem q1447Check_eq : q1447Check = true :=
  Certificates.certificate7194

theorem q1447Check_parts :
    s7InvB = true ∧ g5InvB = true ∧ m22InvB = true ∧ (∀ c ∈ [0, 1], o3InvB c = true) ∧
      s7KB = true ∧ g5KB = true ∧ m22KB = true := by
  have h := q1447Check_eq
  simp only [q1447Check, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem invol8_of {x : GL (Fin 8) (ZMod 2)} (hx1 : x ≠ 1) (hxx : x * x = 1) :
    invol8 (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))) = true := by
  simp only [invol8, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq]
  refine ⟨fun h => hx1 (O3Cert.eq_one_of_colsOf h), ?_⟩
  rw [← colsOf_mul, ← Units.val_mul, hxx, Units.val_one, colsOf_one]

theorem bigImg8_spec {x : GL (Fin 8) (ZMod 2)}
    (h : bigImg8 (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2))) = true) :
    4 < (Finset.univ.image fun v : Fin 8 → ZMod 2 =>
      (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v).card := by
  classical
  simp only [bigImg8, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hlen, hsort⟩, hlt⟩ := h
  set S := spanN (O3Cert.imgBasis (colsOf (x : Matrix (Fin 8) (Fin 8) (ZMod 2)))) with hS
  have hnd : S.Nodup := by
    have h2 : (S.mergeSort).Nodup :=
      (List.isChain_iff_pairwise.mp hsort).imp (fun hab => ne_of_lt hab)
    exact (List.mergeSort_perm _ _).nodup_iff.mp h2
  let f : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
    Matrix.mulVecLin (x : Matrix (Fin 8) (Fin 8) (ZMod 2)) + LinearMap.id
  have hmem : ∀ s ∈ S, vec8 s ∈ LinearMap.range f := by
    refine spanN_mem _ _ fun v hv => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
    refine ⟨vec8 (2 ^ j), ?_⟩
    simp only [f, LinearMap.add_apply, Matrix.mulVecLin_apply, LinearMap.id_apply]
    rw [mulVec_vec8, ← vec8_xor]
  have hsub : S.toFinset.image vec8 ⊆ Finset.univ.image fun v : Fin 8 → ZMod 2 =>
      (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v := by
    intro u hu
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v, hv⟩ := hmem s (List.mem_toFinset.mp hs)
    refine Finset.mem_image.mpr ⟨v, Finset.mem_univ _, ?_⟩
    simpa [f] using hv
  have hcard : (S.toFinset.image vec8).card = S.length := by
    rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd]
    intro a ha b hb hab
    exact vec8_inj (hlt a (List.mem_toFinset.mp ha)) (hlt b (List.mem_toFinset.mp hb)) hab
  have := Finset.card_le_card hsub
  omega

theorem invol12_of {x : GL (Fin 12) (ZMod 2)} (hx1 : x ≠ 1) (hxx : x * x = 1) :
    invol12 (MatNCert.colsN (x : Matrix (Fin 12) (Fin 12) (ZMod 2))) = true := by
  simp only [invol12, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq]
  refine ⟨fun h => hx1 (MatNCert.eq_of_colsN_eq (by rw [h, Units.val_one, MatNCert.colsN_one])),
    ?_⟩
  rw [← MatNCert.colsN_mul, ← Units.val_mul, hxx, Units.val_one, MatNCert.colsN_one]

theorem bigImg12_spec {x : GL (Fin 12) (ZMod 2)}
    (h : bigImg12 (MatNCert.colsN (x : Matrix (Fin 12) (Fin 12) (ZMod 2))) = true) :
    4 < (Finset.univ.image fun v : Fin 12 → ZMod 2 =>
      (x : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v + v).card := by
  classical
  simp only [bigImg12, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hlen, hsort⟩, hlt⟩ := h
  set S := MatNCert.spanN (imgBasis12 (MatNCert.colsN (x : Matrix (Fin 12) (Fin 12) (ZMod 2))))
    with hS
  have hnd : S.Nodup := by
    have h2 : (S.mergeSort).Nodup :=
      (List.isChain_iff_pairwise.mp hsort).imp (fun hab => ne_of_lt hab)
    exact (List.mergeSort_perm _ _).nodup_iff.mp h2
  let f : (Fin 12 → ZMod 2) →ₗ[ZMod 2] (Fin 12 → ZMod 2) :=
    Matrix.mulVecLin (x : Matrix (Fin 12) (Fin 12) (ZMod 2)) + LinearMap.id
  have hmem : ∀ s ∈ S, MatNCert.vecN 12 s ∈ LinearMap.range f := by
    refine MatNCert.spanN_mem _ _ fun v hv => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
    refine ⟨MatNCert.vecN 12 (2 ^ j), ?_⟩
    simp only [f, LinearMap.add_apply, Matrix.mulVecLin_apply, LinearMap.id_apply]
    rw [MatNCert.mulVec_vecN, ← MatNCert.vecN_xor]
  have hsub : S.toFinset.image (MatNCert.vecN 12) ⊆ Finset.univ.image
      fun v : Fin 12 → ZMod 2 => (x : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v + v := by
    intro u hu
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v, hv⟩ := hmem s (List.mem_toFinset.mp hs)
    refine Finset.mem_image.mpr ⟨v, Finset.mem_univ _, ?_⟩
    simpa [f] using hv
  have hcard : (S.toFinset.image (MatNCert.vecN 12)).card = S.length := by
    rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd]
    intro a ha b hb hab
    exact MatNCert.vecN_inj (hlt a (List.mem_toFinset.mp ha)) (hlt b (List.mem_toFinset.mp hb))
      hab
  have := Finset.card_le_card hsub
  omega

theorem s7_big
    {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ s7) (hx1 : x ≠ 1) (hxx : x * x = 1) :
    4 < (Finset.univ.image fun v : Fin 8 → ZMod 2 =>
      (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v).card := by
  have h := q1447Check_parts.1
  simp only [s7InvB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h _ ((S7Cert.mem_s7_iff x).mp hx) with h' | h'
  · rw [invol8_of hx1 hxx] at h'
    exact absurd h' (by decide)
  · exact bigImg8_spec h'

theorem g5_big
    {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ g5 true true) (hx1 : x ≠ 1) (hxx : x * x = 1) :
    4 < (Finset.univ.image fun v : Fin 8 → ZMod 2 =>
      (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v).card := by
  have h := q1447Check_parts.2.1
  simp only [g5InvB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h _ ((G5Cert.mem_gS_iff x).mp hx) with h' | h'
  · rw [invol8_of hx1 hxx] at h'
    exact absurd h' (by decide)
  · exact bigImg8_spec h'

theorem PM_big
    {x : GL (Fin 12) (ZMod 2)} (hx : x ∈ M22Cert.PM) (hx1 : x ≠ 1) (hxx : x * x = 1) :
    4 < (Finset.univ.image fun v : Fin 12 → ZMod 2 =>
      (x : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v + v).card := by
  have h := q1447Check_parts.2.2.1
  simp only [m22InvB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h _ ((M22Cert.mem_PM_iff x).mp hx) with h' | h'
  · rw [invol12_of hx1 hxx] at h'
    exact absurd h' (by decide)
  · exact bigImg12_spec h'

theorem card_image_conj {n : ℕ} (x γ : GL (Fin n) (ZMod 2)) :
    (Finset.univ.image fun v : Fin n → ZMod 2 =>
      ((γ⁻¹ * x * γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v + v).card =
    (Finset.univ.image fun v : Fin n → ZMod 2 =>
      (x : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v + v).card := by
  classical
  have hinj : Function.Injective
      (((γ⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec) := by
    intro u w h
    have := congrArg (((γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec) h
    simpa [Matrix.mulVec_mulVec] using this
  have hsurj : Function.Surjective
      (((γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec) := fun w =>
    ⟨((γ⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w, by
      simp [Matrix.mulVec_mulVec]⟩
  have hfun : (fun v : Fin n → ZMod 2 =>
      ((γ⁻¹ * x * γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v + v) =
      (((γ⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec ∘
        fun w => (x : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w + w) ∘
      ((γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec := by
    funext v
    simp only [Function.comp_apply, Matrix.mulVec_add, Units.val_mul, ← Matrix.mulVec_mulVec]
    congr 1
    simp [Matrix.mulVec_mulVec]
  rw [hfun, ← Finset.image_image, Finset.image_univ_of_surjective hsurj, ← Finset.image_image,
    Finset.card_image_of_injective _ hinj]

theorem exists_conj_mem_of_card {G : Type*} [Group G] [Finite G] {Γ P : Subgroup G}
    (hPΓ : P ≤ Γ) {a m : ℕ} (hP : Nat.card P = 2 ^ a) (hΓ : Nat.card Γ = 2 ^ a * m)
    (hm : ¬ 2 ∣ m) {x : G} (hx : x ∈ Γ) (hxx : x * x = 1) : ∃ γ ∈ Γ, γ⁻¹ * x * γ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  have hfac : (Nat.card Γ).factorization 2 = a := by
    rw [hΓ, Nat.factorization_mul (by positivity) hm0, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm,
      add_zero]
  let F : Subgroup Γ := P.subgroupOf Γ
  have hF : Nat.card F = 2 ^ (Nat.card Γ).factorization 2 := by
    rw [hfac, ← hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPΓ).toEquiv
  have hx2 : (⟨x, hx⟩ : Γ) ^ 2 = 1 := Subtype.ext (by simp [sq, hxx])
  let E : Subgroup Γ := Subgroup.zpowers ⟨x, hx⟩
  have hE : IsPGroup 2 E := by
    intro y
    refine ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
    apply Subtype.ext
    have h2 : (y : Γ) ^ 2 = 1 := by
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
    simpa using h2
  obtain ⟨S, hS⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (Sylow.ofCard F hF) S
  have hyS : (⟨x, hx⟩ : Γ) ∈ (S : Subgroup Γ) := hS (Subgroup.mem_zpowers _)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyS
  have hF' : g⁻¹ * ⟨x, hx⟩ * g ∈ F := by
    simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc] using hyS
  exact ⟨g, g.2, by simpa [F, Subgroup.mem_subgroupOf] using hF'⟩

theorem m22_big
    {x : GL (Fin 12) (ZMod 2)} (hx : x ∈ m22) (hx1 : x ≠ 1) (hxx : x * x = 1) :
    4 < (Finset.univ.image fun v : Fin 12 → ZMod 2 =>
      (x : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec v + v).card := by
  obtain ⟨γ, -, hγ⟩ := exists_conj_mem_of_card M22Cert.PM_le_m22 (a := 8) (m := 10395)
    (by rw [M22Cert.card_PM]; norm_num) (by rw [M22Cert.card_m22]; norm_num) (by decide) hx hxx
  have h1 : γ⁻¹ * x * γ ≠ 1 := fun h => hx1 (by
    have := congrArg (fun y => γ * y * γ⁻¹) h
    simpa [mul_assoc] using this)
  have h2 : γ⁻¹ * x * γ * (γ⁻¹ * x * γ) = 1 := by
    rw [show γ⁻¹ * x * γ * (γ⁻¹ * x * γ) = γ⁻¹ * (x * x) * γ by group, hxx]
    group
  rw [← card_image_conj x γ]
  exact PM_big hγ h1 h2

theorem o3_big {c : ℕ} (hc : c < 2)
    {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ O3Cert.gam c) (hx1 : x ≠ 1) (hxx : x * x = 1) :
    4 < (Finset.univ.image fun v : Fin 8 → ZMod 2 =>
      (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v).card ∨
    ∀ v, (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v ≠ vec8 (O3Cert.vS c) := by
  have h := q1447Check_parts.2.2.2.1 c (O3Cert.mem_zero_one hc)
  simp only [o3InvB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h _ ((O3Cert.mem_gam_iff hc x).mp hx) with (h' | h') | h'
  · rw [invol8_of hx1 hxx] at h'
    exact absurd h' (by decide)
  · exact Or.inl (bigImg8_spec h')
  · refine Or.inr fun v hv => ?_
    have hvlt : O3Cert.vS c < 256 := by interval_cases c <;> decide
    rw [List.any_eq_false] at h'
    apply h' (code8 v) (List.mem_range.mpr (code8_lt v))
    rw [beq_iff_eq]
    apply vec8_inj (O3Cert.xor_lt_256 (mv8_lt (valid8_colsOf _) _) (code8_lt v)) hvlt
    rw [vec8_xor, ← mulVec_vec8, vec8_code8, hv]

theorem conjB_spec {L : List (List ℕ × List ℕ × List ℕ)} {Γl Yl : List (List ℕ)} {m : ℕ}
    (h : conjB L Γl Yl m = true) {Γ : Subgroup (GL (Fin 8) (ZMod 2))}
    (hΓ : ∀ u : GL (Fin 8) (ZMod 2), u ∈ Γ ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ Γl)
    (hΓv : ∀ c ∈ Γl, Valid8 c)
    (hΓex : ∀ c ∈ Γl, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c)
    (hYv : ∀ c ∈ Yl, Valid8 c)
    (hYex : ∀ c ∈ Yl, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c)
    {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ Γ) (hxm : x ^ m = 1) :
    x ∈ Subgroup.closure {y | ∃ k ∈ Γ, ∃ w : GL (Fin 8) (ZMod 2),
      colsOf (w : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ Yl ∧ y = k * w * k⁻¹} := by
  simp only [conjB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨⟨h5, h6⟩, h7⟩ := h
  have hgen : ∀ g ∈ conjOf L, ∃ y ∈ {y | ∃ k ∈ Γ, ∃ w : GL (Fin 8) (ZMod 2),
      colsOf (w : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ Yl ∧ y = k * w * k⁻¹},
      (y : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    obtain ⟨⟨ht1, ht2⟩, ht3⟩ := h5 t ht
    obtain ⟨k, hk'⟩ := hΓex _ ht1
    have hkΓ : k ∈ Γ := (hΓ k).mpr (by rw [hk', colsOf_dec8 (hΓv _ ht1)]; exact ht1)
    obtain ⟨w, hw'⟩ := hYex _ ht3
    have hwY : colsOf (w : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ Yl := by
      rw [hw', colsOf_dec8 (hYv _ ht3)]
      exact ht3
    have hlen : t.2.1.length = 8 := by rw [← length_mul8 t.1 t.2.1, ht2]; rfl
    have hinv : dec8 t.2.1 = ((k⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
      have h1 : (k : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 t.2.1 = 1 := by
        rw [hk', ← dec8_mul8 _ _ hlen, ht2, dec8_one8]
      calc dec8 t.2.1
          = ((k⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *
              ((k : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 t.2.1) := by
            rw [Units.inv_mul_cancel_left]
        _ = ((k⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
            rw [h1, mul_one]
    refine ⟨k * w * k⁻¹, ⟨k, hkΓ, w, hwY, rfl⟩, ?_⟩
    show _ = dec8 (mul8 (mul8 t.1 t.2.2) t.2.1)
    rw [dec8_mul8 _ _ hlen, dec8_mul8 _ _ (hYv _ ht3).1, Units.val_mul, Units.val_mul, hk', hw',
      hinv]
  have hunit : ∀ g ∈ conjOf L, ∃ v : GL (Fin 8) (ZMod 2),
      (v : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g :=
    fun g hg => let ⟨y, _, hy⟩ := hgen g hg; ⟨y, hy⟩
  have hle : genSub (conjOf L) ≤ Subgroup.closure {y | ∃ k ∈ Γ, ∃ w : GL (Fin 8) (ZMod 2),
      colsOf (w : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ Yl ∧ y = k * w * k⁻¹} := by
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    obtain ⟨y, hy, hy'⟩ := hgen _ hu
    have : u = y := Units.ext (by rw [hy', dec8_colsOf])
    rw [this]
    exact Subgroup.subset_closure hy
  refine hle ((S7Cert.mem_genSub_iff_of h6 hunit x).mpr ?_)
  rcases h7 _ ((hΓ x).mp hx) with h8 | h8
  · exact absurd (by rw [← O3Cert.colsOf_pow, hxm, Units.val_one, colsOf_one]) h8
  · exact h8

theorem oTwoUpper_le_of_pow {G : Type*} [Group G] {Γ N : Subgroup G} {a m : ℕ}
    (hΓ : Nat.card Γ = 2 ^ a * m) (h : ∀ x ∈ Γ, x ^ m = 1 → x ∈ N) : oTwoUpper Γ ≤ N := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨hxΓ, hodd⟩ := hx
  apply h x hxΓ
  have hd : orderOf x ∣ 2 ^ a * m := by
    rw [← hΓ, ← Subgroup.orderOf_mk x hxΓ]
    exact orderOf_dvd_natCard _
  have hc : Nat.Coprime (orderOf x) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd)
  exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_left hd)

theorem s7_oTwoUpper_le :
    oTwoUpper s7 ≤ Subgroup.closure {y | ∃ k ∈ s7, ∃ w ∈ S7Cert.N7, y = k * w * k⁻¹} := by
  have hYv := (S7Cert.subB_spec S7Cert.cvB_spec.2.1).1
  have hYex : ∀ c ∈ elemsOf S7Cert.n8G, ∃ u : GL (Fin 8) (ZMod 2),
      (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
    intro c hc
    obtain ⟨w, rfl⟩ := S7Cert.mem_elemsOf hc
    obtain ⟨u, -, hu⟩ := exists_evalW _ (S7Cert.subB_spec S7Cert.cvB_spec.2.1).2.2.2.2
      (S7Cert.unit_of_s7E S7Cert.cvB_spec.2.2.1) w
    exact ⟨u, hu⟩
  refine oTwoUpper_le_of_pow (a := 4) (m := 315) (by rw [S7Cert.card_s7]; norm_num)
    fun x hx hxm => ?_
  have h := conjB_spec q1447Check_parts.2.2.2.2.1 S7Cert.mem_s7_iff
    (S7Cert.subB_spec S7Cert.s7Basic_spec.1).1
    (fun c hc => let ⟨u, _, hu⟩ := S7Cert.exists_mem_s7 hc; ⟨u, hu⟩) hYv hYex hx hxm
  refine Subgroup.closure_mono ?_ h
  rintro y ⟨k, hk, w, hw, rfl⟩
  exact ⟨k, hk, w, (S7Cert.mem_N7_iff w).mpr hw, rfl⟩

theorem g5_oTwoUpper_le :
    oTwoUpper (g5 true true) ≤ Subgroup.closure {y | ∃ k ∈ g5 true true, ∃ z : GL (Fin 8) (ZMod 2),
      colsOf (z : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ G5Cert.zPG ∧ y = k * z * k⁻¹} := by
  have hPv := (S7Cert.subB_spec G5Cert.pB_spec.2.1).1
  have hYv : ∀ c ∈ G5Cert.zPG, Valid8 c := fun c hc => hPv c (G5Cert.zB_spec.1 c hc).1
  have hYex : ∀ c ∈ G5Cert.zPG, ∃ u : GL (Fin 8) (ZMod 2),
      (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
    intro c hc
    obtain ⟨w, hw⟩ := S7Cert.mem_elemsOf (G5Cert.zB_spec.1 c hc).1
    obtain ⟨u, -, hu⟩ := exists_evalW _ (S7Cert.subB_spec G5Cert.pB_spec.2.1).2.2.2.2
      (G5Cert.unit_of_gSE G5Cert.pB_spec.2.2.1) w
    exact ⟨u, hw ▸ hu⟩
  exact oTwoUpper_le_of_pow (a := 4) (m := 45) (by rw [G5Cert.card_gS]; norm_num) fun x hx hxm =>
    conjB_spec q1447Check_parts.2.2.2.2.2.1 G5Cert.mem_gS_iff
      (S7Cert.subB_spec G5Cert.basic_spec.1).1
      (fun c hc => let ⟨u, _, hu⟩ := G5Cert.exists_mem_gS hc; ⟨u, hu⟩) hYv hYex hx hxm

theorem oTwoUpper_le_of_gens {G : Type*} [Group G] {Γ N : Subgroup G} {a b : G}
    (hΓ : Γ = Subgroup.closure {a, b})
    (hnorm : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (ha : a ∈ N) (hb : b * b ∈ N) :
    oTwoUpper Γ ≤ N := by
  have hbΓ : b ∈ Γ := hΓ ▸ Subgroup.subset_closure (by simp)
  have hbi : b⁻¹ ∈ Γ := Γ.inv_mem hbΓ
  have hb2i : b⁻¹ * b⁻¹ ∈ N := by
    have := N.inv_mem hb
    simpa [mul_inv_rev] using this
  have key : ∀ x ∈ Γ, x ∈ N ∨ b⁻¹ * x ∈ N := by
    intro x hx
    rw [hΓ] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact Or.inl ha
      · exact Or.inr (by simp [N.one_mem])
    | one => exact Or.inl N.one_mem
    | mul x y _ _ hx hy =>
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (N.mul_mem hx hy)
      · refine Or.inr ?_
        have := N.mul_mem (hnorm _ hbi _ hx) hy
        simpa [mul_assoc] using this
      · refine Or.inr ?_
        simpa [mul_assoc] using N.mul_mem hx hy
      · refine Or.inl ?_
        have h1 := hnorm _ hbΓ _ hx
        have := N.mul_mem (N.mul_mem h1 hb) hy
        simpa [mul_assoc] using this
    | inv x _ hx =>
      rcases hx with hx | hx
      · exact Or.inl (N.inv_mem hx)
      · refine Or.inr ?_
        have h1 := hnorm _ hbi _ (N.inv_mem hx)
        have := N.mul_mem h1 hb2i
        simpa [mul_assoc] using this
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨hxΓ, hodd⟩ := hx
  have hx2 : x * x ∈ N := by
    rcases key x hxΓ with h | h
    · exact N.mul_mem h h
    · have h1 := hnorm _ hbΓ _ h
      have := N.mul_mem (N.mul_mem h1 hb) h
      simpa [mul_assoc] using this
  obtain ⟨k, hk⟩ := hodd
  have : x = (x * x) ^ (k + 1) := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [this]
  exact N.pow_mem hx2 _

theorem m22_conj_normal :
    ∀ γ ∈ m22, ∀ n ∈ Subgroup.closure {y | ∃ k ∈ m22, ∃ e ∈ M22Cert.E0, y = k * e * k⁻¹},
      γ * n * γ⁻¹ ∈ Subgroup.closure {y | ∃ k ∈ m22, ∃ e ∈ M22Cert.E0, y = k * e * k⁻¹} := by
  intro γ hγ n hn
  induction hn using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, e, he, rfl⟩ := hy
    exact Subgroup.subset_closure ⟨γ * k, m22.mul_mem hγ hk, e, he, by group⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have := Subgroup.mul_mem _ hx hy
    simpa [mul_assoc] using this
  | inv x _ hx =>
    have := Subgroup.inv_mem _ hx
    simpa [mul_assoc] using this

theorem exists_mem_E0 {c : List ℕ} (hc : c ∈ M22Cert.e0E) :
    ∃ u ∈ M22Cert.E0, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = MatNCert.decN 12 c := by
  obtain ⟨w, rfl⟩ := MatNCert.mem_elemsOf hc
  exact MatNCert.exists_evalW _ (MatNCert.subB_spec M22Cert.e0B_spec.1).2.2.2.2
    (M22Cert.unit_of_s0E M22Cert.e0G_mem) w

theorem mem_conj_of_word {w e t : List ℕ} (he : e ∈ M22Cert.e0E)
    (hinv : MatNCert.mulN (MatNCert.evalW 12 M22Cert.gG w)
      (MatNCert.evalW 12 M22Cert.gInv w.reverse) = MatNCert.oneN 12)
    (ht : MatNCert.mulN (MatNCert.mulN (MatNCert.evalW 12 M22Cert.gG w) e)
      (MatNCert.evalW 12 M22Cert.gInv w.reverse) = t)
    {τ : GL (Fin 12) (ZMod 2)} (hτ : (τ : Matrix (Fin 12) (Fin 12) (ZMod 2)) = MatNCert.decN 12 t) :
    τ ∈ Subgroup.closure {y | ∃ k ∈ m22, ∃ e ∈ M22Cert.E0, y = k * e * k⁻¹} := by
  obtain ⟨e', he', he''⟩ := exists_mem_E0 he
  have hlenX := MatNCert.length_evalW (n := 12) M22Cert.gG w
  have hlenXi : (MatNCert.evalW 12 M22Cert.gInv w.reverse).length = 12 := by
    have := congrArg List.length hinv
    rwa [MatNCert.length_mulN, show (MatNCert.oneN 12).length = 12 by rfl] at this
  have hlene : e.length = 12 := ((MatNCert.subB_spec M22Cert.e0B_spec.1).1 e he).1
  have hX : ((M22Cert.tU w : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      MatNCert.decN 12 (MatNCert.evalW 12 M22Cert.gG w) := M22Cert.tU_val w
  have hXi : MatNCert.decN 12 (MatNCert.evalW 12 M22Cert.gInv w.reverse) =
      (((M22Cert.tU w)⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) := by
    have h1 : ((M22Cert.tU w : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
        MatNCert.decN 12 (MatNCert.evalW 12 M22Cert.gInv w.reverse) = 1 := by
      rw [hX, ← MatNCert.decN_mulN hlenX hlenXi, hinv, MatNCert.decN_oneN]
    calc MatNCert.decN 12 (MatNCert.evalW 12 M22Cert.gInv w.reverse)
        = (((M22Cert.tU w)⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
            (((M22Cert.tU w : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
              MatNCert.decN 12 (MatNCert.evalW 12 M22Cert.gInv w.reverse)) := by
          rw [Units.inv_mul_cancel_left]
      _ = _ := by rw [h1, mul_one]
  refine Subgroup.subset_closure ⟨M22Cert.tU w, M22Cert.tU_mem w, e', he', Units.ext ?_⟩
  rw [hτ, ← ht, MatNCert.decN_mulN (by rw [MatNCert.length_mulN, hlene]) hlenXi,
    MatNCert.decN_mulN hlenX hlene, Units.val_mul, Units.val_mul, hX, he'', hXi]

theorem m22_oTwoUpper_le :
    oTwoUpper m22 ≤ Subgroup.closure {y | ∃ k ∈ m22, ∃ e ∈ M22Cert.E0, y = k * e * k⁻¹} := by
  have h := q1447Check_parts.2.2.2.2.2.2
  simp only [m22KB, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
    Std.HashSet.contains_ofList, List.contains_iff_mem] at h
  obtain ⟨⟨hea, hia⟩, hta⟩ := h _ List.mem_cons_self
  obtain ⟨⟨heb, hib⟩, htb⟩ := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine oTwoUpper_le_of_gens (a := m22a) (b := m22b) rfl m22_conj_normal
    (mem_conj_of_word hea hia hta ?_) (mem_conj_of_word heb hib htb ?_)
  · rw [M22Cert.gG_cols]
    exact (MatNCert.decN_colsN _).symm
  · rw [M22Cert.gG_cols]
    show _ = MatNCert.decN 12 (MatNCert.mulN (MatNCert.colsN (m22b : Matrix (Fin 12) (Fin 12)
      (ZMod 2))) (MatNCert.colsN (m22b : Matrix (Fin 12) (Fin 12) (ZMod 2))))
    rw [← MatNCert.colsN_mul, MatNCert.decN_colsN, Units.val_mul]

end CFSG.Quasithin.H13.Q1447Cert
