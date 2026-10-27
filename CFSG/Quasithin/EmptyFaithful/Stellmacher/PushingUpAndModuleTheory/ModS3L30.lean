module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS3Class

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

theorem eq_of_card_le_two {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : Nat.card H ≤ 2) {a b : G} (ha : a ∈ H) (hb : b ∈ H) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    a = b := by
  by_contra hab
  have hsub : ({1, a, b} : Set G) ⊆ (H : Set G) := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact H.one_mem
    · exact ha
    · exact hb
  have h3 : ({1, a, b} : Set G).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨1, a, b, fun h => ha1 h.symm, fun h => hb1 h.symm, hab, rfl⟩
  have h4 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h5 : Nat.card H = (H : Set G).ncard := Nat.card_coe_set_eq (H : Set G)
  omega

theorem act_eq_of_fixed_gens {M : Model 3} {v : M.W} (hd : M.act s3d v = v)
    (ht : M.act s3t v = v) (σ : Perm (Fin 3)) : M.act σ v = v := by
  obtain ⟨i, -, j, -, rfl⟩ := s3_gen σ
  rw [act_mul_apply, act_pow_eq, act_pow_eq, pow_apply_of_fixed ht, pow_apply_of_fixed hd]

theorem exists_fixed_t_mem (M : Model 3) {U : Subgroup M.W} (hU : ∀ x ∈ U, M.act s3t x ∈ U)
    {w : M.W} (hwU : w ∈ U) (hw : w ≠ 1) : ∃ v ∈ U, v ≠ 1 ∧ M.act s3t v = v := by
  by_cases h : M.act s3t w = w
  · exact ⟨w, hwU, hw, h⟩
  · refine ⟨M.act s3t w * w⁻¹, U.mul_mem (hU w hwU) (U.inv_mem hwU),
      fun h1 => h (mul_inv_eq_one.mp h1), ?_⟩
    rw [map_mul, map_inv, s3_act_t_t, inv_eq_of_mul_eq_one_right (M.sq w),
      inv_eq_of_mul_eq_one_right (M.sq (M.act s3t w)), mul_comm]

theorem act_t_mem_fixW_d {M : Model 3} {x : M.W} (hx : x ∈ fixW M (Subgroup.zpowers s3d)) :
    M.act s3t x ∈ fixW M (Subgroup.zpowers s3d) := by
  have hxd : M.act s3d x = x := (mem_fixW_zpowers M).mp hx
  rw [mem_fixW_zpowers, s3_act_d_t, hxd, hxd]

theorem act_d_d_eq {M : Model 3} (hC : ∀ w : M.W, M.act s3d w = w → w = 1) (w : M.W) :
    M.act s3d (M.act s3d w) = w * M.act s3d w := by
  have hx : M.act s3d (w * M.act s3d w * M.act s3d (M.act s3d w)) =
      w * M.act s3d w * M.act s3d (M.act s3d w) := by
    rw [map_mul, map_mul, s3_act_d_three, mul_comm (M.act s3d w * M.act s3d (M.act s3d w)) w,
      mul_assoc]
  have h2 := eq_inv_of_mul_eq_one_right (hC _ hx)
  rw [h2]
  exact inv_eq_of_mul_eq_one_right (M.sq _)

theorem s3_card_eq_sq (M : Model 3) (hY : fixW M ⊤ = ⊥) :
    (∀ w : M.W, M.act s3d w = w → w = 1) ∧
      Nat.card M.W = Nat.card (fixW M S3Syl) ^ 2 := by
  have hC : ∀ w : M.W, M.act s3d w = w → w = 1 := by
    intro c hcd
    by_contra hc1
    have hmem : c ∈ fixW M (Subgroup.zpowers s3d) := (mem_fixW_zpowers M).mpr hcd
    obtain ⟨v, hvC, hv1, hvt⟩ := exists_fixed_t_mem M (U := fixW M (Subgroup.zpowers s3d))
      (fun x hx => act_t_mem_fixW_d hx) hmem hc1
    have hvd : M.act s3d v = v := (mem_fixW_zpowers M).mp hvC
    have hv : v ∈ fixW M ⊤ := fun b _ => act_eq_of_fixed_gens hvd hvt b
    rw [hY, Subgroup.mem_bot] at hv
    exact hv1 hv
  refine ⟨hC, ?_⟩
  have hrel := act_d_d_eq hC
  have hFR : fixW M S3Syl = commW M S3Syl ⊤ := by
    apply le_antisymm
    · intro c hc
      rw [S3Syl_eq, commW_top_zpowers_eq_range]
      refine ⟨M.act s3d c, ?_⟩
      have hct : M.act s3t c = c := (mem_fixW_zpowers M).mp (by rwa [S3Syl_eq] at hc)
      show M.act s3t (M.act s3d c) * (M.act s3d c)⁻¹ = c
      rw [s3_act_t_d, hct, hrel, inv_eq_of_mul_eq_one_right (M.sq (M.act s3d c)), mul_assoc,
        M.sq, mul_one]
    · rw [S3Syl_eq]
      exact commW_le_fixW_of_sq M s3t_mul_self
  have h1 := Subgroup.card_mul_index (fixW M S3Syl)
  have h2 := bf1 M s3t
  rw [← S3Syl_eq, ← hFR] at h2
  rw [← h1, h2, sq]

@[expose] def Model.isoRestrictOfEqTop {n : ℕ} (M : Model n) (U : Subgroup M.W)
    (hU : IsInvSub M ⊤ U) (h : U = ⊤) : M.Iso (M.restrict U hU) where
  toMulEquiv :=
    { toFun := fun x => ⟨x, by rw [h]; trivial⟩
      invFun := fun x => x.1
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  map_act _ _ := rfl

theorem s3_lemma30 (M : Model 3) (hA : fixW M (alternatingGroup (Fin 3)) ≠ ⊤)
    (hidx : (fixW M S3Syl).index ≤ 2) :
    ∃ hU : IsInvSub M ⊤ (commW M (alternatingGroup (Fin 3)) ⊤),
      IsCompl (commW M (alternatingGroup (Fin 3)) ⊤) (fixW M (alternatingGroup (Fin 3))) ∧
      Nonempty ((M.restrict (commW M (alternatingGroup (Fin 3)) ⊤) hU).Iso nat3) ∧
      fixW M (alternatingGroup (Fin 3)) = fixW M ⊤ := by
  rw [alternatingGroup_three] at hA ⊢
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : Odd (orderOf s3d) := by
    rw [orderOf_eq_prime s3d_pow_three s3d_ne_one]
    decide
  have hcompl := bf3_isCompl M hord
  set C := fixW M (Subgroup.zpowers s3d) with hCdef
  set R := commW M (Subgroup.zpowers s3d) ⊤ with hRdef
  have hCR : ∀ x ∈ C, x ∈ R → x = 1 := fun x hxC hxR =>
    Subgroup.disjoint_def.mp hcompl.disjoint hxC hxR
  have hRrange : R = (delHom (M.act s3d)).range := commW_top_zpowers_eq_range M s3d
  have hmemR : ∀ w : M.W, M.act s3d w * w⁻¹ ∈ R := fun w =>
    Subgroup.subset_closure ⟨s3d, Subgroup.mem_zpowers s3d, w, Subgroup.mem_top w, rfl⟩
  have hRd : ∀ x ∈ R, M.act s3d x ∈ R := by
    have := isInvSub_commW M (B := Subgroup.zpowers s3d) (U := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
    exact fun x hx => this s3d (Subgroup.mem_zpowers s3d) x hx
  have hRt : ∀ x ∈ R, M.act s3t x ∈ R := by
    intro x hx
    rw [hRrange] at hx
    obtain ⟨w, rfl⟩ := hx
    have h1 : M.act s3t (delHom (M.act s3d) w) =
        (M.act s3d (M.act s3d (M.act s3t w)) * (M.act s3d (M.act s3t w))⁻¹) *
        (M.act s3d (M.act s3t w) * (M.act s3t w)⁻¹) := by
      show M.act s3t (M.act s3d w * w⁻¹) = _
      rw [map_mul, map_inv, s3_act_t_d]
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [h1]
    exact R.mul_mem (hmemR _) (hmemR _)
  have hRinv : IsInvSub M ⊤ R := isInvSub_top_of_gens hRd hRt
  obtain ⟨w₀, hw₀⟩ : ∃ w : M.W, M.act s3d w ≠ w := by
    by_contra hcon
    push Not at hcon
    apply hA
    rw [eq_top_iff]
    intro x _
    exact (mem_fixW_zpowers M).mpr (hcon x)
  obtain ⟨r₀, hr₀, hr₀1⟩ : ∃ r ∈ R, r ≠ 1 :=
    ⟨M.act s3d w₀ * w₀⁻¹, hmemR w₀, fun h => hw₀ (mul_inv_eq_one.mp h)⟩
  have hnorm : ∀ r ∈ R, M.act s3d (M.act s3d r) = r * M.act s3d r := by
    intro r hr
    have hx : M.act s3d (r * M.act s3d r * M.act s3d (M.act s3d r)) =
        r * M.act s3d r * M.act s3d (M.act s3d r) := by
      rw [map_mul, map_mul, s3_act_d_three, mul_comm (M.act s3d r * M.act s3d (M.act s3d r)) r,
        mul_assoc]
    have hxR : r * M.act s3d r * M.act s3d (M.act s3d r) ∈ R :=
      R.mul_mem (R.mul_mem hr (hRd r hr)) (hRd _ (hRd r hr))
    have h1 := hCR _ ((mem_fixW_zpowers M).mpr hx) hxR
    have h2 := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_right (M.sq _)
  have hdR : ∀ r ∈ R, M.act s3d r = r → r = 1 := fun r hr h =>
    hCR r ((mem_fixW_zpowers M).mpr h) hr
  have hD2 : ∃ r ∈ R, M.act s3t r ≠ r := by
    by_contra hno
    push Not at hno
    apply hr₀1
    have e1 : M.act s3t (M.act s3d r₀) = M.act s3d r₀ := hno _ (hRd _ hr₀)
    rw [s3_act_t_d, hno _ hr₀] at e1
    exact hdR r₀ hr₀ ((M.act s3d).injective e1)
  have hHcard : Nat.card (commW M (Subgroup.zpowers s3t) ⊤) ≤ 2 := by
    rw [← bf1 M s3t]
    exact hidx
  have hmemH : ∀ w : M.W, M.act s3t w * w⁻¹ ∈ commW M (Subgroup.zpowers s3t) ⊤ := fun w =>
    Subgroup.subset_closure ⟨s3t, Subgroup.mem_zpowers s3t, w, Subgroup.mem_top w, rfl⟩
  have hD1 : ∀ c ∈ C, M.act s3t c = c := by
    intro c hc
    by_contra hne
    obtain ⟨r, hrR, hrt⟩ := hD2
    have ha : M.act s3t c * c⁻¹ ∈ C := C.mul_mem (act_t_mem_fixW_d hc) (C.inv_mem hc)
    have hb : M.act s3t r * r⁻¹ ∈ R := R.mul_mem (hRt r hrR) (R.inv_mem hrR)
    have hab := eq_of_card_le_two hHcard (hmemH c) (hmemH r) (fun h => hne (mul_inv_eq_one.mp h))
      (fun h => hrt (mul_inv_eq_one.mp h))
    rw [hab] at ha
    exact hrt (mul_inv_eq_one.mp (hCR _ ha hb))
  obtain ⟨r₁, hr₁, hr₁t⟩ := hD2
  obtain ⟨u, hu, hu1, hut, hH2⟩ : ∃ u ∈ R, u ≠ 1 ∧ M.act s3t u = u ∧
      ∀ w : M.W, M.act s3t w * w⁻¹ = 1 ∨ M.act s3t w * w⁻¹ = u := by
    refine ⟨M.act s3t r₁ * r₁⁻¹, R.mul_mem (hRt r₁ hr₁) (R.inv_mem hr₁),
      fun h => hr₁t (mul_inv_eq_one.mp h), ?_, ?_⟩
    · rw [map_mul, map_inv, s3_act_t_t, inv_eq_of_mul_eq_one_right (M.sq r₁),
        inv_eq_of_mul_eq_one_right (M.sq (M.act s3t r₁)), mul_comm]
    · intro w
      by_cases h : M.act s3t w * w⁻¹ = 1
      · exact Or.inl h
      · exact Or.inr (eq_of_card_le_two hHcard (hmemH w) (hmemH r₁) h
          (fun h' => hr₁t (mul_inv_eq_one.mp h')))
  have hspan : ∀ v ∈ R, v = 1 ∨ v = u ∨ v = M.act s3d u ∨ v = u * M.act s3d u := by
    intro v hv
    obtain ⟨z, hzdef⟩ : ∃ z, z = M.act s3t v * v⁻¹ := ⟨_, rfl⟩
    have hτv : M.act s3t v = z * v := by rw [hzdef, inv_mul_cancel_right]
    obtain ⟨y, hydef⟩ : ∃ y, y = M.act s3t (M.act s3d v) * (M.act s3d v)⁻¹ := ⟨_, rfl⟩
    have hy : y = M.act s3d (M.act s3d z) * v := by
      rw [hydef, s3_act_t_d, hτv, inv_eq_of_mul_eq_one_right (M.sq (M.act s3d v)), map_mul,
        map_mul, hnorm v hv, mul_assoc, mul_assoc, M.sq, mul_one]
    have hvy : v = M.act s3d (M.act s3d z) * y := by
      rw [hy, ← mul_assoc, M.sq, one_mul]
    have hz : z = 1 ∨ z = u := by rw [hzdef]; exact hH2 v
    have hy' : y = 1 ∨ y = u := by rw [hydef]; exact hH2 (M.act s3d v)
    rcases hz with hz | hz <;> rcases hy' with hy' | hy' <;> rw [hz, hy'] at hvy
    · left
      simpa using hvy
    · right; left
      simpa using hvy
    · right; right; right
      rw [hnorm u hu, mul_one] at hvy
      exact hvy
    · right; right; left
      rw [hnorm u hu, mul_comm u (M.act s3d u), mul_assoc, M.sq, mul_one] at hvy
      exact hvy
  have hframe : S3Frame (M.restrict R hRinv) ⟨u, hu⟩ :=
    { fix_t := Subtype.ext hut
      ne_one := fun h => hu1 (congrArg Subtype.val h)
      d_ne := fun h => hu1 (hdR u hu (congrArg Subtype.val h))
      rel := Subtype.ext (hnorm u hu)
      span := fun v' => by
        obtain ⟨v, hvR⟩ := v'
        rcases hspan v hvR with h | h | h | h
        · left; exact Subtype.ext h
        · right; left; exact Subtype.ext h
        · right; right; left; exact Subtype.ext h
        · right; right; right; exact Subtype.ext h }
  obtain ⟨u₂, hu₂⟩ := exists_frame_nat3
  obtain ⟨e, -⟩ := hframe.exists_iso hu₂
  refine ⟨hRinv, hcompl.symm, ⟨e⟩, ?_⟩
  apply le_antisymm
  · intro c hc b _
    exact act_eq_of_fixed_gens ((mem_fixW_zpowers M).mp hc) (hD1 c hc) b
  · intro c hc
    exact (mem_fixW_zpowers M).mpr (hc s3d (Subgroup.mem_top _))

theorem s3_lemma30_natural (M : Model 3) (hA : fixW M (alternatingGroup (Fin 3)) ≠ ⊤)
    (hidx : (fixW M S3Syl).index ≤ 2) (hY : fixW M ⊤ = ⊥) : Nonempty (M.Iso nat3) := by
  obtain ⟨hU, hcompl, ⟨e⟩, hfix⟩ := s3_lemma30 M hA hidx
  have hC : fixW M (alternatingGroup (Fin 3)) = ⊥ := by rw [hfix, hY]
  have hR : commW M (alternatingGroup (Fin 3)) ⊤ = ⊤ := by
    rw [hC] at hcompl
    have := hcompl.codisjoint
    rwa [codisjoint_iff, sup_bot_eq] at this
  exact ⟨(Model.isoRestrictOfEqTop M _ hU hR).trans e⟩

end CFSG.Quasithin.F53Mod
