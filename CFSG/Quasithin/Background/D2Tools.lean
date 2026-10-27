module

public import CFSG.Quasithin.Background.D2Dihedral

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem commSub_invariant {E X : Subgroup (MulAut V)} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hX : X ≤ E) {W : Subgroup V} (hW : ∀ h ∈ E, ∀ w ∈ W, h w ∈ W) :
    ∀ h ∈ E, ∀ c ∈ commSub W X, h c ∈ commSub W X := by
  intro h hh c hc
  refine Subgroup.closure_induction (p := fun c _ => h c ∈ commSub W X) ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨x, hx, w, hw, rfl⟩
    have hxh : h * x = x * h := hE h hh x (hX hx)
    have : h (x w * w⁻¹) = x (h w) * (h w)⁻¹ := by
      rw [map_mul, map_inv]
      have : h (x w) = x (h w) := by
        calc h (x w) = (h * x) w := rfl
          _ = (x * h) w := by rw [hxh]
          _ = x (h w) := rfl
      rw [this]
    rw [this]
    exact Subgroup.subset_closure ⟨x, hx, h w, hW h hh w hw, rfl⟩
  · rw [map_one]; exact Subgroup.one_mem _
  · intro a b _ _ ha hb
    rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [map_inv]; exact Subgroup.inv_mem _ ha

omit [Finite V] in
theorem commSub_sup_left (A B : Subgroup V) (X : Subgroup (MulAut V)) :
    commSub (A ⊔ B) X = commSub A X ⊔ commSub B X := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    have : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
      rw [map_mul, mul_inv]
      exact mul_mul_mul_comm _ _ _ _
    rw [this]
    exact Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨x, hx, a, ha, rfl⟩)
      (Subgroup.subset_closure ⟨x, hx, b, hb, rfl⟩)
  · exact sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl)

omit [Finite V] in
theorem commSub_bot_left (X : Subgroup (MulAut V)) : commSub (⊥ : Subgroup V) X = ⊥ := by
  rw [commSub_eq_bot_iff]
  exact bot_le

theorem commSub_commSub_self (hV : ∀ v : V, v ^ 2 = 1) {u : MulAut V} (hu : u ^ 2 = 1)
    {W : Subgroup V} (hW : ∀ x ∈ Subgroup.zpowers u, ∀ w ∈ W, x w ∈ W) :
    commSub (commSub W (Subgroup.zpowers u)) (Subgroup.zpowers u) = ⊥ := by
  rw [commSub_eq_bot_iff]
  exact (commSub_zpowers_le_inf_fixV hV hu hW).trans inf_le_right

omit [Finite V] in
theorem commHom_comm {u v : MulAut V} (huv : u * v = v * u) (w : V) :
    commHom u (commHom v w) = commHom v (commHom u w) := by
  simp only [commHom_apply, map_mul, map_inv, mul_inv, inv_inv]
  have : u (v w) = v (u w) := by
    calc u (v w) = (u * v) w := rfl
      _ = (v * u) w := by rw [huv]
      _ = v (u w) := rfl
  rw [this]
  ac_rfl

theorem commSub_comm {E : Subgroup (MulAut V)} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {u v : MulAut V}
    (hu : u ∈ E) (hv : v ∈ E) {W : Subgroup V} (hW : ∀ h ∈ E, ∀ w ∈ W, h w ∈ W) :
    commSub (commSub W (Subgroup.zpowers v)) (Subgroup.zpowers u) =
      commSub (commSub W (Subgroup.zpowers u)) (Subgroup.zpowers v) := by
  have huv : u * v = v * u := hE u hu v hv
  have hzu : Subgroup.zpowers u ≤ E := Subgroup.zpowers_le.mpr hu
  have hzv : Subgroup.zpowers v ≤ E := Subgroup.zpowers_le.mpr hv
  have hWu : ∀ x ∈ Subgroup.zpowers u, ∀ w ∈ W, x w ∈ W := fun x hx w hw => hW x (hzu hx) w hw
  have hWv : ∀ x ∈ Subgroup.zpowers v, ∀ w ∈ W, x w ∈ W := fun x hx w hw => hW x (hzv hx) w hw
  have hCv := commSub_invariant hE hzv hW
  have hCu := commSub_invariant hE hzu hW
  rw [commSub_zpowers_eq_map (fun x hx w hw => hCv x (hzu hx) w hw), commSub_zpowers_eq_map hWv,
    commSub_zpowers_eq_map (fun x hx w hw => hCu x (hzv hx) w hw), commSub_zpowers_eq_map hWu,
    Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext w
  exact commHom_comm huv w

theorem exists_card_four {E : Subgroup (MulAut V)} (hE : IsElemAbelian2 E) (hcard : Nat.card E = 4) :
    ∃ u v : MulAut V, u ∈ E ∧ v ∈ E ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧
      ∀ g ∈ E, g = 1 ∨ g = u ∨ g = v ∨ g = u * v := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hcard' : Fintype.card E = 4 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  obtain ⟨u, hu⟩ : ∃ u : E, u ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card E = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
    omega
  obtain ⟨v, hv1, hv2⟩ : ∃ v : E, v ≠ 1 ∧ v ≠ u := by
    by_contra h
    push Not at h
    have hle : Fintype.card E ≤ 2 := by
      rw [← Finset.card_univ]
      refine (Finset.card_le_card (s := Finset.univ) (t := {1, u}) ?_).trans Finset.card_le_two
      intro x _
      by_cases hx : x = 1
      · simp [hx]
      · simp [h x hx]
    omega
  have hw : u * v ≠ 1 := by
    intro h
    have h2 : u = v⁻¹ := mul_eq_one_iff_eq_inv.mp h
    have h3 : (v : MulAut V) ^ 2 = 1 := hE.2 v v.2
    have h4 : (v : MulAut V)⁻¹ = v := by rw [inv_eq_iff_mul_eq_one, ← pow_two, h3]
    exact hv2 (Subtype.ext ((congrArg Subtype.val h2).trans h4).symm)
  have h1u : (1 : E) ≠ u := hu.symm
  have h1v : (1 : E) ≠ v := hv1.symm
  have h1w : (1 : E) ≠ u * v := hw.symm
  have huv : u ≠ v := fun h => hv2 h.symm
  have huw : u ≠ u * v := fun h => hv1 (mul_eq_left.mp h.symm)
  have hvw : v ≠ u * v := fun h => hu (mul_eq_right.mp h.symm)
  have hcardS : ({1, u, v, u * v} : Finset E).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h1u, h1v, h1w]),
      Finset.card_insert_of_notMem (by simp [huv, huw]),
      Finset.card_insert_of_notMem (by simp [hvw]), Finset.card_singleton]
  have hS : ({1, u, v, u * v} : Finset E) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcardS, hcard'])
  refine ⟨u, v, u.2, v.2, fun h => hu (Subtype.ext h), fun h => hv1 (Subtype.ext h),
    fun h => huv (Subtype.ext h), fun g hg => ?_⟩
  have hmem : (⟨g, hg⟩ : E) ∈ ({1, u, v, u * v} : Finset E) := by
    rw [hS]; exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

omit [Finite V] in
theorem commSub_card_four {E : Subgroup (MulAut V)} {u v : MulAut V} (hu : u ∈ E) (hv : v ∈ E)
    (hEall : ∀ g ∈ E, g = 1 ∨ g = u ∨ g = v ∨ g = u * v) {W : Subgroup V}
    (hW : ∀ h ∈ E, ∀ w ∈ W, h w ∈ W) :
    commSub W E = commSub W (Subgroup.zpowers u) ⊔ commSub W (Subgroup.zpowers v) := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨g, hg, w, hw, rfl⟩
    rcases hEall g hg with rfl | rfl | rfl | rfl
    · simp
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, Subgroup.mem_zpowers _, w, hw, rfl⟩)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, Subgroup.mem_zpowers _, w, hw, rfl⟩)
    · have : (u * v) w * w⁻¹ = (u (v w) * (v w)⁻¹) * (v w * w⁻¹) := by
        simp only [MulAut.mul_apply]
        group
      rw [this]
      exact Subgroup.mul_mem_sup
        (Subgroup.subset_closure ⟨u, Subgroup.mem_zpowers _, v w, hW v hv w hw, rfl⟩)
        (Subgroup.subset_closure ⟨v, Subgroup.mem_zpowers _, w, hw, rfl⟩)
  · exact sup_le (commSub_mono le_rfl (Subgroup.zpowers_le.mpr hu))
      (commSub_mono le_rfl (Subgroup.zpowers_le.mpr hv))

theorem commSeries_three_eq_bot_of_card_four (hV : ∀ v : V, v ^ 2 = 1) {E : Subgroup (MulAut V)}
    (hE : IsElemAbelian2 E) (hcard : Nat.card E = 4) : commSeries E 3 = ⊥ := by
  obtain ⟨u, v, hu, hv, hu1, hv1, huv, hall⟩ := exists_card_four hE hcard
  have hu2 : u ^ 2 = 1 := hE.2 u hu
  have hv2 : v ^ 2 = 1 := hE.2 v hv
  have hzu : Subgroup.zpowers u ≤ E := Subgroup.zpowers_le.mpr hu
  have hzv : Subgroup.zpowers v ≤ E := Subgroup.zpowers_le.mpr hv
  have hEinv : ∀ W : Subgroup V, (∀ h ∈ E, ∀ w ∈ W, h w ∈ W) → ∀ g ∈ E,
      ∀ h ∈ E, ∀ c ∈ commSub W (Subgroup.zpowers g), h c ∈ commSub W (Subgroup.zpowers g) :=
    fun W hW g hg => commSub_invariant hE.1 (Subgroup.zpowers_le.mpr hg) hW
  have htop : ∀ h ∈ E, ∀ w ∈ (⊤ : Subgroup V), h w ∈ (⊤ : Subgroup V) := fun _ _ _ _ =>
    Subgroup.mem_top _
  set A := commSub ⊤ (Subgroup.zpowers u) with hA
  set B := commSub ⊤ (Subgroup.zpowers v) with hB
  have hAinv : ∀ h ∈ E, ∀ w ∈ A, h w ∈ A := hEinv ⊤ htop u hu
  have hBinv : ∀ h ∈ E, ∀ w ∈ B, h w ∈ B := hEinv ⊤ htop v hv
  have hAu : ∀ x ∈ Subgroup.zpowers u, ∀ w ∈ A, x w ∈ A := fun x hx w hw => hAinv x (hzu hx) w hw
  have hAv : ∀ x ∈ Subgroup.zpowers v, ∀ w ∈ A, x w ∈ A := fun x hx w hw => hAinv x (hzv hx) w hw
  have hBu : ∀ x ∈ Subgroup.zpowers u, ∀ w ∈ B, x w ∈ B := fun x hx w hw => hBinv x (hzu hx) w hw
  have hBv : ∀ x ∈ Subgroup.zpowers v, ∀ w ∈ B, x w ∈ B := fun x hx w hw => hBinv x (hzv hx) w hw
  have hAuu : commSub A (Subgroup.zpowers u) = ⊥ :=
    commSub_commSub_self hV hu2 (W := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
  have hBvv : commSub B (Subgroup.zpowers v) = ⊥ :=
    commSub_commSub_self hV hv2 (W := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
  have hL1 : commSeries E 1 = A ⊔ B := by
    rw [commSeries_one, commV_eq_commSub, commSub_card_four hu hv hall htop]
  set C := commSub A (Subgroup.zpowers v) with hC
  set C' := commSub B (Subgroup.zpowers u) with hC'
  have hCinv : ∀ h ∈ E, ∀ w ∈ C, h w ∈ C := hEinv A hAinv v hv
  have hC'inv : ∀ h ∈ E, ∀ w ∈ C', h w ∈ C' := hEinv B hBinv u hu
  have hL2 : commSeries E 2 = C ⊔ C' := by
    have h2 : commSeries E 2 = commSub (commSeries E 1) E := rfl
    rw [h2, hL1, commSub_sup_left, commSub_card_four hu hv hall hAinv,
      commSub_card_four hu hv hall hBinv, hAuu, hBvv]
    simp only [bot_sup_eq, sup_bot_eq]
    rfl
  have hCC' : C' = C := by
    simp only [hC, hC', hA, hB]
    exact commSub_comm hE.1 hu hv htop
  have hL3 : commSeries E 3 = commSub (C ⊔ C') E := by
    have h3 : commSeries E 3 = commSub (commSeries E 2) E := rfl
    rw [h3, hL2]
  rw [hL3, hCC', sup_idem, commSub_card_four hu hv hall hCinv]
  have hCu : commSub C (Subgroup.zpowers u) = ⊥ := by
    have : commSub C (Subgroup.zpowers u) = commSub (commSub A (Subgroup.zpowers u)) (Subgroup.zpowers v) := by
      simp only [hC]
      exact commSub_comm hE.1 hu hv hAinv
    rw [this, hAuu, commSub_bot_left]
  have hCv : commSub C (Subgroup.zpowers v) = ⊥ :=
    commSub_commSub_self hV hv2 (fun x hx w hw => hAv x hx w hw)
  rw [hCu, hCv]
  simp

theorem rk_eq_add_of_isDirectSum {W U₁ U₂ : Subgroup V} (hd : IsDirectSum W U₁ U₂) :
    rk W = rk U₁ + rk U₂ := by
  have := rk_sup_add_rk_inf U₁ U₂
  rw [hd.1, hd.2, rk_bot] at this
  omega

omit [Finite V] in
theorem commSub_isDirectSum {g : MulAut V} {W U₁ U₂ : Subgroup V} (hd : IsDirectSum W U₁ U₂)
    (h₁ : ∀ x ∈ Subgroup.zpowers g, ∀ u ∈ U₁, x u ∈ U₁)
    (h₂ : ∀ x ∈ Subgroup.zpowers g, ∀ u ∈ U₂, x u ∈ U₂) :
    IsDirectSum (commSub W (Subgroup.zpowers g)) (commSub U₁ (Subgroup.zpowers g))
      (commSub U₂ (Subgroup.zpowers g)) := by
  refine ⟨?_, ?_⟩
  · rw [← hd.1, commSub_sup_left]
  · refine le_bot_iff.mp ?_
    calc commSub U₁ (Subgroup.zpowers g) ⊓ commSub U₂ (Subgroup.zpowers g) ≤ U₁ ⊓ U₂ :=
          inf_le_inf (commSub_le_of_invariant h₁) (commSub_le_of_invariant h₂)
      _ = ⊥ := hd.2

theorem rk_commSub_isDirectSum {g : MulAut V} {W U₁ U₂ : Subgroup V} (hd : IsDirectSum W U₁ U₂)
    (h₁ : ∀ x ∈ Subgroup.zpowers g, ∀ u ∈ U₁, x u ∈ U₁)
    (h₂ : ∀ x ∈ Subgroup.zpowers g, ∀ u ∈ U₂, x u ∈ U₂) :
    rk (commSub W (Subgroup.zpowers g)) =
      rk (commSub U₁ (Subgroup.zpowers g)) + rk (commSub U₂ (Subgroup.zpowers g)) :=
  rk_eq_add_of_isDirectSum (commSub_isDirectSum hd h₁ h₂)

theorem rk_fixV_pos_of_isPGroup_two (hV : ∀ v : V, v ^ 2 = 1) {E : Subgroup (MulAut V)}
    (hE : IsPGroup 2 E) (hrk : 0 < rk V) : 0 < rk (fixV E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := card_modEq_card_fixV hE
  rw [card_eq_two_pow_rk hV, card_eq_two_pow hV] at hmod
  by_contra h0
  have h0' : rk (fixV E) = 0 := by omega
  rw [h0'] at hmod
  have h1 : 2 ^ rk V ≡ 1 [MOD 2] := by simpa using hmod
  have h2 : 2 ∣ 2 ^ rk V := dvd_pow_self 2 (by omega)
  have h3 : (2 ^ rk V) % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
  have h4 : (2 ^ rk V) % 2 = 1 % 2 := h1
  omega

theorem three_group_card_dvd_nine (hV : ∀ v : V, v ^ 2 = 1) (hrk : rk V = 4)
    {P : Subgroup (MulAut V)} (hP : IsPGroup 3 P) : Nat.card P ∣ 9 := by
  have hdvd : Nat.card P ∣ Nat.card (MulAut V) := Subgroup.card_subgroup_dvd_card P
  rw [card_mulAut_eq hV, hrk] at hdvd
  have hprod : (∏ i : Fin 4, (2 ^ 4 - 2 ^ (i : ℕ))) = 20160 := by decide
  rw [hprod] at hdvd
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  rw [ha] at hdvd ⊢
  have ha2 : a ≤ 2 := by
    by_contra h
    have h3 : 3 ^ 3 ∣ 3 ^ a := pow_dvd_pow 3 (by omega)
    have := h3.trans hdvd
    omega
  exact (pow_dvd_pow 3 ha2)

theorem three_group_card_dvd_81 (hV : ∀ v : V, v ^ 2 = 1) (hrk : rk V = 6)
    {P : Subgroup (MulAut V)} (hP : IsPGroup 3 P) : Nat.card P ∣ 81 := by
  have hdvd : Nat.card P ∣ Nat.card (MulAut V) := Subgroup.card_subgroup_dvd_card P
  rw [card_mulAut_eq hV, hrk] at hdvd
  have hprod : (∏ i : Fin 6, (2 ^ 6 - 2 ^ (i : ℕ))) = 20158709760 := by decide
  rw [hprod] at hdvd
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  rw [ha] at hdvd ⊢
  have ha2 : a ≤ 4 := by
    by_contra h
    have h3 : 3 ^ 5 ∣ 3 ^ a := pow_dvd_pow 3 (by omega)
    have := h3.trans hdvd
    omega
  exact (pow_dvd_pow 3 ha2)

omit [Finite V] in
theorem card_mulAut_of_rk_two [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hrk : rk V = 2) :
    Nat.card (MulAut V) = 6 := by
  rw [card_mulAut_eq hV, hrk]
  decide

theorem klein_table {G : Type*} [Group G] {t w : G} (htt : t * t = 1) (hww : w * w = 1)
    (hwt : w * t = t * w) :
    t * (t * w) = w ∧ w * (t * w) = t ∧ t * w * t = w ∧ t * w * w = t ∧ t * w * (t * w) = 1 := by
  have h1 : t * (t * w) = w := by rw [← mul_assoc, htt, one_mul]
  have h2 : w * (t * w) = t := by rw [← mul_assoc, hwt, mul_assoc, hww, mul_one]
  have h3 : t * w * t = w := by rw [mul_assoc, hwt, ← mul_assoc, htt, one_mul]
  have h4 : t * w * w = t := by rw [mul_assoc, hww, mul_one]
  have h5 : t * w * (t * w) = 1 := by rw [← mul_assoc, h3, hww]
  exact ⟨h1, h2, h3, h4, h5⟩

@[expose] def klein {G : Type*} [Group G] (t w : G) (htt : t * t = 1) (hww : w * w = 1)
    (hwt : w * t = t * w) : Subgroup G where
  carrier := {x | x = 1 ∨ x = t ∨ x = w ∨ x = t * w}
  one_mem' := Or.inl rfl
  mul_mem' := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := klein_table htt hww hwt
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp [htt, hww, hwt, h1, h2, h3, h4, h5]
  inv_mem' := by
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    rintro a (rfl | rfl | rfl | rfl)
    · simp
    · simp [hti]
    · simp [hwi]
    · simp [mul_inv_rev, hti, hwi, hwt]

theorem mem_klein {G : Type*} [Group G] {t w : G} {htt : t * t = 1} {hww : w * w = 1}
    {hwt : w * t = t * w} {x : G} :
    x ∈ klein t w htt hww hwt ↔ x = 1 ∨ x = t ∨ x = w ∨ x = t * w := Iff.rfl

theorem card_klein {G : Type*} [Group G] {t w : G} (htt : t * t = 1) (hww : w * w = 1)
    (hwt : w * t = t * w) (ht1 : t ≠ 1) (hw1 : w ≠ 1) (htw : t ≠ w) :
    Nat.card (klein t w htt hww hwt) = 4 := by
  have h1t : (1 : G) ≠ t := ht1.symm
  have h1w : (1 : G) ≠ w := hw1.symm
  have h1tw : (1 : G) ≠ t * w := fun h => htw (mul_eq_one_iff_eq_inv.mp h.symm |>.trans
    (inv_eq_of_mul_eq_one_right hww))
  have htt' : t ≠ t * w := fun h => hw1 (mul_eq_left.mp h.symm)
  have hwt' : w ≠ t * w := fun h => ht1 (mul_eq_right.mp h.symm)
  have hset : ((klein t w htt hww hwt : Subgroup G) : Set G) = {1, t, w, t * w} := by
    ext x
    simp [mem_klein]
  have hcongr : Nat.card ↥(klein t w htt hww hwt) =
      Nat.card ↥((klein t w htt hww hwt : Subgroup G) : Set G) := rfl
  rw [hcongr, hset, Nat.card_coe_set_eq,
    Set.ncard_insert_of_notMem (by simp [h1t, h1w, h1tw]),
    Set.ncard_insert_of_notMem (by simp [htw, htt']), Set.ncard_pair hwt']

omit [Finite V] in
theorem klein_isElemAbelian2 {t w : MulAut V} (htt : t * t = 1) (hww : w * w = 1)
    (hwt : w * t = t * w) : IsElemAbelian2 (klein t w htt hww hwt) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := klein_table htt hww hwt
  refine ⟨?_, ?_⟩
  · rintro a (rfl | rfl | rfl | rfl) b (rfl | rfl | rfl | rfl) <;>
      simp [htt, hww, hwt, h1, h2, h3, h4, h5]
  · rintro a (rfl | rfl | rfl | rfl) <;> simp [pow_two, htt, hww, h5]

theorem exists_card_four_of_even {t t' : MulAut V} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (ht'1 : t' ≠ 1) (ht'2 : t' ^ 2 = 1) (hne : t ≠ t') (heven : Even (orderOf (t * t'))) :
    ∃ E : Subgroup (MulAut V), E ≤ Subgroup.closure {t, t'} ∧ IsElemAbelian2 E ∧
      Nat.card E = 4 ∧ t ∈ E := by
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have ht'' : t' * t' = 1 := by rw [← pow_two]; exact ht'2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have ht'i : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht''
  set u := t * t' with hu
  have hu1 : u ≠ 1 := by
    intro h
    apply hne
    have : t = t'⁻¹ := mul_eq_one_iff_eq_inv.mp h
    rw [this, ht'i]
  obtain ⟨k, hk⟩ := heven
  have hk0 : 0 < k := by
    have := orderOf_pos u
    omega
  set w := u ^ k with hw
  have hww : w * w = 1 := by
    rw [hw, ← pow_add, ← two_mul]
    have : 2 * k = orderOf u := by omega
    rw [this]; exact pow_orderOf_eq_one u
  have hw1 : w ≠ 1 := by
    intro h
    have h2 : orderOf u ∣ k := orderOf_dvd_of_pow_eq_one h
    have := Nat.le_of_dvd hk0 h2
    omega
  have htut : t * u * t⁻¹ = u⁻¹ := by
    rw [hu, hti]
    calc t * (t * t') * t = (t * t) * t' * t := by group
      _ = t' * t := by rw [htt, one_mul]
      _ = (t * t')⁻¹ := by rw [mul_inv_rev, hti, ht'i]
  have hwt : w * t = t * w := by
    have h1 : t * w * t⁻¹ = w⁻¹ := by
      rw [hw, ← conj_pow, htut, inv_pow]
    have h2 : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    rw [h2] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have htw : t ≠ w := by
    intro h
    have hc : t * u = u * t := by
      rw [h, hw]; exact (Commute.pow_left (Commute.refl u) k).eq
    have h3 : u * u = 1 := by
      have e1 : t * u * t⁻¹ = u := by rw [hc]; group
      exact mul_eq_one_iff_eq_inv.mpr (e1.symm.trans htut)
    have hu2 : u ^ 2 = 1 := by rw [pow_two]; exact h3
    have hord : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
    have h4 : orderOf u = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h5 | h5
      · exact absurd (orderOf_eq_one_iff.mp h5) hu1
      · exact h5
    have hk1 : k = 1 := by omega
    rw [hk1, pow_one] at hw
    have h6 : t = t * t' := by rw [← hu, ← hw]; exact h
    exact ht'1 (mul_eq_left.mp h6.symm)
  refine ⟨klein t w htt hww hwt, ?_, klein_isElemAbelian2 htt hww hwt,
    card_klein htt hww hwt ht1 hw1 htw, Or.inr (Or.inl rfl)⟩
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) k
  · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))) k)

theorem even_of_three_dvd_two_pow_sub_one {a : ℕ} (h : 3 ∣ 2 ^ a - 1) : Even a := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases a with _ | _ | a
    · exact ⟨0, rfl⟩
    · norm_num at h
    · have h2 : 2 ^ (a + 2) = 4 * 2 ^ a := by ring
      have hpos : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      rw [h2] at h
      have h3 : 3 ∣ 2 ^ a - 1 := by omega
      obtain ⟨m, hm⟩ := ih a (by omega) h3
      exact ⟨m + 1, by omega⟩

theorem commV_card_three (hV : ∀ v : V, v ^ 2 = 1) {S : Subgroup (MulAut V)} (hS : Nat.card S = 3) :
    commV S ⊔ fixV S = ⊤ ∧ commV S ⊓ fixV S = ⊥ ∧ rk (commV S) + rk (fixV S) = rk V ∧
      Even (rk (commV S)) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hodd : Odd (Nat.card S) := by rw [hS]; exact ⟨1, rfl⟩
  obtain ⟨h1, h2⟩ := coprime_decomp hodd hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)
  rw [← commV_eq_commSub, top_inf_eq] at h1 h2
  have hrk : rk (commV S) + rk (fixV S) = rk V := by
    have := rk_sup_add_rk_inf (commV S) (fixV S)
    rw [h1, h2, rk_bot, rk_top] at this
    omega
  refine ⟨h1, h2, hrk, ?_⟩
  have hinv : ∀ g ∈ S, ∀ f ∈ commV S, g f ∈ commV S := fun g hg f hf =>
    commV_smul_mem (fun q hq => by
      have := S.mul_mem (S.mul_mem hg hq) (S.inv_mem hg)
      exact this) hf
  by_cases hbot : commV S = ⊥
  · rw [hbot, rk_bot]; exact ⟨0, rfl⟩
  · have hdvd := prime_dvd_card_sub_one hS hinv h2
    rw [card_eq_two_pow hV (commV S)] at hdvd
    exact even_of_three_dvd_two_pow_sub_one hdvd

theorem exists_order_three_fixed (hV : ∀ v : V, v ^ 2 = 1) (hrk : rk V = 4)
    {Q : Subgroup (MulAut V)} (hQ : Nat.card Q = 9) :
    ∃ q ∈ Q, orderOf q = 3 ∧ ∃ v : V, v ≠ 1 ∧ q v = v := by
  by_contra hcon
  push Not at hcon
  have hfree : ∀ g ∈ Q, ∀ v ∈ {v : V | v ∈ (⊤ : Subgroup V) ∧ v ≠ 1}, g v = v → g = 1 := by
    intro g hg v hv hgv
    by_contra hg1
    have hdvd : orderOf g ∣ 9 := by
      have := orderOf_dvd_natCard (⟨g, hg⟩ : ↥Q)
      rwa [Subgroup.orderOf_mk, hQ] at this
    have h3 : 3 ∣ orderOf g := by
      have hg1' : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
      have hd : orderOf g ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hdivs : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [hdivs] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with h | h | h
      · exact absurd h hg1'
      · rw [h]
      · rw [h]; norm_num
    have hco : orderOf g ≠ 0 := (orderOf_pos g).ne'
    set q := g ^ (orderOf g / 3) with hq
    have hqo : orderOf q = 3 := orderOf_pow_orderOf_div hco h3
    have hqQ : q ∈ Q := Q.pow_mem hg _
    have hqv : q v = v := by
      have hs : g ∈ MulAction.stabilizer (MulAut V) v := hgv
      exact Subgroup.pow_mem _ hs _
    exact hcon q hqQ hqo v hv.2 hqv
  have hΩ : ∀ g ∈ Q, ∀ v ∈ {v : V | v ∈ (⊤ : Subgroup V) ∧ v ≠ 1},
      g v ∈ {v : V | v ∈ (⊤ : Subgroup V) ∧ v ≠ 1} := by
    intro g hg v hv
    refine ⟨Subgroup.mem_top _, fun h => hv.2 (g.injective (by rw [h, map_one]))⟩
  have hdvd := card_dvd_card_of_free hΩ hfree
  have hΩcard : Nat.card {v : V | v ∈ (⊤ : Subgroup V) ∧ v ≠ 1} = 15 := by
    have h1 := card_ne_one_add_one (⊤ : Subgroup V)
    have h2 : Nat.card (⊤ : Subgroup V) = 16 := by
      rw [card_eq_two_pow hV, rk_top, hrk]; norm_num
    have h3 : Nat.card {v : V | v ∈ (⊤ : Subgroup V) ∧ v ≠ 1} =
        Nat.card {c : V // c ∈ (⊤ : Subgroup V) ∧ c ≠ 1} := rfl
    omega
  rw [hQ, hΩcard] at hdvd
  omega

omit [Finite V] in
theorem conjBy_eq_of_mem_normalizer {g : MulAut V} {Y : Subgroup (MulAut V)}
    (hg : g ∈ Subgroup.normalizer (Y : Set (MulAut V))) : conjBy g Y = Y := by
  ext y
  rw [mem_conjBy_iff]
  have h := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g))
  have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rw [e] at h
  exact h

theorem fixV_fittingOf_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hO2 : pCoreOf 2 X = ⊥) (hcomm : commV (fittingOf X) = ⊤) : fixV (fittingOf X) = ⊥ := by
  obtain ⟨-, hinf⟩ := coprime_decomp (odd_card_fittingOf hO2) hV (W := ⊤)
    (fun _ _ w _ => Subgroup.mem_top _)
  rw [← commV_eq_commSub, hcomm, top_inf_eq, top_inf_eq] at hinf
  exact hinf

theorem rk_commSub_inverted_le (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} {t x : MulAut V}
    (ht2 : t ^ 2 = 1) (hodd : Odd (orderOf x)) (hinv : t * x * t⁻¹ = x⁻¹)
    (hWt : ∀ g ∈ Subgroup.zpowers t, ∀ w ∈ W, g w ∈ W)
    (hWx : ∀ g ∈ Subgroup.zpowers x, ∀ w ∈ W, g w ∈ W)
    (hm : rk (commSub W (Subgroup.zpowers t)) ≤ 2) (hx : ∃ w ∈ W, x w ≠ w) :
    Even (rk (commSub W (Subgroup.zpowers x))) ∧ 1 ≤ rk (commSub W (Subgroup.zpowers x)) ∧
      rk (commSub W (Subgroup.zpowers x)) ≤ 2 * rk (commSub W (Subgroup.zpowers t)) := by
  have hts : t ∈ stabSub W := by
    intro u
    constructor
    · intro hu
      have h2 : t (t u) = u := by
        have : (t ^ 2) u = u := by rw [ht2]; rfl
        simpa [pow_two] using this
      rw [← h2]
      exact hWt t (Subgroup.mem_zpowers t) _ hu
    · exact hWt t (Subgroup.mem_zpowers t) u
  have hxs : x ∈ stabSub W := by
    intro u
    constructor
    · intro hu
      have hinvmem : x⁻¹ ∈ Subgroup.zpowers x := Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
      have := hWx x⁻¹ hinvmem (x u) hu
      simpa using this
    · exact hWx x (Subgroup.mem_zpowers x) u
  have hVW : ∀ w : W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  set t' := resHom W ⟨t, hts⟩ with ht'
  set x' := resHom W ⟨x, hxs⟩ with hx'
  have ht2' : t' ^ 2 = 1 := by
    rw [ht', ← map_pow]
    have : (⟨t, hts⟩ : stabSub W) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    rw [this, map_one]
  have hxt' : t' * x' * t'⁻¹ = x'⁻¹ := by
    rw [ht', hx', ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (by simpa using hinv)
  have hx1 : x' ≠ 1 := by
    intro h
    obtain ⟨w, hw, hxw⟩ := hx
    apply hxw
    have := congrArg (fun φ : MulAut W => ((φ ⟨w, hw⟩ : W) : V)) h
    simpa [hx', resHom_apply] using this
  have hxodd : Odd (orderOf x') := by
    have h1 : orderOf x' ∣ orderOf x := by
      have := orderOf_map_dvd (resHom W) (⟨x, hxs⟩ : stabSub W)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hodd h1
  have hm' : rk (commV (Subgroup.zpowers t')) ≤ 2 := by
    rw [ht', rk_commV_resHom hts hWt]
    exact hm
  obtain ⟨h1, h2, -⟩ := d2_11_core hVW ht2' hm' hx1 hxodd hxt'
  have hr1 : rk (commV (Subgroup.zpowers x')) = rk (commSub W (Subgroup.zpowers x)) := by
    rw [hx', rk_commV_resHom hxs hWx]
  have hr2 : rk (commV (Subgroup.zpowers t')) = rk (commSub W (Subgroup.zpowers t)) := by
    rw [ht', rk_commV_resHom hts hWt]
  rw [hr1] at h1
  rw [hr2] at h2
  refine ⟨⟨rk (commSub (commV (Subgroup.zpowers x')) (Subgroup.zpowers t')), by omega⟩, ?_,
    by omega⟩
  have := one_le_rk_commV_zpowers hVW hx1
  rw [hr1] at this
  exact this

omit [Finite V] in
theorem commV_zpowers_le_of_fixes {U₁ U₂ : Subgroup V} (hd : U₁ ⊔ U₂ = ⊤) {t : MulAut V}
    (ht2 : t ^ 2 = 1) (hU₁ : ∀ u ∈ U₁, t u ∈ U₁) (hfix : ∀ u ∈ U₂, t u = u) :
    commV (Subgroup.zpowers t) ≤ U₁ ∧ Subgroup.zpowers t ≤ centSub U₂ := by
  refine ⟨?_, Subgroup.zpowers_le.mpr (fun u hu => hfix u hu)⟩
  apply commV_zpowers_le_of_forall ht2
  intro v
  have hv : v ∈ U₁ ⊔ U₂ := by rw [hd]; exact Subgroup.mem_top v
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.mp hv
  rw [map_mul, hfix v₂ hv₂, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
  exact U₁.mul_mem (hU₁ v₁ hv₁) (U₁.inv_mem hv₁)

theorem rk_commSub_iSup {ι : Type*} [Fintype ι] (S : ι → Subgroup V) (hS : iSupIndep S)
    {t : MulAut V} (hinv : ∀ i, ∀ x ∈ Subgroup.zpowers t, ∀ u ∈ S i, x u ∈ S i) :
    rk (commSub (⨆ i, S i) (Subgroup.zpowers t)) =
      ∑ i, rk (commSub (S i) (Subgroup.zpowers t)) := by
  classical
  have hinvS : ∀ x ∈ Subgroup.zpowers t, ∀ u ∈ (⨆ i, S i), x u ∈ ⨆ i, S i := by
    intro x hx u hu
    have hle : (⨆ i, S i) ≤ (⨆ i, S i).comap x.toMonoidHom := by
      refine iSup_le fun i u hu => ?_
      exact le_iSup S i (hinv i x hx u hu)
    exact hle hu
  rw [commSub_zpowers_eq_map hinvS, Subgroup.map_iSup]
  have hT : ∀ i, (S i).map (commHom t) = commSub (S i) (Subgroup.zpowers t) := fun i =>
    (commSub_zpowers_eq_map (hinv i)).symm
  have e : (⨆ i, (S i).map (commHom t)) = ⨆ i, commSub (S i) (Subgroup.zpowers t) :=
    iSup_congr hT
  rw [e]
  have hind : iSupIndep (fun i => commSub (S i) (Subgroup.zpowers t)) :=
    hS.mono fun i => commSub_le_of_invariant (hinv i)
  have := rk_iSup_biSup_eq_sum (fun i => commSub (S i) (Subgroup.zpowers t)) hind Finset.univ
  have e2 : (⨆ i ∈ (Finset.univ : Finset ι), commSub (S i) (Subgroup.zpowers t)) =
      ⨆ i, commSub (S i) (Subgroup.zpowers t) :=
    iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [e2] at this
  exact this

end CFSG.Quasithin
