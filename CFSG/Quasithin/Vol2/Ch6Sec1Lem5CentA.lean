module

public import CFSG.Quasithin.Background.E2Three

public section

namespace CFSG.Quasithin.H13

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

abbrev SL22 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

@[expose] def g3_615 : SL22 := ⟨!![0, 1; 1, 1], by decide⟩

theorem g3_615_ne_one : g3_615 ≠ 1 := by decide

theorem g3_615_pow_three : g3_615 ^ 3 = 1 := by decide

theorem pow_six_sl22 : ∀ g : SL22, g ^ 6 = 1 := by decide

theorem inv_conj_sl22 : ∀ a x : SL22, a ≠ 1 → a ^ 2 = 1 → x ≠ 1 → x ^ 3 = 1 →
    a * x * a⁻¹ = x⁻¹ := by decide

theorem eq_of_pow_three_sl22 : ∀ u v : SL22, u ^ 3 = 1 → v ^ 3 = 1 → v ≠ 1 →
    u = 1 ∨ u = v ∨ u = v⁻¹ := by decide

theorem eq_one_of_comm_sl22 : ∀ z : SL22, (∀ g : SL22, z * g = g * z) → z = 1 := by decide

theorem commutator_mem_sl22 : ∀ a b : SL22, a * b * a⁻¹ * b⁻¹ = 1 ∨
    a * b * a⁻¹ * b⁻¹ = g3_615 ∨ a * b * a⁻¹ * b⁻¹ = g3_615⁻¹ := by decide

theorem card_sl22 : Nat.card SL22 = 6 := by rw [Nat.card_eq_fintype_card]; decide

theorem card_sl22_sq : Nat.card (SL22 × SL22) = 36 := by
  rw [Nat.card_prod, card_sl22]

theorem eq_of_commute_sl22 : ∀ u v : SL22, u ^ 2 = 1 → v ^ 2 = 1 → u * v = v * u →
    u = 1 ∨ v = 1 ∨ u = v := by
  decide

theorem exists_inl_sl22 (s₁ s₂ : SL22 × SL22) (h₁ : s₁ ≠ 1) (h₂ : s₂ ≠ 1) (h₁₂ : s₁ ≠ s₂)
    (h₁2 : s₁ ^ 2 = 1) (h₂2 : s₂ ^ 2 = 1) (hc : s₁ * s₂ = s₂ * s₁) :
    (s₁.2 = 1 ∧ s₁.1 ≠ 1) ∨ (s₂.2 = 1 ∧ s₂.1 ≠ 1) ∨ ((s₁ * s₂).2 = 1 ∧ (s₁ * s₂).1 ≠ 1) := by
  obtain ⟨a, b⟩ := s₁
  obtain ⟨c, d⟩ := s₂
  simp only [ne_eq, Prod.mk_eq_one, not_and_or, Prod.mk.injEq, Prod.pow_mk,
    Prod.mk_mul_mk] at h₁ h₂ h₁₂ h₁2 h₂2 hc ⊢
  rcases eq_of_commute_sl22 a c h₁2.1 h₂2.1 hc.1 with rfl | rfl | rfl <;>
  rcases eq_of_commute_sl22 b d h₁2.2 h₂2.2 hc.2 with rfl | rfl | rfl <;>
  (simp_all [sq]; try exact fun h => h₁₂ h.symm)

theorem isSolvable_sl22 : Group.IsSolvable SL22 := by
  rw [Group.isSolvable_def]
  refine ⟨2, ?_⟩
  have h1 : derivedSeries SL22 1 ≤ Subgroup.zpowers g3_615 := by
    rw [derivedSeries_succ, derivedSeries_zero, Subgroup.commutator_le]
    intro a _ b _
    rcases commutator_mem_sl22 a b with h | h | h
    · rw [commutatorElement_def, h]; exact Subgroup.one_mem _
    · rw [commutatorElement_def, h]; exact Subgroup.mem_zpowers _
    · rw [commutatorElement_def, h]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  rw [derivedSeries_succ, eq_bot_iff]
  refine (Subgroup.commutator_mono h1 h1).trans ?_
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm, ← _root_.zpow_add,
    ← _root_.zpow_add, add_comm]


@[expose] noncomputable def slCongr615 {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by ext i j; simp
  right_inv A := by ext i j; simp
  map_mul' := map_mul _

variable {W : Type*} [CommGroup W]

theorem exists_hom_of_isL2Natural_ch615 {L : Subgroup (MulAut W)} {C : Subgroup W}
    (h : E2.IsL2Natural L C 1) :
    ∃ ψ : SL22 →* MulAut W, Function.Injective ψ ∧ ψ.range = L := by
  obtain ⟨-, F, _, _, hF, e, -⟩ := h
  have hcard : Fintype.card F = Fintype.card (ZMod 2) := by rw [hF, ZMod.card]; rfl
  let κ : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard
  let θ : SL22 ≃* ↥L := ((e.trans (slCongr615 κ))).symm
  refine ⟨L.subtype.comp θ.toMonoidHom, ?_, ?_⟩
  · exact L.subtype_injective.comp θ.injective
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr θ.surjective, Subgroup.map_top,
      Subgroup.range_subtype]

theorem exists_hom_two_ch615 {L₁ L₂ : Subgroup (MulAut W)} {ψ₁ ψ₂ : SL22 →* MulAut W}
    (hψ₁ : Function.Injective ψ₁) (hψ₂ : Function.Injective ψ₂) (hr₁ : ψ₁.range = L₁)
    (hr₂ : ψ₂.range = L₂) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hdisj : L₁ ⊓ L₂ = ⊥) :
    ∃ ψ : SL22 × SL22 →* MulAut W, Function.Injective ψ ∧ ψ.range = L₁ ⊔ L₂ ∧
      (∀ u, ψ (u, 1) = ψ₁ u) ∧ (∀ v, ψ (1, v) = ψ₂ v) := by
  have hc : ∀ m n, Commute (ψ₁ m) (ψ₂ n) := fun m n =>
    hcomm _ (hr₁ ▸ ⟨m, rfl⟩) _ (hr₂ ▸ ⟨n, rfl⟩)
  refine ⟨ψ₁.noncommCoprod ψ₂ hc, ?_, ?_, fun u => ?_, fun v => ?_⟩
  · rw [MonoidHom.noncommCoprod_injective]
    refine ⟨hψ₁, hψ₂, ?_⟩
    rw [hr₁, hr₂, disjoint_iff]
    exact hdisj
  · rw [MonoidHom.noncommCoprod_range, hr₁, hr₂]
  · simp [MonoidHom.noncommCoprod_apply]
  · simp [MonoidHom.noncommCoprod_apply]

theorem orderOf_dvd_six_sq_ch615 (s : SL22 × SL22) : orderOf s ∣ 6 :=
  orderOf_dvd_of_pow_eq_one (Prod.ext (pow_six_sl22 s.1) (pow_six_sl22 s.2))

theorem pow_three_of_odd_ch615 {s : SL22 × SL22} (h : Odd (orderOf s)) : s ^ 3 = 1 := by
  have h6 := orderOf_dvd_six_sq_ch615 s
  have h3 : orderOf s ∣ 3 := by
    have : Nat.Coprime (orderOf s) 2 := Nat.coprime_two_right.mpr h
    have h63 : (6 : ℕ) = 2 * 3 := rfl
    rw [h63] at h6
    exact this.dvd_of_dvd_mul_left h6
  exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem pow_two_of_pow_two_pow_ch615 {s : SL22 × SL22} {k : ℕ} (h : s ^ 2 ^ k = 1) :
    s ^ 2 = 1 := by
  have h6 := orderOf_dvd_six_sq_ch615 s
  have hk := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hk
  have h2 : orderOf s ∣ 2 := by
    rcases j with _ | _ | j
    · rw [hj]; exact one_dvd _
    · rw [hj]; simp
    · exfalso
      have : 2 ^ (j + 2) ∣ 6 := hj ▸ h6
      have h4 : 4 ∣ 6 := (pow_dvd_pow 2 (by omega : 2 ≤ j + 2)).trans this
      omega
  exact orderOf_dvd_iff_pow_eq_one.mp h2

theorem two_data_ch615 [Finite W] {ψ : SL22 × SL22 →* MulAut W} (hψ : Function.Injective ψ)
    {S : Subgroup (MulAut W)} (hS : IsSylowTwoOf S ψ.range) {t : MulAut W}
    (htB : ∀ b ∈ ψ.range, t * b * t⁻¹ ∈ ψ.range)
    (ht₁ : ∀ u : SL22, ∃ v : SL22, t * ψ (u, 1) * t⁻¹ = ψ (1, v))
    (ht₂ : ∀ v : SL22, ∃ u : SL22, ψ (1, v) = t * ψ (u, 1) * t⁻¹) {g : SL22} (hg1 : g ≠ 1)
    (hg3 : g ^ 3 = 1) :
    ∃ a ∈ S, a * ψ (g, 1) * a⁻¹ = (ψ (g, 1))⁻¹ ∧
      a * (t * ψ (g, 1) * t⁻¹) * a⁻¹ = t * ψ (g, 1) * t⁻¹ ∧
      (t * (t * ψ (g, 1) * t⁻¹) * t⁻¹ = ψ (g, 1) ∨
        t * (t * ψ (g, 1) * t⁻¹) * t⁻¹ = (ψ (g, 1))⁻¹) ∧
      ∀ b ∈ ψ.range, Odd (orderOf b) →
        b ∈ Subgroup.closure {ψ (g, 1), t * ψ (g, 1) * t⁻¹} := by
  classical
  have hx1 : ψ (g, 1) ≠ 1 := by
    intro h1
    have := hψ (h1.trans (map_one ψ).symm)
    exact hg1 (by simpa using congrArg Prod.fst this)
  obtain ⟨h, hh⟩ := ht₁ g
  have hh3 : h ^ 3 = 1 := by
    have e : ψ ((1, h) ^ 3) = 1 := by
      rw [map_pow, ← hh, conj_pow, ← map_pow,
        show (g, (1 : SL22)) ^ 3 = 1 from Prod.ext hg3 (one_pow 3), map_one]
      group
    have := hψ (e.trans (map_one ψ).symm)
    simpa using congrArg Prod.snd this
  have hh1 : h ≠ 1 := by
    intro h1
    apply hx1
    rw [h1, show ((1 : SL22), (1 : SL22)) = 1 from rfl, map_one] at hh
    have := congrArg (fun z => t⁻¹ * z * t) hh
    simpa [mul_assoc] using this
  have hBcard : Nat.card ψ.range = 36 := by
    rw [← card_sl22_sq]
    exact Nat.card_congr (MonoidHom.ofInjective hψ).symm.toEquiv
  have hScard : Nat.card S = 4 := by
    obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
    have hmul : S.relIndex ψ.range * Nat.card S = 36 := by
      have h1 := Subgroup.relIndex_mul_card S ψ.range
      rwa [inf_eq_left.mpr hS.1, hBcard] at h1
    rw [hk] at hmul ⊢
    have hodd : ¬ 2 ∣ S.relIndex ψ.range := hS.2.2
    have hk5 : k < 6 := by
      by_contra hk6
      have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 0 < S.relIndex ψ.range := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hmul)
      nlinarith
    interval_cases k <;> omega
  have hSmap : (S.comap ψ).map ψ = S := Subgroup.map_comap_eq_self hS.1
  have hS'card : Nat.card (S.comap ψ) = 4 := by
    rw [← hScard]
    conv_rhs => rw [← hSmap]
    rw [Subgroup.card_map_of_injective hψ]
  have hS'2 : ∀ s ∈ S.comap ψ, s ^ 2 = 1 := by
    intro s hs
    obtain ⟨k, hk⟩ := hS.2.1 ⟨ψ s, hs⟩
    have hk' : ψ (s ^ 2 ^ k) = 1 := by
      rw [map_pow]; simpa using congrArg Subtype.val hk
    exact pow_two_of_pow_two_pow_ch615 (hψ (hk'.trans (map_one ψ).symm))
  have hS'comm : ∀ s ∈ S.comap ψ, ∀ s' ∈ S.comap ψ, s * s' = s' * s := by
    intro s hs s' hs'
    have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := ↥(S.comap ψ))
      (by rw [hS'card]; norm_num)).is_comm.comm ⟨s, hs⟩ ⟨s', hs'⟩
    simpa using congrArg Subtype.val this
  obtain ⟨s₁, hs₁, hs₁1⟩ : ∃ s₁ ∈ S.comap ψ, s₁ ≠ 1 := by
    by_contra hall
    have : S.comap ψ = ⊥ := eq_bot_iff.mpr fun s hs => by
      by_contra hs1
      exact hall ⟨s, hs, hs1⟩
    rw [this, Subgroup.card_bot] at hS'card
    omega
  obtain ⟨s₂, hs₂, hs₂z⟩ : ∃ s₂ ∈ S.comap ψ, s₂ ∉ Subgroup.zpowers s₁ := by
    by_contra hall
    have hle : S.comap ψ ≤ Subgroup.zpowers s₁ := fun s hs => by
      by_contra hs1
      exact hall ⟨s, hs, hs1⟩
    have h1 : Nat.card (S.comap ψ) ≤ Nat.card (Subgroup.zpowers s₁) :=
      Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf s₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (hS'2 s₁ hs₁)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hs₂1 : s₂ ≠ 1 := fun h1 => hs₂z (h1 ▸ Subgroup.one_mem _)
  have hs₁₂ : s₁ ≠ s₂ := fun h1 => hs₂z (h1 ▸ Subgroup.mem_zpowers _)
  obtain ⟨s, hsS', hs2, hs1⟩ : ∃ s ∈ S.comap ψ, s.2 = 1 ∧ s.1 ≠ 1 := by
    rcases exists_inl_sl22 s₁ s₂ hs₁1 hs₂1 hs₁₂ (hS'2 s₁ hs₁) (hS'2 s₂ hs₂)
      (hS'comm s₁ hs₁ s₂ hs₂) with h | h | h
    · exact ⟨s₁, hs₁, h⟩
    · exact ⟨s₂, hs₂, h⟩
    · exact ⟨s₁ * s₂, (S.comap ψ).mul_mem hs₁ hs₂, h⟩
  have hseq : s = (s.1, 1) := Prod.ext rfl hs2
  have hu2 : s.1 ^ 2 = 1 := by
    have := hS'2 s hsS'
    rw [hseq] at this
    simpa using congrArg Prod.fst this
  refine ⟨ψ s, hsS', ?_, ?_, ?_, ?_⟩
  ·
    have e : s * (g, 1) * s⁻¹ = (g, 1)⁻¹ := by
      rw [hseq]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_mul, Prod.fst_inv]
        exact inv_conj_sl22 s.1 g hs1 hu2 hg1 hg3
      · simp
    rw [← map_inv, ← map_mul, ← map_mul, e, map_inv]
  ·
    have e : s * (1, h) * s⁻¹ = (1, h) := by
      rw [hseq]
      exact Prod.ext (by simp) (by simp)
    rw [hh, ← map_inv, ← map_mul, ← map_mul, e]
  ·
    obtain ⟨w, hw⟩ := htB (t * ψ (g, 1) * t⁻¹)
      (by rw [hh]; exact MonoidHom.mem_range.mpr ⟨(1, h), rfl⟩)
    have hw2 : w.2 = 1 := by
      refine eq_one_of_comm_sl22 _ fun v => ?_
      obtain ⟨u, hu⟩ := ht₂ v
      have hcom : ψ w * ψ (1, v) = ψ (1, v) * ψ w := by
        rw [hw, hu]
        have e1 : t * (t * ψ (g, 1) * t⁻¹) * t⁻¹ * (t * ψ (u, 1) * t⁻¹) =
            t * ((t * ψ (g, 1) * t⁻¹) * ψ (u, 1)) * t⁻¹ := by group
        have e2 : t * ψ (u, 1) * t⁻¹ * (t * (t * ψ (g, 1) * t⁻¹) * t⁻¹) =
            t * (ψ (u, 1) * (t * ψ (g, 1) * t⁻¹)) * t⁻¹ := by group
        have e3 : ((1 : SL22), h) * (u, 1) = (u, 1) * (1, h) := Prod.ext (by simp) (by simp)
        rw [e1, e2, hh, ← map_mul, ← map_mul, e3]
      rw [← map_mul, ← map_mul] at hcom
      have := hψ hcom
      simpa using congrArg Prod.snd this
    have hw1 : w.1 ^ 3 = 1 := by
      have e : ψ (w ^ 3) = 1 := by
        rw [map_pow, hw, conj_pow, conj_pow, ← map_pow,
          show (g, (1 : SL22)) ^ 3 = 1 from Prod.ext hg3 (one_pow 3), map_one]
        group
      have := hψ (e.trans (map_one ψ).symm)
      simpa using congrArg Prod.fst this
    rcases eq_of_pow_three_sl22 w.1 g hw1 hg3 hg1 with h1 | h1 | h1
    · exfalso
      apply hx1
      have hw' : w = 1 := Prod.ext h1 hw2
      rw [hw', map_one] at hw
      have := congrArg (fun z => t⁻¹ * (t⁻¹ * z * t) * t) hw
      simpa [mul_assoc] using this.symm
    · left
      rw [← hw, show w = (g, 1) from Prod.ext h1 hw2]
    · right
      rw [← hw, show w = (g⁻¹, 1) from Prod.ext h1 hw2, ← map_inv, Prod.inv_mk, inv_one]
  ·
    rintro b ⟨w, rfl⟩ hodd
    rw [orderOf_injective ψ hψ w] at hodd
    have hw3 := pow_three_of_odd_ch615 hodd
    have hw31 : w.1 ^ 3 = 1 := by simpa using congrArg Prod.fst hw3
    have hw32 : w.2 ^ 3 = 1 := by simpa using congrArg Prod.snd hw3
    have hsplit : ψ w = ψ (w.1, 1) * ψ (1, w.2) := by rw [← map_mul]; simp
    rw [hsplit]
    refine Subgroup.mul_mem _ ?_ ?_
    · have hsub : Subgroup.zpowers (ψ (g, 1)) ≤
          Subgroup.closure {ψ (g, 1), t * ψ (g, 1) * t⁻¹} :=
        Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
      refine hsub ?_
      rcases eq_of_pow_three_sl22 w.1 g hw31 hg3 hg1 with
        h1 | h1 | h1
      · rw [h1, show ((1 : SL22), (1 : SL22)) = 1 from rfl, map_one]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.mem_zpowers _
      · rw [h1, show ((g⁻¹ : SL22), (1 : SL22)) = (g, 1)⁻¹ by simp, map_inv]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    · have hsub : Subgroup.zpowers (t * ψ (g, 1) * t⁻¹) ≤
          Subgroup.closure {ψ (g, 1), t * ψ (g, 1) * t⁻¹} :=
        Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
      refine hsub ?_
      rcases eq_of_pow_three_sl22 w.2 h hw32 hh3 hh1 with h1 | h1 | h1
      · rw [h1, show ((1 : SL22), (1 : SL22)) = 1 from rfl, map_one]; exact Subgroup.one_mem _
      · rw [h1, ← hh]; exact Subgroup.mem_zpowers _
      · rw [h1, show ((1 : SL22), h⁻¹) = (1, h)⁻¹ by simp, map_inv, ← hh]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

theorem one_data_ch615 {ψ : SL22 →* MulAut W} (hψ : Function.Injective ψ) {g : SL22}
    (hg1 : g ≠ 1) (hg3 : g ^ 3 = 1) :
    ∀ b ∈ ψ.range, Odd (orderOf b) → b ∈ Subgroup.zpowers (ψ g) := by
  rintro b ⟨w, rfl⟩ hodd
  rw [orderOf_injective ψ hψ w] at hodd
  have h6 : orderOf w ∣ 6 := orderOf_dvd_of_pow_eq_one (pow_six_sl22 w)
  have h3 : orderOf w ∣ 3 := by
    have : Nat.Coprime (orderOf w) 2 := Nat.coprime_two_right.mpr hodd
    exact this.dvd_of_dvd_mul_left (show orderOf w ∣ 2 * 3 from h6)
  rcases eq_of_pow_three_sl22 w g (orderOf_dvd_iff_pow_eq_one.mp h3) hg3 hg1 with h1 | h1 | h1
  · rw [h1, map_one]; exact Subgroup.one_mem _
  · rw [h1]; exact Subgroup.mem_zpowers _
  · rw [h1, map_inv]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)


end CFSG.Quasithin.H13
