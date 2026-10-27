module

public import CFSG.Quasithin.Background.CommVCommute
public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5CentA

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

section ModD2


variable {W : Type*} [CommGroup W]

theorem mem_fixV_zpowers_iff_ch615 {σ : MulAut W} {w : W} :
    w ∈ fixV (Subgroup.zpowers σ) ↔ σ w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem commV_inf_fixV_ch615 (hW : ∀ w : W, w ^ 2 = 1) {σ : MulAut W} (h3 : σ ^ 3 = 1) :
    commV (Subgroup.zpowers σ) ⊓ fixV (Subgroup.zpowers σ) = ⊥ := by
  have hσ3 : ∀ w, σ (σ (σ w)) = w := fun w => by
    have := congrArg (fun φ : MulAut W => φ w) h3
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using this
  let N : W →* W := MonoidHom.mk' (fun w => w * σ w * σ (σ w)) fun a b => by
    simp only [map_mul]
    ac_rfl
  have hN : ∀ w, N w = w * σ w * σ (σ w) := fun w => rfl
  have hNx : ∀ x ∈ Subgroup.zpowers σ, ∀ w, N (x w) = N w := by
    intro x hx
    rw [Subgroup.zpowers_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.mp hx]
      intro w
      rw [hN, hN, hσ3]
      ac_rfl
    | one => intro w; rfl
    | mul x y _ _ hx hy => intro w; rw [MulAut.mul_apply, hx, hy]
    | inv x _ hx =>
      intro w
      rw [← hx (x⁻¹ w), MulAut.apply_inv_self]
  have hcomm : commV (Subgroup.zpowers σ) ≤ N.ker := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hNx x hx, mul_inv_cancel]
  rw [eq_bot_iff]
  rintro w ⟨hw1, hw2⟩
  have hσw : σ w = w := hw2 σ (Subgroup.mem_zpowers σ)
  have h1 : N w = 1 := hcomm hw1
  rw [hN, hσw, hσw] at h1
  have h2 : w * w = 1 := by rw [← pow_two]; exact hW w
  rw [h2, one_mul] at h1
  exact (Subgroup.mem_bot).mpr h1

theorem mem_commV_of_normalizes_ch615 {σ τ : MulAut W}
    (hτ : ∀ x ∈ Subgroup.zpowers σ, τ * x * τ⁻¹ ∈ Subgroup.zpowers σ) {w : W}
    (hw : w ∈ commV (Subgroup.zpowers σ)) : τ w ∈ commV (Subgroup.zpowers σ) := by
  unfold commV at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    refine Subgroup.subset_closure ⟨τ * x * τ⁻¹, hτ x hx, τ v, ?_⟩
    rw [map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem mem_commV_of_comm_ch615 {σ τ : MulAut W} (hτ : τ * σ = σ * τ) {w : W}
    (hw : w ∈ commV (Subgroup.zpowers σ)) : τ w ∈ commV (Subgroup.zpowers σ) :=
  CFSG.Quasithin.apply_mem_commV_zpowers_of_commute hτ hw

theorem eq_of_mem_commV_ch615 [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {σ : MulAut W}
    (h3 : σ ^ 3 = 1) (hcard : Nat.card (commV (Subgroup.zpowers σ)) ≤ 4) {y : W}
    (hy : y ∈ commV (Subgroup.zpowers σ)) (hy1 : y ≠ 1) {x : W}
    (hx : x ∈ commV (Subgroup.zpowers σ)) : x = 1 ∨ x = y ∨ x = σ y ∨ x = σ (σ y) := by
  classical
  set Y := commV (Subgroup.zpowers σ) with hYdef
  have hσ3 : ∀ w, σ (σ (σ w)) = w := fun w => by
    have := congrArg (fun φ : MulAut W => φ w) h3
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using this
  have hfix : ∀ w ∈ Y, σ w = w → w = 1 := fun w hw hσw =>
    (Subgroup.mem_bot).mp ((commV_inf_fixV_ch615 hW h3).le
      ⟨hw, mem_fixV_zpowers_iff_ch615.mpr hσw⟩)
  have hσY : ∀ w ∈ Y, σ w ∈ Y := fun w hw => mem_commV_of_comm_ch615 rfl hw
  have h1 : σ y ≠ y := fun h => hy1 (hfix y hy h)
  have h2 : σ (σ y) ≠ y := fun h => by
    apply h1
    have := congrArg σ h
    rw [hσ3] at this
    exact this.symm
  have h3' : σ (σ y) ≠ σ y := fun h => h1 (σ.injective h)
  have hσy1 : σ y ≠ 1 := fun h => hy1 (σ.injective (h.trans (map_one σ).symm))
  have hσσy1 : σ (σ y) ≠ 1 := fun h => hσy1 (σ.injective (h.trans (map_one σ).symm))
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hx1, hxy, hxσ, hxσσ⟩ := hne
  set s : Finset W := {x, 1, y, σ y, σ (σ y)} with hs
  have hscard : s.card = 5 := by
    rw [hs, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_pair h3'.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1.symm, h2.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hy1 h.symm, fun h => hσy1 h.symm, fun h => hσσy1 h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hx1, hxy, hxσ, hxσσ⟩
  have hsub : (s : Set W) ⊆ (Y : Set W) := by
    intro a ha
    simp only [hs, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact hx
    · exact Y.one_mem
    · exact hy
    · exact hσY _ hy
    · exact hσY _ (hσY _ hy)
  have hle : (s : Set W).ncard ≤ (Y : Set W).ncard := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, hscard] at hle
  have hY : (Y : Set W).ncard = Nat.card Y := (Nat.card_coe_set_eq _).symm
  omega

theorem apply_three_ch615 {σ : MulAut W} (h3 : σ ^ 3 = 1) (w : W) : σ (σ (σ w)) = w := by
  have := congrArg (fun φ : MulAut W => φ w) h3
  simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using this

theorem existsUnique_fix_ch615 [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {σ ρ : MulAut W}
    (h3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hcard : Nat.card (commV (Subgroup.zpowers σ)) ≤ 4)
    (hρσ : ρ * σ * ρ⁻¹ = σ⁻¹) :
    ∃! w, w ∈ commV (Subgroup.zpowers σ) ∧ w ≠ 1 ∧ ρ w = w := by
  set Y := commV (Subgroup.zpowers σ) with hYdef
  have hσ3 := apply_three_ch615 h3
  have hfix : ∀ w ∈ Y, σ w = w → w = 1 := fun w hw hσw =>
    (Subgroup.mem_bot).mp ((commV_inf_fixV_ch615 hW h3).le
      ⟨hw, mem_fixV_zpowers_iff_ch615.mpr hσw⟩)
  have hσY : ∀ w ∈ Y, σ w ∈ Y := fun w hw => mem_commV_of_comm_ch615 rfl hw
  have hinv : σ⁻¹ = σ * σ := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact h3)
  have hρσ' : ρ * σ = σ⁻¹ * ρ := by rw [← hρσ, inv_mul_cancel_right]
  have hρv : ∀ v, ρ (σ v) = σ (σ (ρ v)) := fun v => by
    rw [← MulAut.mul_apply, hρσ', MulAut.mul_apply, hinv, MulAut.mul_apply]
  have hρY : ∀ w ∈ Y, ρ w ∈ Y := fun w hw => by
    refine mem_commV_of_normalizes_ch615 (fun x hx => ?_) hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hρσ]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers σ)) k
  obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hall
    apply hσ1
    ext v
    have h1 : σ v * v⁻¹ = 1 := by
      by_contra h
      exact hall ⟨_, Subgroup.subset_closure ⟨σ, Subgroup.mem_zpowers σ, v, rfl⟩, h⟩
    rw [MulAut.one_apply]
    exact mul_inv_eq_one.mp h1
  have hne1 : ∀ v, v ≠ 1 → σ v ≠ 1 := fun v hv h => hv (σ.injective (h.trans (map_one σ).symm))
  have hρy1 : ρ y ≠ 1 := fun h => hy1 (ρ.injective (h.trans (map_one ρ).symm))
  have key : ∀ w ∈ Y, w ≠ 1 → ρ w = w → ∀ w' ∈ Y, w' ≠ 1 → ρ w' = w' → w' = w := by
    intro w hw hw1 hρw w' hw' hw'1 hρw'
    rcases eq_of_mem_commV_ch615 hW h3 hcard hw hw1 hw' with h | h | h | h
    · exact absurd h hw'1
    · exact h
    · exfalso
      rw [h, hρv, hρw] at hρw'
      exact hw1 (hfix w hw (σ.injective hρw'))
    · exfalso
      rw [h, hρv, hρv, hρw, hσ3] at hρw'
      exact hw1 (hfix w hw (σ.injective hρw').symm)
  rcases eq_of_mem_commV_ch615 hW h3 hcard hyY hy1 (hρY y hyY) with h | h | h | h
  · exact absurd h hρy1
  · exact ⟨y, ⟨hyY, hy1, h⟩, fun w' hw' => key y hyY hy1 h w' hw'.1 hw'.2.1 hw'.2.2⟩
  · have hw : ρ (σ (σ y)) = σ (σ y) := by rw [hρv, hρv, h, hσ3]
    have hwY : σ (σ y) ∈ Y := hσY _ (hσY _ hyY)
    have hw1 : σ (σ y) ≠ 1 := hne1 _ (hne1 _ hy1)
    exact ⟨σ (σ y), ⟨hwY, hw1, hw⟩, fun w' hw' => key _ hwY hw1 hw w' hw'.1 hw'.2.1 hw'.2.2⟩
  · have hw : ρ (σ y) = σ y := by rw [hρv, h, hσ3]
    have hwY : σ y ∈ Y := hσY _ hyY
    have hw1 : σ y ≠ 1 := hne1 _ hy1
    exact ⟨σ y, ⟨hwY, hw1, hw⟩, fun w' hw' => key _ hwY hw1 hw w' hw'.1 hw'.2.1 hw'.2.2⟩

theorem fix_of_comm_ch615 [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {σ ρ τ : MulAut W}
    (h3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hcard : Nat.card (commV (Subgroup.zpowers σ)) ≤ 4)
    (hρσ : ρ * σ * ρ⁻¹ = σ⁻¹) (hτσ : τ * σ = σ * τ) (hτρ : τ * ρ = ρ * τ) {x : W}
    (hx : x ∈ commV (Subgroup.zpowers σ)) : τ x = x := by
  obtain ⟨w, ⟨hwY, hw1, hρw⟩, huniq⟩ := existsUnique_fix_ch615 hW h3 hσ1 hcard hρσ
  have hτv : ∀ v, τ (σ v) = σ (τ v) := fun v => by
    rw [← MulAut.mul_apply, hτσ, MulAut.mul_apply]
  have hτw : τ w = w := by
    refine huniq (τ w) ⟨mem_commV_of_comm_ch615 hτσ hwY,
      fun h => hw1 (τ.injective (h.trans (map_one τ).symm)), ?_⟩
    rw [← MulAut.mul_apply, ← hτρ, MulAut.mul_apply, hρw]
  rcases eq_of_mem_commV_ch615 hW h3 hcard hwY hw1 hx with rfl | rfl | rfl | rfl
  · exact map_one τ
  · exact hτw
  · rw [hτv, hτw]
  · rw [hτv, hτv, hτw]

theorem eq_of_pow_three_map_ch615 {P : Type*} [Group P] (φ : SL22 →* P) {u : SL22}
    (hu : u ^ 3 = 1) : φ u = 1 ∨ φ u = φ g3_615 ∨ φ u = (φ g3_615)⁻¹ := by
  rcases eq_of_pow_three_sl22 u g3_615 hu g3_615_pow_three g3_615_ne_one with rfl | rfl | rfl
  · exact Or.inl (map_one φ)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (map_inv φ _))

theorem eq_one_of_fix_ch615 (hW : ∀ w : W, w ^ 2 = 1) {σ τ : MulAut W} (h3 : σ ^ 3 = 1)
    (hτ : τ = 1 ∨ τ = σ ∨ τ = σ⁻¹) {w : W} (hw : w ∈ commV (Subgroup.zpowers σ)) (hw1 : w ≠ 1)
    (hτw : τ w = w) : τ = 1 := by
  have hfix : σ w = w → w = 1 := fun hσw =>
    (Subgroup.mem_bot).mp ((commV_inf_fixV_ch615 hW h3).le
      ⟨hw, mem_fixV_zpowers_iff_ch615.mpr hσw⟩)
  rcases hτ with rfl | rfl | rfl
  · rfl
  · exact absurd (hfix hτw) hw1
  · refine absurd (hfix ?_) hw1
    calc σ w = σ (σ⁻¹ w) := by rw [hτw]
      _ = w := MulAut.apply_inv_self _ _ _

theorem existsUnique_one_ch615 [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {ψ₁ : SL22 →* MulAut W}
    (hψ₁ : Function.Injective ψ₁) {A B : Subgroup (MulAut W)}
    (hA : ∀ τ ∈ A, ∃ u : SL22, u ^ 3 = 1 ∧ τ = ψ₁ u) (hgA : ψ₁ g3_615 ∈ A) {r : SL22}
    (hr1 : r ≠ 1) (hr2 : r ^ 2 = 1) (hB : ∀ β ∈ B, β = 1 ∨ β = ψ₁ r) (hrB : ψ₁ r ∈ B)
    (hcard : Nat.card (commV (Subgroup.zpowers (ψ₁ g3_615))) ≤ 4) :
    ∃! w, w ∈ commV A ∧ w ∈ fixV B ∧ w ≠ 1 ∧
      ∀ τ ∈ A, τ w = w → ∀ w' ∈ commV A, τ w' = w' := by
  have h3 : ψ₁ g3_615 ^ 3 = 1 := by rw [← map_pow, g3_615_pow_three, map_one]
  have hσ1 : ψ₁ g3_615 ≠ 1 := fun h => g3_615_ne_one (hψ₁ (h.trans (map_one ψ₁).symm))
  have hρσ : ψ₁ r * ψ₁ g3_615 * (ψ₁ r)⁻¹ = (ψ₁ g3_615)⁻¹ := by
    rw [← map_inv ψ₁ r, ← map_mul, ← map_mul,
      inv_conj_sl22 r g3_615 hr1 hr2 g3_615_ne_one g3_615_pow_three, map_inv]
  have hAσ : ∀ τ ∈ A, τ = 1 ∨ τ = ψ₁ g3_615 ∨ τ = (ψ₁ g3_615)⁻¹ := by
    intro τ hτ
    obtain ⟨u, hu3, rfl⟩ := hA τ hτ
    exact eq_of_pow_three_map_ch615 ψ₁ hu3
  have hAeq : commV A = commV (Subgroup.zpowers (ψ₁ g3_615)) := by
    apply le_antisymm
    · refine Subgroup.closure_mono ?_
      rintro _ ⟨τ, hτ, v, rfl⟩
      refine ⟨τ, ?_, v, rfl⟩
      rcases hAσ τ hτ with rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
      · exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    · refine Subgroup.closure_mono ?_
      rintro _ ⟨x, hx, v, rfl⟩
      exact ⟨x, (Subgroup.zpowers_le.mpr hgA) hx, v, rfl⟩
  rw [hAeq]
  obtain ⟨w, ⟨hwY, hw1, hρw⟩, huniq⟩ := existsUnique_fix_ch615 hW h3 hσ1 hcard hρσ
  refine ⟨w, ⟨hwY, fun β hβ => ?_, hw1, fun τ hτ hτw w' _ => ?_⟩, ?_⟩
  · rcases hB β hβ with rfl | rfl
    · rfl
    · exact hρw
  · rw [eq_one_of_fix_ch615 hW h3 (hAσ τ hτ) hwY hw1 hτw]
    rfl
  · rintro w' ⟨hw'Y, hw'B, hw'1, -⟩
    exact huniq w' ⟨hw'Y, hw'1, hw'B _ hrB⟩

theorem existsUnique_two_ch615 [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {ψ : SL22 × SL22 →* MulAut W} (hψ : Function.Injective ψ) {A B : Subgroup (MulAut W)}
    (hA : ∀ τ ∈ A, ∃ u v : SL22, u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ τ = ψ (u, v))
    (hgA₁ : ψ (g3_615, 1) ∈ A) (hgA₂ : ψ (1, g3_615) ∈ A) {r₁ r₂ : SL22} (hr₁1 : r₁ ≠ 1)
    (hr₁2 : r₁ ^ 2 = 1) (hr₂1 : r₂ ≠ 1) (hr₂2 : r₂ ^ 2 = 1)
    (hB : ∀ β ∈ B, β = 1 ∨ β = ψ (r₁, 1) ∨ β = ψ (1, r₂) ∨ β = ψ (r₁, r₂))
    (hB₁ : ψ (r₁, 1) ∈ B) (hB₂ : ψ (1, r₂) ∈ B)
    (hcard₁ : Nat.card (commV (Subgroup.zpowers (ψ (g3_615, 1)))) ≤ 4)
    (hcard₂ : Nat.card (commV (Subgroup.zpowers (ψ (1, g3_615)))) ≤ 4) :
    ∃! w, w ∈ commV A ∧ w ∈ fixV B ∧ w ≠ 1 ∧
      ∀ τ ∈ A, τ w = w → ∀ w' ∈ commV A, τ w' = w' := by
  set ψ₁ : SL22 →* MulAut W := ψ.comp (MonoidHom.inl SL22 SL22) with hψ₁
  set ψ₂ : SL22 →* MulAut W := ψ.comp (MonoidHom.inr SL22 SL22) with hψ₂
  have hψ₁a : ∀ u, ψ₁ u = ψ (u, 1) := fun u => rfl
  have hψ₂a : ∀ v, ψ₂ v = ψ (1, v) := fun v => rfl
  have hψuv : ∀ u v, ψ (u, v) = ψ₁ u * ψ₂ v := fun u v => by
    rw [hψ₁a, hψ₂a, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hc : ∀ u v, ψ₁ u * ψ₂ v = ψ₂ v * ψ₁ u := fun u v => by
    rw [hψ₁a, hψ₂a, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one, one_mul,
      mul_one, one_mul]
  have hinj₁ : Function.Injective ψ₁ := fun a b h => by
    have := hψ h
    simpa using congrArg Prod.fst this
  have hinj₂ : Function.Injective ψ₂ := fun a b h => by
    have := hψ h
    simpa using congrArg Prod.snd this
  have hdata : ∀ (φ : SL22 →* MulAut W), Function.Injective φ → ∀ r : SL22, r ≠ 1 →
      r ^ 2 = 1 → φ g3_615 ^ 3 = 1 ∧ φ g3_615 ≠ 1 ∧
        φ r * φ g3_615 * (φ r)⁻¹ = (φ g3_615)⁻¹ := by
    intro φ hφ r hr1 hr2
    refine ⟨by rw [← map_pow, g3_615_pow_three, map_one],
      fun h => g3_615_ne_one (hφ (h.trans (map_one φ).symm)), ?_⟩
    rw [← map_inv φ r, ← map_mul, ← map_mul,
      inv_conj_sl22 r g3_615 hr1 hr2 g3_615_ne_one g3_615_pow_three, map_inv]
  obtain ⟨h3₁, hσ1₁, hρσ₁⟩ := hdata ψ₁ hinj₁ r₁ hr₁1 hr₁2
  obtain ⟨h3₂, hσ1₂, hρσ₂⟩ := hdata ψ₂ hinj₂ r₂ hr₂1 hr₂2
  set Y₁ := commV (Subgroup.zpowers (ψ₁ g3_615)) with hY₁
  set Y₂ := commV (Subgroup.zpowers (ψ₂ g3_615)) with hY₂
  have hcard₁' : Nat.card Y₁ ≤ 4 := hcard₁
  have hcard₂' : Nat.card Y₂ ≤ 4 := hcard₂
  have hτ₂Y₁ : ∀ v, ∀ x ∈ Y₁, ψ₂ v x = x := fun v x hx =>
    fix_of_comm_ch615 hW h3₁ hσ1₁ hcard₁' hρσ₁ (hc g3_615 v).symm (hc r₁ v).symm hx
  have hτ₁Y₂ : ∀ u, ∀ x ∈ Y₂, ψ₁ u x = x := fun u x hx =>
    fix_of_comm_ch615 hW h3₂ hσ1₂ hcard₂' hρσ₂ (hc u g3_615) (hc u r₂) hx
  have hfix₁ : ∀ y ∈ Y₁, ψ₁ g3_615 y = y → y = 1 := fun y hy h =>
    (Subgroup.mem_bot).mp ((commV_inf_fixV_ch615 hW h3₁).le
      ⟨hy, mem_fixV_zpowers_iff_ch615.mpr h⟩)
  have hfix₂ : ∀ y ∈ Y₂, ψ₂ g3_615 y = y → y = 1 := fun y hy h =>
    (Subgroup.mem_bot).mp ((commV_inf_fixV_ch615 hW h3₂).le
      ⟨hy, mem_fixV_zpowers_iff_ch615.mpr h⟩)
  have hY12 : ∀ y ∈ Y₁, y ∈ Y₂ → y = 1 := fun y hy₁ hy₂ => hfix₂ y hy₂ (hτ₂Y₁ _ y hy₁)
  have hdec : ∀ a₁ ∈ Y₁, ∀ b₁ ∈ Y₂, ∀ a₂ ∈ Y₁, ∀ b₂ ∈ Y₂, a₁ * b₁ = a₂ * b₂ →
      a₁ = a₂ ∧ b₁ = b₂ := by
    intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ h
    have e : a₁ / a₂ = b₂ / b₁ := div_eq_div_iff_mul_eq_mul.mpr (by rw [h, mul_comm])
    have h1 : a₁ / a₂ = 1 := hY12 _ (Subgroup.div_mem _ ha₁ ha₂) (e ▸ Subgroup.div_mem _ hb₂ hb₁)
    have ha : a₁ = a₂ := div_eq_one.mp h1
    refine ⟨ha, ?_⟩
    rw [ha] at h
    exact mul_left_cancel h
  have hpow : ∀ (φ : SL22 →* MulAut W) (u : SL22), u ^ 3 = 1 →
      φ u ∈ Subgroup.zpowers (φ g3_615) := by
    intro φ u hu
    rcases eq_of_pow_three_map_ch615 φ hu with h | h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
    · exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  have hpres : ∀ (φ : SL22 →* MulAut W) (u : SL22), u ^ 3 = 1 → ∀ x ∈
      commV (Subgroup.zpowers (φ g3_615)), φ u x ∈ commV (Subgroup.zpowers (φ g3_615)) := by
    intro φ u hu x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hpow φ u hu)
    refine mem_commV_of_comm_ch615 ?_ hx
    rw [← hk]
    exact (Commute.zpow_left (Commute.refl _) k).eq
  have hAeq : commV A = Y₁ ⊔ Y₂ := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨τ, hτ, w, rfl⟩
      obtain ⟨u, v, hu, hv, rfl⟩ := hA τ hτ
      have e : ψ (u, v) w * w⁻¹ = (ψ₁ u (ψ₂ v w) * (ψ₂ v w)⁻¹) * (ψ₂ v w * w⁻¹) := by
        rw [hψuv, MulAut.mul_apply, mul_assoc (ψ₁ u (ψ₂ v w)), inv_mul_cancel_left]
      rw [SetLike.mem_coe, e]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, hpow ψ₁ u hu, _, rfl⟩))
        (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, hpow ψ₂ v hv, _, rfl⟩))
    · refine sup_le (Subgroup.closure_mono ?_) (Subgroup.closure_mono ?_)
      · rintro _ ⟨x, hx, v, rfl⟩
        exact ⟨x, (Subgroup.zpowers_le.mpr hgA₁) hx, v, rfl⟩
      · rintro _ ⟨x, hx, v, rfl⟩
        exact ⟨x, (Subgroup.zpowers_le.mpr hgA₂) hx, v, rfl⟩
  have hact : ∀ u v, u ^ 3 = 1 → v ^ 3 = 1 → ∀ a ∈ Y₁, ∀ b ∈ Y₂,
      ψ (u, v) (a * b) = ψ₁ u a * ψ₂ v b := by
    intro u v hu hv a ha b hb
    rw [hψuv, MulAut.mul_apply, map_mul, hτ₂Y₁ v a ha, map_mul,
      hτ₁Y₂ u _ (hpres ψ₂ v hv b hb)]
  obtain ⟨y₁, ⟨hy₁Y, hy₁1, hρy₁⟩, huniq₁⟩ := existsUnique_fix_ch615 hW h3₁ hσ1₁ hcard₁' hρσ₁
  obtain ⟨y₂, ⟨hy₂Y, hy₂1, hρy₂⟩, huniq₂⟩ := existsUnique_fix_ch615 hW h3₂ hσ1₂ hcard₂' hρσ₂
  have hρ₁ : ∀ a ∈ Y₁, ψ₁ r₁ a ∈ Y₁ := fun a ha => by
    refine mem_commV_of_normalizes_ch615 (fun x hx => ?_) ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hρσ₁]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) k
  have hρ₂ : ∀ b ∈ Y₂, ψ₂ r₂ b ∈ Y₂ := fun b hb => by
    refine mem_commV_of_normalizes_ch615 (fun x hx => ?_) hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hρσ₂]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) k
  refine ⟨y₁ * y₂, ⟨?_, fun β hβ => ?_, ?_, fun τ hτ hτw w' _ => ?_⟩, ?_⟩
  · rw [hAeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy₁Y) (Subgroup.mem_sup_right hy₂Y)
  · rcases hB β hβ with rfl | rfl | rfl | rfl
    · rfl
    · rw [← hψ₁a, map_mul, hρy₁, hτ₁Y₂ r₁ y₂ hy₂Y]
    · rw [← hψ₂a, map_mul, hτ₂Y₁ r₂ y₁ hy₁Y, hρy₂]
    · rw [hψuv, MulAut.mul_apply, map_mul (ψ₂ r₂), hτ₂Y₁ r₂ y₁ hy₁Y, hρy₂, map_mul, hρy₁,
        hτ₁Y₂ r₁ y₂ hy₂Y]
  · intro h
    have e : y₁ = y₂⁻¹ := eq_inv_of_mul_eq_one_left h
    exact hy₁1 (hY12 y₁ hy₁Y (e ▸ Subgroup.inv_mem _ hy₂Y))
  · obtain ⟨u, v, hu, hv, rfl⟩ := hA τ hτ
    rw [hact u v hu hv y₁ hy₁Y y₂ hy₂Y] at hτw
    obtain ⟨h1, h2⟩ := hdec _ (hpres ψ₁ u hu y₁ hy₁Y) _ (hpres ψ₂ v hv y₂ hy₂Y) _ hy₁Y _ hy₂Y hτw
    have e1 := eq_one_of_fix_ch615 hW h3₁ (eq_of_pow_three_map_ch615 ψ₁ hu) hy₁Y hy₁1 h1
    have e2 := eq_one_of_fix_ch615 hW h3₂ (eq_of_pow_three_map_ch615 ψ₂ hv) hy₂Y hy₂1 h2
    rw [hψuv, e1, e2, mul_one]
    rfl
  · rintro w ⟨hwA, hwB, hw1, hstab⟩
    rw [hAeq] at hwA
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hwA
    have hρa : ψ₁ r₁ a = a := by
      have h1 := hwB _ hB₁
      rw [← hψ₁a, map_mul, hτ₁Y₂ r₁ b hb] at h1
      exact mul_right_cancel h1
    have hρb : ψ₂ r₂ b = b := by
      have h1 := hwB _ hB₂
      rw [← hψ₂a, map_mul, hτ₂Y₁ r₂ a ha] at h1
      exact mul_left_cancel h1
    have ha' : a = 1 ∨ a = y₁ := by
      by_cases ha1 : a = 1
      · exact Or.inl ha1
      · exact Or.inr (huniq₁ a ⟨ha, ha1, hρa⟩)
    have hb' : b = 1 ∨ b = y₂ := by
      by_cases hb1 : b = 1
      · exact Or.inl hb1
      · exact Or.inr (huniq₂ b ⟨hb, hb1, hρb⟩)
    have hy₁A : y₁ ∈ commV A := by rw [hAeq]; exact Subgroup.mem_sup_left hy₁Y
    have hy₂A : y₂ ∈ commV A := by rw [hAeq]; exact Subgroup.mem_sup_right hy₂Y
    rcases ha' with ha1 | ha1 <;> rcases hb' with hb1 | hb1
    · exact absurd (by rw [ha1, hb1, mul_one]) hw1
    · exfalso
      have h1 : ψ₁ g3_615 (a * b) = a * b := by rw [ha1, hb1, one_mul, hτ₁Y₂ _ y₂ hy₂Y]
      exact hy₁1 (hfix₁ y₁ hy₁Y (hstab _ hgA₁ h1 y₁ hy₁A))
    · exfalso
      have h1 : ψ₂ g3_615 (a * b) = a * b := by rw [ha1, hb1, mul_one, hτ₂Y₁ _ y₁ hy₁Y]
      exact hy₂1 (hfix₂ y₂ hy₂Y (hstab _ hgA₂ h1 y₂ hy₂A))
    · rw [ha1, hb1]

theorem card_commV_le_ch615 [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {C : Subgroup W} (h : E2.IsL2Natural L C 1) {σ : MulAut W} (hσL : σ ∈ L) (h3 : σ ^ 3 = 1)
    (hC : C ≤ fixV (Subgroup.zpowers σ)) :
    Nat.card (commV (Subgroup.zpowers σ)) ≤ 4 := by
  obtain ⟨-, F, _, _, hF, -, β, -, hβk, -⟩ := h
  have hle : commV (Subgroup.zpowers σ) ≤ commV L :=
    Subgroup.closure_mono fun _ ⟨x, hx, v, hv⟩ =>
      ⟨x, (Subgroup.zpowers_le.mpr hσL) hx, v, hv⟩
  let f : ↥(commV (Subgroup.zpowers σ)) → Multiplicative (Fin 2 → F) :=
    fun y => β ⟨y, hle y.2⟩
  have hf : Function.Injective f := by
    intro y y' hyy
    have hk : (⟨y, hle y.2⟩ : ↥(commV L)) * (⟨y', hle y'.2⟩)⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      exact mul_inv_eq_one.mpr hyy
    rw [hβk, Subgroup.mem_subgroupOf] at hk
    have hyC : (y : W) * (y' : W)⁻¹ ∈ C := hk.2
    have hyY : (y : W) * (y' : W)⁻¹ ∈ commV (Subgroup.zpowers σ) :=
      Subgroup.mul_mem _ y.2 (Subgroup.inv_mem _ y'.2)
    have h0 := (commV_inf_fixV_ch615 hW h3).le ⟨hyY, hC hyC⟩
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h0
    exact Subtype.ext h0
  have hcard : Nat.card (Multiplicative (Fin 2 → F)) = 4 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun,
      Fintype.card_fin, hF]
    norm_num
  calc Nat.card (commV (Subgroup.zpowers σ)) ≤ Nat.card (Multiplicative (Fin 2 → F)) :=
        Nat.card_le_card_of_injective f hf
    _ = 4 := hcard


end ModD2

end CFSG.Quasithin.H13
