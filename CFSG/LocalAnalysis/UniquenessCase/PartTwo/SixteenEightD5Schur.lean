module

public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private lemma s16e_d5_pow_apply_pow {W : Type} [Group W] (ξ : MulAut W) (a b : ℕ) (z : W) :
    (ξ ^ a) ((ξ ^ b) z) = (ξ ^ b) ((ξ ^ a) z) := by
  calc (ξ ^ a) ((ξ ^ b) z) = (ξ ^ (a + b)) z := by rw [← MulAut.mul_apply, pow_add]
    _ = (ξ ^ (b + a)) z := by rw [Nat.add_comm a b]
    _ = (ξ ^ b) ((ξ ^ a) z) := by rw [pow_add, MulAut.mul_apply]

private lemma s16e_d5_pow_three_apply {W : Type} [Group W] {ξ : MulAut W} (hξ : ξ ^ 3 = 1)
    (z : W) : ξ (ξ (ξ z)) = z := by
  have h : (ξ ^ 3) z = ξ (ξ (ξ z)) := by simp [pow_succ, MulAut.mul_apply, pow_two]
  rw [← h, hξ, MulAut.one_apply]

theorem s16e_d5_pow_fix {W : Type} [CommGroup W] {ξ : MulAut W} (hξ : ξ ^ 3 = 1)
    {Z : Subgroup W} (hfix : ∀ z ∈ Z, ξ z = z → z = 1) {e : ℕ} (he0 : 0 < e) (he : e < 3) :
    ∀ z ∈ Z, (ξ ^ e) z = z → z = 1 := by
  have he12 : e = 1 ∨ e = 2 := by omega
  rcases he12 with rfl | rfl
  · intro z hz hze
    exact hfix z hz (by simpa [pow_one] using hze)
  · intro z hz hze
    apply hfix z hz
    have h1 : ξ z = ξ ((ξ ^ 2) z) := by rw [hze]
    rw [show (ξ ^ 2) z = ξ (ξ z) by rw [pow_two, MulAut.mul_apply]] at h1
    exact h1.trans (s16e_d5_pow_three_apply hξ z)

theorem s16e_d5_pow_eq_on {W : Type} [CommGroup W] {Z : Subgroup W} (hZ : Nat.card ↥Z = 4)
    {ξ : MulAut W} (hξ : ξ ^ 3 = 1) (hfix : ∀ z ∈ Z, ξ z = z → z = 1) {e e' : ℕ} (he : e < 3)
    (he' : e' < 3) (h : ∀ z ∈ Z, (ξ ^ e) z = (ξ ^ e') z) : e = e' := by
  rcases le_total e e' with hle | hle
  · set d := e' - e with hd
    have he'e : e' = e + d := by omega
    have hd3 : d < 3 := by omega
    have hdz : ∀ z ∈ Z, (ξ ^ d) z = z := by
      intro z hz
      have hz' := h z hz
      rw [he'e, pow_add, MulAut.mul_apply] at hz'
      exact ((ξ ^ e).injective hz').symm
    have hd012 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hd012 with hd0 | hd1 | hd2
    · omega
    · exfalso
      have hbot : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr fun z hz =>
        s16e_d5_pow_fix hξ hfix (e := d) (by omega) hd3 z hz (hdz z hz)
      have hcard : Nat.card ↥Z = 1 := (Subgroup.eq_bot_iff_card Z).mp hbot
      omega
    · exfalso
      have hbot : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr fun z hz =>
        s16e_d5_pow_fix hξ hfix (e := d) (by omega) hd3 z hz (hdz z hz)
      have hcard : Nat.card ↥Z = 1 := (Subgroup.eq_bot_iff_card Z).mp hbot
      omega
  · set d := e - e' with hd
    have he'e : e = e' + d := by omega
    have hd3 : d < 3 := by omega
    have hdz : ∀ z ∈ Z, (ξ ^ d) z = z := by
      intro z hz
      have hz' := h z hz
      rw [he'e, pow_add, MulAut.mul_apply] at hz'
      exact (ξ ^ e').injective hz'
    have hd012 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hd012 with hd0 | hd1 | hd2
    · omega
    · exfalso
      have hbot : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr fun z hz =>
        s16e_d5_pow_fix hξ hfix (e := d) (by omega) hd3 z hz (hdz z hz)
      have hcard : Nat.card ↥Z = 1 := (Subgroup.eq_bot_iff_card Z).mp hbot
      omega
    · exfalso
      have hbot : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr fun z hz =>
        s16e_d5_pow_fix hξ hfix (e := d) (by omega) hd3 z hz (hdz z hz)
      have hcard : Nat.card ↥Z = 1 := (Subgroup.eq_bot_iff_card Z).mp hbot
      omega

private lemma s16e_d5_orbit_exhaust {W : Type} [CommGroup W] {Z : Subgroup W}
    (hZ : Nat.card ↥Z = 4) {ξ : MulAut W} (hξ : ξ ^ 3 = 1)
    (hξZ : ∀ z ∈ Z, ξ z ∈ Z) (hfix : ∀ z ∈ Z, ξ z = z → z = 1)
    {z₀ : W} (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1) :
    ∀ z ∈ Z, z = 1 ∨ z = z₀ ∨ z = ξ z₀ ∨ z = ξ (ξ z₀) := by
  have hz₁Z : ξ z₀ ∈ Z := hξZ z₀ hz₀
  have hz₂Z : ξ (ξ z₀) ∈ Z := hξZ (ξ z₀) hz₁Z
  have h1z₀ : (1 : W) ≠ z₀ := fun h => hz₀1 h.symm
  have h1z₁ : (1 : W) ≠ ξ z₀ := by
    intro h
    exact hz₀1 (ξ.injective (by rw [h.symm, map_one]))
  have h1z₂ : (1 : W) ≠ ξ (ξ z₀) := by
    intro h
    have h2 : ξ z₀ = 1 := ξ.injective (by rw [h.symm, map_one])
    exact hz₀1 (ξ.injective (by rw [h2, map_one]))
  have hz₀z₁ : z₀ ≠ ξ z₀ := fun h => hz₀1 (hfix z₀ hz₀ h.symm)
  have hz₀z₂ : z₀ ≠ ξ (ξ z₀) := by
    intro h
    have h3 : ξ (ξ (ξ z₀)) = ξ z₀ := (congrArg ξ h).symm
    rw [s16e_d5_pow_three_apply hξ z₀] at h3
    exact hz₀z₁ h3
  have hz₁z₂ : ξ z₀ ≠ ξ (ξ z₀) := fun h => hz₀z₁ (ξ.injective h)
  have hnot1 : (1 : W) ∉ ({z₀, ξ z₀, ξ (ξ z₀)} : Set W) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1z₀, h1z₁, h1z₂⟩
  have hnot2 : z₀ ∉ ({ξ z₀, ξ (ξ z₀)} : Set W) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hz₀z₁, hz₀z₂⟩
  have hnot3 : ξ z₀ ∉ ({ξ (ξ z₀)} : Set W) := by
    simpa using hz₁z₂
  have hS : ({1, z₀, ξ z₀, ξ (ξ z₀)} : Set W).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (s := ({z₀, ξ z₀, ξ (ξ z₀)} : Set W)) hnot1,
      Set.ncard_insert_of_notMem (s := ({ξ z₀, ξ (ξ z₀)} : Set W)) hnot2,
      Set.ncard_insert_of_notMem (s := ({ξ (ξ z₀)} : Set W)) hnot3, Set.ncard_singleton]
  have hZc : (Z : Set W).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hZ
  intro z hz
  by_contra hmem
  have hz4 : z ∉ ({1, z₀, ξ z₀, ξ (ξ z₀)} : Set W) := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hins : (insert z ({1, z₀, ξ z₀, ξ (ξ z₀)} : Set W)).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem hz4, hS]
  have hsub : insert z ({1, z₀, ξ z₀, ξ (ξ z₀)} : Set W) ⊆ (Z : Set W) := by
    intro x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with rfl | hx
    · exact hz
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Z.one_mem
      · exact hz₀
      · exact hz₁Z
      · exact hz₂Z
  haveI : Finite (Z : Set W) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_coe_set_eq, hZc]; decide)
  have hle := Set.ncard_le_ncard hsub
  rw [hins, hZc] at hle
  omega

theorem s16e_d5_schur_local {W : Type} [CommGroup W] {Z : Subgroup W} (hZ : Nat.card ↥Z = 4)
    {ξ g : MulAut W} (hξ : ξ ^ 3 = 1) (hξZ : ∀ z ∈ Z, ξ z ∈ Z)
    (hfix : ∀ z ∈ Z, ξ z = z → z = 1) (hgZ : ∀ z ∈ Z, g z ∈ Z)
    (hcomm : ∀ z ∈ Z, g (ξ z) = ξ (g z)) :
    ∃ e : ℕ, e < 3 ∧ ∀ z ∈ Z, g z = (ξ ^ e) z := by
  haveI : Finite ↥Z := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial ↥Z := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  obtain ⟨z0, hz0ne1⟩ := exists_ne (1 : ↥Z)
  have hz0Z : (z0 : W) ∈ Z := z0.2
  have hz01 : (z0 : W) ≠ 1 := fun h => hz0ne1 (Subtype.ext h)
  have hex := s16e_d5_orbit_exhaust hZ hξ hξZ hfix hz0Z hz01
  have hgz0Z : g (z0 : W) ∈ Z := hgZ _ hz0Z
  have hgne1 : g (z0 : W) ≠ 1 := by
    intro h
    exact hz01 (g.injective (by rw [h, map_one]))
  obtain ⟨e, he3, hee⟩ : ∃ e : ℕ, e < 3 ∧ g (z0 : W) = (ξ ^ e) (z0 : W) := by
    rcases hex (g (z0 : W)) hgz0Z with h | h | h | h
    · exact absurd h hgne1
    · exact ⟨0, by decide, by rw [h, pow_zero, MulAut.one_apply]⟩
    · exact ⟨1, by decide, by rw [h, pow_one]⟩
    · refine ⟨2, by decide, ?_⟩
      rw [h]
      exact (show (ξ ^ 2) (z0 : W) = ξ (ξ (z0 : W)) by
        rw [pow_two, MulAut.mul_apply]).symm
  refine ⟨e, he3, fun z hz => ?_⟩
  rcases hex z hz with h | h | h | h
  · simp [h]
  · rw [h, hee]
  · rw [h, hcomm (z0 : W) hz0Z, hee]
    exact (by simpa [pow_one] using (s16e_d5_pow_apply_pow ξ e 1 (z0 : W)).symm)
  · rw [h, hcomm (ξ (z0 : W)) (hξZ (z0 : W) hz0Z), hcomm (z0 : W) hz0Z, hee]
    have h2 : (ξ ^ e) (ξ (ξ (z0 : W))) = (ξ ^ 2) ((ξ ^ e) (z0 : W)) := by
      rw [show ξ (ξ (z0 : W)) = (ξ ^ 2) (z0 : W) by rw [pow_two, MulAut.mul_apply],
        s16e_d5_pow_apply_pow ξ e 2 (z0 : W)]
    rw [h2]
    conv_lhs => rw [← MulAut.mul_apply, ← pow_two]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
