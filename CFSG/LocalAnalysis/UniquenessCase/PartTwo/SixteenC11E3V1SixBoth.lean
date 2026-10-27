module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixSwapB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W W' : Type} [CommGroup W] [Finite W] [CommGroup W'] [Finite W']
  {M L : Subgroup (MulAut W)} {L' : Subgroup (MulAut W')} {κ : W →* W'} {e : ↥L' →* ↥L}

private theorem s1611e3_commSub_sup_left {V : Type} [CommGroup V] (A B : Subgroup V)
    (X : Subgroup (MulAut V)) :
    commSub (A ⊔ B) X = commSub A X ⊔ commSub B X := by
  refine le_antisymm ?_
    (sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl))
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hw
  have hxy : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
    rw [map_mul, mul_inv_rev]
    ac_rfl
  rw [hxy]
  exact Subgroup.mem_sup.mpr ⟨x a * a⁻¹, Subgroup.subset_closure ⟨x, hx, a, ha, rfl⟩,
    x b * b⁻¹, Subgroup.subset_closure ⟨x, hx, b, hb, rfl⟩, rfl⟩

private theorem s1611e3_fixV_map (h : SixHyp M L L' κ e) {n : MulAut W} (hn : n ∈ M)
    {w : W} (hw : w ∈ fixV L) : n w ∈ fixV L := by
  rw [mem_fixV] at hw ⊢
  intro ℓ hℓ
  have hℓmem : n⁻¹ * ℓ * n ∈ L := by
    have := h.normalizes n⁻¹ (M.inv_mem hn) ℓ hℓ
    simpa using this
  have h1 : (n⁻¹ * ℓ * n) w = w := hw _ hℓmem
  calc ℓ (n w) = n ((n⁻¹ * ℓ * n) w) := by
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    _ = n w := by rw [h1]

theorem s1611e3_six_both
    (h : SixHyp M L L' κ e) :
    ∃ (I₁ I₂ : Subgroup W') (W₁ W₂ : Subgroup W)
      (h₁ : ∀ ℓ ∈ L, ∀ w ∈ W₁, (ℓ : MulAut W) w ∈ W₁)
      (h₂ : ∀ ℓ ∈ L, ∀ w ∈ W₂, (ℓ : MulAut W) w ∈ W₂),
      I₁ ⊓ I₂ = ⊥ ∧ I₁ ⊔ I₂ = ⊤ ∧ AlternatingNatural L' I₁ ⊥ 6 ∧ AlternatingNatural L' I₂ ⊥ 6 ∧
      (∀ ψ ∈ Subgroup.centralizer (L' : Set (MulAut W')), I₁.map ψ.toMonoidHom ≠ I₂) ∧
      W₁ ⊔ W₂ = ⊤ ∧ (∀ w ∈ W₁, κ w ∈ I₁) ∧ (∀ w ∈ W₂, κ w ∈ I₂) ∧
      (∀ i ∈ I₁, ∃ w ∈ W₁, κ w = i) ∧ (∀ i ∈ I₂, ∃ w ∈ W₂, κ w = i) ∧
      Nat.card ↥(W₁ ⊓ κ.ker) = 2 ∧ Nat.card ↥(W₂ ⊓ κ.ker) = 2 ∧
      κ.ker = (W₁ ⊓ κ.ker) ⊔ (W₂ ⊓ κ.ker) ∧
      FFModel.Realizes (CFSG.Quasithin.H13.altCoreModel 6)
        (CFSG.Quasithin.H13.VolI.resHom L W₁ h₁).range ⊤ ⊥ ∧
      FFModel.Realizes (CFSG.Quasithin.H13.altCoreModel 6)
        (CFSG.Quasithin.H13.VolI.resHom L W₂ h₂).range ⊤ ⊥ := by
  classical
  obtain ⟨I₁, I₂, -, -, hI₁Z, hI₂Z, hU, hAN₁, hAN₂, hne⟩ := h.sum
  rw [bot_sup_eq] at hI₁Z hI₂Z hU
  have hinf : I₁ ⊓ I₂ = ⊥ := le_bot_iff.1 hI₁Z
  have hsup : I₁ ⊔ I₂ = ⊤ := hU
  obtain ⟨W₁, hW₁, hW₁eq, honto₁, hinto₁, hdich₁⟩ := s1611e3_six_cover h hAN₁
  obtain ⟨W₂, hW₂, hW₂eq, honto₂, hinto₂, hdich₂⟩ := s1611e3_six_cover h hAN₂
  have hUt : I₁.comap κ ⊔ I₂.comap κ = ⊤ := by
    rw [Subgroup.comap_sup_eq (f := κ) I₁ I₂ h.surj, hsup, Subgroup.comap_top]
  have hWsup : W₁ ⊔ W₂ = ⊤ := by
    rw [hW₁eq, hW₂eq, ← s1611e3_commSub_sup_left (I₁.comap κ) (I₂.comap κ) L, hUt,
      ← commV_eq_commSub, h.comm]
  have hker : κ.ker = (W₁ ⊓ κ.ker) ⊔ (W₂ ⊓ κ.ker) := by
    refine le_antisymm ?_ (sup_le inf_le_right inf_le_right)
    intro k hk
    have hkw : k ∈ W₁ ⊔ W₂ := by rw [hWsup]; trivial
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.1 hkw
    have hκ : κ w₁ * κ w₂ = 1 := by simpa only [map_mul] using MonoidHom.mem_ker.mp hk
    have h1 : κ w₁ = 1 := by
      have hmem : κ w₁ ∈ I₁ ⊓ I₂ :=
        ⟨hinto₁ w₁ hw₁, by
          rw [mul_eq_one_iff_eq_inv.mp hκ]
          exact I₂.inv_mem (hinto₂ w₂ hw₂)⟩
      rwa [hinf, Subgroup.mem_bot] at hmem
    have h2 : κ w₂ = 1 := by
      rw [h1, one_mul] at hκ
      exact hκ
    exact Subgroup.mem_sup.mpr ⟨w₁, ⟨hw₁, MonoidHom.mem_ker.mpr h1⟩,
      w₂, ⟨hw₂, MonoidHom.mem_ker.mpr h2⟩, rfl⟩
  have hZne : W₁ ⊓ κ.ker ≠ ⊥ ∨ W₂ ⊓ κ.ker ≠ ⊥ := by
    by_contra hc
    obtain ⟨h1, h2⟩ := not_or.mp hc
    exact h.ne (by rw [hker, not_not.mp h1, not_not.mp h2, bot_sup_eq])
  obtain ⟨m, hmM, hm⟩ := s1611e3_six_swap h hinf hsup hAN₁ hAN₂ hne
  have hne' : ∀ ψ ∈ Subgroup.centralizer (L' : Set (MulAut W')), I₂.map ψ.toMonoidHom ≠ I₁ := by
    intro ψ hψ hmap
    have hψinv : ψ⁻¹ ∈ Subgroup.centralizer (L' : Set (MulAut W')) :=
      (Subgroup.centralizer (L' : Set (MulAut W'))).inv_mem hψ
    have h2 : I₁.map (ψ⁻¹).toMonoidHom = I₂ := by
      have h3 : (I₂.map ψ.toMonoidHom).map (ψ⁻¹).toMonoidHom = I₁.map (ψ⁻¹).toMonoidHom := by
        rw [hmap]
      rw [Subgroup.map_map] at h3
      have hcomp : (ψ⁻¹).toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id W' := by
        ext x; simp
      rw [hcomp, Subgroup.map_id] at h3
      exact h3.symm
    exact hne ψ⁻¹ hψinv h2
  obtain ⟨m', hm'M, hm'⟩ :=
    s1611e3_six_swap h (by rw [inf_comm]; exact hinf) (by rw [sup_comm]; exact hsup)
      hAN₂ hAN₁ hne'
  have hmW : W₁.map m.toMonoidHom ≤ W₂ := by
    rw [hW₁eq, hW₂eq, ← s15_Core_commSub_map_conj (I₁.comap κ) L m]
    refine commSub_mono ?_ ?_
    · rintro x ⟨w, hw, rfl⟩
      exact hm w hw
    · rintro x ⟨l, hl, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h.normalizes m hmM l hl
  have hmker_le : κ.ker.map m.toMonoidHom ≤ κ.ker := by
    rintro _ ⟨w, hw, rfl⟩
    rw [SixHyp.ker_eq h] at hw ⊢
    exact s1611e3_fixV_map h hmM hw
  have hmZ : (W₁ ⊓ κ.ker).map m.toMonoidHom ≤ W₂ ⊓ κ.ker := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hmW (Subgroup.mem_map.mpr ⟨w, hw.1, rfl⟩),
      hmker_le (Subgroup.mem_map.mpr ⟨w, hw.2, rfl⟩)⟩
  have hcardZ₁ : Nat.card ↥(W₁ ⊓ κ.ker) ≤ Nat.card ↥(W₂ ⊓ κ.ker) := by
    have h1 : Nat.card ↥((W₁ ⊓ κ.ker).map m.toMonoidHom) = Nat.card ↥(W₁ ⊓ κ.ker) :=
      Subgroup.card_map_of_injective (K := W₁ ⊓ κ.ker) (f := m.toMonoidHom) m.injective
    rw [← h1]
    exact Subgroup.card_le_of_le hmZ
  have hm'W : W₂.map m'.toMonoidHom ≤ W₁ := by
    rw [hW₂eq, hW₁eq, ← s15_Core_commSub_map_conj (I₂.comap κ) L m']
    refine commSub_mono ?_ ?_
    · rintro x ⟨w, hw, rfl⟩
      exact hm' w hw
    · rintro x ⟨l, hl, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h.normalizes m' hm'M l hl
  have hm'ker_le : κ.ker.map m'.toMonoidHom ≤ κ.ker := by
    rintro _ ⟨w, hw, rfl⟩
    rw [SixHyp.ker_eq h] at hw ⊢
    exact s1611e3_fixV_map h hm'M hw
  have hm'Z : (W₂ ⊓ κ.ker).map m'.toMonoidHom ≤ W₁ ⊓ κ.ker := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hm'W (Subgroup.mem_map.mpr ⟨w, hw.1, rfl⟩),
      hm'ker_le (Subgroup.mem_map.mpr ⟨w, hw.2, rfl⟩)⟩
  have hcardZ₂ : Nat.card ↥(W₂ ⊓ κ.ker) ≤ Nat.card ↥(W₁ ⊓ κ.ker) := by
    have h1 : Nat.card ↥((W₂ ⊓ κ.ker).map m'.toMonoidHom) = Nat.card ↥(W₂ ⊓ κ.ker) :=
      Subgroup.card_map_of_injective (K := W₂ ⊓ κ.ker) (f := m'.toMonoidHom) m'.injective
    rw [← h1]
    exact Subgroup.card_le_of_le hm'Z
  have hcardZ : Nat.card ↥(W₁ ⊓ κ.ker) = Nat.card ↥(W₂ ⊓ κ.ker) :=
    le_antisymm hcardZ₁ hcardZ₂
  have hZ₁ne : W₁ ⊓ κ.ker ≠ ⊥ := by
    intro h1
    rcases hZne with h2 | h2
    · exact h2 h1
    · exact h2 (by rw [Subgroup.eq_bot_iff_card, ← hcardZ, h1, Subgroup.card_bot])
  have hZ₂ne : W₂ ⊓ κ.ker ≠ ⊥ := by
    intro h2
    rcases hZne with h1 | h1
    · exact h1 (by rw [Subgroup.eq_bot_iff_card, hcardZ, h2, Subgroup.card_bot])
    · exact h1 h2
  have hd₁ : Nat.card ↥(W₁ ⊓ κ.ker) = 2 ∧
      FFModel.Realizes (CFSG.Quasithin.H13.altCoreModel 6)
        (CFSG.Quasithin.H13.VolI.resHom L W₁ hW₁).range ⊤ ⊥ := by
    rcases hdich₁ with hb | hr
    · exact absurd hb hZ₁ne
    · exact ⟨hr.1, hr.2.2⟩
  have hd₂ : Nat.card ↥(W₂ ⊓ κ.ker) = 2 ∧
      FFModel.Realizes (CFSG.Quasithin.H13.altCoreModel 6)
        (CFSG.Quasithin.H13.VolI.resHom L W₂ hW₂).range ⊤ ⊥ := by
    rcases hdich₂ with hb | hr
    · exact absurd hb hZ₂ne
    · exact ⟨hr.1, hr.2.2⟩
  exact ⟨I₁, I₂, W₁, W₂, hW₁, hW₂, hinf, hsup, hAN₁, hAN₂, hne, hWsup, hinto₁, hinto₂,
    honto₁, honto₂, hd₁.1, hd₂.1, hker, hd₁.2, hd₂.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
