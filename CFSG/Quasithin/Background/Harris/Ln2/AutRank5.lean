module

public import CFSG.Quasithin.Background.SmithB42LnL5Case11

public section

namespace CFSG.Quasithin.G11.Harris.Ln2

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis CFSG.Quasithin.B42Ln

local notation "𝕄" => Matrix (Fin 5) (Fin 5) (ZMod 2)

theorem center_G5_eq_bot : Subgroup.center G5 = ⊥ := by
  have hc : Nat.card (Subgroup.center G5) = 1 := by
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv]
    have hle := Subgroup.card_le_of_le (le_top : rootsOfUnity (max (Fintype.card (Fin 5)) 1)
      (ZMod 2) ≤ ⊤)
    have hu : Nat.card (ZMod 2)ˣ = 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      decide
    rw [Subgroup.card_top, hu] at hle
    exact le_antisymm hle Nat.card_pos
  exact Subgroup.eq_bot_of_card_eq _ hc

theorem conj_G5_injective : Function.Injective (MulAut.conj : G5 →* MulAut G5) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hmem : a ∈ Subgroup.center G5 := Subgroup.mem_center_iff.mpr fun g => by
    have h := DFunLike.congr_fun ha g
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * a = a * g * a⁻¹ * a := by rw [h]
      _ = a * g := by group
  rw [center_G5_eq_bot, Subgroup.mem_bot] at hmem
  exact hmem

noncomputable abbrev graphAut : MulAut G5 := invTransposeSL 5 (ZMod 2)

theorem aut5_inner_or_graph (τ : MulAut G5) :
    (∃ m : G5, τ = MulAut.conj m) ∨ (∃ m : G5, τ = MulAut.conj m * graphAut) := by
  obtain ⟨P, hP | hP⟩ := aut5_cases τ
  · refine Or.inl ⟨ofGL5 P, ?_⟩
    ext1 x
    apply Subtype.ext
    rw [hP, MulAut.conj_apply, ofGL5_inv]
    rfl
  · refine Or.inr ⟨ofGL5 P, ?_⟩
    ext1 x
    apply Subtype.ext
    rw [hP, MulAut.mul_apply, MulAut.conj_apply, ofGL5_inv]
    rfl

theorem conj_range_normal (G : Type*) [Group G] : (MulAut.conj : G →* MulAut G).range.Normal := by
  refine ⟨?_⟩
  rintro _ ⟨m, rfl⟩ τ
  refine ⟨τ m, ?_⟩
  ext1 x
  simp [MulAut.conj_apply]

theorem index_conj_range_le_two :
    (MulAut.conj : G5 →* MulAut G5).range.index ≠ 0 ∧ (MulAut.conj : G5 →* MulAut G5).range.index ≤ 2 := by
  have := conj_range_normal G5
  set N := (MulAut.conj : G5 →* MulAut G5).range with hN
  let f : Bool → MulAut G5 ⧸ N := fun b =>
    if b then (1 : MulAut G5 ⧸ N) else QuotientGroup.mk graphAut
  have hmk : ∀ m : G5, (QuotientGroup.mk (MulAut.conj m) : MulAut G5 ⧸ N) = 1 := fun m =>
    (QuotientGroup.eq_one_iff _).2 ⟨m, rfl⟩
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective q
    rcases aut5_inner_or_graph τ with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨true, by simp [f, hmk]⟩
    · exact ⟨false, by simp [f, QuotientGroup.mk_mul, hmk]⟩
  have : Finite (MulAut G5 ⧸ N) := Finite.of_surjective f hf
  refine ⟨?_, ?_⟩
  · rw [Subgroup.index]
    exact Nat.card_pos.ne'
  · have := Nat.card_le_card_of_surjective f hf
    simpa [Subgroup.index] using this

theorem card_le_128_of_elemAbelian_aut5 (B : Subgroup (MulAut G5))
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h2 : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 128 := by
  have := conj_range_normal G5
  set c : G5 →* MulAut G5 := MulAut.conj with hcdef
  set E : Subgroup G5 := B.comap c with hE
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    apply conj_G5_injective
    rw [map_mul, map_mul]
    exact hc _ ha _ hb
  have hE2 : ∀ a ∈ E, a * a = 1 := by
    intro a ha
    apply conj_G5_injective
    rw [map_mul, map_one]
    exact h2 _ ha
  have hE64 := card_le_of_elemAbelian hEc hE2
  have hmap : Nat.card (c.range ⊓ B : Subgroup (MulAut G5)) ≤ 64 := by
    rw [← Subgroup.map_comap_eq, Subgroup.card_map_of_injective conj_G5_injective]
    exact hE64
  obtain ⟨hne, hle⟩ := index_conj_range_le_two
  have hrel : c.range.relIndex B ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Subgroup.relIndex_dvd_index_of_normal _ _)).trans hle
  have hmul := Subgroup.relIndex_mul_card (H := c.range) (K := B)
  calc Nat.card B = c.range.relIndex B * Nat.card (c.range ⊓ B : Subgroup (MulAut G5)) :=
        hmul.symm
    _ ≤ 2 * 64 := Nat.mul_le_mul hrel hmap
    _ = 128 := by norm_num

end CFSG.Quasithin.G11.Harris.Ln2
