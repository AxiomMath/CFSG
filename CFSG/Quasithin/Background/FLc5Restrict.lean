module

public import CFSG.Quasithin.Background.FLc3Tr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open CFSG.Quasithin

section

variable {V W : Type} [CommGroup V] [CommGroup W]

@[expose] noncomputable def resAut (ι : W →* V) (hι : Function.Injective ι) (σ : MulAut V)
    (h : ∀ w, ∃ w', ι w' = σ (ι w)) (h' : ∀ w, ∃ w', ι w' = σ⁻¹ (ι w)) : MulAut W where
  toFun w := Classical.choose (h w)
  invFun w := Classical.choose (h' w)
  left_inv w := by
    apply hι
    show ι (Classical.choose (h' (Classical.choose (h w)))) = ι w
    have e1 := Classical.choose_spec (h' (Classical.choose (h w)))
    have e2 := Classical.choose_spec (h w)
    rw [e1, e2, MulAut.inv_apply_self]
  right_inv w := by
    apply hι
    show ι (Classical.choose (h (Classical.choose (h' w)))) = ι w
    have e1 := Classical.choose_spec (h (Classical.choose (h' w)))
    have e2 := Classical.choose_spec (h' w)
    rw [e1, e2, MulAut.apply_inv_self]
  map_mul' x y := by
    apply hι
    show ι (Classical.choose (h (x * y))) = ι (Classical.choose (h x) * Classical.choose (h y))
    have e1 := Classical.choose_spec (h (x * y))
    have e2 := Classical.choose_spec (h x)
    have e3 := Classical.choose_spec (h y)
    rw [e1, map_mul ι (Classical.choose (h x)) (Classical.choose (h y)), e2, e3, map_mul ι x y,
      map_mul σ]

theorem resAut_spec (ι : W →* V) (hι : Function.Injective ι) (σ : MulAut V)
    (h : ∀ w, ∃ w', ι w' = σ (ι w)) (h' : ∀ w, ∃ w', ι w' = σ⁻¹ (ι w)) (w : W) :
    ι (resAut ι hι σ h h' w) = σ (ι w) :=
  Classical.choose_spec (h w)

theorem resAut_one (ι : W →* V) (hι : Function.Injective ι)
    (h : ∀ w, ∃ w', ι w' = (1 : MulAut V) (ι w)) (h' : ∀ w, ∃ w', ι w' = (1 : MulAut V)⁻¹ (ι w)) :
    resAut ι hι 1 h h' = 1 := by
  ext w
  apply hι
  rw [resAut_spec, MulAut.one_apply, MulAut.one_apply]

theorem resAut_mul (ι : W →* V) (hι : Function.Injective ι) (σ τ : MulAut V)
    (hσ : ∀ w, ∃ w', ι w' = σ (ι w)) (hσ' : ∀ w, ∃ w', ι w' = σ⁻¹ (ι w))
    (hτ : ∀ w, ∃ w', ι w' = τ (ι w)) (hτ' : ∀ w, ∃ w', ι w' = τ⁻¹ (ι w))
    (hστ : ∀ w, ∃ w', ι w' = (σ * τ) (ι w)) (hστ' : ∀ w, ∃ w', ι w' = (σ * τ)⁻¹ (ι w)) :
    resAut ι hι (σ * τ) hστ hστ' = resAut ι hι σ hσ hσ' * resAut ι hι τ hτ hτ' := by
  ext w
  apply hι
  rw [resAut_spec, MulAut.mul_apply, MulAut.mul_apply, resAut_spec, resAut_spec]

@[expose] noncomputable def resHom (ι : W →* V) (hι : Function.Injective ι) (A : Subgroup (MulAut V))
    (hstab : ∀ σ ∈ A, ∀ w, ∃ w', ι w' = σ (ι w)) : ↥A →* MulAut W where
  toFun σ := resAut ι hι σ.1 (hstab σ.1 σ.2) (hstab σ.1⁻¹ (A.inv_mem σ.2))
  map_one' := resAut_one ι hι _ _
  map_mul' σ τ := resAut_mul ι hι σ.1 τ.1 _ _ _ _ _ _

theorem resHom_spec (ι : W →* V) (hι : Function.Injective ι) (A : Subgroup (MulAut V))
    (hstab : ∀ σ ∈ A, ∀ w, ∃ w', ι w' = σ (ι w)) (σ : ↥A) (w : W) :
    ι (resHom ι hι A hstab σ w) = (σ : MulAut V) (ι w) :=
  resAut_spec ι hι σ.1 _ _ w

theorem resHom_injective (ι : W →* V) (hι : Function.Injective ι) (A : Subgroup (MulAut V))
    (hstab : ∀ σ ∈ A, ∀ w, ∃ w', ι w' = σ (ι w))
    (hfaith : ∀ σ ∈ A, (∀ w, σ (ι w) = ι w) → σ = 1) :
    Function.Injective (resHom ι hι A hstab) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have h1 : resHom ι hι A hstab σ = 1 := hσ
  have h2 : ∀ w, (σ : MulAut V) (ι w) = ι w := fun w => by
    rw [← resHom_spec ι hι A hstab σ w, h1, MulAut.one_apply]
  exact Subtype.ext (hfaith σ σ.2 h2)

theorem exists_ffstar_of_weak [Finite W] {B : Subgroup (MulAut W)} (hB : B ≠ ⊥) (hab : IsElemAbelian2 B)
    (hw : Nat.card W ≤ Nat.card B * Nat.card (fixV B)) :
    ∃ B' : Subgroup (MulAut W), B' ≤ B ∧ B' ≠ ⊥ ∧ IsElemAbelian2 B' ∧
      ∀ B'' : Subgroup (MulAut W), B'' ≤ B' →
        Nat.card B'' * Nat.card (fixV B'') ≤ Nat.card B' * Nat.card (fixV B') := by
  have : Finite (MulAut W) := Finite.of_injective (fun σ : MulAut W => (σ : W → W))
    (fun σ τ h => MulEquiv.ext (fun w => congrFun h w))
  obtain ⟨X, hXB, hXmax⟩ := Set.exists_max_image {Y : Subgroup (MulAut W) | Y ≤ B}
    (fun Y => Nat.card Y * Nat.card (fixV Y)) (Set.toFinite _) ⟨B, show B ≤ B from le_rfl⟩
  have hfixbot : fixV (⊥ : Subgroup (MulAut W)) = ⊤ := by
    ext v
    simp [mem_fixV]
  by_cases hX : X = ⊥
  ·
    refine ⟨B, le_rfl, hB, hab, fun B'' hB'' => ?_⟩
    have h1 := hXmax B'' hB''
    have h2 : Nat.card X * Nat.card (fixV X) = Nat.card W := by
      rw [hX, hfixbot, Subgroup.card_bot, Subgroup.card_top, one_mul]
    omega
  · refine ⟨X, hXB, hX, ⟨fun a ha b hb => hab.1 a (hXB ha) b (hXB hb), fun a ha => hab.2 a (hXB ha)⟩,
      fun B'' hB'' => hXmax B'' (hB''.trans hXB)⟩

theorem offender_restrict [Finite V] (ι : W →* V) (hι : Function.Injective ι)
    {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    (hstab : ∀ σ ∈ A, ∀ w, ∃ w', ι w' = σ (ι w))
    (hfaith : ∀ σ ∈ A, (∀ w, σ (ι w) = ι w) → σ = 1) :
    ∃ B : Subgroup (MulAut W), (∀ b ∈ B, ∃ σ ∈ A, ∀ w, ι (b w) = σ (ι w)) ∧ B ≠ ⊥ ∧
      IsElemAbelian2 B ∧ ∀ B' : Subgroup (MulAut W), B' ≤ B →
        Nat.card B' * Nat.card (fixV B') ≤ Nat.card B * Nat.card (fixV B) := by
  have : Finite W := Finite.of_injective ι hι
  obtain ⟨-, hA1, hAab, hAmax⟩ := hA
  let res := resHom ι hι A hstab
  have hinj : Function.Injective res := resHom_injective ι hι A hstab hfaith
  let B₀ : Subgroup (MulAut W) := res.range
  have hB₀A : ∀ b ∈ B₀, ∃ σ ∈ A, ∀ w, ι (b w) = σ (ι w) := by
    rintro _ ⟨σ, rfl⟩
    exact ⟨σ.1, σ.2, fun w => resHom_spec ι hι A hstab σ w⟩
  have hB₀ne : B₀ ≠ ⊥ := by
    obtain ⟨σ, hσ⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
    intro h
    apply hσ
    apply hinj
    have : res σ ∈ B₀ := ⟨σ, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    rw [this, map_one]
  have hB₀ab : IsElemAbelian2 B₀ := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAab.1 σ.1 σ.2 τ.1 τ.2)
    · rintro _ ⟨σ, rfl⟩
      rw [← map_pow]
      have : σ ^ 2 = 1 := Subtype.ext (hAab.2 σ.1 σ.2)
      rw [this, map_one]
  have hcardB₀ : Nat.card B₀ = Nat.card ↥A :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hfix : Nat.card (fixV B₀) = Nat.card ↥(fixV A ⊓ ι.range) := by
    refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨ι w.1, ?_, w.1, rfl⟩) ⟨?_, ?_⟩)
    · intro σ hσ
      have h1 := w.2 (res ⟨σ, hσ⟩) ⟨⟨σ, hσ⟩, rfl⟩
      have h2 := resHom_spec ι hι A hstab ⟨σ, hσ⟩ w.1
      rw [h1] at h2
      exact h2.symm
    · intro x y hxy
      exact Subtype.ext (hι (congrArg Subtype.val hxy))
    · rintro ⟨v, hvA, w, rfl⟩
      refine ⟨⟨w, ?_⟩, rfl⟩
      rintro _ ⟨σ, rfl⟩
      apply hι
      rw [resHom_spec]
      exact hvA σ.1 σ.2
  have hwcard : Nat.card W = Nat.card ι.range :=
    Nat.card_congr (MonoidHom.ofInjective hι).toEquiv
  have hVbound : Nat.card V ≤ Nat.card ↥A * Nat.card (fixV A) := by
    have h := hAmax ⊥ bot_le
    have hfixbot : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
      ext v
      simp [mem_fixV]
    rwa [hfixbot, Subgroup.card_bot, Subgroup.card_top, one_mul] at h
  have hweak : Nat.card W ≤ Nat.card B₀ * Nat.card (fixV B₀) := by
    have h1 := card_mul_card_le_inf ι.range (fixV A)
    have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
    rw [hcardB₀, hfix]
    rw [hwcard]
    have h2 : Nat.card ι.range * Nat.card (fixV A) ≤ (Nat.card ↥A * Nat.card ↥(fixV A ⊓ ι.range)) *
        Nat.card (fixV A) := by
      calc Nat.card ι.range * Nat.card (fixV A) ≤ Nat.card V * Nat.card ↥(fixV A ⊓ ι.range) := h1
        _ ≤ (Nat.card ↥A * Nat.card (fixV A)) * Nat.card ↥(fixV A ⊓ ι.range) :=
            Nat.mul_le_mul_right _ hVbound
        _ = (Nat.card ↥A * Nat.card ↥(fixV A ⊓ ι.range)) * Nat.card (fixV A) := by ring
    exact Nat.le_of_mul_le_mul_right h2 hpos
  obtain ⟨B, hBB₀, hBne, hBab, hBmax⟩ := exists_ffstar_of_weak hB₀ne hB₀ab hweak
  exact ⟨B, fun b hb => hB₀A b (hBB₀ hb), hBne, hBab, hBmax⟩

end

end CFSG.Quasithin.FLc
