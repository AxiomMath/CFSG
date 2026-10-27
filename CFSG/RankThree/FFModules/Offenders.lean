module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.FFModules

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def fixSub (ρ : Representation (ZMod 2) G W) (A : Subgroup G) :
    Submodule (ZMod 2) W where
  carrier := {w | ∀ a ∈ A, ρ a w = w}
  add_mem' {v w} hv hw a ha := by rw [map_add, hv a ha, hw a ha]
  zero_mem' a _ := map_zero _
  smul_mem' c v hv a ha := by rw [map_smul, hv a ha]

theorem mem_fixSub {ρ : Representation (ZMod 2) G W} {A : Subgroup G} {w : W} :
    w ∈ fixSub ρ A ↔ ∀ a ∈ A, ρ a w = w :=
  Iff.rfl

@[expose] def IsOffender (ρ : Representation (ZMod 2) G W) (A : Subgroup G) : Prop :=
  Nat.card W ≤ Nat.card A * Nat.card (fixSub ρ A)

@[expose] def IsBestOffender (ρ : Representation (ZMod 2) G W) (A : Subgroup G) : Prop :=
  ∀ B ≤ A, Nat.card B * Nat.card (fixSub ρ B) ≤ Nat.card A * Nat.card (fixSub ρ A)

variable {ρ : Representation (ZMod 2) G W}

theorem fixSub_bot : fixSub ρ ⊥ = ⊤ := by
  ext w
  simp only [mem_fixSub, Subgroup.mem_bot, forall_eq, map_one, Module.End.one_apply,
    Submodule.mem_top]

theorem fixSub_antitone {A B : Subgroup G} (h : A ≤ B) : fixSub ρ B ≤ fixSub ρ A :=
  fun _ hw a ha => hw a (h ha)

theorem fixSub_sup (A B : Subgroup G) : fixSub ρ (A ⊔ B) = fixSub ρ A ⊓ fixSub ρ B := by
  refine le_antisymm (le_inf (fixSub_antitone le_sup_left) (fixSub_antitone le_sup_right)) ?_
  rintro w ⟨hA, hB⟩ x hx
  let S : Subgroup G :=
    { carrier := {g | ρ g w = w}
      mul_mem' := fun {g h} hg hh => by
        change ρ (g * h) w = w
        rw [map_mul, Module.End.mul_apply, hh, hg]
      one_mem' := by change ρ 1 w = w; rw [map_one, Module.End.one_apply]
      inv_mem' := fun {g} hg => by
        change ρ g⁻¹ w = w
        conv_lhs => rw [← hg]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have : A ⊔ B ≤ S := sup_le (fun a ha => hA a ha) (fun b hb => hB b hb)
  exact this hx

omit [Module (ZMod 2) W] in
theorem card_top_submodule [Module (ZMod 2) W] :
    Nat.card (⊤ : Submodule (ZMod 2) W) = Nat.card W :=
  Nat.card_congr Submodule.topEquiv.toEquiv

theorem IsBestOffender.isOffender {A : Subgroup G} (h : IsBestOffender ρ A) : IsOffender ρ A := by
  have := h ⊥ bot_le
  rw [Subgroup.card_bot, fixSub_bot, one_mul, card_top_submodule] at this
  exact this

section Finite

variable [Finite W]

theorem card_inf_mul_card_sup (C D : Submodule (ZMod 2) W) :
    Nat.card ↥(C ⊓ D) * Nat.card ↥(C ⊔ D) = Nat.card C * Nat.card D := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq C D
  have hc : ∀ S : Submodule (ZMod 2) W, Nat.card S = 2 ^ Module.finrank (ZMod 2) S := fun S => by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hc, hc, hc, hc, ← pow_add, ← pow_add]
  congr 1
  omega

theorem card_eq_two_pow_finrank (S : Submodule (ZMod 2) W) :
    Nat.card S = 2 ^ Module.finrank (ZMod 2) S := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem card_eq_two_pow_finrank' : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem isOffender_iff_finrank {A : Subgroup G} {a : ℕ} (hA : Nat.card A = 2 ^ a) :
    IsOffender ρ A ↔
      Module.finrank (ZMod 2) W - Module.finrank (ZMod 2) (fixSub ρ A) ≤ a := by
  have hle := Submodule.finrank_le (fixSub ρ A)
  rw [IsOffender, hA, card_eq_two_pow_finrank, card_eq_two_pow_finrank', ← pow_add,
    Nat.pow_le_pow_iff_right (by norm_num)]
  omega

theorem IsOffender.sup [Finite G] {A₁ A₂ : Subgroup G} (h₁ : IsOffender ρ A₁)
    (h₂ : IsBestOffender ρ A₂) (hc : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x) :
    IsOffender ρ (A₁ ⊔ A₂) := by
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₁ A₂ hc
  have hD := h₂ (A₁ ⊓ A₂) inf_le_right
  have hsub : fixSub ρ A₁ ⊔ fixSub ρ A₂ ≤ fixSub ρ (A₁ ⊓ A₂) :=
    sup_le (fixSub_antitone inf_le_left) (fixSub_antitone inf_le_right)
  have hle : Nat.card ↥(fixSub ρ A₁ ⊔ fixSub ρ A₂) ≤ Nat.card (fixSub ρ (A₁ ⊓ A₂)) :=
    Nat.card_le_card_of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)
  have hCC := card_inf_mul_card_sup (fixSub ρ A₁) (fixSub ρ A₂)
  rw [IsOffender, fixSub_sup]
  have hpos2 : 0 < Nat.card A₂ * Nat.card (fixSub ρ A₂) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have key : Nat.card A₁ * Nat.card (fixSub ρ A₁) * (Nat.card A₂ * Nat.card (fixSub ρ A₂)) ≤
      Nat.card ↥(A₁ ⊔ A₂) * Nat.card ↥(fixSub ρ A₁ ⊓ fixSub ρ A₂) *
        (Nat.card A₂ * Nat.card (fixSub ρ A₂)) := by
    calc Nat.card A₁ * Nat.card (fixSub ρ A₁) * (Nat.card A₂ * Nat.card (fixSub ρ A₂))
        = Nat.card ↥(A₁ ⊔ A₂) * Nat.card ↥(fixSub ρ A₁ ⊓ fixSub ρ A₂) *
            (Nat.card ↥(A₁ ⊓ A₂) * Nat.card ↥(fixSub ρ A₁ ⊔ fixSub ρ A₂)) := by
          rw [show Nat.card A₁ * Nat.card (fixSub ρ A₁) * (Nat.card A₂ * Nat.card (fixSub ρ A₂)) =
            (Nat.card A₁ * Nat.card A₂) * (Nat.card (fixSub ρ A₁) * Nat.card (fixSub ρ A₂)) by
              ring, ← hcard, ← hCC]
          ring
      _ ≤ Nat.card ↥(A₁ ⊔ A₂) * Nat.card ↥(fixSub ρ A₁ ⊓ fixSub ρ A₂) *
            (Nat.card ↥(A₁ ⊓ A₂) * Nat.card (fixSub ρ (A₁ ⊓ A₂))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hle)
      _ ≤ Nat.card ↥(A₁ ⊔ A₂) * Nat.card ↥(fixSub ρ A₁ ⊓ fixSub ρ A₂) *
            (Nat.card A₂ * Nat.card (fixSub ρ A₂)) := Nat.mul_le_mul_left _ hD
  exact h₁.trans (Nat.le_of_mul_le_mul_right key hpos2)

theorem isOffender_finset_sup [Finite G] (𝓑 : Finset (Subgroup G)) (hne : 𝓑.Nonempty)
    (hbest : ∀ B ∈ 𝓑, IsBestOffender ρ B)
    (hc : ∀ B ∈ 𝓑, ∀ B' ∈ 𝓑, ∀ x ∈ B, ∀ y ∈ B', x * y = y * x) :
    IsOffender ρ (𝓑.sup id) := by
  classical
  induction hne using Finset.Nonempty.cons_induction with
  | singleton B => simpa using (hbest B (Finset.mem_singleton_self B)).isOffender
  | cons B 𝓒 hB h𝓒 ih =>
    rw [Finset.sup_cons, id, sup_comm]
    refine IsOffender.sup (ih (fun B' hB' => hbest B' (Finset.mem_cons_of_mem hB'))
      (fun B' hB' B'' hB'' => hc B' (Finset.mem_cons_of_mem hB') B'' (Finset.mem_cons_of_mem hB'')))
      (hbest B (Finset.mem_cons_self B 𝓒)) ?_
    intro x hx y hy
    have hxC : x ∈ Subgroup.centralizer (B : Set G) := by
      have : 𝓒.sup id ≤ Subgroup.centralizer (B : Set G) :=
        Finset.sup_le fun B' hB' z hz => Subgroup.mem_centralizer_iff.mpr fun y hy =>
          hc B (Finset.mem_cons_self B 𝓒) B' (Finset.mem_cons_of_mem hB') y hy z hz
      exact this hx
    exact (Subgroup.mem_centralizer_iff.mp hxC y hy).symm

omit [Finite W] in
theorem exists_isBestOffender [Finite G] {A : Subgroup G} (hA : IsOffender ρ A) (hA1 : A ≠ ⊥) :
    ∃ B ≤ A, B ≠ ⊥ ∧ IsBestOffender ρ B := by
  classical
  let f : Subgroup G → ℕ := fun B => Nat.card B * Nat.card (fixSub ρ B)
  have hfin : (Set.univ : Set (Subgroup G)).Finite := Set.finite_univ
  let T : Finset (Subgroup G) :=
    (hfin.toFinset).filter fun B => B ≤ A ∧ B ≠ ⊥
  have hT : T.Nonempty := ⟨A, by simp [T, hA1]⟩
  obtain ⟨B, hBT, hBmax⟩ := T.exists_max_image f hT
  simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_univ, true_and] at hBT
  refine ⟨B, hBT.1, hBT.2, fun D hD => ?_⟩
  by_cases hD1 : D = ⊥
  ·
    have h1 : f A ≤ f B := hBmax A (by simp [T, hA1])
    have h2 : f D = Nat.card W := by
      simp only [f, hD1, Subgroup.card_bot, fixSub_bot, one_mul]
      exact card_top_submodule
    change f D ≤ f B
    rw [h2]
    exact hA.trans h1
  · exact hBmax D (by simp [T, hD1, hD.trans hBT.1])

end Finite

theorem card_fixSub_conj (g : G) (A : Subgroup G) :
    Nat.card (fixSub ρ (A.map (MulAut.conj g).toMonoidHom)) = Nat.card (fixSub ρ A) := by
  have hρ : ∀ w, ρ g⁻¹ (ρ g w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hρ' : ∀ w, ρ g (ρ g⁻¹ w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  refine Nat.card_congr
    { toFun := fun w => ⟨ρ g⁻¹ w, fun a ha => ?_⟩
      invFun := fun w => ⟨ρ g w, fun b hb => ?_⟩
      left_inv := fun w => Subtype.ext (hρ' w)
      right_inv := fun w => Subtype.ext (hρ w) }
  · have := w.2 (g * a * g⁻¹) ⟨a, ha, rfl⟩
    have e : ρ a (ρ g⁻¹ w) = ρ g⁻¹ (ρ (g * a * g⁻¹) w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [e, this]
  · obtain ⟨a, ha, rfl⟩ := hb
    change ρ (g * a * g⁻¹) (ρ g w) = ρ g w
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hρ, w.2 a ha]

theorem card_map_conj (g : G) (A : Subgroup G) :
    Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
  Nat.card_congr (A.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv.symm

theorem isBestOffender_conj {A : Subgroup G} (h : IsBestOffender ρ A) (g : G) :
    IsBestOffender ρ (A.map (MulAut.conj g).toMonoidHom) := by
  intro B hB
  have hB' : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ A := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hB hy
    simpa [MulAut.conj_apply, mul_assoc] using hz
  have h1 := h _ hB'
  rw [card_map_conj, card_fixSub_conj] at h1
  rw [card_map_conj, card_fixSub_conj]
  exact h1

end CFSG.RankThree.FFModules
