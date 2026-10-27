module

public import CFSG.Quasithin.H13.L32AL2a
public import CFSG.Quasithin.H13.L32AL2b

public section

namespace CFSG.Quasithin.H13.L32A.L2

open Equiv CFSG.Quasithin

theorem perm_elemAb_four : ∀ x : Perm (Fin 5), (x * x = 1 ∧ x ≠ 1) → ∀ y : Perm (Fin 5),
    (y * y = 1 ∧ y ≠ 1 ∧ x ≠ y ∧ x * y = y * x) → ∀ z : Perm (Fin 5),
    (z * z = 1 ∧ x * z = z * x ∧ y * z = z * y) → (z = 1 ∨ z = x ∨ z = y ∨ z = x * y) := by
  decide +kernel

theorem alt5_elemAb_four {X : Type} [Group X] (φ : X ≃* alternatingGroup (Fin 5))
    {α β γ : MulAut X} (hα : α * α = 1) (hβ : β * β = 1) (hγ : γ * γ = 1)
    (hαβ : α * β = β * α) (hαγ : α * γ = γ * α) (hβγ : β * γ = γ * β) (hα1 : α ≠ 1)
    (hβ1 : β ≠ 1) (hne : α ≠ β) : γ = 1 ∨ γ = α ∨ γ = β ∨ γ = α * β := by
  set E : MulAut X ≃* Perm (Fin 5) :=
    (MulAut.congr φ).trans CFSG.Semidihedral.Principal.CyclicAlternatingFive.autEquiv.symm with hE
  have key := perm_elemAb_four (E α) ⟨by rw [← map_mul, hα, map_one],
    fun h => hα1 (E.injective (h.trans (map_one E).symm))⟩ (E β)
    ⟨by rw [← map_mul, hβ, map_one], fun h => hβ1 (E.injective (h.trans (map_one E).symm)),
      fun h => hne (E.injective h), by rw [← map_mul, ← map_mul, hαβ]⟩ (E γ)
    ⟨by rw [← map_mul, hγ, map_one], by rw [← map_mul, ← map_mul, hαγ],
      by rw [← map_mul, ← map_mul, hβγ]⟩
  rcases key with h | h | h | h
  · exact Or.inl (E.injective (h.trans (map_one E).symm))
  · exact Or.inr (Or.inl (E.injective h))
  · exact Or.inr (Or.inr (Or.inl (E.injective h)))
  · exact Or.inr (Or.inr (Or.inr (E.injective (h.trans (map_mul E α β).symm))))

@[expose] def cycle5 : alternatingGroup (Fin 5) :=
  ⟨finRotate 5, Perm.mem_alternatingGroup.mpr (by decide)⟩

section Free

variable {W' : Type} [CommGroup W']

@[expose] def commHom (b : MulAut W') : W' →* W' where
  toFun w := b w * w⁻¹
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem commHom_apply (b : MulAut W') (w : W') : commHom b w = b w * w⁻¹ := rfl

theorem mem_ker_commHom {b : MulAut W'} {w : W'} : w ∈ (commHom b).ker ↔ b w = w := by
  rw [MonoidHom.mem_ker, commHom_apply, mul_inv_eq_one]

theorem range_le_ker (hV : ∀ w : W', w * w = 1) {b : MulAut W'} (hb2 : b * b = 1) :
    (commHom b).range ≤ (commHom b).ker := by
  rintro _ ⟨w, rfl⟩
  rw [mem_ker_commHom, commHom_apply, map_mul, map_inv]
  have hbb : b (b w) = w := by rw [← MulAut.mul_apply, hb2, MulAut.one_apply]
  rw [hbb, inv_eq_of_mul_eq_one_right (hV (b w)), inv_eq_of_mul_eq_one_right (hV w), mul_comm]

theorem card_ker_mul_card_range (b : MulAut W') :
    Nat.card (commHom b).ker * Nat.card (commHom b).range = Nat.card W' := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

variable [Finite W']

theorem card_ker_sq (hV : ∀ w : W', w * w = 1) {b x : MulAut W'} (hb2 : b * b = 1)
    (hbx : b * x * b⁻¹ = x⁻¹) {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1)
    (hfpf : ∀ w : W', x w = w → w = 1) : Nat.card (commHom b).ker ^ 2 = Nat.card W' := by
  set C := (commHom b).ker with hC
  have hcard := card_ker_mul_card_range b
  apply le_antisymm
  · obtain ⟨k, rfl⟩ := hm
    set z := x ^ (k + 1) with hz
    have hz2 : z * z = x := by
      rw [hz, ← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hxm, one_mul]
    have hbz : b * z * b⁻¹ = z⁻¹ := by rw [hz, ← conj_pow, hbx, inv_pow]
    have hbz' : ∀ w, b (z w) = z⁻¹ (b w) := fun w => by
      have e : b * z = z⁻¹ * b := by
        calc b * z = (b * z * b⁻¹) * b := by group
          _ = z⁻¹ * b := by rw [hbz]
      calc b (z w) = (b * z) w := rfl
        _ = (z⁻¹ * b) w := by rw [e]
    have hinf : C ⊓ C.map z.toMonoidHom = ⊥ := by
      rw [eq_bot_iff]
      rintro w ⟨hw, ⟨w', hw', rfl⟩⟩
      rw [Subgroup.mem_bot]
      have hw1 : b w' = w' := mem_ker_commHom.mp hw'
      have hw2 : b (z w') = z w' := mem_ker_commHom.mp hw
      have h1 : z w' = z⁻¹ w' := by rw [← hw2, hbz', hw1]
      have h3 : x w' = w' := by
        rw [← hz2]
        calc (z * z) w' = z (z w') := rfl
          _ = z (z⁻¹ w') := by rw [h1]
          _ = w' := by simp
      show z w' = 1
      rw [hfpf w' h3, map_one]
    have h1 := card_sup_of_inf_eq_bot hinf
    rw [Subgroup.card_map_of_injective z.injective] at h1
    have h2 := Subgroup.card_le_card_group (C ⊔ C.map z.toMonoidHom)
    rw [h1] at h2
    nlinarith
  · have hle := Subgroup.card_le_of_le (range_le_ker hV hb2)
    nlinarith

end Free

structure WrData {W' : Type} [CommGroup W'] (H' P₁ P₂ : Subgroup (MulAut W')) : Prop where
  sq : ∀ w : W', w * w = 1
  card : Nat.card W' = 256
  iso₁ : Nonempty (↥P₁ ≃* alternatingGroup (Fin 5))
  iso₂ : Nonempty (↥P₂ ≃* alternatingGroup (Fin 5))
  le₁ : P₁ ≤ H'
  le₂ : P₂ ≤ H'
  comm : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a
  inf : P₁ ⊓ P₂ = ⊥
  fpf₁ : ∀ y ∈ P₁, y ≠ 1 → ∀ m : ℕ, Odd m → y ^ m = 1 → ∀ w : W', y w = w → w = 1
  fpf₂ : ∀ y ∈ P₂, y ≠ 1 → ∀ m : ℕ, Odd m → y ^ m = 1 → ∀ w : W', y w = w → w = 1
  cases : ∀ f ∈ H', ((∀ a ∈ P₁, f * a * f⁻¹ ∈ P₁) ∧ ∀ b ∈ P₂, f * b * f⁻¹ ∈ P₂) ∨
    ((∀ a ∈ P₁, f * a * f⁻¹ ∈ P₂) ∧ ∀ b ∈ P₂, f * b * f⁻¹ ∈ P₁)
  cent : ∀ c ∈ H', (∀ a ∈ P₁, c * a = a * c) → (∀ b ∈ P₂, c * b = b * c) → c = 1
  inner₁ : ∀ f : MulAut W', (∃ ℓ ∈ P₂, ∀ y ∈ P₂, f * y * f⁻¹ = ℓ * y * ℓ⁻¹) →
    ∃ ℓ ∈ P₁, ∀ y ∈ P₁, f * y * f⁻¹ = ℓ * y * ℓ⁻¹
  inner₂ : ∀ f : MulAut W', (∃ ℓ ∈ P₁, ∀ y ∈ P₁, f * y * f⁻¹ = ℓ * y * ℓ⁻¹) →
    ∃ ℓ ∈ P₂, ∀ y ∈ P₂, f * y * f⁻¹ = ℓ * y * ℓ⁻¹

namespace WrData

variable {W' : Type} [CommGroup W'] {H' P₁ P₂ : Subgroup (MulAut W')}

theorem symm (Y : WrData H' P₁ P₂) : WrData H' P₂ P₁ where
  sq := Y.sq
  card := Y.card
  iso₁ := Y.iso₂
  iso₂ := Y.iso₁
  le₁ := Y.le₂
  le₂ := Y.le₁
  comm a ha b hb := (Y.comm b hb a ha).symm
  inf := by rw [inf_comm]; exact Y.inf
  fpf₁ := Y.fpf₂
  fpf₂ := Y.fpf₁
  cases f hf := (Y.cases f hf).imp (fun h => ⟨h.2, h.1⟩) (fun h => ⟨h.2, h.1⟩)
  cent c hc h1 h2 := Y.cent c hc h2 h1
  inner₁ := Y.inner₂
  inner₂ := Y.inner₁

theorem exists_ne_one₁ (Y : WrData H' P₁ P₂) : ∃ a ∈ P₁, a ≠ 1 := by
  obtain ⟨φ⟩ := Y.iso₁
  refine ⟨φ.symm cycle5, (φ.symm _).2, fun h => ?_⟩
  have h1 : φ.symm cycle5 = 1 := Subtype.ext h
  have h2 := congrArg (fun x => ((φ x : alternatingGroup (Fin 5)) : Perm (Fin 5))) h1
  simp only [MulEquiv.apply_symm_apply, map_one, cycle5] at h2
  exact absurd h2 (by decide)

theorem exists_five₂ (Y : WrData H' P₁ P₂) : ∃ u ∈ P₂, u ≠ 1 ∧ u ^ 5 = 1 := by
  obtain ⟨φ⟩ := Y.iso₂
  set c : alternatingGroup (Fin 5) := cycle5 with hc
  refine ⟨φ.symm c, (φ.symm c).2, fun h => ?_, ?_⟩
  · have h1 : φ.symm c = 1 := Subtype.ext h
    have h2 := congrArg (fun x => ((φ x : alternatingGroup (Fin 5)) : Perm (Fin 5))) h1
    simp only [MulEquiv.apply_symm_apply, map_one, hc, cycle5] at h2
    exact absurd h2 (by decide)
  · have h5 : c ^ 5 = 1 := Subtype.ext (by rw [hc, cycle5]; decide)
    have : (φ.symm c) ^ 5 = 1 := by rw [← map_pow, h5, map_one]
    exact congrArg Subtype.val this

theorem conj_mem₂ (Y : WrData H' P₁ P₂) {f : MulAut W'} (hf : f ∈ H')
    (h : ∀ a ∈ P₁, f * a * f⁻¹ ∈ P₁) : ∀ b ∈ P₂, f * b * f⁻¹ ∈ P₂ := by
  rcases Y.cases f hf with h1 | ⟨h1, -⟩
  · exact h1.2
  · exfalso
    obtain ⟨a, ha, ha1⟩ := Y.exists_ne_one₁
    have hm : f * a * f⁻¹ ∈ P₁ ⊓ P₂ := Subgroup.mem_inf.mpr ⟨h a ha, h1 a ha⟩
    rw [Y.inf, Subgroup.mem_bot] at hm
    apply ha1
    calc a = f⁻¹ * (f * a * f⁻¹) * f := by group
      _ = 1 := by rw [hm]; group

theorem mem_normalizer_of_sq {P : Subgroup (MulAut W')} {x : MulAut W'} (hx2 : x * x = 1)
    (h : ∀ a ∈ P, x * a * x⁻¹ ∈ P) : x ∈ Subgroup.normalizer (P : Set (MulAut W')) := by
  have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨h a, fun ha => ?_⟩
  have := h _ ha
  rwa [hinv, show x * (x * a * x) * x = (x * x) * a * (x * x) by group, hx2, one_mul,
    mul_one] at this

theorem mem_of_comm (Y : WrData H' P₁ P₂) {x : MulAut W'} (hx : x ∈ H')
    (hc : ∀ b ∈ P₂, x * b = b * x) : x ∈ P₁ := by
  obtain ⟨ℓ, hℓ, hℓx⟩ := Y.inner₁ x ⟨1, one_mem _, fun y hy => by rw [hc y hy]; group⟩
  have h1 : ℓ⁻¹ * x = 1 := by
    refine Y.cent (ℓ⁻¹ * x) (mul_mem (inv_mem (Y.le₁ hℓ)) hx) (fun a ha => ?_) (fun b hb => ?_)
    · have e := hℓx a ha
      calc ℓ⁻¹ * x * a = ℓ⁻¹ * (x * a * x⁻¹) * x := by group
        _ = ℓ⁻¹ * (ℓ * a * ℓ⁻¹) * x := by rw [e]
        _ = a * (ℓ⁻¹ * x) := by group
    · have e1 := hc b hb
      have e2 := Y.comm ℓ hℓ b hb
      have e3 : ℓ⁻¹ * b = b * ℓ⁻¹ := by
        calc ℓ⁻¹ * b = ℓ⁻¹ * (b * ℓ) * ℓ⁻¹ := by group
          _ = ℓ⁻¹ * (ℓ * b) * ℓ⁻¹ := by rw [e2]
          _ = b * ℓ⁻¹ := by group
      calc ℓ⁻¹ * x * b = ℓ⁻¹ * (x * b) := by group
        _ = ℓ⁻¹ * (b * x) := by rw [e1]
        _ = (ℓ⁻¹ * b) * x := by group
        _ = b * (ℓ⁻¹ * x) := by rw [e3]; group
  have : x = ℓ := by
    calc x = ℓ * (ℓ⁻¹ * x) := by group
      _ = ℓ := by rw [h1, mul_one]
  rw [this]
  exact hℓ

variable [Finite W']

theorem card_fix_of {P : Subgroup (MulAut W')} (Y : WrData H' P₁ P₂)
    (φ : ↥P ≃* alternatingGroup (Fin 5))
    (fpf : ∀ y ∈ P, y ≠ 1 → ∀ m : ℕ, Odd m → y ^ m = 1 → ∀ w : W', y w = w → w = 1)
    {b : MulAut W'} (hb2 : b * b = 1) (hbN : b ∈ Subgroup.normalizer (P : Set (MulAut W')))
    (hc : ¬ ∀ a ∈ P, b * a = a * b) : Nat.card (commHom b).ker = 16 := by
  set σ := P.normalizerMonoidHom ⟨b, hbN⟩ with hσ
  have hσapp : ∀ y : ↥P, ((σ y : ↥P) : MulAut W') = b * y * b⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P ⟨b, hbN⟩ y
  have hσ2 : σ * σ = 1 := by
    rw [hσ, ← map_mul]
    have : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (P : Set (MulAut W')))) * ⟨b, hbN⟩ = 1 :=
      Subtype.ext hb2
    rw [this, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hc
    intro a ha
    have e := hσapp ⟨a, ha⟩
    rw [h, MulAut.one_apply] at e
    calc b * a = (b * a * b⁻¹) * b := by group
      _ = a * b := by rw [← e]
  have hsq : ∀ (x : ↥P) (m : ℕ), Odd m → x ^ m = 1 → x ≠ 1 → σ x = x⁻¹ →
      Nat.card (commHom b).ker = 16 := by
    intro x m hm hxm hx1 hσx
    have hbx : b * (x : MulAut W') * b⁻¹ = (x : MulAut W')⁻¹ := by
      rw [← hσapp, hσx]
      rfl
    have hxm' : (x : MulAut W') ^ m = 1 := by
      have := congrArg Subtype.val hxm
      simpa using this
    have hx1' : (x : MulAut W') ≠ 1 := fun h => hx1 (Subtype.ext h)
    have h := card_ker_sq Y.sq hb2 hbx hm hxm' (fpf x x.2 hx1' m hm hxm')
    rw [Y.card, show (256 : ℕ) = 16 ^ 2 by norm_num] at h
    exact Nat.pow_left_injective (by norm_num) h
  rcases alt5_involution_cases φ σ hσ2 with h | ⟨x, hx5, hx1, hσx⟩ | ⟨⟨x, hx3, hx1, hσx⟩, -⟩
  · exact absurd h hσ1
  · exact hsq x 5 (by decide) hx5 hx1 hσx
  · exact hsq x 3 (by decide) hx3 hx1 hσx

theorem card_fix (Y : WrData H' P₁ P₂) {b : MulAut W'} (hb : b ∈ H') (hb2 : b * b = 1)
    (hb1 : b ≠ 1) (hN : ∀ a ∈ P₁, b * a * b⁻¹ ∈ P₁) : Nat.card (commHom b).ker = 16 := by
  by_cases hc1 : ∀ a ∈ P₁, b * a = a * b
  · have hc2 : ¬ ∀ a ∈ P₂, b * a = a * b := fun hc2 => hb1 (Y.cent b hb hc1 hc2)
    obtain ⟨φ⟩ := Y.iso₂
    exact Y.card_fix_of φ Y.fpf₂ hb2 (mem_normalizer_of_sq hb2 (Y.conj_mem₂ hb hN)) hc2
  · obtain ⟨φ⟩ := Y.iso₁
    exact Y.card_fix_of φ Y.fpf₁ hb2 (mem_normalizer_of_sq hb2 hN) hc1

omit [Finite W'] in
theorem not_both (Y : WrData H' P₁ P₂) {A : Subgroup (MulAut W')} (hAH : A ≤ H')
    (hF16 : Nat.card (fixV A) = 16)
    (hkerF : ∀ a ∈ A, a ≠ 1 → (∀ y ∈ P₁, a * y * a⁻¹ ∈ P₁) → (commHom a).ker = fixV A)
    {c₁ c₂ : MulAut W'} (hc₁ : c₁ ∈ A) (hc₁1 : c₁ ≠ 1) (hc₁c : ∀ y ∈ P₂, c₁ * y = y * c₁)
    (hc₂ : c₂ ∈ A) (hc₂1 : c₂ ≠ 1) (hc₂c : ∀ y ∈ P₁, c₂ * y = y * c₂) : False := by
  have hc₁P : c₁ ∈ P₁ := Y.mem_of_comm (hAH hc₁) hc₁c
  have hc₂P : c₂ ∈ P₂ := Y.symm.mem_of_comm (hAH hc₂) hc₂c
  have hF := hkerF c₁ hc₁ hc₁1 fun y hy => mul_mem (mul_mem hc₁P hy) (inv_mem hc₁P)
  have hinv : ∀ p ∈ P₂, ∀ w ∈ fixV A, p w ∈ fixV A := by
    intro p hp w hw
    rw [← hF] at hw ⊢
    rw [mem_ker_commHom] at hw ⊢
    have e := hc₁c p hp
    calc c₁ (p w) = (c₁ * p) w := rfl
      _ = (p * c₁) w := by rw [e]
      _ = p w := by rw [MulAut.mul_apply, hw]
  obtain ⟨φ⟩ := Y.iso₂
  have : IsSimpleGroup ↥P₂ :=
    (MulEquiv.isSimpleGroup_congr φ).mpr (alternatingGroup.isSimpleGroup (by simp))
  let S : Subgroup ↥P₂ :=
    { carrier := {p | ∀ w ∈ fixV A, (p : MulAut W') w = w}
      mul_mem' := fun {p q} hp hq w hw => by
        show (p : MulAut W') ((q : MulAut W') w) = w
        rw [hq w hw, hp w hw]
      one_mem' := fun w _ => rfl
      inv_mem' := fun {p} hp w hw => by
        show (p : MulAut W')⁻¹ w = w
        conv_lhs => rw [← hp w hw]
        exact MulAut.inv_apply_self _ _ _ }
  have hSn : S.Normal := by
    refine ⟨fun n hn g w hw => ?_⟩
    show (g : MulAut W') ((n : MulAut W') ((g : MulAut W')⁻¹ w)) = w
    have hgw : (g : MulAut W')⁻¹ w ∈ fixV A := hinv _ (inv_mem g.2) w hw
    rw [hn _ hgw]
    exact MulAut.apply_inv_self _ _ _
  have hc₂S : (⟨c₂, hc₂P⟩ : ↥P₂) ∈ S := fun w hw => hw c₂ hc₂
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h | h
  · have : (⟨c₂, hc₂P⟩ : ↥P₂) ∈ (⊥ : Subgroup ↥P₂) := h ▸ hc₂S
    exact hc₂1 (congrArg Subtype.val (Subgroup.mem_bot.mp this))
  · obtain ⟨u, hu, hu1, hu5⟩ := Y.exists_five₂
    have huS : (⟨u, hu⟩ : ↥P₂) ∈ S := h ▸ Subgroup.mem_top _
    have hbot : fixV A = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      exact Subgroup.mem_bot.mpr (Y.fpf₂ u hu hu1 5 (by decide) hu5 w (huS w hw))
    rw [hbot, Subgroup.card_bot] at hF16
    exact absurd hF16 (by norm_num)

omit [Finite W'] in
theorem mem_four (Y : WrData H' P₁ P₂) {A : Subgroup (MulAut W')} (hAH : A ≤ H')
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hC : ∀ c ∈ A, (∀ y ∈ P₂, c * y = y * c) → c = 1) {x y z : MulAut W'} (hx : x ∈ A)
    (hxN : ∀ a ∈ P₁, x * a * x⁻¹ ∈ P₁) (hx1 : x ≠ 1) (hy : y ∈ A)
    (hyN : ∀ a ∈ P₁, y * a * y⁻¹ ∈ P₁) (hy1 : y ≠ 1) (hxy : x ≠ y) (hz : z ∈ A)
    (hzN : ∀ a ∈ P₁, z * a * z⁻¹ ∈ P₁) : z = 1 ∨ z = x ∨ z = y ∨ z = x * y := by
  obtain ⟨φ⟩ := Y.iso₂
  set N₂ := Subgroup.normalizer (P₂ : Set (MulAut W')) with hN₂
  have hN : ∀ {u : MulAut W'}, u ∈ A → (∀ a ∈ P₁, u * a * u⁻¹ ∈ P₁) → u ∈ N₂ :=
    fun {u} hu huN => mem_normalizer_of_sq (hA2 u hu) (Y.conj_mem₂ (hAH hu) huN)
  set ψ := P₂.normalizerMonoidHom with hψ
  have hψapp : ∀ (u : ↥N₂) (p : ↥P₂), ((ψ u p : ↥P₂) : MulAut W') = u * p * (u : MulAut W')⁻¹ :=
    fun u p => Subgroup.normalizerMonoidHom_apply_apply_coe P₂ u p
  have hinj : ∀ (u v : ↥N₂), (u : MulAut W') ∈ A → (v : MulAut W') ∈ A → ψ u = ψ v → u = v := by
    intro u v hu hv huv
    have h1 : ψ (u⁻¹ * v) = 1 := by rw [map_mul, map_inv, huv, inv_mul_cancel]
    have h2 : ((u⁻¹ * v : ↥N₂) : MulAut W') = 1 := by
      refine hC _ (mul_mem (inv_mem hu) hv) fun p hp => ?_
      have e := hψapp (u⁻¹ * v) ⟨p, hp⟩
      rw [h1, MulAut.one_apply] at e
      calc ((u⁻¹ * v : ↥N₂) : MulAut W') * p
          = (((u⁻¹ * v : ↥N₂) : MulAut W') * p * ((u⁻¹ * v : ↥N₂) : MulAut W')⁻¹) *
            ((u⁻¹ * v : ↥N₂) : MulAut W') := by group
        _ = p * ((u⁻¹ * v : ↥N₂) : MulAut W') := by rw [← e]
    have h3 : u⁻¹ * v = 1 := Subtype.ext h2
    calc u = u * (u⁻¹ * v) := by rw [h3, mul_one]
      _ = v := by group
  set x' : ↥N₂ := ⟨x, hN hx hxN⟩
  set y' : ↥N₂ := ⟨y, hN hy hyN⟩
  set z' : ↥N₂ := ⟨z, hN hz hzN⟩
  have hsq : ∀ (u : ↥N₂), (u : MulAut W') ∈ A → ψ u * ψ u = 1 := fun u hu => by
    rw [← map_mul, show u * u = 1 from Subtype.ext (hA2 _ hu), map_one]
  have hcm : ∀ (u v : ↥N₂), (u : MulAut W') ∈ A → (v : MulAut W') ∈ A →
      ψ u * ψ v = ψ v * ψ u := fun u v hu hv => by
    rw [← map_mul, ← map_mul, show u * v = v * u from Subtype.ext (hAc _ hu _ hv)]
  have hne1 : ∀ (u : ↥N₂), (u : MulAut W') ∈ A → (u : MulAut W') ≠ 1 → ψ u ≠ 1 := by
    intro u hu hu1 h
    apply hu1
    have := hinj u 1 hu (one_mem A) (h.trans (map_one ψ).symm)
    rw [this]
    rfl
  rcases alt5_elemAb_four φ (hsq x' hx) (hsq y' hy) (hsq z' hz) (hcm x' y' hx hy)
      (hcm x' z' hx hz) (hcm y' z' hy hz) (hne1 x' hx hx1) (hne1 y' hy hy1)
      (fun h => hxy (congrArg Subtype.val (hinj x' y' hx hy h))) with h | h | h | h
  · left
    exact congrArg Subtype.val (hinj z' 1 hz (one_mem A) (h.trans (map_one ψ).symm))
  · right; left
    exact congrArg Subtype.val (hinj z' x' hz hx h)
  · right; right; left
    exact congrArg Subtype.val (hinj z' y' hz hy h)
  · right; right; right
    exact congrArg Subtype.val (hinj z' (x' * y') hz (mul_mem hx hy) (h.trans (map_mul ψ x' y').symm))

theorem eq_of_card_le_two {M : Type} [Group M] [Finite M] {Z : Subgroup M}
    (hZ : Nat.card Z ≤ 2) {u v : M} (hu : u ∈ Z) (hv : v ∈ Z) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    u = v := by
  by_contra huv
  have hsub : ({1, u, v} : Set M) ⊆ Z := by
    intro w hw
    rcases hw with rfl | rfl | rfl
    · exact one_mem Z
    · exact hu
    · exact hv
  have h3 : ({1, u, v} : Set M).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, u, v, hu1.symm, hv1.symm, huv, rfl⟩
  have h4 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3, ← Nat.card_coe_set_eq] at h4
  exact absurd (h4.trans hZ) (by norm_num)

theorem exists_mem_not_mem_finset {M : Type} [Group M] (S : Subgroup M) (L : Finset M)
    (hL : L.card < Nat.card S) : ∃ x ∈ S, x ∉ L := by
  by_contra hc
  push Not at hc
  have hsub : (S : Set M) ⊆ ↑L := fun x hx => hc x hx
  have h1 := Set.ncard_le_ncard hsub L.finite_toSet
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h1
  exact absurd (h1.trans_lt hL) (lt_irrefl _)

theorem false_of_offender (Y : WrData H' P₁ P₂) {A : Subgroup (MulAut W')} (hAH : A ≤ H')
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hq : ∀ a ∈ A, ∀ b ∈ A, ∀ w : W', b (a w * w⁻¹) = a w * w⁻¹) (h4 : 4 ≤ Nat.card A)
    {D Z : Subgroup W'} (hZ : Nat.card Z ≤ 2) (hD : D.index ≤ Nat.card A)
    (hDZ : ∀ d ∈ D, ∀ a ∈ A, a d * d⁻¹ ∈ Z) : False := by
  classical
  set N₁ := Subgroup.normalizer (P₁ : Set (MulAut W')) with hN₁
  set F := fixV A with hF
  have hNiff : ∀ a ∈ A, a ∈ N₁ ↔ ∀ y ∈ P₁, a * y * a⁻¹ ∈ P₁ := fun a ha =>
    ⟨fun h y hy => (Subgroup.mem_normalizer_iff.mp h y).mp hy,
      fun h => mem_normalizer_of_sq (hA2 a ha) h⟩
  have hswap : ∀ a ∈ A, ∀ b ∈ A, a ∉ N₁ → b ∉ N₁ → a * b ∈ N₁ := by
    have hsw : ∀ c ∈ A, c ∉ N₁ → (∀ y ∈ P₁, c * y * c⁻¹ ∈ P₂) ∧
        ∀ y ∈ P₂, c * y * c⁻¹ ∈ P₁ := by
      intro c hc hcN
      rcases Y.cases c (hAH hc) with h | h
      · exact absurd ((hNiff c hc).mpr h.1) hcN
      · exact h
    intro a ha b hb haN hbN
    rw [hNiff _ (mul_mem ha hb)]
    intro y hy
    have := (hsw a ha haN).2 _ ((hsw b hb hbN).1 y hy)
    rwa [show a * (b * y * b⁻¹) * a⁻¹ = a * b * y * (a * b)⁻¹ by group] at this
  have hidx : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ N₁) := by
    have hdvd : (N₁.subgroupOf A).index ∣ 2 := by
      rw [Subgroup.index_dvd_two_iff]
      by_cases hall : ∀ a ∈ A, a ∈ N₁
      · exact ⟨1, fun b => Or.inr (Subgroup.mem_subgroupOf.mpr (hall b b.2))⟩
      · push Not at hall
        obtain ⟨s, hs, hsN⟩ := hall
        refine ⟨⟨s, hs⟩, fun b => ?_⟩
        by_cases hb : (b : MulAut W') ∈ N₁
        · exact Or.inr (Subgroup.mem_subgroupOf.mpr hb)
        · exact Or.inl (Subgroup.mem_subgroupOf.mpr (hswap _ b.2 _ hs hb hsN))
    have h1 := Subgroup.relIndex_mul_relIndex ⊥ (A ⊓ N₁) A bot_le inf_le_left
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_left] at h1
    have h2 : N₁.relIndex A ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    rw [← h1]
    calc Nat.card ↥(A ⊓ N₁) * N₁.relIndex A ≤ Nat.card ↥(A ⊓ N₁) * 2 :=
          Nat.mul_le_mul_left _ h2
      _ = 2 * Nat.card ↥(A ⊓ N₁) := mul_comm _ _
  have hfree : ∀ a ∈ A ⊓ N₁, a ≠ 1 → Nat.card (commHom a).ker = 16 := fun a ha ha1 =>
    Y.card_fix (hAH ha.1) (hA2 a ha.1) ha1 ((hNiff a ha.1).mp ha.2)
  have hkerF : ∀ a ∈ A ⊓ N₁, a ≠ 1 → (commHom a).ker = F := by
    intro a ha ha1
    have h16 := hfree a ha ha1
    have hFle : F ≤ (commHom a).ker := fun w hw => mem_ker_commHom.mpr (hw a ha.1)
    have hRF : (commHom a).range ≤ F := by
      rintro _ ⟨w, rfl⟩ b hb
      exact hq a ha.1 b hb w
    have hR : Nat.card (commHom a).range = 16 := by
      have := card_ker_mul_card_range a
      rw [h16, Y.card] at this
      omega
    have hRK : (commHom a).range = (commHom a).ker :=
      Subgroup.eq_of_le_of_card_ge (hRF.trans hFle) (by rw [hR, h16])
    refine le_antisymm ?_ hFle
    rw [← hRK]
    exact hRF
  obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a ∈ A ⊓ N₁, a ≠ 1 := by
    obtain ⟨x, hx, hx1⟩ := exists_mem_not_mem_finset (A ⊓ N₁) {1}
      (by rw [Finset.card_singleton]; omega)
    exact ⟨x, hx, by simpa using hx1⟩
  have hF16 : Nat.card F = 16 := by rw [← hkerF a₀ ha₀ ha₀1]; exact hfree a₀ ha₀ ha₀1
  have hFidx : F.index = 16 := by
    have := Subgroup.card_mul_index F
    rw [hF16, Y.card] at this
    omega
  have hpos : ∀ X : Subgroup W', 0 < X.index := fun X =>
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hA8 : 8 ≤ Nat.card A := by
    set f := (commHom a₀).comp D.subtype with hf
    have hfr : f.range ≤ Z := by
      rintro _ ⟨d, rfl⟩
      exact hDZ d d.2 a₀ ha₀.1
    have hfk : f.ker = (commHom a₀).ker.subgroupOf D := by
      ext d
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      rfl
    have h1 : ((commHom a₀).ker.subgroupOf D).index ≤ 2 := by
      rw [← hfk, Subgroup.index_ker]
      exact (Subgroup.card_le_of_le hfr).trans hZ
    have h2 := Subgroup.relIndex_mul_index (inf_le_right : (commHom a₀).ker ⊓ D ≤ D)
    rw [Subgroup.inf_relIndex_right] at h2
    have h3 : (commHom a₀).ker.index ≤ ((commHom a₀).ker ⊓ D).index :=
      Nat.le_of_dvd (hpos _) (Subgroup.index_dvd_of_le inf_le_left)
    have h4 : ((commHom a₀).ker).relIndex D ≤ 2 := h1
    rw [hkerF a₀ ha₀ ha₀1] at h2 h3 h4
    rw [hFidx] at h3
    nlinarith
  obtain ⟨b, hb, hb'⟩ := exists_mem_not_mem_finset (A ⊓ N₁) {1, a₀}
    (by have := Finset.card_le_two (a := (1 : MulAut W')) (b := a₀); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb'
  have hab : a₀ * b ∈ A ⊓ N₁ := mul_mem ha₀ hb
  have hab1 : a₀ * b ≠ 1 := by
    intro h
    apply hb'.2
    have hinv : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right (hA2 a₀ ha₀.1)
    calc b = a₀⁻¹ * (a₀ * b) := by group
      _ = a₀ := by rw [h, mul_one, hinv]
  have hDF : D ≤ F := by
    intro d hd
    set u := a₀ d * d⁻¹ with hu
    set v := b d * d⁻¹ with hv
    have huZ : u ∈ Z := hDZ d hd a₀ ha₀.1
    have hvZ : v ∈ Z := hDZ d hd b hb.1
    have huv : (a₀ * b) d * d⁻¹ = u * v := by
      have h1 : b d = v * d := by rw [hv, inv_mul_cancel_right]
      have h2 : a₀ v = v := hq b hb.1 a₀ ha₀.1 d
      calc (a₀ * b) d * d⁻¹ = a₀ (b d) * d⁻¹ := rfl
        _ = a₀ (v * d) * d⁻¹ := by rw [h1]
        _ = v * (a₀ d * d⁻¹) := by rw [map_mul, h2, mul_assoc]
        _ = u * v := by rw [mul_comm]
    by_cases hu1 : u = 1
    · rw [← hkerF a₀ ha₀ ha₀1]
      exact mem_ker_commHom.mpr (mul_inv_eq_one.mp hu1)
    by_cases hv1 : v = 1
    · rw [← hkerF b hb hb'.1]
      exact mem_ker_commHom.mpr (mul_inv_eq_one.mp hv1)
    have he := eq_of_card_le_two hZ huZ hvZ hu1 hv1
    rw [← hkerF _ hab hab1]
    refine mem_ker_commHom.mpr (mul_inv_eq_one.mp ?_)
    rw [huv, he]
    exact Y.sq v
  have hA16 : 16 ≤ Nat.card A := by
    have h1 : F.index ≤ D.index := Nat.le_of_dvd (hpos _) (Subgroup.index_dvd_of_le hDF)
    omega
  obtain ⟨z, hz, hz'⟩ := exists_mem_not_mem_finset (A ⊓ N₁) {1, a₀, b, a₀ * b}
    (by have := Finset.card_le_four (a := (1 : MulAut W')) (b := a₀) (c := b) (d := a₀ * b); omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz'
  have hkerF' : ∀ a ∈ A, a ≠ 1 → (∀ y ∈ P₁, a * y * a⁻¹ ∈ P₁) → (commHom a).ker = F :=
    fun a ha ha1 haN => hkerF a ⟨ha, (hNiff a ha).mpr haN⟩ ha1
  have hN' : ∀ {a}, a ∈ A ⊓ N₁ → ∀ y ∈ P₁, a * y * a⁻¹ ∈ P₁ := fun {a} ha =>
    (hNiff a ha.1).mp ha.2
  by_cases hC2 : ∀ c ∈ A, (∀ y ∈ P₂, c * y = y * c) → c = 1
  · rcases Y.mem_four hAH hAc hA2 hC2 ha₀.1 (hN' ha₀) ha₀1 hb.1 (hN' hb) hb'.1
        (Ne.symm hb'.2) hz.1 (hN' hz) with h | h | h | h
    · exact hz'.1 h
    · exact hz'.2.1 h
    · exact hz'.2.2.1 h
    · exact hz'.2.2.2 h
  · push Not at hC2
    obtain ⟨c₁, hc₁, hc₁c, hc₁1⟩ := hC2
    have hC1 : ∀ c ∈ A, (∀ y ∈ P₁, c * y = y * c) → c = 1 := by
      intro c hc hcc
      by_contra hc1
      exact Y.not_both hAH hF16 hkerF' hc₁ hc₁1 hc₁c hc hc1 hcc
    have hN₂ : ∀ {a}, a ∈ A ⊓ N₁ → ∀ y ∈ P₂, a * y * a⁻¹ ∈ P₂ := fun {a} ha =>
      Y.conj_mem₂ (hAH ha.1) (hN' ha)
    rcases Y.symm.mem_four hAH hAc hA2 hC1 ha₀.1 (hN₂ ha₀) ha₀1 hb.1 (hN₂ hb) hb'.1
        (Ne.symm hb'.2) hz.1 (hN₂ hz) with h | h | h | h
    · exact hz'.1 h
    · exact hz'.2.1 h
    · exact hz'.2.2.1 h
    · exact hz'.2.2.2 h

end WrData

end CFSG.Quasithin.H13.L32A.L2
