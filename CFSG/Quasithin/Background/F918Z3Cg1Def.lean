module

public import CFSG.Quasithin.Background.F918Z4bL2

public section

namespace CFSG.Quasithin

namespace Z3Cg1

section Join

variable {Γ : Type*} [Group Γ]

theorem exists_mul_of_mem_sup {D X : Subgroup Γ} (hc : ∀ d ∈ D, ∀ x ∈ X, d * x = x * d) {z : Γ}
    (hz : z ∈ D ⊔ X) : ∃ d ∈ D, ∃ x ∈ X, z = d * x := by
  let S : Subgroup Γ :=
    { carrier := {z | ∃ d ∈ D, ∃ x ∈ X, z = d * x}
      one_mem' := ⟨1, D.one_mem, 1, X.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨d, hd, x, hx, rfl⟩ ⟨d', hd', x', hx', rfl⟩
        refine ⟨d * d', D.mul_mem hd hd', x * x', X.mul_mem hx hx', ?_⟩
        calc d * x * (d' * x') = d * (x * d') * x' := by group
          _ = d * (d' * x) * x' := by rw [← hc d' hd' x hx]
          _ = d * d' * (x * x') := by group
      inv_mem' := by
        rintro _ ⟨d, hd, x, hx, rfl⟩
        refine ⟨d⁻¹, D.inv_mem hd, x⁻¹, X.inv_mem hx, ?_⟩
        have h : Commute d x := hc d hd x hx
        rw [mul_inv_rev, h.inv_inv.eq] }
  have hle : D ⊔ X ≤ S :=
    sup_le (fun d hd => ⟨d, hd, 1, X.one_mem, (mul_one d).symm⟩)
      (fun x hx => ⟨1, D.one_mem, x, hx, (one_mul x).symm⟩)
  exact hle hz

end Join

section ConjRes

variable {Γ : Type*} [Group Γ]

@[expose] def conjRes (D A : Subgroup Γ) (h : ∀ b ∈ A, ∀ y ∈ D, b * y * b⁻¹ ∈ D) :
    ↥A →* MulAut ↥D where
  toFun b :=
    { toFun := fun y => ⟨(b : Γ) * y * (b : Γ)⁻¹, h b b.2 y y.2⟩
      invFun := fun y => ⟨(b : Γ)⁻¹ * y * (b : Γ), by
        simpa using h (b : Γ)⁻¹ (A.inv_mem b.2) y y.2⟩
      left_inv := fun y => by ext; simp [mul_assoc]
      right_inv := fun y => by ext; simp [mul_assoc]
      map_mul' := fun y z => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' b c := by ext y; simp [mul_assoc]

variable {D A : Subgroup Γ} {h : ∀ b ∈ A, ∀ y ∈ D, b * y * b⁻¹ ∈ D}

theorem conjRes_eq_one_iff (b : ↥A) :
    conjRes D A h b = 1 ↔ ∀ y ∈ D, (b : Γ) * y = y * b := by
  constructor
  · intro hb y hy
    have h1 := congrArg (fun φ : MulAut ↥D => ((φ ⟨y, hy⟩ : ↥D) : Γ)) hb
    have h2 : (b : Γ) * y * (b : Γ)⁻¹ = y := h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  · intro H
    ext y
    show (b : Γ) * y * (b : Γ)⁻¹ = y
    rw [mul_inv_eq_iff_eq_mul]
    exact H y y.2

theorem conjRes_eq_conj_iff (b : ↥A) (g : ↥D) :
    conjRes D A h b = MulAut.conj g ↔
      ∀ y ∈ D, (b : Γ) * y * (b : Γ)⁻¹ = (g : Γ) * y * (g : Γ)⁻¹ := by
  constructor
  · intro hb y hy
    have h1 := congrArg (fun φ : MulAut ↥D => ((φ ⟨y, hy⟩ : ↥D) : Γ)) hb
    exact h1
  · intro H
    ext y
    exact H y y.2

end ConjRes

section Rank

theorem isElemAb2_range {Γ : Type*} [Group Γ] {A : Subgroup Γ} (hA : IsElemAb2 A) {Δ : Type*}
    [Group Δ] (f : ↥A →* Δ) : IsElemAb2 f.range := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have hxy : x * y = y * x := Subtype.ext (hA.1 x x.2 y y.2)
    rw [← map_mul, ← map_mul, hxy]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (hA.2 x x.2), map_one]

variable {G H₁ H₂ : Type*} [Group G] [Group H₁] [Group H₂] [Finite H₁] [Finite H₂]

theorem card_le_of_pair_injective (f₁ : G →* H₁) (f₂ : G →* H₂)
    (hinj : ∀ b, f₁ b = 1 → f₂ b = 1 → b = 1) :
    Nat.card G ≤ Nat.card f₁.range * Nat.card f₂.range := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun b : G => (⟨f₁ b, b, rfl⟩, ⟨f₂ b, b, rfl⟩)) ?_
  intro b c hbc
  have h1 : f₁ b = f₁ c := congrArg (fun p => (p.1 : H₁)) hbc
  have h2 : f₂ b = f₂ c := congrArg (fun p => (p.2 : H₂)) hbc
  have : b⁻¹ * c = 1 := hinj _ (by rw [map_mul, map_inv, h1, inv_mul_cancel])
    (by rw [map_mul, map_inv, h2, inv_mul_cancel])
  exact (inv_mul_eq_one.1 this)

theorem rk_le_add_of_pair_injective [Finite G] (hG : IsPGroup 2 G) (f₁ : G →* H₁) (f₂ : G →* H₂)
    (hinj : ∀ b, f₁ b = 1 → f₂ b = 1 → b = 1) : rk G ≤ rk f₁.range + rk f₂.range := by
  have h1 : IsPGroup 2 ↥f₁.range := hG.of_surjective f₁.rangeRestrict f₁.rangeRestrict_surjective
  have h2 : IsPGroup 2 ↥f₂.range := hG.of_surjective f₂.rangeRestrict f₂.rangeRestrict_surjective
  have := card_le_of_pair_injective f₁ f₂ hinj
  rw [card_eq_two_pow_of_isPGroup hG, card_eq_two_pow_of_isPGroup h1,
    card_eq_two_pow_of_isPGroup h2, ← pow_add] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

theorem exists_of_pair_rk_le [Finite G] (hG : IsPGroup 2 G) (f₁ : G →* H₁) (f₂ : G →* H₂)
    (hinj : ∀ b, f₁ b = 1 → f₂ b = 1 → b = 1) (hrk : rk f₁.range + rk f₂.range ≤ rk G)
    (e₁ : ↥f₁.range) (e₂ : ↥f₂.range) : ∃ b : G, f₁ b = e₁ ∧ f₂ b = e₂ := by
  have h1 : IsPGroup 2 ↥f₁.range := hG.of_surjective f₁.rangeRestrict f₁.rangeRestrict_surjective
  have h2 : IsPGroup 2 ↥f₂.range := hG.of_surjective f₂.rangeRestrict f₂.rangeRestrict_surjective
  let F : G → ↥f₁.range × ↥f₂.range :=
    fun b => (⟨f₁ b, b, rfl⟩, ⟨f₂ b, b, rfl⟩)
  have hF : Function.Injective F := by
    intro b c hbc
    have h1 : f₁ b = f₁ c := congrArg (fun p => (p.1 : H₁)) hbc
    have h2 : f₂ b = f₂ c := congrArg (fun p => (p.2 : H₂)) hbc
    have : b⁻¹ * c = 1 := hinj _ (by rw [map_mul, map_inv, h1, inv_mul_cancel])
      (by rw [map_mul, map_inv, h2, inv_mul_cancel])
    exact (inv_mul_eq_one.1 this)
  have hcard : Nat.card (↥f₁.range × ↥f₂.range) ≤ Nat.card G := by
    rw [Nat.card_prod, card_eq_two_pow_of_isPGroup hG, card_eq_two_pow_of_isPGroup h1,
      card_eq_two_pow_of_isPGroup h2, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) hrk
  obtain ⟨b, hb⟩ := (hF.bijective_of_nat_card_le hcard).2 (e₁, e₂)
  exact ⟨b, congrArg (fun p => (p.1 : H₁)) hb, congrArg (fun p => (p.2 : H₂)) hb⟩

end Rank

section Inner

theorem rkIdx_comap_inner_le {L : Type} [Group L] [Finite L] {n : ℕ} (hn : 2 ≤ n)
    (hL : IsPSL 2 2 n L) {G' : Type*} [Group G'] (f : G' →* MulAut L) (hf : IsElemAb2 f.range) :
    rkIdx ((MulAut.conj : L →* MulAut L).range.comap f) ≤ 1 := by
  set Inn : Subgroup (MulAut L) := (MulAut.conj : L →* MulAut L).range with hInn
  have h1 : rk f.range ≤ rk ↥(f.range ⊓ Inn) + 1 := rk_le_rk_inf_inner_add_one hn hL hf
  have h2 := Subgroup.relIndex_mul_card Inn f.range
  rw [inf_comm] at h2
  have hne : Inn.relIndex f.range ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (Nat.card_pos (α := ↥f.range)).ne' h2.symm
  unfold rkIdx
  rw [Subgroup.index_comap]
  have h3 := congrArg (padicValNat 2) h2
  rw [padicValNat.mul hne (card_subgroup_pos _).ne'] at h3
  unfold rk at h1
  omega

end Inner

section Subgroups

variable {G : Type*} [Group G] [Finite G]

theorem card_mul_card_le_of_inf_eq_bot {B₁ B₂ : Subgroup G} (h : B₁ ⊓ B₂ = ⊥) :
    Nat.card B₁ * Nat.card B₂ ≤ Nat.card G := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p : B₁ × B₂ => (p.1 : G) * (p.2 : G)) ?_
  rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
  have hxy' : (x : G) * y = x' * y' := hxy
  have h1 : (x' : G)⁻¹ * x = y' * (y : G)⁻¹ := by
    calc (x' : G)⁻¹ * x = (x' : G)⁻¹ * (x * y) * (y : G)⁻¹ := by group
      _ = y' * (y : G)⁻¹ := by rw [hxy']; group
  have h2 : (x' : G)⁻¹ * x ∈ B₁ ⊓ B₂ :=
    ⟨B₁.mul_mem (B₁.inv_mem x'.2) x.2, by rw [h1]; exact B₂.mul_mem y'.2 (B₂.inv_mem y.2)⟩
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at h2
  have h3 : (y : G) = y' := by
    rw [h2] at hxy'
    exact mul_left_cancel hxy'
  exact Prod.ext (Subtype.ext h2.symm) (Subtype.ext h3)

theorem rk_add_rk_le_of_inf_eq_bot (hG : IsPGroup 2 G) {B₁ B₂ : Subgroup G} (h : B₁ ⊓ B₂ = ⊥) :
    rk B₁ + rk B₂ ≤ rk G := by
  have := card_mul_card_le_of_inf_eq_bot h
  rw [card_eq_two_pow_of_isPGroup (hG.to_subgroup B₁),
    card_eq_two_pow_of_isPGroup (hG.to_subgroup B₂), card_eq_two_pow_of_isPGroup hG,
    ← pow_add] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

omit [Finite G] in
theorem ne_top_of_rk_lt {B : Subgroup G} (h : rk B < rk G) : B ≠ ⊤ := by
  rintro rfl
  exact lt_irrefl _ (rk_top (G := G) ▸ h)

omit [Finite G] in
theorem exists_not_mem_of_rk_lt {B₁ B₂ : Subgroup G} (h₁ : rk B₁ < rk G)
    (h₂ : rk B₂ < rk G) : ∃ b : G, b ∉ B₁ ∧ b ∉ B₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu⟩ : ∃ u : G, u ∉ B₁ := by
    by_contra h'
    push Not at h'
    exact ne_top_of_rk_lt h₁ (Subgroup.eq_top_iff' _ |>.2 h')
  obtain ⟨w, hw⟩ : ∃ w : G, w ∉ B₂ := by
    by_contra h'
    push Not at h'
    exact ne_top_of_rk_lt h₂ (Subgroup.eq_top_iff' _ |>.2 h')
  have hu2 : u ∈ B₂ := hcon u hu
  have hw1 : w ∈ B₁ := by
    by_contra hw1
    exact hw (hcon w hw1)
  by_cases huw : u * w ∈ B₁
  · exact hu (by simpa using B₁.mul_mem huw (B₁.inv_mem hw1))
  · exact hw (by simpa using B₂.mul_mem (B₂.inv_mem hu2) (hcon _ huw))

end Subgroups

end Z3Cg1

end CFSG.Quasithin
