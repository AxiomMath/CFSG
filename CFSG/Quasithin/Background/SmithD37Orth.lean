module

public import CFSG.Quasithin.Background.SmithD37Flag
public import CFSG.Quasithin.Background.SmithD37Swap

public section

namespace CFSG.Quasithin.SmithD37

open scoped Matrix

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)}

theorem card_mul_card_le_of_inf_eq_bot {A C₁ C₂ : Subgroup (MulAut U)} [Finite ↥A]
    (h₁ : C₁ ≤ A) (h₂ : C₂ ≤ A) (hinf : C₁ ⊓ C₂ = ⊥) :
    Nat.card C₁ * Nat.card C₂ ≤ Nat.card A := by
  let f : ↥C₁ × ↥C₂ → ↥A := fun p => ⟨p.1 * p.2, A.mul_mem (h₁ p.1.2) (h₂ p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h1 : (x : MulAut U) * y = x' * y' := congrArg Subtype.val h
    have h2 : (x' : MulAut U)⁻¹ * x = y' * (y : MulAut U)⁻¹ := by
      calc (x' : MulAut U)⁻¹ * x = (x' : MulAut U)⁻¹ * (x * y) * (y : MulAut U)⁻¹ := by group
        _ = (x' : MulAut U)⁻¹ * (x' * y') * (y : MulAut U)⁻¹ := by rw [h1]
        _ = y' * (y : MulAut U)⁻¹ := by group
    have h3 : (x' : MulAut U)⁻¹ * x ∈ C₁ ⊓ C₂ :=
      ⟨C₁.mul_mem (C₁.inv_mem x'.2) x.2, h2 ▸ C₂.mul_mem y'.2 (C₂.inv_mem y.2)⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h3
    have h4 : (y : MulAut U) = y' := by
      rw [← h3] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext h4)
  have : Finite (↥C₁ × ↥C₂) := Finite.of_injective f hf
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective f hf

section Mat

variable {F : Type} [Field F] {d : ℕ}

theorem eq_bot_of_fix (Mm : MatModel L₁ L₂ F d) {C₁ C₂ : Subgroup (MulAut U)}
    (h₁ : ∀ c ∈ C₁, ∀ l ∈ L₁, c * l = l * c) (h₂ : ∀ g ∈ C₂, ∀ k ∈ L₂, g * k = k * g)
    (hfix : fixV C₂ ≤ fixV C₁) (hne : fixV C₂ ≠ ⊥) : C₁ = ⊥ := by
  classical
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨X₀, hX₀⟩ := x
  have hX₀1 : X₀ ≠ 1 := fun h => hx (Subtype.ext h)
  set B₀ := Multiplicative.toAdd (Mm.β X₀) with hB₀
  have hB₀ne : B₀ ≠ 0 := by
    intro h
    apply hX₀1
    rw [← Mm.β.map_eq_one_iff, ← ofAdd_toAdd (Mm.β X₀), ← hB₀, h, ofAdd_zero]
  obtain ⟨a, b, hab⟩ : ∃ a b, B₀ a b ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hB₀ne (Matrix.ext hc)
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  obtain ⟨M, hM⟩ := exists_right_mul Mm (h₁ c hc)
  have hmem : ∀ N : Matrix (Fin d) (Fin d) F,
      Mm.β.symm (Multiplicative.ofAdd (B₀ * N)) ∈ fixV C₂ := by
    intro N g hg
    obtain ⟨D, hD⟩ := exists_left_mul Mm (h₂ g hg)
    have hDB : D * B₀ = B₀ := by
      rw [hB₀, ← hD, hX₀ g hg]
    apply Mm.β.injective
    rw [← ofAdd_toAdd (Mm.β (g _)), hD, MulEquiv.apply_symm_apply, toAdd_ofAdd, ← mul_assoc,
      hDB]
  have hBNM : ∀ N : Matrix (Fin d) (Fin d) F, B₀ * N * M = B₀ * N := by
    intro N
    have h := hM (Mm.β.symm (Multiplicative.ofAdd (B₀ * N)))
    rw [hfix (hmem N) c hc, MulEquiv.apply_symm_apply, toAdd_ofAdd] at h
    exact h.symm
  have hM1 : M = 1 := by
    ext k j
    have h := congrFun (congrFun (hBNM (Matrix.single b k 1)) a) j
    simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero,
      Finset.mem_univ, ite_true, ite_mul, zero_mul, Finset.sum_ite_eq, ite_and] at h
    rw [Matrix.one_apply]
    by_cases hkj : k = j
    · subst hkj
      simp only [ite_true] at h
      simpa using mul_left_cancel₀ hab (h.trans (mul_one _).symm)
    · simp only [hkj, ite_false] at h ⊢
      exact (mul_eq_zero.mp h).resolve_left hab
  apply MulEquiv.ext
  intro u
  apply Mm.β.injective
  rw [← ofAdd_toAdd (Mm.β (c u)), hM, hM1, mul_one, ofAdd_toAdd, MulAut.one_apply]

end Mat

section Orth

variable [Finite U] {X : Subgroup (MulAut U)} {s : MulAut U} {F : Type} [Field F] [Fintype F]
  [CharP F 2]

omit [Finite U] [Fintype F] [CharP F 2] in
theorem natCard_eq_of_matModel {d : ℕ} (Mm : MatModel L₁ L₂ F d) :
    Nat.card U = Nat.card F ^ (d * d) := by
  rw [Nat.card_congr (Mm.β.toEquiv.trans Multiplicative.toAdd), Matrix.card_matrix,
    Nat.card_fin]

theorem false_of_orth
    (hC : Core X L₁ L₂ s) (Mm : MatModel L₁ L₂ F 4) {n : ℕ}
    (hL : IsPSL 2 2 n ↥L₁) {A : Subgroup (MulAut U)} (hA2 : IsA2 X A) (hAr : rAV A ≤ 2)
    (hAN : ∀ a ∈ A, a ∈ Subgroup.normalizer (L₁ : Set (MulAut U))) : False := by
  have hE := hA2.2.2
  have hPN₁ : ∀ a ∈ A, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁ := fun a ha l hl =>
    mul_mem_of_mem_normalizer (hAN a ha) hl
  have hPN₂ : ∀ a ∈ A, ∀ k ∈ L₂, a * k * a⁻¹ ∈ L₂ := fun a ha k hk =>
    mul_mem_of_mem_normalizer (hC.mem_normalizer₂ (hA2.1 ha) (hAN a ha)) hk
  have hC' := hC.swap
  have hL₂ : IsPSL 2 2 n ↥L₂ := isPSL_transfer hC.equiv.symm hL
  have hnc₁ := Mm.not_comm (by norm_num)
  have hnc₂ := Mm.swap.not_comm (by norm_num)
  have hrank : Module.finrank F (⊤ : Submodule F (Fin 4 → F)) = 4 := by
    rw [finrank_top, Module.finrank_fin_fun]
  have htop : ∀ P : Subgroup (MulAut U), IsInvBy P (⊤ : Subgroup U) := fun _ _ _ _ _ =>
    Subgroup.mem_top _
  have hflag₁ := card_fixV_flag Mm (by norm_num) hC.simple hnc₁ hC.sqtk hL hE hPN₁ 4 ⊤ hrank
    (by rw [rowSub_top]; exact htop A)
  have hflag₂ := card_fixV_flag Mm.swap (by norm_num) hC'.simple hnc₂ hC'.sqtk hL₂ hE hPN₂ 4 ⊤
    hrank (by rw [rowSub_top]; exact htop A)
  rw [rowSub_top, top_inf_eq] at hflag₁ hflag₂
  have hU := natCard_eq_of_matModel Mm
  have hr := card_le_sq_mul_fixV hC.exp hA2 hAr
  set C₁ := A ⊓ Subgroup.centralizer (L₁ : Set (MulAut U)) with hC₁
  set C₂ := A ⊓ Subgroup.centralizer (L₂ : Set (MulAut U)) with hC₂
  have hcomm₁ : ∀ c ∈ C₁, ∀ l ∈ L₁, c * l = l * c := fun c hc l hl =>
    (Subgroup.mem_centralizer_iff.mp hc.2 l hl).symm
  have hcomm₂ : ∀ c ∈ C₂, ∀ k ∈ L₂, c * k = k * c := fun c hc k hk =>
    (Subgroup.mem_centralizer_iff.mp hc.2 k hk).symm
  have hinf : C₁ ⊓ C₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact eq_one_of_comm Mm (hcomm₁ x hx.1) (hcomm₂ x hx.2) (e := 1)
      (by rw [pow_one]; exact hE.2 x hx.1.1)
  have hprod := card_mul_card_le_of_inf_eq_bot (inf_le_left : C₁ ≤ A) inf_le_left hinf
  set a := Nat.card A
  set c₁ := Nat.card C₁
  set c₂ := Nat.card C₂
  set f := Nat.card (fixV A)
  set Q := Nat.card F ^ (4 * 4)
  have hf : 0 < f := Nat.card_pos
  have ha : 0 < a := Nat.card_pos
  have hc₁ : 0 < c₁ := Nat.card_pos
  have hc₂ : 0 < c₂ := Nat.card_pos
  have hac : ∀ c, 0 < c → f * a ^ 4 ≤ Q * c ^ 4 → a ≤ c ^ 2 := by
    intro c _ h
    have h1 : f * a ^ 2 * a ^ 2 ≤ f * a ^ 2 * (c ^ 2) ^ 2 :=
      calc f * a ^ 2 * a ^ 2 = f * a ^ 4 := by ring
        _ ≤ Q * c ^ 4 := h
        _ ≤ a ^ 2 * f * c ^ 4 := Nat.mul_le_mul_right _ (hU ▸ hr)
        _ = f * a ^ 2 * (c ^ 2) ^ 2 := by ring
    have h2 := Nat.le_of_mul_le_mul_left h1 (by positivity)
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h2
  have ha₁ := hac c₁ hc₁ hflag₁
  have ha₂ := hac c₂ hc₂ hflag₂
  have hc12 : c₁ = c₂ := by
    apply le_antisymm
    · have : c₁ * c₂ ≤ c₂ * c₂ := by nlinarith
      exact Nat.le_of_mul_le_mul_right this hc₂
    · have : c₁ * c₂ ≤ c₁ * c₁ := by nlinarith
      exact Nat.le_of_mul_le_mul_left this hc₁
  have hac2 : a = c₂ ^ 2 := by
    refine le_antisymm ha₂ ?_
    calc c₂ ^ 2 = c₁ * c₂ := by rw [hc12]; ring
      _ ≤ a := hprod
  have hfQ : f * c₂ ^ 4 = Q := by
    apply le_antisymm
    · have h1 : f * c₂ ^ 4 * c₂ ^ 4 ≤ Q * c₂ ^ 4 :=
        calc f * c₂ ^ 4 * c₂ ^ 4 = f * a ^ 4 := by rw [hac2]; ring
          _ ≤ Q * c₂ ^ 4 := hflag₂
      exact Nat.le_of_mul_le_mul_right h1 (by positivity)
    · calc Q = Nat.card U := hU.symm
        _ ≤ a ^ 2 * f := hr
        _ = f * c₂ ^ 4 := by rw [hac2]; ring
  have hE₂ : IsElemAbelian2 C₂ :=
    ⟨fun x hx y hy => hE.1 x hx.1 y hy.1, fun x hx => hE.2 x hx.1⟩
  have hflag₃ := card_fixV_flag Mm (by norm_num) hC.simple hnc₁ hC.sqtk hL hE₂
    (fun x hx => hPN₁ x hx.1) 4 ⊤ hrank (by rw [rowSub_top]; exact htop C₂)
  rw [rowSub_top, top_inf_eq] at hflag₃
  have hC2c : C₂ ⊓ Subgroup.centralizer (L₁ : Set (MulAut U)) = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    intro x hx
    exact ⟨⟨hx.1.1, hx.2⟩, hx.1⟩
  rw [hC2c, Subgroup.card_bot, one_pow, mul_one] at hflag₃
  have hle : fixV A ≤ fixV C₂ := fixV_anti inf_le_left
  have heq : fixV A = fixV C₂ := by
    apply Subgroup.eq_of_le_of_card_ge hle
    have : Nat.card (fixV C₂) * c₂ ^ 4 ≤ f * c₂ ^ 4 := by rw [hfQ]; exact hflag₃
    exact Nat.le_of_mul_le_mul_right this (by positivity)
  have hnt : Nontrivial U := hC.nt
  have hfix₂ : fixV C₂ ≠ ⊥ := by
    intro h
    have h2 := two_le_card_fixV hC.exp hE₂.isPGroup
    rw [h, Subgroup.card_bot] at h2
    omega
  have hC₁bot : C₁ = ⊥ := eq_bot_of_fix Mm hcomm₁ hcomm₂
    (heq ▸ fixV_anti (inf_le_left : C₁ ≤ A)) hfix₂
  have h1 : c₁ = 1 := by
    show Nat.card C₁ = 1
    rw [hC₁bot, Subgroup.card_bot]
  have h2 : a = 1 := by rw [hac2, ← hc12, h1]; norm_num
  exact hA2.2.1 (Subgroup.eq_bot_of_card_eq A h2)

end Orth

end CFSG.Quasithin.SmithD37
