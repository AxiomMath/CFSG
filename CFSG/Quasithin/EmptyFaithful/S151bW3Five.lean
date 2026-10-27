module

public import CFSG.Quasithin.EmptyFaithful.S151bW3Mod

public section

namespace CFSG.Quasithin

section Abstract

variable {Γ : Type*} [Group Γ]

theorem sign_of_sq_five151b {a g : Γ} (ha : orderOf a = 5) (hg2 : g ^ 2 = 1)
    (h : g * a * g⁻¹ ∈ Subgroup.zpowers a) : g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hgg : g * g = 1 := by rw [← pow_two]; exact hg2
  have h1 : a ^ (k * k) = a ^ (1 : ℤ) := by
    have e1 : g * (g * a * g⁻¹) * g⁻¹ = a := by
      calc g * (g * a * g⁻¹) * g⁻¹ = (g * g) * a * (g * g)⁻¹ := by group
        _ = a := by rw [hgg]; group
    have e2 : g * (g * a * g⁻¹) * g⁻¹ = a ^ (k * k) := by
      rw [← hk, ← conj_zpow, ← hk, ← zpow_mul]
    rw [← e2, e1, zpow_one]
  have h2 : (k * k : ℤ) ≡ 1 [ZMOD (orderOf a : ℤ)] := zpow_eq_zpow_iff_modEq.mp h1
  rw [ha] at h2
  have h3 : ((k : ZMod 5) * (k : ZMod 5)) = 1 := by
    have := (ZMod.intCast_eq_intCast_iff (k * k) 1 5).mpr h2
    simpa using this
  have h4 : (k : ZMod 5) = 1 ∨ (k : ZMod 5) = 4 := by
    revert h3; generalize (k : ZMod 5) = x; revert x; decide
  have ha5 : a ^ 5 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  rcases h4 with h4 | h4
  · left
    rw [← hk]
    have hmod : (k : ℤ) ≡ 1 [ZMOD 5] := (ZMod.intCast_eq_intCast_iff k 1 5).mp (by simpa using h4)
    have h5 : a ^ k = a ^ (1 : ℤ) := zpow_eq_zpow_iff_modEq.mpr (by rw [ha]; exact_mod_cast hmod)
    rw [h5, zpow_one]
  · right
    rw [← hk]
    have hmod : (k : ℤ) ≡ 4 [ZMOD 5] := (ZMod.intCast_eq_intCast_iff k 4 5).mp (by simpa using h4)
    have h5 : a ^ k = a ^ (4 : ℤ) := zpow_eq_zpow_iff_modEq.mpr (by rw [ha]; exact_mod_cast hmod)
    rw [h5]
    have h6 : a ^ (5 : ℤ) = 1 := by exact_mod_cast ha5
    have h7 : a ^ (4 : ℤ) * a = 1 := by
      rw [← h6, show (5 : ℤ) = 4 + 1 by norm_num, zpow_add, zpow_one]
    exact eq_inv_of_mul_eq_one_left h7

theorem inv_ne_self_of_order_five151b {a : Γ} (ha : orderOf a = 5) : a⁻¹ ≠ a := by
  intro h
  have h2 : a ^ 2 = 1 := by
    rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr h.symm
  have := orderOf_dvd_of_pow_eq_one h2
  rw [ha] at this
  omega

theorem mixed_sign_false151b {a b f g : Γ} (hb5 : b ^ 5 = 1) (hfa : f * a * f⁻¹ ∈ Subgroup.zpowers b)
    (hga : g * a * g⁻¹ = a) (hgb : g * b * g⁻¹ = b⁻¹) (hfg : g * f = f * g) : a = 1 := by
  set y := f * a * f⁻¹ with hy
  have hgy : g * y * g⁻¹ = y⁻¹ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hfa
    rw [← hk, ← conj_zpow, hgb, inv_zpow]
  have hgy2 : g * y * g⁻¹ = y := by
    calc g * y * g⁻¹ = (g * f) * a * (g * f)⁻¹ := by rw [hy]; group
      _ = (f * g) * a * (f * g)⁻¹ := by rw [hfg]
      _ = f * (g * a * g⁻¹) * f⁻¹ := by group
      _ = y := by rw [hga]
  have hyy : y = y⁻¹ := hgy2.symm.trans hgy
  have hy2 : y ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr hyy
  have hy5 : y ^ 5 = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hfa
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [hb5]
  have hy1 : y = 1 := by
    have : y = y ^ 5 * (y ^ 2)⁻¹ ^ 2 := by group
    rw [this, hy5, hy2]; simp
  have : a = f⁻¹ * y * f := by rw [hy]; group
  rw [this, hy1]; group

end Abstract
namespace SixData151b

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

omit [Finite W] in
theorem orderOf_a₁_five : orderOf S.a₁ = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (S.a₁_pow (Or.inr rfl)) (S.a₁_ne_one (Or.inr rfl))

omit [Finite W] in
theorem orderOf_a₂_five : orderOf S.a₂ = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (S.a₂_pow (Or.inr rfl)) (S.a₂_ne_one (Or.inr rfl))

theorem eq_of_conj_eq (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {E : Subgroup (MulAut W)} (hE : IsElemAbelian2 E) {g h : MulAut W} (hg : g ∈ E) (hh : h ∈ E)
    (h1 : g * S.a₁ * g⁻¹ = h * S.a₁ * h⁻¹) (h2 : g * S.a₂ * g⁻¹ = h * S.a₂ * h⁻¹) : g = h := by
  have hg2 : g ^ 2 = 1 := hE.2 g hg
  have hh2 : h ^ 2 = 1 := hE.2 h hh
  have hgg : g * g = 1 := by rw [← pow_two]; exact hg2
  have hhh : h * h = 1 := by rw [← pow_two]; exact hh2
  have hd : (g * h) ^ 2 = 1 := hE.2 _ (E.mul_mem hg hh)
  have key : ∀ a : MulAut W, g * a * g⁻¹ = h * a * h⁻¹ → (g * h) * a = a * (g * h) := by
    intro a hga
    have : g * h * a * (g * h)⁻¹ = a := by
      calc g * h * a * (g * h)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ := by group
        _ = g * (g * a * g⁻¹) * g⁻¹ := by rw [hga]
        _ = (g * g) * a * (g * g)⁻¹ := by group
        _ = a := by rw [hgg]; group
    calc g * h * a = (g * h * a * (g * h)⁻¹) * (g * h) := by group
      _ = a * (g * h) := by rw [this]
  have := S.eq_one_of_commute_involution hW hcard rfl hd (key S.a₁ h1) (key S.a₂ h2)
  have hgh : g = h⁻¹ := eq_inv_of_mul_eq_one_left this
  rw [hgh]
  exact inv_eq_of_mul_eq_one_right hhh

theorem card_le_four_of_elemAbelian (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {E : Subgroup (MulAut W)} (hE : IsElemAbelian2 E)
    (hnorm : ∀ g ∈ E, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) : Nat.card E ≤ 4 := by
  classical
  have hp : (5 : ℕ) = 3 ∨ (5 : ℕ) = 5 := Or.inr rfl
  have ho₁ := S.orderOf_a₁_five
  have ho₂ := S.orderOf_a₂_five
  have hI_or : ∀ g : E, S.TypeI g.1 ∨ S.TypeII g.1 := fun g =>
    S.typeI_or_typeII hp hW (hnorm g.1 g.2)
  have hsq : ∀ g : E, g.1 ^ 2 = 1 := fun g => hE.2 g.1 g.2
  have hsign₁ : ∀ g : E, S.TypeI g.1 →
      (g.1 * S.a₁ * g.1⁻¹ = S.a₁ ∨ g.1 * S.a₁ * g.1⁻¹ = S.a₁⁻¹) := fun g hg =>
    sign_of_sq_five151b ho₁ (hsq g) hg.1
  have hsign₂ : ∀ g : E, S.TypeI g.1 →
      (g.1 * S.a₂ * g.1⁻¹ = S.a₂ ∨ g.1 * S.a₂ * g.1⁻¹ = S.a₂⁻¹) := fun g hg =>
    sign_of_sq_five151b ho₂ (hsq g) hg.2
  have hne₁ := inv_ne_self_of_order_five151b ho₁
  have hne₂ := inv_ne_self_of_order_five151b ho₂
  have conj_eq : ∀ (a : MulAut W) (g h : MulAut W), a⁻¹ ≠ a →
      (g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹) → (h * a * h⁻¹ = a ∨ h * a * h⁻¹ = a⁻¹) →
      (g * a * g⁻¹ = a ↔ h * a * h⁻¹ = a) → g * a * g⁻¹ = h * a * h⁻¹ := by
    intro a g h hne hg hh hiff
    rcases hg with hg | hg
    · rw [hg, (hiff.mp hg)]
    · have : ¬ (g * a * g⁻¹ = a) := by rw [hg]; exact hne
      have hh' : ¬ (h * a * h⁻¹ = a) := fun e => this (hiff.mpr e)
      rw [hg]
      rcases hh with hh | hh
      · exact absurd hh hh'
      · exact hh.symm
  have hsplit : Nat.card E = Nat.card {g : E // S.TypeI g.1} + Nat.card {g : E // ¬ S.TypeI g.1} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun g : E => S.TypeI g.1)).symm
  by_cases hT₂ : IsEmpty {g : E // ¬ S.TypeI g.1}
  · have h0 : Nat.card {g : E // ¬ S.TypeI g.1} = 0 := Nat.card_of_isEmpty
    rw [hsplit, h0, add_zero]
    have hinj : Function.Injective (fun g : {g : E // S.TypeI g.1} =>
        (decide (g.1.1 * S.a₁ * g.1.1⁻¹ = S.a₁), decide (g.1.1 * S.a₂ * g.1.1⁻¹ = S.a₂))) := by
      intro g h hgh
      simp only [Prod.mk.injEq, decide_eq_decide] at hgh
      apply Subtype.ext
      apply Subtype.ext
      exact S.eq_of_conj_eq hW hcard hE g.1.2 h.1.2
        (conj_eq S.a₁ g.1.1 h.1.1 hne₁ (hsign₁ g.1 g.2) (hsign₁ h.1 h.2) hgh.1)
        (conj_eq S.a₂ g.1.1 h.1.1 hne₂ (hsign₂ g.1 g.2) (hsign₂ h.1 h.2) hgh.2)
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  · rw [not_isEmpty_iff] at hT₂
    obtain ⟨⟨f, hfI⟩⟩ := hT₂
    have hfII : S.TypeII f.1 := (hI_or f).resolve_left hfI
    have hle : Nat.card {g : E // ¬ S.TypeI g.1} ≤ Nat.card {g : E // S.TypeI g.1} := by
      refine Nat.card_le_card_of_injective
        (fun g : {g : E // ¬ S.TypeI g.1} =>
          (⟨⟨f.1 * g.1.1, E.mul_mem f.2 g.1.2⟩,
            S.typeI_mul_of_typeII hfII ((hI_or g.1).resolve_left g.2)⟩ : {g : E // S.TypeI g.1})) ?_
      intro g h hgh
      have := congrArg (fun x : {g : E // S.TypeI g.1} => x.1.1) hgh
      apply Subtype.ext
      apply Subtype.ext
      exact mul_left_cancel this
    have hsame : ∀ g : E, S.TypeI g.1 →
        (g.1 * S.a₁ * g.1⁻¹ = S.a₁ ↔ g.1 * S.a₂ * g.1⁻¹ = S.a₂) := by
      intro g hg
      have hfg : g.1 * f.1 = f.1 * g.1 := hE.1 g.1 g.2 f.1 f.2
      rcases hsign₁ g hg with h1 | h1 <;> rcases hsign₂ g hg with h2 | h2
      · exact ⟨fun _ => h2, fun _ => h1⟩
      · exact absurd (mixed_sign_false151b (a := S.a₁) (b := S.a₂) (f := f.1) (g := g.1)
          (S.a₂_pow hp) hfII.1 h1 h2 hfg) (S.a₁_ne_one hp)
      · exact absurd (mixed_sign_false151b (a := S.a₂) (b := S.a₁) (f := f.1) (g := g.1)
          (S.a₁_pow hp) hfII.2 h2 h1 hfg) (S.a₂_ne_one hp)
      · exact ⟨fun h => absurd (h1.symm.trans h) hne₁, fun h => absurd (h2.symm.trans h) hne₂⟩
    have hT₁ : Nat.card {g : E // S.TypeI g.1} ≤ 2 := by
      have hinj : Function.Injective (fun g : {g : E // S.TypeI g.1} =>
          decide (g.1.1 * S.a₁ * g.1.1⁻¹ = S.a₁)) := by
        intro g h hgh
        simp only [decide_eq_decide] at hgh
        apply Subtype.ext
        apply Subtype.ext
        exact S.eq_of_conj_eq hW hcard hE g.1.2 h.1.2
          (conj_eq S.a₁ g.1.1 h.1.1 hne₁ (hsign₁ g.1 g.2) (hsign₁ h.1 h.2) hgh)
          (conj_eq S.a₂ g.1.1 h.1.1 hne₂ (hsign₂ g.1 g.2) (hsign₂ h.1 h.2)
            ((hsame g.1 g.2).symm.trans (hgh.trans (hsame h.1 h.2))))
      have := Nat.card_le_card_of_injective _ hinj
      simpa using this
    rw [hsplit]
    omega

end SixData151b

end CFSG.Quasithin
