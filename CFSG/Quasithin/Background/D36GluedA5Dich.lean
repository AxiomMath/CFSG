module

public import CFSG.Quasithin.Background.D36GluedA5Orb
public import CFSG.Quasithin.Background.D36GluedA5Mod

public section

namespace CFSG.Quasithin.A5Dich

open CFSG.Quasithin.A5Mod

variable {Γ : Type} [Group Γ] {M : Type} [CommGroup M] [MulDistribMulAction Γ M]

theorem dichotomy [Finite Γ] [Finite M] (hΓ : Nat.card Γ = 60) (hs : IsSimpleGroup Γ)
    (hM2 : ∀ x : M, x ^ 2 = 1) (hM : Nat.card M = 16)
    (hfix : ∀ x : M, (∀ γ : Γ, γ • x = x) → x = 1) {g l : Γ} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hl2 : l * l = 1) (hl1 : l ≠ 1) (hlg : l * g * l = g⁻¹) {b : MulAut M} (hb2 : b * b = 1)
    (hb1 : b ≠ 1) (hbg : b * MulDistribMulAction.toMulAut Γ M g =
      MulDistribMulAction.toMulAut Γ M g * b)
    (hbl : b * MulDistribMulAction.toMulAut Γ M l = MulDistribMulAction.toMulAut Γ M l * b) :
    Nat.card ↥(fixSub b ⊓ fixSub (MulDistribMulAction.toMulAut Γ M l)) ≤ 2 ∨
      ∃ e₁ e₂ c : Γ, e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧ e₁ * e₂ = e₂ * e₁ ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧
        e₁ ≠ e₂ ∧ c * e₁ * c⁻¹ = e₂ ∧ c * e₂ * c⁻¹ = e₁ * e₂ ∧
        ∃ v : M, v ≠ 1 ∧ e₁ • v = v ∧ e₂ • v = v ∧ c • v = v := by
  have hl2' : MulDistribMulAction.toMulAut Γ M l * MulDistribMulAction.toMulAut Γ M l = 1 := by
    rw [← map_mul, hl2, map_one]
  have hg3' : (MulDistribMulAction.toMulAut Γ M g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
  have hlg' : MulDistribMulAction.toMulAut Γ M l * MulDistribMulAction.toMulAut Γ M g *
      MulDistribMulAction.toMulAut Γ M l = (MulDistribMulAction.toMulAut Γ M g)⁻¹ := by
    rw [← map_mul, ← map_mul, hlg, map_inv]
  by_cases hex : ∃ x : M, MulDistribMulAction.toMulAut Γ M g x = x ∧ x ≠ 1
  · right
    obtain ⟨p, hp1, hgp, hlp⟩ := exists_fixed_of_two hM2 hl2' hlg' hex
    obtain ⟨R, hR5, hR1, hRinv⟩ := A5Orb.exists_five_set hΓ hs hM hfix hp1 hg3 hg1 hl2 hl1 hgp hlp
    have hnf : ∀ x ∈ R, ∃ γ : Γ, γ • x ≠ x := by
      intro x hx
      by_contra hcon
      push Not at hcon
      exact hR1 (hfix x hcon ▸ hx)
    obtain ⟨e₁, e₂, c, h1, h2, h3, h4, h5, h6, h7, h8, v, hv, hv1, hv2, hv3⟩ :=
      A5Orb.exists_A4_fixed hΓ hs R hR5 hRinv hnf
    refine ⟨e₁, e₂, c, h1, h2, h3, h4, h5, h6, h7, h8, v, ?_, hv1, hv2, hv3⟩
    rintro rfl
    exact hR1 hv
  · left
    push Not at hex
    exact card_fixSub_inf_le_two hM2 hM hb2 hb1 hl2' hg3' hex hbg hbl hlg'

theorem range_commHom_conj_le (ψ φ : MulAut M) :
    (commHom (ψ * φ * ψ⁻¹)).range ≤ (commHom φ).range.map ψ.toMonoidHom := by
  rintro _ ⟨z, rfl⟩
  refine ⟨commHom φ (ψ⁻¹ z), ⟨ψ⁻¹ z, rfl⟩, ?_⟩
  simp [commHom_apply, MulAut.mul_apply]

theorem commHom_mul_apply (φ φ' : MulAut M) (y : M) :
    commHom (φ * φ') y = commHom φ (φ' y) * commHom φ' y := by
  simp only [commHom_apply, MulAut.mul_apply]
  group

theorem card_range_commHom_mul_le [Finite M] (φ φ' : MulAut M) :
    Nat.card (commHom (φ * φ')).range ≤
      Nat.card (commHom φ).range * Nat.card (commHom φ').range := by
  have hle : (commHom (φ * φ')).range ≤ (commHom φ).range ⊔ (commHom φ').range := by
    rintro _ ⟨y, rfl⟩
    rw [commHom_mul_apply]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)
  have h1 := Subgroup.card_le_of_le hle
  have h2 := card_sup_mul_card_inf (commHom φ).range (commHom φ').range
  have h3 : 0 < Nat.card ↥((commHom φ).range ⊓ (commHom φ').range) := Nat.card_pos
  calc Nat.card (commHom (φ * φ')).range
      ≤ Nat.card ↥((commHom φ).range ⊔ (commHom φ').range) := h1
    _ ≤ Nat.card ↥((commHom φ).range ⊔ (commHom φ').range) *
          Nat.card ↥((commHom φ).range ⊓ (commHom φ').range) := Nat.le_mul_of_pos_right _ h3
    _ = Nat.card (commHom φ).range * Nat.card (commHom φ').range := h2

theorem false_of_five [Finite M] (e : Γ ≃* alternatingGroup (Fin 5)) (hM2 : ∀ x : M, x ^ 2 = 1)
    (hfaith : ∀ γ : Γ, (∀ x : M, γ • x = x) → γ = 1) {t : Γ} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hrange : Nat.card (commHom (MulDistribMulAction.toMulAut Γ M t)).range ≤ 2) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set k : Equiv.Perm (Fin 5) := ((e t : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) with hk
  have hk2 : k * k = 1 := by
    have : e t * e t = 1 := by rw [← map_mul, ht2, map_one]
    have := congrArg (fun a : alternatingGroup (Fin 5) => (a : Equiv.Perm (Fin 5))) this
    simpa [hk] using this
  have hk1 : k ≠ 1 := by
    intro h
    apply ht1
    apply e.injective
    rw [map_one]
    exact Subtype.ext h
  have hksign : Equiv.Perm.sign k = 1 := Equiv.Perm.mem_alternatingGroup.mp (e t).2
  obtain ⟨h, hhs, hx5, hx1⟩ := CFSG.Quasithin.A5Fin.exists_prod_five k hksign hk2 hk1
  set h' : Γ := e.symm ⟨h, Equiv.Perm.mem_alternatingGroup.mpr hhs⟩ with hh'
  set t' : Γ := h' * t * h'⁻¹ with ht'
  set x : Γ := t * t' with hx
  have hex : ((e x : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = k * (h * k * h⁻¹) := by
    rw [hx, ht', map_mul, map_mul, map_mul, map_inv, hh', MulEquiv.apply_symm_apply]
    rfl
  have hx5' : x ^ 5 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    apply Subtype.ext
    simpa [hex] using hx5
  have hx1' : x ≠ 1 := by
    intro hxe
    apply hx1
    rw [← hex, hxe, map_one]
    rfl
  set a : MulAut M := MulDistribMulAction.toMulAut Γ M t with ha
  set a' : MulAut M := MulDistribMulAction.toMulAut Γ M t' with ha'
  set ax : MulAut M := MulDistribMulAction.toMulAut Γ M x with hax
  have hax_eq : ax = a * a' := by rw [hax, hx, map_mul]
  have hconj : a' = (MulDistribMulAction.toMulAut Γ M h') * a *
      (MulDistribMulAction.toMulAut Γ M h')⁻¹ := by
    rw [ha', ht', map_mul, map_mul, map_inv]
  have hR2 : Nat.card (commHom a').range ≤ 2 := by
    have h1 := Subgroup.card_le_of_le (range_commHom_conj_le
      (MulDistribMulAction.toMulAut Γ M h') a)
    rw [← hconj] at h1
    refine h1.trans ?_
    rw [Subgroup.card_map_of_injective (f := (MulDistribMulAction.toMulAut Γ M h').toMonoidHom)
      (MulEquiv.injective _)]
    exact hrange
  have hK4 : Nat.card (commHom ax).range ≤ 4 := by
    rw [hax_eq]
    calc Nat.card (commHom (a * a')).range
        ≤ Nat.card (commHom a).range * Nat.card (commHom a').range :=
          card_range_commHom_mul_le a a'
      _ ≤ 2 * 2 := Nat.mul_le_mul hrange hR2
  have hKinv : ∀ y ∈ (commHom ax).range, ax y ∈ (commHom ax).range := by
    rintro _ ⟨z, rfl⟩
    exact ⟨ax z, by simp [commHom_apply, MulAut.mul_apply]⟩
  have hax5 : ax ^ 5 = 1 := by rw [hax, ← map_pow, hx5', map_one]
  have hmod := card_fix_modEq 5 ax hax5 (commHom ax).range hKinv
  have hKall : (commHom ax).range ≤ fixSub ax := by
    have hK1 : 1 ≤ Nat.card ↥((commHom ax).range ⊓ fixSub ax) := Nat.card_pos
    have hK2 : Nat.card ↥((commHom ax).range ⊓ fixSub ax) ≤ Nat.card (commHom ax).range :=
      Subgroup.card_le_of_le inf_le_left
    have hK3 : 1 ≤ Nat.card (commHom ax).range := Nat.card_pos
    have heq : Nat.card ↥((commHom ax).range ⊓ fixSub ax) = Nat.card (commHom ax).range := by
      unfold Nat.ModEq at hmod
      omega
    have hinf : (commHom ax).range ⊓ fixSub ax = (commHom ax).range :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [heq])
    rw [← hinf]
    exact inf_le_right
  have hsq : ax * ax = 1 := by
    refine MulEquiv.ext fun y => ?_
    have h1 : ax (commHom ax y) = commHom ax y := hKall ⟨y, rfl⟩
    simp only [commHom_apply, map_mul, map_inv] at h1
    have h2 : (ax y) ^ 2 = 1 := hM2 _
    have h3 : (ax y)⁻¹ = ax y := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h2)
    have h4 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hM2 y)
    rw [h3, h4] at h1
    have h5 : ax (ax y) = y := mul_right_cancel (h1.trans (mul_comm _ _))
    simpa [MulAut.mul_apply] using h5
  have hax1 : ax = 1 := by
    calc ax = ax ^ 5 * ((ax * ax)⁻¹) ^ 2 := by group
      _ = 1 := by rw [hax5, hsq]; simp
  apply hx1'
  refine hfaith x fun y => ?_
  have := congrArg (fun φ : MulAut M => φ y) hax1
  simpa [hax] using this

end CFSG.Quasithin.A5Dich
