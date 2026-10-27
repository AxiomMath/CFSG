module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.Quasithin

namespace SBc16

abbrev Z52 : Type := Multiplicative (Fin 2 → ZMod 5)

def matOf (β : MulAut Z52) : Matrix (Fin 2) (Fin 2) (ZMod 5) :=
  Matrix.of fun i j => Multiplicative.toAdd (β (Multiplicative.ofAdd (Pi.single j 1))) i

theorem matOf_apply (β : MulAut Z52) (x : Fin 2 → ZMod 5) :
    Multiplicative.toAdd (β (Multiplicative.ofAdd x)) = (matOf β).mulVec x := by
  have hx : x = x 0 • Pi.single 0 1 + x 1 • Pi.single 1 1 := by
    ext i; fin_cases i <;> simp
  have hsmul : ∀ (k : ZMod 5) (y : Fin 2 → ZMod 5),
      Multiplicative.toAdd (β (Multiplicative.ofAdd (k • y))) =
        k • Multiplicative.toAdd (β (Multiplicative.ofAdd y)) := by
    intro k y
    have e : k • y = k.val • y := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 5), ZMod.natCast_zmod_val]
    rw [e, ofAdd_nsmul, map_pow, toAdd_pow, ← Nat.cast_smul_eq_nsmul (ZMod 5),
      ZMod.natCast_zmod_val]
  conv_lhs => rw [hx, ofAdd_add, map_mul, toAdd_mul, hsmul, hsmul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, matOf, Matrix.of_apply]
  ring

theorem matOf_one : matOf 1 = 1 := by
  ext i j
  simp only [matOf, Matrix.of_apply, MulAut.one_apply, toAdd_ofAdd, Matrix.one_apply]
  rw [Pi.single_apply]

theorem matOf_mul (β γ : MulAut Z52) : matOf (β * γ) = matOf β * matOf γ := by
  ext i j
  have h := matOf_apply β (Multiplicative.toAdd (γ (Multiplicative.ofAdd (Pi.single j 1))))
  rw [ofAdd_toAdd] at h
  have e : matOf (β * γ) i j =
      Multiplicative.toAdd (β (γ (Multiplicative.ofAdd (Pi.single j 1)))) i := rfl
  rw [e, h]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rfl

theorem matOf_injective : Function.Injective matOf := by
  intro β γ h
  apply MulEquiv.ext
  intro w
  apply Multiplicative.toAdd.injective
  have h1 := matOf_apply β (Multiplicative.toAdd w)
  have h2 := matOf_apply γ (Multiplicative.toAdd w)
  rw [ofAdd_toAdd] at h1 h2
  rw [h1, h2, h]

section Coord

variable {V : Type} [CommGroup V]

theorem pow_val_add (h5 : ∀ x : V, x ^ 5 = 1) (v : V) (a b : ZMod 5) :
    v ^ (a + b).val = v ^ a.val * v ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) 5, pow_add, pow_mul, h5, one_pow, mul_one]

@[expose] def coordHom (h5 : ∀ x : V, x ^ 5 = 1) (v₁ v₂ : V) : Z52 →* V where
  toFun w := v₁ ^ (Multiplicative.toAdd w 0).val * v₂ ^ (Multiplicative.toAdd w 1).val
  map_one' := by simp
  map_mul' w w' := by
    simp only [toAdd_mul, Pi.add_apply, pow_val_add h5]
    exact mul_mul_mul_comm _ _ _ _

theorem coordHom_apply (h5 : ∀ x : V, x ^ 5 = 1) (v₁ v₂ : V) (w : Z52) :
    coordHom h5 v₁ v₂ w =
      v₁ ^ (Multiplicative.toAdd w 0).val * v₂ ^ (Multiplicative.toAdd w 1).val := rfl

theorem eq_zero_of_pow_val_eq_one {v : V} (hv : orderOf v = 5) {a : ZMod 5}
    (h : v ^ a.val = 1) : a = 0 := by
  have hd : orderOf v ∣ a.val := orderOf_dvd_of_pow_eq_one h
  rw [hv] at hd
  have hlt := ZMod.val_lt a
  have : a.val = 0 := by omega
  exact (ZMod.val_eq_zero a).mp this

theorem fst_eq_zero_of_mem {h5 : ∀ x : V, x ^ 5 = 1} {V₁ V₂ : Subgroup V} (hd : V₁ ⊓ V₂ = ⊥)
    {v₁ v₂ : V} (hv₁ : v₁ ∈ V₁) (ho₁ : orderOf v₁ = 5) (hv₂ : v₂ ∈ V₂) {w : Z52}
    (hw : coordHom h5 v₁ v₂ w ∈ V₂) : Multiplicative.toAdd w 0 = 0 := by
  have hA : v₁ ^ (Multiplicative.toAdd w 0).val ∈ V₁ ⊓ V₂ := by
    refine ⟨Subgroup.pow_mem _ hv₁ _, ?_⟩
    have : v₁ ^ (Multiplicative.toAdd w 0).val =
        coordHom h5 v₁ v₂ w * (v₂ ^ (Multiplicative.toAdd w 1).val)⁻¹ := by
      rw [coordHom_apply, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact V₂.mul_mem hw (V₂.inv_mem (Subgroup.pow_mem _ hv₂ _))
  rw [hd, Subgroup.mem_bot] at hA
  exact eq_zero_of_pow_val_eq_one ho₁ hA

theorem snd_eq_zero_of_mem {h5 : ∀ x : V, x ^ 5 = 1} {V₁ V₂ : Subgroup V} (hd : V₁ ⊓ V₂ = ⊥)
    {v₁ v₂ : V} (hv₁ : v₁ ∈ V₁) (hv₂ : v₂ ∈ V₂) (ho₂ : orderOf v₂ = 5) {w : Z52}
    (hw : coordHom h5 v₁ v₂ w ∈ V₁) : Multiplicative.toAdd w 1 = 0 := by
  have hB : v₂ ^ (Multiplicative.toAdd w 1).val ∈ V₁ ⊓ V₂ := by
    refine ⟨?_, Subgroup.pow_mem _ hv₂ _⟩
    have : v₂ ^ (Multiplicative.toAdd w 1).val =
        (v₁ ^ (Multiplicative.toAdd w 0).val)⁻¹ * coordHom h5 v₁ v₂ w := by
      rw [coordHom_apply, inv_mul_cancel_left]
    rw [this]
    exact V₁.mul_mem (V₁.inv_mem (Subgroup.pow_mem _ hv₁ _)) hw
  rw [hd, Subgroup.mem_bot] at hB
  exact eq_zero_of_pow_val_eq_one ho₂ hB

theorem coordHom_injective {h5 : ∀ x : V, x ^ 5 = 1} {V₁ V₂ : Subgroup V} (hd : V₁ ⊓ V₂ = ⊥)
    {v₁ v₂ : V} (hv₁ : v₁ ∈ V₁) (ho₁ : orderOf v₁ = 5) (hv₂ : v₂ ∈ V₂) (ho₂ : orderOf v₂ = 5) :
    Function.Injective (coordHom h5 v₁ v₂) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have h0 : Multiplicative.toAdd w 0 = 0 :=
    fst_eq_zero_of_mem hd hv₁ ho₁ hv₂ (hw ▸ V₂.one_mem)
  have h1 : Multiplicative.toAdd w 1 = 0 :=
    snd_eq_zero_of_mem hd hv₁ hv₂ ho₂ (hw ▸ V₁.one_mem)
  apply Multiplicative.toAdd.injective
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem coordHom_bijective [Finite V] (hV : Nat.card V = 25) {h5 : ∀ x : V, x ^ 5 = 1}
    {V₁ V₂ : Subgroup V} (hd : V₁ ⊓ V₂ = ⊥) {v₁ v₂ : V} (hv₁ : v₁ ∈ V₁) (ho₁ : orderOf v₁ = 5)
    (hv₂ : v₂ ∈ V₂) (ho₂ : orderOf v₂ = 5) : Function.Bijective (coordHom h5 v₁ v₂) := by
  refine (coordHom_injective hd hv₁ ho₁ hv₂ ho₂).bijective_of_nat_card_le ?_
  rw [hV]
  simp [Nat.card_eq_fintype_card, ZMod.card]

end Coord

@[expose] def matHom : MulAut Z52 →* Matrix (Fin 2) (Fin 2) (ZMod 5) where
  toFun := matOf
  map_one' := matOf_one
  map_mul' := matOf_mul

theorem exists_ne_one_of_card_five {V : Type} [Group V] {W : Subgroup V} (hW : Nat.card W = 5) :
    ∃ w ∈ W, w ≠ 1 := by
  have hbot : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hW
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩

theorem exists_matrix_rep (V : Type) [CommGroup V] [Finite V] (hV : Nat.card V = 25)
    (h5 : ∀ x : V, x ^ 5 = 1) (V₁ V₂ : Subgroup V) (h1 : Nat.card V₁ = 5) (h2 : Nat.card V₂ = 5)
    (hd : V₁ ⊓ V₂ = ⊥) :
    ∃ ρ : MulAut V →* GL (Fin 2) (ZMod 5), Function.Injective ρ ∧
      ∀ σ τ : MulAut V, (∀ x ∈ V₂, σ x = x) → (∀ x ∈ V₁, σ x = x⁻¹) →
        V₁.map τ.toMonoidHom = V₂ → V₂.map τ.toMonoidHom = V₁ →
        (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = -1 ∧
        (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = 0 ∧
        (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = 0 ∧
        (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = 1 ∧
        (ρ τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = 0 ∧
        (ρ τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = 0 ∧
        (ρ τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 ≠ 0 ∧
        (ρ τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 ≠ 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨v₁, hv₁, hne₁⟩ := exists_ne_one_of_card_five h1
  obtain ⟨v₂, hv₂, hne₂⟩ := exists_ne_one_of_card_five h2
  have ho₁ : orderOf v₁ = 5 := orderOf_eq_prime (h5 v₁) hne₁
  have ho₂ : orderOf v₂ = 5 := orderOf_eq_prime (h5 v₂) hne₂
  have hbij : Function.Bijective (coordHom h5 v₁ v₂) := coordHom_bijective hV hd hv₁ ho₁ hv₂ ho₂
  let eV : Z52 ≃* V := MulEquiv.ofBijective (coordHom h5 v₁ v₂) hbij
  have heV : ∀ w, eV w = coordHom h5 v₁ v₂ w := fun w => rfl
  let ρ : MulAut V →* GL (Fin 2) (ZMod 5) :=
    (matHom.comp (MulAut.congr eV.symm).toMonoidHom).toHomUnits
  have hent : ∀ (α : MulAut V) (i j : Fin 2), (ρ α : Matrix (Fin 2) (Fin 2) (ZMod 5)) i j =
      Multiplicative.toAdd (eV.symm (α (eV (Multiplicative.ofAdd (Pi.single j 1))))) i :=
    fun α i j => rfl
  have hρinj : Function.Injective ρ := by
    intro α α' h
    have h1 : matOf (MulAut.congr eV.symm α) = matOf (MulAut.congr eV.symm α') :=
      congrArg Units.val h
    exact (MulAut.congr eV.symm).injective (matOf_injective h1)
  have hval1 : (1 : ZMod 5).val = 1 := by decide
  have hvalm1 : (-1 : ZMod 5).val = 4 := by decide
  have hb0 : eV (Multiplicative.ofAdd (Pi.single 0 1)) = v₁ := by
    rw [heV, coordHom_apply]
    simp [hval1]
  have hb1 : eV (Multiplicative.ofAdd (Pi.single 1 1)) = v₂ := by
    rw [heV, coordHom_apply]
    simp [hval1]
  have hinv0 : eV (Multiplicative.ofAdd (Pi.single 0 (-1))) = v₁⁻¹ := by
    rw [heV, coordHom_apply]
    have h4 : v₁ ^ 4 = v₁⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h5 v₁)
    simp [hvalm1, h4]
  have hcrd : ∀ x : V, coordHom h5 v₁ v₂ (eV.symm x) = x := fun x => by
    rw [← heV, MulEquiv.apply_symm_apply]
  have hne : ∀ x : V, x ≠ 1 → Multiplicative.toAdd (eV.symm x) 0 = 0 →
      Multiplicative.toAdd (eV.symm x) 1 = 0 → False := by
    intro x hx h0 h1'
    apply hx
    have : eV.symm x = 1 := by
      apply Multiplicative.toAdd.injective
      ext i
      fin_cases i
      · exact h0
      · exact h1'
    rw [MulEquiv.symm_apply_eq] at this
    rw [this, map_one]
  refine ⟨ρ, hρinj, ?_⟩
  intro σ τ hσ2 hσ1 hτ1 hτ2
  have hc0 : eV.symm (σ v₁) = Multiplicative.ofAdd (Pi.single 0 (-1)) := by
    rw [hσ1 v₁ hv₁, MulEquiv.symm_apply_eq, hinv0]
  have hc1 : eV.symm (σ v₂) = Multiplicative.ofAdd (Pi.single 1 1) := by
    rw [hσ2 v₂ hv₂, MulEquiv.symm_apply_eq, hb1]
  have hτv₁ : τ v₁ ∈ V₂ := by
    rw [← hτ1]
    exact ⟨v₁, hv₁, rfl⟩
  have hτv₂ : τ v₂ ∈ V₁ := by
    rw [← hτ2]
    exact ⟨v₂, hv₂, rfl⟩
  have hτ₁0 : Multiplicative.toAdd (eV.symm (τ v₁)) 0 = 0 :=
    fst_eq_zero_of_mem hd hv₁ ho₁ hv₂ (by rw [hcrd]; exact hτv₁)
  have hτ₂1 : Multiplicative.toAdd (eV.symm (τ v₂)) 1 = 0 :=
    snd_eq_zero_of_mem hd hv₁ hv₂ ho₂ (by rw [hcrd]; exact hτv₂)
  have hτ₁1 : Multiplicative.toAdd (eV.symm (τ v₁)) 1 ≠ 0 := fun h =>
    hne _ (fun h' => hne₁ (τ.injective (h'.trans (map_one τ).symm))) hτ₁0 h
  have hτ₂0 : Multiplicative.toAdd (eV.symm (τ v₂)) 0 ≠ 0 := fun h =>
    hne _ (fun h' => hne₂ (τ.injective (h'.trans (map_one τ).symm))) h hτ₂1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hent, hb0, hc0]
    simp
  · rw [hent, hb1, hc1]
    simp
  · rw [hent, hb0, hc0]
    simp
  · rw [hent, hb1, hc1]
    simp
  · rw [hent, hb0]
    exact hτ₁0
  · rw [hent, hb1]
    exact hτ₂1
  · rw [hent, hb1]
    exact hτ₂0
  · rw [hent, hb0]
    exact hτ₁1

end SBc16

end CFSG.Quasithin
