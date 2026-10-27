module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.OddTranspositions.QZ

open Equiv

theorem A5_involutions_conj : ∀ x y : alternatingGroup (Fin 5), x * x = 1 → x ≠ 1 → y * y = 1 →
    y ≠ 1 → ∃ h : alternatingGroup (Fin 5), h * x * h⁻¹ = y := by
  decide +kernel

theorem A5_involution_eq_mul : ∀ x : alternatingGroup (Fin 5), x * x = 1 → x ≠ 1 →
    ∃ k₁ k₂ : alternatingGroup (Fin 5), k₁ * k₁ = 1 ∧ k₂ * k₂ = 1 ∧ k₁ ≠ 1 ∧ k₂ ≠ 1 ∧
      k₁ * k₂ = k₂ * k₁ ∧ k₁ * k₂ = x := by
  decide +kernel

theorem A5_sq_of_pow_four : ∀ x : alternatingGroup (Fin 5), x ^ 4 = 1 → x * x = 1 := by
  decide +kernel

theorem S5_odd_involutions_conj : ∀ π τ : Perm (Fin 5), Perm.sign π = -1 → π * π = 1 →
    Perm.sign τ = 1 → (τ * π) * (τ * π) = 1 →
    ∃ η : Perm (Fin 5), Perm.sign η = 1 ∧ η * π * η⁻¹ = τ * π := by
  decide +kernel

theorem S5_odd_not_centralize_four : ∀ π : Perm (Fin 5), Perm.sign π = -1 →
    ∀ x : Perm (Fin 5), Perm.sign x = 1 → x ≠ 1 → x * x = 1 → π * x = x * π →
    ∀ y : Perm (Fin 5), Perm.sign y = 1 → y ≠ 1 → y ≠ x → y * y = 1 → x * y = y * x →
      π * y ≠ y * π := by
  decide +kernel

end CFSG.OddTranspositions.QZ


namespace CFSG.OddTranspositions.QZ

open Equiv

variable {G : Type} [Group G]

noncomputable def permAutA5 : Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl (by norm_num))

theorem permAutA5_apply (π : Perm (Fin 5)) (y : alternatingGroup (Fin 5)) :
    ((permAutA5 π y : alternatingGroup (Fin 5)) : Perm (Fin 5)) = π * y * π⁻¹ := by
  rw [permAutA5, MulEquiv.ofBijective_apply, MulAut.conjNormal_apply]

variable {X : Subgroup G} (e : X ≃* alternatingGroup (Fin 5))

noncomputable def rhoA5 : Subgroup.normalizer (X : Set G) →* Perm (Fin 5) :=
  (permAutA5.symm.toMonoidHom.comp (MulAut.congr e).toMonoidHom).comp X.normalizerMonoidHom

theorem rhoA5_spec (s : Subgroup.normalizer (X : Set G)) (x : X) :
    ((e (X.normalizerMonoidHom s x) : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
      rhoA5 e s * (e x : Perm (Fin 5)) * (rhoA5 e s)⁻¹ := by
  have h : permAutA5 (rhoA5 e s) = MulAut.congr e (X.normalizerMonoidHom s) := by
    simp [rhoA5]
  rw [← permAutA5_apply, h]
  simp

theorem rhoA5_spec' (s : Subgroup.normalizer (X : Set G)) {x : G} (hx : x ∈ X) :
    ((e ⟨(s : G) * x * (s : G)⁻¹, (s.2 x).mp hx⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
      rhoA5 e s * (e ⟨x, hx⟩ : Perm (Fin 5)) * (rhoA5 e s)⁻¹ :=
  rhoA5_spec e s ⟨x, hx⟩

theorem rhoA5_of_mem {k : G} (hk : k ∈ X) :
    rhoA5 e ⟨k, Subgroup.le_normalizer hk⟩ = (e ⟨k, hk⟩ : Perm (Fin 5)) := by
  apply permAutA5.injective
  ext y : 1
  obtain ⟨x, rfl⟩ := e.surjective y
  apply Subtype.ext
  rw [permAutA5_apply, permAutA5_apply, ← rhoA5_spec]
  have : X.normalizerMonoidHom ⟨k, Subgroup.le_normalizer hk⟩ x = ⟨k, hk⟩ * x * ⟨k, hk⟩⁻¹ := by
    ext; simp
  rw [this]
  simp

theorem commute_of_rhoA5_eq_one (s : Subgroup.normalizer (X : Set G)) (hs : rhoA5 e s = 1)
    {x : G} (hx : x ∈ X) : (s : G) * x * (s : G)⁻¹ = x := by
  have h := rhoA5_spec' e s hx
  rw [hs] at h
  simp only [one_mul, inv_one, mul_one] at h
  have := congrArg Subtype.val (e.injective (Subtype.ext h))
  exact this

theorem eq_of_rhoA5_eq (s t : Subgroup.normalizer (X : Set G)) (hst : (s : G) * (t : G)⁻¹ ∈ X)
    (h : rhoA5 e s = rhoA5 e t) : (s : G) = t := by
  have hk : rhoA5 e ⟨(s : G) * (t : G)⁻¹, Subgroup.le_normalizer hst⟩ = 1 := by
    have : (⟨(s : G) * (t : G)⁻¹, Subgroup.le_normalizer hst⟩ :
        Subgroup.normalizer (X : Set G)) = s * t⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_inv, h, mul_inv_cancel]
  rw [rhoA5_of_mem e hst] at hk
  have : (⟨(s : G) * (t : G)⁻¹, hst⟩ : X) = 1 :=
    e.injective (by rw [map_one]; exact Subtype.ext hk)
  have := congrArg Subtype.val this
  simp only [Subgroup.coe_one] at this
  exact mul_inv_eq_one.mp this

theorem sign_rhoA5_of_not_inner (s : Subgroup.normalizer (X : Set G))
    (hs : ¬ ∃ k ∈ X, ∀ x ∈ X, (s : G) * x * (s : G)⁻¹ = k * x * k⁻¹) :
    Perm.sign (rhoA5 e s) = -1 := by
  rcases Int.units_eq_one_or (Perm.sign (rhoA5 e s)) with h | h
  · exfalso
    apply hs
    have hmem : rhoA5 e s ∈ alternatingGroup (Fin 5) := h
    set k : X := e.symm ⟨_, hmem⟩
    refine ⟨k, k.2, fun x hx => ?_⟩
    have h1 := rhoA5_spec' e s hx
    have h2 := rhoA5_spec' e ⟨(k : G), Subgroup.le_normalizer k.2⟩ hx
    rw [rhoA5_of_mem e k.2] at h2
    have hk : (e ⟨(k : G), k.2⟩ : Perm (Fin 5)) = rhoA5 e s := by
      simp [k]
    rw [hk, ← h1] at h2
    have := congrArg Subtype.val (e.injective (Subtype.ext h2))
    exact this.symm
  · exact h

end CFSG.OddTranspositions.QZ
