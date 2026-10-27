module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1d1
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.C1

open Equiv

variable {G : Type} [Group G] {L Q : Subgroup G}

@[expose] def Ysub (Q : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ Q ∧ y ^ 2 = 1 ∧ ∀ q ∈ Q, q * y = y * q}
  mul_mem' := by
    rintro a b ⟨ha, ha2, hac⟩ ⟨hb, hb2, hbc⟩
    refine ⟨Q.mul_mem ha hb, ?_, fun q hq => ?_⟩
    · have hab : a * b = b * a := hbc a ha
      rw [pow_two] at ha2 hb2 ⊢
      calc a * b * (a * b) = a * a * (b * b) := by
            rw [mul_assoc, ← mul_assoc b a b, ← hab]; group
        _ = 1 := by rw [ha2, hb2, one_mul]
    · rw [← mul_assoc, hac q hq, mul_assoc, hbc q hq, mul_assoc]
  one_mem' := ⟨Q.one_mem, one_pow 2, fun q _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha2, hac⟩
    refine ⟨Q.inv_mem ha, ?_, fun q hq => ?_⟩
    · rw [inv_pow, ha2, inv_one]
    · exact ((Commute.inv_right (hac q hq : Commute q a))).eq

theorem Ysub_comm {a b : G} (ha : a ∈ Ysub Q) (hb : b ∈ Ysub Q) : a * b = b * a :=
  (ha.2.2 b hb.1).symm

instance instCommGroupYsub (Q : Subgroup G) : CommGroup (Ysub Q) :=
  { (inferInstance : Group (Ysub Q)) with
    mul_comm := fun a b => Subtype.ext (Ysub_comm a.2 b.2) }

section Action

variable (π : ↥L →* Perm (Fin 3))

theorem conj_mem_of_ker (hQL : Q ≤ L) (hker : ∀ g : ↥L, π g = 1 ↔ (g : G) ∈ Q) {g q : G}
    (hg : g ∈ L) (hq : q ∈ Q) : g * q * g⁻¹ ∈ Q := by
  have h1 : π ⟨q, hQL hq⟩ = 1 := (hker _).mpr hq
  have h2 : π (⟨g, hg⟩ * ⟨q, hQL hq⟩ * ⟨g, hg⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, h1, map_inv]; simp
  exact (hker _).mp h2

theorem conj_mem_Ysub (hQL : Q ≤ L) (hker : ∀ g : ↥L, π g = 1 ↔ (g : G) ∈ Q) {g y : G}
    (hg : g ∈ L) (hy : y ∈ Ysub Q) : g * y * g⁻¹ ∈ Ysub Q := by
  obtain ⟨hyQ, hy2, hyc⟩ := hy
  refine ⟨conj_mem_of_ker π hQL hker hg hyQ, ?_, fun q hq => ?_⟩
  · rw [conj_pow, hy2]; group
  · have h := hyc (g⁻¹ * q * g) (by simpa using conj_mem_of_ker π hQL hker (inv_mem hg) hq)
    calc q * (g * y * g⁻¹) = g * (g⁻¹ * q * g * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * q * g)) * g⁻¹ := by rw [h]
      _ = g * y * g⁻¹ * q := by group

@[expose] def conjY (hQL : Q ≤ L) (hker : ∀ g : ↥L, π g = 1 ↔ (g : G) ∈ Q) (g : ↥L) :
    MulAut (Ysub Q) where
  toFun y := ⟨g * y * (g : G)⁻¹, conj_mem_Ysub π hQL hker g.2 y.2⟩
  invFun y := ⟨(g : G)⁻¹ * y * g, by
    simpa using conj_mem_Ysub π hQL hker (inv_mem g.2) y.2⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[expose] def actY (hQL : Q ≤ L) (hker : ∀ g : ↥L, π g = 1 ↔ (g : G) ∈ Q) :
    ↥L →* MulAut (Ysub Q) where
  toFun := conjY π hQL hker
  map_one' := by ext y; simp [conjY]
  map_mul' a b := by ext y; simp [conjY, MulAut.mul_apply, mul_assoc]

theorem ker_le_actY (hQL : Q ≤ L) (hker : ∀ g : ↥L, π g = 1 ↔ (g : G) ∈ Q) :
    π.ker ≤ (actY π hQL hker).ker := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  ext y
  have hgQ : (g : G) ∈ Q := (hker g).mp hg
  have := y.2.2.2 g hgQ
  simp only [actY, MonoidHom.coe_mk, OneHom.coe_mk, conjY, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    MulAut.one_apply]
  rw [this]; group

end Action

section Factor

variable (π : ↥L →* Perm (Fin 3))

@[expose] def Good (Q : Subgroup G) (π : ↥L →* Perm (Fin 3)) (u : G) (τ : Perm (Fin 3)) : Prop :=
  u ∈ Ysub Q ∧ ∃ t : ↥L, π t = τ ∧ (t : G) * u = u * t

theorem exists_factor (hQL : Q ≤ L) (hsurj : Function.Surjective π)
    (hker : ∀ g : ↥L, π g = 1 ↔ (g : G) ∈ Q)
    (hcen : ∀ x ∈ L, (∀ g ∈ L, g * x = x * g) → x = 1) {y : G} (hy : y ∈ Ysub Q) :
    ∃ u₀ u₁ u₂ : G, y = u₀ * u₁ * u₂ ∧ Good Q π u₀ (swap 0 1) ∧ Good Q π u₁ (swap 1 2) ∧
      Good Q π u₂ (swap 0 2) := by
  let ρ : Perm (Fin 3) →* MulAut (Ysub Q) :=
    (π.liftOfSurjective hsurj) ⟨actY π hQL hker, ker_le_actY π hQL hker⟩
  have hρ : ∀ (g : ↥L) (w : Ysub Q), ((ρ (π g) w : Ysub Q) : G) = g * w * (g : G)⁻¹ := by
    intro g w
    change ((π.liftOfRightInverse _ _ ⟨actY π hQL hker, ker_le_actY π hQL hker⟩ (π g)) w : G) = _
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    rfl
  have hA : ∀ x : Ysub Q, x * x = 1 := fun x => Subtype.ext (by simpa [pow_two] using x.2.2.1)
  have hfix : ∀ w : Ysub Q, (∀ σ, ρ σ w = w) → w = 1 := by
    intro w hw
    have h1 : (w : G) = 1 := by
      refine hcen w (hQL w.2.1) (fun g hg => ?_)
      have h := congrArg Subtype.val (hw (π ⟨g, hg⟩))
      rw [hρ] at h
      exact mul_inv_eq_iff_eq_mul.mp h
    exact Subtype.ext h1
  set y' : Ysub Q := ⟨y, hy⟩ with hy'
  have key := eq_prod_transpositions ρ hA hfix y'
  have hgood : ∀ τ : Perm (Fin 3), τ * τ = 1 → Good Q π ((y' * ρ τ y' : Ysub Q) : G) τ := by
    intro τ hτ
    obtain ⟨t, ht⟩ := hsurj τ
    refine ⟨(y' * ρ τ y').2, t, ht, ?_⟩
    have hu : ρ τ (y' * ρ τ y') = y' * ρ τ y' := by
      rw [map_mul, ← act_mul_apply ρ τ τ y', hτ, map_one]
      exact mul_comm _ _
    have hρ' : ∀ w : Ysub Q, ((ρ τ w : Ysub Q) : G) = t * w * (t : G)⁻¹ := by
      intro w; rw [← ht]; exact hρ t w
    have h := congrArg Subtype.val hu
    rw [hρ'] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  refine ⟨_, _, _, congrArg Subtype.val key, hgood _ (by decide), hgood _ (by decide),
    hgood _ (by decide)⟩

end Factor

end CFSG.Quasithin.F53.Stellmacher.S35.C1
