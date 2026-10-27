module

public import CFSG.Quasithin.H13.GoldschmidtG52Reps

public section

namespace CFSG.Quasithin.H13.A6.G52

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix Equiv

@[expose] def tt : Perm (Fin 6) := swap 0 1

theorem tt_mul_self : tt * tt = 1 := swap_mul_self 0 1

theorem sign_tt : Perm.sign tt = -1 := Perm.sign_swap (by decide)

theorem tt_mul_mul_mem {a : Perm (Fin 6)} (ha : a ∈ alternatingGroup (Fin 6)) :
    tt * a * tt ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup] at ha ⊢
  rw [map_mul, map_mul, ha, sign_tt]
  simp

theorem mul_tt_mem {σ : Perm (Fin 6)} (hσ : σ ∉ alternatingGroup (Fin 6)) :
    σ * tt ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup] at hσ ⊢
  rw [map_mul, sign_tt]
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h
  · exact absurd h hσ
  · rw [h]
    decide

section Twist

variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) (Perm (Fin 6)) V) (τ : Representation (ZMod 2) (Perm (Fin 6)) W)

@[expose] def twist (f : V →ₗ[ZMod 2] W) : V →ₗ[ZMod 2] W := τ tt ∘ₗ f ∘ₗ ρ tt

@[expose] def IsAltHom (f : V →ₗ[ZMod 2] W) : Prop :=
  ∀ a : alternatingGroup (Fin 6), ∀ v, f (ρ (a : Perm (Fin 6)) v) = τ (a : Perm (Fin 6)) (f v)

theorem rep_tt_tt {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (π : Representation (ZMod 2) (Perm (Fin 6)) U) (u : U) : π tt (π tt u) = u := by
  rw [← Module.End.mul_apply, ← map_mul, tt_mul_self, map_one]
  rfl

theorem twist_twist (f : V →ₗ[ZMod 2] W) : twist ρ τ (twist ρ τ f) = f := by
  ext v
  simp only [twist, LinearMap.comp_apply]
  rw [rep_tt_tt ρ, rep_tt_tt τ]

theorem twist_add (f g : V →ₗ[ZMod 2] W) : twist ρ τ (f + g) = twist ρ τ f + twist ρ τ g := by
  ext v
  simp [twist]

theorem isAltHom_twist {f : V →ₗ[ZMod 2] W} (hf : IsAltHom ρ τ f) :
    IsAltHom ρ τ (twist ρ τ f) := by
  intro a v
  have hmem := tt_mul_mul_mem a.2
  have e1 : tt * (a : Perm (Fin 6)) = (tt * (a : Perm (Fin 6)) * tt) * tt := by
    rw [mul_assoc (tt * (a : Perm (Fin 6))) tt tt, tt_mul_self, mul_one]
  have e2 : tt * (tt * (a : Perm (Fin 6)) * tt) = (a : Perm (Fin 6)) * tt := by
    rw [← mul_assoc, ← mul_assoc, tt_mul_self, one_mul]
  have h1 : ρ tt (ρ (a : Perm (Fin 6)) v) =
      ρ (tt * (a : Perm (Fin 6)) * tt) (ρ tt v) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← e1]
  have h2 : τ tt (τ (tt * (a : Perm (Fin 6)) * tt) (f (ρ tt v))) =
      τ (a : Perm (Fin 6)) (τ tt (f (ρ tt v))) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, e2]
  simp only [twist, LinearMap.comp_apply]
  rw [h1, hf ⟨_, hmem⟩ (ρ tt v), h2]

theorem isIntertwining_of_twist {f : V →ₗ[ZMod 2] W} (hf : IsAltHom ρ τ f)
    (hfix : twist ρ τ f = f) (σ : Perm (Fin 6)) (v : V) : f (ρ σ v) = τ σ (f v) := by
  have ht : ∀ v, f (ρ tt v) = τ tt (f v) := fun v => by
    have h := LinearMap.congr_fun hfix (ρ tt v)
    simp only [twist, LinearMap.comp_apply] at h
    rw [rep_tt_tt ρ] at h
    exact h.symm
  by_cases hσ : σ ∈ alternatingGroup (Fin 6)
  · exact hf ⟨σ, hσ⟩ v
  · have hmem := mul_tt_mem hσ
    have hσe : σ = (σ * tt) * tt := by rw [mul_assoc, tt_mul_self, mul_one]
    calc f (ρ σ v) = f (ρ ((σ * tt) * tt) v) := by rw [← hσe]
      _ = f (ρ (σ * tt) (ρ tt v)) := by rw [map_mul]; rfl
      _ = τ (σ * tt) (f (ρ tt v)) := hf ⟨_, hmem⟩ (ρ tt v)
      _ = τ (σ * tt) (τ tt (f v)) := by rw [ht]
      _ = τ σ (f v) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_assoc, tt_mul_self, mul_one]

theorem exists_intertwining_of_alt {ι : V →ₗ[ZMod 2] W} (hι : IsAltHom ρ τ ι) (hne : ι ≠ 0) :
    ∃ f : V →ₗ[ZMod 2] W, f ≠ 0 ∧ ∀ σ v, f (ρ σ v) = τ σ (f v) := by
  have hadd : IsAltHom ρ τ (ι + twist ρ τ ι) := fun a v => by
    simp only [LinearMap.add_apply, map_add]
    rw [hι a v, isAltHom_twist ρ τ hι a v]
  have hfix : twist ρ τ (ι + twist ρ τ ι) = ι + twist ρ τ ι := by
    rw [twist_add, twist_twist, add_comm]
  by_cases h0 : ι + twist ρ τ ι = 0
  · have h2 : ι + ι = 0 := by
      ext v
      simp only [LinearMap.add_apply, LinearMap.zero_apply]
      rw [← two_smul (ZMod 2) (ι v)]
      have : (2 : ZMod 2) = 0 := by decide
      rw [this, zero_smul]
    have hΘ : twist ρ τ ι = ι := by
      have h3 : twist ρ τ ι = -ι := eq_neg_of_add_eq_zero_right h0
      rw [h3]
      exact neg_eq_of_add_eq_zero_left h2
    exact ⟨ι, hne, isIntertwining_of_twist ρ τ hι hΘ⟩
  · exact ⟨ι + twist ρ τ ι, h0, isIntertwining_of_twist ρ τ hadd hfix⟩

end Twist


section Classify


theorem exists_equiv_Mrep {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (τ : Representation (ZMod 2) (Perm (Fin 6)) V)
    (hτ : Representation.IsIrreducible τ) :
    ∃ i : Fin 4, Nonempty (Representation.Equiv (Mrep i) τ) := by
  have : Nontrivial V := nontrivial_of_isIrreducible τ
  obtain ⟨U, -, hUirr⟩ :=
    exists_isIrreducible_subrepresentation (τ.comp (alternatingGroup (Fin 6)).subtype)
  obtain ⟨-, i, ⟨e⟩⟩ := a6BinaryRep_complete U.toSubmodule U.toRepresentation hUirr
  let incl : U.toRepresentation.IntertwiningMap (τ.comp (alternatingGroup (Fin 6)).subtype) :=
    ⟨U.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
  let ι : Representation.IntertwiningMap ((Mrep i).comp (alternatingGroup (Fin 6)).subtype)
      (τ.comp (alternatingGroup (Fin 6)).subtype) :=
    incl.comp (e.symm.toIntertwiningMap.comp (MrepRestrictEquiv i).toIntertwiningMap)
  have hι : IsAltHom (Mrep i) τ ι.toLinearMap := fun a v =>
    Representation.IntertwiningMap.isIntertwining _ _ ι a v
  have : Representation.IsIrreducible (Mrep i) := isIrreducible_Mrep i
  have : Nontrivial (Fin (![1, 4, 4, 16] i) → ZMod 2) := nontrivial_of_isIrreducible (Mrep i)
  have hinj : Function.Injective ι.toLinearMap := by
    intro x y hxy
    have h1 : U.toSubmodule.subtype (e.symm ((MrepRestrictEquiv i) x)) =
        U.toSubmodule.subtype (e.symm ((MrepRestrictEquiv i) y)) := hxy
    exact (MrepRestrictEquiv i).injective (e.symm.injective (Subtype.ext h1))
  have hne : ι.toLinearMap ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : Fin (![1, 4, 4, 16] i) → ZMod 2)
    exact hx (hinj (by rw [h0]; simp))
  obtain ⟨f, hf0, hf⟩ := exists_intertwining_of_alt (Mrep i) τ hι hne
  let F : (Mrep i).IntertwiningMap τ := f.intertwiningMap_of_isIntertwiningMap (Mrep i) τ hf
  have hF0 : F ≠ 0 := fun h => hf0 (congrArg Representation.IntertwiningMap.toLinearMap h)
  have := hτ
  exact ⟨i, ⟨F.ofBijective
    ((Representation.IsIrreducible.bijective_or_eq_zero F).resolve_right hF0)⟩⟩

end Classify

end CFSG.Quasithin.H13.A6.G52
