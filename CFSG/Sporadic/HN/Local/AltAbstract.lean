module

public import CFSG.Sporadic.HN.Local.Partitions
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Sporadic.HN.Local

open Equiv

noncomputable abbrev natHom : Perm (Fin 12) →* Perm Part :=
  MulAction.toPermHom (Perm (Fin 12)) Part

theorem natHom_apply (σ : Perm (Fin 12)) (S : Part) : natHom σ S = σ • S := rfl

theorem card_part : Fintype.card Part = 462 := by decide +kernel

theorem exists_mulEquiv_alt {H : Type*} [Group H] [Finite H]
    (φ : H →* Perm (Fin 462)) (hφ : Function.Injective φ) (x y : H)
    (hxy : Subgroup.closure ({x, y} : Set H) = ⊤)
    (lab : Fin 462 → Part) (hlab : Function.Injective lab)
    (p₁ p₂ : Perm (Fin 12)) (h₁ : p₁ ∈ alternatingGroup (Fin 12))
    (h₂ : p₂ ∈ alternatingGroup (Fin 12))
    (hx : ∀ k, lab (φ x k) = p₁ • lab k) (hy : ∀ k, lab (φ y k) = p₂ • lab k)
    (hcard : Nat.card H = (Nat.factorial 12) / 2) :
    (∀ σ τ : alternatingGroup (Fin 12),
      (∀ S : Part, (σ : Perm (Fin 12)) • S = (τ : Perm (Fin 12)) • S) → σ = τ) ∧
    ∃ θ : H ≃* alternatingGroup (Fin 12),
      (θ x : Perm (Fin 12)) = p₁ ∧ (θ y : Perm (Fin 12)) = p₂ ∧
        ∀ (h : H) (k : Fin 462), lab (φ h k) = (θ h : Perm (Fin 12)) • lab k := by
  classical
  have hbij : Function.Bijective lab :=
    (Fintype.bijective_iff_injective_and_card lab).2 ⟨hlab, by simp [card_part]⟩
  let ℓ : Fin 462 ≃ Part := Equiv.ofBijective lab hbij
  let Φ : H →* Perm Part := ℓ.permCongrHom.toMonoidHom.comp φ
  have hΦ : Function.Injective Φ := ℓ.permCongrHom.injective.comp hφ
  let ν : alternatingGroup (Fin 12) →* Perm Part :=
    natHom.comp (alternatingGroup (Fin 12)).subtype
  have hΦ_apply : ∀ (h : H) (k : Fin 462), Φ h (lab k) = lab (φ h k) := by
    intro h k
    show ℓ (φ h (ℓ.symm (lab k))) = lab (φ h k)
    have : ℓ.symm (lab k) = k := ℓ.symm_apply_eq.2 rfl
    rw [this]; rfl
  have hΦx : Φ x = ν ⟨p₁, h₁⟩ := by
    ext S
    obtain ⟨k, rfl⟩ := hbij.2 S
    rw [hΦ_apply, hx]; rfl
  have hΦy : Φ y = ν ⟨p₂, h₂⟩ := by
    ext S
    obtain ⟨k, rfl⟩ := hbij.2 S
    rw [hΦ_apply, hy]; rfl
  have hle : Φ.range ≤ ν.range := by
    rw [MonoidHom.range_eq_map, ← hxy, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with rfl | hz
    · exact ⟨_, hΦx.symm⟩
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨_, hΦy.symm⟩
  have hcardΦ : Nat.card Φ.range = Nat.card H :=
    (Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv).symm
  have hcardAlt : Nat.card (alternatingGroup (Fin 12)) = (Nat.factorial 12) / 2 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  have hcardν : Nat.card ν.range ≤ Nat.card (alternatingGroup (Fin 12)) :=
    Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective ν)
  have heq : Φ.range = ν.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardΦ, hcard, ← hcardAlt]; exact hcardν)
  have hcardν' : Nat.card ν.range = Nat.card (alternatingGroup (Fin 12)) := by
    rw [← heq, hcardΦ, hcard, hcardAlt]
  have hν : Function.Injective ν := by
    have hb := (MonoidHom.rangeRestrict_surjective ν).bijective_of_nat_card_le hcardν'.ge
    intro a b hab
    apply hb.1
    exact Subtype.ext hab
  let θ : H ≃* alternatingGroup (Fin 12) :=
    ((MonoidHom.ofInjective hΦ).trans (MulEquiv.subgroupCongr heq)).trans
      (MonoidHom.ofInjective hν).symm
  have hθ : ∀ h : H, ν (θ h) = Φ h := by
    intro h
    have := (MonoidHom.ofInjective hν).apply_symm_apply
      (MulEquiv.subgroupCongr heq (MonoidHom.ofInjective hΦ h))
    exact congrArg Subtype.val this
  refine ⟨fun σ τ h => hν (Equiv.ext fun S => h S), θ, ?_, ?_, ?_⟩
  · have : θ x = ⟨p₁, h₁⟩ := hν (by rw [hθ, hΦx])
    rw [this]
  · have : θ y = ⟨p₂, h₂⟩ := hν (by rw [hθ, hΦy])
    rw [this]
  · intro h k
    rw [← hΦ_apply, ← hθ]
    rfl

end CFSG.Sporadic.HN.Local
