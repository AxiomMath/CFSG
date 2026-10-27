module

public import CFSG.Quasithin.Background.JonesParshallCurtisModels
public import CFSG.Quasithin.Background.JonesParshallCurtisBound

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.JonesParshall.Curtis

open Matrix

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem type_of_unique {ρ : Representation (ZMod 2) G5 V} {y : V} {s : Fin 4}
    (hs : Th ρ s y ≠ 0) (hother : ∀ t, t ≠ s → Th ρ t y = 0) (t : Fin 4) :
    Th ρ t y = 0 ↔ t ≠ s :=
  ⟨fun h hts => hs (hts ▸ h), hother t⟩

theorem classify_ten
    {ρ : Representation (ZMod 2) G5 V} (hρ : IsSimpleRep ρ) [Finite V]
    (hdim : Module.finrank (ZMod 2) V = 10) :
    (∃ β : V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2), ∀ g v, β (ρ g v) = wedgeRep g (β v)) ∨
      ∃ β : V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2), ∀ g v, β (ρ g v) = wedgeRep (twistα g) (β v) := by
  have := hρ.1
  obtain ⟨y, hy, hy0⟩ := exists_fixU_ne ρ
  by_cases hall : ∀ s, Th ρ s y = 0
  · exfalso
    obtain ⟨β, -⟩ := iso_of_type hρ triv_simple hy hy0 (triv_fixU 1) one_ne_zero
      fun s => iff_of_true (hall s) (triv_type s)
    have h := β.finrank_eq
    rw [hdim, Module.finrank_self] at h
    omega
  · push Not at hall
    obtain ⟨s, hs⟩ := hall
    have hother : ∀ t, t ≠ s → Th ρ t y = 0 := fun t hts => by
      by_contra ht
      have := eleven_le_finrank' hρ hy hy0 hts ht hs
      omega
    have hJ := type_of_unique hs hother
    rcases (by decide : ∀ s : Fin 4, s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) s with rfl | rfl | rfl | rfl
    · exfalso
      obtain ⟨β, -⟩ := iso_of_type hρ natRep_simple hy hy0 e0_mem_fixU e0_ne
        fun t => (hJ t).trans (natRep_type t).symm
      have h := β.finrank_eq
      rw [hdim, Module.finrank_fin_fun] at h
      omega
    · left
      exact iso_of_type hρ wedge_simple hy hy0 e01_mem_fixU e01_ne
        fun t => (hJ t).trans (wedge_type t).symm
    · right
      obtain ⟨β, hβ⟩ := iso_of_type hρ wedgeTw_simple hy hy0 e01_mem_fixU_tw e01_ne
        fun t => (hJ t).trans (wedgeTw_type t).symm
      exact ⟨β, fun g v => (hβ g v).trans (wedgeTw_apply g (β v))⟩
    · exfalso
      obtain ⟨β, -⟩ := iso_of_type hρ natTw_simple hy hy0 e0_mem_fixU_tw e0_ne
        fun t => (hJ t).trans (natTw_type t).symm
      have h := β.finrank_eq
      rw [hdim, Module.finrank_fin_fun] at h
      omega

theorem isSimpleRep_of_irreducible {Γ : Type*} [Group Γ] [Nontrivial V]
    {ρ : Representation (ZMod 2) Γ V} (θ : Γ ≃* G5) (hρ : ρ.IsIrreducible) :
    IsSimpleRep (ρ.comp θ.symm.toMonoidHom) := by
  refine ⟨inferInstance, fun W hW => ?_⟩
  let σ : Subrepresentation ρ :=
    { toSubmodule := W
      apply_mem_toSubmodule := by
        intro γ v hv
        have h := hW (θ γ) v hv
        simpa using h }
  rcases IsSimpleOrder.eq_bot_or_eq_top σ with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

theorem finrank_H1_irreducible_ten
    {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) Γ W}
    (θ : Γ ≃* SpecialLinearGroup (Fin 5) (ZMod 2)) (hρ : ρ.IsIrreducible)
    (hdim : Module.finrank (ZMod 2) W = 10) : Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  have hpos : 0 < Module.finrank (ZMod 2) W := by omega
  have : Module.Finite (ZMod 2) W := Module.finite_of_finrank_pos hpos
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have : Nontrivial W := Module.nontrivial_of_finrank_pos hpos
  have : Finite Γ := Finite.of_equiv _ θ.toEquiv.symm
  apply finrank_H1_of_card
  rcases classify_ten (isSimpleRep_of_irreducible θ hρ) hdim with ⟨β, hβ⟩ | ⟨β, hβ⟩
  · have hβ' : ∀ γ w, β.toAddEquiv (ρ γ w) = muW (ZMod 2) (θ γ) (β.toAddEquiv w) :=
      fun γ w => by
        have h := hβ (θ γ) w
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.symm_apply_apply] at h
        exact h
    rw [card_H1_eq_of_card ρ hβ' card_Z1A_wedge, pow_zero]
  · have hβ' : ∀ γ w, β.toAddEquiv (ρ γ w) =
        muW (ZMod 2) ((θ.trans twistα) γ) (β.toAddEquiv w) :=
      fun γ w => by
        have h := hβ (θ γ) w
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.symm_apply_apply] at h
        exact h
    rw [card_H1_eq_of_card ρ hβ' card_Z1A_wedge, pow_zero]

end CFSG.Quasithin.JonesParshall.Curtis
