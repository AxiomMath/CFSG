module

public import CFSG.Quasithin.Background.RonanG52Conj
public import CFSG.Quasithin.Background.RonanG52Steinberg

public section

namespace CFSG.Quasithin.RonanG52

open Equiv CFSG.QuasithinUnique CFSG.Quasithin.H13.A6 CFSG.Quasithin.H13.A6.G52

theorem exists_line_conj {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) (Perm (Fin 6)) V) (c : Perm (Fin 6)) (G' X : Set (Perm (Fin 6)))
    (L : AddSubgroup V) (hL : Nat.card L = 4) (hLG : ∀ g ∈ G', ∀ l ∈ L, τ g l ∈ L)
    (hX : ∀ g ∈ X, c⁻¹ * g * c ∈ G') :
    ∃ L' : Submodule (ZMod 2) V, Nat.card L' = 4 ∧ ∀ g ∈ X, ∀ v ∈ L', τ g v ∈ L' := by
  have hinj : Function.Injective (τ c) := (Representation.apply_bijective τ c).1
  refine ⟨(AddSubgroup.toZModSubmodule 2 L).map (τ c), ?_, ?_⟩
  · rw [← hL]
    exact (Nat.card_congr (Submodule.equivMapOfInjective (τ c) hinj
      (AddSubgroup.toZModSubmodule 2 L)).toEquiv).symm
  · rintro g hg v ⟨l, hl, rfl⟩
    refine ⟨τ (c⁻¹ * g * c) l, hLG _ (hX g hg) l hl, ?_⟩
    simp only [map_mul, Module.End.mul_apply]
    have : τ c (τ c⁻¹ (τ g (τ c l))) = τ g (τ c l) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    exact this

theorem nonempty_equiv_St_of_lines {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (τ : Representation (ZMod 2) (Perm (Fin 6)) V)
    (hτ : Representation.IsIrreducible τ) (Ga Gb : Subgroup (Perm (Fin 6))) (c : Perm (Fin 6))
    (hca : ∀ g ∈ g5G1, c⁻¹ * g * c ∈ Ga) (hcb : ∀ g ∈ cA6, c⁻¹ * g * c ∈ Gb)
    (M₁ M₂ : AddSubgroup V) (hM₁ : Nat.card M₁ = 4) (hM₂ : Nat.card M₂ = 4)
    (hM₁G : ∀ g ∈ Ga, ∀ l ∈ M₁, τ g l ∈ M₁) (hM₂G : ∀ g ∈ Gb, ∀ l ∈ M₂, τ g l ∈ M₂) :
    Nonempty (Representation.Equiv St τ) := by
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨L₁', hL₁', hL₁''⟩ := exists_line_conj τ c (Ga : Set (Perm (Fin 6)))
    (g5G1 : Set (Perm (Fin 6))) M₁ hM₁ hM₁G hca
  obtain ⟨L₂', hL₂', hL₂''⟩ := exists_line_conj τ c (Gb : Set (Perm (Fin 6)))
    (cA6 : Set (Perm (Fin 6))) M₂ hM₂ hM₂G hcb
  exact equiv_Mrep_three τ hτ L₁' L₂' hL₁' hL₂' hL₁'' hL₂''

theorem steinberg_of_fixesLines {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (τ : Representation (ZMod 2) (Perm (Fin 6)) V)
    (hτ : Representation.IsIrreducible τ) {T G₁ G₂ : Subgroup (Perm (Fin 6))}
    (hsyl : IsSylowTwoOf T (alternatingGroup (Fin 6)))
    (le₁ : G₁ ≤ alternatingGroup (Fin 6)) (le₂ : G₂ ≤ alternatingGroup (Fin 6))
    (T_le₁ : T ≤ G₁) (T_le₂ : T ≤ G₂)
    (index₁ : G₁.relIndex (alternatingGroup (Fin 6)) = 15)
    (index₂ : G₂.relIndex (alternatingGroup (Fin 6)) = 15) (ne : G₁ ≠ G₂)
    (only : ∀ H : Subgroup (Perm (Fin 6)), H ≤ alternatingGroup (Fin 6) → T ≤ H →
      H.relIndex (alternatingGroup (Fin 6)) = 15 → H = G₁ ∨ H = G₂)
    (L₁ L₂ : AddSubgroup V) (h₁ : Nat.card L₁ = 4) (h₂ : Nat.card L₂ = 4)
    (hL₁ : ∀ g ∈ G₁, ∀ l ∈ L₁, τ g l ∈ L₁) (hL₂ : ∀ g ∈ G₂, ∀ l ∈ L₂, τ g l ∈ L₂) :
    Nat.card V = 2 ^ 16 ∧
      Module.Projective (MonoidAlgebra (ZMod 2) (Perm (Fin 6))) τ.asModule := by
  obtain ⟨c, -, hc⟩ := exists_conj_g5G1_cA6 hsyl le₁ le₂ T_le₁ T_le₂ index₁ index₂ ne only
  obtain ⟨e⟩ : Nonempty (Representation.Equiv St τ) := by
    rcases hc with ⟨hc₁, hc₂⟩ | ⟨hc₁, hc₂⟩
    · exact nonempty_equiv_St_of_lines τ hτ G₁ G₂ c hc₁ hc₂ L₁ L₂ h₁ h₂ hL₁ hL₂
    · exact nonempty_equiv_St_of_lines τ hτ G₂ G₁ c hc₁ hc₂ L₂ L₁ h₂ h₁ hL₂ hL₁
  exact ⟨natCard_eq_two_pow_sixteen e, projective_of_equiv_St e⟩

end CFSG.Quasithin.RonanG52
