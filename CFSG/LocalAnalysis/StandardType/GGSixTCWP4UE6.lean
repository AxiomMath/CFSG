module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6Disc
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UExc

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint

section Rank

theorem e6_finrank_le_two
    {Ψ : Set (Fin Tag.E6.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} (hρ : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ)
    (horth : ∀ γ ∈ Ψ, ∀ δ ∈ (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' Ψ,
      iform γ δ = 0 ∧ ¬ IsRoot .E6 (γ + δ)) :
    Module.finrank ℤ (Submodule.span ℤ Ψ) ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have hnorm : ∀ x ∈ Ψ, iform x x = 2 := fun x hx =>
    e6_iform_self x (mem_rootFinset.2 (hΨ.isRoot x hx))
  obtain ⟨α, hα, β, hβ, γ, hγ, hne1, hne2, hs, hbc, hg⟩ :=
    exists_path_of_three_le_finrank hΨ hnorm (by omega)
  have h4 := gram3_eq_four (hnorm α hα) (hnorm β hβ) (hnorm γ hγ) hne1 hne2 hs hbc hg
  have hcross : ∀ x ∈ Ψ, ∀ y ∈ Ψ, iform x (ρ y) = 0 := fun x hx y hy =>
    (horth x hx (ρ y) ⟨y, hy, rfl⟩).1
  exact e6_gram_false (hnorm α hα) (hnorm β hβ) (hnorm γ hγ)
    (by rw [hρ]; exact hnorm α hα) (by rw [hρ]; exact hnorm β hβ) (by rw [hρ]; exact hnorm γ hγ)
    (hρ α β) (hρ α γ) (hρ β γ)
    (hcross α hα α hα) (hcross α hα β hβ) (hcross α hα γ hγ)
    (hcross β hβ α hα) (hcross β hβ β hβ) (hcross β hβ γ hγ)
    (hcross γ hγ α hα) (hcross γ hγ β hβ) (hcross γ hγ γ hγ) h4

end Rank

section Leaf

theorem upper_E6_of_inputs_inner
    (hR : LangFamilyCompFieldSL)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .E6 n f).K →* X} (h : GGTCHyp .E6 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .E6 f) (htor : p = 3 → p ^ 5 ≤ Nat.card B)
    (hp3 : p ≠ 3 ∨ ¬ 3 ∣ 2 ^ f - 1) : Nat.card B ≤ p ^ 4 := by
  have hp := h.prime
  have hp2 := h.ne_two
  have hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E6 (2 ^ f) :=
    ((LieModel.chevalleyExceptional_iff (by decide)).1 h.model).2.2
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hTor : UToralAt .E6 p (Nat.card B) := by
    by_cases hp3' : p = 3
    · subst hp3'
      refine utoralAt_of_bigBar (τ := .E6) hp hp2
        ExcFramesHalf.bigElemAbelianToralBar_E6_three ?_
      have h5 := htor rfl
      have h6 : Tag.rank .E6 - 1 = 5 := rfl
      rw [h6]
      exact h5
    · exact utoralAt_of_nonTorsion hp hp2 (fun _ => hp3') (fun h => by cases h) hBpos
  obtain ⟨t', m, f', hlt, hm, -⟩ := hF
  obtain ⟨Ψ, ρ, hΨ, -, hρ, horth, hcard, -⟩ := uframe_main
    (uFieldInput_of_SL hR (Or.inl rfl)) (Or.inr (Or.inl rfl)) hp hp2 hmod
    h.b_norm (h.inner_E6 hp3) h.b_faithful h.b_elem h.d_le h.d_card
    (h.j_comp.1.trans inf_le_left) (Assembly.isComponentOf_iff_open.1 h.j_comp) h.j_cent
    ⟨t', m, f', hlt, hm⟩ hTor
  have hr := e6_finrank_le_two hΨ hρ horth
  exact hcard.trans (Nat.pow_le_pow_right hp.pos (by omega))

end Leaf

end CFSG.StandardType.TableCRes
