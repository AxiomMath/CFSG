module

public import CFSG.Quasithin.Background.G118Hyp
public import CFSG.Quasithin.Background.G116IIModule
public import CFSG.Quasithin.Background.G116IIQuasi

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_component_data [Finite V] {Γ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    {x : GLV V} (hL : IsComponentOf L Γ) (hnum : numConjugates Γ L ≤ 2)
    (hirr : IsIrr (normalClosure Γ L) I) (hfH : FaithfulOn (normalClosure Γ L) I) (hxΓ : x ∈ Γ)
    (hcompl : IsCompl I (conjSub x I)) (hn : ¬ HIso (normalClosure Γ L) I (conjSub x I))
    (hdual : IsDualOf (normalClosure Γ L) I (conjSub x I)) {Y : Subgroup (GLV V)}
    (hYne : ∃ y ∈ Y, y ≠ 1)
    (hYC : ∀ y ∈ Y, (∀ h ∈ normalClosure Γ L, y * h = h * y) → y = 1) :
    ∃ L₁ : Subgroup (GLV V), IsComponentOf L₁ Γ ∧ L₁ ≤ normalClosure Γ L ∧
      (∃ a ∈ Y, ∃ l ∈ L₁, a * l ≠ l * a) ∧
      (normalClosure Γ L = L₁ ∨ ∃ L₂ : Subgroup (GLV V), IsComponentOf L₂ Γ ∧ L₂ ≠ L₁ ∧
        normalClosure Γ L = L₁ ⊔ L₂ ∧ ∃ (hL₁I : Invariant L₁ I) (hL₂I : Invariant L₂ I),
          QuasiEquivalent (restrictRange L₁ I hL₁I) (restrictRange L₂ I hL₂I)) := by
  set H := normalClosure Γ L with hH
  have hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H := normalClosure_normal Γ L
  obtain ⟨y₀, hy₀Y, hy₀⟩ := hYne
  by_cases hall : ∀ γ ∈ Γ, L.map (MulAut.conj γ).toMonoidHom = L
  ·
    have hHL : H = L := normalClosure_eq_of_conj_eq hall
    refine ⟨L, hL, le_normalClosure Γ L, ?_, Or.inl hHL⟩
    by_contra hcon
    push Not at hcon
    exact hy₀ (hYC y₀ hy₀Y fun h hh => hcon y₀ hy₀Y h (hHL ▸ hh))
  · push Not at hall
    obtain ⟨γ, hγ, hne⟩ := hall
    set L₂ : Subgroup (GLV V) := L.map (MulAut.conj γ).toMonoidHom with hL₂
    have hHsup : H = L ⊔ L₂ := normalClosure_eq_sup_of_numConjugates_le_two hnum hγ hne
    have hcL₂ : IsComponentOf L₂ Γ := isComponentOf_map_conj hL hγ
    have hLH : L ≤ H := le_normalClosure Γ L
    have hL₂H : L₂ ≤ H := map_conj_le_normalClosure hγ
    have hmapγ : L.map (MulAut.conj γ).toMonoidHom = L₂ := rfl
    have hmapγ' : L₂.map (MulAut.conj γ⁻¹).toMonoidHom = L := Comp.map_conj_inv_map_conj
    have hcase : ∀ t ∈ Γ, conjSub t I = I ∨ IsDualOf H I (conjSub t I) := fun t ht =>
      conjSub_eq_or_isDualOf hN hxΓ ht hirr hcompl hn hdual
    have qe1 := quasiEquivalent_restrictRange_of_conj hirr hfH hLH hL₂H
      (fun h hh => hN γ hγ h hh) hmapγ (hcase γ hγ)
    have qe2 := quasiEquivalent_restrictRange_of_conj hirr hfH hL₂H hLH
      (fun h hh => hN γ⁻¹ (Γ.inv_mem hγ) h hh) hmapγ' (hcase γ⁻¹ (Γ.inv_mem hγ))
    by_cases hLY : ∃ a ∈ Y, ∃ l ∈ L, a * l ≠ l * a
    · exact ⟨L, hL, hLH, hLY, Or.inr ⟨L₂, hcL₂, hne, hHsup, qe1⟩⟩
    · have hL₂Y : ∃ a ∈ Y, ∃ l ∈ L₂, a * l ≠ l * a := by
        by_contra hcon
        push Not at hLY hcon
        refine hy₀ (hYC y₀ hy₀Y fun h hh => ?_)
        have hle : L ⊔ L₂ ≤ Subgroup.centralizer ({y₀} : Set (GLV V)) :=
          sup_le (fun l hl => Subgroup.mem_centralizer_iff.2 fun g hg => by
              rw [Set.mem_singleton_iff] at hg
              rw [hg]
              exact hLY y₀ hy₀Y l hl)
            (fun l hl => Subgroup.mem_centralizer_iff.2 fun g hg => by
              rw [Set.mem_singleton_iff] at hg
              rw [hg]
              exact hcon y₀ hy₀Y l hl)
        exact Subgroup.mem_centralizer_iff.1 (hle (hHsup ▸ hh)) y₀ (Set.mem_singleton y₀)
      exact ⟨L₂, hcL₂, hL₂H, hL₂Y, Or.inr ⟨L, hL, hne.symm, by rw [hHsup, sup_comm], qe2⟩⟩

end G11

end CFSG.Quasithin
