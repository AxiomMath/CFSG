module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Group

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem exists_noncyclic_pGroup_of_perfect_section {H Z : Type*} [Group H] [Finite H] [Group Z]
    (ψ : H →* Z) (hψ : Function.Surjective ψ) {p : ℕ} [Fact p.Prime] {P₀ : Subgroup Z}
    (hP₀ : Group.IsPerfect P₀) (hpP₀ : p ∣ Nat.card P₀) (hpker : p ∣ Nat.card ψ.ker) :
    ∃ X : Subgroup H, IsPGroup p X ∧ ¬ IsCyclic X := by
  let H₂ : Subgroup H := P₀.comap ψ
  have hker_le : ψ.ker ≤ H₂ := MonoidHom.ker_le_comap ψ P₀
  let φ : H₂ →* P₀ := (ψ.domRestrict H₂).codRestrict P₀ fun x => by
    change ψ (x : H) ∈ P₀
    exact x.2
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨h, hh⟩ := hψ x
    refine ⟨⟨h, ?_⟩, ?_⟩
    · change ψ h ∈ P₀
      rw [hh]
      exact x.2
    · apply Subtype.ext
      exact hh
  have hφker : Nat.card φ.ker = Nat.card ψ.ker := by
    have h1 : φ.ker = ψ.ker.subgroupOf H₂ := by
      ext x
      change φ x = 1 ↔ ψ (x : H) = 1
      exact ⟨fun hx => congrArg Subtype.val hx, fun hx => Subtype.ext hx⟩
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
  haveI : Group.IsPerfect P₀ := hP₀
  obtain ⟨P : Sylow p H₂⟩ := Sylow.nonempty (p := p) (G := H₂)
  have hPnc : ¬ IsCyclic (P : Subgroup H₂) :=
    not_isCyclic_sylow_of_perfect_quotient φ hφ hpP₀ (hφker.symm ▸ hpker) P
  refine ⟨(P : Subgroup H₂).map H₂.subtype, (P.isPGroup').map H₂.subtype, ?_⟩
  intro hc
  exact hPnc ((MulEquiv.isCyclic
    (Subgroup.equivMapOfInjective (P : Subgroup H₂) H₂.subtype H₂.subtype_injective)).2 hc)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
