module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRegionDefs
public import CFSG.RankThree.PartOne.S11d.LieComponentLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem

section Abstract

variable {U U' G : Type*} [Group U] [Group U'] [Group G]

theorem ggConj_eq_of_card_two {H : Subgroup U'} (h2 : Nat.card H = 2) {h z : U'}
    (hh : h ∈ Subgroup.normalizer (H : Set U')) (hz : z ∈ H) : h * z * h⁻¹ = z := by
  have hz' : h * z * h⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hh z).mp hz
  by_cases h1 : z = 1
  · subst h1; simp
  · have h1' : h * z * h⁻¹ ≠ 1 := by
      intro h0; apply h1
      have : h * z = h := by simpa [mul_inv_eq_one] using h0
      simpa using this
    obtain ⟨a, b, hab, hall⟩ := Nat.card_eq_two_iff.mp h2
    have key : ∀ c d : H, c ≠ 1 → d ≠ 1 → c = d := by
      intro c d hc hd
      have hc' : c ∈ ({a, b} : Set H) := hall ▸ Set.mem_univ c
      have hd' : d ∈ ({a, b} : Set H) := hall ▸ Set.mem_univ d
      have h1m : (1 : H) ∈ ({a, b} : Set H) := hall ▸ Set.mem_univ 1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc' hd' h1m
      rcases h1m with h1m | h1m <;> rcases hc' with rfl | rfl <;> rcases hd' with rfl | rfl <;>
        first | rfl | (exact absurd h1m.symm hc) | (exact absurd h1m.symm hd)
    have := key ⟨_, hz'⟩ ⟨_, hz⟩ (by simpa [Subtype.ext_iff] using h1')
      (by simpa [Subtype.ext_iff] using h1)
    simpa [Subtype.ext_iff] using this

variable (Δ : UniversalRootDatum U) (Δ' : UniversalRootDatum U')

end Abstract

section Restrict

variable {G : Type*} [Group G]

theorem ggIsComponentOf_inf_of_le {L K H : Subgroup G} (h : IsComponentOf L K) (hLH : L ≤ H) :
    IsComponentOf L (K ⊓ H) := by
  refine ⟨le_inf h.1 hLH, ?_, h.2.2⟩
  have := h.2.1.inf H
  rwa [inf_eq_left.mpr hLH] at this

end Restrict

section Cell

@[expose] def GGSecFiveQTwoCell {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) : Prop :=
  GGInnerDiagOnLabel GGLabQTwo p Bs L ∧
    (GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₆ ∨
      GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₇ ∨
      GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₈ ∨
      GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.F₄)

end Cell

end CFSG.StandardType

end
