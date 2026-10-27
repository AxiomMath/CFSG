module

public import CFSG.Permutation.FiveTransitive.StabilizerSylowConjugacy

public section

namespace CFSG

namespace FiveTransitive.StabilizerSylowFusion

open MulAction

private theorem exists_sylow_at_fixed_point
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    {p : ℕ} [Fact p.Prime] (x y : X) (hxy : ∃ g : G, g • x = y)
    (P : Sylow p (stabilizer G x))
    (hPy : (P : Subgroup (stabilizer G x)).map (stabilizer G x).subtype ≤
      stabilizer G y) :
    ∃ S : Sylow p (stabilizer G y),
      (S : Subgroup (stabilizer G y)).map (stabilizer G y).subtype =
        (P : Subgroup (stabilizer G x)).map (stabilizer G x).subtype := by
  let A := (P : Subgroup (stabilizer G x)).map (stabilizer G x).subtype
  obtain ⟨g, hg⟩ := hxy
  have hcard : Nat.card (stabilizer G x) = Nat.card (stabilizer G y) :=
    Nat.card_congr (stabilizerEquivStabilizer hg.symm).toEquiv
  have hA : Nat.card A = Nat.card P :=
    (Nat.card_congr ((P : Subgroup (stabilizer G x)).equivMapOfInjective
      (stabilizer G x).subtype (stabilizer G x).subtype_injective).toEquiv).symm
  have hsub : Nat.card (A.subgroupOf (stabilizer G y)) =
      p ^ (Nat.card (stabilizer G y)).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPy).toEquiv, hA,
      P.card_eq_multiplicity, hcard]
  let S : Sylow p (stabilizer G y) := Sylow.ofCard _ hsub
  exact ⟨S, Subgroup.map_subgroupOf_eq_of_le hPy⟩

theorem eq_of_normalizer_fixes
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    {p : ℕ} [Fact p.Prime] (x y : X) (hxy : ∃ g : G, g • x = y)
    (P : Sylow p (stabilizer G x))
    (hPy : (P : Subgroup (stabilizer G x)).map (stabilizer G x).subtype ≤
      stabilizer G y)
    (hNy : ∀ g : G, g ∈ Subgroup.normalizer
      (((P : Subgroup (stabilizer G x)).map (stabilizer G x).subtype) : Set G) →
      g • y = y) : x = y := by
  obtain ⟨S, hS⟩ := exists_sylow_at_fixed_point x y hxy P hPy
  obtain ⟨g, hg, hmap⟩ :=
    StabilizerSylowConjugacy.exists_conjugating_transporter x y hxy P S
  have hN : g ∈ Subgroup.normalizer
      (((P : Subgroup (stabilizer G x)).map (stabilizer G x).subtype) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hmap.trans hS)
  exact (MulAction.injective g) (hg.trans (hNy g hN).symm)

end FiveTransitive.StabilizerSylowFusion

end CFSG
