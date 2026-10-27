module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog
public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms

theorem autRank_of_outer_two {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥)
    (hcard : Nat.card (MulAut S) ≤ 2 * Nat.card S) {r : ℕ}
    (hr : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r)
    (B : Subgroup (MulAut S)) (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hs : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 2 ^ (r + 1) := by
  let c : S →* MulAut S := MulAut.conj
  have hcinj : Function.Injective c :=
    CFSG.QuasithinUnique.Setup.Family.conj_injective_of_center_eq_bot hcen
  have hIcard : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner S) = Nat.card S :=
    (Nat.card_congr (MonoidHom.ofInjective hcinj).toEquiv).symm
  have hidx : (CFSG.ComponentClassification.OuterAutomorphisms.inner S).index ≤ 2 := by
    have hmul := Subgroup.card_mul_index (CFSG.ComponentClassification.OuterAutomorphisms.inner S)
    rw [hIcard] at hmul
    have hpos : 0 < Nat.card S := Nat.card_pos
    nlinarith
  have hrel : (CFSG.ComponentClassification.OuterAutomorphisms.inner S).relIndex B ≤ 2 := by
    have hd := Subgroup.relIndex_dvd_index_of_normal (H := CFSG.ComponentClassification.OuterAutomorphisms.inner S) B
    have hne : (CFSG.ComponentClassification.OuterAutomorphisms.inner S).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd).trans hidx
  have h1 := Subgroup.relIndex_mul_card (H := CFSG.ComponentClassification.OuterAutomorphisms.inner S) (K := B)
  have hmap : (B.comap c).map c = CFSG.ComponentClassification.OuterAutomorphisms.inner S ⊓ B := by
    rw [Subgroup.map_comap_eq]
    rfl
  have hcard' : Nat.card ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner S ⊓ B) = Nat.card (B.comap c) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective hcinj
  have hB0 : Nat.card (B.comap c) ≤ 2 ^ r := by
    refine hr (B.comap c) ?_ ?_
    · intro x hx y hy
      apply hcinj
      rw [map_mul, map_mul]
      exact hc _ hx _ hy
    · intro x hx
      apply hcinj
      rw [map_mul, map_one]
      exact hs _ hx
  calc Nat.card B = (CFSG.ComponentClassification.OuterAutomorphisms.inner S).relIndex B * Nat.card ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner S ⊓ B) := h1.symm
    _ ≤ 2 * 2 ^ r := by
      rw [hcard']
      exact Nat.mul_le_mul hrel hB0
    _ = 2 ^ (r + 1) := by ring

theorem m12_autRank :
    ∀ B : Subgroup (MulAut ↥NativeSporadic.M12),
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 4 :=
  fun B hc hs => autRank_of_outer_two (S := ↥NativeSporadic.M12)
    CFSG.Sporadic.Schreier.m12_center_eq_bot'
    CFSG.Sporadic.Schreier.m12_mulAut_card (r := 3) CFSG.QuasithinUnique.Setup.X1.m12_rank_le B hc hs

theorem m12_cover :
    ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* NativeSporadic.Carrier .M12),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥ :=
  fun E _ _ _ π hπ hC hodd => CFSG.SectionRank.M12_perfect_odd_cover_trivial π hπ hC hodd

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
