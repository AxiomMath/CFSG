module

public import CFSG.Permutation.FiveTransitive.InvariantSylow

public section

namespace CFSG

namespace FiveTransitive.NormalizerInvariantSylow

theorem exists_of_pgroup
    (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Finite G]
    (H R : Subgroup G) (hR : IsPGroup p R)
    (hnorm : R ≤ Subgroup.normalizer (H : Set G)) :
    ∃ P : Sylow p H,
      R ≤ Subgroup.normalizer (((P : Subgroup H).map H.subtype) : Set G) := by
  let f : R →* MulAut H := H.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  obtain ⟨P, hP⟩ := InvariantSylow.exists_invariant_hom p R H hR f
  refine ⟨P, Subgroup.le_normalizer_iff.mpr ?_⟩
  intro r hr h hh
  obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hh
  have hin := hP ⟨r, hr⟩ h' hh'
  refine Subgroup.mem_map.mpr ⟨f ⟨r, hr⟩ h', hin, ?_⟩
  exact H.normalizerMonoidHom_apply_apply_coe ⟨r, hnorm hr⟩ h'

theorem exists_of_order_pow
    (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Finite G]
    (H : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (H : Set G))
    (k : ℕ) (hk : orderOf a = p ^ k) :
    ∃ P : Sylow p H,
      a ∈ Subgroup.normalizer (((P : Subgroup H).map H.subtype) : Set G) := by
  have hp : IsPGroup p (Subgroup.zpowers a) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hn : Subgroup.zpowers a ≤ Subgroup.normalizer (H : Set G) :=
    Subgroup.zpowers_le.mpr ha
  obtain ⟨P, hP⟩ := exists_of_pgroup p G H (Subgroup.zpowers a) hp hn
  exact ⟨P, hP (Subgroup.mem_zpowers a)⟩

end FiveTransitive.NormalizerInvariantSylow

end CFSG
