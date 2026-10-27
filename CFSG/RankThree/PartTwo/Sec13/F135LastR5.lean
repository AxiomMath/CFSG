module

public import CFSG.RankThree.PartTwo.Sec13.F135LastParts

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13
open scoped commutatorElement

section Facts

variable {G : Type} [Group G] [Finite G]

theorem r5g_Y_le_cM {p : ℕ} (hp : p.Prime) {Y : Subgroup G} (hY : Nat.card Y = p) : Y ≤ cM Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic Y := isCyclic_of_prime_card hY
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact congrArg Subtype.val
    ((IsMulCommutative.is_comm (M := Y)).comm (⟨h, hh⟩ : Y) (⟨y, hy⟩ : Y))

theorem r5g_Y_sub {p : ℕ} (hp : p.Prime) {Y : Subgroup G} (hY : Nat.card Y = p) :
    Nat.card (Y.subgroupOf (cM Y)) = p ∧ Y.subgroupOf (cM Y) ≤ Subgroup.center (cM Y) := by
  have hYM := r5g_Y_le_cM hp hY
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv, hY]
  · intro m hm
    rw [Subgroup.mem_center_iff]
    intro g
    have hmY : (m : G) ∈ Y := Subgroup.mem_subgroupOf.mp hm
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp g.2) _ hmY).symm

theorem r5g_map_normalizer {M : Type*} [Group M] (R : Subgroup M) [R.Normal] (E : Subgroup M) {x : M}
    (hx : x ∈ Subgroup.normalizer (E : Set M)) :
    (x : M ⧸ R) ∈ Subgroup.normalizer ((E.map (QuotientGroup.mk' R) : Subgroup (M ⧸ R)) :
      Set (M ⧸ R)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hconj : ∀ y : M, (y : M ⧸ R) * h * (y : M ⧸ R)⁻¹ = QuotientGroup.mk' R y * h *
      (QuotientGroup.mk' R y)⁻¹ := fun y => rfl
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨x * e * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx e).mp he, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  · rintro ⟨e', he', hee⟩
    have hx' : x⁻¹ ∈ Subgroup.normalizer (E : Set M) := Subgroup.inv_mem _ hx
    refine ⟨x⁻¹ * e' * x, by simpa using (Subgroup.mem_normalizer_iff.mp hx' e').mp he', ?_⟩
    have h1 : QuotientGroup.mk' R e' = (x : M ⧸ R) * h * (x : M ⧸ R)⁻¹ := hee
    calc QuotientGroup.mk' R (x⁻¹ * e' * x)
        = (QuotientGroup.mk' R x)⁻¹ * QuotientGroup.mk' R e' * QuotientGroup.mk' R x := by
          simp only [map_mul, map_inv]
      _ = h := by
          rw [h1]
          show ((x : M ⧸ R))⁻¹ * ((x : M ⧸ R) * h * (x : M ⧸ R)⁻¹) * (x : M ⧸ R) = h
          group

theorem r5g_subgroupOf_normalizer (M U : Subgroup G) {f : M}
    (hf : (f : G) ∈ Subgroup.normalizer (U : Set G)) :
    f ∈ Subgroup.normalizer ((U.subgroupOf M : Subgroup M) : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp hf (h : G)

theorem r5g_cM_ne_top (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) {Y : Subgroup G}
    (hY : Y ≠ ⊥) : cM Y ≠ ⊤ := by
  intro htop
  have hYc : Y ≤ Subgroup.center G := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ cM Y := by rw [htop]; exact Subgroup.mem_top g
    exact ((Subgroup.mem_centralizer_iff.mp hg) y hy).symm
  rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
  · exact hY (le_bot_iff.mp (h ▸ hYc))
  · obtain ⟨a, b, hab⟩ := hn
    apply hab
    have := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ Subgroup.center G) a
    exact this

end Facts

end CFSG.RankThree.PartTwo.Sec13.F135Last
