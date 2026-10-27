module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEndComp

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Assembly

section Bound

variable {G : Type*} [Group G]

theorem card_le_three_mul_inf_of_sup [Finite G] {X D : Subgroup G} (hX : IsCyclic X)
    (hXD : X ≤ Subgroup.centralizer (D : Set G)) {E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hEN : E ≤ X ⊔ D) : Nat.card E ≤ 3 * Nat.card (E ⊓ D : Subgroup G) := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G, N = X ⊔ D := ⟨_, rfl⟩
  subst hN
  set N : Subgroup G := X ⊔ D with hN
  have hle : N ≤ Subgroup.normalizer (D : Set G) :=
    sup_le (hXD.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  haveI hnorm : (D.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff le_sup_right]
    intro d k hd hk
    exact (Subgroup.mem_normalizer_iff.1 (hle hk) d).1 hd
  let π : N →* N ⧸ D.subgroupOf N := QuotientGroup.mk' _
  have hXsurj : Function.Surjective (π.comp (Subgroup.inclusion (le_sup_left : X ≤ N))) := by
    have h1 : (X.subgroupOf N) ⊔ (D.subgroupOf N) = ⊤ :=
      (Subgroup.subgroupOf_sup le_sup_left le_sup_right).symm.trans (Subgroup.subgroupOf_self N)
    have h2 : (X.subgroupOf N).map π = ⊤ := by
      have h3 : ((X.subgroupOf N) ⊔ (D.subgroupOf N)).map π = ⊤ := by
        rw [h1, Subgroup.map_top, MonoidHom.range_eq_top]
        exact QuotientGroup.mk'_surjective _
      rw [Subgroup.map_sup] at h3
      have h4 : (D.subgroupOf N).map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        exact (QuotientGroup.ker_mk' _).ge
      rwa [h4, sup_bot_eq] at h3
    intro q
    have hq : q ∈ (X.subgroupOf N).map π := by rw [h2]; trivial
    obtain ⟨n, hn, rfl⟩ := hq
    exact ⟨⟨n.1, hn⟩, rfl⟩
  haveI : IsCyclic (N ⧸ D.subgroupOf N) := isCyclic_of_surjective _ hXsurj
  let f : E →* N ⧸ D.subgroupOf N := π.comp (Subgroup.inclusion hEN)
  have hmem : ∀ e : E, f e = 1 ↔ (e : G) ∈ D := fun e => by
    change (QuotientGroup.mk (Subgroup.inclusion hEN e) : N ⧸ D.subgroupOf N) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact Iff.rfl
  have hker : Nat.card f.ker = Nat.card (E ⊓ D : Subgroup G) :=
    Nat.card_congr
      { toFun := fun e => ⟨e.1.1, e.1.2, (hmem e.1).1 e.2⟩
        invFun := fun g => ⟨⟨g.1, g.2.1⟩, (hmem ⟨g.1, g.2.1⟩).2 g.2.2⟩
        left_inv := fun e => rfl
        right_inv := fun g => rfl }
  have hrange : Nat.card f.range ≤ 3 := by
    refine card_le_three_of_injective_cyclic (inferInstance : IsCyclic (N ⧸ D.subgroupOf N))
      f.range.subtype Subtype.val_injective fun c => ?_
    obtain ⟨e, he⟩ := c.2
    refine Subtype.ext ?_
    change (c : N ⧸ D.subgroupOf N) ^ 3 = 1
    rw [← he, ← map_pow]
    have h3 : e ^ 3 = 1 := Subtype.ext (by simpa using hE.2 e.1 e.2)
    rw [h3, map_one]
  have hcard : Nat.card E = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker]
    exact congrArg (· * Nat.card f.ker)
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv)
  rw [hcard, hker]
  exact Nat.mul_le_mul_right _ hrange

theorem card_le_three_mul_inf_layer [Finite G] {X D : Subgroup G} (hX : IsCyclic X)
    (hXD : X ≤ Subgroup.centralizer (D : Set G)) (hD : IsQuasisimple D) {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (hEN : E ≤ X ⊔ D) :
    Nat.card E ≤ 3 * Nat.card (E ⊓ LargeEvenLayer (X ⊔ D) : Subgroup G) := by
  rw [(layer_sup_eq hX hXD hD).1]
  exact card_le_three_mul_inf_of_sup hX hXD hE hEN

end Bound

end CFSG.StandardType.TwE6D3

end
