module

public import CFSG.Permutation.FiveTransitive.GenericSylowFixedAction
public import CFSG.Permutation.FiveTransitive.NormalSylowFixedFive
public import CFSG.Permutation.FiveTransitive.FourTransitiveEvenStabilizer

public section

namespace CFSG

namespace FiveTransitive.NormalSylowFixedDegree

open MulAction Subgroup GenericSylowFixedAction

theorem internal_normalizer_four_transitive
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (s : Set X) (hs : s.ncard = 4) {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup G s)) :
    MulAction.IsMultiplyPretransitive (sylowNormalizer G X s S) (sylowFixedPoints G X s S) 4 := by
  apply FiveTransitive.isMultiplyPretransitive_of_explicit _ _ 4
  apply sylowNormalizer_transitive_on_fixedPoints G X 4 _ s hs S
  intro a b ha hb
  obtain ⟨g, hg⟩ := h4.exists_smul_eq (⟨a, ha⟩ : Fin 4 ↪ X) ⟨b, hb⟩
  exact ⟨g, fun i => DFunLike.congr_fun hg i⟩

theorem fixed_degree_le_twentySix
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup G s)) :
    Nat.card (sylowFixedPoints G X s S) ≤ 26 := by
  classical
  let K := sylowNormalizer G X s S
  let F := sylowFixedPoints G X s S
  let _ : Fintype F := Fintype.ofFinite F
  let J := (MulAction.toPermHom K F).range
  let sF : Set F := {x | (x : X) ∈ s}
  have hsF : s ⊆ (F : Set X) := base_subset_fixedPoints G X s S
  let e : s ≃ sF :=
    { toFun := fun x => ⟨⟨x.1, hsF x.2⟩, x.2⟩
      invFun := fun x => ⟨x.1.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsFcard : sF.ncard = 4 := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr e.symm, Nat.card_coe_set_eq, hs]
  have hK4 := internal_normalizer_four_transitive G X h4 s hs S
  have hJ4 : MulAction.IsMultiplyPretransitive J F 4 :=
    FiveTransitive.isMultiplyPretransitive_range_toPermHom K F 4 hK4
  have hfree := prime_not_dvd_fixedAction_stabilizer_card G X s S
  change ¬ 2 ∣ Nat.card (fixingSubgroup J sF) at hfree
  by_contra hlarge
  have hdegree : 27 ≤ Fintype.card F := by
    change ¬ Nat.card F ≤ 26 at hlarge
    rw [Nat.card_eq_fintype_card] at hlarge
    omega
  obtain ⟨k, hk⟩ := FourTransitiveEvenStabilizer.even_card_fixingSubgroup
    J F hdegree hJ4 sF hsFcard
  exact hfree ⟨k, by omega⟩

theorem mem_internal_fixedPoints_iff
    (G X : Type) [Group G] [MulAction G X]
    (s : Set X) {p : ℕ} (S : Sylow p (fixingSubgroup G s)) (x : X) :
    x ∈ sylowFixedPoints G X s S ↔ ∀ z : S, z • x = x := by
  constructor
  · intro hx z
    have hz : (((z : fixingSubgroup G s) : G)) ∈ sylowImage G X s S :=
      Subgroup.mem_map_of_mem (fixingSubgroup G s).subtype z.property
    let zK : sylowNormalizer G X s S := ⟨_, Subgroup.le_normalizer hz⟩
    exact hx (⟨zK, hz⟩ : sylowInNormalizer G X s S)
  · intro hx z
    obtain ⟨u, huS, hu⟩ := Subgroup.mem_map.mp z.property
    change ((z : sylowNormalizer G X s S) : G) • x = x
    exact (congrArg (fun g : G => g • x) hu).symm.trans (hx ⟨u, huS⟩)

theorem normal_fixedPoints_eq_internal
    (G X : Type) [Group G] [MulAction G X]
    (N : Subgroup G) (s : Set X) {p : ℕ} (S : Sylow p (fixingSubgroup N s)) :
    NormalSylowFixedFive.normalSylowFixedPoints G X N s S = sylowFixedPoints N X s S := by
  ext x
  rw [mem_internal_fixedPoints_iff]
  constructor
  · intro hx z
    have hz : (((z : fixingSubgroup N s) : N) : G) ∈
        NormalSylowFixedFive.normalSylowImage G X N s S :=
      Subgroup.mem_map_of_mem (N.subtype.comp (fixingSubgroup N s).subtype) z.property
    let zK : NormalSylowFixedFive.normalSylowNormalizer G X N s S :=
      ⟨_, Subgroup.le_normalizer hz⟩
    exact hx (⟨zK, hz⟩ : NormalSylowFixedFive.normalSylowInNormalizer G X N s S)
  · intro hx z
    obtain ⟨u, huS, hu⟩ := Subgroup.mem_map.mp z.property
    change ((z : NormalSylowFixedFive.normalSylowNormalizer G X N s S) : G) • x = x
    exact (congrArg (fun g : G => g • x) hu).symm.trans (hx ⟨u, huS⟩)

end FiveTransitive.NormalSylowFixedDegree

end CFSG
