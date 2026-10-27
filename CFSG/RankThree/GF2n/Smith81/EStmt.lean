module

public import CFSG.RankThree.GF2n.Smith81.ESetup
public import CFSG.RankThree.GF2n.Smith81.Lanes
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Smith28EStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → ∀ (X : Subgroup G) (x : G), Sit M Q Z X x →
      ∃ v : G, IsConj x v ∧ v ∈ Q ∧ v ∈ QB X

section Eight

variable [Finite G]

theorem card_bar_eq_of_inf_eq_bot {M Q S : Subgroup G} [(Q.subgroupOf M).Normal] (hSM : S ≤ M)
    (h : S ⊓ Q = ⊥) : Nat.card (bar M Q S) = Nat.card S := by
  have hinj : Function.Injective
      ((QuotientGroup.mk' (Q.subgroupOf M)).domRestrict (S.subgroupOf M)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : (x : ↥M) ∈ Q.subgroupOf M := (QuotientGroup.eq_one_iff _).mp hx
    have hxS : ((x : ↥M) : G) ∈ S := x.2
    have hxQ : ((x : ↥M) : G) ∈ Q := hx1
    have h1 : ((x : ↥M) : G) ∈ S ⊓ Q := ⟨hxS, hxQ⟩
    rw [h, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have h1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [MonoidHom.domRestrict_range] at h1
  exact h1.symm.trans (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv)

end Eight

@[expose] def Smith212ENonfusedStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ x : G, x ∈ M → x ∉ Q → IsConj z x →
      ∀ w ∈ Z, w ≠ 1 → ¬ IsConj x (x * w)

@[expose] def Smith213EStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → ∀ z ∈ Z, z ≠ 1 →
      Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G))

section Twelve

variable [Finite G]

theorem conjClassSet_inter_cosetSet_eq {z x : G} {Z : Subgroup G} (hx : IsConj z x)
    (h : ∀ w ∈ Z, w ≠ 1 → ¬ IsConj x (x * w)) : conjClassSet z ∩ cosetSet x Z = {x} := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, w, hw, hwy⟩
    subst hwy
    by_contra hne
    have hw1 : w ≠ 1 := fun h1 => hne (by simp [h1])
    exact h w hw hw1 (hx.symm.trans hy)
  · rintro rfl
    exact ⟨hx, 1, Subgroup.one_mem Z, by simp⟩

end Twelve

@[expose] def Smith216ECountStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ A C : Subgroup G, IsZConjugate Z A →
      IsZConjugate Z C → A ≠ C → C ≤ QB A → ∃ S : Subgroup G, S ≤ QB A ⊓ QB C ∧
        (∀ s ∈ S, s ≠ 1 → IsConj z s) ∧ Nat.card Z ^ 2 < Nat.card S

@[expose] def Smith216EOddStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ x z' w y : G, IsConj z x → IsConj z z' →
      IsConj z w → IsConj z y → Commute x z' → Commute z' w → Commute w y → ¬ Commute x w →
      ¬ Commute z' y → Odd (orderOf (x * w)) → Odd (orderOf (z' * y)) →
        ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y

@[expose] def Smith216EStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ x z' w y : G, IsConj z x → IsConj z z' →
      IsConj z w → IsConj z y → Commute x z' → Commute z' w → Commute w y →
        ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y

@[expose] def Smith219EInspectionStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B →
      (∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z)) →
        Timmesfeld.Outcome (FStar G) → SmithLaneE M Q Z B

end CFSG.RankThree.GF2n.Smith81
