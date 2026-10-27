module

public import CFSG.RankThree.GF2n.Smith81.Sec2Defs
public import CFSG.RankThree.GF2n.Smith81.Bridge

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem mem_Lgen_of_mem {M L : Subgroup G} {x : G} (hx : x ∈ L) : x ∈ Lgen M L := by
  unfold Lgen
  refine (Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem M.one_mem ?_))
  rw [conjSubgroup_one]
  exact hx

@[expose] def Smith212Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ x : G, x ∈ M → x ∉ Q → IsConj z x →
      (conjClassSet z ∩ cosetSet x Z = {x}) ∧
      ({g : G | IsConj x g} ∩ {g : G | ∃ q ∈ Q, g = x * q} = conjOrbit Q x) ∧
      (∀ X : Subgroup G, IsZConjugate Z X → x ∈ X →
        (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x⁆ ⊔ Z) ∧
      (((Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) =
        CQt Q Z (Subgroup.zpowers x))

@[expose] def Smith216Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ x z' w y : G, IsConj z x → IsConj z z' → IsConj z w →
      IsConj z y → Commute x z' → Commute z' w → Commute w y →
        ∃ v : G, IsConj z v ∧ Commute x v ∧ Commute v y

theorem smith216At_of_statement (h : Smith216Statement) {G : Type} [Group G] [Finite G]
    (hb : Smith216Below (Nat.card G)) : Smith216At G :=
  fun M Q Z B hT => h G M Q Z B ⟨hT, hb⟩

@[expose] def Smith217Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → ∀ z ∈ Z, z ≠ 1 → ∀ x y : G, IsConj z x → IsConj z y →
      Relation.ReflTransGen (CommOn (conjClassSet z)) x y

end CFSG.RankThree.GF2n.Smith81
