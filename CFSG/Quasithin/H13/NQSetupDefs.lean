module

public import CFSG.Quasithin.H13.Statements
public import CFSG.Quasithin.Background.BlueprintB2Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

variable {G : Type} [Group G]

abbrev qtnqVc (M : Subgroup G) : Subgroup G :=
  (primeReducedAggregate ↥M 2).map M.subtype

abbrev qtnqU (L M : Subgroup G) : Subgroup G :=
  ⁅qtnqVc M, L⁆

structure QTNQ [Finite G] (T L M : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : QuasithinUnique.quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  not_excluded : ¬ QT13Excluded G
  maximal_local : quasithinIsMaximalLocal T L
  faithful_local : quasithinIsFaithfulLocal T L
  not_quasisimple : ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  t_le : T ≤ M
  eq_normalizer : M = Subgroup.normalizer (L : Set G)
  max_two_local : quasithinIsMaxTwoLocal M
  join_le : L ⊔ T ≤ M
  join_unique : ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → L ⊔ T ≤ M' → M' = M
  centralizer_eq_radical :
    L ⊓ Subgroup.centralizer (qtnqVc M : Set G) = (CFSG.solvableRadical ↥L).map L.subtype
  centralizer_le : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M
  centralizer_unique : ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M' → M' = M

namespace QTNQ

variable [Finite G] {T L M : Subgroup G}

theorem l_le (h : QTNQ T L M) : L ≤ M := by
  rw [h.eq_normalizer]
  exact Subgroup.le_normalizer

end QTNQ

end CFSG.Quasithin.H13
