module

public import CFSG.Quasithin.H13.NQSetupDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

variable {G : Type} [Group G]

@[expose] def nqPrimeResidualX (D : Subgroup G) (p : ℕ) : Subgroup G :=
  (Subgroup.closure {e : D | e ∈ (Subgroup.closure
      {c : D ⧸ CFSG.pCore 2 D | c ∈ CFSG.pCore p (D ⧸ CFSG.pCore 2 D) ∧ c ^ p = 1}).comap
        (QuotientGroup.mk' (CFSG.pCore 2 D)) ∧ Odd (orderOf e)}).map D.subtype

@[expose] def nqOriginalCentralizer (T L : Subgroup G) : Set G :=
  {t | t ∈ T ∧ ∀ l ∈ L, t * l * t⁻¹ * l⁻¹ ∈ (CFSG.solvableRadical L).map L.subtype}

@[expose] def nqOriginalK (T L : Subgroup G) : Subgroup G :=
  (CFSG.perfectResidual ↥(L ⊓ Subgroup.normalizer (nqOriginalCentralizer T L))).map
    (L ⊓ Subgroup.normalizer (nqOriginalCentralizer T L)).subtype

structure QTTMaxNQPrime [Finite G] (T L M D : Subgroup G) (p : ℕ) (X : Subgroup G) : Prop where
  qtnq : QTNQ T L M
  maximal_local : quasithinIsMaximalLocal T D
  faithful_local : quasithinIsFaithfulLocal T D
  le_normalizer : T ≤ Subgroup.normalizer (D : Set G)
  not_quasisimple : ¬ CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D)
  prime : p.Prime
  five_le : 5 ≤ p
  core_ne_bot : CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) ≠ ⊥
  eq_residual : X = nqPrimeResidualX D p

structure QTMaxNQPrime [Finite G] (T L M D : Subgroup G) (p : ℕ) (X : Subgroup G) : Prop where
  qtnq : QTNQ T L M
  maximal_local : quasithinIsMaximalLocal T D
  faithful_local : quasithinIsFaithfulLocal T D
  original_K_le : nqOriginalK T L ≤ D
  not_quasisimple : ¬ CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D)
  prime : p.Prime
  five_le : 5 ≤ p
  core_ne_bot : CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) ≠ ⊥
  eq_residual : X = nqPrimeResidualX D p

end CFSG.Quasithin.H13
