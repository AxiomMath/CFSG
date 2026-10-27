
module

public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.Background.A3StructureFacts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

abbrev PStar (p : ℕ) (H : Type) [Group H] : Type := H ⧸ CFSG.pPrimeCore p H

abbrev starImage (p : ℕ) {H : Type} [Group H] (L : Subgroup H) : Subgroup (PStar p H) :=
  L.map (QuotientGroup.mk' (CFSG.pPrimeCore p H))

@[expose] def A318Case3Group (X : Type) [Group X] : Prop :=
  (∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧ IsSLEps3 s q X) ∨
    IsHat X (alternatingGroup (Fin 6)) ∨ IsHat X (alternatingGroup (Fin 7)) ∨
    IsHat X (CFSG.Blueprint.NativeSporadic.Carrier .M22)

@[expose] def A318Case2 {G : Type} [Group G] (S : Subgroup G) : Prop :=
  ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧ IsPSLEps3q s q ↥S ∧
    (IsPGLEps3 s q ↥(oPrimeResidualOf 3 (⊤ : Subgroup G)) ∨
      ∃ m : ℕ, q = 2 ^ (3 * m) ∧ IsL3CircAbstract s q ↥(oPrimeResidualOf 3 (⊤ : Subgroup G)))

@[expose] def IsPGLModCenter (s : Bool) (q : ℕ) {G : Type} [Group G] (S X : Subgroup G) : Prop :=
  ∃ (_ : (((Subgroup.center ↥S).map S.subtype).subgroupOf X).Normal),
    IsPGLEps3 s q (↥X ⧸ ((Subgroup.center ↥S).map S.subtype).subgroupOf X)

@[expose] def A318Case3b {G : Type} [Group G] (S : Subgroup G) : Prop :=
  ∃ (s : Bool) (q : ℕ) (x : G), IsSLEps3 s q ↥S ∧ orderOf x = 3 ∧ x ∉ S ∧
    oPrimeResidualOf 3 (⊤ : Subgroup G) = S ⊔ Subgroup.zpowers x ∧
    IsPGLModCenter s q S (S ⊔ Subgroup.zpowers x) ∧
    IsCyclic ↥(S ⊓ Subgroup.centralizer ({x} : Set G)) ∧
    Nat.card ↥(S ⊓ Subgroup.centralizer ({x} : Set G)) =
      (if s then q ^ 2 + q + 1 else q ^ 2 - q + 1) ∧
    ∀ Y : Subgroup G, Nat.card Y = 3 → ¬ Y ≤ S →
      ∃ l ∈ S, Y = (Subgroup.zpowers x).map (MulAut.conj l).toMonoidHom

@[expose] def A318Conclusion {H : Type} [Group H] [Finite H] (p : ℕ) (L : Subgroup H) : Prop :=
  L = oPrimeResidualOf p ⊤ ∨
    (p = 3 ∧ A318Case2 (starImage p L)) ∨
    (p = 3 ∧ A318Case3Group ↥(starImage p L) ∧
      (L = thetaOf (⊤ : Subgroup H) ∨ A318Case3b (starImage p L)))

@[expose] def A318AutFact : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X) [S.Normal],
    (∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1) → IsSimpleGroup ↥S → A23List ↥S →
    1 < CFSG.Open.pRank p S → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 →
    oPrimeResidualOf p ⊤ = S ∨ (p = 3 ∧ A318Case2 S)

@[expose] def A318CenterFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], A36Case2List X → Nat.card (Subgroup.center X) = 3 →
    A318Case3Group X

@[expose] def A318CentralFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X) [S.Normal], CFSG.IsQuasisimple ↥S →
    Nat.card (Subgroup.center ↥S) = 3 → A36Case2List ↥S → CFSG.pPrimeCore 3 X = ⊥ →
    2 ≤ CFSG.Open.pRank 3 S → CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 →
    ∀ x : X, orderOf x = 3 → x ∉ S → A318Case3b S

structure A318Facts : Prop where
  aut : A318AutFact
  center : A318CenterFact
  central : A318CentralFact
  list : A23SQTKListFact

end CFSG.Quasithin
