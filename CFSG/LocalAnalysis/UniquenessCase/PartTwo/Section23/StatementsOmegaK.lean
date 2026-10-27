module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwentyThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def zOneOf (T : Subgroup G) : Subgroup G :=
  CFSG.inSubgroup (fun K _ => CFSG.higherElemThompsonOmega K 1) T

@[expose] def KThomp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsSolvable X → ¬ 3 ∣ Nat.card X →
    Subgroup.centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X →
    ∀ P : Sylow 2 X,
      (Set.univ : Set X) =
        (Subgroup.normalizer (F12.jOf (P : Subgroup X) : Set X) : Set X) *
          (Subgroup.normalizer (zOneOf (P : Subgroup X) : Set X) : Set X)

@[expose] def OmegaMinusFrame {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) (n : ℕ)
    (S : Sylow 2 ↥H) (Tstar : Subgroup (MulAut W)) : Prop :=
  2 ≤ n ∧ NatOmegaMinus H ⊤ ⊥ 4 n ∧
    Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) ∧ IsPGroup 2 ↥Tstar ∧
    (S : Subgroup ↥H).map H.subtype ≤ Tstar ∧
    ∀ t ∈ Tstar, ∀ w ∈ CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype), t w = w

@[expose] def KOmA : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ) (S : Sylow 2 ↥H)
    (Tstar : Subgroup (MulAut W)), OmegaMinusFrame H n S Tstar →
    ∀ E : Subgroup (MulAut W), E ≤ Tstar → IsElemAbelian 2 E →
      Nat.card W ≤ Nat.card ↥E * Nat.card ↥(CFSG.Quasithin.fixV E) → E = ⊥

@[expose] def KOmB : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ) (S : Sylow 2 ↥H)
    (Tstar : Subgroup (MulAut W)), OmegaMinusFrame H n S Tstar →
    ∀ E : Subgroup (MulAut W), E ≤ Tstar → IsElemAbelian 2 E → E ≠ ⊥ →
      Nat.card W ≤ 2 * (Nat.card ↥E * Nat.card ↥(CFSG.Quasithin.fixV E)) →
      n = 2 ∧ ¬ Tstar ≤ H ∧
      ∃ A₀ : Subgroup W, Nat.card ↥A₀ = 4 ∧
        (∀ E' : Subgroup (MulAut W), E' ≤ Tstar → IsElemAbelian 2 E' →
          Nat.card W ≤ 2 * (Nat.card ↥E' * Nat.card ↥(CFSG.Quasithin.fixV E')) →
          A₀ ≤ CFSG.Quasithin.fixV E') ∧
        ∃ h ∈ H, A₀.map (h : MulAut W).toMonoidHom = A₀ ∧
          (CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype)).map
              (h : MulAut W).toMonoidHom ≠
            CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype)

@[expose] def KOmC : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ) (S : Sylow 2 ↥H)
    (Tstar : Subgroup (MulAut W)), OmegaMinusFrame H n S Tstar → ¬ Tstar ≤ H →
    ∀ B : Subgroup (MulAut W), B ≤ H → Odd (Nat.card ↥B) →
      (∀ b ∈ B, (CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype)).map
          (b : MulAut W).toMonoidHom =
            CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype)) →
      ∃ t ∈ Tstar, (∀ b ∈ B, t * b * t⁻¹ ∈ B) ∧
        ∀ b ∈ B, (∀ w ∈ CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype),
            b w = w) →
          t * b * t⁻¹ = b⁻¹

@[expose] def Ctx23L.withB {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (B' : Subgroup G) (hB' : B' ∈ calB1 D.T D.M c.L0) (hle' : B' ≤ c.B0) : Ctx23L D Ch :=
  { c with B := B', hB := hB', hle := hle' }

@[expose] def S23_23CaseBFit (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, IsOmegaMinus (Bar2 c.L) 4 (pRank 2 D.Z) →
    ∀ hV : IsElemAbelian 2 c.V, NatOmegaMinus (barSub ⊥ c.V hV c.L) ⊤ ⊥ 4 (pRank 2 D.Z) →
      S23_23OmegaCaseB c → ∀ q : ℕ, q.Prime → 5 ≤ q → IsCyclic ↥(CFSG.pCore q (Bar2 D.M))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
