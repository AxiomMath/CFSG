module

public import CFSG.RankThree.GF2n.Stroth80.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

@[expose] def QuotSat (S N : Subgroup G) (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∃ _ : (N.subgroupOf S).Normal, P (↥S ⧸ N.subgroupOf S)

@[expose] def IsSLModel (n q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧ Nonempty (X ≃* ↥(StatedSL n K))

@[expose] def IsPSLModel (n q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
    Nonempty (X ≃* StatedProj (StatedSL n K))

@[expose] def IsPSUModel (n q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ 2 ∧
    Nonempty (X ≃* StatedProj (StatedSU n q K))

@[expose] def IsOmegaPlus (m q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
    Nonempty (X ≃* ↥(StatedOmega (StatedQuadPlus m K)))

@[expose] def IsOmegaMinus (m q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧ ∃ b c : K,
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (X ≃* ↥(StatedOmega (StatedQuadMinus m K b c)))

@[expose] def IsProdOf (P₁ P₂ : ∀ (X : Type) [Group X], Prop) (X : Type) [Group X] : Prop :=
  ∃ (A B : Type) (_ : Group A) (_ : Group B), P₁ A ∧ P₂ B ∧ Nonempty (X ≃* A × B)

@[expose] def bar (H Q S : Subgroup G) [(Q.subgroupOf H).Normal] :
    Subgroup (↥H ⧸ Q.subgroupOf H) :=
  (S.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H))

@[expose] def SubConfig (M Q Z N : Subgroup G) : Prop :=
  ∃ hN : (Q.subgroupOf (H0 M Z)).Normal,
    haveI := hN
    StrothHyp (G := ↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z))
      (Subgroup.normalizer ((cen (bar (H0 M Z) Q N) : Subgroup _) : Set _))
      (bar (H0 M Z) Q N) (cen (bar (H0 M Z) Q N))

@[expose] def SectionAct {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
    (S V Z : Subgroup G) (φ : S →* GL ι K) (act : GL ι K → Matrix ι ι K) : Prop :=
  S ≤ Subgroup.normalizer (V : Set G) ∧
  ∃ _ : (Z.subgroupOf V).Normal, ∃ ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K),
    ∀ (s : S) (v w : V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        act (φ s) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v))

@[expose] def FrobClause (M Z : Subgroup G) : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
    ∃ e : ↥Z ≃* Multiplicative K, ∀ m ∈ M, ∃ (a : Kˣ) (σ : K ≃+* K), ∀ z w : Z,
      (w : G) = m * z * m⁻¹ →
        Multiplicative.toAdd (e w) = (a : K) * σ (Multiplicative.toAdd (e z))) ∧
  (Nat.card Z - 1) ∣ (H0 M Z).relIndex M

@[expose] def CentDvd (M Q Z S : Subgroup G) : Prop :=
  ∃ C : Subgroup G, Q ≤ C ∧ C ≤ H0 M Z ∧ (∀ h, h ∈ C ↔ h ∈ H0 M Z ∧ ∀ x ∈ S, ⁅h, x⁆ ∈ Q) ∧
    Nat.card C ∣ Nat.card Q * (Nat.card Z - 1)

@[expose] def CaseVI (M Q Z S : Subgroup G) : Prop :=
  ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
    ∃ φ : S →* GL (Fin n) K, φ.range = StatedSL n K ∧ φ.ker = Q.subgroupOf S ∧
      ∃ V₁ V₂ : Subgroup G, Z ≤ V₁ ∧ V₁ ≤ Q ∧ Z ≤ V₂ ∧ V₂ ≤ Q ∧ V₁ ⊓ V₂ = Z ∧ V₁ ⊔ V₂ = Q ∧
        SectionAct (ι := Fin n) K S V₁ Z φ (fun g => (g : Matrix (Fin n) (Fin n) K)) ∧
        SectionAct (ι := Fin n) K S V₂ Z φ
          (fun g => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ) ∧
        (∃ x ∈ M, conjSubgroup x V₁ = V₂) ∧ CentDvd M Q Z S

@[expose] def IsA2 (Q Z : Subgroup G) (a : G) : Prop :=
  a ∈ Subgroup.normalizer (Q : Set G) ∧ a ∉ Q ∧ a ^ 2 ∈ Q ∧
    Nat.card ↥(⁅Q, Subgroup.zpowers a⁆ ⊔ Z) = Nat.card Z ^ 3 ∧
    Assembly.IsElemAbelian 2 ⁅Q, Subgroup.zpowers a⁆

@[expose] def NoA2 (Q Z L : Subgroup G) : Prop := ∀ a ∈ L, ¬ IsA2 Q Z a

@[expose] def NoA2All (M Q Z : Subgroup G) : Prop :=
  ∀ B' : Subgroup G, (∃ g : G, B' = conjSubgroup g Z) → B' ≤ Q → B' ≠ Z → NoA2 Q Z (LB M Q B')

@[expose] def StrothConclusion (M Q Z B : Subgroup G) : Prop :=
  let q := Nat.card Z
  let L := LB M Q B
  let S := Lgen M L
  ((∃ n : ℕ, q = 2 ^ n ∧ Tim79.IsL3Type n Q) ∨
    (Nat.card Q = q ^ 5 ∧ QuotSat S Q (IsSLModel 2 q)) ∨
    (Nat.card Q = q ^ 9 ∧ QuotSat S Q (IsSLModel 2 (q ^ 3)) ∧ CentTrivial M Q Z S) ∨
    (¬ IsTIMod M Q L ∧
      ((NoA2All M Q Z ∧ ∃ t ∈ L, t ∉ Q ∧ CentTrivial M Q Z S ∧
        ((Nat.card Q = q ^ 9 ∧ Nat.card (Nt M L t) = Nat.card Q * q ∧
            (QuotSat (Rt M L t) (Nt M L t) (IsOmegaPlus 2 q) ∨
              QuotSat (Rt M L t) (Nt M L t) (IsOmegaMinus 2 q))) ∨
          (∃ m : ℕ, 2 ≤ m ∧ Nat.card Q = q ^ (4 * m + 1) ∧
            Nat.card (Nt M L t) = Nat.card Q * q ∧
            ((QuotSat (Rt M L t) (Nt M L t) (IsOmegaPlus m q) ∧
                QuotSat S Q (IsProdOf (IsSLModel 2 q) (IsOmegaPlus m q))) ∨
              (QuotSat (Rt M L t) (Nt M L t) (IsOmegaMinus m q) ∧
                QuotSat S Q (IsProdOf (IsSLModel 2 q) (IsOmegaMinus m q))))) ∨
          (Nat.card Q = q ^ 21 ∧
            (∃ hN : (Q.subgroupOf M).Normal, haveI := hN
              layer (↥M ⧸ Q.subgroupOf M) =
                (S.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M))) ∧
            (QuotSat S Q (IsPSUModel 6 q) ∨ QuotSat S Q (IsPSLModel 6 q))) ∨
          (Nat.card Q = q ^ 33 ∧ Nat.card (Nt M L t) = Nat.card Q * q ^ 17 ∧
            QuotSat (Rt M L t) (Nt M L t) (IsOmegaPlus 4 q) ∧ SubConfig M Q Z (Nt M L t)) ∨
          (Nat.card Q = q ^ 57 ∧ Nat.card (Nt M L t) = Nat.card Q * q ^ 33 ∧
            QuotSat (Rt M L t) (Nt M L t) (IsOmegaPlus 6 q) ∧ SubConfig M Q Z (Nt M L t)))) ∨
      CaseVI M Q Z S))) ∧
  FrobClause M Z

@[expose] def Stroth1980Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z : Subgroup G), StrothHyp M Q Z →
    ∀ B : Subgroup G, (∃ g : G, B = conjSubgroup g Z) → B ≤ Q → B ≠ Z →
      StrothConclusion M Q Z B

end CFSG.RankThree.GF2n.Stroth80
