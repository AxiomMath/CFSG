module

public import CFSG.RankThree.GF2n.Stroth80.Conclusion

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

@[expose] def OuterOnFStar (G : Type) [Group G] : Prop :=
  ∃ g : G, ∀ h ∈ generalizedFitting G, ∃ x ∈ generalizedFitting G, g * x * g⁻¹ ≠ h * x * h⁻¹

section Cases

variable (M Q Z B : Subgroup G)

@[expose] def CaseD1 (n : ℕ) : Prop := Nat.card Z = 2 ^ n ∧ Tim79.IsL3Type n Q

@[expose] def CaseD2 : Prop :=
  Nat.card Q = Nat.card Z ^ 5 ∧ QuotSat (Lgen M (LB M Q B)) Q (IsSLModel 2 (Nat.card Z))

@[expose] def CaseD3 : Prop :=
  Nat.card Q = Nat.card Z ^ 9 ∧
    QuotSat (Lgen M (LB M Q B)) Q (IsSLModel 2 (Nat.card Z ^ 3)) ∧
    CentTrivial M Q Z (Lgen M (LB M Q B))

@[expose] def CtxD4 (t : G) : Prop :=
  ¬ IsTIMod M Q (LB M Q B) ∧ t ∈ LB M Q B ∧ t ∉ Q ∧
    CentTrivial M Q Z (Lgen M (LB M Q B))

@[expose] def CaseE1 (t : G) : Prop :=
  Nat.card Q = Nat.card Z ^ 9 ∧ Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z ∧
    (QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaPlus 2 (Nat.card Z)) ∨
      QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaMinus 2 (Nat.card Z)))

@[expose] def CaseE1Plus (t : G) : Prop :=
  Nat.card Q = Nat.card Z ^ 9 ∧ Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z ∧
    QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaPlus 2 (Nat.card Z))

@[expose] def CaseE1Minus (t : G) : Prop :=
  Nat.card Q = Nat.card Z ^ 9 ∧ Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z ∧
    QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaMinus 2 (Nat.card Z))

@[expose] def CaseE2 (t : G) (m : ℕ) : Prop :=
  2 ≤ m ∧ Nat.card Q = Nat.card Z ^ (4 * m + 1) ∧
    Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z ∧
    ((QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaPlus m (Nat.card Z)) ∧
        QuotSat (Lgen M (LB M Q B)) Q
          (IsProdOf (IsSLModel 2 (Nat.card Z)) (IsOmegaPlus m (Nat.card Z)))) ∨
      (QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaMinus m (Nat.card Z)) ∧
        QuotSat (Lgen M (LB M Q B)) Q
          (IsProdOf (IsSLModel 2 (Nat.card Z)) (IsOmegaMinus m (Nat.card Z)))))

@[expose] def CaseE2Plus (t : G) (m : ℕ) : Prop :=
  2 ≤ m ∧ Nat.card Q = Nat.card Z ^ (4 * m + 1) ∧
    Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z ∧
    QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaPlus m (Nat.card Z)) ∧
      QuotSat (Lgen M (LB M Q B)) Q
        (IsProdOf (IsSLModel 2 (Nat.card Z)) (IsOmegaPlus m (Nat.card Z)))

@[expose] def CaseE2Minus (t : G) (m : ℕ) : Prop :=
  2 ≤ m ∧ Nat.card Q = Nat.card Z ^ (4 * m + 1) ∧
    Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z ∧
    QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaMinus m (Nat.card Z)) ∧
      QuotSat (Lgen M (LB M Q B)) Q
        (IsProdOf (IsSLModel 2 (Nat.card Z)) (IsOmegaMinus m (Nat.card Z)))

@[expose] def CaseE3 : Prop :=
  Nat.card Q = Nat.card Z ^ 21 ∧
    (∃ hN : (Q.subgroupOf M).Normal, haveI := hN
      layer (↥M ⧸ Q.subgroupOf M) =
        ((Lgen M (LB M Q B)).subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M))) ∧
    (QuotSat (Lgen M (LB M Q B)) Q (IsPSUModel 6 (Nat.card Z)) ∨
      QuotSat (Lgen M (LB M Q B)) Q (IsPSLModel 6 (Nat.card Z)))

@[expose] def CaseE3U : Prop :=
  Nat.card Q = Nat.card Z ^ 21 ∧
    (∃ hN : (Q.subgroupOf M).Normal, haveI := hN
      layer (↥M ⧸ Q.subgroupOf M) =
        ((Lgen M (LB M Q B)).subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M))) ∧
    QuotSat (Lgen M (LB M Q B)) Q (IsPSUModel 6 (Nat.card Z))

@[expose] def CaseE3L : Prop :=
  Nat.card Q = Nat.card Z ^ 21 ∧
    (∃ hN : (Q.subgroupOf M).Normal, haveI := hN
      layer (↥M ⧸ Q.subgroupOf M) =
        ((Lgen M (LB M Q B)).subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M))) ∧
    QuotSat (Lgen M (LB M Q B)) Q (IsPSLModel 6 (Nat.card Z))

@[expose] def CaseE4 (t : G) : Prop :=
  Nat.card Q = Nat.card Z ^ 33 ∧
    Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z ^ 17 ∧
    QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaPlus 4 (Nat.card Z)) ∧
    SubConfig M Q Z (Nt M (LB M Q B) t)

@[expose] def CaseE5 (t : G) : Prop :=
  Nat.card Q = Nat.card Z ^ 57 ∧
    Nat.card (Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z ^ 33 ∧
    QuotSat (Rt M (LB M Q B) t) (Nt M (LB M Q B) t) (IsOmegaPlus 6 (Nat.card Z)) ∧
    SubConfig M Q Z (Nt M (LB M Q B) t)

@[expose] def CaseE6 (n : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
    ∃ φ : (Lgen M (LB M Q B)) →* GL (Fin n) K, φ.range = StatedSL n K ∧
      φ.ker = Q.subgroupOf (Lgen M (LB M Q B)) ∧
      ∃ V₁ V₂ : Subgroup G, Z ≤ V₁ ∧ V₁ ≤ Q ∧ Z ≤ V₂ ∧ V₂ ≤ Q ∧ V₁ ⊓ V₂ = Z ∧ V₁ ⊔ V₂ = Q ∧
        SectionAct (ι := Fin n) K (Lgen M (LB M Q B)) V₁ Z φ
          (fun g => (g : Matrix (Fin n) (Fin n) K)) ∧
        SectionAct (ι := Fin n) K (Lgen M (LB M Q B)) V₂ Z φ
          (fun g => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ) ∧
        (∃ x ∈ M, conjSubgroup x V₁ = V₂) ∧ CentDvd M Q Z (Lgen M (LB M Q B))

theorem strothConclusion_iff_cases :
    StrothConclusion M Q Z B ↔
      (((∃ n : ℕ, CaseD1 Q Z n) ∨ CaseD2 M Q Z B ∨ CaseD3 M Q Z B ∨
        (¬ IsTIMod M Q (LB M Q B) ∧
          ((NoA2All M Q Z ∧ ∃ t ∈ LB M Q B, t ∉ Q ∧ CentTrivial M Q Z (Lgen M (LB M Q B)) ∧
            (CaseE1 M Q Z B t ∨ (∃ m : ℕ, CaseE2 M Q Z B t m) ∨ CaseE3 M Q Z B ∨
              CaseE4 M Q Z B t ∨ CaseE5 M Q Z B t)) ∨
          ∃ n : ℕ, CaseE6 M Q Z B n))) ∧ FrobClause M Z) :=
  Iff.rfl

theorem caseE1_iff (t : G) :
    CaseE1 M Q Z B t ↔ CaseE1Plus M Q Z B t ∨ CaseE1Minus M Q Z B t := by
  unfold CaseE1 CaseE1Plus CaseE1Minus
  constructor
  · rintro ⟨h1, h2, h3 | h3⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2, h3⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨h1, h2, Or.inl h3⟩
    · exact ⟨h1, h2, Or.inr h3⟩

theorem caseE2_iff (t : G) (m : ℕ) :
    CaseE2 M Q Z B t m ↔ CaseE2Plus M Q Z B t m ∨ CaseE2Minus M Q Z B t m := by
  unfold CaseE2 CaseE2Plus CaseE2Minus
  constructor
  · rintro ⟨h0, h1, h2, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩
    · exact Or.inl ⟨h0, h1, h2, h3, h4⟩
    · exact Or.inr ⟨h0, h1, h2, h3, h4⟩
  · rintro (⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩)
    · exact ⟨h0, h1, h2, Or.inl ⟨h3, h4⟩⟩
    · exact ⟨h0, h1, h2, Or.inr ⟨h3, h4⟩⟩

theorem caseE3_iff : CaseE3 M Q Z B ↔ CaseE3U M Q Z B ∨ CaseE3L M Q Z B := by
  unfold CaseE3 CaseE3U CaseE3L
  constructor
  · rintro ⟨h1, h2, h3 | h3⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2, h3⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨h1, h2, Or.inl h3⟩
    · exact ⟨h1, h2, Or.inr h3⟩

end Cases

abbrev FStar (G : Type) [Group G] : Type := ↥(generalizedFitting G)

section Conclusion

variable (M Q Z B : Subgroup G)

@[expose] def SmithConclusion : Prop :=
  (∀ n : ℕ, CaseD1 Q Z n →
    CFSG.Blueprint.LieModel (FStar G) .PSL 3 2 n ∧ OuterOnFStar G) ∧
  (CaseD2 M Q Z B →
    (NoA2 Q Z (LB M Q B) → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
      CFSG.Blueprint.LieModel (FStar G) .G2 0 2 f) ∧
    (¬ NoA2 Q Z (LB M Q B) → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
      CFSG.Blueprint.LieModel (FStar G) .PSL 4 2 f ∧ OuterOnFStar G)) ∧
  (CaseD3 M Q Z B → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .trialityD4 0 2 f) ∧
  (∀ t : G, CtxD4 M Q Z B t → CaseE1Plus M Q Z B t → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .POmegaPlus 4 2 f) ∧
  (∀ t : G, CtxD4 M Q Z B t → CaseE1Minus M Q Z B t → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .POmegaMinus 4 2 f) ∧
  (∀ (t : G) (m : ℕ), CtxD4 M Q Z B t → CaseE2Plus M Q Z B t m → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .POmegaPlus (m + 2) 2 f) ∧
  (∀ (t : G) (m : ℕ), CtxD4 M Q Z B t → CaseE2Minus M Q Z B t m → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .POmegaMinus (m + 2) 2 f) ∧
  (∀ t : G, CtxD4 M Q Z B t → CaseE3U M Q Z B → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .twistedE6 0 2 f) ∧
  (∀ t : G, CtxD4 M Q Z B t → CaseE3L M Q Z B → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .E6 0 2 f) ∧
  (∀ t : G, CtxD4 M Q Z B t → CaseE4 M Q Z B t → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .E7 0 2 f) ∧
  (∀ t : G, CtxD4 M Q Z B t → CaseE5 M Q Z B t → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .E8 0 2 f) ∧
  (¬ IsTIMod M Q (LB M Q B) → ∀ n : ℕ, CaseE6 M Q Z B n → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
    CFSG.Blueprint.LieModel (FStar G) .PSL (n + 2) 2 f ∧ OuterOnFStar G)

end Conclusion

@[expose] def Smith1981Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z : Subgroup G), StrothHyp M Q Z →
    ∀ B : Subgroup G, (∃ g : G, B = conjSubgroup g Z) → B ≤ Q → B ≠ Z →
      StrothConclusion M Q Z B → SmithConclusion M Q Z B

end CFSG.RankThree.GF2n.Smith81
