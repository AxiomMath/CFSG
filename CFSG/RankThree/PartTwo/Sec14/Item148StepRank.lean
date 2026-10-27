module

public import CFSG.RankThree.PartTwo.Sec14.Item148Steps

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KF148FieldTypes : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → Group.IsPerfect X →
    Sec4.IsoLThreePi X 2 n →
    IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧
      (∀ _ : Fact (Nat.Prime 7),
        IsEmpty (X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∧
      ∀ (p f : ℕ) [Fact p.Prime], 1 ≤ f → IsLThreeEpsAt X p f → p = 2 ∧ f = n

section Steps

@[expose] def Step148RankImg : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2;
          Lift148Eq A Y K J ∨ Lift148Ten A Y K J ∨ Lift148Field A Y e he K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) →
        letI := ker148_normal hY.2
        img148 A Y (deltaZero A (lB A) Y) = img148 A Y J

@[expose] def Step148RankTen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (_he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Ten A Y K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) →
        (letI := ker148_normal hY.2; img148 A Y (deltaZero A (lB A) Y) = img148 A Y J) →
        (∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
          Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7))) ∧
        (Nonempty (wStar A ≃* Equiv.Perm (Fin 4)) ∨
          Nonempty (wStar A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))

@[expose] def Step148RankFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Field A Y e he K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) →
        (letI := ker148_normal hY.2; img148 A Y (deltaZero A (lB A) Y) = img148 A Y J) →
        inSubgroup perfectResidual
            (oPrimeResidualOf 3 (deltaZero A (lB A) Y ⊓ Subgroup.centralizer ({e} : Set G))) =
          deltaZero A (lB A) (inSubgroup perfectResidual
            (oPrimeResidualOf 3 (deltaZero A (lB A) Y ⊓ Subgroup.centralizer ({e} : Set G))))

end Steps

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isoLThreePi_of_mulEquiv148 {X X' : Type} [Group X] [Group X'] (φ : X ≃* X') {p e : ℕ}
    [Fact p.Prime] (h : Sec4.IsoLThreePi X' p e) : Sec4.IsoLThreePi X p e := by
  rcases h with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
  · exact Or.inl ⟨hq, ⟨φ.trans ψ⟩⟩
  · exact Or.inr ⟨hq, ⟨φ.trans ψ⟩⟩

end CFSG.RankThree.PartTwo.Sec14
