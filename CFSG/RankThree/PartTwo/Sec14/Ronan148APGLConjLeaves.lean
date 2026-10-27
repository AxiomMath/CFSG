module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148MInd

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KFact148L3Cent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (D E : Subgroup X) (p f : ℕ) [Fact p.Prime], 1 ≤ f →
    Sec4.IsoLThreePi ↥D p f → E ≤ Subgroup.normalizer (D : Set X) → IsMulCommutative ↥E →
    (∀ x ∈ E, x ^ 3 = 1) → Nat.card E = 27 →
    (∃ a ∈ E, a ≠ 1 ∧ a ∈ Subgroup.centralizer (D : Set X)) →
    ∀ e ∈ E ⊓ D, e ≠ 1 → E ⊓ D ≤ Subgroup.zpowers e →
    (∀ w ∈ Subgroup.centralizer (E : Set X), w ^ 3 = 1 → w ∈ E) →
    (∀ V : Subgroup X, V ≤ D → ¬ 3 ∣ Nat.card V → E ≤ Subgroup.normalizer (V : Set X) →
      ⁅V, E⁆ = ⊥) →
    p = 2 ∧ p ^ f % 3 = 2 ∧ ¬ 9 ∣ p ^ f + 1

@[expose] def KF148L3TwoLocal : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (D : Subgroup X) (p f : ℕ) [Fact p.Prime], 1 ≤ f →
    Sec4.IsoLThreePi ↥D p f → (p ≠ 2 ∨ 9 ∣ p ^ f - 1) →
    ∃ T E : Subgroup X, T ≤ D ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ D ∧
      E ≤ Subgroup.normalizer (T : Set X) ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9


@[expose] def Step148PGLConjOmega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Eq A Y K J) →
        (∃ (p f : ℕ), 1 ≤ f ∧
          (letI := ker148_normal hY.2; IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f)) →
        Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
        letI := ker148_normal hY.2
        img148 A Y (deltaZero A (lB A) (Ronan148M.centPre148 A Y J)) = ⊥ →
        ∀ (y : G) (hy : y ∈ Y),
          let D := (img148 A Y J).map (MulAut.conj (QuotientGroup.mk' (ker148 A Y)
            (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)))).toMonoidHom
          D ≠ img148 A Y J →
          D ≤ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
          img148 A Y A ≤ Subgroup.normalizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
          alpha148 A Y e he ∈ D →
          (∀ V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), V ≤ D →
            V ≤ Subgroup.centralizer {alpha148 A Y e he} → ¬ 3 ∣ Nat.card V →
            img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
            ⁅V, img148 A Y A⁆ = ⊥) →
          (∃ V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), V ≤ D ∧ ¬ 3 ∣ Nat.card V ∧
            img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ∧
            ⁅V, img148 A Y A⁆ ≠ ⊥) →
          ∀ (a₀ : G) (ha₀ : a₀ ∈ A), a₀ ≠ 1 → alpha148 A Y a₀ ha₀ ∈ img148 A Y J →
            Subgroup.zpowers a₀ ∈ omegaA A

@[expose] def Step148PGLConjOmega2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Eq A Y K J) →
        ∀ f : ℕ, 1 ≤ f → ¬ 9 ∣ 2 ^ f - 1 →
        (letI := ker148_normal hY.2; IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) 2 f) →
        Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
        letI := ker148_normal hY.2
        img148 A Y (deltaZero A (lB A) (Ronan148M.centPre148 A Y J)) = ⊥ →
        ∀ (y : G) (hy : y ∈ Y),
          let D := (img148 A Y J).map (MulAut.conj (QuotientGroup.mk' (ker148 A Y)
            (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)))).toMonoidHom
          D ≠ img148 A Y J →
          D ≤ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
          img148 A Y A ≤ Subgroup.normalizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
          alpha148 A Y e he ∈ D →
          (∀ V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), V ≤ D →
            V ≤ Subgroup.centralizer {alpha148 A Y e he} → ¬ 3 ∣ Nat.card V →
            img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
            ⁅V, img148 A Y A⁆ = ⊥) →
          (∃ V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), V ≤ D ∧ ¬ 3 ∣ Nat.card V ∧
            img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ∧
            ⁅V, img148 A Y A⁆ ≠ ⊥) →
          ∀ (a₀ : G) (ha₀ : a₀ ∈ A), a₀ ≠ 1 → alpha148 A Y a₀ ha₀ ∈ img148 A Y J →
            Subgroup.zpowers a₀ ∈ omegaA A

@[expose] def Step148PGLConjU3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Eq A Y K J) →
        ∀ f : ℕ, 1 ≤ f → 2 ^ f % 3 = 2 → ¬ 9 ∣ 2 ^ f + 1 →
        (letI := ker148_normal hY.2; IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) 2 f) →
        Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
        letI := ker148_normal hY.2
        img148 A Y (deltaZero A (lB A) (Ronan148M.centPre148 A Y J)) = ⊥ →
        ∀ (y : G) (hy : y ∈ Y),
          let D := (img148 A Y J).map (MulAut.conj (QuotientGroup.mk' (ker148 A Y)
            (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)))).toMonoidHom
          D ≠ img148 A Y J →
          D ≤ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
          img148 A Y A ≤ Subgroup.normalizer (D : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
          alpha148 A Y e he ∈ D →
          (∀ V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), V ≤ D → ¬ 3 ∣ Nat.card V →
            img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
            ⁅V, img148 A Y A⁆ = ⊥) →
          False

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
