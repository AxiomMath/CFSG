module

public import CFSG.RankThree.PartTwo.Sec4.Notation
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp localRank)

abbrev Spor (n : TauCeti.SporadicName) : Type :=
  (TauCeti.CFSGIndex.sporadic n).Group

@[expose] def g2ThreeIndex : TauCeti.ValidLieTypeIndex :=
  ⟨.G2 ⟨3, 1, Nat.prime_three, Nat.one_pos⟩, by simp⟩

@[expose] def IsoGTwoPrime (X : Type) [Group X] : Prop :=
  (∃ p f : ℕ, Blueprint.ChevalleyExceptionalModel X .G2 p f) ∨ Nonempty (X ≃* projSU 3 3 1)

@[expose] def IsoLThreePi (X : Type) [Group X] (p e : ℕ) [Fact p.Prime] : Prop :=
  (p ^ e % 3 = 1 ∧ Nonempty (X ≃* projSL 3 (GaloisField p e))) ∨
    (p ^ e % 3 = 2 ∧ Nonempty (X ≃* projSU 3 p e))

@[expose] def Item4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G →
    ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal], layer (H ⧸ N) = ⊤ →
      ((∀ p : ℕ, p.Prime → 3 < p → localRank p (H ⧸ N) < 3) ∧
        (IsQuasisimple (H ⧸ N) → localRank 3 (H ⧸ N) ≤ 3)) ∧
      (∀ p : ℕ, p.Prime → CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 3 →
        (3 < p →
          CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ N)) ≤ CFSG.Open.pRank p (⊤ : Subgroup G)) ∧
        (p = 3 → IsQuasisimple (H ⧸ N) →
          CFSG.Open.pRank 3 (⊤ : Subgroup (H ⧸ N)) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) ∨
          (Nonempty ((H ⧸ N) ≃* Blueprint.NativeSporadic.ON) ∧
            ∃ (H' : Subgroup G) (N' : Subgroup H') (_ : N'.Normal),
              IsQuasisimple (H' ⧸ N') ∧
              IsExtOf (H' ⧸ N') Blueprint.NativeSporadic.ON (Multiplicative (ZMod 3)) ∧
              ∃ f : H' ⧸ N' →* H ⧸ N, Function.Surjective f)))

@[expose] def Item4_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → IsQuasisimple G →
    3 ∣ Nat.card (Subgroup.center G) →
      (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ IsoLThreePi (G ⧸ Subgroup.center G) p e) ∨
      Nonempty (G ⧸ Subgroup.center G ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (G ⧸ Subgroup.center G ≃* alternatingGroup (Fin 7)) ∨
      Blueprint.ChevalleyExceptionalModel (G ⧸ Subgroup.center G) .G2 3 1 ∨
      Nonempty (G ⧸ Subgroup.center G ≃* projSU 4 3 1) ∨
      Nonempty (G ⧸ Subgroup.center G ≃* Blueprint.NativeSporadic.M22) ∨
      Nonempty (G ⧸ Subgroup.center G ≃* Blueprint.NativeSporadic.J3) ∨
      Nonempty (G ⧸ Subgroup.center G ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (G ⧸ Subgroup.center G ≃* Blueprint.NativeSporadic.ON)

@[expose] def Item4_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G, IsPGroup 3 A →
    (CFSG.pCore 3 G ≠ ⊥ ∨
      (CFSG.Assembly.IsElemAbelian 3 A ∧ ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n)) →
    ∀ L ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (L : Set G)

@[expose] def Item4_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G,
    CFSG.Assembly.IsElemAbelian 3 A → (∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n) →
    ∀ x ∈ A, x ≠ 1 → ∀ Y ∈ thetaComponentsAt 3 x, ∃ L ∈ thetaComponents 3 G, Y ≤ L

@[expose] def Item4_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → 3 ∣ Nat.card (Subgroup.center G) →
    ∀ L ∈ thetaComponents 3 G, ∀ X : Subgroup G, IsPGroup 3 X →
      (∀ K ∈ thetaComponents 3 G, X ≤ Subgroup.normalizer (K : Set G)) →
      ∀ U ∈ invariantPiSubgroups ⊤ X (piOf 2), ⁅X, U⁆ = U → U ≤ L ⊔ thetaQuotCentralizer L

@[expose] def Item4_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → Group.IsPerfect G →
    CFSG.pPrimeCore 3 G = CFSG.oddCore G →
    Nonempty (G ⧸ CFSG.pPrimeCore 3 G ≃* projSL 2 (GaloisField 3 3)) → IsSimpleGroup G

@[expose] def Item4_22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G,
    Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
    ∀ c : G, c ∈ A → ∀ hc : c ∈ Subgroup.center G, c ≠ 1 →
      (haveI : (Subgroup.zpowers c).Normal :=
          Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hc);
        thetaAlpha 3 (A.map (QuotientGroup.mk' (Subgroup.zpowers c))) ≤
          aschbacherSolvableCore 3 (G ⧸ Subgroup.zpowers c)) ∨
      ∃ L ∈ thetaComponents 3 G, Nat.card (autThetaQuot A L) = 9 ∧
        thetaAlpha 3 ((autThetaQuot A L).subgroupOf (autThetaQuot ⊤ L)) ≠ ⊥

@[expose] def Item4_27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G, Late.IsE27 A →
    partTwoE G = partTwoF G → aschbacherSolvableCore 3 G = ⊥ → ∀ L : Subgroup G, IsComponent L →
    ∀ d ∈ A, d ≠ 1 →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
    ∀ K : Subgroup (L ⊓ Subgroup.centralizer {d} : Subgroup G), IsComponent K →
      (Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 5)) ∨
        (d ∈ K.map (L ⊓ Subgroup.centralizer {d}).subtype ∧
          IsExtOf (K ⧸ CFSG.pCore 2 K) Blueprint.NativeSporadic.ON (Multiplicative (ZMod 3)))) →
      K.map (L ⊓ Subgroup.centralizer {d}).subtype = L

@[expose] def Item4_31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G →
    CFSG.Open.pRank 3 (⊤ : Subgroup G) = 3 → aschbacherSolvableCore 3 G = ⊥ →
    ∀ A : Subgroup G, Late.IsE27 A → ∀ c ∈ A, c ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    ∀ K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G), IsComponent K →
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 6)) →
      Nonempty (L ≃* alternatingGroup (Fin 6)) ∨ Nonempty (L ≃* Blueprint.NativeSporadic.J3) ∨
        Nonempty (L ≃* projSp 3 (GaloisField 2 1)) ∨ Nonempty (L ≃* alternatingGroup (Fin 9)) ∨
        Nonempty (L ≃* projSp 2 (GaloisField 2 3))

@[expose] def Item4_32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → CFSG.pPrimeCore 3 G = ⊥ →
    ∀ Z : Subgroup G, Nat.card Z = 3 →
    (∀ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set G) →
      Z.map (MulAut.conj g).toMonoidHom = Z) →
      CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set G)) = 1 ∨
        IsoGTwoPrime (Subgroup.normalClosure (Z : Set G)) ∨
        Nonempty (Subgroup.normalClosure (Z : Set G) ≃* Blueprint.NativeSporadic.J2)

@[expose] def Item4_39 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M Q : Subgroup G), Ctx434 G A M Q →
    A ⊓ Subgroup.centralizer (layer G : Set G) ≠ ⊥ →
    ¬ A ⊓ Subgroup.centralizer (layer G : Set G) ≤
      (Subgroup.center (layer G)).map (layer G).subtype →
    CFSG.Open.pRank 3 (⊤ : Subgroup G) = 3 ∧
      ((A ⊔ layer G = (A ⊓ Subgroup.centralizer (layer G : Set G)) ⊔ layer G ∧
          A ⊓ Subgroup.centralizer (layer G : Set G) ⊓ layer G = ⊥) ∨
        ∃ a ∈ A, InducesOuter a (layer G) ∧
          CFSG.Open.pRank 3 (layer G ⊓ Subgroup.centralizer {a}) = 1)

@[expose] def Item4_44_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Ctx444 G A M →
    CFSG.pPrimeCore 3 G ≠ inSubgroup (CFSG.pPrimeCore 3) M →
    ∃ L ∈ oTwoComponents G, ∃ S : Sylow 2 (inSubgroup (CFSG.pPrimeCore 3) M),
      A ⊔ L ⊔ (S : Subgroup _).map (inSubgroup (CFSG.pPrimeCore 3) M).subtype ∈ Late.scriptH₀ A M

@[expose] def Item4_44_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Ctx444 G A M → ∀ H ∈ Late.scriptH₀ A M,
    ∃ L ∈ oTwoComponents G, ¬ L ≤ M ∧
      (L = inSubgroup perfectResidual H ⊔ inSubgroup (CFSG.pCore 2) L ∨
        (Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
            projSL 3 (GaloisField 2 2)) ∧
          ∃ J ∈ oTwoComponents G, ⁅inSubgroup perfectResidual H, ⊤⁆ = L ⊔ J ∧
            Nonempty (L ⧸ CFSG.pCore 2 L ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∧
            ((∃ n : ℕ, 1 ≤ n ∧ Nonempty (J ⧸ CFSG.pCore 2 J ≃*
                Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * n)))) ∨
              IsExtOf (J ⧸ CFSG.pCore 2 J) Blueprint.NativeSporadic.M22
                (Multiplicative (ZMod 3)))))

@[expose] def Item4_45 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Ctx444 G A M →
    ∀ x ∈ Subgroup.centralizer (A : Set G), x ^ 3 = 1 → x ∈ A

@[expose] def Item4_47 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Ctx444 G A M →
    ∀ L ∈ thetaComponents 3 G, ¬ L ≤ M →
      inSubgroup (CFSG.pPrimeCore 3) M ≤ Subgroup.normalizer (L : Set G)

@[expose] def Item4_50 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Ctx444 G A M →
    (CFSG.pPrimeCore 3 G ≠ inSubgroup (CFSG.pPrimeCore 3) M ∨ ⊤ ∈ Late.scriptH₀ A M) →
    ∃ L ∈ thetaComponents 3 G,
      inSubgroup (CFSG.pPrimeCore 3) M ≤ Subgroup.normalizer (L : Set G) ∧
        ⁅L, inSubgroup (CFSG.pPrimeCore 3) M⁆ = L ∧ ¬ L ≤ M

@[expose] def Item4_52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Ctx444 G A M →
    (CFSG.pPrimeCore 3 G ≠ inSubgroup (CFSG.pPrimeCore 3) M ∨ ⊤ ∈ Late.scriptH₀ A M) →
    ∀ L ∈ thetaComponents 3 G,
      inSubgroup (CFSG.pPrimeCore 3) M ≤ Subgroup.normalizer (L : Set G) →
      ⁅L, inSubgroup (CFSG.pPrimeCore 3) M⁆ = L → ¬ L ≤ M → L ∈ oTwoComponents G

@[expose] def Item4_53 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Ctx444 G A M →
    CFSG.pPrimeCore 3 G ≠ inSubgroup (CFSG.pPrimeCore 3) M →
    ∀ L ∈ thetaComponents 3 G,
      inSubgroup (CFSG.pPrimeCore 3) M ≤ Subgroup.normalizer (L : Set G) →
      ⁅L, inSubgroup (CFSG.pPrimeCore 3) M⁆ = L → ¬ L ≤ M →
    ∀ S : Sylow 2 (inSubgroup (CFSG.pPrimeCore 3) M),
      A ≤ Subgroup.normalizer
        (((S : Subgroup _).map (inSubgroup (CFSG.pPrimeCore 3) M).subtype : Subgroup G) : Set G) →
      A ⊔ L ⊔ (S : Subgroup _).map (inSubgroup (CFSG.pPrimeCore 3) M).subtype ∈ Late.scriptH₀ A M

@[expose] def Item4_62 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G, Late.IsE27 A →
    ∀ a ∈ A, a ∈ Subgroup.center G → a ≠ 1 → ∀ B : Subgroup G, B ≤ A → Nat.card B = 9 →
    ∀ U : Subgroup G, IsKleinFour U → ⁅U, A⁆ = U →
      U = inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (B : Set G)) →
    ∀ D : Subgroup G, D ≤ A → B ⊓ D = ⊥ → B ⊔ D = A →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G) →
      CFSG.Open.pRank 3 (Subgroup.centralizer (A : Set G)) = 3 →
      U ≤ aschbacherSolvableCore 3 G ∨
        ∃ L ∈ thetaComponents 3 G, U ≤ L ∧
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 3)) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.J2) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.M12)) ∧
          ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)), B⁆ ≤
            aschbacherSolvableCore 3 G

@[expose] def Item4_63 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G,
    Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
    ∀ a ∈ A, a ∈ Subgroup.center G → a ≠ 1 → Odd (Nat.card (aschbacherSolvableCore 3 G)) →
    ∀ B : Subgroup G, B ≤ A → Nat.card B = 9 →
      Even (Nat.card (⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)),
        A⁆ : Subgroup G)) →
      ∃ L ∈ thetaComponents 3 G,
        haveI : (solvableRadical L).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1;
        Nonempty (L ⧸ solvableRadical L ≃* alternatingGroup (Fin 7)) ∨
          Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.M12) ∨
          Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.J2) ∨
          Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.M22) ∨
          (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
            IsoLThreePi (L ⧸ solvableRadical L) p e) ∨
          Nonempty (L ⧸ solvableRadical L ≃* projSL 2 (GaloisField 3 3))

end CFSG.RankThree.PartTwo.Sec4
