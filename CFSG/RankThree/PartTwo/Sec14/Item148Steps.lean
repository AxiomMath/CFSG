module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec14.Item14Statements
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Certificates

section Cases

variable (A : Subgroup G) (LB : Subgroup G → Subgroup G) (Y : Subgroup G)

@[expose] def Case148One : Prop :=
  deltaZero A LB Y ≤ pPrimeCoreOf 3 Y

variable [(ker148 A Y).Normal]

@[expose] def Case148Two : Prop :=
  ∃ c : G, Subgroup.zpowers c ∈ omegaA A ∧
    deltaZero A LB Y = pPrimeCoreOf 3 (deltaZero A LB Y) ⊔
      deltaZero A LB (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
    ∃ L ∈ lA A c,
      Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      ((Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
          (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
            CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
          (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
            CFSG.Assembly.RankThreeEven.projSU 3 5 1))) ∧
        Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* alternatingGroup (Fin 7))) ∨
      (∃ (p f e : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e ∧
        Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p (f * e) ∧
        IsLThreeEpsAt ↥(img148 A Y (deltaZero A LB Y)) p f) ∨
      (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
        (Sec4.IsTripleCover ↥(img148 A Y (deltaZero A LB Y)) (alternatingGroup (Fin 6)) ∨
          Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* alternatingGroup (Fin 5))))

@[expose] def Case148Three : Prop :=
  ∃ (c d : G) (L : Subgroup G), Subgroup.zpowers c ∈ omegaA A ∧ L ∈ lA A c ∧
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
    d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn L d ∧
    deltaZero A LB Y = pPrimeCoreOf 3 (deltaZero A LB Y) ⊔
      deltaZero A LB (Y ⊓ Subgroup.centralizer ({d} : Set G)) ∧
    (Sec4.IsTripleCover ↥(img148 A Y (deltaZero A LB Y)) CFSG.Blueprint.NativeSporadic.ON ∨
      IsCentralProductA6Covers ↥(img148 A Y (deltaZero A LB Y)) ∨
      IsA6CoverTimesA5 ↥(img148 A Y (deltaZero A LB Y)) ∨
      Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃*
        alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∨
      Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* alternatingGroup (Fin 7)) ∨
      (∃ _ : Fact (Nat.Prime 7), Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))))

@[expose] def Case148Four : Prop :=
  Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* alternatingGroup (Fin 10)) ∧
    (∃ (c : G) (L : Subgroup G), Subgroup.zpowers c ∈ omegaA A ∧ L ∈ lA A c ∧
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))) ∧
    (Nonempty (wStar A ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (wStar A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))

@[expose] def Case148Five : Prop :=
  ∃ (c : G) (hcA : c ∈ A) (L : Subgroup G) (n m : ℕ), Subgroup.zpowers c ∈ omegaA A ∧
    L ∈ lA A c ∧ 1 ≤ n ∧ 1 ≤ m ∧
    Sec4.IsoLThreePi ↥(img148 A Y (deltaZero A LB Y)) 2 (3 * n) ∧
    img148 A Y (deltaZero A LB Y ⊔ A) =
      img148 A Y (deltaZero A LB Y) ⊔ Subgroup.zpowers (alpha148 A Y c hcA) ∧
    alpha148 A Y c hcA ∉ img148 A Y (deltaZero A LB Y) ∧
    KFacts.InducesStdKind (img148 A Y (deltaZero A LB Y)) (alpha148 A Y c hcA) .field ∧
    IsLThreeEpsAt (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 (n * m) ∧
    inSubgroup perfectResidual
        (oPrimeResidualOf 3 (deltaZero A LB Y ⊓ Subgroup.centralizer ({c} : Set G))) =
      deltaZero A LB (inSubgroup perfectResidual
        (oPrimeResidualOf 3 (deltaZero A LB Y ⊓ Subgroup.centralizer ({c} : Set G)))) ∧
    ∃ K : Subgroup G, K ≤ L ⊓ Y ∧ Sec4.IsoLThreePi ↥(img148 A Y K) 2 n ∧
      Group.IsPerfect ↥K ∧ K = deltaZero A LB K

@[expose] def Case148Six : Prop :=
  Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃*
      alternatingGroup (Fin 5) × CFSG.Blueprint.NativeSporadic.J2) ∧
    (∃ (c : G) (L : Subgroup G), Subgroup.zpowers c ∈ omegaA A ∧ L ∈ lA A c ∧
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) ∧
    (omegaA A).ncard = 6

@[expose] def Case148Seven : Prop :=
  ∃ (a₁ a₂ : G) (L₁ L₂ J₁ J₂ : Subgroup G) (p₁ f₁ e₁ p₂ f₂ e₂ : ℕ)
      (_ : Fact p₁.Prime) (_ : Fact p₂.Prime),
    Subgroup.zpowers a₁ ∈ omegaA A ∧ Subgroup.zpowers a₂ ∈ omegaA A ∧
    L₁ ∈ lA A a₁ ∧ L₂ ∈ lA A a₂ ∧ J₁ ≤ L₁ ⊓ Y ∧ J₂ ≤ L₂ ⊓ Y ∧
    img148 A Y J₁ ⊔ img148 A Y J₂ = img148 A Y (deltaZero A LB Y) ∧
    img148 A Y J₁ ⊓ img148 A Y J₂ = ⊥ ∧ ⁅img148 A Y J₁, img148 A Y J₂⁆ = ⊥ ∧
    1 ≤ f₁ ∧ 1 ≤ e₁ ∧ 1 ≤ f₂ ∧ 1 ≤ e₂ ∧
    IsZ3PGLThreeAt ↥(img148 A Y (J₁ ⊔ A)) p₁ f₁ ∧
    IsZ3PGLThreeAt ↥(img148 A Y (J₂ ⊔ A)) p₂ f₂ ∧
    Sec4.IsoLThreePi (↥L₁ ⧸ aschbacherSolvableCore 3 ↥L₁) p₁ (f₁ * e₁) ∧
    Sec4.IsoLThreePi (↥L₂ ⧸ aschbacherSolvableCore 3 ↥L₂) p₂ (f₂ * e₂)

@[expose] def Item148Cases : Prop :=
  Case148One A LB Y ∨ Case148Two A LB Y ∨ Case148Three A LB Y ∨ Case148Four A LB Y ∨
    Case148Five A LB Y ∨ Case148Six A LB Y ∨ Case148Seven A LB Y

end Cases

@[expose] def Item148At (A : Subgroup G) (LB : Subgroup G → Subgroup G) (Y : Subgroup G)
    (hY : Y ∈ scriptY A) : Prop :=
  letI := ker148_normal hY.2
  (((deltaZero A LB Y).subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal ∧
    Item148Cases A LB Y

theorem item148_iff (A : Subgroup G) (LB : Subgroup G → Subgroup G) :
    Item148 A LB ↔ ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), Item148At A LB Y hY :=
  Iff.rfl

@[expose] def Ind148 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (Y : Subgroup G) : Prop :=
  ∀ (Y' : Subgroup G) (hY' : Y' ∈ scriptY A), Nat.card Y' < Nat.card Y → Item148At A LB Y' hY'

end Certificates

@[expose] def YBOne (A : Subgroup G) (LB : Subgroup G → Subgroup G) (Y B : Subgroup G) :
    Prop :=
  deltaZero A LB (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
    pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G))

@[expose] def IsPoint148 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (Y B Q : Subgroup G)
    (e : G) (K Le : Subgroup G) : Prop :=
  IsHyperplane A B ∧ Q ∈ scriptQZero A LB ∧ Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) ∧
    e ∈ B ∧ e ≠ 1 ∧
    K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) ∧ K = deltaZero A LB K ∧
    K ≤ Le ∧ Le ∈ thetaComponentsAt 3 e ∧
    ((Subgroup.zpowers e ∈ omegaA A ∧ Le ∈ lA A e) ∨
      ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ c' ∈ B ∧
        L' ∈ lA A c' ∧
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
        IsThreeCentralIn L' e ∧
        Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) CFSG.Blueprint.NativeSporadic.ON)

@[expose] def KType148 (A Y : Subgroup G) [(ker148 A Y).Normal] (e : G) (K Le : Subgroup G) :
    Prop :=
  Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G) ∧
    ((Subgroup.zpowers e ∈ omegaA A ∧ Le ∈ lA A e ∧
        (Nonempty (↥(img148 A Y K) ≃* ↥Le ⧸ aschbacherSolvableCore 3 ↥Le) ∨
          ((Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
              (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
                CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
              (∃ _ : Fact (Nat.Prime 5), Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
                CFSG.Assembly.RankThreeEven.projSU 3 5 1))) ∧
            Nonempty (↥(img148 A Y K) ≃* alternatingGroup (Fin 7))) ∨
          (∃ (p f e' : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e' ∧
            Sec4.IsoLThreePi (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) p (f * e') ∧
            IsLThreeEpsAt ↥(img148 A Y K) p f))) ∨
      (Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) CFSG.Blueprint.NativeSporadic.ON ∧
        (Nonempty (↥(img148 A Y K) ≃* alternatingGroup (Fin 7)) ∨
          (∃ _ : Fact (Nat.Prime 7), Nonempty (↥(img148 A Y K) ≃*
            CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))))))

@[expose] def Type148 (X : Type) [Group X] : Prop :=
  IsLThreePi X ∨ (∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 3 ∧ 1 ≤ f ∧ IsLThreeEpsAt X p f) ∨
    Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)

section Lift

variable (A Y : Subgroup G) [(ker148 A Y).Normal]

@[expose] def Lift148Eq (K J : Subgroup G) : Prop :=
  img148 A Y K = img148 A Y J

@[expose] def Lift148Ten (K J : Subgroup G) : Prop :=
  Nonempty (↥(img148 A Y K) ≃* alternatingGroup (Fin 7)) ∧
    Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 10))

section CertificatesLift


@[expose] def Lift148Field (e : G) (he : e ∈ A) (K J : Subgroup G) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi ↥(img148 A Y K) 2 n ∧
    Sec4.IsoLThreePi ↥(img148 A Y J) 2 (3 * n) ∧
    KFacts.InducesStdKind (img148 A Y J) (alpha148 A Y e he) .field

@[expose] def Lift148D4 (e : G) (he : e ∈ A) (K J : Subgroup G) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi ↥(img148 A Y K) 2 n ∧
    CFSG.Blueprint.ChevalleyExceptionalModel ↥(img148 A Y J) .trialityD4 2 n ∧
    KFacts.InducesStdKind (img148 A Y J) (alpha148 A Y e he) .graphField

end CertificatesLift

end Lift

section Steps


@[expose] def Step148YB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y → ∀ B : Subgroup G,
      IsHyperplane A B → ¬ YBOne A (lB A) Y B →
      ∃ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
        (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
          Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) ∧
        deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
          pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB ∧
        ∃ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb ∧
          YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B

@[expose] def Step148YBShape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y → ∀ B : Subgroup G,
      IsHyperplane A B → ¬ YBOne A (lB A) Y B →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      ∃ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
        (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
          Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) ∧
        deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
          pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB ∧
        YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B

@[expose] def Step148HJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y

@[expose] def Step148Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
        (∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))) →
        Q ≤ pPrimeCoreOf 3 Y

@[expose] def Step148Point : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ Y ∈ scriptY A, ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ B : Subgroup G, IsHyperplane A B →
      ∀ Q ∈ scriptQZero A (lB A), Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) →
        ∃ (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le

@[expose] def Step148KType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
        letI := ker148_normal hY.2
        KType148 A Y e K Le

@[expose] def Step148Lift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      ∀ (e : G) (he : e ∈ A), e ≠ 1 →
      ∀ K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)),
      A ≤ Subgroup.normalizer (K : Set G) →
      Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G) →
      (letI := ker148_normal hY.2; Type148 ↥(img148 A Y K)) →
      ∃ J ∈ thetaComponentsIn Y, K ≤ J ∧ A ≤ Subgroup.normalizer (J : Set G) ∧
        letI := ker148_normal hY.2
        (Lift148Eq A Y K J ∨ Lift148Ten A Y K J ∨ Lift148Field A Y e he K J ∨
          Lift148D4 A Y e he K J)

@[expose] def Step148D4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148D4 A Y e he K J) → False

@[expose] def Step148D4Data : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) → ∀ n : ℕ, 1 ≤ n →
        (letI := ker148_normal hY.2; Sec4.IsoLThreePi ↥(img148 A Y K) 2 n ∧
            CFSG.Blueprint.ChevalleyExceptionalModel ↥(img148 A Y J) .trialityD4 2 n ∧
            KFacts.InducesStdKind (img148 A Y J) (alpha148 A Y e he) .graphField) →
        ∃ (b : G) (Jb Lb : Subgroup G), B ⊓ J = Subgroup.zpowers b ∧ b ≠ 1 ∧
          Jb ∈ thetaComponentsIn (J ⊓ Subgroup.centralizer ({b} : Set G)) ∧
          Sec4.IsSLThreePiAt (↥Jb ⧸ aschbacherSolvableCore 3 ↥Jb) (2 ^ n) ∧ Jb = ⁅Q, Jb⁆ ∧
          Subgroup.zpowers b ∈ omegaA A ∧ Lb ∈ lA A b ∧ Jb ≤ Lb ∧ b ∈ Jb

@[expose] def Step148One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2;
          Lift148Eq A Y K J ∨ Lift148Ten A Y K J ∨ Lift148Field A Y e he K J) →
        A = Subgroup.zpowers e ⊔ (A ⊓ J) ∨
          ∃ (p f : ℕ), 1 ≤ f ∧
            (letI := ker148_normal hY.2; IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f)

@[expose] def Step148Rank : Prop :=
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
        Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Four A (lB A) Y ∨
          Case148Five A (lB A) Y

@[expose] def Step148PGL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2;
          Lift148Eq A Y K J ∨ Lift148Ten A Y K J ∨ Lift148Field A Y e he K J) →
        (∃ (p f : ℕ), 1 ≤ f ∧
          (letI := ker148_normal hY.2; IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f)) →
        letI := ker148_normal hY.2
        Case148Two A (lB A) Y ∨ Case148Seven A (lB A) Y

@[expose] def Step148Normal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (letI := ker148_normal hY.2; Item148Cases A (lB A) Y) →
      ¬ Case148One A (lB A) Y →
      (((deltaZero A (lB A) Y).subgroupOf Y).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal

@[expose] def Item148S14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Item148 A (lB A)

@[expose] def Item148NormalS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Item148Normal A (lB A)

@[expose] def Step148Lift429 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      ∀ (e : G) (he : e ∈ A), e ≠ 1 →
      ∀ K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)),
      A ≤ Subgroup.normalizer (K : Set G) →
      Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G) →
      (letI := ker148_normal hY.2; Type148 ↥(img148 A Y K)) →
      ∀ J ∈ thetaComponentsIn Y, K ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
        letI := ker148_normal hY.2
        Lift148Eq A Y K J ∨ Lift148Ten A Y K J ∨ Lift148Field A Y e he K J ∨
          Lift148D4 A Y e he K J

end Steps

@[expose] def Item148Small (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A),
    (letI := ker148_normal hY.2; IsQuasisimple ↥(img148 A Y (deltaZero A LB Y))) →
    (letI := ker148_normal hY.2;
      Nat.card ↥(img148 A Y (deltaZero A LB Y)) = 60 ∨
        Nat.card ↥(img148 A Y (deltaZero A LB Y)) = 1080) →
    ∃ c : G, Subgroup.zpowers c ∈ omegaA A ∧
      deltaZero A LB Y = pPrimeCoreOf 3 (deltaZero A LB Y) ⊔
        deltaZero A LB (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
      ∃ L ∈ lA A c,
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)

@[expose] def Item148Simple (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A) {K : Type} [Group K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) →
    (letI := ker148_normal hY.2; Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* K)) →
    IsEmpty (K ≃* alternatingGroup (Fin 5)) → IsEmpty (K ≃* alternatingGroup (Fin 7)) →
    IsEmpty (K ≃* alternatingGroup (Fin 10)) →
    (∀ (p f : ℕ) [Fact p.Prime], ¬ IsLThreeEpsAt K p f) →
    ∃ c' : G, Subgroup.zpowers c' ∈ omegaA A ∧
      ∃ L' ∈ lA A c', Nonempty (K ≃* ↥L' ⧸ aschbacherSolvableCore 3 ↥L')

@[expose] def Item148SmallS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Item148Small A (lB A)

@[expose] def Item148SimpleS14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → Item148Simple A (lB A)

end CFSG.RankThree.PartTwo.Sec14
