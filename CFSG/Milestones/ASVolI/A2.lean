module

public import CFSG.Milestones.ASVolI.A1
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Small
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Sporadic
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.McL
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.U54
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Alt9
public import CFSG.Adapters.StatedPSLTwoNine
public import CFSG.LieType.SeitzGeneration.UnitaryHyperDiag
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Glue
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Main
public import CFSG.RankThree.OddKernel.SimpleQuotient
public import CFSG.RankThree.OddKernel.FailureReduction
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.LocalAnalysis.SectionRank.QTK.A134ListSL2
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Milestones.LR_rank_two_isomorphism_types
public import CFSG.RankThree.PartOne.KF.F128SL
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimePrimeCentralizer
public import CFSG.GH74.GLS.IVK.Proofs2.Std44LinConj
public import CFSG.GH74.GLS.IVK.Proofs2.Std44UniConj
public import CFSG.GH74.KGroups.L3EpsBlockLin
public import CFSG.GH74.GLS.LU.Local.L3Cover
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
public import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerT
public import CFSG.Quasithin.Background.A3FactsNumber
public import CFSG.Milestones.ASVolI.I1

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint
open CFSG.ASVolI.ChA

namespace ChA

@[expose] def IsSectionOf (S : Type*) [Group S] (G : Type*) [Group G] : Prop :=
  ∃ (H K : Subgroup G) (_ : (K.subgroupOf H).Normal), Nonempty (S ≃* ↥H ⧸ K.subgroupOf H)

@[expose] def IsProperSectionOf (S : Type*) [Group S] (G : Type*) [Group G] : Prop :=
  IsSectionOf S G ∧ Nat.card S < Nat.card G

@[expose] def TheoremAConclusion (G : Type) [Group G] [Finite G]
    (S : Type) [Group S] [Finite S] (p : ℕ) : Prop :=
  ((twoLocalPrimeRank p S ≤ twoLocalPrimeRank p G ∧ twoLocalPrimeRank p G ≤ 2) ∨
    (p = 3 ∧ ∃ (H H₁ H₂ : Subgroup G) (n₁ n₂ : ℕ),
      Nonempty (S ≃* ↥H ⧸ Subgroup.center ↥H) ∧ pRank 3 H = 3 ∧ H = H₁ ⊔ H₂ ∧
      IsComponentOf H₁ H ∧ IsComponentOf H₂ H ∧ IsSUn 3 (2 ^ n₁) ↥H₁ ∧ IsSUn 3 (2 ^ n₂) ↥H₂ ∧
      3 ≤ n₁ ∧ Odd n₁ ∧ 3 ≤ n₂ ∧ Odd n₂ ∧ centerOf H₁ = centerOf H₂ ∧
      (Nat.gcd n₁ n₂ = 1 ∨ Nat.gcd n₁ n₂ = 3))) ∧
  (pRank p (⊤ : Subgroup G) ≤ 2 → pRank p (⊤ : Subgroup S) ≤ pRank p (⊤ : Subgroup G))

@[expose] def TheoremAHolds (G : Type) [Group G] [Finite G] : Prop :=
  evenRank G ≤ 2 → CFSG.SectionRank.IsKGroupCat G →
    ∀ (S : Type) [Group S] [Finite S], IsSectionOf S G → genFittingLayer S = ⊤ →
      (∀ p : ℕ, p.Prime → p ≠ 2 → TheoremAConclusion G S p) ∧
      (CFSG.IsStronglyQuasithin G → CFSG.IsStronglyQuasithin S)

@[expose] def TheoremBList (G : Type) [Group G] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ n ≤ 9 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 2 p f) ∨
  (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ (e = 1 ∨ e = 2) ∧
    (StatedClassicalModel G .PSL 3 p e ∨ StatedClassicalModel G .PSU 3 p e)) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    (StatedClassicalModel G .PSp 2 p 1 ∨ ChevalleyExceptionalModel G .G2 p 1)) ∨
  (∃ a r : ℕ, r = 2 ^ a + 1 ∧ r.Prime ∧ StatedClassicalModel G .PSL 4 r 1) ∨
  (∃ b s : ℕ, s = 2 ^ b - 1 ∧ s.Prime ∧ StatedClassicalModel G .PSU 4 s 1) ∨
  (∃ f : ℕ,
    (2 ≤ f ∧ StatedClassicalModel G .PSL 2 2 f) ∨
    (1 ≤ f ∧ StatedClassicalModel G .PSL 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel G .PSU 3 2 f) ∨
    (1 ≤ f ∧ StatedClassicalModel G .PSU 4 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel G .PSp 2 2 f) ∨
    (2 ≤ f ∧ ChevalleyExceptionalModel G .G2 2 f) ∨
    (1 ≤ f ∧ ChevalleyExceptionalModel G .trialityD4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ ReeTitsModel G .twistedF4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ SuzukiModel G 2 f)) ∨
  ReeTitsModel G .Tits 2 1 ∨ StatedClassicalModel G .PSU 5 2 2 ∨
  StatedClassicalModel G .PSL 4 2 1 ∨ StatedClassicalModel G .PSL 5 2 1 ∨
  StatedClassicalModel G .PSp 3 2 1 ∨
  (∃ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J1 ∨ s = .J2 ∨ s = .J3 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .McL) ∧
    Nonempty (G ≃* NativeSporadic.Carrier s))

@[expose] def TheoremBHolds (G : Type) [Group G] [Finite G] : Prop :=
  IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → evenRank G ≤ 2 →
    CFSG.SectionRank.IsKGroupCat G → TheoremBList G

@[expose] def TheoremCHolds (G : Type) [Group G] [Finite G] : Prop :=
  IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → CFSG.SectionRank.IsSQTKCat G →
    CFSG.Milestones.SQTKSimpleList G

@[expose] def IsMinimalCounterexampleToA (G : Type) [Group G] [Finite G]
    (S : Type) [Group S] [Finite S] (p : ℕ) : Prop :=
  evenRank G ≤ 2 ∧ CFSG.SectionRank.IsKGroupCat G ∧ IsSectionOf S G ∧ genFittingLayer S = ⊤ ∧
  p.Prime ∧ p ≠ 2 ∧ ¬ TheoremAConclusion G S p ∧
  ∀ (X : Type) [Group X] [Finite X], IsProperSectionOf X G → TheoremAHolds X

@[expose] def IsMinimalCounterexampleABC (G : Type) [Group G] [Finite G] : Prop :=
  (¬ TheoremAHolds G ∨ ¬ TheoremBHolds G ∨ ¬ TheoremCHolds G) ∧
  ∀ (X : Type) [Group X] [Finite X], IsProperSectionOf X G →
    TheoremAHolds X ∧ TheoremBHolds X ∧ TheoremCHolds X

section LieAut

open CFSG.Blueprint.Chevalley

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def glMapAut (σ : K ≃+* K) : GL ι K →* GL ι K :=
  Units.map (RingHom.mapMatrix (σ : K →+* K)).toMonoidHom

@[expose] def IsProjFieldAut (H : Subgroup (GL ι K)) (σ : K ≃+* K)
    (φ : MulAut (StatedProj H)) : Prop :=
  ∀ g : ↥H, ∃ g' : ↥H, (g' : GL ι K) = glMapAut σ (g : GL ι K) ∧
    φ (QuotientGroup.mk g) = QuotientGroup.mk g'

@[expose] def IsProjConjAut (H : Subgroup (GL ι K)) (c : GL ι K)
    (φ : MulAut (StatedProj H)) : Prop :=
  ∀ g : ↥H, ∃ g' : ↥H, (g' : GL ι K) = c * g * c⁻¹ ∧
    φ (QuotientGroup.mk g) = QuotientGroup.mk g'

@[expose] def IsEvenLieThmC (S : Type) [Group S] : Prop :=
  (∃ n, StatedClassicalModel S .PSL 2 2 n) ∨ (∃ n, StatedClassicalModel S .PSL 3 2 n) ∨
  (∃ n, StatedClassicalModel S .PSU 3 2 n) ∨ (∃ n, StatedClassicalModel S .PSp 2 2 n) ∨
  (∃ n, ChevalleyExceptionalModel S .G2 2 n) ∨ (∃ n, ChevalleyExceptionalModel S .trialityD4 2 n) ∨
  (∃ n, SuzukiModel S 2 n) ∨ (∃ n, ReeTitsModel S .twistedF4 2 n) ∨ ReeTitsModel S .Tits 2 1 ∨
  StatedClassicalModel S .PSL 4 2 1 ∨ StatedClassicalModel S .PSL 5 2 1 ∨
  Nonempty (S ≃* alternatingGroup (Fin 6)) ∨ StatedClassicalModel S .PSU 3 3 1

@[expose] def IsEvenLieAll (S : Type) [Group S] : Prop :=
  CFSG.Blueprint.EvenLieType S ∨ Nonempty (S ≃* alternatingGroup (Fin 6)) ∨
    StatedClassicalModel S .PSU 3 3 1

@[expose] def IsFieldAut (S : Type) [Group S] (θ : MulAut S) : Prop :=
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (e : S ≃* StatedProj (StatedSL 2 K))
      (σ : RingAut K), Nat.card K = 2 ^ n ∧ IsProjFieldAut (StatedSL 2 K) σ (MulAut.congr e θ)) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (e : S ≃* StatedProj (StatedSL 3 K))
      (σ : RingAut K), Nat.card K = 2 ^ n ∧ IsProjFieldAut (StatedSL 3 K) σ (MulAut.congr e θ)) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
      (e : S ≃* StatedProj (StatedSU 3 (2 ^ n) K)) (σ : RingAut K), Nat.card K = (2 ^ n) ^ 2 ∧
        Odd (orderOf σ) ∧ IsProjFieldAut (StatedSU 3 (2 ^ n) K) σ (MulAut.congr e θ)) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (e : S ≃* StatedProj (StatedSp 2 K))
      (σ : RingAut K), Nat.card K = 2 ^ n ∧ IsProjFieldAut (StatedSp 2 K) σ (MulAut.congr e θ)) ∨
  (∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (e : S ≃* ↥(suzukiGroup a K))
      (σ : RingAut K), Nat.card K = 2 ^ (2 * a + 1) ∧
        ∀ g : ↥(suzukiGroup a K), ∃ g' : ↥(suzukiGroup a K),
          (g' : GL (Fin 4) K) = glMapAut σ (g : GL (Fin 4) K) ∧ MulAut.congr e θ g = g') ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (e : S ≃* AdjointQuotient Tag.G2 K)
      (σ : RingAut K), Nat.card K = 2 ^ n ∧
        ∀ g : ↥(adjointGroup Tag.G2 K), ∃ g' : ↥(adjointGroup Tag.G2 K),
          (g' : ModGL Tag.G2 K) = Units.map (entrywiseHom (σ : K →+* K)) (g : ModGL Tag.G2 K) ∧
          MulAut.congr e θ (QuotientGroup.mk g) = QuotientGroup.mk g') ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (σq : K →+* K)
      (e : S ≃* DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σq)) (σ : RingAut K),
      Nat.card K = (2 ^ n) ^ 3 ∧ (∀ c, σq c = c ^ 2 ^ n) ∧ Nat.Coprime (orderOf σ) 3 ∧
        ∀ g : ↥⁅twistedFixedGroup TwistTag.D4 K σq, twistedFixedGroup TwistTag.D4 K σq⁆,
          ∃ g' : ↥⁅twistedFixedGroup TwistTag.D4 K σq, twistedFixedGroup TwistTag.D4 K σq⁆,
            (g' : ModGL TwistTag.D4.tag K) =
              Units.map (entrywiseHom (σ : K →+* K)) (g : ModGL TwistTag.D4.tag K) ∧
            MulAut.congr e θ (QuotientGroup.mk g) = QuotientGroup.mk g') ∨
  (∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
      (e : S ≃* DerivedCentralQuotient
        (reeFixedGroup Tag.F4 K reeF4Perm fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)))
      (σ : RingAut K), Nat.card K = 2 ^ (2 * a + 1) ∧
        ∀ g : ↥⁅reeFixedGroup Tag.F4 K reeF4Perm
            (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)),
            reeFixedGroup Tag.F4 K reeF4Perm
            (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1))⁆,
          ∃ g' : ↥⁅reeFixedGroup Tag.F4 K reeF4Perm
            (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)),
            reeFixedGroup Tag.F4 K reeF4Perm
            (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1))⁆,
            (g' : ModGL Tag.F4 K) =
              Units.map (entrywiseHom (σ : K →+* K)) (g : ModGL Tag.F4 K) ∧
            MulAut.congr e θ (QuotientGroup.mk g) = QuotientGroup.mk g') ∨
  (θ = 1 ∧ (StatedClassicalModel S .PSL 4 2 1 ∨ StatedClassicalModel S .PSL 5 2 1 ∨
    ReeTitsModel S .Tits 2 1 ∨ Nonempty (S ≃* alternatingGroup (Fin 6)) ∨
    StatedClassicalModel S .PSU 3 3 1))

@[expose] def IsInnDiagAut (S : Type) [Group S] (ψ : MulAut S) : Prop :=
  ψ ∈ (MulAut.conj : S →* MulAut S).range ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (e : S ≃* StatedProj (StatedSL 3 K))
      (c : GL (Fin 3) K), Nat.card K = 2 ^ n ∧ IsProjConjAut (StatedSL 3 K) c (MulAut.congr e ψ)) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
      (e : S ≃* StatedProj (StatedSU 3 (2 ^ n) K)) (c : GL (Fin 3) K), Nat.card K = (2 ^ n) ^ 2 ∧
        IsProjConjAut (StatedSU 3 (2 ^ n) K) c (MulAut.congr e ψ))

@[expose] def IsInnDiagFieldAut (S : Type) [Group S] (θ : MulAut S) : Prop :=
  ∃ ψ₁ ψ₂ : MulAut S, IsInnDiagAut S ψ₁ ∧ IsFieldAut S ψ₂ ∧ θ = ψ₁ * ψ₂

@[expose] def innDiagSubgroup (S : Type) [Group S] : Subgroup (MulAut S) :=
  Subgroup.closure {ψ | IsInnDiagAut S ψ}

end LieAut

end ChA

@[expose] def A_2_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], evenRank G ≤ 2 → CFSG.SectionRank.IsKGroupCat G →
    ∀ (S : Type) [Group S] [Finite S], IsSectionOf S G → genFittingLayer S = ⊤ →
      (∀ p : ℕ, p.Prime → p ≠ 2 → TheoremAConclusion G S p) ∧
      (CFSG.IsStronglyQuasithin G → CFSG.IsStronglyQuasithin S)

theorem A_2_1_iff : A_2_1 ↔ ∀ (G : Type) [Group G] [Finite G], TheoremAHolds G :=
  Iff.rfl

@[expose] def A_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    evenRank G ≤ 2 → CFSG.SectionRank.IsKGroupCat G → TheoremBList G

section BurnsideWA2

private theorem theoremBList_of_qtkSimpleList {G : Type} [Group G]
    (h : CFSG.SectionRank.QTK.QTKSimpleList G) : TheoremBList G := by
  unfold CFSG.SectionRank.QTK.QTKSimpleList at h
  unfold TheoremBList
  rcases h with h1 | ⟨p, hp, hp2, h2⟩ | (⟨f, h3⟩ | h3 | h3) | h4 | h5
  · exact Or.inl h1
  · rcases h2 with ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | hm | hm | ⟨⟨a, ha⟩, hm⟩ | ⟨⟨b, hb⟩, hm⟩
    · iterate 1 right
      exact Or.inl ⟨p, f, hp, hp2, hf, hm⟩
    · iterate 2 right
      exact Or.inl ⟨p, f, hp, hp2, hf, hm⟩
    · iterate 3 right
      exact Or.inl ⟨p, hp, hp2, Or.inl hm⟩
    · iterate 3 right
      exact Or.inl ⟨p, hp, hp2, Or.inr hm⟩
    · iterate 4 right
      exact Or.inl ⟨a, p, ha, hp, hm⟩
    · iterate 5 right
      exact Or.inl ⟨b, p, by omega, hp, hm⟩
  · iterate 6 right
    refine Or.inl ⟨f, ?_⟩
    rcases h3 with a | b | c | d | e | f' | g | h | i
    · exact Or.inl a
    · iterate 1 right
      exact Or.inl b
    · iterate 2 right
      exact Or.inl c
    · iterate 4 right
      exact Or.inl d
    · iterate 3 right
      exact Or.inl e
    · iterate 5 right
      exact Or.inl f'
    · iterate 6 right
      exact Or.inl g
    · iterate 7 right
      exact Or.inl h
    · iterate 8 right
      exact i
  · iterate 8 right
    exact Or.inl h3
  · iterate 7 right
    exact Or.inl h3
  · rcases h4 with ⟨n, hn | hn, hm⟩ | hm
    · subst hn
      iterate 9 right
      exact Or.inl hm
    · subst hn
      iterate 10 right
      exact Or.inl hm
    · iterate 11 right
      exact Or.inl hm
  · iterate 12 right
    exact h5

end BurnsideWA2

section

theorem as_A_2_2
    : A_2_2 := by
  intro G _ _ hsimple hnonab hev hK
  haveI := hsimple
  exact theoremBList_of_qtkSimpleList
    (CFSG.SectionRank.QTK.qtk_simple_list_simple G hnonab hev hK)

end

@[expose] def A_2_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.SectionRank.IsSQTKCat G →
    ∀ (L : Subgroup G) [L.Normal],
      CFSG.IsQuasisimple (↥L ⧸ pCore 2 ↥L) →
      IsEvenLieAll ((↥L ⧸ pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ pCore 2 ↥L)) →
      IsEvenLieThmC ((↥L ⧸ pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ pCore 2 ↥L)) ∧
      ∀ x : G, Odd (orderOf x) →
        ∃ θ : MulAut ((↥L ⧸ pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ pCore 2 ↥L)),
          IsInnDiagFieldAut _ θ ∧
          ∀ l : ↥L, θ (QuotientGroup.mk (QuotientGroup.mk l)) =
            QuotientGroup.mk (QuotientGroup.mk (MulAut.conjNormal x l))

@[expose] def A_2_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) [K.Normal] (p : ℕ), p.Prime → p ≠ 2 →
    (pRank p (⊤ : Subgroup G) ≤ 1 → pRank p (⊤ : Subgroup (G ⧸ K)) ≤ pRank p (⊤ : Subgroup G)) ∧
    (twoLocalPrimeRank p G ≤ 1 → twoLocalPrimeRank p (G ⧸ K) ≤ twoLocalPrimeRank p G) ∧
    (pRank p (⊤ : Subgroup (G ⧸ K)) ≤ 2 →
      pRank p (⊤ : Subgroup (G ⧸ K)) ≤ pRank p (⊤ : Subgroup G)) ∧
    (twoLocalPrimeRank p (G ⧸ K) ≤ 2 → twoLocalPrimeRank p (G ⧸ K) ≤ twoLocalPrimeRank p G) ∧
    (pRank p (⊤ : Subgroup (G ⧸ K)) ≤ 2 →
      pRank p (⊤ : Subgroup (G ⧸ K)) ≤ pRank p (⊤ : Subgroup G) ∧
      twoLocalPrimeRank p (G ⧸ K) ≤ twoLocalPrimeRank p G)

private theorem a27_pRank_top_subgroup_eq {X : Type*} [Group X] [Finite X] (p : ℕ) :
    CFSG.pRank p ↥(⊤ : Subgroup X) = CFSG.pRank p X := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top p ↥(⊤ : Subgroup X),
    CFSG.SectionRank.pRank_eq_open_pRank_top p X,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup X)]

private theorem a27_twoLocalPrimeRank_le_pRank {X : Type*} [Group X] [Finite X] {p : ℕ} (hp :
    p.Prime) :
    twoLocalPrimeRank p X ≤ CFSG.pRank p X := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine csSup_le' ?_
  rintro _ ⟨H, -, rfl⟩
  exact CFSG.SectionRank.pRank_mono hp.one_lt le_top

private theorem a27_twoLocalPrimeRank_le_evenRank {X : Type*} [Group X] [Finite X] {p : ℕ} (hp
    : p.Prime)
    (hp2 : p ≠ 2) : twoLocalPrimeRank p X ≤ evenRank X := by
  refine csSup_le' ?_
  rintro _ ⟨H, hH, rfl⟩
  refine le_csSup ⟨Nat.card X, ?_⟩ ⟨p, H, hp, hp2, hH, rfl⟩
  rintro _ ⟨q, K, hq, -, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt K

private theorem a214_evenRank_le_two_of_isStronglyQuasithin {X : Type*} [Group X] [Finite X]
    (h : CFSG.IsStronglyQuasithin X) : evenRank X ≤ 2 := by
  refine csSup_le' ?_
  rintro _ ⟨p, H, hp, hp2, -, rfl⟩
  exact (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans
    (CFSG.SectionRank.isStronglyQuasithin_iff.mp h p hp hp2)

private theorem a214_evenRank_le_two_and_isKGroupCat_of_minimalCounterexampleABC {G : Type}
    [Group G]
    [Finite G] (h : IsMinimalCounterexampleABC G) :
    evenRank G ≤ 2 ∧ CFSG.SectionRank.IsKGroupCat G := by
  rcases h.1 with hA | hB | hC
  · by_contra hc
    exact hA fun h1 h2 => absurd ⟨h1, h2⟩ hc
  · by_contra hc
    exact hB fun _ _ h1 h2 => absurd ⟨h1, h2⟩ hc
  · by_contra hc
    exact hC fun _ _ hsq => absurd ⟨a214_evenRank_le_two_of_isStronglyQuasithin hsq.1, hsq.2⟩ hc

theorem as_A_2_7 : A_2_7 := by
  intro G _ _ K _ p hp hp2
  simp only [a27_pRank_top_subgroup_eq]
  have h1 : CFSG.pRank p G ≤ 1 → CFSG.pRank p (G ⧸ K) ≤ CFSG.pRank p G := fun h =>
    CFSG.RankThree.OddKernel.pRank_le_of_surjective_of_le_one hp hp2 (QuotientGroup.mk' K)
      (QuotientGroup.mk'_surjective K) h
  have h2 : twoLocalPrimeRank p G ≤ 1 →
      twoLocalPrimeRank p (G ⧸ K) ≤ twoLocalPrimeRank p G := fun h =>
    CFSG.RankThree.OddKernel.localRank_quotient_le_of_surjective hp.one_lt K
      (fun _ _ ψ hψ hM =>
        (CFSG.RankThree.OddKernel.pRank_le_of_surjective_of_le_one hp hp2 ψ hψ (hM.trans h)).trans
          hM) le_rfl
  have h3 : CFSG.pRank p (G ⧸ K) ≤ 2 → CFSG.pRank p (G ⧸ K) ≤ CFSG.pRank p G := fun h => by
    by_cases hG : CFSG.pRank p G ≤ 1
    · exact h1 hG
    · omega
  have h4 : twoLocalPrimeRank p (G ⧸ K) ≤ 2 →
      twoLocalPrimeRank p (G ⧸ K) ≤ twoLocalPrimeRank p G := fun h => by
    by_cases hG : twoLocalPrimeRank p G ≤ 1
    · exact h2 hG
    · omega
  exact ⟨h1, h2, h3, h4, fun h => ⟨h3 h, h4 ((a27_twoLocalPrimeRank_le_pRank hp).trans h)⟩⟩

@[expose] def A_2_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Type) [Group S] [Finite S] (p : ℕ),
    IsMinimalCounterexampleToA G S p →
    (∀ H : Subgroup G, IsSectionOf S ↥H → H = ⊤) ∧
    (∃ (K : Subgroup G) (_ : K.Normal), Nonempty (S ≃* G ⧸ K))

section BurnsideMA2

private theorem burnside_pRank_top_eq {X : Type*} [Group X] [Finite X] (p : ℕ) :
    CFSG.pRank p ↥(⊤ : Subgroup X) = CFSG.pRank p X := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top p ↥(⊤ : Subgroup X),
    CFSG.SectionRank.pRank_eq_open_pRank_top p X,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup X)]

private theorem burnside_twoLocalPrimeRank_le_pRank {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) : twoLocalPrimeRank p X ≤ CFSG.pRank p X := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine csSup_le' ?_
  rintro _ ⟨H, -, rfl⟩
  exact CFSG.SectionRank.pRank_mono hp.one_lt le_top

private theorem burnside_twoLocalPrimeRank_le_evenRank {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : twoLocalPrimeRank p X ≤ evenRank X := by
  refine csSup_le' ?_
  rintro _ ⟨H, hH, rfl⟩
  refine le_csSup ⟨Nat.card X, ?_⟩ ⟨p, H, hp, hp2, hH, rfl⟩
  rintro _ ⟨q, K, hq, -, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt K

private theorem burnside_evenRank_le_two_of_isStronglyQuasithin {X : Type*} [Group X] [Finite X]
    (h : CFSG.IsStronglyQuasithin X) : evenRank X ≤ 2 := by
  refine csSup_le' ?_
  rintro _ ⟨p, H, hp, hp2, -, rfl⟩
  exact (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans
    (CFSG.SectionRank.isStronglyQuasithin_iff.mp h p hp hp2)

private theorem burnside_evenRank_isKGroup_of_minimalABC {G : Type} [Group G] [Finite G]
    (h : IsMinimalCounterexampleABC G) :
    evenRank G ≤ 2 ∧ CFSG.SectionRank.IsKGroupCat G := by
  rcases h.1 with hA | hB | hC
  · by_contra hc
    exact hA fun h1 h2 => absurd ⟨h1, h2⟩ hc
  · by_contra hc
    exact hB fun _ _ h1 h2 => absurd ⟨h1, h2⟩ hc
  · by_contra hc
    exact hC fun _ _ hsq => absurd ⟨burnside_evenRank_le_two_of_isStronglyQuasithin hsq.1, hsq.2⟩ hc

private theorem burnside_pRank_le_of_injective {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y]
    {p : ℕ} (hp : 1 < p) (f : X →* Y) (hf : Function.Injective f) :
    CFSG.pRank p X ≤ CFSG.pRank p Y := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top p X, CFSG.SectionRank.pRank_eq_open_pRank_top p Y]
  exact CFSG.SectionRank.pRank_top_le_of_injective hp f hf

private theorem burnside_pRank_quotient_two {Y : Type*} [Group Y] [Finite Y] (N : Subgroup Y)
    [N.Normal]
    (hN : IsPGroup 2 N) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.pRank p (Y ⧸ N) = CFSG.pRank p Y := by
  have : Fact p.Prime := ⟨hp⟩
  have hnd : ¬ p ∣ Nat.card N := by
    intro h
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hN
    rw [hk] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have h := CFSG.SectionRank.pRank_quotient_eq (p := p) N hnd
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top p (Y ⧸ N),
    CFSG.SectionRank.pRank_eq_open_pRank_top p Y]
  exact h

private theorem burnside_isTwoLocal_map_inj {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) {L : Subgroup X} (hL : IsTwoLocal L) :
    ∃ L' : Subgroup Y, IsTwoLocal L' ∧ L.map f ≤ L' := by
  obtain ⟨P, hP1, hP2, rfl⟩ := hL
  refine ⟨Subgroup.normalizer ((P.map f : Subgroup Y) : Set Y), ⟨P.map f, ?_, ?_, rfl⟩, ?_⟩
  · intro h
    exact hP1 ((Subgroup.map_eq_bot_iff_of_injective P hf).mp h)
  · exact hP2.of_equiv (P.equivMapOfInjective f hf)
  · exact Subgroup.le_normalizer_map (H := P) f

private theorem burnside_twoLocalPrimeRank_le_of_injective {X Y : Type*} [Group X] [Group Y]
    [Finite X]
    [Finite Y] {p : ℕ} (hp : p.Prime) (f : X →* Y) (hf : Function.Injective f) :
    twoLocalPrimeRank p X ≤ twoLocalPrimeRank p Y := by
  refine csSup_le' ?_
  rintro _ ⟨L, hL, rfl⟩
  obtain ⟨L', hL', hLL'⟩ := burnside_isTwoLocal_map_inj f hf hL
  have h1 : CFSG.Open.pRank p L ≤ CFSG.Open.pRank p L' :=
    (CFSG.SectionRank.pRank_le_map hp.one_lt f hf L).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt hLL')
  refine h1.trans (le_csSup ⟨Nat.card Y, ?_⟩ ⟨L', hL', rfl⟩)
  rintro _ ⟨K, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hp.one_lt K

private theorem burnside_evenRank_le_of_injective {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y] (f : X →* Y) (hf : Function.Injective f) : evenRank X ≤ evenRank Y := by
  refine csSup_le' ?_
  rintro _ ⟨q, L, hq, hq2, hL, rfl⟩
  obtain ⟨L', hL', hLL'⟩ := burnside_isTwoLocal_map_inj f hf hL
  have h1 : CFSG.Open.pRank q L ≤ CFSG.Open.pRank q L' :=
    (CFSG.SectionRank.pRank_le_map hq.one_lt f hf L).trans
      (CFSG.SectionRank.pRank_mono hq.one_lt hLL')
  refine h1.trans (le_csSup ⟨Nat.card Y, ?_⟩ ⟨q, L', hq, hq2, hL', rfl⟩)
  rintro _ ⟨q', K, hq', -, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hq'.one_lt K

private theorem burnside_isTwoLocal_top {G : Type*} [Group G] (U : Subgroup G) [U.Normal]
    (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥) : IsTwoLocal (⊤ : Subgroup G) :=
  ⟨U, hU1, hU2, (Subgroup.normalizer_eq_top_iff.mpr inferInstance).symm⟩

private theorem burnside_pRank_le_twoLocalPrimeRank_of_pCore {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hU : pCore 2 G ≠ ⊥) : CFSG.pRank p G ≤ twoLocalPrimeRank p G := by
  have hT : IsTwoLocal (⊤ : Subgroup G) :=
    burnside_isTwoLocal_top (pCore 2 G) CFSG.pCore_isPGroup hU
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact le_csSup ⟨Nat.card G, by
    rintro _ ⟨K, -, rfl⟩
    exact CFSG.SectionRank.pRank_le_card_of_one_lt hp.one_lt K⟩ ⟨⊤, hT, rfl⟩

private theorem burnside_pRank_le_two_of_pCore {G : Type} [Group G] [Finite G] {p : ℕ} (hp :
    p.Prime)
    (hp2 : p ≠ 2) (hev : evenRank G ≤ 2) (hU : pCore 2 G ≠ ⊥) : CFSG.pRank p G ≤ 2 :=
  (burnside_pRank_le_twoLocalPrimeRank_of_pCore hp hU).trans
    ((burnside_twoLocalPrimeRank_le_evenRank hp hp2).trans hev)

private theorem burnside_evenRank_quotient_le_two {G : Type} [Group G] [Finite G] (U : Subgroup G)
    [U.Normal] (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥) (hev : evenRank G ≤ 2) :
    evenRank (G ⧸ U) ≤ 2 := by
  refine le_trans (csSup_le' ?_) hev
  rintro _ ⟨q, L, hq, hq2, -, rfl⟩
  have h1 : CFSG.Open.pRank q L ≤ CFSG.Open.pRank q (⊤ : Subgroup (G ⧸ U)) :=
    CFSG.SectionRank.pRank_mono hq.one_lt le_top
  have h2 : CFSG.Open.pRank q (⊤ : Subgroup (G ⧸ U)) = CFSG.Open.pRank q (⊤ : Subgroup G) := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact burnside_pRank_quotient_two U hU2 hq hq2
  refine h1.trans (h2.le.trans ?_)
  exact le_csSup ⟨Nat.card G, by
    rintro _ ⟨q', K, hq', -, -, rfl⟩
    exact CFSG.SectionRank.pRank_le_card_of_one_lt hq'.one_lt K⟩
    ⟨q, ⊤, hq, hq2, burnside_isTwoLocal_top U hU2 hU1, rfl⟩

private theorem burnside_isSectionOf_quotient {X : Type} [Group X] (N : Subgroup X) [N.Normal] :
    IsSectionOf (X ⧸ N) X := by
  refine ⟨⊤, N, inferInstance, ⟨QuotientGroup.congr N (N.subgroupOf ⊤) Subgroup.topEquiv.symm ?_⟩⟩
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨(x : X), hx, rfl⟩

private theorem burnside_isSectionOf_quotient_quotient {G : Type} [Group G] (N M : Subgroup G)
    [N.Normal] [M.Normal] (h : N ≤ M) : IsSectionOf (G ⧸ M) (G ⧸ N) := by
  obtain ⟨H, K, hK, ⟨e⟩⟩ := burnside_isSectionOf_quotient (M.map (QuotientGroup.mk' N))
  exact ⟨H, K, hK, ⟨(QuotientGroup.quotientQuotientEquivQuotient N M h).symm.trans e⟩⟩

private theorem burnside_isProperSectionOf_subgroup {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hH : H ≠ ⊤) : IsProperSectionOf ↥H G := by
  refine ⟨⟨H, ⊥, inferInstance, ⟨?_⟩⟩, ?_⟩
  · exact (QuotientGroup.quotientBot (G := ↥H)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf H).symm)
  · exact lt_of_le_of_ne (Subgroup.card_le_card_group H) fun h =>
      hH ((Subgroup.card_eq_iff_eq_top H).mp h)

private theorem burnside_card_quotient_lt {G : Type*} [Group G] [Finite G] (U : Subgroup G)
    [U.Normal]
    (hU : U ≠ ⊥) : Nat.card (G ⧸ U) < Nat.card G := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup U
  have h1 : 1 < Nat.card U := (Subgroup.one_lt_card_iff_ne_bot U).mpr hU
  have h2 : 0 < Nat.card (G ⧸ U) := Nat.card_pos
  rw [h]
  exact lt_mul_of_one_lt_right h2 h1

private theorem burnside_card_section_le {X : Type*} [Group X] [Finite X] {S : Type*} [Group S]
    (h : IsSectionOf S X) : Nat.card S ≤ Nat.card X := by
  obtain ⟨H, K, hK, ⟨e⟩⟩ := h
  calc Nat.card S = Nat.card (↥H ⧸ K.subgroupOf H) := Nat.card_congr e.toEquiv
    _ ≤ Nat.card ↥H :=
        Nat.card_le_card_of_surjective (QuotientGroup.mk' (K.subgroupOf H))
          (QuotientGroup.mk'_surjective _)
    _ ≤ Nat.card X := Subgroup.card_le_card_group H

private theorem burnside_isSectionOf_subgroup {G : Type} [Group G] (M : Subgroup G) {S : Type*}
    [Group S]
    (h : IsSectionOf S ↥M) : IsSectionOf S G := by
  obtain ⟨H, K, hK, ⟨e⟩⟩ := h
  have hf : Function.Injective M.subtype := M.subtype_injective
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥H ≃* ↥(H.map M.subtype), ∀ y : ↥H, ((φ y : ↥(H.map M.subtype)) : G) =
      (((y : ↥M)) : G) := ⟨H.equivMapOfInjective M.subtype hf, fun y => rfl⟩
  have hmap : (K.subgroupOf H).map φ.toMonoidHom =
      (K.map M.subtype).subgroupOf (H.map M.subtype) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      refine ⟨(y : ↥M), hy, ?_⟩
      exact (hφ y).symm
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨k, hk, hkx⟩ := hx
      refine ⟨φ.symm x, ?_, by simp⟩
      have h1 : M.subtype ((φ.symm x : ↥H) : ↥M) = (x : G) := by
        have := hφ (φ.symm x)
        rw [φ.apply_symm_apply] at this
        exact this.symm
      have h2 : ((φ.symm x : ↥H) : ↥M) = k := hf (h1.trans hkx.symm)
      show ((φ.symm x : ↥H) : ↥M) ∈ K
      rw [h2]
      exact hk
  have hn : ((K.map M.subtype).subgroupOf (H.map M.subtype)).Normal := by
    rw [← hmap]
    exact hK.map _ φ.surjective
  exact ⟨H.map M.subtype, K.map M.subtype, hn,
    ⟨e.trans (QuotientGroup.congr (K.subgroupOf H) _ φ hmap)⟩⟩

private theorem burnside_layer_map_le {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) : (genFittingLayer G).map f ≤ genFittingLayer H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro component hcomponent
  apply Subgroup.map_le_iff_le_comap.mp
  by_cases hkilled : component ≤ f.ker
  · rw [component.map_eq_bot_iff.mpr hkilled]
    exact bot_le
  · exact CFSG.ComponentClassification.Layer.component_le
      (CFSG.ComponentClassification.LocalComponents.image hcomponent f hf hkilled)

private theorem burnside_genFittingLayer_top_of_surjective {G H : Type*} [Group G] [Group H]
    (hG : genFittingLayer G = ⊤) (f : G →* H) (hf : Function.Surjective f) :
    genFittingLayer H = ⊤ := by
  have h := burnside_layer_map_le f hf
  rw [hG, Subgroup.map_top_of_surjective f hf] at h
  exact top_le_iff.mp h

private theorem burnside_quotCenter_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nonempty ((A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B)) :=
  ⟨QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (Subgroup.map_center_eq e)⟩

private theorem burnside_centerOf_map {G : Type} [Group G] (M : Subgroup G) (X : Subgroup ↥M) :
    centerOf (X.map M.subtype) = (centerOf X).map M.subtype := by
  ext z
  simp only [centerOf, centralizerOf, Subgroup.mem_inf, Subgroup.mem_map,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, fun y hy => ?_⟩, rfl⟩
    have := hc (y : G) ⟨y, hy, rfl⟩
    exact Subtype.ext this
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hc y hy)

private theorem burnside_isComponentOf_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) {L K : Subgroup X} (h : IsComponentOf L K) :
    IsComponentOf (L.map f) (K.map f) :=
  ⟨Subgroup.map_mono h.1, h.2.1.map f,
    CFSG.Open.IsQuasisimple.of_mulEquiv (L.equivMapOfInjective f hf).symm h.2.2⟩

private theorem burnside_clauseB_transport {G : Type} [Group G] [Finite G] (M : Subgroup G)
    {S : Type} [Group S] [Finite S]
    (h : ∃ (H H₁ H₂ : Subgroup ↥M) (n₁ n₂ : ℕ),
      Nonempty (S ≃* ↥H ⧸ Subgroup.center ↥H) ∧ pRank 3 H = 3 ∧ H = H₁ ⊔ H₂ ∧
      IsComponentOf H₁ H ∧ IsComponentOf H₂ H ∧ IsSUn 3 (2 ^ n₁) ↥H₁ ∧ IsSUn 3 (2 ^ n₂) ↥H₂ ∧
      3 ≤ n₁ ∧ Odd n₁ ∧ 3 ≤ n₂ ∧ Odd n₂ ∧ centerOf H₁ = centerOf H₂ ∧
      (Nat.gcd n₁ n₂ = 1 ∨ Nat.gcd n₁ n₂ = 3)) :
    ∃ (H H₁ H₂ : Subgroup G) (n₁ n₂ : ℕ),
      Nonempty (S ≃* ↥H ⧸ Subgroup.center ↥H) ∧ pRank 3 H = 3 ∧ H = H₁ ⊔ H₂ ∧
      IsComponentOf H₁ H ∧ IsComponentOf H₂ H ∧ IsSUn 3 (2 ^ n₁) ↥H₁ ∧ IsSUn 3 (2 ^ n₂) ↥H₂ ∧
      3 ≤ n₁ ∧ Odd n₁ ∧ 3 ≤ n₂ ∧ Odd n₂ ∧ centerOf H₁ = centerOf H₂ ∧
      (Nat.gcd n₁ n₂ = 1 ∨ Nat.gcd n₁ n₂ = 3) := by
  obtain ⟨H, H₁, H₂, n₁, n₂, ⟨e⟩, hr, hsup, hc1, hc2, hs1, hs2, h31, ho1, h32, ho2, hcen, hg⟩ := h
  have hf : Function.Injective M.subtype := M.subtype_injective
  refine ⟨H.map M.subtype, H₁.map M.subtype, H₂.map M.subtype, n₁, n₂, ?_, ?_, ?_,
    burnside_isComponentOf_map M.subtype hf hc1, burnside_isComponentOf_map M.subtype hf hc2,
    ?_, ?_, h31, ho1, h32, ho2, ?_, hg⟩
  · obtain ⟨c⟩ := burnside_quotCenter_equiv (H.equivMapOfInjective M.subtype hf)
    exact ⟨e.trans c⟩
  · exact (CFSG.pRank_congr_of_mulEquiv (H.equivMapOfInjective M.subtype hf).symm 3).trans hr
  · rw [hsup, Subgroup.map_sup]
  · obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := hs1
    exact ⟨K, hK, hKf, hcard, ⟨(H₁.equivMapOfInjective M.subtype hf).symm.trans e'⟩⟩
  · obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := hs2
    exact ⟨K, hK, hKf, hcard, ⟨(H₂.equivMapOfInjective M.subtype hf).symm.trans e'⟩⟩
  · rw [burnside_centerOf_map, burnside_centerOf_map, hcen]

private theorem burnside_theoremAConclusion_of_subgroup {G : Type} [Group G] [Finite G] (H :
    Subgroup G)
    {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hev : evenRank G ≤ 2)
    (h : TheoremAConclusion ↥H S p) : TheoremAConclusion G S p := by
  unfold TheoremAConclusion at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun hG => ?_⟩
  · rcases h1 with ⟨ha, hb⟩ | ⟨hp3, hB⟩
    · exact Or.inl ⟨ha.trans (burnside_twoLocalPrimeRank_le_of_injective hp H.subtype
        H.subtype_injective), (burnside_twoLocalPrimeRank_le_evenRank hp hp2).trans hev⟩
    · exact Or.inr ⟨hp3, burnside_clauseB_transport H hB⟩
  · have hH : CFSG.pRank p ↥H ≤ CFSG.pRank p G :=
      burnside_pRank_le_of_injective hp.one_lt H.subtype H.subtype_injective
    simp only [burnside_pRank_top_eq] at h2 hG ⊢
    exact (h2 (hH.trans hG)).trans hH

private theorem burnside_theoremAConclusion_of_injective {G : Type} [Group G] [Finite G] {S : Type}
    [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hev : evenRank G ≤ 2)
    (f : S →* G) (hf : Function.Injective f) : TheoremAConclusion G S p := by
  unfold TheoremAConclusion
  refine ⟨Or.inl ⟨burnside_twoLocalPrimeRank_le_of_injective hp f hf,
    (burnside_twoLocalPrimeRank_le_evenRank hp hp2).trans hev⟩, fun _ => ?_⟩
  simp only [burnside_pRank_top_eq]
  exact burnside_pRank_le_of_injective hp.one_lt f hf

private theorem burnside_theoremAConclusion_of_mulEquiv {G : Type} [Group G] [Finite G] {S S' :
    Type}
    [Group S] [Group S'] [Finite S] [Finite S'] {p : ℕ} (hp : p.Prime) (e : S ≃* S')
    (h : TheoremAConclusion G S' p) : TheoremAConclusion G S p := by
  unfold TheoremAConclusion at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun hG => ?_⟩
  · rcases h1 with ⟨ha, hb⟩ | ⟨hp3, B⟩
    · exact Or.inl ⟨(burnside_twoLocalPrimeRank_le_of_injective hp e.toMonoidHom e.injective).trans
        ha, hb⟩
    · refine Or.inr ⟨hp3, ?_⟩
      obtain ⟨H, H₁, H₂, n₁, n₂, ⟨e'⟩, rest⟩ := B
      exact ⟨H, H₁, H₂, n₁, n₂, ⟨e.trans e'⟩, rest⟩
  · have hS : CFSG.pRank p S = CFSG.pRank p S' := CFSG.pRank_congr_of_mulEquiv e p
    simp only [burnside_pRank_top_eq] at h2 hG ⊢
    rw [hS]
    exact h2 hG

private theorem burnside_a28_cover {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S]
    {p : ℕ} (hmin : IsMinimalCounterexampleToA G S p) (H : Subgroup G)
    (hH : IsSectionOf S ↥H) : H = ⊤ := by
  obtain ⟨hev, hK, -, hss, hp, hp2, hnc, hprop⟩ := hmin
  by_contra hne
  have hA : TheoremAHolds ↥H := hprop ↥H (burnside_isProperSectionOf_subgroup H hne)
  have hevH : evenRank ↥H ≤ 2 :=
    (burnside_evenRank_le_of_injective H.subtype H.subtype_injective).trans hev
  have hKH : CFSG.SectionRank.IsKGroupCat ↥H := hK.subgroup H
  exact hnc (burnside_theoremAConclusion_of_subgroup H hp hp2 hev
    ((hA hevH hKH S hH hss).1 p hp hp2))

private theorem burnside_a28_quotient {G : Type} [Group G] [Finite G] {S : Type} [Group S]
    [Finite S]
    {p : ℕ} (hmin : IsMinimalCounterexampleToA G S p) :
    ∃ (K : Subgroup G) (_ : K.Normal), Nonempty (S ≃* G ⧸ K) := by
  obtain ⟨H, K, hKn, ⟨e⟩⟩ := hmin.2.2.1
  have hS : IsSectionOf S ↥H := by
    obtain ⟨H', K', hK', ⟨e'⟩⟩ := burnside_isSectionOf_quotient (K.subgroupOf H)
    exact ⟨H', K', hK', ⟨e.trans e'⟩⟩
  have hH : H = ⊤ := burnside_a28_cover hmin H hS
  subst hH
  have hKnorm : K.Normal := by
    refine ⟨fun k hk g => ?_⟩
    have := hKn.conj_mem ⟨k, trivial⟩ (by simpa [Subgroup.mem_subgroupOf] using hk) ⟨g, trivial⟩
    simpa [Subgroup.mem_subgroupOf] using this
  refine ⟨K, hKnorm, ⟨e.trans (QuotientGroup.congr (K.subgroupOf ⊤) K Subgroup.topEquiv ?_)⟩⟩
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, trivial⟩, hx, rfl⟩


private theorem burnside_pRank_quotient_sup_two {G : Type} [Group G] [Finite G] (K U : Subgroup G)
    [K.Normal] [U.Normal] (hU2 : IsPGroup 2 U) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.pRank p (G ⧸ K) = CFSG.pRank p (G ⧸ (K ⊔ U)) := by
  have e := QuotientGroup.quotientQuotientEquivQuotient K (K ⊔ U) le_sup_left
  have hmap : (K ⊔ U).map (QuotientGroup.mk' K) = U.map (QuotientGroup.mk' K) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hN : IsPGroup 2 ((K ⊔ U).map (QuotientGroup.mk' K)) := by
    rw [hmap]
    exact hU2.of_surjective ((QuotientGroup.mk' K).subgroupMap U)
      ((QuotientGroup.mk' K).subgroupMap_surjective U)
  have hN' := burnside_pRank_quotient_two _ hN hp hp2
  rw [← CFSG.pRank_congr_of_mulEquiv e p]
  exact hN'.symm


private theorem burnside_card_le_three_pow_of_injective {G α K : Type*} [Finite G] [Fintype α]
    [Field K]
    (φ : G → α → K) (hφ : Function.Injective φ) (h3 : ∀ g a, φ g a ^ 3 = 1) :
    Nat.card G ≤ 3 ^ Fintype.card α := by
  classical
  set S : Finset K := (Polynomial.nthRoots 3 (1 : K)).toFinset
  have hS : S.card ≤ 3 := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)
  let ψ : G → (α → S) := fun g a =>
    ⟨φ g a, by rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]; exact h3 g a⟩
  have hψ : Function.Injective ψ := fun g g' h =>
    hφ (funext fun a => congrArg Subtype.val (congrFun h a))
  calc Nat.card G ≤ Nat.card (α → S) := Nat.card_le_card_of_injective ψ hψ
    _ = S.card ^ Fintype.card α := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe]
    _ ≤ 3 ^ Fintype.card α := Nat.pow_le_pow_left hS _

open Polynomial Module Matrix in
private theorem burnside_exists_common_eigenbasis_pow_three {K : Type*} [Field K] [IsAlgClosed K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (h3 : (3 : K) ≠ 0) (E : Subgroup (GL ι K))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1) :
    ∃ (b : Module.Basis ι K (ι → K)) (d : GL ι K → ι → K),
      ∀ x ∈ E, ∀ a, (x : Matrix ι ι K) *ᵥ b a = d x a • b a := by
  classical
  set f : E → Module.End K (ι → K) :=
    fun x => Matrix.toLinAlgEquiv' ((x : GL ι K) : Matrix ι ι K) with hfdef
  have hfcomm : ∀ i j, Commute (f i) (f j) := fun i j => by
    change Matrix.toLinAlgEquiv' _ * Matrix.toLinAlgEquiv' _ =
      Matrix.toLinAlgEquiv' _ * Matrix.toLinAlgEquiv' _
    rw [← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, hcomm _ i.2 _ j.2]
  have hf3 : ∀ i, f i ^ 3 = 1 := fun i => by
    change (Matrix.toLinAlgEquiv' _) ^ 3 = 1
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hexp _ i.2, Units.val_one, map_one]
  have hsep : (X ^ 3 - C (1 : K)).Separable :=
    separable_X_pow_sub_C 1 (by exact_mod_cast h3) one_ne_zero
  have hss : ∀ i, (f i).IsSemisimple := fun i =>
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hf3 i])
  set W : (E → K) → Submodule K (ι → K) := fun χ => ⨅ i, (f i).maxGenEigenspace (χ i) with hW
  have hind : iSupIndep W :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hfcomm j i) φ)
  have htop : ⨆ χ, W χ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      (fun i j _ => hfcomm i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  set b₀ := hint.collectedBasis (fun χ => Module.finBasis K (W χ))
  let e := b₀.indexEquiv (Pi.basisFun K ι)
  refine ⟨b₀.reindex e, fun x a => if hx : x ∈ E then (e.symm a).1 ⟨x, hx⟩ else 0, ?_⟩
  intro x hx a
  have hmem : b₀.reindex e a ∈ W (e.symm a).1 := by
    rw [Module.Basis.reindex_apply]
    exact hint.collectedBasis_mem _ _
  have h1 : b₀.reindex e a ∈ (f ⟨x, hx⟩).maxGenEigenspace ((e.symm a).1 ⟨x, hx⟩) :=
    (Submodule.mem_iInf _).mp hmem ⟨x, hx⟩
  rw [(hss ⟨x, hx⟩).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
    Module.End.mem_eigenspace_iff] at h1
  simp only [hx, ↓reduceDIte]
  rw [← h1]
  rfl

open Module Matrix in
private theorem burnside_card_le_of_det_eq_one_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (h3 : (3 : K) ≠ 0) (a₀ : ι)
    (E : Subgroup (GL ι K)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hdet : ∀ x ∈ E, (x : Matrix ι ι K).det = 1) [Finite E] :
    Nat.card E ≤ 3 ^ (Fintype.card ι - 1) := by
  classical
  obtain ⟨b, d, hb⟩ := burnside_exists_common_eigenbasis_pow_three h3 E hcomm hexp
  have eigen_mul : ∀ {x y : GL ι K}, x ∈ E → y ∈ E → ∀ a, d (x * y) a = d x a * d y a := by
    intro x y hx hy a
    have h1 := hb (x * y) (E.mul_mem hx hy) a
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb y hy a, Matrix.mulVec_smul, hb x hx a,
      smul_smul] at h1
    rw [mul_comm]
    exact (smul_left_injective K (b.ne_zero a) h1).symm
  have eigen_one : ∀ a, d 1 a = 1 := by
    intro a
    have h0 := hb 1 E.one_mem a
    rw [Units.val_one, Matrix.one_mulVec] at h0
    exact smul_left_injective K (b.ne_zero a) (show d 1 a • b a = (1 : K) • b a by
      rw [← h0, one_smul])
  have eigen_pow_three : ∀ {x : GL ι K}, x ∈ E → x ^ 3 = 1 → ∀ a, d x a ^ 3 = 1 := by
    intro x hx hx3 a
    have h := eigen_mul (E.mul_mem hx hx) hx a
    have h1 := eigen_mul hx hx a
    have hx3' : x * x * x = 1 := by rw [mul_assoc, ← pow_three, hx3]
    rw [hx3', eigen_one a, h1] at h
    rw [h]
    ring
  have eigen_ext : ∀ {x y : GL ι K}, x ∈ E → y ∈ E → (∀ a, d x a = d y a) → x = y := by
    intro x y hx hy h
    apply Units.ext
    apply Matrix.toLin'.injective
    apply b.ext
    intro a
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hb x hx a, hb y hy a, h a]
  have eigen_det : ∀ {x : GL ι K}, x ∈ E → (x : Matrix ι ι K).det = ∏ a, d x a := by
    intro x hx
    rw [← LinearMap.det_toLin', ← LinearMap.det_toMatrix b,
      show LinearMap.toMatrix b b (Matrix.toLin' (x : Matrix ι ι K)) =
        Matrix.diagonal (d x) from ?_, Matrix.det_diagonal]
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hb x hx j, map_smul, b.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have h := burnside_card_le_three_pow_of_injective (α := {a : ι // a ≠ a₀})
    (fun (x : E) a => d x a)
    (fun x y hxy => by
      have hxy' : ∀ a, a ≠ a₀ → d x a = d y a := fun a ha => congrFun hxy ⟨a, ha⟩
      apply Subtype.ext
      refine eigen_ext x.2 y.2 fun a => ?_
      by_cases ha : a = a₀
      · subst ha
        have hx := (eigen_det x.2).symm.trans (hdet x x.2)
        have hy := (eigen_det y.2).symm.trans (hdet y y.2)
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)] at hx hy
        have hp : ∏ c ∈ Finset.univ.erase a, d x c = ∏ c ∈ Finset.univ.erase a, d y c :=
          Finset.prod_congr rfl fun c hc => hxy' c (Finset.ne_of_mem_erase hc)
        rw [hp] at hx
        have hne : ∏ c ∈ Finset.univ.erase a, d y c ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hy
          exact zero_ne_one hy
        exact mul_right_cancel₀ hne (hx.trans hy.symm)
      · exact hxy' a ha)
    (fun x a => eigen_pow_three x.2 (hexp x x.2) a)
  rwa [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h

private theorem burnside_card_le_of_det_eq_one {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (h3 : (3 : K) ≠ 0) (a₀ : ι) (E : Subgroup (GL ι K)) [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hdet : ∀ x ∈ E, (x : Matrix ι ι K).det = 1) :
    Nat.card E ≤ 3 ^ (Fintype.card ι - 1) := by
  set L := AlgebraicClosure K
  set Φ := Matrix.GeneralLinearGroup.map (n := ι) (algebraMap K L)
  have hΦ : Function.Injective Φ := fun _ _ h =>
    Units.ext (Matrix.map_injective (algebraMap K L).injective (congrArg Units.val h))
  have h3' : (3 : L) ≠ 0 := by
    intro h
    apply h3
    apply (algebraMap K L).injective
    rw [map_ofNat, h, map_zero]
  have : Finite (E.map Φ) := Finite.of_surjective _ (Φ.subgroupMap_surjective E)
  have h := burnside_card_le_of_det_eq_one_of_isAlgClosed h3' a₀ (E.map Φ)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one])
    (by
      rintro _ ⟨x, hx, rfl⟩
      change ((x : Matrix ι ι K).map (algebraMap K L)).det = 1
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet x hx, map_one])
  rwa [Subgroup.card_map_of_injective hΦ] at h

private theorem burnside_three_ne_zero_of_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (hcard : Nat.card K = (2 ^ n) ^ 2) : (3 : K) ≠ 0 := by
  intro h
  have : Fintype K := Fintype.ofFinite K
  have h3 : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
  haveI : CharP K 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr h3
  obtain ⟨m, -, hm⟩ := FiniteField.card K 3
  rw [← Nat.card_eq_fintype_card, hcard] at hm
  have h3d : 3 ∣ (2 ^ n) ^ 2 := by
    rw [hm]
    exact dvd_pow_self 3 m.pos.ne'
  have := Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow h3d)
  omega

private theorem burnside_pRank_three_le_two_of_isSUn {n : ℕ} {X : Type} [Group X] [Finite X]
    (h : IsSUn 3 (2 ^ n) X) : CFSG.pRank 3 X ≤ 2 := by
  obtain ⟨K, hK, hKf, hcard, ⟨e⟩⟩ := h
  have h3K : (3 : K) ≠ 0 := burnside_three_ne_zero_of_card hcard
  rw [CFSG.pRank_congr_of_mulEquiv e 3]
  refine csSup_le' ?_
  rintro r ⟨B, hB, hr⟩
  obtain ⟨hBc, hBe⟩ := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 B).mp hB
  set E : Subgroup (GL (Fin 3) K) := B.map (StatedSU 3 (2 ^ n) K).subtype with hEdef
  have hfin : Finite E := inferInstance
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩))
  have hexp : ∀ x ∈ E, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hBe x hx, map_one]
  have hdet : ∀ x ∈ E, (x : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rintro _ ⟨x, -, rfl⟩
    exact CFSG.Open.StatedAPI.det_of_mem_statedSU x.2
  have hbound := burnside_card_le_of_det_eq_one h3K (0 : Fin 3) E hcomm hexp
    hdet
  rw [Fintype.card_fin, hEdef,
    Subgroup.card_map_of_injective (StatedSU 3 (2 ^ n) K).subtype_injective, hr] at hbound
  have h32 : 3 ^ r ≤ 3 ^ 2 := by simpa using hbound
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h32

private theorem burnside_not_commutative_of_quasisimple {L : Type*} [Group L]
    (h : CFSG.Open.IsQuasisimple L) : ¬ ∀ a b : L, a * b = b * a := by
  intro hc
  have hz : Subgroup.center L = ⊤ :=
    (Subgroup.eq_top_iff' _).mpr fun a => Subgroup.mem_center_iff.mpr fun b => hc b a
  obtain ⟨-, hs⟩ := h
  haveI : Subsingleton (L ⧸ Subgroup.center L) := by
    rw [hz]
    exact QuotientGroup.subsingleton_quotient_top
  exact (not_subsingleton (L ⧸ Subgroup.center L)) inferInstance

private theorem burnside_isComponentOf_subgroupOf {X : Type*} [Group X] {H L : Subgroup X}
    (h : IsComponentOf L H) : IsComponentOf (L.subgroupOf H) ⊤ :=
  ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib h.2.1.subgroupOf,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.2⟩

private theorem burnside_false_of_clauseB_simple {X : Type} [Group X] [Finite X] {R : Type}
    [Group R]
    [IsSimpleGroup R] (hnab : ∃ a b : R, a * b ≠ b * a) {H H₁ H₂ : Subgroup X} {n₁ : ℕ}
    (e : R ≃* ↥H ⧸ Subgroup.center ↥H) (hr : CFSG.pRank 3 ↥H = 3) (hsup : H = H₁ ⊔ H₂)
    (hc₁ : IsComponentOf H₁ H) (hc₂ : IsComponentOf H₂ H) (hs₁ : IsSUn 3 (2 ^ n₁) ↥H₁) :
    False := by
  by_cases hne : H₁ = H₂
  · subst hne
    rw [sup_idem] at hsup
    subst hsup
    have := burnside_pRank_three_le_two_of_isSUn hs₁
    omega
  · have hle₁ : H₁ ≤ H := hc₁.1
    have hle₂ : H₂ ≤ H := hc₂.1
    have hA₁ := burnside_isComponentOf_subgroupOf hc₁
    have hA₂ := burnside_isComponentOf_subgroupOf hc₂
    have hne' : H₁.subgroupOf H ≠ H₂.subgroupOf H := by
      intro h
      apply hne
      have := Subgroup.subgroupOf_inj.mp h
      rwa [inf_of_le_left hle₁, inf_of_le_left hle₂] at this
    have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hA₁ hA₂ hne'
    have hsupA : H₁.subgroupOf H ⊔ H₂.subgroupOf H = ⊤ := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_of_le_left hle₁, inf_of_le_left hle₂, ← hsup, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    set π := QuotientGroup.mk' (Subgroup.center ↥H) with hπ
    set B₁ : Subgroup (↥H ⧸ Subgroup.center ↥H) := (H₁.subgroupOf H).map π with hB₁
    set B₂ : Subgroup (↥H ⧸ Subgroup.center ↥H) := (H₂.subgroupOf H).map π with hB₂
    have hBsup : B₁ ⊔ B₂ = ⊤ := by
      rw [hB₁, hB₂, ← Subgroup.map_sup, hsupA,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have hle : H₁.subgroupOf H ≤ Subgroup.centralizer ((H₂.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hBc : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hba : b * a = a * b := Subgroup.mem_centralizer_iff.mp (hle ha) b hb
      rw [← map_mul, ← map_mul, hba]
    haveI hQs : IsSimpleGroup (↥H ⧸ Subgroup.center ↥H) := e.symm.isSimpleGroup
    have hnormB : ∀ (B C : Subgroup (↥H ⧸ Subgroup.center ↥H)), B ⊔ C = ⊤ →
        (∀ x ∈ B, ∀ y ∈ C, x * y = y * x) → B.Normal := by
      intro B C hBC hc
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hBC]
      refine sup_le Subgroup.le_normalizer fun y hy => Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hc h hh y hy
    haveI hB₁n : B₁.Normal := hnormB B₁ B₂ hBsup hBc
    haveI hB₂n : B₂.Normal :=
      hnormB B₂ B₁ (by rw [sup_comm]; exact hBsup) (fun x hx y hy => (hBc y hy x hx).symm)
    have hnotbot : ∀ {L : Subgroup X}, IsComponentOf L H → ¬ ((L.subgroupOf H).map π = ⊥) := by
      intro L hL hbot
      rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
      refine burnside_not_commutative_of_quasisimple hL.2.2 fun a b => ?_
      have ha : (⟨(a : X), hL.1 a.2⟩ : ↥H) ∈ Subgroup.center ↥H := hbot a.2
      have h1 := Subgroup.mem_center_iff.mp ha ⟨(b : X), hL.1 b.2⟩
      exact Subtype.ext (congrArg (fun z : ↥H => (z : X)) h1.symm)
    have hB₁top : B₁ = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal B₁).resolve_left (hnotbot hc₁)
    have hB₂top : B₂ = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal B₂).resolve_left (hnotbot hc₂)
    have hQc : ∀ a b : ↥H ⧸ Subgroup.center ↥H, a * b = b * a := fun a b =>
      hBc a (by rw [hB₁top]; exact Subgroup.mem_top a) b (by rw [hB₂top]; exact Subgroup.mem_top b)
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact hQc _ _


private theorem burnside_a213_structure {G : Type} [Group G] [Finite G] {S : Type} [Group S]
    [Finite S]
    {p : ℕ}
    (h11 : ∀ (G : Type) [Group G] [Finite G] (S : Type) [Group S] [Finite S] (p : ℕ),
      IsMinimalCounterexampleToA G S p →
      Nonempty ((G ⧸ pCore p G) ≃* (S ⧸ Subgroup.center S)))
    (hq : IsQuasisimple G) (hmin : IsMinimalCounterexampleToA G S p) :
    ∃ (K : Subgroup G) (_ : K.Normal), Nonempty (S ≃* G ⧸ K) ∧ K ≠ ⊥ ∧ K ≠ ⊤ ∧
      K ≤ Subgroup.center G ∧ IsPGroup p (Subgroup.center G) := by
  obtain ⟨K, hKn, ⟨e⟩⟩ := burnside_a28_quotient hmin
  have hmin2 := hmin
  obtain ⟨hev, -, -, -, hp, hp2, hnc, -⟩ := hmin2
  have hq2 := hq
  obtain ⟨-, hsimple, -⟩ := hq2
  have hK1 : K ≠ ⊥ := by
    intro hK
    subst hK
    refine hnc (burnside_theoremAConclusion_of_injective hp hp2 hev
      ((QuotientGroup.quotientBot (G := G)).toMonoidHom.comp e.toMonoidHom) ?_)
    exact (QuotientGroup.quotientBot (G := G)).injective.comp e.injective
  have hKtop : K ≠ ⊤ := by
    intro hK
    subst hK
    haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
    refine hnc (burnside_theoremAConclusion_of_injective hp hp2 hev (1 : S →* G) ?_)
    intro a b _
    exact e.injective (Subsingleton.elim _ _)
  have hKz : K ≤ Subgroup.center G :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hq hKn).resolve_left hKtop
  obtain ⟨f⟩ := h11 G S p hmin
  obtain ⟨-, -, hZK⟩ := CFSG.LocalCores.quasisimple_central_quotient hq K hKz
  have e1 : (S ⧸ Subgroup.center S) ≃* ((G ⧸ K) ⧸ Subgroup.center (G ⧸ K)) :=
    QuotientGroup.congr (Subgroup.center S) (Subgroup.center (G ⧸ K)) e (Subgroup.map_center_eq e)
  have e2 : ((G ⧸ K) ⧸ Subgroup.center (G ⧸ K)) ≃* G ⧸ Subgroup.center G :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans
      (QuotientGroup.quotientQuotientEquivQuotient K (Subgroup.center G) hKz)
  have hcard : Nat.card (G ⧸ pCore p G) = Nat.card (G ⧸ Subgroup.center G) :=
    Nat.card_congr (f.toEquiv.trans (e1.trans e2).toEquiv)
  have hO : pCore p G ≤ Subgroup.center G := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (CFSG.pCore_normal (p := p) (G := G)) with h | h
    · exfalso
      have h1 : Nat.card (G ⧸ pCore p G) = 1 := Subgroup.index_eq_one.mpr h
      rw [h1] at hcard
      obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp hcard.symm
      exact (not_subsingleton (G ⧸ Subgroup.center G)) hsub
    · exact h
  have hO' : pCore p G = Subgroup.center G := by
    refine Subgroup.eq_of_le_of_card_ge hO ?_
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore p G)
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
    rw [hcard] at h1
    have hpos : 0 < Nat.card (G ⧸ Subgroup.center G) := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)).ge
  refine ⟨K, hKn, ⟨e⟩, hK1, hKtop, hKz, ?_⟩
  rw [← hO']
  exact CFSG.pCore_isPGroup

private theorem burnside_a213_of_a211_a212
    (h11 : ∀ (G : Type) [Group G] [Finite G] (S : Type) [Group S] [Finite S] (p : ℕ),
      IsMinimalCounterexampleToA G S p →
      Nonempty ((G ⧸ pCore p G) ≃* (S ⧸ Subgroup.center S)))
    (h12 : ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G → ¬ TheoremAHolds G →
      IsQuasisimple G) :
    ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    (IsSimpleGroup G ∧ (¬ TheoremBHolds G ∨ ¬ TheoremCHolds G)) ∨
    (IsQuasisimple G ∧ ¬ IsSimpleGroup G ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      IsPGroup p (Subgroup.center G) ∧
      ∃ (Z : Subgroup G) (_ : Z.Normal), Z ≠ ⊥ ∧ Z ≤ Subgroup.center G ∧
        evenRank G ≤ 2 ∧ CFSG.SectionRank.IsKGroupCat G ∧ IsSectionOf (G ⧸ Z) G ∧
        genFittingLayer (G ⧸ Z) = ⊤ ∧ ¬ TheoremAConclusion G (G ⧸ Z) p ∧
        ∀ (q : ℕ), q.Prime → q ≠ 2 →
          ∀ (S : Type) [Group S] [Finite S], IsSectionOf S G → genFittingLayer S = ⊤ →
            ¬ TheoremAConclusion G S q → q = p) := by
  intro G _ _ hmin
  by_cases hB : TheoremBHolds G
  swap
  · left
    refine ⟨?_, Or.inl hB⟩
    by_contra hns
    exact hB fun hs => absurd hs hns
  by_cases hC : TheoremCHolds G
  swap
  · left
    refine ⟨?_, Or.inr hC⟩
    by_contra hns
    exact hC fun hs => absurd hs hns
  right
  have hA : ¬ TheoremAHolds G := by
    rcases hmin.1 with h | h | h
    · exact h
    · exact absurd hB h
    · exact absurd hC h
  have hev : evenRank G ≤ 2 := by
    by_contra h
    exact hA fun h' => absurd h' h
  have hKG : CFSG.SectionRank.IsKGroupCat G := by
    by_contra h
    exact hA fun _ h' => absurd h' h
  obtain ⟨S, _, _, hSsec, hSss, hnot⟩ : ∃ (S : Type) (_ : Group S) (_ : Finite S),
      IsSectionOf S G ∧ genFittingLayer S = ⊤ ∧
      ¬ ((∀ p : ℕ, p.Prime → p ≠ 2 → TheoremAConclusion G S p) ∧
        (CFSG.IsStronglyQuasithin G → CFSG.IsStronglyQuasithin S)) := by
    by_contra hcon
    push Not at hcon
    refine hA ?_
    intro _ _ S _ _ hs hss
    exact hcon S _ _ hs hss
  obtain ⟨p, hp, hp2, hnp⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ TheoremAConclusion G S p := by
    by_contra hcon
    push Not at hcon
    refine hnot ⟨fun p hp hp2 => hcon p hp hp2, fun hsqt q hq hq2 => ?_⟩
    have hc := hcon q hq hq2
    unfold TheoremAConclusion at hc
    have h2 := hc.2
    simp only [burnside_pRank_top_eq] at h2
    have h3 := hsqt q hq hq2
    exact (h2 h3).trans h3
  have hmin' : IsMinimalCounterexampleToA G S p :=
    ⟨hev, hKG, hSsec, hSss, hp, hp2, hnp, fun X _ _ hX => (hmin.2 X hX).1⟩
  have hqs : IsQuasisimple G := h12 G hmin hA
  obtain ⟨K, hKn, ⟨e⟩, hK1, hKtop, hKz, hpz⟩ := burnside_a213_structure h11 hqs hmin'
  refine ⟨hqs, ?_, p, hp, hp2, hpz, K, hKn, hK1, hKz, hev, hKG,
    burnside_isSectionOf_quotient K, ?_, ?_, ?_⟩
  · intro hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
    · exact hK1 h
    · exact hKtop h
  · exact burnside_genFittingLayer_top_of_surjective hSss e.toMonoidHom e.surjective
  · intro hconc
    exact hnp (burnside_theoremAConclusion_of_mulEquiv hp e hconc)
  · intro q hq hq2 S' _ _ hS'sec hS'ss hnq
    have hmin'' : IsMinimalCounterexampleToA G S' q :=
      ⟨hev, hKG, hS'sec, hS'ss, hq, hq2, hnq, fun X _ _ hX => (hmin.2 X hX).1⟩
    obtain ⟨-, -, -, -, -, -, hqz⟩ := burnside_a213_structure h11 hqs hmin''
    obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK1
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fact q.Prime := ⟨hq⟩
    have hgz : (g : G) ∈ Subgroup.center G := hKz g.2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hpz) ⟨g, hgz⟩
    obtain ⟨l, hl⟩ := (IsPGroup.iff_orderOf.mp hqz) ⟨g, hgz⟩
    have hne1 : orderOf (⟨g, hgz⟩ : Subgroup.center G) ≠ 1 := by
      intro h
      apply hg1
      have := orderOf_eq_one_iff.mp h
      exact Subtype.ext (congrArg (fun z : Subgroup.center G => (z : G)) this)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne1 (by rw [hk]; simp)
    have hdvd : p ∣ q ^ l := by
      rw [← hl, hk]
      exact dvd_pow_self p hk0
    exact ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)).symm

end BurnsideMA2

theorem as_A_2_8 : A_2_8 := by
  intro G _ _ S _ _ p hmin
  exact ⟨fun H hH => burnside_a28_cover hmin H hH, burnside_a28_quotient hmin⟩

@[expose] def A_2_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Type) [Group S] [Finite S] (p : ℕ),
    IsMinimalCounterexampleToA G S p → pCore 2 G = ⊥

theorem as_A_2_10 : A_2_10 := by
  intro G _ _ S _ _ p hmin
  by_contra hU
  obtain ⟨K, hKn, ⟨e⟩⟩ := burnside_a28_quotient hmin
  obtain ⟨hev, hKg, -, hss, hp, hp2, hnc, hprop⟩ := hmin
  have hU2 : IsPGroup 2 (pCore 2 G) := CFSG.pCore_isPGroup
  have hrk : CFSG.pRank p G ≤ 2 := burnside_pRank_le_two_of_pCore hp hp2 hev hU
  have hproper : IsProperSectionOf (G ⧸ pCore 2 G) G :=
    ⟨burnside_isSectionOf_quotient _, burnside_card_quotient_lt _ hU⟩
  have hA : TheoremAHolds (G ⧸ pCore 2 G) := hprop _ hproper
  have hevQ : evenRank (G ⧸ pCore 2 G) ≤ 2 := burnside_evenRank_quotient_le_two _ hU2 hU hev
  have hKQ : CFSG.SectionRank.IsKGroupCat (G ⧸ pCore 2 G) := hKg.quotient _
  have hTsec : IsSectionOf (G ⧸ (K ⊔ pCore 2 G)) (G ⧸ pCore 2 G) :=
    burnside_isSectionOf_quotient_quotient _ _ le_sup_right
  have hsurj : Function.Surjective
      ((QuotientGroup.map K (K ⊔ pCore 2 G) (MonoidHom.id G) le_sup_left).comp e.toMonoidHom) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨s, hs⟩ := e.surjective (QuotientGroup.mk g)
    refine ⟨s, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hs]
    rfl
  have hTss : genFittingLayer (G ⧸ (K ⊔ pCore 2 G)) = ⊤ :=
    burnside_genFittingLayer_top_of_surjective hss _ hsurj
  have hconc := (hA hevQ hKQ _ hTsec hTss).1 p hp hp2
  unfold TheoremAConclusion at hconc
  obtain ⟨-, h2⟩ := hconc
  have hq1 : CFSG.pRank p (G ⧸ pCore 2 G) = CFSG.pRank p G :=
    burnside_pRank_quotient_two _ hU2 hp hp2
  have hSle : CFSG.pRank p S ≤ CFSG.pRank p G := by
    have h3 : CFSG.pRank p ↥(⊤ : Subgroup (G ⧸ pCore 2 G)) ≤ 2 := by
      rw [burnside_pRank_top_eq, hq1]
      exact hrk
    have h4 := h2 h3
    simp only [burnside_pRank_top_eq] at h4
    rw [hq1] at h4
    calc CFSG.pRank p S = CFSG.pRank p (G ⧸ K) := CFSG.pRank_congr_of_mulEquiv e p
      _ = CFSG.pRank p (G ⧸ (K ⊔ pCore 2 G)) := burnside_pRank_quotient_sup_two K _ hU2 hp hp2
      _ ≤ CFSG.pRank p G := h4
  apply hnc
  unfold TheoremAConclusion
  refine ⟨Or.inl ⟨?_, ?_⟩, fun _ => ?_⟩
  · exact (burnside_twoLocalPrimeRank_le_pRank hp).trans
      (hSle.trans (burnside_pRank_le_twoLocalPrimeRank_of_pCore hp hU))
  · exact (burnside_twoLocalPrimeRank_le_evenRank hp hp2).trans hev
  · simp only [burnside_pRank_top_eq]
    exact hSle

@[expose] def A_2_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Type) [Group S] [Finite S] (p : ℕ),
    IsMinimalCounterexampleToA G S p →
    Nonempty ((G ⧸ pCore p G) ≃* (S ⧸ Subgroup.center S))

section BurnsideTA11

@[expose] def burnsideTA11_Rank2Fact : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    twoRank T = 2 →
    (∀ r : ℕ, r.Prime → r ≠ 2 → twoLocalPrimeRank r T ≤ 2) ∨
    (∃ s f : ℕ, s.Prime ∧ s ≠ 2 ∧ 3 ≤ f ∧
      (StatedClassicalModel T .PSL 3 s f ∨ StatedClassicalModel T .PSU 3 s f) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = s ^ f ∧
        ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* T, Function.Injective φ)

private theorem burnsideTA11_pRank_top_eq {X : Type*} [Group X] [Finite X] (p : ℕ) :
    CFSG.pRank p ↥(⊤ : Subgroup X) = CFSG.pRank p X := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top p ↥(⊤ : Subgroup X),
    CFSG.SectionRank.pRank_eq_open_pRank_top p X,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup X)]

private theorem burnsideTA11_twoLocalPrimeRank_le_evenRank {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : twoLocalPrimeRank p X ≤ evenRank X := by
  refine csSup_le' ?_
  rintro _ ⟨H, hH, rfl⟩
  refine le_csSup ⟨Nat.card X, ?_⟩ ⟨p, H, hp, hp2, hH, rfl⟩
  rintro _ ⟨q, K, hq, -, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt K

private theorem burnsideTA11_isSectionOf_quotient {X : Type} [Group X] (N : Subgroup X) [N.Normal] :
    ChA.IsSectionOf (X ⧸ N) X := by
  refine ⟨⊤, N, inferInstance, ⟨QuotientGroup.congr N (N.subgroupOf ⊤) Subgroup.topEquiv.symm ?_⟩⟩
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨(x : X), hx, rfl⟩

private theorem burnsideTA11_isSectionOf_quotient_quotient {G : Type} [Group G] (N M : Subgroup G)
    [N.Normal] [M.Normal] (h : N ≤ M) : ChA.IsSectionOf (G ⧸ M) (G ⧸ N) := by
  obtain ⟨H, K, hK, ⟨e⟩⟩ := burnsideTA11_isSectionOf_quotient (M.map (QuotientGroup.mk' N))
  exact ⟨H, K, hK, ⟨(QuotientGroup.quotientQuotientEquivQuotient N M h).symm.trans e⟩⟩

private theorem burnsideTA11_card_quotient_lt {G : Type*} [Group G] [Finite G] (U : Subgroup G)
    [U.Normal] (hU : U ≠ ⊥) : Nat.card (G ⧸ U) < Nat.card G := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup U
  have h1 : 1 < Nat.card U := (Subgroup.one_lt_card_iff_ne_bot U).mpr hU
  have h2 : 0 < Nat.card (G ⧸ U) := Nat.card_pos
  rw [h]
  exact lt_mul_of_one_lt_right h2 h1

private theorem burnsideTA11_layer_map_le {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) : (genFittingLayer G).map f ≤ genFittingLayer H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro component hcomponent
  apply Subgroup.map_le_iff_le_comap.mp
  by_cases hkilled : component ≤ f.ker
  · rw [component.map_eq_bot_iff.mpr hkilled]
    exact bot_le
  · exact CFSG.ComponentClassification.Layer.component_le
      (CFSG.ComponentClassification.LocalComponents.image hcomponent f hf hkilled)

private theorem burnsideTA11_genFittingLayer_top_of_surjective {G H : Type*} [Group G] [Group H]
    (hG : genFittingLayer G = ⊤) (f : G →* H) (hf : Function.Surjective f) :
    genFittingLayer H = ⊤ := by
  have h := burnsideTA11_layer_map_le f hf
  rw [hG, Subgroup.map_top_of_surjective f hf] at h
  exact top_le_iff.mp h

section Cfg

variable {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S] {p : ℕ}

structure burnsideTA11_Cfg (π : G →* S) (C : Subgroup G) [C.Normal] : Prop where
  surj : Function.Surjective π
  eq : C = (Subgroup.center S).comap π
  perfect : Group.IsPerfect G
  nilp : Group.IsNilpotent C
  odd : Odd (Nat.card C)
  syl : ∀ (q : ℕ) [Fact q.Prime] (P : Sylow q C), ((P : Subgroup C).map C.subtype).Normal
  center_eq : Subgroup.center (G ⧸ C) = ⊥
  layer_eq : CFSG.layer (G ⧸ C) = ⊤

private theorem burnsideTA11_cfg (hmin : ChA.IsMinimalCounterexampleToA G S p) :
    ∃ (π : G →* S) (C : Subgroup G) (_ : C.Normal), burnsideTA11_Cfg π C ∧
      Nonempty ((G ⧸ C) ≃* (S ⧸ Subgroup.center S)) := by
  obtain ⟨K, hKn, ⟨e⟩⟩ := (as_A_2_8 G S p hmin).2
  have hcover := (as_A_2_8 G S p hmin).1
  have hO2 : pCore 2 G = ⊥ := as_A_2_10 G S p hmin
  have hssl : genFittingLayer S = ⊤ := hmin.2.2.2.1
  let π : G →* S := e.symm.toMonoidHom.comp (QuotientGroup.mk' K)
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective K)
  have hmin' : ∀ Y : Subgroup G, Y ≠ ⊤ → Y.map π ≠ ⊤ := by
    intro Y hY hYmap
    apply hY
    apply hcover Y
    let φ : Y →* S := π.comp Y.subtype
    have hφ : Function.Surjective φ := by
      intro s
      have hs : s ∈ Y.map π := hYmap ▸ Subgroup.mem_top s
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hs
      exact ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨H, K', hK', ⟨e'⟩⟩ := burnsideTA11_isSectionOf_quotient φ.ker
    exact ⟨H, K', hK', ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans e'⟩⟩
  have hss : CFSG.layer S = ⊤ := by
    rw [← CFSG.Adapters.genFittingLayer_eq_foundations]
    exact hssl
  obtain ⟨hperf, hCn, hnil, hsyl, ⟨e', he'⟩, hZS, hES, hZX, hEX⟩ :=
    CFSG.SectionRank.minimal_semisimple_cover hss π hπ hmin'
  haveI := hCn
  have hodd : Odd (Nat.card ((Subgroup.center S).comap π)) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ((Subgroup.center S).comap π)))
    have hPne := Sylow.ne_bot_of_dvd_card P h2
    apply hPne
    haveI := hsyl 2 P
    have hle : (P : Subgroup ((Subgroup.center S).comap π)).map
        ((Subgroup.center S).comap π).subtype ≤ pCore 2 G :=
      CFSG.RankThree.OddKernel.le_pCore inferInstance (P.isPGroup'.map _)
    rw [hO2, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _
      ((Subgroup.center S).comap π).subtype_injective).mp hle
  exact ⟨π, (Subgroup.center S).comap π, hCn,
    ⟨hπ, rfl, hperf, hnil, hodd, hsyl, hZX, hEX⟩, ⟨e'⟩⟩

end Cfg

section Transfer

private theorem burnsideTA11_odd_not_dvd_of_pgroup {q p : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (hp : p.Prime) (hpq : p ≠ q) {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup q Q) :
    Odd (Nat.card Q) ∧ ¬ p ∣ Nat.card Q := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  rw [hk]
  refine ⟨(hq.out.odd_of_ne_two hq2).pow, fun h => hpq ?_⟩
  exact (Nat.prime_dvd_prime_iff_eq hp hq.out).mp (hp.dvd_of_dvd_pow h)

private theorem burnsideTA11_evenRank_le_two_of_local {X : Type*} [Group X] [Finite X]
    (h : ∀ r : ℕ, r.Prime → r ≠ 2 → twoLocalPrimeRank r X ≤ 2) : evenRank X ≤ 2 := by
  refine csSup_le' ?_
  rintro _ ⟨r, H, hr, hr2, hH, rfl⟩
  refine le_trans ?_ (h r hr hr2)
  exact le_csSup ⟨Nat.card X, by
    rintro _ ⟨K, -, rfl⟩
    exact CFSG.SectionRank.pRank_le_card_of_one_lt hr.one_lt K⟩ ⟨H, hH, rfl⟩

private theorem burnsideTA11_pRank_quotient_sup {G : Type} [Group G] [Finite G] (K Q : Subgroup G)
    [K.Normal] [Q.Normal] {q p : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hp : p.Prime) (hpq : p ≠ q)
    (hQ : IsPGroup q Q) :
    CFSG.pRank p (G ⧸ K) = CFSG.pRank p (G ⧸ (K ⊔ Q)) := by
  have : Fact p.Prime := ⟨hp⟩
  have e := QuotientGroup.quotientQuotientEquivQuotient K (K ⊔ Q) le_sup_left
  have hmap : (K ⊔ Q).map (QuotientGroup.mk' K) = Q.map (QuotientGroup.mk' K) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hN : IsPGroup q ((K ⊔ Q).map (QuotientGroup.mk' K)) := by
    rw [hmap]
    exact hQ.of_surjective ((QuotientGroup.mk' K).subgroupMap Q)
      ((QuotientGroup.mk' K).subgroupMap_surjective Q)
  have hcop := (burnsideTA11_odd_not_dvd_of_pgroup hq2 hp hpq hN).2
  have h := CFSG.SectionRank.pRank_quotient_eq (p := p) ((K ⊔ Q).map (QuotientGroup.mk' K)) hcop
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top p (G ⧸ K),
    CFSG.SectionRank.pRank_eq_open_pRank_top p (G ⧸ (K ⊔ Q)),
    ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact h.symm

private theorem burnsideTA11_twoLocal_le_quotient_sup {G : Type} [Group G] [Finite G] (K Q :
    Subgroup G)
    [K.Normal] [Q.Normal] {q p : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hp : p.Prime) (hpq : p ≠ q)
    (hQ : IsPGroup q Q) :
    twoLocalPrimeRank p (G ⧸ K) ≤ twoLocalPrimeRank p (G ⧸ (K ⊔ Q)) := by
  have e := QuotientGroup.quotientQuotientEquivQuotient K (K ⊔ Q) le_sup_left
  have hmap : (K ⊔ Q).map (QuotientGroup.mk' K) = Q.map (QuotientGroup.mk' K) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hN : IsPGroup q ((K ⊔ Q).map (QuotientGroup.mk' K)) := by
    rw [hmap]
    exact hQ.of_surjective ((QuotientGroup.mk' K).subgroupMap Q)
      ((QuotientGroup.mk' K).subgroupMap_surjective Q)
  obtain ⟨hodd, hcop⟩ := burnsideTA11_odd_not_dvd_of_pgroup hq2 hp hpq hN
  have h := CFSG.RankThree.OddKernel.localRank_le_quotient_of_odd hp
    ((K ⊔ Q).map (QuotientGroup.mk' K)) hodd hcop
  exact h.trans (CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp).le

end Transfer

section SLBound

private theorem burnsideTA11_card_le_pow_of_injective {G α K : Type*} [Finite G] [Fintype α]
    [Field K]
    {r : ℕ} (hr : r ≠ 0) (φ : G → α → K) (hφ : Function.Injective φ)
    (hpow : ∀ g a, φ g a ^ r = 1) : Nat.card G ≤ r ^ Fintype.card α := by
  classical
  set S : Finset K := (Polynomial.nthRoots r (1 : K)).toFinset
  have hS : S.card ≤ r := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots r 1)
  let ψ : G → (α → S) := fun g a =>
    ⟨φ g a, by rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hr)];
                exact hpow g a⟩
  have hψ : Function.Injective ψ := fun g g' h =>
    hφ (funext fun a => congrArg Subtype.val (congrFun h a))
  calc Nat.card G ≤ Nat.card (α → S) := Nat.card_le_card_of_injective ψ hψ
    _ = S.card ^ Fintype.card α := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe]
    _ ≤ r ^ Fintype.card α := Nat.pow_le_pow_left hS _

open Polynomial Module Matrix in
private theorem burnsideTA11_exists_common_eigenbasis {K : Type*} [Field K] [IsAlgClosed K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (hr : (r : K) ≠ 0) (E : Subgroup (GL ι K))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ r = 1) :
    ∃ (b : Module.Basis ι K (ι → K)) (d : GL ι K → ι → K),
      ∀ x ∈ E, ∀ a, (x : Matrix ι ι K) *ᵥ b a = d x a • b a := by
  classical
  set f : E → Module.End K (ι → K) :=
    fun x => Matrix.toLinAlgEquiv' ((x : GL ι K) : Matrix ι ι K) with hfdef
  have hfcomm : ∀ i j, Commute (f i) (f j) := fun i j => by
    change Matrix.toLinAlgEquiv' _ * Matrix.toLinAlgEquiv' _ =
      Matrix.toLinAlgEquiv' _ * Matrix.toLinAlgEquiv' _
    rw [← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, hcomm _ i.2 _ j.2]
  have hfr : ∀ i, f i ^ r = 1 := fun i => by
    change (Matrix.toLinAlgEquiv' _) ^ r = 1
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hexp _ i.2, Units.val_one, map_one]
  have hsep : (X ^ r - C (1 : K)).Separable := separable_X_pow_sub_C 1 hr one_ne_zero
  have hss : ∀ i, (f i).IsSemisimple := fun i =>
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hfr i])
  set W : (E → K) → Submodule K (ι → K) := fun χ => ⨅ i, (f i).maxGenEigenspace (χ i) with hW
  have hind : iSupIndep W :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hfcomm j i) φ)
  have htop : ⨆ χ, W χ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      (fun i j _ => hfcomm i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  set b₀ := hint.collectedBasis (fun χ => Module.finBasis K (W χ))
  let e := b₀.indexEquiv (Pi.basisFun K ι)
  refine ⟨b₀.reindex e, fun x a => if hx : x ∈ E then (e.symm a).1 ⟨x, hx⟩ else 0, ?_⟩
  intro x hx a
  have hmem : b₀.reindex e a ∈ W (e.symm a).1 := by
    rw [Module.Basis.reindex_apply]
    exact hint.collectedBasis_mem _ _
  have h1 : b₀.reindex e a ∈ (f ⟨x, hx⟩).maxGenEigenspace ((e.symm a).1 ⟨x, hx⟩) :=
    (Submodule.mem_iInf _).mp hmem ⟨x, hx⟩
  rw [(hss ⟨x, hx⟩).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
    Module.End.mem_eigenspace_iff] at h1
  simp only [hx, ↓reduceDIte]
  rw [← h1]
  rfl

open Module Matrix in
private theorem burnsideTA11_card_le_of_det_eq_one_of_isAlgClosed {K : Type*} [Field K]
    [IsAlgClosed K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (hr0 : r ≠ 0) (hr : (r : K) ≠ 0) (a₀ : ι)
    (E : Subgroup (GL ι K)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ r = 1) (hdet : ∀ x ∈ E, (x : Matrix ι ι K).det = 1) [Finite E] :
    Nat.card E ≤ r ^ (Fintype.card ι - 1) := by
  classical
  obtain ⟨b, d, hb⟩ := burnsideTA11_exists_common_eigenbasis hr E hcomm hexp
  have eigen_mul : ∀ {x y : GL ι K}, x ∈ E → y ∈ E → ∀ a, d (x * y) a = d x a * d y a := by
    intro x y hx hy a
    have h1 := hb (x * y) (E.mul_mem hx hy) a
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb y hy a, Matrix.mulVec_smul, hb x hx a,
      smul_smul] at h1
    rw [mul_comm]
    exact (smul_left_injective K (b.ne_zero a) h1).symm
  have eigen_one : ∀ a, d 1 a = 1 := by
    intro a
    have h0 := hb 1 E.one_mem a
    rw [Units.val_one, Matrix.one_mulVec] at h0
    exact smul_left_injective K (b.ne_zero a) (show d 1 a • b a = (1 : K) • b a by
      rw [← h0, one_smul])
  have eigen_pow : ∀ {x : GL ι K}, x ∈ E → ∀ (n : ℕ) (a : ι), d (x ^ n) a = d x a ^ n := by
    intro x hx n a
    induction n with
    | zero => rw [pow_zero, pow_zero, eigen_one]
    | succ n ih => rw [pow_succ, eigen_mul (E.pow_mem hx n) hx, ih, pow_succ]
  have eigen_pow_r : ∀ {x : GL ι K}, x ∈ E → ∀ a, d x a ^ r = 1 := by
    intro x hx a
    rw [← eigen_pow hx r a, hexp x hx, eigen_one]
  have eigen_ext : ∀ {x y : GL ι K}, x ∈ E → y ∈ E → (∀ a, d x a = d y a) → x = y := by
    intro x y hx hy h
    apply Units.ext
    apply Matrix.toLin'.injective
    apply b.ext
    intro a
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hb x hx a, hb y hy a, h a]
  have eigen_det : ∀ {x : GL ι K}, x ∈ E → (x : Matrix ι ι K).det = ∏ a, d x a := by
    intro x hx
    rw [← LinearMap.det_toLin', ← LinearMap.det_toMatrix b,
      show LinearMap.toMatrix b b (Matrix.toLin' (x : Matrix ι ι K)) =
        Matrix.diagonal (d x) from ?_, Matrix.det_diagonal]
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hb x hx j, map_smul, b.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have h := burnsideTA11_card_le_pow_of_injective (α := {a : ι // a ≠ a₀}) hr0
    (fun (x : E) a => d x a)
    (fun x y hxy => by
      have hxy' : ∀ a, a ≠ a₀ → d x a = d y a := fun a ha => congrFun hxy ⟨a, ha⟩
      apply Subtype.ext
      refine eigen_ext x.2 y.2 fun a => ?_
      by_cases ha : a = a₀
      · subst ha
        have hx := (eigen_det x.2).symm.trans (hdet x x.2)
        have hy := (eigen_det y.2).symm.trans (hdet y y.2)
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)] at hx hy
        have hp : ∏ c ∈ Finset.univ.erase a, d x c = ∏ c ∈ Finset.univ.erase a, d y c :=
          Finset.prod_congr rfl fun c hc => hxy' c (Finset.ne_of_mem_erase hc)
        rw [hp] at hx
        have hne : ∏ c ∈ Finset.univ.erase a, d y c ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hy
          exact zero_ne_one hy
        exact mul_right_cancel₀ hne (hx.trans hy.symm)
      · exact hxy' a ha)
    (fun x a => eigen_pow_r x.2 a)
  rwa [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h

private theorem burnsideTA11_card_le_of_det_eq_one {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {r : ℕ} (hr0 : r ≠ 0) (hr : (r : K) ≠ 0) (a₀ : ι)
    (E : Subgroup (GL ι K)) [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ r = 1)
    (hdet : ∀ x ∈ E, (x : Matrix ι ι K).det = 1) :
    Nat.card E ≤ r ^ (Fintype.card ι - 1) := by
  set L := AlgebraicClosure K
  set Φ := Matrix.GeneralLinearGroup.map (n := ι) (algebraMap K L)
  have hΦ : Function.Injective Φ := fun _ _ h =>
    Units.ext (Matrix.map_injective (algebraMap K L).injective (congrArg Units.val h))
  have hr' : (r : L) ≠ 0 := by
    intro h
    apply hr
    apply (algebraMap K L).injective
    rw [map_natCast, h, map_zero]
  have : Finite (E.map Φ) := Finite.of_surjective _ (Φ.subgroupMap_surjective E)
  have h := burnsideTA11_card_le_of_det_eq_one_of_isAlgClosed hr0 hr' a₀ (E.map Φ)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one])
    (by
      rintro _ ⟨x, hx, rfl⟩
      change ((x : Matrix ι ι K).map (algebraMap K L)).det = 1
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet x hx, map_one])
  rwa [Subgroup.card_map_of_injective hΦ] at h

end SLBound

section ClauseB

private theorem burnsideTA11_three_ne_zero_of_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (hcard : Nat.card K = (2 ^ n) ^ 2) : (3 : K) ≠ 0 := by
  intro h
  have : Fintype K := Fintype.ofFinite K
  have h3 : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
  haveI : CharP K 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr h3
  obtain ⟨m, -, hm⟩ := FiniteField.card K 3
  rw [← Nat.card_eq_fintype_card, hcard] at hm
  have h3d : 3 ∣ (2 ^ n) ^ 2 := by
    rw [hm]
    exact dvd_pow_self 3 m.pos.ne'
  have := Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow h3d)
  omega

private theorem burnsideTA11_pRank_three_le_two_of_isSUn {n : ℕ} {X : Type} [Group X] [Finite X]
    (h : ChA.IsSUn 3 (2 ^ n) X) : CFSG.pRank 3 X ≤ 2 := by
  obtain ⟨K, hK, hKf, hcard, ⟨e⟩⟩ := h
  have h3K : (3 : K) ≠ 0 := burnsideTA11_three_ne_zero_of_card hcard
  rw [CFSG.pRank_congr_of_mulEquiv e 3]
  refine csSup_le' ?_
  rintro r ⟨B, hB, hr⟩
  obtain ⟨hBc, hBe⟩ := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 B).mp hB
  set E : Subgroup (GL (Fin 3) K) := B.map (StatedSU 3 (2 ^ n) K).subtype with hEdef
  have hfin : Finite E := inferInstance
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩))
  have hexp : ∀ x ∈ E, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hBe x hx, map_one]
  have hdet : ∀ x ∈ E, (x : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rintro _ ⟨x, -, rfl⟩
    exact CFSG.Open.StatedAPI.det_of_mem_statedSU x.2
  have hbound := burnsideTA11_card_le_of_det_eq_one (r := 3) (by norm_num)
    (by exact_mod_cast h3K) (0 : Fin 3) E hcomm hexp hdet
  rw [Fintype.card_fin, hEdef,
    Subgroup.card_map_of_injective (StatedSU 3 (2 ^ n) K).subtype_injective, hr] at hbound
  have h32 : 3 ^ r ≤ 3 ^ 2 := by simpa using hbound
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h32

private theorem burnsideTA11_not_commutative_of_quasisimple {L : Type*} [Group L]
    (h : CFSG.Open.IsQuasisimple L) : ¬ ∀ a b : L, a * b = b * a := by
  intro hc
  have hz : Subgroup.center L = ⊤ :=
    (Subgroup.eq_top_iff' _).mpr fun a => Subgroup.mem_center_iff.mpr fun b => hc b a
  obtain ⟨-, hs⟩ := h
  haveI : Subsingleton (L ⧸ Subgroup.center L) := by
    rw [hz]
    exact QuotientGroup.subsingleton_quotient_top
  exact (not_subsingleton (L ⧸ Subgroup.center L)) inferInstance

private theorem burnsideTA11_isComponentOf_subgroupOf {X : Type*} [Group X] {H L : Subgroup X}
    (h : IsComponentOf L H) : IsComponentOf (L.subgroupOf H) ⊤ :=
  ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib h.2.1.subgroupOf,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.2⟩

private theorem burnsideTA11_false_of_clauseB_simple {X : Type} [Group X] [Finite X] {R : Type}
    [Group R] [IsSimpleGroup R] (hnab : ∃ a b : R, a * b ≠ b * a) {H H₁ H₂ : Subgroup X}
    {n₁ : ℕ} (e : R ≃* ↥H ⧸ Subgroup.center ↥H) (hr : CFSG.pRank 3 ↥H = 3) (hsup : H = H₁ ⊔ H₂)
    (hc₁ : IsComponentOf H₁ H) (hc₂ : IsComponentOf H₂ H) (hs₁ : ChA.IsSUn 3 (2 ^ n₁) ↥H₁) :
    False := by
  by_cases hne : H₁ = H₂
  · subst hne
    rw [sup_idem] at hsup
    subst hsup
    have := burnsideTA11_pRank_three_le_two_of_isSUn hs₁
    omega
  · have hle₁ : H₁ ≤ H := hc₁.1
    have hle₂ : H₂ ≤ H := hc₂.1
    have hA₁ := burnsideTA11_isComponentOf_subgroupOf hc₁
    have hA₂ := burnsideTA11_isComponentOf_subgroupOf hc₂
    have hne' : H₁.subgroupOf H ≠ H₂.subgroupOf H := by
      intro h
      apply hne
      have := Subgroup.subgroupOf_inj.mp h
      rwa [inf_of_le_left hle₁, inf_of_le_left hle₂] at this
    have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hA₁ hA₂ hne'
    have hsupA : H₁.subgroupOf H ⊔ H₂.subgroupOf H = ⊤ := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_of_le_left hle₁, inf_of_le_left hle₂, ← hsup, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    set π := QuotientGroup.mk' (Subgroup.center ↥H) with hπ
    set B₁ : Subgroup (↥H ⧸ Subgroup.center ↥H) := (H₁.subgroupOf H).map π with hB₁
    set B₂ : Subgroup (↥H ⧸ Subgroup.center ↥H) := (H₂.subgroupOf H).map π with hB₂
    have hBsup : B₁ ⊔ B₂ = ⊤ := by
      rw [hB₁, hB₂, ← Subgroup.map_sup, hsupA,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have hle : H₁.subgroupOf H ≤ Subgroup.centralizer ((H₂.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hBc : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hba : b * a = a * b := Subgroup.mem_centralizer_iff.mp (hle ha) b hb
      rw [← map_mul, ← map_mul, hba]
    haveI hQs : IsSimpleGroup (↥H ⧸ Subgroup.center ↥H) := e.symm.isSimpleGroup
    have hnormB : ∀ (B C : Subgroup (↥H ⧸ Subgroup.center ↥H)), B ⊔ C = ⊤ →
        (∀ x ∈ B, ∀ y ∈ C, x * y = y * x) → B.Normal := by
      intro B C hBC hc
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hBC]
      refine sup_le Subgroup.le_normalizer fun y hy => Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hc h hh y hy
    haveI hB₁n : B₁.Normal := hnormB B₁ B₂ hBsup hBc
    haveI hB₂n : B₂.Normal :=
      hnormB B₂ B₁ (by rw [sup_comm]; exact hBsup) (fun x hx y hy => (hBc y hy x hx).symm)
    have hnotbot : ∀ {L : Subgroup X}, IsComponentOf L H → ¬ ((L.subgroupOf H).map π = ⊥) := by
      intro L hL hbot
      rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
      refine burnsideTA11_not_commutative_of_quasisimple hL.2.2 fun a b => ?_
      have ha : (⟨(a : X), hL.1 a.2⟩ : ↥H) ∈ Subgroup.center ↥H := hbot a.2
      have h1 := Subgroup.mem_center_iff.mp ha ⟨(b : X), hL.1 b.2⟩
      exact Subtype.ext (congrArg (fun z : ↥H => (z : X)) h1.symm)
    have hB₁top : B₁ = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal B₁).resolve_left (hnotbot hc₁)
    have hB₂top : B₂ = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal B₂).resolve_left (hnotbot hc₂)
    have hQc : ∀ a b : ↥H ⧸ Subgroup.center ↥H, a * b = b * a := fun a b =>
      hBc a (by rw [hB₁top]; exact Subgroup.mem_top a) b (by rw [hB₂top]; exact Subgroup.mem_top b)
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact hQc _ _

private theorem burnsideTA11_isPerfect_of_sup_components {X : Type*} [Group X] {H H₁ H₂ :
    Subgroup X}
    (hsup : H = H₁ ⊔ H₂) (hc₁ : IsComponentOf H₁ H) (hc₂ : IsComponentOf H₂ H) :
    Group.IsPerfect ↥H := by
  have hle₁ : H₁ ≤ H := hc₁.1
  have hle₂ : H₂ ≤ H := hc₂.1
  have hA₁ := burnsideTA11_isComponentOf_subgroupOf hc₁
  have hA₂ := burnsideTA11_isComponentOf_subgroupOf hc₂
  have hsupA : H₁.subgroupOf H ⊔ H₂.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hle₁, inf_of_le_left hle₂, ← hsup, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have p₁ : ⁅H₁.subgroupOf H, H₁.subgroupOf H⁆ = H₁.subgroupOf H :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hA₁.2.2.1)
  have p₂ : ⁅H₂.subgroupOf H, H₂.subgroupOf H⁆ = H₂.subgroupOf H :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hA₂.2.2.1)
  rw [Group.isPerfect_def, commutator_def]
  refine eq_top_iff.mpr ?_
  have h1 : H₁.subgroupOf H ≤ ⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ := by
    calc H₁.subgroupOf H = ⁅H₁.subgroupOf H, H₁.subgroupOf H⁆ := p₁.symm
      _ ≤ ⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ := Subgroup.commutator_mono le_top le_top
  have h2 : H₂.subgroupOf H ≤ ⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ := by
    calc H₂.subgroupOf H = ⁅H₂.subgroupOf H, H₂.subgroupOf H⁆ := p₂.symm
      _ ≤ ⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ := Subgroup.commutator_mono le_top le_top
  have h12 := sup_le h1 h2
  rwa [hsupA] at h12

private theorem burnsideTA11_false_of_clauseB {X : Type} [Group X] [Finite X] {Y R : Type} [Group Y]
    [Group R] [IsSimpleGroup R] (hnab : ∃ a b : R, a * b ≠ b * a) (φ : Y →* R)
    (hφ : Function.Surjective φ) (hφc : φ.ker ≤ Subgroup.center Y) {H H₁ H₂ : Subgroup X}
    {n₁ : ℕ} (e : Y ≃* ↥H ⧸ Subgroup.center ↥H) (hr : CFSG.pRank 3 ↥H = 3)
    (hsup : H = H₁ ⊔ H₂) (hc₁ : IsComponentOf H₁ H) (hc₂ : IsComponentOf H₂ H)
    (hs₁ : ChA.IsSUn 3 (2 ^ n₁) ↥H₁) : False := by
  haveI := burnsideTA11_isPerfect_of_sup_components hsup hc₁ hc₂
  have hZ : Subgroup.center (↥H ⧸ Subgroup.center ↥H) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot ↥H
  have hZY : Subgroup.center Y = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have h1 : e z ∈ Subgroup.center (↥H ⧸ Subgroup.center ↥H) := by
      rw [← Subgroup.map_center_eq e]
      exact Subgroup.mem_map_of_mem _ hz
    rw [hZ, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact e.injective (h1.trans (map_one e).symm)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZY]
    exact hφc
  exact burnsideTA11_false_of_clauseB_simple hnab
    ((MulEquiv.ofBijective φ ⟨hinj, hφ⟩).symm.trans e) hr hsup hc₁ hc₂ hs₁

end ClauseB

section R1

variable {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S] {p : ℕ}

private theorem burnsideTA11_not_dvd_card_map_sylow {C : Subgroup G} {q : ℕ} [hq : Fact q.Prime]
    (P : Sylow q C) (Q : Subgroup G) [Q.Normal] (hQ : Q = (P : Subgroup C).map C.subtype) :
    ¬ q ∣ Nat.card (C.map (QuotientGroup.mk' Q)) := by
  have hQC : Q ≤ C := hQ ▸ Subgroup.map_subtype_le _
  set f : C →* G ⧸ Q := (QuotientGroup.mk' Q).domRestrict C with hf
  have hker : f.ker = Q.subgroupOf C := by
    rw [hf, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  have hrange : f.range = C.map (QuotientGroup.mk' Q) := MonoidHom.domRestrict_range C _
  have hcard : Nat.card C = Nat.card f.range * Nat.card f.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hkcard : Nat.card f.ker = q ^ (Nat.card C).factorization q := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv, hQ,
      Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity]
  intro hdvd
  rw [← hrange] at hdvd
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  set v := (Nat.card C).factorization q with hv
  obtain ⟨m, hm⟩ := hdvd
  have h1 : q ^ (v + 1) ∣ Nat.card C := ⟨m, by rw [hcard, hkcard, hm]; ring⟩
  have h2 := (hq.out.pow_dvd_iff_le_factorization hC0).mp h1
  omega

private theorem burnsideTA11_R1 {π : G →* S} {C : Subgroup G} [C.Normal] (hcfg :
    burnsideTA11_Cfg π C)
    (hmin : ChA.IsMinimalCounterexampleToA G S p)
    {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hsimple : IsSimpleGroup (G ⧸ C)) (hnab : ∃ a b : G ⧸ C, a * b ≠ b * a)
    (hloc : twoLocalPrimeRank q (G ⧸ C) ≤ 2) : ¬ q ∣ Nat.card C := by
  intro hqC
  obtain ⟨hev, hK, hsec, hss, hp, hp2, hnc, hprop⟩ := hmin
  have hpq : p ≠ q := fun h => hqp h.symm
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow q C))
  set Q : Subgroup G := (P : Subgroup C).map C.subtype with hQdef
  haveI hQn : Q.Normal := hcfg.syl q P
  have hQC : Q ≤ C := Subgroup.map_subtype_le _
  have hQq : IsPGroup q Q := P.isPGroup'.map C.subtype
  have hQne : Q ≠ ⊥ := by
    intro h
    exact Sylow.ne_bot_of_dvd_card P hqC
      ((Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp h)
  obtain ⟨hQodd, hQpcop⟩ := burnsideTA11_odd_not_dvd_of_pgroup hq2 hp hpq hQq
  have hproper : ChA.IsProperSectionOf (G ⧸ Q) G :=
    ⟨burnsideTA11_isSectionOf_quotient Q, burnsideTA11_card_quotient_lt Q hQne⟩
  have hA : ChA.TheoremAHolds (G ⧸ Q) := hprop _ hproper
  have hKQ : CFSG.SectionRank.IsKGroupCat (G ⧸ Q) := hK.quotient _
  have hlocQ : ∀ r : ℕ, r.Prime → r ≠ 2 → twoLocalPrimeRank r (G ⧸ Q) ≤ 2 := by
    intro r hr hr2
    by_cases hrq : r = q
    · subst hrq
      set N' : Subgroup (G ⧸ Q) := C.map (QuotientGroup.mk' Q) with hN'
      haveI : N'.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Q)
      have hodd : Odd (Nat.card N') :=
        Odd.of_dvd_nat hcfg.odd (Subgroup.card_map_dvd C (QuotientGroup.mk' Q))
      have hcop : ¬ r ∣ Nat.card N' := burnsideTA11_not_dvd_card_map_sylow P Q hQdef
      have e := QuotientGroup.quotientQuotientEquivQuotient Q C hQC
      calc twoLocalPrimeRank r (G ⧸ Q) ≤ twoLocalPrimeRank r ((G ⧸ Q) ⧸ N') :=
            CFSG.RankThree.OddKernel.localRank_le_quotient_of_odd hr N' hodd hcop
        _ = twoLocalPrimeRank r (G ⧸ C) :=
            CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr
        _ ≤ 2 := hloc
    · have hrQ : ¬ r ∣ Nat.card Q := (burnsideTA11_odd_not_dvd_of_pgroup hq2 hr hrq hQq).2
      calc twoLocalPrimeRank r (G ⧸ Q) ≤ twoLocalPrimeRank r G :=
            CFSG.RankThree.Classical2.localRank_quotient_le hr hr2 Q hrQ
        _ ≤ evenRank G := burnsideTA11_twoLocalPrimeRank_le_evenRank hr hr2
        _ ≤ 2 := hev
  have hevQ : evenRank (G ⧸ Q) ≤ 2 := burnsideTA11_evenRank_le_two_of_local hlocQ
  set K : Subgroup G := π.ker with hKdef
  have e1 : S ≃* G ⧸ K := (QuotientGroup.quotientKerEquivOfSurjective π hcfg.surj).symm
  have hKC : K ≤ C := by
    intro g hg
    rw [hcfg.eq]
    change π g ∈ Subgroup.center S
    rw [MonoidHom.mem_ker.mp hg]
    exact one_mem _
  have hKQC : K ⊔ Q ≤ C := sup_le hKC hQC
  have hTsec : ChA.IsSectionOf (G ⧸ (K ⊔ Q)) (G ⧸ Q) :=
    burnsideTA11_isSectionOf_quotient_quotient _ _ le_sup_right
  have hsurj : Function.Surjective
      ((QuotientGroup.map K (K ⊔ Q) (MonoidHom.id G) le_sup_left).comp e1.toMonoidHom) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨e1.symm (QuotientGroup.mk g), ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rfl
  have hTss : genFittingLayer (G ⧸ (K ⊔ Q)) = ⊤ :=
    burnsideTA11_genFittingLayer_top_of_surjective hss _ hsurj
  have hconc := (hA hevQ hKQ _ hTsec hTss).1 p hp hp2
  unfold ChA.TheoremAConclusion at hconc
  obtain ⟨hconc1, hconc2⟩ := hconc
  have hnotB : ¬ (p = 3 ∧ ∃ (H H₁ H₂ : Subgroup (G ⧸ Q)) (n₁ n₂ : ℕ),
      Nonempty (G ⧸ (K ⊔ Q) ≃* ↥H ⧸ Subgroup.center ↥H) ∧ CFSG.pRank 3 ↥H = 3 ∧ H = H₁ ⊔ H₂ ∧
      IsComponentOf H₁ H ∧ IsComponentOf H₂ H ∧ ChA.IsSUn 3 (2 ^ n₁) ↥H₁ ∧
      ChA.IsSUn 3 (2 ^ n₂) ↥H₂ ∧ 3 ≤ n₁ ∧ Odd n₁ ∧ 3 ≤ n₂ ∧ Odd n₂ ∧
      ChA.centerOf H₁ = ChA.centerOf H₂ ∧ (Nat.gcd n₁ n₂ = 1 ∨ Nat.gcd n₁ n₂ = 3)) := by
    rintro ⟨-, H, H₁, H₂, n₁, n₂, ⟨e⟩, hr3, hsup, hc1, hc2, hs1, -⟩
    haveI := hsimple
    let φ : G ⧸ (K ⊔ Q) →* G ⧸ C := QuotientGroup.map (K ⊔ Q) C (MonoidHom.id G) hKQC
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨QuotientGroup.mk g, rfl⟩
    have hφc : φ.ker ≤ Subgroup.center (G ⧸ (K ⊔ Q)) := by
      intro x hx
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      have hgC : g ∈ C := by
        have : φ (QuotientGroup.mk g) = 1 := hx
        exact (QuotientGroup.eq_one_iff g).mp this
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hgS : π g ∈ Subgroup.center S := by
        have := hgC
        rw [hcfg.eq] at this
        exact this
      have hcomm : π (h * g) = π (g * h) := by
        rw [map_mul, map_mul]
        exact (Subgroup.mem_center_iff.mp hgS (π h))
      have hker : (h * g)⁻¹ * (g * h) ∈ K := by
        rw [hKdef, MonoidHom.mem_ker, map_mul, map_inv, hcomm, inv_mul_cancel]
      exact Subgroup.mem_sup_left hker
    exact burnsideTA11_false_of_clauseB hnab φ hφ hφc e hr3 hsup hc1 hc2 hs1
  rcases hconc1 with ⟨ha, -⟩ | hB
  swap
  · exact absurd hB hnotB
  apply hnc
  unfold ChA.TheoremAConclusion
  refine ⟨Or.inl ⟨?_, (burnsideTA11_twoLocalPrimeRank_le_evenRank hp hp2).trans hev⟩, fun hG => ?_⟩
  · calc twoLocalPrimeRank p S = twoLocalPrimeRank p (G ⧸ K) :=
          (CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e1 hp)
      _ ≤ twoLocalPrimeRank p (G ⧸ (K ⊔ Q)) :=
          burnsideTA11_twoLocal_le_quotient_sup K Q hq2 hp hpq hQq
      _ ≤ twoLocalPrimeRank p (G ⧸ Q) := ha
      _ ≤ twoLocalPrimeRank p G :=
          CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 Q hQpcop
  · haveI : Fact p.Prime := ⟨hp⟩
    have hGQ : CFSG.pRank p (G ⧸ Q) = CFSG.pRank p G := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top p (G ⧸ Q),
        CFSG.SectionRank.pRank_eq_open_pRank_top p G]
      exact CFSG.SectionRank.pRank_quotient_eq Q hQpcop
    have hS : CFSG.pRank p S = CFSG.pRank p (G ⧸ (K ⊔ Q)) :=
      (CFSG.pRank_congr_of_mulEquiv e1 p).trans (burnsideTA11_pRank_quotient_sup K Q hq2 hp hpq hQq)
    simp only [burnsideTA11_pRank_top_eq] at hconc2 hG ⊢
    rw [hS]
    exact hGQ ▸ hconc2 (hGQ ▸ hG)

end R1

section Misc

variable {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S] {p : ℕ}

private theorem burnsideTA11_pCoreOf_top {G : Type*} [Group G] (p : ℕ) :
    CFSG.Open.pCoreOf p (⊤ : Subgroup G) = CFSG.pCore p G := by
  unfold CFSG.Open.pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv p (Subgroup.topEquiv (G := G)).symm,
    Subgroup.map_map]
  have hid : (Subgroup.subtype ⊤).comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom =
      MonoidHom.id G := by
    ext x
    rfl
  rw [hid, Subgroup.map_id]

private theorem burnsideTA11_relPPrimeCore_top (G : Type) [Group G] [Finite G] :
    (relPPrimeCore 2 (⊤ : Subgroup G)).Normal ∧
      Odd (Nat.card (relPPrimeCore 2 (⊤ : Subgroup G))) := by
  have hmem : ∀ N ∈ {N : Subgroup G | N ≤ ⊤ ∧ (N.subgroupOf ⊤).Normal ∧
      Nat.Coprime 2 (Nat.card N)}, N.Normal ∧ Odd (Nat.card N) := by
    rintro N ⟨-, hN, hcop⟩
    refine ⟨⟨fun k hk g => ?_⟩, Nat.coprime_two_left.mp hcop⟩
    have := hN.conj_mem ⟨k, trivial⟩ (by simpa [Subgroup.mem_subgroupOf] using hk) ⟨g, trivial⟩
    simpa [Subgroup.mem_subgroupOf] using this
  refine ⟨?_, ?_⟩
  · exact Subgroup.sSup_normal _ fun N hN => (hmem N hN).1
  · exact CFSG.ComponentClassification.OddCore.odd_card_sSup _ (Set.toFinite _)
      (fun N hN => (hmem N hN).1) (fun N hN => (hmem N hN).2)

private theorem burnsideTA11_coprime_kernel (hev : evenRank G ≤ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Subgroup G) [K.Normal] (hK : ¬ p ∣ Nat.card K) (e : S ≃* G ⧸ K) :
    ChA.TheoremAConclusion G S p := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold ChA.TheoremAConclusion
  refine ⟨Or.inl ⟨?_, (burnsideTA11_twoLocalPrimeRank_le_evenRank hp hp2).trans hev⟩, fun _ => ?_⟩
  · calc twoLocalPrimeRank p S = twoLocalPrimeRank p (G ⧸ K) :=
          CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp
      _ ≤ twoLocalPrimeRank p G := CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 K hK
  · simp only [burnsideTA11_pRank_top_eq]
    rw [CFSG.pRank_congr_of_mulEquiv e p, CFSG.SectionRank.pRank_eq_open_pRank_top p (G ⧸ K),
      CFSG.SectionRank.pRank_eq_open_pRank_top p G]
    exact (CFSG.SectionRank.pRank_quotient_eq K hK).le

private theorem burnsideTA11_nontrivial_quot {π : G →* S} {C : Subgroup G} [C.Normal]
    (hcfg : burnsideTA11_Cfg π C) (hC : C ≠ ⊥) : Nontrivial (G ⧸ C) := by
  by_contra hno
  rw [not_nontrivial_iff_subsingleton] at hno
  have htop : C = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have : (QuotientGroup.mk g : G ⧸ C) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff g).mp this
  subst htop
  haveI := hcfg.perfect
  haveI : Nontrivial G := by
    by_contra hG
    rw [not_nontrivial_iff_subsingleton] at hG
    exact hC (Subsingleton.elim _ _)
  exact Group.IsPerfect.not_isNilpotent G (Group.isNilpotent_top.mp hcfg.nilp)

private theorem burnsideTA11_exists_big_rank {π : G →* S} {C :
    Subgroup G}
    [C.Normal] (hcfg : burnsideTA11_Cfg π C) (hCZ : ¬ C ≤ Subgroup.center G) :
    ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card C ∧ 2 < CFSG.Open.pRank r C := by
  by_contra hno
  push Not at hno
  apply hCZ
  exact CFSG.SectionRank.Ccomm.odd_nilpotent_kernel_centralization hcfg.perfect C hcfg.nilp
    hcfg.odd (fun N _ => (CFSG.SectionRank.centerless_semisimple_quotient hcfg.layer_eq
      hcfg.center_eq (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)).2)
    fun r hr hrC => hno r hr hrC

open scoped commutatorElement in
private theorem burnsideTA11_R2b {π : G →* S} {C : Subgroup G} [C.Normal] (hcfg :
    burnsideTA11_Cfg π C)
    (hev : evenRank G ≤ 2) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrank : 2 < CFSG.Open.pRank r C) :
    CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ 3 ∧ CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ 2 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hloc : twoLocalPrimeRank r G ≤ 2 :=
    (burnsideTA11_twoLocalPrimeRank_le_evenRank hr hr2).trans hev
  obtain ⟨E, hEC, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hr.one_lt C
  have hEp : IsPGroup r E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  have hEcore : E ≤ CFSG.pCore r G := by
    have hEp' : IsPGroup r (E.subgroupOf C) :=
      hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEC).symm
    obtain ⟨P, hP⟩ := hEp'.exists_le_sylow
    haveI := hcfg.syl r P
    have hle : (P : Subgroup C).map C.subtype ≤ CFSG.pCore r G :=
      CFSG.RankThree.OddKernel.le_pCore inferInstance (P.isPGroup'.map _)
    intro x hx
    exact hle ⟨⟨x, hEC hx⟩, hP (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hcore : 2 < CFSG.pRank r ↥(pCoreOf r (⊤ : Subgroup G)) := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank, burnsideTA11_pCoreOf_top]
    exact lt_of_lt_of_le hrank (CFSG.SectionRank.le_pRank hr.one_lt hEcore hE hEcard)
  obtain ⟨h3, hmore⟩ := as_A_1_28 G r hr hr2 hloc ⊤ hcore
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
  refine ⟨h3, ?_⟩
  by_contra hgt
  push Not at hgt
  have heq : CFSG.pRank 2 ↥(⊤ : Subgroup G) = 3 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    omega
  obtain ⟨a, -, ha1, ha2, hcomm⟩ := hmore heq
  obtain ⟨hOn, hOodd⟩ := burnsideTA11_relPPrimeCore_top G
  haveI := hOn
  have hOC : relPPrimeCore 2 (⊤ : Subgroup G) ≤ C :=
    CFSG.RankThree.OddKernel.le_of_odd_card_normal hcfg.layer_eq hcfg.center_eq hOodd
  have hac : (QuotientGroup.mk a : G ⧸ C) ∈ Subgroup.center (G ⧸ C) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 := hOC (hcomm h (Subgroup.mem_top h))
    have h2 : (QuotientGroup.mk' C) ⁅a, h⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_commutatorElement] at h2
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  rw [hcfg.center_eq, Subgroup.mem_bot] at hac
  have haC : a ∈ C := (QuotientGroup.eq_one_iff a).mp hac
  have hord : orderOf (⟨a, haC⟩ : C) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime ha2 ha1
  have h2dvd : 2 ∣ Nat.card C := by
    rw [← hord]
    exact orderOf_dvd_natCard _
  exact (Nat.not_even_iff_odd.mpr hcfg.odd) (even_iff_two_dvd.mpr h2dvd)

private theorem burnsideTA11_simple_of_twoRank_le_three {X : Type}
    [Group X] [Finite X] [Nontrivial X] (hE : CFSG.layer X = ⊤) (hZ : Subgroup.center X = ⊥)
    (h2 : CFSG.Open.pRank 2 (⊤ : Subgroup X) ≤ 3) : IsSimpleGroup X := by
  classical
  obtain ⟨C₁, hC₁⟩ := CFSG.RankThree.OddKernel.exists_isComponent hE
  have hall : ∀ C₂ : Subgroup X, CFSG.IsComponent C₂ → C₂ = C₁ := by
    intro C₂ hC₂
    by_contra hne
    have hcomm : ⁅C₁, C₂⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hC₁ hC₂).resolve_left (fun h => hne h.symm)
    have hZ₁ := CFSG.RankThree.OddKernel.center_eq_bot_of_isComponent hE hZ hC₁
    have hZ₂ := CFSG.RankThree.OddKernel.center_eq_bot_of_isComponent hE hZ hC₂
    obtain ⟨hs₁, hnab₁⟩ := CFSG.RankThree.OddKernel.isSimpleGroup_of_isQuasisimple hC₁.1 hZ₁
    obtain ⟨hs₂, hnab₂⟩ := CFSG.RankThree.OddKernel.isSimpleGroup_of_isQuasisimple hC₂.1 hZ₂
    obtain ⟨V₁, hV₁c, hV₁2, hV₁4⟩ :=
      CFSG.RankThree.OddKernel.exists_four_group_of_isSimpleGroup hnab₁
    obtain ⟨V₂, hV₂c, hV₂2, hV₂4⟩ :=
      CFSG.RankThree.OddKernel.exists_four_group_of_isSimpleGroup hnab₂
    have h12 : C₁ ≤ Subgroup.centralizer (C₂ : Set X) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm
    obtain ⟨V, hVc, hV2, hV16⟩ := CFSG.RankThree.OddKernel.exists_elementary_sixteen
      (V₁ := V₁.map C₁.subtype) (V₂ := V₂.map C₂.subtype)
      (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; exact congrArg Subtype.val (hV₁c x hx y hy))
      (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; exact congrArg Subtype.val (hV₂c x hx y hy))
      (by rintro _ ⟨x, hx, rfl⟩; exact congrArg Subtype.val (hV₁2 x hx))
      (by rintro _ ⟨x, hx, rfl⟩; exact congrArg Subtype.val (hV₂2 x hx))
      (by rw [Subgroup.card_map_of_injective C₁.subtype_injective, hV₁4])
      (by rw [Subgroup.card_map_of_injective C₂.subtype_injective, hV₂4])
      (by
        rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
        exact (Subgroup.mem_centralizer_iff.1 (h12 x.2) y y.2).symm)
      (by
        rw [eq_bot_iff]
        rintro _ ⟨⟨x, -, rfl⟩, ⟨y, -, hxy⟩⟩
        have hx1 : x ∈ Subgroup.center C₁ := by
          rw [Subgroup.mem_center_iff]
          intro c
          apply Subtype.ext
          have hyc := Subgroup.mem_centralizer_iff.1 (h12 c.2) y y.2
          rw [show ((y : C₂) : X) = (x : X) from hxy] at hyc
          exact hyc.symm
        rw [hZ₁, Subgroup.mem_bot] at hx1
        rw [Subgroup.mem_bot, hx1]
        rfl)
    have hVe : IsElemAbelian 2 V := ⟨⟨⟨fun a b => Subtype.ext (hVc a a.2 b b.2)⟩⟩, hV2⟩
    have h4 := CFSG.SectionRank.le_pRank (p := 2) one_lt_two (le_top : V ≤ ⊤) hVe
      (by rw [hV16]; norm_num : Nat.card V = 2 ^ 4)
    omega
  have hlayer : CFSG.layer X = C₁ := by
    rw [CFSG.layer.eq_sSup]
    exact le_antisymm (sSup_le fun C hC => (hall C hC).le) (le_sSup hC₁)
  have hC1top : C₁ = ⊤ := hlayer.symm.trans hE
  subst hC1top
  have hq : CFSG.IsQuasisimple X :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := X)) hC₁.1
  exact (CFSG.RankThree.OddKernel.isSimpleGroup_of_isQuasisimple hq hZ).1

private theorem burnsideTA11_R4one {π : G →* S} {C : Subgroup G} [C.Normal]
    (hcfg : burnsideTA11_Cfg π C) (hC : CFSG.SectionRank.QTK.QTCentreFact) (hev : evenRank G ≤ 2)
    (hK : CFSG.SectionRank.IsKGroupCat G) (hCZ : C ≤ Subgroup.center G)
    (hs : IsSimpleGroup (G ⧸ C)) (hnab : ∃ a b : G ⧸ C, a * b ≠ b * a) :
    ∀ r : ℕ, r.Prime → r ≠ 2 → twoLocalPrimeRank r (G ⧸ C) ≤ 2 := by
  have hZG : Subgroup.center G = C := by
    refine le_antisymm (fun z hz => ?_) hCZ
    have hz' : (QuotientGroup.mk z : G ⧸ C) ∈ Subgroup.center (G ⧸ C) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hz h]
    rw [hcfg.center_eq, Subgroup.mem_bot] at hz'
    exact (QuotientGroup.eq_one_iff z).mp hz'
  let e₁ : G ⧸ C ≃* G ⧸ Subgroup.center G := QuotientGroup.quotientMulEquivOfEq hZG.symm
  haveI := hs
  have hq : CFSG.IsQuasisimple G := by
    refine ⟨hcfg.perfect, e₁.symm.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e₁ a, e₁ b, fun h => hab (e₁.injective (by rw [map_mul, map_mul, h]))⟩
  have e₀ : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  have hq' : CFSG.IsQuasisimple ↥(⊤ : Subgroup G) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hq
  have h := CFSG.SectionRank.QTK.evenRank_center_quotient_le_two hC hev hq' (hK.subgroup ⊤)
  have e₂ : (↥(⊤ : Subgroup G) ⧸ Subgroup.center ↥(⊤ : Subgroup G)) ≃* G ⧸ C :=
    (QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)).trans e₁.symm
  intro r hr hr2
  calc twoLocalPrimeRank r (G ⧸ C)
      = twoLocalPrimeRank r (↥(⊤ : Subgroup G) ⧸ Subgroup.center ↥(⊤ : Subgroup G)) :=
        (CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e₂ hr).symm
    _ ≤ evenRank _ := burnsideTA11_twoLocalPrimeRank_le_evenRank hr hr2
    _ ≤ 2 := h

private theorem burnsideTA11_center_eq {π : G →* S} {C : Subgroup G} [C.Normal]
    (hcfg : burnsideTA11_Cfg π C) (hCZ : C ≤ Subgroup.center G) : Subgroup.center G = C := by
  refine le_antisymm (fun z hz => ?_) hCZ
  have hz' : (QuotientGroup.mk z : G ⧸ C) ∈ Subgroup.center (G ⧸ C) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hz h]
  rw [hcfg.center_eq, Subgroup.mem_bot] at hz'
  exact (QuotientGroup.eq_one_iff z).mp hz'

private theorem burnsideTA11_R4 {π : G →* S} {C : Subgroup G} [C.Normal] (hcfg :
    burnsideTA11_Cfg π C)
    (hcat : CFSG.SectionRank.CatalogStepHyp) (hev : evenRank G ≤ 2)
    (hK : CFSG.SectionRank.IsKGroupCat G) (hCZ : C ≤ Subgroup.center G)
    (hns : ¬ IsSimpleGroup (G ⧸ C)) : ∀ q : ℕ, q.Prime → q ∣ Nat.card C → q = 3 := by
  intro q hq hqC
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZG : Subgroup.center G = C := burnsideTA11_center_eq hcfg hCZ
  have hlayer : CFSG.layer G = ⊤ :=
    CFSG.SectionRank.perfect_central_semisimple_extension hcfg.perfect C hCZ hcfg.layer_eq
  have hother : ∀ L : Subgroup G, CFSG.IsComponent L →
      ∃ L' : Subgroup G, CFSG.IsComponent L' ∧ L' ≠ L := by
    intro L hL
    by_contra hno
    push Not at hno
    have hlay : CFSG.layer G = L := by
      rw [CFSG.layer.eq_sSup]
      exact le_antisymm (sSup_le fun C' hC' => (hno C' hC').le) (le_sSup hL)
    have hLtop : L = ⊤ := hlay.symm.trans hlayer
    subst hLtop
    have hq' : CFSG.IsQuasisimple G :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := G)) hL.1
    haveI := hq'.2.1
    exact hns ((QuotientGroup.quotientMulEquivOfEq hZG.symm).isSimpleGroup)
  have hcomp : ∀ L : Subgroup G, CFSG.IsComponent L →
      Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3 := by
    intro L hL
    obtain ⟨L', hL', hne⟩ := hother L hL
    have hL'even : Even (Nat.card L') := CFSG.RankThree.OddKernel.even_card_of_isQuasisimple hL'.1
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := L') 2 (even_iff_two_dvd.mp hL'even)
    have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
    have hcommL : ∀ x ∈ L, Commute x (t : G) := by
      rcases CFSG.LocalCores.distinct_components_commute hL hL' with h | h
      · exact absurd h.symm hne
      · intro x hx
        have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx
        exact (Subgroup.mem_centralizer_iff.mp h1 (t : G) t.2).symm
    have hU : (Subgroup.zpowers (t : G)) ≠ ⊥ := by
      intro h
      have : (t : G) = 1 := by
        have := Subgroup.mem_zpowers (t : G)
        rw [h, Subgroup.mem_bot] at this
        exact this
      rw [this, orderOf_one] at ht2
      omega
    have hU2 : IsPGroup 2 (Subgroup.zpowers (t : G)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, ht2]
      norm_num
    have hLN : L ≤ Subgroup.normalizer ((Subgroup.zpowers (t : G) : Subgroup G) : Set G) := by
      intro x hx
      have hxc : x ∈ Subgroup.centralizer ((Subgroup.zpowers (t : G) : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        exact ((hcommL x hx).zpow_right k).symm.eq
      exact Subgroup.centralizer_le_normalizer _ hxc
    have hSQT : CFSG.IsStronglyQuasithin ↥L := by
      intro r hr hr2
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
      refine le_trans (CFSG.SectionRank.pRank_mono hr.one_lt hLN) ?_
      refine le_trans ?_ hev
      refine le_trans ?_ (burnsideTA11_twoLocalPrimeRank_le_evenRank hr hr2)
      exact le_csSup ⟨Nat.card G, by
        rintro _ ⟨K, -, rfl⟩
        exact CFSG.SectionRank.pRank_le_card_of_one_lt hr.one_lt K⟩
        ⟨_, ⟨_, hU, hU2, rfl⟩, rfl⟩
    have hle : (Subgroup.center ↥L).map L.subtype ≤ Subgroup.center G := by
      intro z hz
      have h1 := CFSG.LocalCores.center_component_le_centralizer_layer hL hz
      rw [hlayer, Subgroup.coe_top, Subgroup.centralizer_univ] at h1
      exact h1
    have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by
      have hdvd := Subgroup.card_dvd_of_le (hle.trans hZG.le)
      rw [Subgroup.card_map_of_injective L.subtype_injective] at hdvd
      exact Odd.of_dvd_nat hcfg.odd hdvd
    exact (hcat L hL.1 ⟨hSQT, hK.subgroup L⟩ hodd).1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := C) q hqC
  have hzG : (z : G) ∈ Subgroup.center G := hCZ z.2
  have hzord : orderOf (z : G) = q := by rw [Subgroup.orderOf_coe]; exact hz
  obtain ⟨y, hy⟩ := CFSG.LocalCores.exists_layerMul_eq (g := (z : G)) (hlayer ▸ Subgroup.mem_top _)
  have hycent : ∀ K : CFSG.LocalCores.ComponentIndex G, y K ∈ Subgroup.center K.1 := by
    rw [← CFSG.LocalCores.layerMul_mem_centralizer_iff, hy, hlayer, Subgroup.coe_top,
      Subgroup.centralizer_univ]
    exact hzG
  set n : ℕ := ∏ K : CFSG.LocalCores.ComponentIndex G, Nat.card (Subgroup.center K.1) with hn
  have hyn : y ^ n = 1 := by
    funext K
    rw [Pi.pow_apply, Pi.one_apply]
    have hdvd : Nat.card (Subgroup.center K.1) ∣ n :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ K)
    obtain ⟨m, hm⟩ := hdvd
    rw [hm, pow_mul]
    have : ((y K : K.1) ^ Nat.card (Subgroup.center K.1)) = 1 := by
      have := pow_card_eq_one' (G := Subgroup.center K.1)
        (x := (⟨y K, hycent K⟩ : Subgroup.center K.1))
      exact congrArg Subtype.val this
    rw [this, one_pow]
  have hzn : (z : G) ^ n = 1 := by
    rw [← hy, ← map_pow, hyn, map_one]
  have hqn : q ∣ n := hzord ▸ orderOf_dvd_of_pow_eq_one hzn
  obtain ⟨K, -, hKq⟩ := (Prime.dvd_finset_prod_iff hq.prime _).mp hqn
  rcases hcomp K.1 K.2 with h1 | h1
  · rw [h1] at hKq
    exact absurd (Nat.le_of_dvd one_pos hKq) (by have := hq.two_le; omega)
  · rw [h1] at hKq
    exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hKq

end Misc

section Main

variable {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S] {p : ℕ}

section R3exc

private theorem burnsideTA11_isProperSectionOf_subgroup {G : Type} [Group G] [Finite G] (H :
    Subgroup G)
    (hH : H ≠ ⊤) : ChA.IsProperSectionOf ↥H G := by
  refine ⟨⟨H, ⊥, inferInstance, ⟨?_⟩⟩, ?_⟩
  · exact (QuotientGroup.quotientBot (G := ↥H)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf H).symm)
  · exact lt_of_le_of_ne (Subgroup.card_le_card_group H) fun h =>
      hH ((Subgroup.card_eq_iff_eq_top H).mp h)

@[expose] def burnsideTA11_negOne (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨-1, by simp [Matrix.det_neg]⟩

private theorem burnsideTA11_negOne_central {K : Type} [Field K] (g : Matrix.SpecialLinearGroup
    (Fin 2) K) :
    g * burnsideTA11_negOne K = burnsideTA11_negOne K * g := by
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) K) * (-1) = (-1) * (g : Matrix (Fin 2) (Fin 2) K)
  simp

private theorem burnsideTA11_negOne_ne_one {K : Type} [Field K] (h2 : (2 : K) ≠ 0) :
    burnsideTA11_negOne K ≠ 1 := by
  intro h
  have h1 := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  change (-1 : Matrix (Fin 2) (Fin 2) K) 0 0 = (1 : Matrix (Fin 2) (Fin 2) K) 0 0 at h1
  simp at h1
  apply h2
  linear_combination -h1

private theorem burnsideTA11_negOne_sq {K : Type} [Field K] : burnsideTA11_negOne K ^ 2 = 1 := by
  rw [sq]
  apply Subtype.ext
  change (-1 : Matrix (Fin 2) (Fin 2) K) * (-1) = 1
  simp

private theorem burnsideTA11_twoLocal_SL2 {K : Type} [Field K] [Finite K] {s f : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hK : Nat.card K = s ^ f) :
    f ≤ twoLocalPrimeRank s (Matrix.SpecialLinearGroup (Fin 2) K) := by
  haveI : Fact s.Prime := ⟨hs⟩
  have hchar : CharP K s := by
    have : Fintype K := Fintype.ofFinite K
    haveI := ringChar.charP K
    obtain ⟨n, hp', hn⟩ := FiniteField.card K (ringChar K)
    rw [← Nat.card_eq_fintype_card, hK] at hn
    have hf0 : f ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Nat.one_lt_pow n.pos.ne' hp'.one_lt).ne' hn.symm
    have hdvd : s ∣ ringChar K ^ (n : ℕ) := by
      rw [← hn]
      exact dvd_pow_self s hf0
    have : s = ringChar K := (Nat.prime_dvd_prime_iff_eq hs hp').mp (hs.dvd_of_dvd_pow hdvd)
    rw [this]
    infer_instance
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K s 2).mp h2
    exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp this)
  have hz1 : Subgroup.zpowers (burnsideTA11_negOne K) ≠ ⊥ := by
    intro h
    have := Subgroup.mem_zpowers (burnsideTA11_negOne K)
    rw [h, Subgroup.mem_bot] at this
    exact burnsideTA11_negOne_ne_one h2K this
  have hord : orderOf (burnsideTA11_negOne K) = 2 :=
    orderOf_eq_prime burnsideTA11_negOne_sq (burnsideTA11_negOne_ne_one h2K)
  have hz2 : IsPGroup 2 (Subgroup.zpowers (burnsideTA11_negOne K)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]
    norm_num
  have hzn : (Subgroup.zpowers (burnsideTA11_negOne K)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute g (burnsideTA11_negOne K) := burnsideTA11_negOne_central g
    rw [(hc.zpow_right k).mul_inv_cancel]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hloc : IsTwoLocal (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) :=
    ⟨Subgroup.zpowers (burnsideTA11_negOne K), hz1, hz2,
      (Subgroup.normalizer_eq_top_iff.mpr hzn).symm⟩
  set E := (CFSG.SectionRank.QTK.sl2UpperHom (K := K)).range with hE
  have hEel : IsElemAbelian s E := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      change CFSG.SectionRank.QTK.sl2UpperHom a * CFSG.SectionRank.QTK.sl2UpperHom b =
        CFSG.SectionRank.QTK.sl2UpperHom b * CFSG.SectionRank.QTK.sl2UpperHom a
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨c, rfl⟩
      rw [← map_pow]
      have : c ^ s = 1 := Multiplicative.toAdd.injective (by
        rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul])
      rw [this, map_one]
  have hEcard : Nat.card E = s ^ f := by
    rw [hE, ← Nat.card_congr (MonoidHom.ofInjective
      (CFSG.SectionRank.QTK.sl2UpperHom_injective (K := K))).toEquiv, Nat.card_congr
      (Multiplicative.toAdd : Multiplicative K ≃ K), hK]
  have hf : f ≤ CFSG.Open.pRank s (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) :=
    CFSG.SectionRank.le_pRank hs.one_lt le_top hEel hEcard
  refine hf.trans ?_
  exact le_csSup ⟨Nat.card _, by
    rintro _ ⟨K', -, rfl⟩
    exact CFSG.SectionRank.pRank_le_card_of_one_lt hs.one_lt K'⟩ ⟨⊤, hloc, rfl⟩

end R3exc

private theorem burnsideTA11_R3exc {π : G →* S} {C : Subgroup G} [C.Normal] (hcfg :
    burnsideTA11_Cfg π C)
    (hmin : ChA.IsMinimalCounterexampleToA G S p)
    {s f : ℕ} (hs1 : s.Prime) (hs2 : s ≠ 2) (hf : 3 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = s ^ f) (φ : Matrix.SpecialLinearGroup (Fin 2) K →* G ⧸ C)
    (hφ : Function.Injective φ) : False := by
  obtain ⟨hev, hKG, hsec, hss, hp, hp2, hnc, hprop⟩ := hmin
  haveI : Fact s.Prime := ⟨hs1⟩
  have hfs : 4 ≤ s ^ f := by
    have h3 : 3 ≤ s := by have := hs1.two_le; omega
    have h27 : 3 ^ 3 ≤ s ^ f :=
      (Nat.pow_le_pow_left h3 3).trans (Nat.pow_le_pow_right hs1.pos hf)
    omega
  have h4 : ∃ t : Finset K, t.card = 4 := by
    have : Fintype K := Fintype.ofFinite K
    have hle : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
      exact hfs
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq hle
    exact ⟨t, ht⟩
  have hq : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.RankThree.Classical.isQuasisimple_SL2 h4
  have h2K : (2 : K) ≠ 0 := by
    have hchar : CharP K s := by
      have : Fintype K := Fintype.ofFinite K
      haveI := ringChar.charP K
      obtain ⟨n, hp', hn⟩ := FiniteField.card K (ringChar K)
      rw [← Nat.card_eq_fintype_card, hK] at hn
      have hf0 : f ≠ 0 := by omega
      have hdvd : s ∣ ringChar K ^ (n : ℕ) := by
        rw [← hn]
        exact dvd_pow_self s hf0
      have : s = ringChar K := (Nat.prime_dvd_prime_iff_eq hs1 hp').mp (hs1.dvd_of_dvd_pow hdvd)
      rw [this]
      infer_instance
    intro h
    have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K s 2).mp h2
    exact hs2 ((Nat.prime_dvd_prime_iff_eq hs1 Nat.prime_two).mp this)
  set Lh : Subgroup (G ⧸ C) := φ.range with hLh
  set L : Subgroup G := Lh.comap (QuotientGroup.mk' C) with hLdef
  have hL : L ≠ ⊤ := by
    intro hLtop
    have hrange : φ.range = ⊤ := by
      have h1 : Lh = L.map (QuotientGroup.mk' C) :=
        (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C) Lh).symm
      rw [hLtop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)] at h1
      exact h1
    have hcentral : φ (burnsideTA11_negOne K) ∈ Subgroup.center (G ⧸ C) := by
      rw [Subgroup.mem_center_iff]
      intro g'
      have hg' : g' ∈ φ.range := by rw [hrange]; exact Subgroup.mem_top g'
      obtain ⟨x, rfl⟩ := hg'
      rw [← map_mul, ← map_mul, burnsideTA11_negOne_central x]
    rw [hcfg.center_eq, Subgroup.mem_bot, ← map_one φ] at hcentral
    exact burnsideTA11_negOne_ne_one h2K (hφ hcentral)
  have hA : ChA.TheoremAHolds ↥L := hprop ↥L (burnsideTA11_isProperSectionOf_subgroup L hL)
  have hevL : evenRank ↥L ≤ 2 := (CFSG.RankThree.PartTwo.evenRank_subgroup_le L).trans hev
  have hKL : CFSG.SectionRank.IsKGroupCat ↥L := hKG.subgroup L
  let ι : ↥L →* ↥φ.range := ((QuotientGroup.mk' C).comp L.subtype).codRestrict φ.range
    (fun g => g.2)
  have hι : Function.Surjective ι := by
    intro y
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective C (y : G ⧸ C)
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    change QuotientGroup.mk' C g ∈ φ.range
    rw [hg]
    exact y.2
  have e₁ : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥L ⧸ ι.ker :=
    (MonoidHom.ofInjective hφ).trans (QuotientGroup.quotientKerEquivOfSurjective ι hι).symm
  have hsecL : ChA.IsSectionOf (Matrix.SpecialLinearGroup (Fin 2) K) ↥L := by
    obtain ⟨H', K', hK', ⟨e'⟩⟩ := burnsideTA11_isSectionOf_quotient ι.ker
    exact ⟨H', K', hK', ⟨e₁.trans e'⟩⟩
  have hX : genFittingLayer (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤ := by
    rw [CFSG.Adapters.genFittingLayer_eq_foundations]
    exact CFSG.WholeGroup.layer_eq_top_of_isQuasisimple hq
  have hconc := (hA hevL hKL _ hsecL hX).1 s hs1 hs2
  unfold ChA.TheoremAConclusion at hconc
  obtain ⟨hc1, -⟩ := hconc
  rcases hc1 with ⟨ha, hb⟩ | ⟨-, H, H₁, H₂, n₁, n₂, ⟨e⟩, hr3, hsup, hc1, hc2, hs1', -⟩
  · have h3 := burnsideTA11_twoLocal_SL2 hs1 hs2 hK
    omega
  · haveI := hq.2.1
    exact burnsideTA11_false_of_clauseB hq.2.2 (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _).le e hr3 hsup hc1 hc2 hs1'

private theorem burnsideTA11_main
    (hR3 : burnsideTA11_Rank2Fact) (hC : CFSG.SectionRank.QTK.QTCentreFact)
    (hcat : CFSG.SectionRank.CatalogStepHyp)
    (hmin : ChA.IsMinimalCounterexampleToA G S p) :
    Nonempty ((G ⧸ pCore p G) ≃* (S ⧸ Subgroup.center S)) := by
  obtain ⟨π, C, hCn, hcfg, ⟨e⟩⟩ := burnsideTA11_cfg hmin
  haveI := hCn
  have hmin' := hmin
  obtain ⟨hev, hK, hsec, hss, hp, hp2, hnc, hprop⟩ := hmin'
  haveI : Fact p.Prime := ⟨hp⟩
  have hCodd := hcfg.odd
  have hCne : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hq2 : ∀ q : ℕ, q ∣ Nat.card C → q ≠ 2 := by
    rintro q hq rfl
    exact (Nat.not_even_iff_odd.mpr hCodd) (even_iff_two_dvd.mpr hq)
  have hGCperf : Group.IsPerfect (G ⧸ C) :=
    Group.IsPerfect.top_iff.mp (hcfg.layer_eq ▸ CFSG.LocalCores.layer_isPerfect)
  have hnab : IsSimpleGroup (G ⧸ C) → ∃ a b : G ⧸ C, a * b ≠ b * a := by
    intro hs
    by_contra hcomm
    push Not at hcomm
    haveI : IsMulCommutative (G ⧸ C) := ⟨⟨fun a b => hcomm a b⟩⟩
    haveI := hGCperf
    haveI : Subsingleton (G ⧸ C) := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact not_subsingleton (G ⧸ C) inferInstance
  have key : ∀ q : ℕ, q.Prime → q ∣ Nat.card C → q = p := by
    intro q hq hqC
    by_contra hqp
    haveI : Fact q.Prime := ⟨hq⟩
    have hq2' := hq2 q hqC
    by_cases hs : IsSimpleGroup (G ⧸ C)
    · have hnab' := hnab hs
      by_cases hCZ : C ≤ Subgroup.center G
      · exact burnsideTA11_R1 hcfg hmin hq2' hqp hs hnab'
          (burnsideTA11_R4one hcfg hC hev hK hCZ hs hnab' q hq hq2') hqC
      · obtain ⟨r, hr, hrC, hrank⟩ := burnsideTA11_exists_big_rank hcfg hCZ
        have h2 := (burnsideTA11_R2b hcfg hev hr (hq2 r hrC) hrank).2
        have htwo : twoRank (G ⧸ C) = 2 := by
          haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          have h1 : twoRank (G ⧸ C) = CFSG.Open.pRank 2 (⊤ : Subgroup G) :=
            CFSG.SectionRank.pRank_quotient_eq C (fun h => hq2 2 h rfl)
          have heven :=
            (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab').1
          have h3 : 2 ≤ twoRank (G ⧸ C) :=
            CFSG.Assembly.LowTwoRank.two_le_twoRank (G ⧸ C) hnab' heven
          exact le_antisymm (h1 ▸ h2) h3
        rcases hR3 (G ⧸ C) hs hnab' htwo with
          hfirst | ⟨s, f, hs1, hs2, hf, -, K, _, _, hK', φ, hφ⟩
        · exact burnsideTA11_R1 hcfg hmin hq2' hqp hs hnab' (hfirst q hq hq2') hqC
        · exact burnsideTA11_R3exc hcfg hmin hs1 hs2 hf K hK' φ hφ
    ·
      have hCZ : C ≤ Subgroup.center G := by
        by_contra hCZ
        obtain ⟨r, hr, hrC, hrank⟩ := burnsideTA11_exists_big_rank hcfg hCZ
        have h3 := (burnsideTA11_R2b hcfg hev hr (hq2 r hrC) hrank).1
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have h1 : CFSG.Open.pRank 2 (⊤ : Subgroup (G ⧸ C)) =
            CFSG.Open.pRank 2 (⊤ : Subgroup G) :=
          CFSG.SectionRank.pRank_quotient_eq C (fun h => hq2 2 h rfl)
        haveI : Nontrivial (G ⧸ C) :=
          burnsideTA11_nontrivial_quot hcfg (fun h => by
            rw [h, Subgroup.card_bot] at hqC
            exact hq.one_lt.ne' (Nat.dvd_one.mp hqC))
        exact hs (burnsideTA11_simple_of_twoRank_le_three hcfg.layer_eq hcfg.center_eq (h1 ▸ h3))
      have h3 := burnsideTA11_R4 hcfg hcat hev hK hCZ hs q hq hqC
      subst h3
      have hp3 : p ≠ 3 := fun h => hqp h.symm
      have hker : ¬ p ∣ Nat.card π.ker := by
        intro hpk
        have hkC : π.ker ≤ C := by
          intro g hg
          rw [hcfg.eq]
          change π g ∈ Subgroup.center S
          rw [MonoidHom.mem_ker.mp hg]
          exact one_mem _
        have : p ∣ Nat.card C := hpk.trans (Subgroup.card_dvd_of_le hkC)
        exact hp3 (burnsideTA11_R4 hcfg hcat hev hK hCZ hs p hp this)
      haveI : π.ker.Normal := inferInstance
      exact hnc (burnsideTA11_coprime_kernel hev hp hp2 π.ker hker
        (QuotientGroup.quotientKerEquivOfSurjective π hcfg.surj).symm)
  have hCp : IsPGroup p C := by
    rw [IsPGroup.iff_card]
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hCne (fun hd hdC => key _ hd hdC)⟩
  have hle1 : C ≤ pCore p G := CFSG.RankThree.OddKernel.le_pCore inferInstance hCp
  have hle2 : pCore p G ≤ C := by
    haveI : (pCore p G).Normal := CFSG.pCore_normal
    refine CFSG.RankThree.OddKernel.le_of_odd_card_normal hcfg.layer_eq hcfg.center_eq ?_
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := p) (G := G)))
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hEq : C = pCore p G := le_antisymm hle1 hle2
  subst hEq
  exact ⟨e⟩

end Main

section Orbit

private theorem burnsideTA11_orbit {T : Type} [Group T] [Finite T] {p c d : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h2 : CFSG.Open.pRank 2 (⊤ : Subgroup T) ≤ 2)
    (hH1 : ∀ t : T, orderOf t = 2 → ∀ V : Subgroup T, IsElemAbelian p V →
      V ≤ Subgroup.centralizer {t} → Nat.card V ≤ p ^ c)
    (hH2 : ∀ t₁ t₂ : T, orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ ≠ t₂ → t₁ * t₂ = t₂ * t₁ →
      ∀ V : Subgroup T, IsElemAbelian p V → V ≤ Subgroup.centralizer {t₁} →
        V ≤ Subgroup.centralizer {t₂} → Nat.card V ≤ p ^ d)
    (U : Subgroup T) (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (V : Subgroup T) (hV : IsElemAbelian p V)
    (hVU : V ≤ Subgroup.normalizer (U : Set T)) :
    Nat.card V ≤ p ^ c ∨ (p = 3 ∧ Nat.card V ≤ 3 * p ^ d) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp : IsPGroup p V := fun g => ⟨1, Subtype.ext (by simpa using hV.2 g g.2)⟩
  let Z : Subgroup T :=
    { carrier := {z | z ∈ U ∧ (∀ u ∈ U, u * z = z * u) ∧ z ^ 2 = 1}
      mul_mem' := by
        rintro a b ⟨haU, haC, ha2⟩ ⟨hbU, hbC, hb2⟩
        refine ⟨mul_mem haU hbU, fun u hu => ?_, ?_⟩
        · rw [← mul_assoc, haC u hu, mul_assoc, hbC u hu, mul_assoc]
        · rw [(show Commute a b from (haC b hbU).symm).mul_pow, ha2, hb2, one_mul]
      one_mem' := ⟨U.one_mem, fun u _ => by rw [mul_one, one_mul], one_pow 2⟩
      inv_mem' := by
        rintro a ⟨haU, haC, ha2⟩
        exact ⟨inv_mem haU, fun u hu => (show Commute u a from haC u hu).inv_right,
          by rw [inv_pow, ha2, inv_one]⟩ }
  obtain ⟨t, htZ, ht1⟩ : ∃ t ∈ Z, t ≠ 1 := by
    have : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hU
    have hcenter := hU2.center_nontrivial
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hU2.to_subgroup (Subgroup.center U))
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr hcenter).ne' hn
    have hdvd : 2 ∣ Nat.card (Subgroup.center U) := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    refine ⟨((x : U) : T), ⟨(x : U).2, fun u hu => ?_, ?_⟩, ?_⟩
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨u, hu⟩)
    · have h : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
      have h' := congrArg (fun y : Subgroup.center U => ((y : U) : T)) h
      simpa using h'
    · intro h1
      have hx1 : x = 1 := Subtype.ext (Subtype.ext h1)
      rw [hx1, orderOf_one] at hx
      omega
  have hVZ : V ≤ Subgroup.normalizer (Z : Set T) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro v hv z hz
    obtain ⟨hzU, hzC, hz2⟩ := hz
    have hvN := hVU hv
    refine ⟨(Subgroup.mem_normalizer_iff.mp hvN z).mp hzU, fun u hu => ?_, ?_⟩
    · have hu' : v⁻¹ * u * v⁻¹⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (inv_mem hvN) u).mp hu
      rw [inv_inv] at hu'
      have key := hzC _ hu'
      calc u * (v * z * v⁻¹) = v * ((v⁻¹ * u * v) * z) * v⁻¹ := by group
        _ = v * (z * (v⁻¹ * u * v)) * v⁻¹ := by rw [key]
        _ = v * z * v⁻¹ * u := by group
    · rw [conj_pow, hz2, mul_one, mul_inv_cancel]
  have hZcard : Nat.card Z ≤ 4 := by
    have hZ2 : IsPGroup 2 Z := fun g => ⟨1, Subtype.ext (by simpa using g.2.2.2)⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ2
    have hab : IsElemAbelian 2 Z := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hx.2.2⟩
      exact (a.2.2.1 b b.2.1).symm
    have hle : n ≤ CFSG.Open.pRank 2 (⊤ : Subgroup T) :=
      CFSG.SectionRank.le_pRank Nat.one_lt_two le_top hab hn
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hle.trans h2)
      _ = 4 := by norm_num
  have ht2 : orderOf t = 2 := orderOf_eq_prime htZ.2.2 ht1
  letI actionV : MulDistribMulAction V Z := CFSG.SignalizerFunctor.Helpers.conjugationAction V Z hVZ
  let t' : Z := ⟨t, htZ⟩
  have hsmul : ∀ (v : V) (z : Z), ((v • z : Z) : T) = (v : T) * (z : T) * (v : T)⁻¹ :=
    fun v z => rfl
  set St : Subgroup V := MulAction.stabilizer V t' with hSt
  set orb : Set Z := MulAction.orbit V t' with horb
  have hcard : Nat.card St * orb.ncard = Nat.card V := by
    rw [← MulAction.index_stabilizer V t']
    exact Subgroup.card_mul_index _
  have hone : ∀ v : V, v • t' ≠ 1 := by
    intro v hv
    have : t' = 1 := by
      have h1 : v⁻¹ • (v • t') = t' := inv_smul_smul v t'
      rw [hv, smul_one] at h1
      exact h1.symm
    exact ht1 (congrArg Subtype.val this)
  have horb_le : orb.ncard + 1 ≤ Nat.card Z := by
    have hsub : orb ⊆ ({1}ᶜ : Set Z) := by
      rintro _ ⟨v, rfl⟩
      exact hone v
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_compl, Set.ncard_singleton] at h1
    have hpos : 0 < Nat.card Z := Nat.card_pos
    omega
  have horb_pos : 0 < orb.ncard := by
    rw [Set.ncard_pos (Set.toFinite _)]
    exact ⟨t', MulAction.mem_orbit_self t'⟩
  have horb3 : orb.ncard ≤ 3 := by omega
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hVp
  have horbdvd : orb.ncard ∣ p ^ m := by
    rw [← hm, ← hcard]
    exact Dvd.intro_left _ rfl
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp horbdvd
  have hfix : orb.ncard = 1 → V ≤ Subgroup.centralizer {t} := by
    intro h1
    have hSttop : St = ⊤ := by
      have : Nat.card St = Nat.card V := by rw [h1, mul_one] at hcard; exact hcard
      exact (Subgroup.card_eq_iff_eq_top St).mp this
    intro v hv
    have hv' : (⟨v, hv⟩ : V) ∈ St := by rw [hSttop]; exact Subgroup.mem_top _
    have := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hv')
    rw [Subgroup.mem_centralizer_singleton_iff]
    change v * t * v⁻¹ = t at this
    calc v * t = v * t * v⁻¹ * v := by group
      _ = t * v := by rw [this]
  by_cases hk1 : orb.ncard = 1
  · left
    exact hH1 t ht2 V hV (hfix hk1)
  · right
    have hj1 : j ≠ 0 := by
      rintro rfl
      exact hk1 (by rw [hj, pow_zero])
    have hp3 : p = 3 := by
      have h3 : p ^ j ≤ 3 := hj ▸ horb3
      have hp3' : p ≤ 3 := (Nat.le_self_pow hj1 p).trans h3
      have := hp.two_le
      omega
    subst hp3
    have hj2 : j = 1 := by
      by_contra hne
      have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : 3 ^ j ≤ 3 := hj ▸ horb3
      omega
    subst hj2
    have hk3 : orb.ncard = 3 := by rw [hj]; norm_num
    refine ⟨rfl, ?_⟩
    obtain ⟨x, hx, hxt⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < orb.ncard) t'
    obtain ⟨v₀, rfl⟩ := hx
    set t₂ : T := ((v₀ • t' : Z) : T) with ht₂def
    have ht₂Z : t₂ ∈ Z := (v₀ • t' : Z).2
    have ht₂1 : t₂ ≠ 1 := fun h => hone v₀ (Subtype.ext h)
    have ht₂ord : orderOf t₂ = 2 := orderOf_eq_prime ht₂Z.2.2 ht₂1
    have hne : t ≠ t₂ := fun h => hxt (Subtype.ext h.symm)
    have hcomm : t * t₂ = t₂ * t := (htZ.2.1 t₂ ht₂Z.1).symm
    set V' : Subgroup T := St.map V.subtype with hV'
    have hV'V : V' ≤ V := by
      rintro _ ⟨s, -, rfl⟩
      exact s.2
    have hV'ab : IsElemAbelian 3 V' :=
      ⟨⟨⟨fun a b => Subtype.ext (by
        have := hV.1.is_comm.comm ⟨a, hV'V a.2⟩ ⟨b, hV'V b.2⟩
        exact congrArg (fun z : ↥V => (z : T)) this)⟩⟩, fun x hx => hV.2 x (hV'V hx)⟩
    have hV'1 : V' ≤ Subgroup.centralizer {t} := by
      rintro _ ⟨s, hs, rfl⟩
      have := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hs)
      rw [Subgroup.mem_centralizer_singleton_iff]
      change (s : T) * t * (s : T)⁻¹ = t at this
      calc (s : T) * t = (s : T) * t * (s : T)⁻¹ * (s : T) := by group
        _ = t * (s : T) := by rw [this]
    have hV'2 : V' ≤ Subgroup.centralizer {t₂} := by
      rintro _ ⟨s, hs, rfl⟩
      have h1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hs)
      change (s : T) * t * (s : T)⁻¹ = t at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hsv : (s : T) * (v₀ : T) = (v₀ : T) * (s : T) :=
        congrArg Subtype.val (hV.1.is_comm.comm s v₀)
      have h2 : (s : T) * t₂ * (s : T)⁻¹ = t₂ := by
        rw [ht₂def, hsmul]
        calc (s : T) * ((v₀ : T) * t * (v₀ : T)⁻¹) * (s : T)⁻¹
            = ((s : T) * (v₀ : T)) * t * ((s : T) * (v₀ : T))⁻¹ := by group
          _ = ((v₀ : T) * (s : T)) * t * ((v₀ : T) * (s : T))⁻¹ := by rw [hsv]
          _ = (v₀ : T) * ((s : T) * t * (s : T)⁻¹) * (v₀ : T)⁻¹ := by group
          _ = (v₀ : T) * t * (v₀ : T)⁻¹ := by rw [h1]
      calc (s : T) * t₂ = (s : T) * t₂ * (s : T)⁻¹ * (s : T) := by group
        _ = t₂ * (s : T) := by rw [h2]
    have hb := hH2 t t₂ ht2 ht₂ord hne hcomm V' hV'ab hV'1 hV'2
    rw [hV', Subgroup.card_map_of_injective V.subtype_injective] at hb
    rw [← hcard, hk3, mul_comm]
    exact Nat.mul_le_mul_left 3 hb

end Orbit

section Models

private theorem burnsideTA11_charP_of_card {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) : CharP K p := by
  have : Fintype K := Fintype.ofFinite K
  haveI := ringChar.charP K
  obtain ⟨n, hp', hn⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card, hK] at hn
  have hdvd : p ∣ ringChar K ^ (n : ℕ) := by
    rw [← hn]
    exact dvd_pow_self p (by omega)
  have : p = ringChar K := (Nat.prime_dvd_prime_iff_eq hp hp').mp (hp.dvd_of_dvd_pow hdvd)
  rw [this]
  infer_instance

private theorem burnsideTA11_natCast_ne_zero {K : Type} [Field K] {p r : ℕ} [CharP K p] (hp :
    p.Prime)
    (hr : r.Prime) (hrp : r ≠ p) : (r : K) ≠ 0 := by
  intro h
  have := (CharP.cast_eq_zero_iff K p r).mp h
  exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp this).symm

private theorem burnsideTA11_twoLocal_le_pRank {T : Type*} [Group T] [Finite T] {r : ℕ} (hr :
    r.Prime) :
    twoLocalPrimeRank r T ≤ CFSG.pRank r T := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine csSup_le' ?_
  rintro _ ⟨H, -, rfl⟩
  exact CFSG.SectionRank.pRank_mono hr.one_lt le_top

private theorem burnsideTA11_twoLocal_le_of_orbit {T : Type} [Group T] [Finite T] {p c d k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h2 : CFSG.Open.pRank 2 (⊤ : Subgroup T) ≤ 2)
    (hH1 : ∀ t : T, orderOf t = 2 → ∀ V : Subgroup T, IsElemAbelian p V →
      V ≤ Subgroup.centralizer {t} → Nat.card V ≤ p ^ c)
    (hH2 : ∀ t₁ t₂ : T, orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ ≠ t₂ → t₁ * t₂ = t₂ * t₁ →
      ∀ V : Subgroup T, IsElemAbelian p V → V ≤ Subgroup.centralizer {t₁} →
        V ≤ Subgroup.centralizer {t₂} → Nat.card V ≤ p ^ d)
    (hc : c ≤ k) (hd : p = 3 → d + 1 ≤ k) : twoLocalPrimeRank p T ≤ k := by
  refine csSup_le' ?_
  rintro _ ⟨N, ⟨U, hU, hU2, rfl⟩, rfl⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt fun V hVN hV => ?_
  rcases burnsideTA11_orbit hp hp2 h2 hH1 hH2 U hU hU2 V hV hVN with h | ⟨hp3, h⟩
  · exact h.trans (Nat.pow_le_pow_right hp.pos hc)
  · subst hp3
    calc Nat.card V ≤ 3 * 3 ^ d := h
      _ = 3 ^ (d + 1) := by ring
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (hd rfl)

private theorem burnsideTA11_pRank_proj_le {K : Type} [Field K] [Finite K] {n r k : ℕ}
    {H : Subgroup (GL (Fin n) K)} (hr : r.Prime)
    (hcop : ¬ r ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf H))
    (hbound : ∀ E ≤ H, (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) → (∀ g ∈ E, g ^ r = 1) →
      Nat.card E ≤ r ^ k) :
    CFSG.pRank r (StatedProj H) ≤ k := by
  rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hr _ hcop,
    CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.RankThree.PartOne.LIT.pRank_le_of_card_gl hr.one_lt H hbound

private theorem burnsideTA11_PSL2_local {T : Type} [Group T] [Finite T] {K : Type} [Field K]
    [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (e : T ≃* StatedProj (StatedSL 2 K)) (h2 : CFSG.Open.pRank 2 (⊤ : Subgroup T) ≤ 2) :
    ∀ r : ℕ, r.Prime → r ≠ 2 → twoLocalPrimeRank r T ≤ 2 := by
  intro r hr hr2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar := burnsideTA11_charP_of_card hp hf hK
  by_cases hrp : r = p
  · subst hrp
    haveI : Fact r.Prime := ⟨hr⟩
    let e' : T ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K :=
      e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
    have hH1 : ∀ t : T, orderOf t = 2 → ∀ V : Subgroup T, IsElemAbelian r V →
        V ≤ Subgroup.centralizer {t} → Nat.card V ≤ r ^ 0 := by
      intro t ht V hV hVC
      have hbot : V = ⊥ := by
        rw [eq_bot_iff]
        intro v hv
        by_contra hne
        have hv1 : v ≠ 1 := fun h => hne (by rw [h]; exact Subgroup.one_mem _)
        have hvr : orderOf v = r := orderOf_eq_prime (hV.2 v hv) hv1
        have hcomm : Commute v t := Subgroup.mem_centralizer_singleton_iff.mp (hVC hv)
        exact CFSG.GorensteinWalter.psl2_no_commuting_distinct_prime_order hK
          (Ne.symm hr2) (a := e' v) (b := e' t) (by rw [MulEquiv.orderOf_eq, hvr])
          (by rw [MulEquiv.orderOf_eq, ht]) (hcomm.map e'.toMonoidHom)
      rw [hbot, Subgroup.card_bot, pow_zero]
    exact burnsideTA11_twoLocal_le_of_orbit hr hr2 h2 hH1
      (fun t₁ _ h1 _ _ _ V hV hV1 _ => hH1 t₁ h1 V hV hV1) (by norm_num) (by intro; norm_num)
  · have hrK : (r : K) ≠ 0 := burnsideTA11_natCast_ne_zero hp hr hrp
    have hbound : ∀ E ≤ StatedSL 2 K, (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) →
        (∀ g ∈ E, g ^ r = 1) → Nat.card E ≤ r ^ 1 := by
      intro E hE hcomm hexp
      have := burnsideTA11_card_le_of_det_eq_one hr.ne_zero hrK (0 : Fin 2) E hcomm hexp
        (fun x hx => CFSG.Open.StatedAPI.det_of_mem_statedSL (hE hx))
      simpa using this
    have h1 : CFSG.pRank r (StatedProj (StatedSL 2 K)) ≤ 1 :=
      CFSG.RankThree.PartOne.pRank_statedProj_statedSL_le hr
        (fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)) hbound
    calc twoLocalPrimeRank r T ≤ CFSG.pRank r T := burnsideTA11_twoLocal_le_pRank hr
      _ = CFSG.pRank r (StatedProj (StatedSL 2 K)) := CFSG.pRank_congr_of_mulEquiv e r
      _ ≤ 1 := h1
      _ ≤ 2 := by norm_num

end Models

section E4

open CFSG.RankThree.CentralCover Matrix in
private theorem burnsideTA11_scalar_eq_one {K : Type} [Field K] [CharP K 3] {c : K} (hc : c ^ 3
    = 1) :
    c = 1 := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have h : (c - 1) ^ 3 = 0 := by linear_combination hc + (c - c ^ 2) * h3
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)

open CFSG.RankThree.CentralCover Matrix in
private theorem burnsideTA11_coe_oddDiag₃ {K : Type} [Field K] :
    ((oddDiag₃ K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![-1, -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oddDiag₃]

open CFSG.RankThree.CentralCover Matrix in
private theorem burnsideTA11_coe_oddDiag₂ {K : Type} [Field K] :
    ((oddDiag₂ K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![-1, 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oddDiag₂]

open CFSG.RankThree.CentralCover Matrix in
private theorem burnsideTA11_E4_core {K : Type} [Field K] [Finite K] [CharP K 3]
    {H : Subgroup (GL (Fin 3) K)} (hH : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hD₃ : oddDiag₃ K ∈ H) (hD₂ : oddDiag₂ K ∈ H) {u : StatedProj H} (hu3 : u ^ 3 = 1)
    (hc₃ : u * statedProjMk H ⟨oddDiag₃ K, hD₃⟩ = statedProjMk H ⟨oddDiag₃ K, hD₃⟩ * u)
    (hc₂ : u * statedProjMk H ⟨oddDiag₂ K, hD₂⟩ = statedProjMk H ⟨oddDiag₂ K, hD₂⟩ * u) :
    u = 1 := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K 3 2).mp this
    omega
  have hinj : Function.Injective (statedProjMk H) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    rw [statedProjMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
    obtain ⟨c, hc⟩ := hz
    have hdet := hH (z : GL (Fin 3) K) z.2
    rw [← hc] at hdet
    have hc3 : (c : K) ^ 3 = 1 := by
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.det_smul] using hdet
    have hc1 : (c : K) = 1 := burnsideTA11_scalar_eq_one hc3
    apply Subtype.ext
    rw [← hc]
    have : c = 1 := Units.ext hc1
    rw [this, map_one]
    rfl
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ u
  change statedProjMk H w ^ 3 = 1 at hu3
  change statedProjMk H w * _ = _ * statedProjMk H w at hc₃ hc₂
  rw [← map_mul, ← map_mul] at hc₃ hc₂
  have hw₃ := hinj hc₃
  have hw₂ := hinj hc₂
  rw [← map_pow, ← map_one (statedProjMk H)] at hu3
  have hw3 := hinj hu3
  set W : Matrix (Fin 3) (Fin 3) K := ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hW
  have e₃ : W * diagonal ![-1, -1, 1] = diagonal ![-1, -1, 1] * W := by
    have := congrArg (fun x : H => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hw₃
    simpa [hW, burnsideTA11_coe_oddDiag₃, Subgroup.coe_mul, Units.val_mul] using this
  have e₂ : W * diagonal ![-1, 1, -1] = diagonal ![-1, 1, -1] * W := by
    have := congrArg (fun x : H => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hw₂
    simpa [hW, burnsideTA11_coe_oddDiag₂, Subgroup.coe_mul, Units.val_mul] using this
  have hoff : ∀ i j : Fin 3, i ≠ j → W i j = 0 := by
    intro i j hij
    have a3 := congrFun (congrFun e₃ i) j
    have a2 := congrFun (congrFun e₂ i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at a3 a2
    fin_cases i <;> fin_cases j <;> simp at hij a3 a2 ⊢ <;>
      first
      | exact (mul_eq_zero.mp (by linear_combination a3 : (2 : K) * _ = 0)).resolve_left h2
      | exact (mul_eq_zero.mp (by linear_combination a2 : (2 : K) * _ = 0)).resolve_left h2
      | exact (mul_eq_zero.mp (by linear_combination -a3 : (2 : K) * _ = 0)).resolve_left h2
      | exact (mul_eq_zero.mp (by linear_combination -a2 : (2 : K) * _ = 0)).resolve_left h2
  have hdiag : W = diagonal (fun i => W i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  have hW3 : W ^ 3 = 1 := by
    have := congrArg (fun x : H => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hw3
    simpa [hW] using this
  have hd1 : ∀ i, W i i = 1 := by
    intro i
    refine burnsideTA11_scalar_eq_one ?_
    have h := congrFun (congrFun hW3 i) i
    rw [hdiag, Matrix.diagonal_pow] at h
    simpa using h
  have hW1 : W = 1 := by
    rw [hdiag]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hd1]
    · simp [Matrix.diagonal_apply_ne _ hij, hij]
  have hw1 : w = 1 := Subtype.ext (Units.ext hW1)
  rw [hw1, map_one]

open CFSG.RankThree.CentralCover Matrix in
private theorem burnsideTA11_H2 {K : Type} [Field K] [Finite K] [CharP K 3] {H : Subgroup (GL
    (Fin 3) K)}
    (hH : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hD₃ : oddDiag₃ K ∈ H) (hD₂ : oddDiag₂ K ∈ H)
    (hconj : ∀ v v' : StatedProj H, orderOf v = 2 → orderOf v' = 2 → v ≠ v' → v * v' = v' * v →
      ∃ g : StatedProj H, g * v * g⁻¹ = statedProjMk H ⟨oddDiag₃ K, hD₃⟩ ∧
        g * v' * g⁻¹ = statedProjMk H ⟨oddDiag₂ K, hD₂⟩)
    {T : Type} [Group T] [Finite T] (e : T ≃* StatedProj H) (t₁ t₂ : T) (h1 : orderOf t₁ = 2)
    (h2 : orderOf t₂ = 2) (hne : t₁ ≠ t₂) (hcomm : t₁ * t₂ = t₂ * t₁) (V : Subgroup T)
    (hV : IsElemAbelian 3 V) (hV1 : V ≤ Subgroup.centralizer {t₁})
    (hV2 : V ≤ Subgroup.centralizer {t₂}) : Nat.card V ≤ 3 ^ 0 := by
  have hbot : V = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨g, hg1, hg2⟩ := hconj (e t₁) (e t₂) (by rw [MulEquiv.orderOf_eq, h1])
      (by rw [MulEquiv.orderOf_eq, h2]) (fun h => hne (e.injective h))
      (by rw [← map_mul, ← map_mul, hcomm])
    have hc1 : v * t₁ = t₁ * v := Subgroup.mem_centralizer_singleton_iff.mp (hV1 hv)
    have hc2 : v * t₂ = t₂ * v := Subgroup.mem_centralizer_singleton_iff.mp (hV2 hv)
    have hu : g * e v * g⁻¹ = 1 := by
      refine burnsideTA11_E4_core hH hD₃ hD₂ ?_ ?_ ?_
      · rw [conj_pow, ← map_pow, hV.2 v hv, map_one, mul_one, mul_inv_cancel]
      · rw [← hg1]
        calc g * e v * g⁻¹ * (g * e t₁ * g⁻¹) = g * e (v * t₁) * g⁻¹ := by
              rw [map_mul]; group
          _ = g * e (t₁ * v) * g⁻¹ := by rw [hc1]
          _ = g * e t₁ * g⁻¹ * (g * e v * g⁻¹) := by rw [map_mul]; group
      · rw [← hg2]
        calc g * e v * g⁻¹ * (g * e t₂ * g⁻¹) = g * e (v * t₂) * g⁻¹ := by
              rw [map_mul]; group
          _ = g * e (t₂ * v) * g⁻¹ := by rw [hc2]
          _ = g * e t₂ * g⁻¹ * (g * e v * g⁻¹) := by rw [map_mul]; group
    have : e v = 1 := by
      have := congrArg (fun x => g⁻¹ * x * g) hu
      simpa [mul_assoc] using this
    rw [Subgroup.mem_bot]
    exact e.injective (this.trans (map_one e).symm)
  rw [hbot, Subgroup.card_bot, pow_zero]

end E4

section ModelS

open CFSG.RankThree.CentralCover in
private theorem burnsideTA11_H1_of_valuation {T : Type} [Group T] [Finite T] {p c : ℕ} (hp :
    p.Prime)
    (hval : ∀ t : T, orderOf t = 2 →
      padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set T))) = c) :
    ∀ t : T, orderOf t = 2 → ∀ V : Subgroup T, IsElemAbelian p V →
      V ≤ Subgroup.centralizer {t} → Nat.card V ≤ p ^ c := by
  intro t ht V hV hVC
  haveI : Fact p.Prime := ⟨hp⟩
  have hVp : IsPGroup p V := fun g => ⟨1, Subtype.ext (by simpa using hV.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hVp
  have hdvd : p ^ k ∣ Nat.card (Subgroup.centralizer ({t} : Set T)) := by
    rw [← hk]
    exact Subgroup.card_dvd_of_le hVC
  have := (padicValNat_dvd_iff_le (Nat.card_pos.ne')).mp hdvd
  rw [hval t ht] at this
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos this

open CFSG.RankThree.CentralCover in
private theorem burnsideTA11_PSL3_local_s {T : Type} [Group T] [Finite T] {K : Type} [Field K]
    [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hfle : f ≤ 2)
    (hK : Nat.card K = p ^ f) (e : T ≃* StatedProj (StatedSL 3 K))
    (h2 : CFSG.Open.pRank 2 (⊤ : Subgroup T) ≤ 2) : twoLocalPrimeRank p T ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hchar := burnsideTA11_charP_of_card hp hf hK
  let φ : T ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm
  have hval : ∀ t : T, orderOf t = 2 →
      padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set T))) = f := by
    intro t ht
    rw [← CFSG.Semidihedral.Principal.DegreeThreeModel.card_centralizer_mulEquiv φ t]
    exact CFSG.Semidihedral.Principal.DegreeThreeModel.padicValNat_centralizer_psl3 hp hpodd hf hK
      (φ t) (by rw [MulEquiv.orderOf_eq, ht])
  have hH1 := burnsideTA11_H1_of_valuation hp hval
  by_cases hp3 : p = 3
  · subst hp3
    have hodd : Odd (Nat.card K) := by rw [hK]; exact hpodd.pow
    have hconj := CFSG.GH74.GLS.IVK.Proofs2.linConj K hodd
    have hH2 : ∀ t₁ t₂ : T, orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ ≠ t₂ → t₁ * t₂ = t₂ * t₁ →
        ∀ V : Subgroup T, IsElemAbelian 3 V → V ≤ Subgroup.centralizer {t₁} →
          V ≤ Subgroup.centralizer {t₂} → Nat.card V ≤ 3 ^ 0 := by
      intro t₁ t₂ h1 h2' hne hcomm V hV hV1 hV2
      exact burnsideTA11_H2 (H := StatedSL 3 K)
        (fun x hx => CFSG.Open.StatedAPI.det_of_mem_statedSL hx)
        (Subgroup.subset_closure (det_oddDiag₃ K)) (Subgroup.subset_closure (det_oddDiag₂ K))
        hconj e t₁ t₂ h1 h2' hne hcomm V hV hV1 hV2
    exact burnsideTA11_twoLocal_le_of_orbit hp hp2 h2 hH1 hH2 hfle (by intro; omega)
  · exact burnsideTA11_twoLocal_le_of_orbit hp hp2 h2 hH1
      (fun t₁ _ h1 _ _ _ V hV hV1 _ => hH1 t₁ h1 V hV hV1) hfle (fun h => absurd h hp3)

open CFSG.RankThree.CentralCover in
private theorem burnsideTA11_PSU3_local_s {T : Type} [Group T] [Finite T] {K : Type} [Field K]
    [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hfle : f ≤ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (e : T ≃* StatedProj (StatedSU 3 (p ^ f) K))
    (h2 : CFSG.Open.pRank 2 (⊤ : Subgroup T) ≤ 2) : twoLocalPrimeRank p T ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hchar := burnsideTA11_charP_of_card hp (by omega) hK'
  have hval : ∀ t : T, orderOf t = 2 →
      padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set T))) = f := by
    intro t ht
    rw [← CFSG.Semidihedral.Principal.DegreeThreeModel.card_centralizer_mulEquiv e t]
    exact CFSG.Semidihedral.Principal.DegreeThreeModel.padicValNat_centralizer_psu3 hpodd hf hK
      (e t) (by rw [MulEquiv.orderOf_eq, ht])
  have hH1 := burnsideTA11_H1_of_valuation hp hval
  by_cases hp3 : p = 3
  · subst hp3
    have hq : Odd (3 ^ f) := hpodd.pow
    have hconj := CFSG.GH74.GLS.IVK.Proofs2.uniConj K hq hK
    have hH2 : ∀ t₁ t₂ : T, orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ ≠ t₂ → t₁ * t₂ = t₂ * t₁ →
        ∀ V : Subgroup T, IsElemAbelian 3 V → V ≤ Subgroup.centralizer {t₁} →
          V ≤ Subgroup.centralizer {t₂} → Nat.card V ≤ 3 ^ 0 := by
      intro t₁ t₂ h1 h2' hne hcomm V hV hV1 hV2
      exact burnsideTA11_H2 (H := StatedSU 3 (3 ^ f) K)
        (fun x hx => CFSG.Open.StatedAPI.det_of_mem_statedSU hx)
        (Subgroup.subset_closure ⟨det_oddDiag₃ K, unitary_oddDiag₃ hq⟩)
        (Subgroup.subset_closure ⟨det_oddDiag₂ K, unitary_oddDiag₂ hq⟩)
        hconj e t₁ t₂ h1 h2' hne hcomm V hV hV1 hV2
    exact burnsideTA11_twoLocal_le_of_orbit hp hp2 h2 hH1 hH2 hfle (by intro; omega)
  · exact burnsideTA11_twoLocal_le_of_orbit hp hp2 h2 hH1
      (fun t₁ _ h1 _ _ _ V hV hV1 _ => hH1 t₁ h1 V hV hV1) hfle (fun h => absurd h hp3)

end ModelS

section ModelNe

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial in
private theorem burnsideTA11_card_scalars_dvd {K : Type} [Field K] [Finite K] {n : ℕ}
    (H : Subgroup (GL (Fin n) K)) :
    Nat.card ((StatedScalars (Fin n) K).subgroupOf H) ∣ Nat.card K - 1 := by
  have h1 : Nat.card ((StatedScalars (Fin n) K).subgroupOf H) ∣
      Nat.card (StatedScalars (Fin n) K) :=
    Subgroup.card_dvd_of_injective
      ((H.subtype.comp ((StatedScalars (Fin n) K).subgroupOf H).subtype).codRestrict _
        fun x => Subgroup.mem_subgroupOf.mp x.2)
      fun x y hxy => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : StatedScalars (Fin n) K => (z : GL (Fin n) K)) hxy
  have h2 : Nat.card (StatedScalars (Fin n) K) ∣ Nat.card Kˣ := Subgroup.card_range_dvd _
  rw [Nat.card_units] at h2
  exact h1.trans h2

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial in
private theorem burnsideTA11_PSL3_local_ne {T : Type} [Group T] [Finite T] {K : Type} [Field K]
    [Finite K]
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (e : T ≃* StatedProj (StatedSL 3 K)) {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) :
    twoLocalPrimeRank r T ≤ 2 := by
  have hchar := burnsideTA11_charP_of_card hp hf hK
  have hrK : (r : K) ≠ 0 := burnsideTA11_natCast_ne_zero hp hr hrp
  have hbound : ∀ E ≤ StatedSL 3 K, (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) →
      (∀ g ∈ E, g ^ r = 1) → Nat.card E ≤ r ^ 2 := by
    intro E hE hcomm hexp
    have := burnsideTA11_card_le_of_det_eq_one hr.ne_zero hrK (0 : Fin 3) E hcomm hexp
      (fun x hx => CFSG.Open.StatedAPI.det_of_mem_statedSL (hE hx))
    simpa using this
  have hP : CFSG.pRank r (StatedProj (StatedSL 3 K)) ≤ 2 := by
    by_cases hr3 : r = 3
    · subst hr3
      by_cases h3 : 3 ∣ p ^ f - 1
      · have := CFSG.SectionRank.QTK.CentreFact.small_pRank_three_statedSL_le_two hp hf hK h3
        rwa [CFSG.SectionRank.pRank_eq_open_pRank_top]
      · refine burnsideTA11_pRank_proj_le hr (fun hd => h3 ?_) hbound
        have := hd.trans (burnsideTA11_card_scalars_dvd (StatedSL 3 K))
        rwa [hK] at this
    · exact CFSG.RankThree.PartOne.pRank_statedProj_statedSL_le hr
        (fun h => hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h)) hbound
  calc twoLocalPrimeRank r T ≤ CFSG.pRank r T := burnsideTA11_twoLocal_le_pRank hr
    _ = CFSG.pRank r (StatedProj (StatedSL 3 K)) := CFSG.pRank_congr_of_mulEquiv e r
    _ ≤ 2 := hP

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial in
private theorem burnsideTA11_PSU3_local_ne {T : Type} [Group T] [Finite T] {K : Type} [Field K]
    [Finite K]
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2)
    (e : T ≃* StatedProj (StatedSU 3 (p ^ f) K)) {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) :
    twoLocalPrimeRank r T ≤ 2 := by
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData p f K := ⟨hp, hf, hK'⟩
  have hchar := burnsideTA11_charP_of_card hp (by omega) hK'
  have hrK : (r : K) ≠ 0 := burnsideTA11_natCast_ne_zero hp hr hrp
  have hbound : ∀ E ≤ StatedSU 3 (p ^ f) K, (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) →
      (∀ g ∈ E, g ^ r = 1) → Nat.card E ≤ r ^ 2 := by
    intro E hE hcomm hexp
    have := burnsideTA11_card_le_of_det_eq_one hr.ne_zero hrK (0 : Fin 3) E hcomm hexp
      (fun x hx => CFSG.Open.StatedAPI.det_of_mem_statedSU (hE hx))
    simpa using this
  have hcard : Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K)) =
      Nat.gcd 3 (p ^ f + 1) := by
    rw [← unitaryScalars_eq hU (by norm_num), card_unitaryScalars hU (by norm_num)]
  have hP : CFSG.pRank r (StatedProj (StatedSU 3 (p ^ f) K)) ≤ 2 := by
    by_cases hr3 : r = 3
    · subst hr3
      by_cases h3 : 3 ∣ p ^ f + 1
      · have := CFSG.LieType.SeitzGeneration.pRank_three_projSU_three_le hU h3
        rwa [CFSG.SectionRank.pRank_eq_open_pRank_top]
      · refine burnsideTA11_pRank_proj_le hr (fun hd => h3 ?_) hbound
        rw [hcard] at hd
        exact hd.trans (Nat.gcd_dvd_right _ _)
    · refine burnsideTA11_pRank_proj_le hr (fun hd => hr3 ?_) hbound
      rw [hcard] at hd
      exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hd.trans (Nat.gcd_dvd_left _ _))
  calc twoLocalPrimeRank r T ≤ CFSG.pRank r T := burnsideTA11_twoLocal_le_pRank hr
    _ = CFSG.pRank r (StatedProj (StatedSU 3 (p ^ f) K)) := CFSG.pRank_congr_of_mulEquiv e r
    _ ≤ 2 := hP

end ModelNe

section Small

private theorem burnsideTA11_local_le_two_of_card {T : Type*} [Group T] [Finite T]
    (h : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ^ 3 ∣ Nat.card T) :
    ∀ r : ℕ, r.Prime → r ≠ 2 → twoLocalPrimeRank r T ≤ 2 := by
  intro r hr hr2
  refine csSup_le' ?_
  rintro _ ⟨H, -, rfl⟩
  refine CFSG.SectionRank.pRank_le hr.one_lt fun E _ hE => ?_
  haveI : Fact r.Prime := ⟨hr⟩
  have hEp : IsPGroup r E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  rw [hk]
  by_contra hgt
  have hk3 : 3 ≤ k := by
    by_contra hlt
    exact hgt (Nat.pow_le_pow_right hr.pos (by omega))
  exact h r hr hr2 ((pow_dvd_pow r hk3).trans (hk ▸ Subgroup.card_subgroup_dvd_card E))

private theorem burnsideTA11_not_cube_dvd {N r : ℕ} (hN : N = 2520 ∨ N = 7920 ∨ N = 62400)
    (hr : r.Prime) (hr2 : r ≠ 2) : ¬ r ^ 3 ∣ N := by
  intro h
  have hN0 : 0 < N := by rcases hN with rfl | rfl | rfl <;> norm_num
  have hle : r ^ 3 ≤ N := Nat.le_of_dvd hN0 h
  have hr40 : r < 40 := by
    by_contra hge
    push Not at hge
    have : 40 ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left hge 3
    rcases hN with rfl | rfl | rfl <;> omega
  interval_cases r <;> first | exact absurd rfl hr2 | (revert hr; decide) |
    (rcases hN with rfl | rfl | rfl <;> norm_num at h)

end Small

section Embed

open Matrix in
@[expose] def burnsideTA11_blockMat {K : Type} [Field K] (M : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 3) (Fin 3) K :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, 1]

open Matrix in
private theorem burnsideTA11_blockMat_mul {K : Type} [Field K] (M N : Matrix (Fin 2) (Fin 2) K) :
    burnsideTA11_blockMat (M * N) = burnsideTA11_blockMat M * burnsideTA11_blockMat N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideTA11_blockMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

open Matrix in
private theorem burnsideTA11_blockMat_one {K : Type} [Field K] :
    burnsideTA11_blockMat (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideTA11_blockMat]

open Matrix in
private theorem burnsideTA11_blockMat_det {K : Type} [Field K] (M : Matrix (Fin 2) (Fin 2) K) :
    (burnsideTA11_blockMat M).det = M.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_three]
  simp [burnsideTA11_blockMat]

open Matrix in
@[expose] def burnsideTA11_block (K : Type) [Field K] :
    SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K where
  toFun A := ⟨burnsideTA11_blockMat (A : Matrix (Fin 2) (Fin 2) K), by
    rw [burnsideTA11_blockMat_det]; exact A.2⟩
  map_one' := by
    apply Subtype.ext
    exact burnsideTA11_blockMat_one
  map_mul' A B := by
    apply Subtype.ext
    exact burnsideTA11_blockMat_mul _ _

open Matrix in
private theorem burnsideTA11_block_coe {K : Type} [Field K] (A : SpecialLinearGroup (Fin 2) K) :
    ((burnsideTA11_block K A : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      burnsideTA11_blockMat (A : Matrix (Fin 2) (Fin 2) K) := rfl

open Matrix in
private theorem burnsideTA11_embed_PSL3 {K : Type} [Field K] :
    ∃ φ : SpecialLinearGroup (Fin 2) K →* StatedProj (StatedSL 3 K), Function.Injective φ := by
  refine ⟨(QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))).comp
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom.comp
      (burnsideTA11_block K)), ?_⟩
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hA
  obtain ⟨c, hc⟩ := hA
  have hmat : burnsideTA11_blockMat (A : Matrix (Fin 2) (Fin 2) K) =
      Matrix.scalar (Fin 3) (c : K) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
    rw [Matrix.GeneralLinearGroup.coe_scalar] at this
    exact this.symm
  have h22 := congrFun (congrFun hmat 2) 2
  have hc1 : (c : K) = 1 := by
    simpa [burnsideTA11_blockMat] using h22.symm
  have e00 := congrFun (congrFun hmat 0) 0
  have e01 := congrFun (congrFun hmat 0) 1
  have e10 := congrFun (congrFun hmat 1) 0
  have e11 := congrFun (congrFun hmat 1) 1
  simp [burnsideTA11_blockMat, hc1] at e00 e01 e10 e11
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial in
open Matrix in
private theorem burnsideTA11_embed_PSU3 {T : Type} [Group T] [Finite T] {K : Type} [Field K]
    [Finite K]
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2)
    (e : T ≃* StatedProj (StatedSU 3 (p ^ f) K)) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = p ^ f ∧
      ∃ φ : SpecialLinearGroup (Fin 2) K' →* T, Function.Injective φ := by
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hU : UnitaryFieldData p f K := ⟨hp, hf, hK'⟩
  haveI := hU.finite
  obtain ⟨ψ⟩ := CFSG.RankThree.Classical.nonempty_coordBlock_mulEquiv hU (0 : Fin 3)
  have hinj := CFSG.RankThree.Classical.injective_unitaryProj_comp_coordBlock hU (0 : Fin 3)
  refine ⟨↥hU.fixedField, inferInstance, inferInstance, UnitaryFieldData.card_fixedField hU,
    e.symm.toMonoidHom.comp ((unitaryPSUEquiv hU (by norm_num : 1 ≤ 3)).toMonoidHom.comp
      ((unitaryProj hU 3).comp
        ((CFSG.RankThree.Classical.coordBlock p f K 0).subtype.comp ψ.symm.toMonoidHom))), ?_⟩
  intro a b hab
  have h1 : (unitaryPSUEquiv hU (by norm_num : 1 ≤ 3))
      (unitaryProj hU 3 ((CFSG.RankThree.Classical.coordBlock p f K 0).subtype (ψ.symm a))) =
      (unitaryPSUEquiv hU (by norm_num : 1 ≤ 3))
      (unitaryProj hU 3 ((CFSG.RankThree.Classical.coordBlock p f K 0).subtype (ψ.symm b))) :=
    e.symm.injective hab
  have h2 := (unitaryPSUEquiv hU (by norm_num : 1 ≤ 3)).injective h1
  exact ψ.symm.injective (hinj h2)

end Embed

section Dichotomy


private theorem burnsideTA11_rank_two_dichotomy : burnsideTA11_Rank2Fact := by
  intro T _ _ hs hnab hrank
  have h2 : CFSG.Open.pRank 2 (⊤ : Subgroup T) ≤ 2 := hrank.le
  rcases CFSG.Milestones.lr_rank_two_isomorphism_types T hnab hrank with
    ⟨p, f, hp, hp2, hf, hM⟩ | ⟨p, f, hp, hp2, hf, hM⟩ | ⟨p, f, hp, hp2, hf, hM⟩ | hM |
    he | he
  ·
    left
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hM
    exact burnsideTA11_PSL2_local hp hp2 hf hK e h2
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hM
    by_cases hf2 : f ≤ 2
    · left
      intro r hr hr2
      by_cases hrp : r = p
      · subst hrp
        exact burnsideTA11_PSL3_local_s hr hp2 hf hf2 hK e h2
      · exact burnsideTA11_PSL3_local_ne hp hf hK e hr hrp
    · right
      obtain ⟨φ, hφ⟩ := burnsideTA11_embed_PSL3 (K := K)
      exact ⟨p, f, hp, hp2, by omega, Or.inl hM, K, inferInstance, inferInstance, hK,
        e.symm.toMonoidHom.comp φ, e.symm.injective.comp hφ⟩
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hM
    by_cases hf2 : f ≤ 2
    · left
      intro r hr hr2
      by_cases hrp : r = p
      · subst hrp
        exact burnsideTA11_PSU3_local_s hr hp2 hf hf2 hK e h2
      · exact burnsideTA11_PSU3_local_ne hp hf hK e hr hrp
    · right
      obtain ⟨K', _, _, hK', φ, hφ⟩ := burnsideTA11_embed_PSU3 hp hf hK e
      exact ⟨p, f, hp, hp2, by omega, Or.inr hM, K', inferInstance, inferInstance, hK', φ, hφ⟩
  ·
    left
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hM
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hchar := burnsideTA11_charP_of_card Nat.prime_two (by norm_num : 1 ≤ 4) (by
      rw [hK]; norm_num : Nat.card K = 2 ^ 4)
    have hcardH : Nat.card (StatedSU 3 (2 ^ 2) K) = 62400 := by
      rw [CFSG.SectionRank.OddCover.card_statedSU_three hK]
      norm_num
    have hdvd : Nat.card T ∣ 62400 := by
      rw [Nat.card_congr e.toEquiv, ← hcardH]
      exact Subgroup.card_quotient_dvd_card _
    exact burnsideTA11_local_le_two_of_card fun r hr hr2 h3 =>
      burnsideTA11_not_cube_dvd (Or.inr (Or.inr rfl)) hr hr2 (h3.trans hdvd)
  ·
    left
    obtain ⟨e⟩ := he
    have hcard : Nat.card T = 2520 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    exact burnsideTA11_local_le_two_of_card fun r hr hr2 h3 =>
      burnsideTA11_not_cube_dvd (Or.inl rfl) hr hr2 (hcard ▸ h3)
  ·
    left
    obtain ⟨e⟩ := he
    have hcard : Nat.card T = 7920 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Semidihedral.GL2Recognition.card_lowTwoRankStatedM11
    exact burnsideTA11_local_le_two_of_card fun r hr hr2 h3 =>
      burnsideTA11_not_cube_dvd (Or.inr (Or.inl rfl)) hr hr2 (hcard ▸ h3)

end Dichotomy

end BurnsideTA11

section

theorem as_A_2_11
    : A_2_11 := by
  intro G _ _ S _ _ p hmin
  exact burnsideTA11_main burnsideTA11_rank_two_dichotomy
    CFSG.SectionRank.QTK.CentreFact.qtCentreFact_holds CFSG.SectionRank.catalogStepHyp hmin

end

@[expose] def A_2_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G → ¬ TheoremAHolds G →
    IsQuasisimple G

@[expose] def A_2_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    (IsSimpleGroup G ∧ (¬ TheoremBHolds G ∨ ¬ TheoremCHolds G)) ∨
    (IsQuasisimple G ∧ ¬ IsSimpleGroup G ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p (Subgroup.center G) ∧
      ∃ (Z : Subgroup G) (_ : Z.Normal), Z ≠ ⊥ ∧ Z ≤ Subgroup.center G ∧
        evenRank G ≤ 2 ∧ CFSG.SectionRank.IsKGroupCat G ∧ IsSectionOf (G ⧸ Z) G ∧
        genFittingLayer (G ⧸ Z) = ⊤ ∧ ¬ TheoremAConclusion G (G ⧸ Z) p ∧
        ∀ (q : ℕ), q.Prime → q ≠ 2 →
          ∀ (S : Type) [Group S] [Finite S], IsSectionOf S G → genFittingLayer S = ⊤ →
            ¬ TheoremAConclusion G S q → q = p)

@[expose] def A_2_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → IsPGroup p (Subgroup.center G) →
    ∀ (Z : Subgroup G) (_ : Z.Normal), Z ≠ ⊥ → Z ≤ Subgroup.center G →
      genFittingLayer (G ⧸ Z) = ⊤ → ¬ TheoremAConclusion G (G ⧸ Z) p →
      2 < pRank p (⊤ : Subgroup (G ⧸ Z)) ∧
      (Nat.card (Subgroup.center G) = p →
        2 < pRank p (⊤ : Subgroup (G ⧸ Subgroup.center G)))

theorem as_A_2_14 : A_2_14 := by
  intro G _ _ hmin p hp hp2 _ Z _ hZ1 hZc _ hnA
  obtain ⟨hev, -⟩ := a214_evenRank_le_two_and_isKGroupCat_of_minimalCounterexampleABC hmin
  have key : 2 < pRank p (⊤ : Subgroup (G ⧸ Z)) := by
    by_contra hle
    obtain ⟨hr1, hr2⟩ := (as_A_2_7 G Z p hp hp2).2.2.2.2 (not_lt.mp hle)
    apply hnA
    unfold TheoremAConclusion
    exact ⟨Or.inl ⟨hr2, (a27_twoLocalPrimeRank_le_evenRank hp hp2).trans hev⟩, fun _ => hr1⟩
  refine ⟨key, fun hcard => ?_⟩
  have hZdvd : Nat.card Z ∣ Nat.card (Subgroup.center G) := Subgroup.card_dvd_of_le hZc
  rw [hcard] at hZdvd
  have hZne : Nat.card Z ≠ 1 := fun h => hZ1 (Subgroup.card_eq_one.mp h)
  have hZeq : Z = Subgroup.center G := by
    refine Subgroup.eq_of_le_of_card_ge hZc ?_
    rw [hcard]
    rcases (Nat.dvd_prime hp).mp hZdvd with h | h
    · exact absurd h hZne
    · exact h.ge
  subst hZeq
  exact key

@[expose] def A_2_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    ∀ M : Subgroup G, M < ⊤ → ∀ (R : Type) [Group R] [Finite R], IsSectionOf R ↥M →
      genFittingLayer R = ⊤ → ∀ r : ℕ, r.Prime → r ≠ 2 →
      (pRank r (⊤ : Subgroup G) ≤ 2 →
        pRank r (⊤ : Subgroup R) ≤ pRank r M ∧ pRank r M ≤ pRank r (⊤ : Subgroup G)) ∧
      (IsTwoLocal M →
        pRank r (⊤ : Subgroup R) ≤ pRank r M ∧ pRank r M ≤ twoLocalPrimeRank r G ∧
          twoLocalPrimeRank r G ≤ 2) ∧
      (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        TheoremBList R ∧ (IsTwoLocal M → CFSG.Milestones.SQTKSimpleList R))

theorem as_A_2_15 : A_2_15 := by
  intro G _ _ hmin M hM R _ _ hRsec hRss r hr hr2
  obtain ⟨hev, hKG⟩ := burnside_evenRank_isKGroup_of_minimalABC hmin
  have hMne : M ≠ ⊤ := lt_top_iff_ne_top.mp hM
  have hMprop : IsProperSectionOf ↥M G := burnside_isProperSectionOf_subgroup M hMne
  have hAM : TheoremAHolds ↥M := (hmin.2 ↥M hMprop).1
  have hevM : evenRank ↥M ≤ 2 :=
    (burnside_evenRank_le_of_injective M.subtype M.subtype_injective).trans hev
  have hKM : CFSG.SectionRank.IsKGroupCat ↥M := hKG.subgroup M
  have hconc := (hAM hevM hKM R hRsec hRss).1
  have hAq : ∀ q : ℕ, q.Prime → q ≠ 2 →
      (CFSG.pRank q ↥M ≤ 2 → CFSG.pRank q R ≤ CFSG.pRank q ↥M) := by
    intro q hq hq2 h
    have hh := hconc q hq hq2
    unfold TheoremAConclusion at hh
    have h2 := hh.2
    simp only [burnside_pRank_top_eq] at h2
    exact h2 h
  have hMloc : ∀ q : ℕ, q.Prime → IsTwoLocal M → CFSG.pRank q ↥M ≤ twoLocalPrimeRank q G := by
    intro q hq hT
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact le_csSup ⟨Nat.card G, by
      rintro _ ⟨K, -, rfl⟩
      exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt K⟩ ⟨M, hT, rfl⟩
  have hloc2 : ∀ q : ℕ, q.Prime → q ≠ 2 → twoLocalPrimeRank q G ≤ 2 := fun q hq hq2 =>
    (burnside_twoLocalPrimeRank_le_evenRank hq hq2).trans hev
  have hMG : CFSG.pRank r ↥M ≤ CFSG.pRank r G :=
    burnside_pRank_le_of_injective hr.one_lt M.subtype M.subtype_injective
  refine ⟨fun hG => ?_, fun hT => ?_, fun hsimple hnab => ?_⟩
  · simp only [burnside_pRank_top_eq] at hG ⊢
    exact ⟨hAq r hr hr2 (hMG.trans hG), hMG⟩
  · simp only [burnside_pRank_top_eq]
    have hle := hMloc r hr hT
    exact ⟨hAq r hr hr2 (hle.trans (hloc2 r hr hr2)), hle, hloc2 r hr hr2⟩
  · haveI : IsSimpleGroup R := hsimple
    have hRsecG : IsSectionOf R G := burnside_isSectionOf_subgroup M hRsec
    have hRprop : IsProperSectionOf R G :=
      ⟨hRsecG, lt_of_le_of_lt (burnside_card_section_le hRsec)
        (lt_of_le_of_ne (Subgroup.card_le_card_group M)
          fun h => hMne ((Subgroup.card_eq_iff_eq_top M).mp h))⟩
    obtain ⟨-, hB, hC⟩ := hmin.2 R hRprop
    have hKR : CFSG.SectionRank.IsKGroupCat R := by
      obtain ⟨H, K, hK, ⟨e⟩⟩ := hRsec
      exact ((hKM.subgroup H).quotient (K.subgroupOf H)).of_mulEquiv e
    have hevR : evenRank R ≤ 2 := by
      refine csSup_le' ?_
      rintro _ ⟨q, L, hq, hq2, hL, rfl⟩
      have hcq := hconc q hq hq2
      unfold TheoremAConclusion at hcq
      obtain ⟨hcq1, -⟩ := hcq
      rcases hcq1 with ⟨ha, hb⟩ | ⟨-, H, H₁, H₂, n₁, n₂, ⟨e⟩, hr3, hsup, hc1, hc2, hs1, -⟩
      · refine le_trans ?_ (ha.trans hb)
        exact le_csSup ⟨Nat.card R, by
          rintro _ ⟨K, -, rfl⟩
          exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt K⟩ ⟨L, hL, rfl⟩
      · exact (burnside_false_of_clauseB_simple hnab e hr3 hsup hc1 hc2 hs1).elim
    refine ⟨hB hsimple hnab hevR hKR, fun hT => ?_⟩
    have hsqt : CFSG.IsStronglyQuasithin R := by
      intro q hq hq2
      have h1 := hMloc q hq hT
      have h2 := hloc2 q hq hq2
      exact (hAq q hq hq2 (h1.trans h2)).trans (h1.trans h2)
    exact hC hsimple hnab ⟨hsqt, hKR⟩

@[expose] def A_2_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    ¬ ∃ n : ℕ, 5 ≤ n ∧ Nonempty ((G ⧸ Subgroup.center G) ≃* alternatingGroup (Fin n))

@[expose] def A_2_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    ¬ OddLieType (G ⧸ Subgroup.center G)

@[expose] def A_2_18 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    ¬ EvenLieType (G ⧸ Subgroup.center G)

@[expose] def A_2_19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    ¬ NativeSporadic.SporadicRep (G ⧸ Subgroup.center G)

section TheoremAReduction

open CFSG.Open CFSG.Blueprint
open CFSG.ASVolI.ChA
open scoped commutatorElement

open CFSG.SectionRank in
private theorem ta_exists_elemAbelian_of_preimage {G : Type} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (Z Zs : Subgroup G) [Z.Normal]
    (hZs : Zs ≤ Subgroup.center G) (hZZs : Z ≤ Zs) (hZcard : Nat.card Z = p)
    (hZscard : Nat.card Zs = p ^ 2) (hZsexp : ∀ z ∈ Zs, z ^ p = 1)
    (E : Subgroup (G ⧸ Z)) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3)
    (hW : ∀ z ∈ Zs, (QuotientGroup.mk' Z z) ∈ E) :
    ∃ F : Subgroup G, F ≤ E.comap (QuotientGroup.mk' Z) ∧ IsElemAbelian p F ∧
      Nat.card F = p ^ 3 := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  set P : Subgroup G := E.comap (QuotientGroup.mk' Z) with hP
  have hZP : Z ≤ P := fun a ha => by
    change (QuotientGroup.mk' Z) a ∈ E
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff a).2 ha]
    exact one_mem E
  have hZsP : Zs ≤ P := fun z hz => hW z hz
  have hPcard : Nat.card P = p ^ 4 := by
    have h1 : Nat.card P = Nat.card Z * Nat.card E :=
      QuotientGroup.card_preimage_mk Z (E : Set (G ⧸ Z))
    rw [h1, hZcard, hEcard]; ring
  have hEcomm := hE.1
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ Z := by
    intro x hx y hy
    rw [← QuotientGroup.eq_one_iff]
    have h1 : (⟨QuotientGroup.mk' Z x, hx⟩ : E) * ⟨QuotientGroup.mk' Z y, hy⟩ =
        ⟨QuotientGroup.mk' Z y, hy⟩ * ⟨QuotientGroup.mk' Z x, hx⟩ := mul_comm' _ _
    have h2 := congrArg Subtype.val h1
    change (QuotientGroup.mk' Z) (x * y * x⁻¹ * y⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    change (QuotientGroup.mk' Z x) * (QuotientGroup.mk' Z y) =
      (QuotientGroup.mk' Z y) * (QuotientGroup.mk' Z x) at h2
    rw [h2]
    group
  have hpow : ∀ x ∈ P, x ^ p ∈ Z := by
    intro x hx
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' Z) (x ^ p) = 1
    rw [map_pow]
    exact hE.2 _ hx
  have hcZ : ∀ x y : P, ((⁅x, y⁆ : P) : G) ∈ Z := fun x y => hcomm x x.2 y y.2
  have hc : ∀ x y z : P, Commute ⁅x, y⁆ z := fun x y z => by
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.1 (hZs (hZZs (hcZ x y))) (z : G)).symm
  have hcp : ∀ x y : P, ⁅x, y⁆ ^ p = 1 := fun x y => by
    apply Subtype.ext
    have h1 : (⟨((⁅x, y⁆ : P) : G), hcZ x y⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    rw [hZcard] at h1
    have h2 := congrArg Subtype.val h1
    exact h2
  set φ := CFSG.SectionRank.powHom hc hp.out hp2 hcp with hφ
  have hrange : φ.range ≤ Z.subgroupOf P := by
    rintro _ ⟨x, rfl⟩
    exact hpow x x.2
  have hKcard : p ^ 3 ≤ Nat.card φ.ker := by
    have h1 : Nat.card P = Nat.card (P ⧸ φ.ker) * Nat.card φ.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h2 : Nat.card (P ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    have h3 : Nat.card φ.range ≤ Nat.card (Z.subgroupOf P) := Subgroup.card_le_of_le hrange
    have h4 : Nat.card (Z.subgroupOf P) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZcard]
    rw [h2] at h1
    have h5 : p ^ 4 ≤ p * Nat.card φ.ker := by
      calc p ^ 4 = Nat.card P := hPcard.symm
        _ = Nat.card φ.range * Nat.card φ.ker := h1
        _ ≤ p * Nat.card φ.ker := Nat.mul_le_mul_right _ (h4 ▸ h3)
    have h6 : p * p ^ 3 ≤ p * Nat.card φ.ker := by
      calc p * p ^ 3 = p ^ 4 := by ring
        _ ≤ _ := h5
    exact Nat.le_of_mul_le_mul_left h6 hp.out.pos
  have hZsK : Zs.subgroupOf P ≤ φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact hZsexp _ (Subgroup.mem_subgroupOf.1 hz)
  have hZs'card : Nat.card (Zs.subgroupOf P) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZsP).toEquiv, hZscard]
  obtain ⟨y, hyK, hyZs⟩ : ∃ y ∈ φ.ker, y ∉ Zs.subgroupOf P := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (fun y hy => hcon y hy : φ.ker ≤ Zs.subgroupOf P)
    have h23 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp1 (by norm_num)
    omega
  have hy1 : (y : G) ^ p = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hyK)
  have hyn : (y : G) ∉ Zs := fun h => hyZs (Subgroup.mem_subgroupOf.2 h)
  have hcenZs : ∀ b : Zs, Commute ((Zs.subtype b : G)) (y : G) := fun b =>
    (Subgroup.mem_center_iff.1 (hZs b.2) (y : G)).symm
  obtain ⟨F', hF'inj, hF'comm, hF'pow, hF'card, hF'mem⟩ := CFSG.SectionRank.exists_extend
    (P := G) (p := p) (B := Zs) (fun a b => Subtype.ext ((Subgroup.mem_center_iff.1 (hZs b.2) a.1)))
    (fun a => Subtype.ext (hZsexp a.1 a.2)) hZscard Zs.subtype Zs.subtype_injective hy1
    (by rw [Subgroup.range_subtype]; exact hyn) hcenZs
  refine ⟨F'.range, ?_, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨a, rfl⟩
    obtain ⟨b, n, hbn⟩ := hF'mem a
    rw [hbn]
    exact mul_mem (hZsP b.2) (pow_mem y.2 n)
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    change F' a * F' b = F' b * F' a
    rw [← map_mul, ← map_mul, hF'comm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hF'pow, map_one]
  · exact (Nat.card_congr (MonoidHom.ofInjective hF'inj).toEquiv).symm.trans hF'card

open CFSG.SectionRank in
private theorem ta_lift_card_le {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (Z : Subgroup G) [Z.Normal] (hZc : Z ≤ Subgroup.center G)
    (hZcard : Nat.card Z = p) (hZscard : Nat.card (Subgroup.center G) = p ^ 2)
    (hZsexp : ∀ z ∈ Subgroup.center G, z ^ p = 1) (E : Subgroup (G ⧸ Z))
    (hE : IsElemAbelian p E) {k : ℕ} (hEk : Nat.card E = p ^ k)
    (hbd : Nat.card ((E.comap (QuotientGroup.mk' Z)).map
      (QuotientGroup.mk' (Subgroup.center G))) ≤ p ^ 2) :
    k ≤ 2 ∨ ∃ F : Subgroup G, F ≤ E.comap (QuotientGroup.mk' Z) ∧ IsElemAbelian p F ∧
      Nat.card F = p ^ 3 := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  set Eh : Subgroup G := E.comap (QuotientGroup.mk' Z) with hEh
  have hEhcard : Nat.card Eh = p * p ^ k := by
    have h1 : Nat.card Eh = Nat.card Z * Nat.card E :=
      QuotientGroup.card_preimage_mk Z (E : Set (G ⧸ Z))
    rw [h1, hZcard, hEk]
  set φ : Eh →* G ⧸ Subgroup.center G := (QuotientGroup.mk' (Subgroup.center G)).comp Eh.subtype
    with hφ
  have hrange : φ.range = Eh.map (QuotientGroup.mk' (Subgroup.center G)) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = (Subgroup.center G).subgroupOf Eh := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hinf : Nat.card ((Subgroup.center G).subgroupOf Eh) =
      Nat.card ↥((Subgroup.center G) ⊓ Eh) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective Eh.subtype_injective]
  have hmcard : Nat.card φ.ker ≤ p ^ 2 := by
    rw [hker, hinf, ← hZscard]
    exact Subgroup.card_le_of_le inf_le_left
  have hfac : Nat.card Eh = Nat.card φ.range * Nat.card φ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hrcard : Nat.card φ.range ≤ p ^ 2 := by rw [hrange]; exact hbd
  have hmain : p * p ^ k ≤ p ^ 2 * p ^ 2 := by
    calc p * p ^ k = Nat.card Eh := hEhcard.symm
      _ = Nat.card φ.range * Nat.card φ.ker := hfac
      _ ≤ p ^ 2 * p ^ 2 := Nat.mul_le_mul hrcard hmcard
  by_cases hk2 : k ≤ 2
  · exact Or.inl hk2
  right
  have hk3 : k = 3 := by
    by_contra hne
    have hk4 : 4 ≤ k := by omega
    have : p ^ 5 ≤ p ^ 4 := by
      calc p ^ 5 = p * p ^ 4 := by ring
        _ ≤ p * p ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.out.pos hk4)
        _ ≤ p ^ 2 * p ^ 2 := hmain
        _ = p ^ 4 := by ring
    have := Nat.pow_lt_pow_right hp1 (show 4 < 5 by norm_num)
    omega
  subst hk3
  have hmeq : Nat.card φ.ker = p ^ 2 := by
    have h1 : p ^ 4 ≤ p ^ 2 * Nat.card φ.ker := by
      calc p ^ 4 = Nat.card Eh := by rw [hEhcard]; ring
        _ = Nat.card φ.range * Nat.card φ.ker := hfac
        _ ≤ p ^ 2 * Nat.card φ.ker := Nat.mul_le_mul_right _ hrcard
    have h2 : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card φ.ker := by
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ _ := h1
    have h3 : p ^ 2 ≤ Nat.card φ.ker :=
      Nat.le_of_mul_le_mul_left h2 (pow_pos hp.out.pos 2)
    omega
  have hcenEh : Subgroup.center G ≤ Eh := by
    have h1 : Nat.card ↥((Subgroup.center G) ⊓ Eh) = p ^ 2 := by
      rw [← hinf, ← hker]
      exact hmeq
    have h2 : (Subgroup.center G) ⊓ Eh = Subgroup.center G :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hZscard])
    exact h2 ▸ inf_le_right
  exact ta_exists_elemAbelian_of_preimage hp2 Z (Subgroup.center G) le_rfl hZc hZcard hZscard
    hZsexp E hE hEk (fun z hz => hcenEh hz)

private theorem ta_card_eq_pow_of_isElemAbelian {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {E : Subgroup X} (hE : IsElemAbelian p E) : ∃ k : ℕ, Nat.card E = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact IsPGroup.iff_card.1 fun g => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hE.2 _ g.2)⟩

private theorem ta_card_le_of_pRank {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {H E : Subgroup X} (hH : CFSG.Open.pRank p H ≤ 2) (hEH : E ≤ H) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 2 := by
  obtain ⟨k, hk⟩ := ta_card_eq_pow_of_isElemAbelian hp hE
  have := CFSG.SectionRank.le_pRank hp.one_lt hEH hE hk
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos (this.trans hH)

private theorem ta_map_ne_bot {X Y : Type*} [Group X] [Group Y] {p : ℕ} (hp2 : p ≠ 2) (hp : p.Prime)
    (f : X →* Y) (hker : ∀ x ∈ f.ker, x ^ p = 1) {R : Subgroup X} (hR : R ≠ ⊥)
    (hR2 : IsPGroup 2 R) : R.map f ≠ ⊥ := by
  intro hbot
  apply hR
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxk : x ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    have : f x ∈ R.map f := Subgroup.mem_map_of_mem f hx
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  obtain ⟨m, hm⟩ := hR2 ⟨x, hx⟩
  have hm' : x ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have h1 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
  have h2 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hker x hxk)
  have hcop : Nat.Coprime (2 ^ m) p :=
    Nat.Coprime.pow_left m ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h3 : Nat.Coprime (orderOf x) p := Nat.Coprime.coprime_dvd_left h1 hcop
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h3 h2)

private theorem ta_pRank_top_eq {X : Type*} [Group X] [Finite X] (p : ℕ) :
    CFSG.pRank p ↥(⊤ : Subgroup X) = CFSG.pRank p X := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top p ↥(⊤ : Subgroup X),
    CFSG.SectionRank.pRank_eq_open_pRank_top p X,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup X)]

private theorem ta_twoLocalPrimeRank_le_evenRank {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : twoLocalPrimeRank p X ≤ evenRank X := by
  refine csSup_le' ?_
  rintro _ ⟨H, hH, rfl⟩
  refine le_csSup ⟨Nat.card X, ?_⟩ ⟨p, H, hp, hp2, hH, rfl⟩
  rintro _ ⟨q, K, hq, -, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt K

private theorem ta_twoLocalPrimeRank_le_two_of_bound {X : Type*} [Group X] [Finite X] {p : ℕ}
    (h : ∀ R : Subgroup X, R ≠ ⊥ → IsPGroup 2 R →
      CFSG.Open.pRank p (Subgroup.normalizer (R : Set X)) ≤ 2) :
    twoLocalPrimeRank p X ≤ 2 := by
  refine csSup_le' ?_
  rintro _ ⟨H, ⟨R, hR, hR2, rfl⟩, rfl⟩
  exact h R hR hR2

@[expose] def QTCentreRankDown : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → CFSG.SectionRank.IsKGroupCat K →
    CFSG.Open.evenRank K ≤ 2 → ∀ r : ℕ, r.Prime → r ≠ 2 → IsPGroup r ↥(Subgroup.center K) →
      Subgroup.center K ≠ ⊥ → CFSG.pRank r K ≤ 2 → CFSG.pRank r (K ⧸ Subgroup.center K) ≤ 2

private theorem ta_caseII_big (hC : CFSG.SectionRank.QTK.QTCentreFact) (hRd : QTCentreRankDown)
    {G : Type} [Group G] [Finite G] (hq : CFSG.IsQuasisimple G) (hev : evenRank G ≤ 2)
    (hK : CFSG.SectionRank.IsKGroupCat G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Z : Subgroup G) [Z.Normal] (hZc : Z ≤ Subgroup.center G) (hZcard : Nat.card Z = p)
    (hZscard : Nat.card (Subgroup.center G) = p ^ 2)
    (hZsexp : ∀ z ∈ Subgroup.center G, z ^ p = 1) : TheoremAConclusion G (G ⧸ Z) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hpc : p ∣ Nat.card (Subgroup.center G) := by
    rw [hZscard]; exact dvd_pow_self p (by norm_num)
  set f : G ⧸ Z →* G ⧸ Subgroup.center G :=
    QuotientGroup.map Z (Subgroup.center G) (MonoidHom.id G) (by rw [Subgroup.comap_id]; exact hZc)
    with hf
  have hfπ : ∀ g : G, f (QuotientGroup.mk' Z g) = QuotientGroup.mk' (Subgroup.center G) g :=
    fun g => rfl
  have hcomp : QuotientGroup.mk' (Subgroup.center G) = f.comp (QuotientGroup.mk' Z) :=
    MonoidHom.ext hfπ
  have himg : ∀ E : Subgroup (G ⧸ Z), (E.comap (QuotientGroup.mk' Z)).map
      (QuotientGroup.mk' (Subgroup.center G)) = E.map f := by
    intro E
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective Z)]
  have hkerf : ∀ x ∈ f.ker, x ^ p = 1 := by
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MonoidHom.mem_ker] at hx
    have hg : g ∈ Subgroup.center G := by
      have : QuotientGroup.mk' (Subgroup.center G) g = 1 := hx
      exact (QuotientGroup.eq_one_iff g).1 this
    rw [← QuotientGroup.mk_pow, hZsexp g hg, QuotientGroup.mk_one]
  have hlift : ∀ (E : Subgroup (G ⧸ Z)) {k : ℕ}, IsElemAbelian p E → Nat.card E = p ^ k →
      Nat.card (E.map f) ≤ p ^ 2 → k ≤ 2 ∨ ∃ F : Subgroup G,
        F ≤ E.comap (QuotientGroup.mk' Z) ∧ IsElemAbelian p F ∧ Nat.card F = p ^ 3 :=
    fun E k hE hk hbd => ta_lift_card_le hp2 Z hZc hZcard hZscard hZsexp E hE hk
      (by rw [himg]; exact hbd)
  have hloc : twoLocalPrimeRank p (G ⧸ Z) ≤ 2 := by
    refine ta_twoLocalPrimeRank_le_two_of_bound fun R hR hR2 => ?_
    refine CFSG.SectionRank.pRank_le hp1 fun E hEH hE => ?_
    obtain ⟨k, hk⟩ := ta_card_eq_pow_of_isElemAbelian hp hE
    have hR' : R.map f ≠ ⊥ := ta_map_ne_bot hp2 hp f hkerf hR hR2
    have hEN : E.map f ≤ Subgroup.normalizer ((R.map f : Subgroup _) : Set _) :=
      (Subgroup.map_mono hEH).trans (Subgroup.le_normalizer_map f)
    have hbd : Nat.card (E.map f) ≤ p ^ 2 :=
      ta_card_le_of_pRank hp (hC G hq hK hev p hp hp2 hpc (R.map f) hR' (hR2.map f)) hEN
        (CFSG.Open.IsElemAbelian.map hE f)
    rcases hlift E hE hk hbd with hk2 | ⟨F, hFP, hFe, hFc⟩
    · rw [hk]; exact Nat.pow_le_pow_right hp.pos hk2
    · exfalso
      obtain ⟨R₂, hR₂1, hR₂2, hR₂N⟩ :=
        CFSG.SectionRank.QTK.exists_two_subgroup_normalized (Y := G) hR' (hR2.map f)
      have hFN : F ≤ Subgroup.normalizer (R₂ : Set G) := by
        intro w hw
        apply hR₂N w
        have h1 : QuotientGroup.mk' Z w ∈ Subgroup.normalizer (R : Set (G ⧸ Z)) :=
          hEH (hFP hw)
        have h2 := Subgroup.le_normalizer_map f ⟨_, h1, rfl⟩
        exact h2
      have := CFSG.SectionRank.QTK.le_two_of_evenRank_le_two hev hR₂1 hR₂2 hp hp2 hFe hFN hFc
      omega
  have hrk : CFSG.pRank p G ≤ 2 → CFSG.pRank p ↥(⊤ : Subgroup (G ⧸ Z)) ≤ 2 := by
    intro hG'
    have hQ : CFSG.Open.pRank p (⊤ : Subgroup (G ⧸ Subgroup.center G)) ≤ 2 := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
      refine hRd G hq hK hev p hp hp2 (IsPGroup.of_card hZscard) ?_ hG'
      intro hbot
      rw [hbot, Subgroup.card_bot] at hZscard
      have := hp.one_lt
      nlinarith
    rw [ta_pRank_top_eq, CFSG.SectionRank.pRank_eq_open_pRank_top]
    refine CFSG.SectionRank.pRank_le hp1 fun E _ hE => ?_
    obtain ⟨k, hk⟩ := ta_card_eq_pow_of_isElemAbelian hp hE
    have hbd : Nat.card (E.map f) ≤ p ^ 2 :=
      ta_card_le_of_pRank hp hQ le_top (CFSG.Open.IsElemAbelian.map hE f)
    rcases hlift E hE hk hbd with hk2 | ⟨F, -, hFe, hFc⟩
    · rw [hk]; exact Nat.pow_le_pow_right hp.pos hk2
    · exfalso
      have h3 := CFSG.SectionRank.le_pRank hp1 (le_top : F ≤ ⊤) hFe hFc
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h3
      omega
  have h7 := as_A_2_7 G Z p hp hp2
  unfold TheoremAConclusion
  refine ⟨Or.inl ⟨h7.2.2.2.1 hloc, (ta_twoLocalPrimeRank_le_evenRank hp hp2).trans hev⟩, ?_⟩
  intro hG
  have hG' : CFSG.pRank p G ≤ 2 := by
    rwa [ta_pRank_top_eq] at hG
  exact h7.2.2.1 (hrk hG')


@[expose] def QTCentreShape : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → CFSG.SectionRank.IsKGroupCat K →
    CFSG.Open.evenRank K ≤ 2 → ∀ r : ℕ, r.Prime → r ≠ 2 → IsPGroup r ↥(Subgroup.center K) →
      Nat.card (Subgroup.center K) ∣ r ^ 2 ∧
        (r ^ 2 ∣ Nat.card (Subgroup.center K) → ∀ z ∈ Subgroup.center K, z ^ r = 1)

private theorem ta_caseII_small (hC : CFSG.SectionRank.QTK.QTCentreFact) (hRd : QTCentreRankDown)
    {G : Type} [Group G] [Finite G] (hq : CFSG.IsQuasisimple G) (hev : evenRank G ≤ 2)
    (hK : CFSG.SectionRank.IsKGroupCat G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpz : IsPGroup p ↥(Subgroup.center G)) (hZ1 : Subgroup.center G ≠ ⊥) :
    TheoremAConclusion G (G ⧸ Subgroup.center G) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpc : p ∣ Nat.card (Subgroup.center G) := by
    rcases hpz.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hZ1
    · exact h
  have hloc : twoLocalPrimeRank p (G ⧸ Subgroup.center G) ≤ 2 :=
    ta_twoLocalPrimeRank_le_two_of_bound (hC G hq hK hev p hp hp2 hpc)
  have h7 := as_A_2_7 G (Subgroup.center G) p hp hp2
  unfold TheoremAConclusion
  refine ⟨Or.inl ⟨h7.2.2.2.1 hloc, (ta_twoLocalPrimeRank_le_evenRank hp hp2).trans hev⟩, ?_⟩
  intro hG
  have hG' : CFSG.pRank p G ≤ 2 := by
    rwa [ta_pRank_top_eq] at hG
  have hQ : CFSG.pRank p ↥(⊤ : Subgroup (G ⧸ Subgroup.center G)) ≤ 2 := by
    rw [ta_pRank_top_eq]
    exact hRd G hq hK hev p hp hp2 hpz hZ1 hG'
  exact h7.2.2.1 hQ

private theorem ta_caseII (hC : CFSG.SectionRank.QTK.QTCentreFact) (hRd : QTCentreRankDown)
    (hSh : QTCentreShape) {G : Type} [Group G] [Finite G] (hq : CFSG.IsQuasisimple G)
    (hev : evenRank G ≤ 2) (hK : CFSG.SectionRank.IsKGroupCat G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpz : IsPGroup p ↥(Subgroup.center G)) (Z : Subgroup G) [Z.Normal]
    (hZ1 : Z ≠ ⊥) (hZc : Z ≤ Subgroup.center G) : TheoremAConclusion G (G ⧸ Z) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpZ : IsPGroup p ↥Z := hpz.of_injective _ (Subgroup.inclusion_injective hZc)
  have hpZd : p ∣ Nat.card Z := by
    rcases hpZ.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hZ1
    · exact h
  have hpc : p ∣ Nat.card (Subgroup.center G) := hpZd.trans (Subgroup.card_dvd_of_le hZc)
  by_cases hZeq : Z = Subgroup.center G
  · subst hZeq
    exact ta_caseII_small hC hRd hq hev hK hp hp2 hpz hZ1
  · obtain ⟨hdvd, hexp⟩ := hSh G hq hK hev p hp hp2 hpz
    obtain ⟨i, hi2, hi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hdZ : Nat.card Z ∣ Nat.card (Subgroup.center G) := Subgroup.card_dvd_of_le hZc
    have hne : ∀ h : Nat.card Z = Nat.card (Subgroup.center G), False := fun h =>
      hZeq (Subgroup.eq_of_le_of_card_ge hZc (by rw [h]))
    have hZpow : ∃ j, j ≤ 2 ∧ Nat.card Z = p ^ j :=
      (Nat.dvd_prime_pow hp).1 (hdZ.trans hdvd)
    obtain ⟨j, hj2, hj⟩ := hZpow
    have hj1 : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      rw [this, pow_zero] at hj
      exact hZ1 (Subgroup.card_eq_one.1 hj)
    have hi1 : 1 ≤ i := by
      by_contra h0
      have : i = 0 := by omega
      rw [this, pow_zero] at hi
      rw [hi] at hpc
      exact hp.one_lt.ne' (Nat.dvd_one.1 hpc)
    have hdZ' : p ^ j ∣ p ^ i := by
      rw [hj, hi] at hdZ
      exact hdZ
    have hji : j ≤ i := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdZ'
    have hi2' : i = 2 := by
      by_contra h
      have hi1' : i = 1 := by omega
      have hj1' : j = 1 := by omega
      exact hne (by rw [hj, hi, hj1', hi1'])
    subst hi2'
    have hj1' : j = 1 := by
      by_contra h
      have hj2' : j = 2 := by omega
      exact hne (by rw [hj, hi, hj2'])
    subst hj1'
    exact ta_caseII_big hC hRd hq hev hK hp hp2 Z hZc (by rw [hj, pow_one]) hi
      (hexp (by rw [hi]))


private theorem ta_pRank_le_two_of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] [Finite T]
    {r : ℕ} (hr : 1 < r) (e : S ≃* T) (h : CFSG.Open.pRank r (⊤ : Subgroup T) ≤ 2) :
    CFSG.pRank r S ≤ 2 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr e]
  exact h

section RankDown

open CFSG.SectionRank.QTK CFSG.SectionRank.QTK.CentreFact Subgroup


private theorem ta_rankDown_sub {G : Type} [Group G] [Finite G] (he : evenRank G ≤ 2) {Y :
    Subgroup G}
    (hq : CFSG.IsQuasisimple ↥Y) (hK : CFSG.SectionRank.IsKGroupCat ↥Y) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hpz : IsPGroup r ↥(center ↥Y)) (hZ1 : center ↥Y ≠ ⊥)
    (hrk : CFSG.pRank r ↥Y ≤ 2) : CFSG.pRank r (↥Y ⧸ center ↥Y) ≤ 2 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hrZ : r ∣ Nat.card (center ↥Y) := by
    rcases hpz.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hZ1
    · exact h
  have hT : TableRestricted (↥Y ⧸ center ↥Y) r := fun _ _ _ _ hm =>
    CoverB.tablePrime_of_dvd hq hm hr hr2 hrZ
  have hrk' : CFSG.Open.pRank r (⊤ : Subgroup ↥Y) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]; exact hrk
  have hrank3 : ∀ {t : StatedLieTag} {n p f : ℕ}, StatedClassicalModel (↥Y ⧸ center ↥Y) t n p f →
      r = 3 → (t = .PSL ∧ n = 3 ∧ 3 ∣ p ^ f - 1) ∨ (t = .PSU ∧ n = 3 ∧ 3 ∣ p ^ f + 1) →
      CFSG.pRank r (↥Y ⧸ center ↥Y) ≤ 2 := by
    intro t n p f hm hr3 hcase
    subst hr3
    rcases hcase with ⟨rfl, rfl, h3⟩ | ⟨rfl, rfl, h3⟩
    · obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
      exact ta_pRank_le_two_of_mulEquiv (by norm_num) e
        (small_pRank_three_statedSL_le_two hp hf hK h3)
    · obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
      have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
        ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
      exact ta_pRank_le_two_of_mulEquiv (by norm_num) e
        (CFSG.LieType.SeitzGeneration.pRank_three_projSU_three_le hU h3)
  have hu43 : StatedClassicalModel (↥Y ⧸ center ↥Y) .PSU 4 3 1 → r = 3 →
      CFSG.pRank r (↥Y ⧸ center ↥Y) ≤ 2 := by
    intro hm hr3
    subst hr3
    exfalso
    obtain ⟨-, -, hrank⟩ := CFSG.SectionRank.classical_model_rank (by norm_num) hm
    have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥Y ⧸ center ↥Y)) := by
      rcases hrank with ⟨h, -⟩ | ⟨-, ⟨h, -⟩ | h⟩ | ⟨h, -⟩ | h
      · exact absurd h (by decide)
      · exact absurd h (by norm_num)
      · exact h
      · exact absurd h (by decide)
      · exact h
    have h3 := CFSG.SectionRank.pRank_quotient_le_three (by norm_num) hrk' (center ↥Y) le_rfl
    omega
  rcases CoverB.qtkSimpleList_of_cover he hq hK with
    ⟨n, -, hn, ⟨e⟩⟩ | ⟨p, -, -, h⟩ | h | h | ⟨s, hs, ⟨e⟩⟩
  ·
    rcases Nat.lt_or_ge n 9 with h8 | h9
    · exact ta_pRank_le_two_of_mulEquiv hr.one_lt e
        (CFSG.SectionRank.pRank_alternating_le_two (by omega) hr hr2)
    · obtain rfl : n = 9 := by omega
      by_cases hr3 : r = 3
      · subst hr3
        exact absurd hrZ (not_three_dvd_card_center_of_alt_nine he e)
      · refine ta_pRank_le_two_of_mulEquiv hr.one_lt e
          (small_pRank_top_le_two_of_not_dvd hr ?_)
        rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
        intro hd
        have h2 : r ^ 2 ∣ 2 ^ 6 * 3 ^ 4 * 35 := by
          rw [show 2 ^ 6 * 3 ^ 4 * 35 = Nat.factorial 9 / 2 by decide]
          exact (pow_dvd_pow r (by norm_num : 2 ≤ 3)).trans hd
        exact CFSG.SectionRank.not_sq_dvd_of_not_sq_dvd_cofactor hr hr2 hr3
          (CFSG.SectionRank.not_sq_dvd_of_bound (B := 6) (by norm_num) (by norm_num) (by decide)
            hr hr2 hr3) h2
  ·
    rcases h with ⟨f, -, hm⟩ | ⟨f, -, hm | hm⟩ | hm | hm | ⟨-, hm⟩ | ⟨-, hm⟩
    · obtain ⟨rfl, rfl, rfl⟩ := tablePrime_psl_two hr hr2 (hT.classical hm)
      obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine hm
      exact ta_pRank_le_two_of_mulEquiv hr.one_lt e
        (CFSG.SectionRank.pRank_alternating_le_two (by norm_num) hr hr2)
    · obtain ⟨hr3, hrq⟩ := tablePrime_psl_three (hT.classical hm)
      exact hrank3 hm ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hr3)
        (Or.inl ⟨rfl, rfl, by
          rwa [(Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hr3] at hrq⟩)
    · obtain ⟨hr3, hrq⟩ := tablePrime_psu_three (hT.classical hm)
      exact hrank3 hm ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hr3)
        (Or.inr ⟨rfl, rfl, by
          rwa [(Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hr3] at hrq⟩)
    · exact absurd (hT.classical hm) not_tablePrime_psp
    · obtain ⟨rfl, rfl, -⟩ := tablePrime_g2 (hT.chevalley (by decide) hm)
      exfalso
      have h3 := (CFSG.SectionRank.g2_odd_central_cover_rank_three (center ↥Y) le_rfl hr hr2
        hm).1
      omega
    · exact absurd (hT.classical hm) (not_tablePrime_psl_four hr hr2)
    · obtain ⟨rfl, rfl, -⟩ := tablePrime_psu_four hr hr2 (hT.classical hm)
      exact hu43 hm rfl
  ·
    rcases h with ⟨f, ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ |
      ⟨-, -, hm⟩ | ⟨-, -, hm⟩⟩ | hm | hm
    · exact absurd (tablePrime_psl_two hr hr2 (hT.classical hm)).2.1 (by norm_num)
    · obtain ⟨hr3, hrq⟩ := tablePrime_psl_three (hT.classical hm)
      exact hrank3 hm ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hr3)
        (Or.inl ⟨rfl, rfl, by
          rwa [(Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hr3] at hrq⟩)
    · obtain ⟨hr3, hrq⟩ := tablePrime_psu_three (hT.classical hm)
      exact hrank3 hm ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hr3)
        (Or.inr ⟨rfl, rfl, by
          rwa [(Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hr3] at hrq⟩)
    · exact absurd (hT.classical hm) not_tablePrime_psp
    · exact absurd (tablePrime_psu_four hr hr2 (hT.classical hm)).2.1 (by norm_num)
    · exact absurd (tablePrime_g2 (hT.chevalley (by decide) hm)).2.1 (by norm_num)
    · exact absurd (hT.chevalley (by decide) hm) not_tablePrime_trialityD4
    · exact absurd (hT.reeTits (by decide) hm) not_tablePrime_twistedF4
    · exact absurd (hT.suzuki hm) not_tablePrime_twistedB2
    · exact absurd (hrZ : r ∣ Nat.card (center ↥Y)) (by
        rw [tablePrime_psu_five_two_two hr (hT.classical hm)]
        exact not_five_dvd_card_center_of_U54 he hm)
    · exact absurd (hT.reeTits (by decide) hm) not_tablePrime_tits
  ·
    rcases h with ⟨n, -, hm⟩ | hm
    · exact absurd (hT.classical hm) (not_tablePrime_psl_two_one hr)
    · exact absurd (hT.classical hm) not_tablePrime_psp
  ·
    have hJ4 : CFSG.SectionRank.J4OrderHyp := dvd_of_eq CFSG.Sporadic.J4.card_J4
    have hJ3p : ∀ {r : ℕ}, r.Prime → r ≠ 2 → r ≠ 3 →
        ¬ r ^ 3 ∣ Nat.card (NativeSporadic.Carrier .J3) := by
      intro r hr hr2 hr3 hd
      rw [show Nat.card (NativeSporadic.Carrier .J3) = 50232960 from CFSG.Sporadic.J3.card_J3]
        at hd
      have h2 : r ^ 2 ∣ 2 ^ 7 * 3 ^ 5 * 1615 := by
        rw [show 2 ^ 7 * 3 ^ 5 * 1615 = 50232960 by norm_num]
        exact (pow_dvd_pow r (by norm_num : 2 ≤ 3)).trans hd
      exact CFSG.SectionRank.not_sq_dvd_of_not_sq_dvd_cofactor hr hr2 hr3
        (CFSG.SectionRank.not_sq_dvd_of_bound (B := 41) (by norm_num) (by norm_num) (by decide)
          hr hr2 hr3) h2
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · haveI := Finite.of_equiv _ e.toEquiv
      refine ta_pRank_le_two_of_mulEquiv hr.one_lt e (small_pRank_top_le_two_of_not_dvd hr ?_)
      rw [show Nat.card (NativeSporadic.Carrier .M11) = 7920 from CFSG.Sporadic.Mathieu.card_M11]
      exact small_not_pow_three_dvd (Or.inl rfl) hr hr2
    · exact absurd hrZ (not_dvd_card_center_of_M12 hq e hr hr2)
    · haveI := Finite.of_equiv _ e.toEquiv
      refine ta_pRank_le_two_of_mulEquiv hr.one_lt e (small_pRank_top_le_two_of_not_dvd hr ?_)
      rw [show Nat.card (NativeSporadic.Carrier .M22) = 443520 from
        CFSG.Sporadic.Mathieu.card_M22]
      exact small_not_pow_three_dvd (Or.inr (Or.inl rfl)) hr hr2
    · haveI := Finite.of_equiv _ e.toEquiv
      refine ta_pRank_le_two_of_mulEquiv hr.one_lt e (small_pRank_top_le_two_of_not_dvd hr ?_)
      rw [show Nat.card (NativeSporadic.Carrier .M23) = 10200960 from by
        change Nat.card NativeSporadic.M23 = _
        rw [CFSG.Sporadic.Mathieu.nativeM23_eq, Nat.card_eq_fintype_card]
        exact CFSG.M23.M23Group.card_M23]
      exact small_not_pow_three_dvd (Or.inr (Or.inr (Or.inl rfl))) hr hr2
    · exact absurd hrZ (not_dvd_card_center_of_M24 hq e hr hr2)
    · haveI := Finite.of_equiv _ e.toEquiv
      refine ta_pRank_le_two_of_mulEquiv hr.one_lt e (small_pRank_top_le_two_of_not_dvd hr ?_)
      rw [show Nat.card (NativeSporadic.Carrier .J1) = 175560 from CFSG.Sporadic.J1.card_J1]
      exact small_not_pow_three_dvd (Or.inr (Or.inr (Or.inr rfl))) hr hr2
    · exact absurd hrZ (not_dvd_card_center_of_J2 hq e hr hr2)
    · by_cases hr3 : r = 3
      · subst hr3
        exfalso
        obtain ⟨K, hKp, Q, x, y, hh, cc, a, b, c, d, -, hQ, hQcard, hcyc, hhK, hgen, hx, hy, hdet,
          hcK, hcc, hcK1⟩ := CFSG.SectionRank.J3_perfect_local_det_witness
        haveI : Finite NativeSporadic.J3 := Finite.of_equiv _ e.toEquiv
        let π : ↥Y →* NativeSporadic.J3 := e.toMonoidHom.comp (QuotientGroup.mk' (center ↥Y))
        have hπ : Function.Surjective π :=
          e.surjective.comp (QuotientGroup.mk'_surjective _)
        have hπker : π.ker ≤ center ↥Y := fun g hg => by
          have h1 : e (QuotientGroup.mk' (center ↥Y) g) = 1 := hg
          have h2 : QuotientGroup.mk' (center ↥Y) g = 1 := e.injective (by rw [h1, map_one])
          exact (QuotientGroup.eq_one_iff g).1 h2
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hpz.to_le hπker)
        have hodd : Odd (Nat.card π.ker) := by
          rw [hn]
          exact Odd.pow (by decide)
        obtain ⟨E3, hE3, hcard⟩ := CFSG.SectionRank.perfect_local_det_cover_rank K Q hQ hQcard
          hcyc hh hhK hgen hx hy hdet cc hcK hcc hcK1 π hπ hπker hodd
        have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥Y) :=
          CFSG.SectionRank.le_pRank (by norm_num) le_top hE3 hcard
        omega
      · haveI := Finite.of_equiv _ e.toEquiv
        exact ta_pRank_le_two_of_mulEquiv hr.one_lt e
          (small_pRank_top_le_two_of_not_dvd hr (hJ3p hr hr2 hr3))
    · exact absurd hrZ (not_dvd_card_center_of_J4 hJ4 hq e hr hr2)
    · exact absurd hrZ (not_dvd_card_center_of_HS hq e hr hr2)
    · exact absurd hrZ (not_dvd_card_center_of_He hq e hr hr2)
    · exact absurd hrZ (not_dvd_card_center_of_Ru hq e hr hr2)
    · by_cases hr3 : r = 3
      · subst hr3
        exact absurd hrZ (not_three_dvd_card_center_of_McL he e)
      · exact absurd hrZ (not_dvd_card_center_of_McL_ne_three hq e hr hr3)

private theorem ta_rankDown_holds : QTCentreRankDown := by
  intro K _ _ hq hK he r hr hr2 hpz hZ1 hrk
  let e : (⊤ : Subgroup K) ≃* K := Subgroup.topEquiv
  have hq' : CFSG.IsQuasisimple ↥(⊤ : Subgroup K) := hq.of_mulEquiv e
  have hpz' : IsPGroup r ↥(center ↥(⊤ : Subgroup K)) :=
    hpz.of_equiv (Subgroup.centerCongr e).symm
  have hZ1' : center ↥(⊤ : Subgroup K) ≠ ⊥ := by
    intro hb
    apply hZ1
    rw [← Subgroup.card_eq_one] at hb ⊢
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hb
  have hrk' : CFSG.pRank r ↥(⊤ : Subgroup K) ≤ 2 := by
    rw [ta_pRank_top_eq]
    exact hrk
  have h := ta_rankDown_sub he hq' (hK.subgroup ⊤) hr hr2 hpz' hZ1' hrk'
  have e' : (↥(⊤ : Subgroup K) ⧸ center ↥(⊤ : Subgroup K)) ≃* K ⧸ center K :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  rwa [CFSG.pRank_congr_of_mulEquiv e' r] at h

end RankDown

private theorem ta_lieModel_of_statedClassicalModel {S : Type} [Group S] {t : StatedLieTag} {n
    p f : ℕ}
    (hm : StatedClassicalModel S t n p f) : LieModel S t n p f := by
  refine Or.inl ⟨?_, hm⟩
  cases t <;> first | exact hm.2.elim | simp [classicalTags]

private theorem ta_catalog_cases {X : Type} [Group X] (h : Catalog X) :
    (∃ p : ℕ, p.Prime ∧ Nonempty (X ≃* Multiplicative (ZMod p))) ∨
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
    OddLieType X ∨ EvenLieType X ∨ NativeSporadic.SporadicRep X := by
  have key : ∀ {t : StatedLieTag} {n p f : ℕ}, StatedLieAdmissible t n p f → LieModel X t n p f →
      OddLieType X ∨ EvenLieType X := by
    intro t n p f hadm hl
    by_cases h2 : p = 2
    · subst h2
      exact Or.inr ⟨t, n, f, hadm, hl⟩
    · exact Or.inl ⟨t, n, p, f, hadm.1, h2, hadm, hl⟩
  rcases h with hc | ha | ⟨t, n, p, f, hm⟩ | hx | hs
  · exact Or.inl hc
  · exact Or.inr (Or.inl ha)
  · rcases key hm.1 (ta_lieModel_of_statedClassicalModel hm) with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases hx with ⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩
    · rcases key hm.1 (Or.inr (Or.inl ⟨rfl, ht, hm⟩)) with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · rcases key hm.1 (Or.inr (Or.inr (Or.inl ⟨rfl, ht, hm⟩))) with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · have hl : LieModel X .twistedB2 0 p f := Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hm⟩))
      rcases key hl.admissible hl with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hs)))


private theorem ta_pRank_le_of_injective {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    {p : ℕ} (hp : 1 < p) (f : X →* Y) (hf : Function.Injective f) :
    CFSG.pRank p X ≤ CFSG.pRank p Y := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top p X, CFSG.SectionRank.pRank_eq_open_pRank_top p Y]
  exact CFSG.SectionRank.pRank_top_le_of_injective hp f hf

private theorem ta_isTwoLocal_map_inj {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) {L : Subgroup X} (hL : IsTwoLocal L) :
    ∃ L' : Subgroup Y, IsTwoLocal L' ∧ L.map f ≤ L' := by
  obtain ⟨P, hP1, hP2, rfl⟩ := hL
  refine ⟨Subgroup.normalizer ((P.map f : Subgroup Y) : Set Y), ⟨P.map f, ?_, ?_, rfl⟩, ?_⟩
  · intro h
    exact hP1 ((Subgroup.map_eq_bot_iff_of_injective P hf).mp h)
  · exact hP2.of_equiv (P.equivMapOfInjective f hf)
  · exact Subgroup.le_normalizer_map (H := P) f

private theorem ta_twoLocalPrimeRank_le_of_injective {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y] {p : ℕ} (hp : p.Prime) (f : X →* Y) (hf : Function.Injective f) :
    twoLocalPrimeRank p X ≤ twoLocalPrimeRank p Y := by
  refine csSup_le' ?_
  rintro _ ⟨L, hL, rfl⟩
  obtain ⟨L', hL', hLL'⟩ := ta_isTwoLocal_map_inj f hf hL
  have h1 : CFSG.Open.pRank p L ≤ CFSG.Open.pRank p L' :=
    (CFSG.SectionRank.pRank_le_map hp.one_lt f hf L).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt hLL')
  refine h1.trans (le_csSup ⟨Nat.card Y, ?_⟩ ⟨L', hL', rfl⟩)
  rintro _ ⟨K, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hp.one_lt K

private theorem ta_isSectionOf_quotient {X : Type} [Group X] (N : Subgroup X) [N.Normal] :
    IsSectionOf (X ⧸ N) X := by
  refine ⟨⊤, N, inferInstance, ⟨QuotientGroup.congr N (N.subgroupOf ⊤) Subgroup.topEquiv.symm ?_⟩⟩
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨(x : X), hx, rfl⟩

private theorem ta_layer_map_le {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) : (genFittingLayer G).map f ≤ genFittingLayer H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro component hcomponent
  apply Subgroup.map_le_iff_le_comap.mp
  by_cases hkilled : component ≤ f.ker
  · rw [component.map_eq_bot_iff.mpr hkilled]
    exact bot_le
  · exact CFSG.ComponentClassification.Layer.component_le
      (CFSG.ComponentClassification.LocalComponents.image hcomponent f hf hkilled)

private theorem ta_genFittingLayer_top_of_surjective {G H : Type*} [Group G] [Group H]
    (hG : genFittingLayer G = ⊤) (f : G →* H) (hf : Function.Surjective f) :
    genFittingLayer H = ⊤ := by
  have h := ta_layer_map_le f hf
  rw [hG, Subgroup.map_top_of_surjective f hf] at h
  exact top_le_iff.mp h

private theorem ta_theoremAConclusion_of_injective {G : Type} [Group G] [Finite G] {S : Type}
    [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hev : evenRank G ≤ 2)
    (f : S →* G) (hf : Function.Injective f) : TheoremAConclusion G S p := by
  unfold TheoremAConclusion
  refine ⟨Or.inl ⟨ta_twoLocalPrimeRank_le_of_injective hp f hf,
    (ta_twoLocalPrimeRank_le_evenRank hp hp2).trans hev⟩, fun _ => ?_⟩
  simp only [ta_pRank_top_eq]
  exact ta_pRank_le_of_injective hp.one_lt f hf

private theorem ta_theoremAConclusion_of_mulEquiv {G : Type} [Group G] [Finite G] {S S' : Type}
    [Group S] [Group S'] [Finite S] [Finite S'] {p : ℕ} (hp : p.Prime) (e : S ≃* S')
    (h : TheoremAConclusion G S' p) : TheoremAConclusion G S p := by
  unfold TheoremAConclusion at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun hG => ?_⟩
  · rcases h1 with ⟨ha, hb⟩ | ⟨hp3, B⟩
    · exact Or.inl ⟨(ta_twoLocalPrimeRank_le_of_injective hp e.toMonoidHom e.injective).trans
        ha, hb⟩
    · refine Or.inr ⟨hp3, ?_⟩
      obtain ⟨H, H₁, H₂, n₁, n₂, ⟨e'⟩, rest⟩ := B
      exact ⟨H, H₁, H₂, n₁, n₂, ⟨e.trans e'⟩, rest⟩
  · have hS : CFSG.pRank p S = CFSG.pRank p S' := CFSG.pRank_congr_of_mulEquiv e p
    simp only [ta_pRank_top_eq] at h2 hG ⊢
    rw [hS]
    exact h2 hG

private theorem ta_a213_structure {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S]
    {p : ℕ}
    (h11 : ∀ (G : Type) [Group G] [Finite G] (S : Type) [Group S] [Finite S] (p : ℕ),
      IsMinimalCounterexampleToA G S p →
      Nonempty ((G ⧸ pCore p G) ≃* (S ⧸ Subgroup.center S)))
    (hq : IsQuasisimple G) (hmin : IsMinimalCounterexampleToA G S p) :
    ∃ (K : Subgroup G) (_ : K.Normal), Nonempty (S ≃* G ⧸ K) ∧ K ≠ ⊥ ∧ K ≠ ⊤ ∧
      K ≤ Subgroup.center G ∧ IsPGroup p (Subgroup.center G) := by
  obtain ⟨K, hKn, ⟨e⟩⟩ := (as_A_2_8 G S p hmin).2
  have hmin2 := hmin
  obtain ⟨hev, -, -, -, hp, hp2, hnc, -⟩ := hmin2
  have hq2 := hq
  obtain ⟨-, hsimple, -⟩ := hq2
  have hK1 : K ≠ ⊥ := by
    intro hK
    subst hK
    refine hnc (ta_theoremAConclusion_of_injective hp hp2 hev
      ((QuotientGroup.quotientBot (G := G)).toMonoidHom.comp e.toMonoidHom) ?_)
    exact (QuotientGroup.quotientBot (G := G)).injective.comp e.injective
  have hKtop : K ≠ ⊤ := by
    intro hK
    subst hK
    haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
    refine hnc (ta_theoremAConclusion_of_injective hp hp2 hev (1 : S →* G) ?_)
    intro a b _
    exact e.injective (Subsingleton.elim _ _)
  have hKz : K ≤ Subgroup.center G :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hq hKn).resolve_left hKtop
  obtain ⟨f⟩ := h11 G S p hmin
  obtain ⟨-, -, hZK⟩ := CFSG.LocalCores.quasisimple_central_quotient hq K hKz
  have e1 : (S ⧸ Subgroup.center S) ≃* ((G ⧸ K) ⧸ Subgroup.center (G ⧸ K)) :=
    QuotientGroup.congr (Subgroup.center S) (Subgroup.center (G ⧸ K)) e (Subgroup.map_center_eq e)
  have e2 : ((G ⧸ K) ⧸ Subgroup.center (G ⧸ K)) ≃* G ⧸ Subgroup.center G :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans
      (QuotientGroup.quotientQuotientEquivQuotient K (Subgroup.center G) hKz)
  have hcard : Nat.card (G ⧸ pCore p G) = Nat.card (G ⧸ Subgroup.center G) :=
    Nat.card_congr (f.toEquiv.trans (e1.trans e2).toEquiv)
  have hO : pCore p G ≤ Subgroup.center G := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (CFSG.pCore_normal (p := p) (G := G)) with h | h
    · exfalso
      have h1 : Nat.card (G ⧸ pCore p G) = 1 := Subgroup.index_eq_one.mpr h
      rw [h1] at hcard
      obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp hcard.symm
      exact (not_subsingleton (G ⧸ Subgroup.center G)) hsub
    · exact h
  have hO' : pCore p G = Subgroup.center G := by
    refine Subgroup.eq_of_le_of_card_ge hO ?_
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore p G)
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
    rw [hcard] at h1
    have hpos : 0 < Nat.card (G ⧸ Subgroup.center G) := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)).ge
  refine ⟨K, hKn, ⟨e⟩, hK1, hKtop, hKz, ?_⟩
  rw [← hO']
  exact CFSG.pCore_isPGroup

private theorem ta_a_2_13_of_a_2_11_a_2_12
    (h11 : ∀ (G : Type) [Group G] [Finite G] (S : Type) [Group S] [Finite S] (p : ℕ),
      IsMinimalCounterexampleToA G S p →
      Nonempty ((G ⧸ pCore p G) ≃* (S ⧸ Subgroup.center S)))
    (h12 : ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G → ¬ TheoremAHolds G →
      IsQuasisimple G) :
    ∀ (G : Type) [Group G] [Finite G], IsMinimalCounterexampleABC G →
    (IsSimpleGroup G ∧ (¬ TheoremBHolds G ∨ ¬ TheoremCHolds G)) ∨
    (IsQuasisimple G ∧ ¬ IsSimpleGroup G ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      IsPGroup p (Subgroup.center G) ∧
      ∃ (Z : Subgroup G) (_ : Z.Normal), Z ≠ ⊥ ∧ Z ≤ Subgroup.center G ∧
        evenRank G ≤ 2 ∧ CFSG.SectionRank.IsKGroupCat G ∧ IsSectionOf (G ⧸ Z) G ∧
        genFittingLayer (G ⧸ Z) = ⊤ ∧ ¬ TheoremAConclusion G (G ⧸ Z) p ∧
        ∀ (q : ℕ), q.Prime → q ≠ 2 →
          ∀ (S : Type) [Group S] [Finite S], IsSectionOf S G → genFittingLayer S = ⊤ →
            ¬ TheoremAConclusion G S q → q = p) := by
  intro G _ _ hmin
  by_cases hB : TheoremBHolds G
  swap
  · left
    refine ⟨?_, Or.inl hB⟩
    by_contra hns
    exact hB fun hs => absurd hs hns
  by_cases hC : TheoremCHolds G
  swap
  · left
    refine ⟨?_, Or.inr hC⟩
    by_contra hns
    exact hC fun hs => absurd hs hns
  right
  have hA : ¬ TheoremAHolds G := by
    rcases hmin.1 with h | h | h
    · exact h
    · exact absurd hB h
    · exact absurd hC h
  have hev : evenRank G ≤ 2 := by
    by_contra h
    exact hA fun h' => absurd h' h
  have hKG : CFSG.SectionRank.IsKGroupCat G := by
    by_contra h
    exact hA fun _ h' => absurd h' h
  obtain ⟨S, _, _, hSsec, hSss, hnot⟩ : ∃ (S : Type) (_ : Group S) (_ : Finite S),
      IsSectionOf S G ∧ genFittingLayer S = ⊤ ∧
      ¬ ((∀ p : ℕ, p.Prime → p ≠ 2 → TheoremAConclusion G S p) ∧
        (CFSG.IsStronglyQuasithin G → CFSG.IsStronglyQuasithin S)) := by
    by_contra hcon
    push Not at hcon
    refine hA ?_
    intro _ _ S _ _ hs hss
    exact hcon S _ _ hs hss
  obtain ⟨p, hp, hp2, hnp⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ TheoremAConclusion G S p := by
    by_contra hcon
    push Not at hcon
    refine hnot ⟨fun p hp hp2 => hcon p hp hp2, fun hsqt q hq hq2 => ?_⟩
    have hc := hcon q hq hq2
    unfold TheoremAConclusion at hc
    have h2 := hc.2
    simp only [ta_pRank_top_eq] at h2
    have h3 := hsqt q hq hq2
    exact (h2 h3).trans h3
  have hmin' : IsMinimalCounterexampleToA G S p :=
    ⟨hev, hKG, hSsec, hSss, hp, hp2, hnp, fun X _ _ hX => (hmin.2 X hX).1⟩
  have hqs : IsQuasisimple G := h12 G hmin hA
  obtain ⟨K, hKn, ⟨e⟩, hK1, hKtop, hKz, hpz⟩ := ta_a213_structure h11 hqs hmin'
  refine ⟨hqs, ?_, p, hp, hp2, hpz, K, hKn, hK1, hKz, hev, hKG,
    ta_isSectionOf_quotient K, ?_, ?_, ?_⟩
  · intro hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
    · exact hK1 h
    · exact hKtop h
  · exact ta_genFittingLayer_top_of_surjective hSss e.toMonoidHom e.surjective
  · intro hconc
    exact hnp (ta_theoremAConclusion_of_mulEquiv hp e hconc)
  · intro q hq hq2 S' _ _ hS'sec hS'ss hnq
    have hmin'' : IsMinimalCounterexampleToA G S' q :=
      ⟨hev, hKG, hS'sec, hS'ss, hq, hq2, hnq, fun X _ _ hX => (hmin.2 X hX).1⟩
    obtain ⟨-, -, -, -, -, -, hqz⟩ := ta_a213_structure h11 hqs hmin''
    obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK1
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fact q.Prime := ⟨hq⟩
    have hgz : (g : G) ∈ Subgroup.center G := hKz g.2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hpz) ⟨g, hgz⟩
    obtain ⟨l, hl⟩ := (IsPGroup.iff_orderOf.mp hqz) ⟨g, hgz⟩
    have hne1 : orderOf (⟨g, hgz⟩ : Subgroup.center G) ≠ 1 := by
      intro h
      apply hg1
      have := orderOf_eq_one_iff.mp h
      exact Subtype.ext (congrArg (fun z : Subgroup.center G => (z : G)) this)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne1 (by rw [hk]; simp)
    have hdvd : p ∣ q ^ l := by
      rw [← hl, hk]
      exact dvd_pow_self p hk0
    exact ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)).symm

private theorem ta_a_2_13 (h11 : A_2_11) (h12 : A_2_12) : A_2_13 :=
  ta_a_2_13_of_a_2_11_a_2_12 h11 h12


private theorem ta_center_shape_of_multiplier {K : Type} [Group K] [Finite K] (hperf :
    Group.IsPerfect K)
    {N E : ℕ} (hN : Nat.card (quasithinHopfMultiplier (K ⧸ Subgroup.center K)) = N)
    (hE : ∀ m : quasithinHopfMultiplier (K ⧸ Subgroup.center K), m ^ E = 1)
    {r : ℕ} (hr : r.Prime) (hZ : IsPGroup r ↥(Subgroup.center K))
    (hN3 : ¬ r ^ 3 ∣ N) (hE2 : ¬ r ^ 2 ∣ E) :
    Nat.card (Subgroup.center K) ∣ r ^ 2 ∧ ∀ z ∈ Subgroup.center K, z ^ r = 1 := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hq : Function.Surjective (QuotientGroup.mk' (Subgroup.center K)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (Subgroup.center K)).ker ≤ Subgroup.center K :=
    (QuotientGroup.ker_mk' _).le
  have hmap := CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift
    (QuotientGroup.mk' (Subgroup.center K)) hq hker
  rw [QuotientGroup.ker_mk'] at hmap
  set L := CFSG.RankThree.PerfectCover.hopfLift (QuotientGroup.mk' (Subgroup.center K)) hq hker
    with hL
  set e : quasithinHopfMultiplier (K ⧸ Subgroup.center K) ≃*
      CFSG.RankThree.PerfectCover.hopfMultiplier (K ⧸ Subgroup.center K) :=
    CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _ with he
  have hcard : Nat.card (Subgroup.center K) ∣ N := by
    have h1 := Subgroup.card_map_dvd (H := CFSG.RankThree.PerfectCover.hopfMultiplier
      (K ⧸ Subgroup.center K)) L
    rw [hmap] at h1
    have h2 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (K ⧸ Subgroup.center K)) =
        Nat.card (quasithinHopfMultiplier (K ⧸ Subgroup.center K)) :=
      (Nat.card_congr e.toEquiv).symm
    rw [h2, hN] at h1
    exact h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hZ
  refine ⟨?_, ?_⟩
  · rw [hk] at hcard ⊢
    have hk2 : k ≤ 2 := by
      by_contra h
      exact hN3 ((pow_dvd_pow r (by omega : 3 ≤ k)).trans hcard)
    exact pow_dvd_pow r hk2
  · intro z hz
    have hz' : z ∈ (CFSG.RankThree.PerfectCover.hopfMultiplier (K ⧸ Subgroup.center K)).map L := by
      rw [hmap]; exact hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hz'
    have hE' : u ^ E = 1 := by
      have h1 := hE (e.symm ⟨u, hu⟩)
      have h2 := congrArg e h1
      rw [map_pow, MulEquiv.apply_symm_apply, map_one] at h2
      exact congrArg Subtype.val h2
    have hLE : (L u) ^ E = 1 := by rw [← map_pow, hE', map_one]
    have hzc : L u ∈ Subgroup.center K := hz
    obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.1 hZ) ⟨L u, hzc⟩
    have hi' : orderOf (L u) = r ^ i := by
      have := congrArg id hi
      rw [← Subgroup.orderOf_coe] at hi
      exact hi
    have hdvd : r ^ i ∣ E := hi' ▸ orderOf_dvd_of_pow_eq_one hLE
    have hi1 : i ≤ 1 := by
      by_contra h
      exact hE2 ((pow_dvd_pow r (by omega : 2 ≤ i)).trans hdvd)
    have : orderOf (L u) ∣ r := by
      rw [hi']
      calc r ^ i ∣ r ^ 1 := pow_dvd_pow r hi1
        _ = r := pow_one r
    exact orderOf_dvd_iff_pow_eq_one.1 this


private theorem ta_not_cube_dvd {r N : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hN : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 6 ∨ N = 12 ∨ N = 36 ∨ N = 48) :
    ¬ r ^ 3 ∣ N := by
  intro h
  have h3 : 3 ≤ r := by have := hr.two_le; omega
  have h27 : 27 ≤ r ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ r ^ 3 := Nat.pow_le_pow_left h3 3
  have hpos : 0 < N := by rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hle : r ^ 3 ≤ N := Nat.le_of_dvd hpos h
  have hr3 : r = 3 := by
    by_contra hne
    have h4 : 4 ≤ r := by omega
    have : 64 ≤ r ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ r ^ 3 := Nat.pow_le_pow_left h4 3
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  subst hr3
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem ta_not_sq_dvd {r E : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hE : E = 1 ∨ E = 2 ∨ E = 3 ∨ E = 4 ∨ E = 5 ∨ E = 6 ∨ E = 12) : ¬ r ^ 2 ∣ E := by
  intro h
  have h3 : 3 ≤ r := by have := hr.two_le; omega
  have h9 : 9 ≤ r ^ 2 := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ r ^ 2 := Nat.pow_le_pow_left h3 2
  have hpos : 0 < E := by rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hle : r ^ 2 ≤ E := Nat.le_of_dvd hpos h
  have hr3 : r = 3 := by
    by_contra hne
    have h4 : 4 ≤ r := by omega
    have : 16 ≤ r ^ 2 := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ r ^ 2 := Nat.pow_le_pow_left h4 2
    rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  subst hr3
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega


private theorem ta_shape_of_equiv {K : Type} [Group K] [Finite K] (hperf : Group.IsPerfect K)
    {A : Type}
    [Group A] (ψ : quasithinHopfMultiplier (K ⧸ Subgroup.center K) ≃* A) {N E : ℕ}
    (hN : Nat.card A = N) (hE : ∀ a : A, a ^ E = 1)
    (hN' : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 6 ∨ N = 12 ∨ N = 36 ∨ N = 48)
    (hE' : E = 1 ∨ E = 2 ∨ E = 3 ∨ E = 4 ∨ E = 5 ∨ E = 6 ∨ E = 12) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hZ : IsPGroup r ↥(Subgroup.center K)) :
    Nat.card (Subgroup.center K) ∣ r ^ 2 ∧ ∀ z ∈ Subgroup.center K, z ^ r = 1 :=
  ta_center_shape_of_multiplier hperf (by rw [Nat.card_congr ψ.toEquiv]; exact hN)
    (fun m => ψ.injective (by rw [map_pow, hE, map_one])) hr hZ (ta_not_cube_dvd hr hr2 hN')
    (ta_not_sq_dvd hr hr2 hE')

private theorem ta_card_mult_zmod (d : ℕ) [NeZero d] : Nat.card (Multiplicative (ZMod d)) = d := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod d) ≃ ZMod d), Nat.card_zmod]

private theorem ta_exp_mult_zmod (d : ℕ) (a : Multiplicative (ZMod d)) : a ^ d = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private theorem ta_shape_of_cyclic {K : Type} [Group K] [Finite K] (hperf : Group.IsPerfect K)
    {d : ℕ}
    (hd : d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 12)
    (h : quasithinMultiplierCyclic (K ⧸ Subgroup.center K) d) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hZ : IsPGroup r ↥(Subgroup.center K)) :
    Nat.card (Subgroup.center K) ∣ r ^ 2 ∧ ∀ z ∈ Subgroup.center K, z ^ r = 1 := by
  obtain ⟨ψ⟩ := h
  haveI : NeZero d := ⟨by omega⟩
  exact ta_shape_of_equiv hperf ψ (N := d) (E := d) (ta_card_mult_zmod d) (ta_exp_mult_zmod d)
    (by omega) (by omega) hr hr2 hZ

private theorem ta_shape_of_two_two {K : Type} [Group K] [Finite K] (hperf : Group.IsPerfect K)
    (ψ : quasithinHopfMultiplier (K ⧸ Subgroup.center K) ≃* Multiplicative (ZMod 2 × ZMod 2))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hZ : IsPGroup r ↥(Subgroup.center K)) :
    Nat.card (Subgroup.center K) ∣ r ^ 2 ∧ ∀ z ∈ Subgroup.center K, z ^ r = 1 :=
  ta_shape_of_equiv hperf ψ (N := 4) (E := 2)
    (by rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2 × ZMod 2) ≃ _),
      Nat.card_prod, Nat.card_zmod])
    (fun a => by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      have : ∀ x : ZMod 2 × ZMod 2, (2 : ℕ) • x = 0 := by decide
      exact this _) (by omega) (by omega) hr hr2 hZ

private theorem ta_shape_of_four_four_three {K : Type} [Group K] [Finite K] (hperf :
    Group.IsPerfect K)
    (ψ : quasithinHopfMultiplier (K ⧸ Subgroup.center K) ≃*
      Multiplicative (ZMod 4 × ZMod 4 × ZMod 3))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hZ : IsPGroup r ↥(Subgroup.center K)) :
    Nat.card (Subgroup.center K) ∣ r ^ 2 ∧ ∀ z ∈ Subgroup.center K, z ^ r = 1 :=
  ta_shape_of_equiv hperf ψ (N := 48) (E := 12)
    (by rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 4 × ZMod 4 × ZMod 3) ≃ _),
      Nat.card_prod, Nat.card_prod, Nat.card_zmod, Nat.card_zmod])
    (fun a => by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      have : ∀ x : ZMod 4 × ZMod 4 × ZMod 3, (12 : ℕ) • x = 0 := by decide
      exact this _) (by omega) (by omega) hr hr2 hZ

private theorem ta_shape_of_three_three_four {K : Type} [Group K] [Finite K] (hperf :
    Group.IsPerfect K)
    (ψ : quasithinHopfMultiplier (K ⧸ Subgroup.center K) ≃*
      Multiplicative (ZMod 3 × ZMod 3 × ZMod 4))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hZ : IsPGroup r ↥(Subgroup.center K)) :
    Nat.card (Subgroup.center K) ∣ r ^ 2 ∧ ∀ z ∈ Subgroup.center K, z ^ r = 1 :=
  ta_shape_of_equiv hperf ψ (N := 36) (E := 12)
    (by rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3 × ZMod 3 × ZMod 4) ≃ _),
      Nat.card_prod, Nat.card_prod, Nat.card_zmod, Nat.card_zmod])
    (fun a => by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      have : ∀ x : ZMod 3 × ZMod 3 × ZMod 4, (12 : ℕ) • x = 0 := by decide
      exact this _) (by omega) (by omega) hr hr2 hZ

private theorem ta_shape_of_subsingleton {K : Type} [Group K] [Finite K] (hperf : Group.IsPerfect K)
    (h : Subsingleton (quasithinHopfMultiplier (K ⧸ Subgroup.center K))) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hZ : IsPGroup r ↥(Subgroup.center K)) :
    Nat.card (Subgroup.center K) ∣ r ^ 2 ∧ ∀ z ∈ Subgroup.center K, z ^ r = 1 :=
  ta_center_shape_of_multiplier hperf (N := 1) (E := 1) (Nat.card_of_subsingleton 1)
    (fun m => by rw [pow_one]; exact Subsingleton.elim _ _) hr hZ
    (ta_not_cube_dvd hr hr2 (by omega)) (ta_not_sq_dvd hr hr2 (by omega))


@[expose] def taListedI13D2 (G : Type) [Group G] : Prop :=
  StatedClassicalModel G .PSL 4 2 1 ∨ ChevalleyExceptionalModel G .G2 2 2 ∨
    NativeSporadic.IsSporadic G .M12 ∨ NativeSporadic.IsSporadic G .J2 ∨
    NativeSporadic.IsSporadic G .HS ∨ NativeSporadic.IsSporadic G .Ru ∨
    ∃ p f : ℕ, p ≠ 2 ∧ 1 ≤ f ∧ p ^ f ≠ 9 ∧ StatedClassicalModel G .PSL 2 p f

@[expose] def taListedI13D3 (G : Type) [Group G] : Prop :=
  (∃ p f : ℕ, (p ^ f % 3 = 1 ∧ StatedClassicalModel G .PSL 3 p f) ∨
      (p ^ f % 3 = 2 ∧ StatedClassicalModel G .PSU 3 p f)) ∧
    ¬ StatedClassicalModel G .PSL 3 2 2

@[expose] def taListedI13D6 (G : Type) [Group G] : Prop :=
  Nonempty (G ≃* alternatingGroup (Fin 6)) ∨ Nonempty (G ≃* alternatingGroup (Fin 7))

@[expose] def taListedI14D2 (G : Type) [Group G] : Prop :=
  Nonempty (G ≃* alternatingGroup (Fin 9)) ∨ StatedClassicalModel G .PSU 4 2 1 ∨
    StatedClassicalModel G .PSL 4 3 1 ∨
    ∃ p f : ℕ, p ≠ 2 ∧ 1 ≤ f ∧ 9 < p ^ f ∧ StatedClassicalModel G .PSL 2 p f

@[expose] def taListedI14D3 (G : Type) [Group G] : Prop :=
  NativeSporadic.IsSporadic G .J3 ∨ NativeSporadic.IsSporadic G .McL ∨
    ChevalleyExceptionalModel G .G2 3 1 ∨
    ∃ p f : ℕ, p ≠ 2 ∧ ((p ^ f % 3 = 1 ∧ StatedClassicalModel G .PSL 3 p f) ∨
      (p ^ f % 3 = 2 ∧ StatedClassicalModel G .PSU 3 p f))

@[expose] def taListedI14D4 (G : Type) [Group G] : Prop :=
  (∃ r m : ℕ, r.Prime ∧ r = 2 ^ 2 ^ m + 1 ∧ 3 < r ∧ StatedClassicalModel G .PSL 4 r 1) ∨
    (∃ s m : ℕ, s.Prime ∧ s = 2 ^ m - 1 ∧ 3 < s ∧ StatedClassicalModel G .PSU 4 s 1)

@[expose] def TA_I_1_3 : Prop :=
  (∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → CFSG.SectionRank.IsSQTKCat G →
    Nontrivial (quasithinHopfMultiplier G) →
    taListedI13D2 G ∨ taListedI13D3 G ∨ taListedI13D6 G ∨ NativeSporadic.IsSporadic G .M22 ∨
      SuzukiModel G 2 3 ∨ StatedClassicalModel G .PSL 3 2 2) ∧
  (∀ (G : Type) [Group G] [Finite G], taListedI13D2 G → quasithinMultiplierCyclic G 2) ∧
  (∀ (G : Type) [Group G] [Finite G], taListedI13D3 G → quasithinMultiplierCyclic G 3) ∧
  (∀ (G : Type) [Group G] [Finite G], taListedI13D6 G → quasithinMultiplierCyclic G 6) ∧
  (∀ (G : Type) [Group G] [Finite G], NativeSporadic.IsSporadic G .M22 →
    quasithinMultiplierCyclic G 12) ∧
  (∀ (G : Type) [Group G] [Finite G], SuzukiModel G 2 3 →
    Nonempty (quasithinHopfMultiplier G ≃* Multiplicative (ZMod 2 × ZMod 2))) ∧
  (∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSL 3 2 2 →
    Nonempty (quasithinHopfMultiplier G ≃* Multiplicative (ZMod 4 × ZMod 4 × ZMod 3)))

@[expose] def TA_I_1_4 : Prop :=
  (∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → CFSG.SectionRank.IsKGroupCat G →
    CFSG.Quasithin.IsQuasithin G → ¬ CFSG.IsStronglyQuasithin G →
    Nontrivial (quasithinHopfMultiplier G) →
    taListedI14D2 G ∨ taListedI14D3 G ∨ taListedI14D4 G ∨ StatedClassicalModel G .PSU 5 2 2 ∨
      StatedClassicalModel G .PSU 4 3 1 ∨
      StatedClassicalModel G .PSp 3 2 1 ∨
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ StatedClassicalModel G .PSp 2 p 1)) ∧
  (∀ (G : Type) [Group G] [Finite G], taListedI14D2 G → quasithinMultiplierCyclic G 2) ∧
  (∀ (G : Type) [Group G] [Finite G], taListedI14D3 G → quasithinMultiplierCyclic G 3) ∧
  (∀ (G : Type) [Group G] [Finite G], taListedI14D4 G → quasithinMultiplierCyclic G 4) ∧
  (∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSU 5 2 2 →
    quasithinMultiplierCyclic G 5) ∧
  (∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSU 4 3 1 →
    Nonempty (quasithinHopfMultiplier G ≃* Multiplicative (ZMod 3 × ZMod 3 × ZMod 4))) ∧
  (∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSp 3 2 1 →
    quasithinMultiplierCyclic G 2) ∧
  (∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 5 ≤ p →
    StatedClassicalModel G .PSp 2 p 1 → quasithinMultiplierCyclic G 2)

private theorem ta_evenRank_center_quotient (hC : CFSG.SectionRank.QTK.QTCentreFact) {K : Type}
    [Group K] [Finite K] (hq : CFSG.IsQuasisimple K) (hK : CFSG.SectionRank.IsKGroupCat K)
    (hev : evenRank K ≤ 2) : evenRank (K ⧸ Subgroup.center K) ≤ 2 := by
  refine csSup_le' ?_
  rintro _ ⟨q, L, hq', hq2, ⟨R, hR1, hR2, rfl⟩, rfl⟩
  by_cases hdvd : q ∣ Nat.card (Subgroup.center K)
  · exact hC K hq hK hev q hq' hq2 hdvd R hR1 hR2
  · let e : (⊤ : Subgroup K) ≃* K := Subgroup.topEquiv
    have hZ' : ¬ q ∣ Nat.card (Subgroup.center (⊤ : Subgroup K)) := by
      rwa [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    have hob : CFSG.SectionRank.QTK.CentreFact.OddBound q
        (↥(⊤ : Subgroup K) ⧸ Subgroup.center ↥(⊤ : Subgroup K)) :=
      fun R hR hR2 =>
        CFSG.SectionRank.QTK.pRank_normalizer_le_two_of_not_dvd hev hq' hq2 hZ' hR hR2
    exact CFSG.SectionRank.QTK.CentreFact.OddBound.of_mulEquiv hq'.one_lt
      (QuotientGroup.congr (Subgroup.center (⊤ : Subgroup K)) (Subgroup.center K) e
        (Subgroup.map_center_eq e)).symm hob R hR1 hR2

private theorem ta_shape (hC : CFSG.SectionRank.QTK.QTCentreFact) (h13 : TA_I_1_3) (h14 :
    TA_I_1_4) :
    QTCentreShape := by
  intro K _ _ hq hK hev r hr hr2 hZ
  haveI : Group.IsPerfect K := hq.1
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2.1
  have hKS : CFSG.SectionRank.IsKGroupCat (K ⧸ Subgroup.center K) := hK.quotient _
  have key : Nat.card (Subgroup.center K) ∣ r ^ 2 ∧ ∀ z ∈ Subgroup.center K, z ^ r = 1 := by
    by_cases hsub : Subsingleton (quasithinHopfMultiplier (K ⧸ Subgroup.center K))
    · exact ta_shape_of_subsingleton hq.1 hsub hr hr2 hZ
    haveI : Nontrivial (quasithinHopfMultiplier (K ⧸ Subgroup.center K)) :=
      not_subsingleton_iff_nontrivial.1 hsub
    by_cases hsqt : CFSG.IsStronglyQuasithin (K ⧸ Subgroup.center K)
    · obtain ⟨hc, h1, h2, h3, h4, h5, h6⟩ := h13
      rcases hc _ hq.2.1 ⟨hsqt, hKS⟩ ‹_› with hD2 | hD3 | hD6 | hM22 | hSz | hL34
      · exact ta_shape_of_cyclic hq.1 (by omega) (h1 _ hD2) hr hr2 hZ
      · exact ta_shape_of_cyclic hq.1 (by omega) (h2 _ hD3) hr hr2 hZ
      · exact ta_shape_of_cyclic hq.1 (by omega) (h3 _ hD6) hr hr2 hZ
      · exact ta_shape_of_cyclic hq.1 (by omega) (h4 _ hM22) hr hr2 hZ
      · obtain ⟨ψ⟩ := h5 _ hSz
        exact ta_shape_of_two_two hq.1 ψ hr hr2 hZ
      · obtain ⟨ψ⟩ := h6 _ hL34
        exact ta_shape_of_four_four_three hq.1 ψ hr hr2 hZ
    · have hqt : CFSG.Quasithin.IsQuasithin (K ⧸ Subgroup.center K) :=
        ta_evenRank_center_quotient hC hq hK hev
      obtain ⟨hc, h1, h2, h3, h4, h5, h6, h7⟩ := h14
      rcases hc _ hq.2.1 hKS hqt hsqt ‹_› with hD2 | hD3 | hD4 | hU5 | hU4 | hSp6 |
        ⟨p, hp, hp5, hSp4⟩
      · exact ta_shape_of_cyclic hq.1 (by omega) (h1 _ hD2) hr hr2 hZ
      · exact ta_shape_of_cyclic hq.1 (by omega) (h2 _ hD3) hr hr2 hZ
      · exact ta_shape_of_cyclic hq.1 (by omega) (h3 _ hD4) hr hr2 hZ
      · exact ta_shape_of_cyclic hq.1 (by omega) (h4 _ hU5) hr hr2 hZ
      · obtain ⟨ψ⟩ := h5 _ hU4
        exact ta_shape_of_three_three_four hq.1 ψ hr hr2 hZ
      · exact ta_shape_of_cyclic hq.1 (by omega) (h6 _ hSp6) hr hr2 hZ
      · exact ta_shape_of_cyclic hq.1 (by omega) (h7 _ p hp hp5 hSp4) hr hr2 hZ
  exact ⟨key.1, fun _ => key.2⟩

section Main



private theorem ta_theoremAHolds
    (h13 : A_2_13) (hC : CFSG.SectionRank.QTK.QTCentreFact)
    (hRd : QTCentreRankDown) (hSh : QTCentreShape) :
    ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → TheoremAHolds G := by
  have hB : ∀ (G : Type) [Group G] [Finite G], TheoremBHolds G := fun G _ _ => as_A_2_2 G
  have hCt : ∀ (G : Type) [Group G] [Finite G], TheoremCHolds G := fun G _ _ hs hn hsq => by
    haveI := hs
    exact CFSG.Milestones.cl_lit_sqtk_simple_list_simple G hn hsq
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn
  by_contra hA
  have hmin : IsMinimalCounterexampleABC G :=
    ⟨Or.inl hA, fun X _ _ hX => ⟨ih _ (hn ▸ hX.2) X rfl, hB X, hCt X⟩⟩
  rcases h13 G hmin with ⟨-, hbc⟩ | ⟨hq, -, p, hp, hp2, hpz, Z, hZn, hZ1, hZc, hev, hK, -, -, hnot, -⟩
  · rcases hbc with h | h
    · exact h (hB G)
    · exact h (hCt G)
  · exact hnot (ta_caseII hC hRd hSh hq hev hK hp hp2 hpz Z hZ1 hZc)

structure Missing_TheoremA : Prop where
  a_2_11 : A_2_11
  a_2_12 : A_2_12
  i_1_3 : TA_I_1_3
  i_1_4 : TA_I_1_4


private theorem ta_theoremAHolds'
    (h12 : A_2_12) (h16 : A_2_16) (h17 : A_2_17) (h18 : A_2_18)
    (h19 : A_2_19) :
    ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → TheoremAHolds G := by
  have hB : ∀ (G : Type) [Group G] [Finite G], TheoremBHolds G := fun G _ _ => as_A_2_2 G
  have hCt : ∀ (G : Type) [Group G] [Finite G], TheoremCHolds G := fun G _ _ hs hn hsq => by
    haveI := hs
    exact CFSG.Milestones.cl_lit_sqtk_simple_list_simple G hn hsq
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn
  by_contra hA
  have hmin : IsMinimalCounterexampleABC G :=
    ⟨Or.inl hA, fun X _ _ hX => ⟨ih _ (hn ▸ hX.2) X rfl, hB X, hCt X⟩⟩
  have hev : evenRank G ≤ 2 := by
    by_contra h
    exact hA fun h' => absurd h' h
  have hKG : CFSG.SectionRank.IsKGroupCat G := by
    by_contra h
    exact hA fun _ h' => absurd h' h
  have hq : CFSG.IsQuasisimple G := h12 G hmin hA
  haveI : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2.1
  have hcat : Catalog (G ⧸ Subgroup.center G) :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hKG ⊤
      ((QuotientGroup.mk' (Subgroup.center G)).comp (⊤ : Subgroup G).subtype) fun s => by
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
        exact ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩
  rcases ta_catalog_cases hcat with ⟨p, hp, ⟨e⟩⟩ | ha | ho | he | hs
  · obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact h16 G hmin ha
  · exact h17 G hmin ho
  · exact h18 G hmin he
  · exact h19 G hmin hs

private theorem ta_A_2_1'
    (h12 : A_2_12) (h16 : A_2_16) (h17 : A_2_17) (h18 : A_2_18) (h19 :
    A_2_19) :
    A_2_1 :=
  fun G _ _ => ta_theoremAHolds' h12 h16 h17 h18 h19 _ G rfl


end Main

section Final


theorem a_2_1_of_facts
    (hC : CFSG.SectionRank.QTK.QTCentreFact)
    (hM : Missing_TheoremA) : A_2_1 :=
  fun G _ _ =>
    ta_theoremAHolds (ta_a_2_13 hM.a_2_11 hM.a_2_12) hC ta_rankDown_holds
      (ta_shape hC hM.i_1_3 hM.i_1_4) _ G rfl

end Final

end TheoremAReduction

section TheoremAReductionCentre


theorem a_2_1_of_reduction
    (h11 : A_2_11) (h12 : A_2_12) (h13 : TA_I_1_3) (h14 : TA_I_1_4) :
    A_2_1 :=
  a_2_1_of_facts CFSG.SectionRank.QTK.CentreFact.qtCentreFact_holds ⟨h11, h12, h13, h14⟩

end TheoremAReductionCentre

section BurnsideTA12

section BurnsideTA12

open CFSG.ASVolI.ChA
open CFSG.Blueprint
open scoped commutatorElement

private theorem burnsideTA12_pRank_top_eq {X : Type*} [Group X] [Finite X] (p : ℕ) :
    CFSG.pRank p ↥(⊤ : Subgroup X) = CFSG.pRank p X := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top p ↥(⊤ : Subgroup X),
    CFSG.SectionRank.pRank_eq_open_pRank_top p X,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup X)]

private theorem burnsideTA12_twoLocalPrimeRank_le_pRank {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) : twoLocalPrimeRank p X ≤ CFSG.pRank p X := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine csSup_le' ?_
  rintro _ ⟨H, -, rfl⟩
  exact CFSG.SectionRank.pRank_mono hp.one_lt le_top

private theorem burnsideTA12_twoLocalPrimeRank_le_evenRank {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : twoLocalPrimeRank p X ≤ evenRank X := by
  refine csSup_le' ?_
  rintro _ ⟨H, hH, rfl⟩
  refine le_csSup ⟨Nat.card X, ?_⟩ ⟨p, H, hp, hp2, hH, rfl⟩
  rintro _ ⟨q, K, hq, -, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt K

private theorem burnsideTA12_evenRank_le_two_of_isStronglyQuasithin {X : Type*} [Group X] [Finite X]
    (h : CFSG.IsStronglyQuasithin X) : evenRank X ≤ 2 := by
  refine csSup_le' ?_
  rintro _ ⟨p, H, hp, hp2, -, rfl⟩
  exact (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans
    (CFSG.SectionRank.isStronglyQuasithin_iff.mp h p hp hp2)

private theorem burnsideTA12_evenRank_isKGroup_of_minimalABC {G : Type} [Group G] [Finite G]
    (h : IsMinimalCounterexampleABC G) :
    evenRank G ≤ 2 ∧ CFSG.SectionRank.IsKGroupCat G := by
  rcases h.1 with hA | hB | hC
  · by_contra hc
    exact hA fun h1 h2 => absurd ⟨h1, h2⟩ hc
  · by_contra hc
    exact hB fun _ _ h1 h2 => absurd ⟨h1, h2⟩ hc
  · by_contra hc
    exact hC fun _ _ hsq =>
      absurd ⟨burnsideTA12_evenRank_le_two_of_isStronglyQuasithin hsq.1, hsq.2⟩ hc

private theorem burnsideTA12_pRank_le_of_injective {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y] {p : ℕ} (hp : 1 < p) (f : X →* Y) (hf : Function.Injective f) :
    CFSG.pRank p X ≤ CFSG.pRank p Y := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top p X, CFSG.SectionRank.pRank_eq_open_pRank_top p Y]
  exact CFSG.SectionRank.pRank_top_le_of_injective hp f hf

private theorem burnsideTA12_isTwoLocal_map_inj {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) {L : Subgroup X} (hL : IsTwoLocal L) :
    ∃ L' : Subgroup Y, IsTwoLocal L' ∧ L.map f ≤ L' := by
  obtain ⟨P, hP1, hP2, rfl⟩ := hL
  refine ⟨Subgroup.normalizer ((P.map f : Subgroup Y) : Set Y), ⟨P.map f, ?_, ?_, rfl⟩, ?_⟩
  · intro h
    exact hP1 ((Subgroup.map_eq_bot_iff_of_injective P hf).mp h)
  · exact hP2.of_equiv (P.equivMapOfInjective f hf)
  · exact Subgroup.le_normalizer_map (H := P) f

private theorem burnsideTA12_twoLocalPrimeRank_le_of_injective {X Y : Type*} [Group X] [Group Y]
    [Finite X] [Finite Y] {p : ℕ} (hp : p.Prime) (f : X →* Y) (hf : Function.Injective f) :
    twoLocalPrimeRank p X ≤ twoLocalPrimeRank p Y := by
  refine csSup_le' ?_
  rintro _ ⟨L, hL, rfl⟩
  obtain ⟨L', hL', hLL'⟩ := burnsideTA12_isTwoLocal_map_inj f hf hL
  have h1 : CFSG.Open.pRank p L ≤ CFSG.Open.pRank p L' :=
    (CFSG.SectionRank.pRank_le_map hp.one_lt f hf L).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt hLL')
  refine h1.trans (le_csSup ⟨Nat.card Y, ?_⟩ ⟨L', hL', rfl⟩)
  rintro _ ⟨K, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hp.one_lt K

private theorem burnsideTA12_evenRank_le_of_injective {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y] (f : X →* Y) (hf : Function.Injective f) : evenRank X ≤ evenRank Y := by
  refine csSup_le' ?_
  rintro _ ⟨q, L, hq, hq2, hL, rfl⟩
  obtain ⟨L', hL', hLL'⟩ := burnsideTA12_isTwoLocal_map_inj f hf hL
  have h1 : CFSG.Open.pRank q L ≤ CFSG.Open.pRank q L' :=
    (CFSG.SectionRank.pRank_le_map hq.one_lt f hf L).trans
      (CFSG.SectionRank.pRank_mono hq.one_lt hLL')
  refine h1.trans (le_csSup ⟨Nat.card Y, ?_⟩ ⟨q, L', hq, hq2, hL', rfl⟩)
  rintro _ ⟨q', K, hq', -, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hq'.one_lt K

private theorem burnsideTA12_isSectionOf_quotient {X : Type} [Group X] (N : Subgroup X) [N.Normal] :
    IsSectionOf (X ⧸ N) X := by
  refine ⟨⊤, N, inferInstance, ⟨QuotientGroup.congr N (N.subgroupOf ⊤) Subgroup.topEquiv.symm ?_⟩⟩
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨(x : X), hx, rfl⟩

private theorem burnsideTA12_isProperSectionOf_subgroup {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hH : H ≠ ⊤) : IsProperSectionOf ↥H G := by
  refine ⟨⟨H, ⊥, inferInstance, ⟨?_⟩⟩, ?_⟩
  · exact (QuotientGroup.quotientBot (G := ↥H)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf H).symm)
  · exact lt_of_le_of_ne (Subgroup.card_le_card_group H) fun h =>
      hH ((Subgroup.card_eq_iff_eq_top H).mp h)

private theorem burnsideTA12_isSectionOf_of_mulEquiv {S S' X : Type} [Group S] [Group S'] [Group X]
    (e : S ≃* S') (h : IsSectionOf S' X) : IsSectionOf S X := by
  obtain ⟨H, K, hK, ⟨e'⟩⟩ := h
  exact ⟨H, K, hK, ⟨e.trans e'⟩⟩

private theorem burnsideTA12_isSectionOf_subgroup_of_surjective {G S : Type} [Group G] [Group S]
    (Y : Subgroup G) (f : G →* S) (hf : Y.map f = ⊤) : IsSectionOf S ↥Y := by
  have hs : Function.Surjective (f.comp Y.subtype) := by
    intro s
    have hs : s ∈ Y.map f := by rw [hf]; exact Subgroup.mem_top s
    obtain ⟨y, hy, rfl⟩ := hs
    exact ⟨⟨y, hy⟩, rfl⟩
  have e : ↥Y ⧸ (f.comp Y.subtype).ker ≃* S :=
    QuotientGroup.quotientKerEquivOfSurjective _ hs
  exact burnsideTA12_isSectionOf_of_mulEquiv e.symm
    (burnsideTA12_isSectionOf_quotient (X := ↥Y) (f.comp Y.subtype).ker)


private theorem burnsideTA12_layer_eq_top {X : Type*} [Group X] (h : genFittingLayer X = ⊤) :
    CFSG.layer X = ⊤ := by
  rwa [← CFSG.Adapters.genFittingLayer_eq_foundations]

private theorem burnsideTA12_cover (h11 : A_2_11) {G : Type} [Group G] [Finite G] {S : Type} [Group S]
    [Finite S] {p : ℕ} (hmin : IsMinimalCounterexampleToA G S p) :
    ∃ π : G →* S, Function.Surjective π ∧ (∀ Y : Subgroup G, Y ≠ ⊤ → Y.map π ≠ ⊤) ∧
      (Subgroup.center S).comap π = pCore p G := by
  obtain ⟨hcover, K, hKn, ⟨e⟩⟩ := as_A_2_8 G S p hmin
  set π : G →* S := e.symm.toMonoidHom.comp (QuotientGroup.mk' K) with hπdef
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective K)
  have hcov : ∀ Y : Subgroup G, Y ≠ ⊤ → Y.map π ≠ ⊤ := fun Y hY hmap =>
    hY (hcover Y (burnsideTA12_isSectionOf_subgroup_of_surjective Y π hmap))
  refine ⟨π, hπ, hcov, ?_⟩
  have hss : CFSG.layer S = ⊤ := burnsideTA12_layer_eq_top hmin.2.2.2.1
  obtain ⟨hperf, hHn, hnil, hsyl, ⟨e2, he2⟩, hZS, hLS, hZ', hL'⟩ :=
    CFSG.SectionRank.minimal_semisimple_cover hss π hπ hcov
  haveI : ((Subgroup.center S).comap π).Normal := hHn
  haveI : Fact p.Prime := ⟨hmin.2.2.2.2.1⟩
  set H : Subgroup G := (Subgroup.center S).comap π with hH
  have hle : pCore p G ≤ H := by
    have hp : IsPGroup p (pCore p G) := CFSG.pCore_isPGroup
    set N : Subgroup (G ⧸ H) := (pCore p G).map (QuotientGroup.mk' H) with hN
    haveI : N.Normal := Subgroup.Normal.map CFSG.pCore_normal _ (QuotientGroup.mk'_surjective H)
    have hNp : IsPGroup p N := hp.of_surjective ((QuotientGroup.mk' H).subgroupMap (pCore p G))
      ((QuotientGroup.mk' H).subgroupMap_surjective _)
    haveI : Group.IsNilpotent N := hNp.isNilpotent
    have h1 := (CFSG.SectionRank.semisimple_solvable_quotient hL' N inferInstance).1
    rw [hZ'] at h1
    intro x hx
    have hx' : QuotientGroup.mk' H x ∈ N := Subgroup.mem_map_of_mem _ hx
    exact (QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 (h1 hx'))
  obtain ⟨f⟩ := h11 G S p hmin
  have hcard : Nat.card (G ⧸ pCore p G) = Nat.card (G ⧸ H) :=
    Nat.card_congr (f.toEquiv.trans e2.symm.toEquiv)
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore p G)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup H
  rw [hcard] at h1
  have hpos : 0 < Nat.card (G ⧸ H) := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)).ge

structure burnsideTA12_Data (G : Type) [Group G] [Finite G] (H : Subgroup G) : Prop where
  perfect : Group.IsPerfect G
  normal : H.Normal
  center_bot : Subgroup.center (G ⧸ H) = ⊥
  layer_top : CFSG.layer (G ⧸ H) = ⊤

private theorem burnsideTA12_data {G : Type} [Group G] [Finite G] {S : Type} [Group S]
    (hss : CFSG.layer S = ⊤) (π : G →* S) (hπ : Function.Surjective π)
    (hcov : ∀ Y : Subgroup G, Y ≠ ⊤ → Y.map π ≠ ⊤) :
    burnsideTA12_Data G ((Subgroup.center S).comap π) := by
  obtain ⟨hperf, hHn, -, -, -, -, -, hZ', hL'⟩ :=
    CFSG.SectionRank.minimal_semisimple_cover hss π hπ hcov
  exact ⟨hperf, hHn, hZ', hL'⟩

private theorem burnsideTA12_central_of_rank_le_two {G : Type} [Group G]
    [Finite G] {H : Subgroup G} (hD : burnsideTA12_Data G H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hHp : IsPGroup p H) (hrank : CFSG.Open.pRank p H ≤ 2) : H ≤ Subgroup.center G := by
  haveI := hD.normal
  haveI := hD.perfect
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (Nat.card H) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hHp
    rw [hn]
    exact Odd.pow (hp.eq_two_or_odd'.resolve_left hp2)
  refine CFSG.SectionRank.Ccomm.pgroup_le_center_of_perfect H hodd ?_ H le_rfl hHp hrank
  intro N _
  exact (CFSG.SectionRank.centerless_semisimple_quotient hD.layer_top hD.center_bot
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)).2


private theorem burnsideTA12_normal_of_subgroupOf_top {G : Type} [Group G] {N : Subgroup G}
    (hN : (N.subgroupOf ⊤).Normal) : N.Normal := by
  refine ⟨fun k hk g => ?_⟩
  have := hN.conj_mem ⟨k, trivial⟩ (by simpa [Subgroup.mem_subgroupOf] using hk) ⟨g, trivial⟩
  simpa [Subgroup.mem_subgroupOf] using this

private theorem burnsideTA12_le_of_odd_normal {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hD : burnsideTA12_Data G H) {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N)) : N ≤ H := by
  haveI := hD.normal
  set N' : Subgroup (G ⧸ H) := N.map (QuotientGroup.mk' H) with hN'
  haveI : N'.Normal := Subgroup.Normal.map ‹N.Normal› _ (QuotientGroup.mk'_surjective H)
  have hodd : Odd (Nat.card N') := Odd.of_dvd_nat hN (Subgroup.card_map_dvd N _)
  have hsolv : Group.IsSolvable N' := CFSG.Milestones.odd_order_solvable hodd
  have h1 := (CFSG.SectionRank.semisimple_solvable_quotient hD.layer_top N' hsolv).1
  rw [hD.center_bot] at h1
  intro x hx
  have hx' : QuotientGroup.mk' H x ∈ N' := Subgroup.mem_map_of_mem _ hx
  exact (QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 (h1 hx'))

private theorem burnsideTA12_relPPrimeCore_le {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hD : burnsideTA12_Data G H) : relPPrimeCore 2 (⊤ : Subgroup G) ≤ H := by
  refine sSup_le ?_
  rintro N ⟨-, hN, hcop⟩
  haveI := burnsideTA12_normal_of_subgroupOf_top hN
  exact burnsideTA12_le_of_odd_normal hD (Nat.coprime_two_left.mp hcop)

private theorem burnsideTA12_pRank_two_quotient {G : Type} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] (hN : Odd (Nat.card N)) : CFSG.pRank 2 (G ⧸ N) = CFSG.pRank 2 G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnd : ¬ 2 ∣ Nat.card N := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.2 hN
  have h := CFSG.SectionRank.pRank_quotient_eq (p := 2) N hnd
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 2 (G ⧸ N),
    CFSG.SectionRank.pRank_eq_open_pRank_top 2 G]
  exact h

private theorem burnsideTA12_pRank_two_le_two {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hD : burnsideTA12_Data G H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hH : H = pCore p G)
    (hloc : twoLocalPrimeRank p G ≤ 2) (h3 : 2 < CFSG.Open.pRank p H) :
    CFSG.pRank 2 G ≤ 2 := by
  haveI := hD.normal
  have hcore : 2 < CFSG.pRank p ↥(pCoreOf p (⊤ : Subgroup G)) := by
    rw [CFSG.Quasithin.pCoreOf_top, ← hH, CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact h3
  obtain ⟨h1, h2⟩ := as_A_1_28 G p hp hp2 hloc ⊤ hcore
  rw [burnsideTA12_pRank_top_eq] at h1 h2
  by_contra hgt
  have h3' : CFSG.pRank 2 G = 3 := by omega
  obtain ⟨a, -, ha1, ha2, hcomm⟩ := h2 h3'
  have haH : a ∈ H := by
    have hmem : QuotientGroup.mk' H a ∈ Subgroup.center (G ⧸ H) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H y
      have hc := burnsideTA12_relPPrimeCore_le hD (hcomm g trivial)
      have : QuotientGroup.mk' H ⁅a, g⁆ = 1 := (QuotientGroup.eq_one_iff _).2 hc
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at this
      exact this.symm
    rw [hD.center_bot] at hmem
    exact (QuotientGroup.eq_one_iff a).1 (Subgroup.mem_bot.1 hmem)
  have hHp : IsPGroup p H := hH ▸ CFSG.pCore_isPGroup
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hHp) ⟨a, haH⟩
  have hord : orderOf (⟨a, haH⟩ : H) = 2 := by
    have : (⟨a, haH⟩ : H) ^ 2 = 1 := Subtype.ext ha2
    exact orderOf_eq_prime this (fun h => ha1 (congrArg Subtype.val h))
  rw [hord] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  have hdvd : 2 ∣ p ^ k := hk ▸ dvd_refl 2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
    (Nat.prime_two.dvd_of_dvd_pow hdvd)).symm


private theorem burnsideTA12_four_le_pRank_two {X : Type} [Group X]
    [Finite X] (hL : CFSG.layer X = ⊤) (hZ : Subgroup.center X = ⊥) {K₁ K₂ : Subgroup X}
    (h₁ : CFSG.IsComponent K₁) (h₂ : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂) :
    4 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup X) := by
  have hcomm : ⁅K₁, K₂⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute h₁ h₂).resolve_left hne
  have hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x := by
    intro x hx y hy
    have : ⁅x, y⁆ ∈ ⁅K₁, K₂⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hz1 := CFSG.RankThree.OddKernel.center_eq_bot_of_isComponent hL hZ h₁
  have hz2 := CFSG.RankThree.OddKernel.center_eq_bot_of_isComponent hL hZ h₂
  obtain ⟨hs1, hn1⟩ := CFSG.RankThree.OddKernel.isSimpleGroup_of_isQuasisimple h₁.1 hz1
  obtain ⟨hs2, hn2⟩ := CFSG.RankThree.OddKernel.isSimpleGroup_of_isQuasisimple h₂.1 hz2
  obtain ⟨V₁, hV₁c, hV₁2, hV₁4⟩ := CFSG.RankThree.OddKernel.exists_four_group_of_isSimpleGroup hn1
  obtain ⟨V₂, hV₂c, hV₂2, hV₂4⟩ := CFSG.RankThree.OddKernel.exists_four_group_of_isSimpleGroup hn2
  set W₁ : Subgroup X := V₁.map K₁.subtype with hW₁
  set W₂ : Subgroup X := V₂.map K₂.subtype with hW₂
  have hW₁K : W₁ ≤ K₁ := Subgroup.map_subtype_le V₁
  have hW₂K : W₂ ≤ K₂ := Subgroup.map_subtype_le V₂
  have hW₁c : ∀ x ∈ W₁, ∀ y ∈ W₁, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hV₁c x hx y hy)
  have hW₂c : ∀ x ∈ W₂, ∀ y ∈ W₂, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hV₂c x hx y hy)
  have hW₁2 : ∀ x ∈ W₁, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (hV₁2 x hx)
  have hW₂2 : ∀ x ∈ W₂, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (hV₂2 x hx)
  have hW₁4 : Nat.card W₁ = 4 := by
    rw [hW₁, Subgroup.card_map_of_injective K₁.subtype_injective, hV₁4]
  have hW₂4 : Nat.card W₂ = 4 := by
    rw [hW₂, Subgroup.card_map_of_injective K₂.subtype_injective, hV₂4]
  have hinf : W₁ ⊓ W₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z ⟨hz1', hz2'⟩
    have hzc : (⟨z, hW₁K hz1'⟩ : K₁) ∈ Subgroup.center K₁ := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hc y y.2 z (hW₂K hz2'))
    rw [hz1, Subgroup.mem_bot] at hzc
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hzc)
  obtain ⟨V, hVc, hV2, hV16⟩ := CFSG.RankThree.OddKernel.exists_elementary_sixteen hW₁c hW₂c hW₁2
    hW₂2 hW₁4 hW₂4 (fun x hx y hy => hc x (hW₁K hx) y (hW₂K hy)) hinf
  exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) (le_top : V ≤ ⊤)
    ⟨⟨⟨fun a b => Subtype.ext (hVc a a.2 b b.2)⟩⟩, fun x hx => hV2 x hx⟩
    (by rw [hV16]; norm_num)

private theorem burnsideTA12_isSimple_of_rank {X : Type} [Group X]
    [Finite X] [Nontrivial X] (hL : CFSG.layer X = ⊤) (hZ : Subgroup.center X = ⊥)
    (hr : CFSG.Open.pRank 2 (⊤ : Subgroup X) < 4) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  by_cases hex : ∃ K : Subgroup X, CFSG.IsComponent K
  swap
  · exfalso
    push Not at hex
    have h1 : CFSG.layer X = ⊥ := CFSG.LocalCores.layer_eq_bot_of_forall hex
    rw [hL] at h1
    exact (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup X)).1 inferInstance h1
  obtain ⟨K₁, h₁⟩ := hex
  by_cases hK : K₁ = ⊤
  · subst hK
    have hq : CFSG.IsQuasisimple X :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv h₁.1
    exact CFSG.RankThree.OddKernel.isSimpleGroup_of_isQuasisimple hq hZ
  · exfalso
    by_cases hall : ∀ K : Subgroup X, CFSG.IsComponent K → K = K₁
    · apply hK
      have hle : CFSG.layer X ≤ K₁ := by
        rw [CFSG.layer.eq_sSup]
        exact sSup_le fun K hK' => (hall K hK').le
      rw [hL] at hle
      exact top_le_iff.1 hle
    · push Not at hall
      obtain ⟨K₂, h₂, hne⟩ := hall
      have := burnsideTA12_four_le_pRank_two hL hZ h₁ h₂ hne.symm
      omega


private theorem burnsideTA12_ringChar_eq {F : Type} [Field F] [Finite F] {s f : ℕ} (hs : s.Prime)
    (hf : 0 < f) (hF : Nat.card F = s ^ f) : ringChar F = s := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  rw [← Nat.card_eq_fintype_card, hF] at hn
  have hd : s ∣ (ringChar F) ^ (n : ℕ) := by
    rw [← hn]
    exact dvd_pow_self s hf.ne'
  exact ((Nat.prime_dvd_prime_iff_eq hs hp).1 (hs.dvd_of_dvd_pow hd)).symm

@[expose] def burnsideTA12_u (F : Type) [Field F] :
    Multiplicative F →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun a := ⟨!![1, Multiplicative.toAdd a; 0, 1], by simp [Matrix.det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    show (!![1, Multiplicative.toAdd (1 : Multiplicative F); 0, 1] : Matrix (Fin 2) (Fin 2) F) = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    show (!![1, Multiplicative.toAdd (a * b); 0, 1] : Matrix (Fin 2) (Fin 2) F) =
      !![1, Multiplicative.toAdd a; 0, 1] * !![1, Multiplicative.toAdd b; 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem burnsideTA12_u_apply (F : Type) [Field F] (a : Multiplicative F) :
    ((burnsideTA12_u F a : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, Multiplicative.toAdd a; 0, 1] := rfl

private theorem burnsideTA12_u_injective (F : Type) [Field F] : Function.Injective (burnsideTA12_u F) := by
  intro a b h
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp only [burnsideTA12_u_apply] at this
  simpa using this

private theorem burnsideTA12_exists_elem_sl2 {F : Type} [Field F] [Finite F] {s f : ℕ} (hs : s.Prime)
    (hF : Nat.card F = s ^ f) (hchar : ringChar F = s) :
    ∃ E : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F),
      IsElemAbelian s E ∧ Nat.card E = s ^ f := by
  haveI : CharP F s := hchar ▸ ringChar.charP F
  refine ⟨(burnsideTA12_u F).range, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ s = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    rw [this, map_one]
  · rw [← hF, Nat.card_congr (MonoidHom.ofInjective (burnsideTA12_u_injective F)).toEquiv.symm]
    exact Nat.card_congr Multiplicative.toAdd

private theorem burnsideTA12_center_sl2_ne_bot {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ≠ ⊥ := by
  intro hbot
  have hmem : (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by norm_num, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 0) hmem
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at h1
  simp at h1
  exact h2 (by linear_combination -h1)

private theorem burnsideTA12_genFittingLayer_top_of_quasisimple {X : Type*} [Group X]
    (h : CFSG.IsQuasisimple X) : genFittingLayer X = ⊤ := by
  rw [CFSG.Adapters.genFittingLayer_eq_foundations]
  refine top_unique ?_
  rw [CFSG.layer.eq_sSup]
  refine le_sSup ?_
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm h,
    Subgroup.IsSubnormal.top⟩


private theorem burnsideTA12_isPerfect_of_sup {X : Type} [Group X] {H H₁ H₂ : Subgroup X}
    (hsup : H = H₁ ⊔ H₂) (h₁ : IsComponentOf H₁ H) (h₂ : IsComponentOf H₂ H) :
    Group.IsPerfect ↥H := by
  have hq : ∀ L : Subgroup X, IsComponentOf L H → ⁅L, L⁆ = L := by
    intro L hL
    haveI : Group.IsPerfect ↥L := Group.isPerfect_def.2 hL.2.2.1
    exact Subgroup.commutator_eq_self
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  calc H = H₁ ⊔ H₂ := hsup
    _ = ⁅H₁, H₁⁆ ⊔ ⁅H₂, H₂⁆ := by rw [hq H₁ h₁, hq H₂ h₂]
    _ ≤ ⁅H, H⁆ := sup_le (Subgroup.commutator_mono h₁.1 h₁.1) (Subgroup.commutator_mono h₂.1 h₂.1)

private theorem burnsideTA12_center_eq_bot_of_clauseB {X : Type} [Group X] {S' : Type} [Group S']
    {H H₁ H₂ : Subgroup X} (e : S' ≃* ↥H ⧸ Subgroup.center ↥H) (hsup : H = H₁ ⊔ H₂)
    (h₁ : IsComponentOf H₁ H) (h₂ : IsComponentOf H₂ H) : Subgroup.center S' = ⊥ := by
  haveI : Group.IsPerfect ↥H := burnsideTA12_isPerfect_of_sup hsup h₁ h₂
  have hc := Group.IsPerfect.center_quotient_center_eq_bot (G := ↥H)
  rw [eq_bot_iff]
  intro z hz
  have hmem : e z ∈ Subgroup.center (↥H ⧸ Subgroup.center ↥H) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := Subgroup.mem_center_iff.1 hz (e.symm y)
    have h2 := congrArg e h1
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2
  rw [hc, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.2 (e.injective (by rw [hmem, map_one]))


private theorem burnsideTA12_isTwoLocal_top_of_central {X : Type} [Group X] {z : X}
    (hz : z ∈ Subgroup.center X) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    IsTwoLocal (⊤ : Subgroup X) := by
  refine ⟨Subgroup.zpowers z, ?_, ?_, ?_⟩
  · intro h
    exact hz1 (by simpa using (Subgroup.zpowers_eq_bot.1 h))
  · have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  · symm
    rw [Subgroup.eq_top_iff']
    intro g
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc : Commute g z := Subgroup.mem_center_iff.1 hz g
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      rw [(hc.zpow_right k).mul_inv_cancel]
      exact hh
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
      have h1 : h = g⁻¹ * (g * h * g⁻¹) * g := by group
      have hck : Commute g⁻¹ (z ^ k) := (hc.zpow_right k).inv_left
      rw [h1, ← hk, hck.eq, inv_mul_cancel_right]
      exact Subgroup.zpow_mem_zpowers z k

private theorem burnsideTA12_neg_one_sl2 {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ∧
      (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ^ 2 = 1 ∧
      (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by norm_num, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · apply Subtype.ext
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    simp
  · intro h
    have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at h1
    simp at h1
    exact h2 (by linear_combination -h1)

private theorem burnsideTA12_le_twoLocalPrimeRank_sl2 {F : Type} [Field F] [Finite F] {s f : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hf : 0 < f) (hF : Nat.card F = s ^ f) :
    f ≤ twoLocalPrimeRank s (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hchar : ringChar F = s := burnsideTA12_ringChar_eq hs hf hF
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [hchar]; exact hs2)
  obtain ⟨hz, hz2, hz1⟩ := burnsideTA12_neg_one_sl2 h2F
  have hT := burnsideTA12_isTwoLocal_top_of_central hz hz2 hz1
  obtain ⟨E, hE, hcard⟩ := burnsideTA12_exists_elem_sl2 hs hF hchar
  have hrank : f ≤ CFSG.Open.pRank s (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    have := CFSG.SectionRank.le_pRank hs.one_lt (le_top : E ≤ ⊤) hE hcard
    exact this
  refine hrank.trans (le_csSup ⟨Nat.card (Matrix.SpecialLinearGroup (Fin 2) F), ?_⟩ ⟨⊤, hT, rfl⟩)
  rintro _ ⟨K, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hs.one_lt K

private theorem burnsideTA12_false_of_sl2 {G : Type} [Group G] [Finite G] (hev : evenRank G ≤ 2)
    (hKG : CFSG.SectionRank.IsKGroupCat G)
    (hprop : ∀ (X : Type) [Group X] [Finite X], IsProperSectionOf X G → TheoremAHolds X)
    {H : Subgroup G} [H.Normal] (hZ : Subgroup.center (G ⧸ H) = ⊥)
    {s f : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hf : 3 ≤ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = s ^ f) (φ : Matrix.SpecialLinearGroup (Fin 2) F →* G ⧸ H)
    (hφ : Function.Injective φ) : False := by
  have hchar : ringChar F = s := burnsideTA12_ringChar_eq hs (by omega) hF
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [hchar]; exact hs2)
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ s ^ 3 := Nat.pow_le_pow_left hs.two_le 3
      _ ≤ s ^ f := Nat.pow_le_pow_right hs.pos hf
  set Y : Subgroup (G ⧸ H) := φ.range with hY
  set M : Subgroup G := Y.comap (QuotientGroup.mk' H) with hM
  have hMne : M ≠ ⊤ := by
    intro hMtop
    have hYtop : Y = ⊤ := by
      have h1 : Y.comap (QuotientGroup.mk' H) = ⊤ := hMtop
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective H) Y, h1,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective H)]
    obtain ⟨hz, -, hz1⟩ := burnsideTA12_neg_one_sl2 h2F
    have hcen : φ (-1) ∈ Subgroup.center (G ⧸ H) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy : y ∈ Y := by rw [hYtop]; exact Subgroup.mem_top y
      obtain ⟨w, rfl⟩ := hy
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz w).symm]
    rw [hZ, Subgroup.mem_bot] at hcen
    exact hz1 (hφ (by rw [hcen, map_one]))
  have hMprop : IsProperSectionOf ↥M G := burnsideTA12_isProperSectionOf_subgroup M hMne
  have hA : TheoremAHolds ↥M := hprop ↥M hMprop
  have hevM : evenRank ↥M ≤ 2 :=
    (burnsideTA12_evenRank_le_of_injective M.subtype M.subtype_injective).trans hev
  have hKM : CFSG.SectionRank.IsKGroupCat ↥M := hKG.subgroup M
  let ψ : ↥M →* ↥Y := ((QuotientGroup.mk' H).comp M.subtype).codRestrict Y fun m => m.2
  let f' : ↥M →* Matrix.SpecialLinearGroup (Fin 2) F :=
    (MonoidHom.ofInjective hφ).symm.toMonoidHom.comp ψ
  have hf' : Function.Surjective f' := by
    intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective H (φ x)
    have hgM : g ∈ M := by
      show QuotientGroup.mk' H g ∈ Y
      rw [hg]
      exact ⟨x, rfl⟩
    refine ⟨⟨g, hgM⟩, ?_⟩
    show (MonoidHom.ofInjective hφ).symm ⟨QuotientGroup.mk' H g, _⟩ = x
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    exact hg
  have hsec : IsSectionOf (Matrix.SpecialLinearGroup (Fin 2) F) ↥M :=
    burnsideTA12_isSectionOf_of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective f' hf').symm
      (burnsideTA12_isSectionOf_quotient f'.ker)
  have hss : genFittingLayer (Matrix.SpecialLinearGroup (Fin 2) F) = ⊤ :=
    burnsideTA12_genFittingLayer_top_of_quasisimple (CFSG.GH74.KGroups.L3Eps.isQuasisimple_sl2c h4)
  have hconc := (hA hevM hKM _ hsec hss).1 s hs hs2
  have hloc := burnsideTA12_le_twoLocalPrimeRank_sl2 hs hs2 (by omega) hF
  have hM2 : twoLocalPrimeRank s ↥M ≤ 2 :=
    (burnsideTA12_twoLocalPrimeRank_le_evenRank hs hs2).trans hevM
  unfold TheoremAConclusion at hconc
  rcases hconc.1 with ⟨ha, hb⟩ | ⟨-, H', H₁, H₂, n₁, n₂, ⟨e⟩, -, hsup, hc1, hc2, -⟩
  · omega
  · exact burnsideTA12_center_sl2_ne_bot h2F
      (burnsideTA12_center_eq_bot_of_clauseB e hsup hc1 hc2)


open CFSG.Blueprint in
@[expose] def burnsideTA12_Rank2Fact : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    twoRank T = 2 →
    (∀ r : ℕ, r.Prime → r ≠ 2 → twoLocalPrimeRank r T ≤ 2) ∨
    (∃ s f : ℕ, s.Prime ∧ s ≠ 2 ∧ 3 ≤ f ∧
      (StatedClassicalModel T .PSL 3 s f ∨ StatedClassicalModel T .PSU 3 s f) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = s ^ f ∧
        ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* T, Function.Injective φ)

@[expose] def burnsideTA12_CoverFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p.Prime → p ≠ 2 → CFSG.IsQuasisimple S →
    twoRank (S ⧸ Subgroup.center S) = 2 → Subgroup.center S ≠ ⊥ →
    IsPGroup p ↥(Subgroup.center S) → CFSG.pRank p S ≤ 2

@[expose] def burnsideTA12_CForSections (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsProperSectionOf X G → TheoremCHolds X

@[expose] def burnsideTA12_PairFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G], evenRank G ≤ 2 → CFSG.SectionRank.IsKGroupCat G →
    burnsideTA12_CForSections G →
    ∀ L₁ L₂ : Subgroup G, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ → L₁ ≠ L₂ →
      ∀ r : ℕ, r.Prime → r ≠ 2 → IsPGroup r ↥(Subgroup.center ↥L₁) →
        IsPGroup r ↥(Subgroup.center ↥L₂) → Subgroup.center ↥L₁ ≠ ⊥ → Subgroup.center ↥L₂ ≠ ⊥ →
        r = 3 ∧ Nat.card (Subgroup.center ↥L₁) = 3 ∧ CFSG.layer G = L₁ ⊔ L₂ ∧
          CFSG.pRank 3 ↥(L₁ ⊔ L₂) = 3 ∧ centerOf L₁ = centerOf L₂ ∧
          ∃ n₁ n₂ : ℕ, IsSUn 3 (2 ^ n₁) ↥L₁ ∧ IsSUn 3 (2 ^ n₂) ↥L₂ ∧ 3 ≤ n₁ ∧ Odd n₁ ∧ 3 ≤ n₂ ∧
            Odd n₂ ∧ (Nat.gcd n₁ n₂ = 1 ∨ Nat.gcd n₁ n₂ = 3)

private theorem burnsideTA12_theoremAConclusion_of_injective {G : Type} [Group G] [Finite G] {S : Type}
    [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hev : evenRank G ≤ 2)
    (f : S →* G) (hf : Function.Injective f) : TheoremAConclusion G S p := by
  unfold TheoremAConclusion
  refine ⟨Or.inl ⟨burnsideTA12_twoLocalPrimeRank_le_of_injective hp f hf,
    (burnsideTA12_twoLocalPrimeRank_le_evenRank hp hp2).trans hev⟩, fun _ => ?_⟩
  simp only [burnsideTA12_pRank_top_eq]
  exact burnsideTA12_pRank_le_of_injective hp.one_lt f hf

private theorem burnsideTA12_twoLocalPrimeRank_congr {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y] {p : ℕ} (hp : p.Prime) (e : X ≃* Y) :
    twoLocalPrimeRank p X = twoLocalPrimeRank p Y :=
  le_antisymm (burnsideTA12_twoLocalPrimeRank_le_of_injective hp e.toMonoidHom e.injective)
    (burnsideTA12_twoLocalPrimeRank_le_of_injective hp e.symm.toMonoidHom e.symm.injective)

private theorem burnsideTA12_no_injective {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S]
    {p : ℕ} (hmin : IsMinimalCounterexampleToA G S p) (f : S →* G) : ¬ Function.Injective f := by
  obtain ⟨hev, -, -, -, hp, hp2, hnc, -⟩ := hmin
  exact fun hf => hnc (burnsideTA12_theoremAConclusion_of_injective hp hp2 hev f hf)


private theorem burnsideTA12_two_le_pRank_two {X : Type} [Group X]
    [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) :
    2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup X) := by
  obtain ⟨V, hVc, hV2, hV4⟩ := CFSG.RankThree.OddKernel.exists_four_group_of_isSimpleGroup hnab
  exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) (le_top : V ≤ ⊤)
    ⟨⟨⟨fun a b => Subtype.ext (hVc a a.2 b b.2)⟩⟩, fun x hx => hV2 x hx⟩
    (by rw [hV4]; norm_num)

private theorem burnsideTA12_equiv {G : Type} [Group G] [Finite G] {S : Type} [Group S]
    (hss : CFSG.layer S = ⊤) (π : G →* S) (hπ : Function.Surjective π)
    (hcov : ∀ Y : Subgroup G, Y ≠ ⊤ → Y.map π ≠ ⊤) :
    ∃ e : G ⧸ (Subgroup.center S).comap π ≃* S ⧸ Subgroup.center S,
      ∀ x : G, e (QuotientGroup.mk x) = QuotientGroup.mk (π x) := by
  obtain ⟨-, -, -, -, he, -⟩ := CFSG.SectionRank.minimal_semisimple_cover hss π hπ hcov
  exact he

private theorem burnsideTA12_noncentral_false
    (hR2F : burnsideTA12_Rank2Fact) (hCover : burnsideTA12_CoverFact)
    {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S] {p : ℕ}
    (hmin : IsMinimalCounterexampleToA G S p) (π : G →* S) (hπ : Function.Surjective π)
    (hcov : ∀ Y : Subgroup G, Y ≠ ⊤ → Y.map π ≠ ⊤)
    (hH : (Subgroup.center S).comap π = pCore p G)
    (hnc : ¬ (Subgroup.center S).comap π ≤ Subgroup.center G) : False := by
  have hev : evenRank G ≤ 2 := hmin.1
  have hKG : CFSG.SectionRank.IsKGroupCat G := hmin.2.1
  have hp : p.Prime := hmin.2.2.2.2.1
  have hp2 : p ≠ 2 := hmin.2.2.2.2.2.1
  have hprop := hmin.2.2.2.2.2.2.2
  have hss : CFSG.layer S = ⊤ := burnsideTA12_layer_eq_top hmin.2.2.2.1
  set H : Subgroup G := (Subgroup.center S).comap π with hHdef
  have hD : burnsideTA12_Data G H := burnsideTA12_data hss π hπ hcov
  haveI := hD.normal
  haveI := hD.perfect
  have hHp : IsPGroup p H := hH ▸ CFSG.pCore_isPGroup
  haveI : Fact p.Prime := ⟨hp⟩
  have hrank3 : 2 < CFSG.Open.pRank p H := by
    by_contra hle
    exact hnc (burnsideTA12_central_of_rank_le_two hD hp hp2 hHp (not_lt.mp hle))
  have hloc : twoLocalPrimeRank p G ≤ 2 :=
    (burnsideTA12_twoLocalPrimeRank_le_evenRank hp hp2).trans hev
  have h2G : CFSG.pRank 2 G ≤ 2 := burnsideTA12_pRank_two_le_two hD hp hp2 hH hloc hrank3
  have hHodd : Odd (Nat.card H) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hHp
    rw [hn]
    exact Odd.pow (hp.eq_two_or_odd'.resolve_left hp2)
  have h2Gb : CFSG.pRank 2 (G ⧸ H) ≤ 2 := by
    rw [burnsideTA12_pRank_two_quotient H hHodd]
    exact h2G
  haveI : Nontrivial (G ⧸ H) := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    have hHtop : H = ⊤ := by
      rw [← Subgroup.index_eq_one, Subgroup.index_eq_card]
      exact Nat.card_of_subsingleton (1 : G ⧸ H)
    have hGp : IsPGroup p G := by
      have := hHp
      rw [hHtop] at this
      exact this.of_equiv Subgroup.topEquiv
    haveI : Group.IsNilpotent G := hGp.isNilpotent
    haveI : Subsingleton G := by
      by_contra hns
      haveI : Nontrivial G := not_subsingleton_iff_nontrivial.1 hns
      exact Group.IsPerfect.not_isNilpotent G inferInstance
    exact burnsideTA12_no_injective hmin 1 (fun a b _ => by
      have : Subsingleton S := Function.Surjective.subsingleton hπ
      exact Subsingleton.elim a b)
  have hsimp := burnsideTA12_isSimple_of_rank (X := G ⧸ H) hD.layer_top hD.center_bot
    (by rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]; omega)
  obtain ⟨hsimple, hnab⟩ := hsimp
  have hr2 : CFSG.Open.pRank 2 (⊤ : Subgroup (G ⧸ H)) = 2 := by
    have h1 := burnsideTA12_two_le_pRank_two hnab
    have h2 : CFSG.Open.pRank 2 (⊤ : Subgroup (G ⧸ H)) ≤ 2 := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact h2Gb
    omega
  have hmapH : H.map π = Subgroup.center S := Subgroup.map_comap_eq_self_of_surjective hπ _
  have hZp : IsPGroup p ↥(Subgroup.center S) := by
    have h := hHp.of_surjective (π.subgroupMap H) (π.subgroupMap_surjective H)
    rw [hmapH] at h
    exact h
  have hpgt : 2 < CFSG.pRank p ↥(⊤ : Subgroup G) := by
    rw [burnsideTA12_pRank_top_eq, CFSG.SectionRank.pRank_eq_open_pRank_top p G]
    exact lt_of_lt_of_le hrank3 (CFSG.SectionRank.pRank_mono hp.one_lt le_top)
  rcases hR2F (G ⧸ H) hsimple hnab hr2 with hi | ⟨s, f, hs, hs2, hf, -, F, _, _, hF, φ, hφ⟩
  swap
  · exact burnsideTA12_false_of_sl2 hev hKG hprop hD.center_bot hs hs2 hf hF φ hφ
  obtain ⟨e, he⟩ := burnsideTA12_equiv hss π hπ hcov
  haveI := hsimple
  have hq : CFSG.IsQuasisimple S := by
    refine ⟨Group.IsPerfect.ofSurjective (f := π) hπ, e.symm.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  have hSloc : twoLocalPrimeRank p S ≤ 2 := by
    by_cases hZS : Subgroup.center S = ⊥
    · have hinj : Function.Injective
          (e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center S))) := by
        refine e.symm.injective.comp ?_
        rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZS]
      exact (burnsideTA12_twoLocalPrimeRank_le_of_injective hp _ hinj).trans (hi p hp hp2)
    · have hr2S : twoRank (S ⧸ Subgroup.center S) = 2 :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) e).symm.trans hr2
      exact (burnsideTA12_twoLocalPrimeRank_le_pRank hp).trans
        (hCover S p hp hp2 hq hr2S hZS hZp)
  have h1 : twoLocalPrimeRank p S ≤ twoLocalPrimeRank p G := by
    have hA7 := (as_A_2_7 G π.ker p hp hp2).2.2.2.1
    have eS : G ⧸ π.ker ≃* S := QuotientGroup.quotientKerEquivOfSurjective π hπ
    rw [burnsideTA12_twoLocalPrimeRank_congr hp eS] at hA7
    exact hA7 hSloc
  refine hmin.2.2.2.2.2.2.1 ?_
  unfold TheoremAConclusion
  refine ⟨Or.inl ⟨h1, hloc⟩, fun hle => ?_⟩
  exact absurd hle (by omega)


private theorem burnsideTA12_card_eq_pow_of_isElemAbelian {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {E : Subgroup X} (hE : IsElemAbelian p E) : ∃ k : ℕ, Nat.card E = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact IsPGroup.iff_card.1 fun g => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hE.2 _ g.2)⟩

private theorem burnsideTA12_twoLocalPrimeRank_le_of_bound {X : Type*} [Group X] [Finite X] {p : ℕ} {k : ℕ}
    (h : ∀ R : Subgroup X, R ≠ ⊥ → IsPGroup 2 R →
      CFSG.Open.pRank p (Subgroup.normalizer (R : Set X)) ≤ k) :
    twoLocalPrimeRank p X ≤ k := by
  refine csSup_le' ?_
  rintro _ ⟨H, ⟨R, hR, hR2, rfl⟩, rfl⟩
  exact h R hR hR2

private theorem burnsideTA12_pRank_normalizer_le {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {T : Subgroup X} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) :
    CFSG.Open.pRank p (Subgroup.normalizer (T : Set X)) ≤ twoLocalPrimeRank p X := by
  refine le_csSup ⟨Nat.card X, ?_⟩ ⟨_, ⟨T, hT, hT2, rfl⟩, rfl⟩
  rintro _ ⟨K, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hp.one_lt K

private theorem burnsideTA12_card_le_prod_map {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (E : Subgroup (X × Y)) :
    Nat.card E ≤ Nat.card (E.map (MonoidHom.fst X Y)) * Nat.card (E.map (MonoidHom.snd X Y)) := by
  let f : E → (E.map (MonoidHom.fst X Y)) × (E.map (MonoidHom.snd X Y)) := fun e =>
    (⟨(e : X × Y).1, Subgroup.mem_map_of_mem (MonoidHom.fst X Y) e.2⟩,
      ⟨(e : X × Y).2, Subgroup.mem_map_of_mem (MonoidHom.snd X Y) e.2⟩)
  have hf : Function.Injective f := by
    intro a b h
    have h1 := congrArg (fun z => (z.1 : X)) h
    have h2 := congrArg (fun z => (z.2 : Y)) h
    exact Subtype.ext (Prod.ext h1 h2)
  calc Nat.card E ≤ Nat.card ((E.map (MonoidHom.fst X Y)) × (E.map (MonoidHom.snd X Y))) :=
        Nat.card_le_card_of_injective f hf
    _ = _ := Nat.card_prod _ _

private theorem burnsideTA12_pRank_le_prod {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    {p : ℕ} (hp : p.Prime) (H : Subgroup (X × Y)) :
    CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (H.map (MonoidHom.fst X Y)) +
      CFSG.Open.pRank p (H.map (MonoidHom.snd X Y)) := by
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E hEH hE => ?_
  have hE1 : IsElemAbelian p (E.map (MonoidHom.fst X Y)) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  have hE2 : IsElemAbelian p (E.map (MonoidHom.snd X Y)) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  obtain ⟨a, ha⟩ := burnsideTA12_card_eq_pow_of_isElemAbelian hp hE1
  obtain ⟨b, hb⟩ := burnsideTA12_card_eq_pow_of_isElemAbelian hp hE2
  have ha' : a ≤ CFSG.Open.pRank p (H.map (MonoidHom.fst X Y)) :=
    CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.map_mono hEH) hE1 ha
  have hb' : b ≤ CFSG.Open.pRank p (H.map (MonoidHom.snd X Y)) :=
    CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.map_mono hEH) hE2 hb
  calc Nat.card E ≤ _ := burnsideTA12_card_le_prod_map E
    _ = p ^ a * p ^ b := by rw [ha, hb]
    _ = p ^ (a + b) := (pow_add p a b).symm
    _ ≤ _ := Nat.pow_le_pow_right hp.pos (add_le_add ha' hb')

private theorem burnsideTA12_isPGroup_map {X Y : Type*} [Group X] [Group Y] {T : Subgroup X}
    (hT : IsPGroup 2 T) (f : X →* Y) : IsPGroup 2 (T.map f) :=
  hT.of_surjective (f.subgroupMap T) (f.subgroupMap_surjective T)

private theorem burnsideTA12_twoLocalPrimeRank_prod_le {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y] {r : ℕ} (hr : r.Prime) :
    twoLocalPrimeRank r (X × Y) ≤
      max (twoLocalPrimeRank r X + CFSG.Open.pRank r (⊤ : Subgroup Y))
        (CFSG.Open.pRank r (⊤ : Subgroup X) + twoLocalPrimeRank r Y) := by
  refine burnsideTA12_twoLocalPrimeRank_le_of_bound fun T hT hT2 => ?_
  set N : Subgroup (X × Y) := Subgroup.normalizer (T : Set (X × Y)) with hN
  have hbound := burnsideTA12_pRank_le_prod hr N
  set TX : Subgroup X := T.map (MonoidHom.fst X Y) with hTX
  set TY : Subgroup Y := T.map (MonoidHom.snd X Y) with hTY
  have hNX : N.map (MonoidHom.fst X Y) ≤ Subgroup.normalizer (TX : Set X) :=
    Subgroup.le_normalizer_map (MonoidHom.fst X Y)
  have hNY : N.map (MonoidHom.snd X Y) ≤ Subgroup.normalizer (TY : Set Y) :=
    Subgroup.le_normalizer_map (MonoidHom.snd X Y)
  have hTX2 : IsPGroup 2 TX := burnsideTA12_isPGroup_map hT2 _
  have hTY2 : IsPGroup 2 TY := burnsideTA12_isPGroup_map hT2 _
  have hX_top : CFSG.Open.pRank r (N.map (MonoidHom.fst X Y)) ≤
      CFSG.Open.pRank r (⊤ : Subgroup X) := CFSG.SectionRank.pRank_mono hr.one_lt le_top
  have hY_top : CFSG.Open.pRank r (N.map (MonoidHom.snd X Y)) ≤
      CFSG.Open.pRank r (⊤ : Subgroup Y) := CFSG.SectionRank.pRank_mono hr.one_lt le_top
  have hX_loc : TX ≠ ⊥ → CFSG.Open.pRank r (N.map (MonoidHom.fst X Y)) ≤ twoLocalPrimeRank r X :=
    fun h => (CFSG.SectionRank.pRank_mono hr.one_lt hNX).trans
      (burnsideTA12_pRank_normalizer_le hr h hTX2)
  have hY_loc : TY ≠ ⊥ → CFSG.Open.pRank r (N.map (MonoidHom.snd X Y)) ≤ twoLocalPrimeRank r Y :=
    fun h => (CFSG.SectionRank.pRank_mono hr.one_lt hNY).trans
      (burnsideTA12_pRank_normalizer_le hr h hTY2)
  have hTne : TX ≠ ⊥ ∨ TY ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hT
    rw [Subgroup.eq_bot_iff_forall]
    intro t ht
    have h1 : t.1 ∈ TX := Subgroup.mem_map_of_mem (MonoidHom.fst X Y) ht
    have h2 : t.2 ∈ TY := Subgroup.mem_map_of_mem (MonoidHom.snd X Y) ht
    rw [hcon.1, Subgroup.mem_bot] at h1
    rw [hcon.2, Subgroup.mem_bot] at h2
    exact Prod.ext h1 h2
  rcases hTne with h | h
  · exact hbound.trans ((add_le_add (hX_loc h) hY_top).trans (le_max_left _ _))
  · exact hbound.trans ((add_le_add hX_top (hY_loc h)).trans (le_max_right _ _))

private theorem burnsideTA12_isElemAbelian_prod {X Y : Type*} [Group X] [Group Y] {p : ℕ}
    {E₁ : Subgroup X} {E₂ : Subgroup Y} (h₁ : IsElemAbelian p E₁) (h₂ : IsElemAbelian p E₂) :
    IsElemAbelian p (E₁.prod E₂) := by
  have c1 := h₁.1
  have c2 := h₂.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    change (a : X × Y) * b = b * a
    refine Prod.ext ?_ ?_
    · exact congrArg Subtype.val
        (c1.is_comm.comm (⟨(a : X × Y).1, a.2.1⟩ : E₁) ⟨(b : X × Y).1, b.2.1⟩)
    · exact congrArg Subtype.val
        (c2.is_comm.comm (⟨(a : X × Y).2, a.2.2⟩ : E₂) ⟨(b : X × Y).2, b.2.2⟩)
  · exact Prod.ext (h₁.2 _ hx.1) (h₂.2 _ hx.2)

private theorem burnsideTA12_pRank_prod_ge {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    {p : ℕ} (hp : p.Prime) (A : Subgroup X) (B : Subgroup Y) :
    CFSG.Open.pRank p A + CFSG.Open.pRank p B ≤ CFSG.Open.pRank p (A.prod B) := by
  obtain ⟨E₁, hE₁A, hE₁, hc₁⟩ := CFSG.SectionRank.exists_pRank hp.one_lt A
  obtain ⟨E₂, hE₂B, hE₂, hc₂⟩ := CFSG.SectionRank.exists_pRank hp.one_lt B
  refine CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.prod_mono hE₁A hE₂B)
    (burnsideTA12_isElemAbelian_prod hE₁ hE₂) ?_
  rw [Nat.card_congr (Subgroup.prodEquiv E₁ E₂).toEquiv, Nat.card_prod, hc₁, hc₂, pow_add]


private theorem burnsideTA12_twoLocal_add_pRank_le {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y] {r : ℕ} (hr : r.Prime) (hX : ∃ T : Subgroup X, T ≠ ⊥ ∧ IsPGroup 2 T) :
    twoLocalPrimeRank r X + CFSG.Open.pRank r (⊤ : Subgroup Y) ≤ twoLocalPrimeRank r (X × Y) := by
  have hbdd : BddAbove {k | ∃ H : Subgroup X, IsTwoLocal H ∧ CFSG.Open.pRank r H = k} := by
    refine ⟨Nat.card X, ?_⟩
    rintro _ ⟨K, -, rfl⟩
    exact CFSG.SectionRank.pRank_le_card_of_one_lt hr.one_lt K
  have hne : {k | ∃ H : Subgroup X, IsTwoLocal H ∧ CFSG.Open.pRank r H = k}.Nonempty := by
    obtain ⟨T, hT, hT2⟩ := hX
    exact ⟨_, _, ⟨T, hT, hT2, rfl⟩, rfl⟩
  obtain ⟨H, ⟨T₀, hT₀, hT₀2, rfl⟩, hH⟩ := Nat.sSup_mem hne hbdd
  change CFSG.Open.pRank r (Subgroup.normalizer (T₀ : Set X)) = twoLocalPrimeRank r X at hH
  rw [← hH]
  set T' : Subgroup (X × Y) := T₀.prod ⊥ with hT'
  have hT'ne : T' ≠ ⊥ := by
    intro h
    obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hT₀)
    have : (t, (1 : Y)) ∈ T' := ⟨ht, Subgroup.one_mem _⟩
    rw [h, Subgroup.mem_bot] at this
    exact ht1 (Subtype.ext (by simpa using congrArg Prod.fst this))
  have hT'2 : IsPGroup 2 T' := by
    let f : ↥T' →* ↥T₀ := ⟨⟨fun x => ⟨(x : X × Y).1, x.2.1⟩, rfl⟩, fun x y => rfl⟩
    have hf : Function.Injective f := by
      intro x y h
      have h1 := congrArg Subtype.val h
      have h2x : (x : X × Y).2 = 1 := Subgroup.mem_bot.1 x.2.2
      have h2y : (y : X × Y).2 = 1 := Subgroup.mem_bot.1 y.2.2
      exact Subtype.ext (Prod.ext h1 (h2x.trans h2y.symm))
    exact hT₀2.of_injective f hf
  have hsub : (Subgroup.normalizer (T₀ : Set X)).prod (⊤ : Subgroup Y) ≤
      Subgroup.normalizer (T' : Set (X × Y)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    rintro ⟨a, b⟩
    have hx1 := Subgroup.mem_normalizer_iff.1 hx.1 a
    simp only [hT', Subgroup.mem_prod, Subgroup.mem_bot]
    have e1 : (x * (a, b) * x⁻¹).1 = x.1 * a * x.1⁻¹ := rfl
    have e2 : (x * (a, b) * x⁻¹).2 = x.2 * b * x.2⁻¹ := rfl
    rw [e1, e2, ← hx1]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [h2]; group⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have h3 := congrArg (fun z => x.2⁻¹ * z * x.2) h2
      simpa [mul_assoc] using h3
  calc CFSG.Open.pRank r (Subgroup.normalizer (T₀ : Set X)) + CFSG.Open.pRank r (⊤ : Subgroup Y)
      ≤ CFSG.Open.pRank r ((Subgroup.normalizer (T₀ : Set X)).prod (⊤ : Subgroup Y)) :=
        burnsideTA12_pRank_prod_ge hr _ _
    _ ≤ CFSG.Open.pRank r (Subgroup.normalizer (T' : Set (X × Y))) :=
        CFSG.SectionRank.pRank_mono hr.one_lt hsub
    _ ≤ twoLocalPrimeRank r (X × Y) := burnsideTA12_pRank_normalizer_le hr hT'ne hT'2

private theorem burnsideTA12_pRank_add_twoLocal_le {X Y : Type} [Group X] [Group Y] [Finite X]
    [Finite Y] {r : ℕ} (hr : r.Prime) (hY : ∃ T : Subgroup Y, T ≠ ⊥ ∧ IsPGroup 2 T) :
    CFSG.Open.pRank r (⊤ : Subgroup X) + twoLocalPrimeRank r Y ≤ twoLocalPrimeRank r (X × Y) := by
  have h := burnsideTA12_twoLocal_add_pRank_le (X := Y) (Y := X) hr hY
  rw [add_comm] at h
  exact h.trans (le_of_eq
    (burnsideTA12_twoLocalPrimeRank_congr hr (MulEquiv.prodComm (M := Y) (N := X))))

private theorem burnsideTA12_twoLocal_transfer {X X' Y : Type} [Group X] [Group X'] [Group Y] [Finite X]
    [Finite X'] [Finite Y] {r : ℕ} (hr : r.Prime) (hX : ∃ T : Subgroup X, T ≠ ⊥ ∧ IsPGroup 2 T)
    (hY : ∃ T : Subgroup Y, T ≠ ⊥ ∧ IsPGroup 2 T)
    (h1 : twoLocalPrimeRank r X' ≤ twoLocalPrimeRank r X)
    (h2 : CFSG.Open.pRank r (⊤ : Subgroup X') ≤ CFSG.Open.pRank r (⊤ : Subgroup X)) :
    twoLocalPrimeRank r (X' × Y) ≤ twoLocalPrimeRank r (X × Y) := by
  refine (burnsideTA12_twoLocalPrimeRank_prod_le hr).trans (max_le ?_ ?_)
  · exact (Nat.add_le_add_right h1 _).trans (burnsideTA12_twoLocal_add_pRank_le hr hX)
  · exact (Nat.add_le_add_right h2 _).trans (burnsideTA12_pRank_add_twoLocal_le hr hY)

private theorem burnsideTA12_pRank_top_prod_le {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p (⊤ : Subgroup (X × Y)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup X) + CFSG.Open.pRank p (⊤ : Subgroup Y) :=
  (burnsideTA12_pRank_le_prod hp ⊤).trans
    (Nat.add_le_add (CFSG.SectionRank.pRank_mono hp.one_lt le_top)
      (CFSG.SectionRank.pRank_mono hp.one_lt le_top))

private theorem burnsideTA12_pRank_top_prod_ge {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p (⊤ : Subgroup X) + CFSG.Open.pRank p (⊤ : Subgroup Y) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (X × Y)) := by
  have h := burnsideTA12_pRank_prod_ge hp (⊤ : Subgroup X) (⊤ : Subgroup Y)
  rwa [Subgroup.top_prod_top] at h


private theorem burnsideTA12_directFactor {G : Type} [Group G] (A : Subgroup G) [A.Normal] (ρ : G →* ↥A)
    (hρ : ∀ a : ↥A, ρ a = a) :
    ∃ Ψ : ↥A × ↥ρ.ker ≃* G, ∀ (a : ↥A) (b : ↥ρ.ker), Ψ (a, b) = (a : G) * (b : G) := by
  haveI : ρ.ker.Normal := MonoidHom.normal_ker ρ
  have hker : ∀ g : G, g ∈ A → g ∈ ρ.ker → g = 1 := by
    intro g hgA hgk
    have h1 : ρ g = 1 := hgk
    have h2 : ρ g = ⟨g, hgA⟩ := hρ ⟨g, hgA⟩
    rw [h1] at h2
    exact (congrArg Subtype.val h2).symm
  have hcomm : ∀ (a : ↥A) (b : ↥ρ.ker), Commute (A.subtype a) (ρ.ker.subtype b) := by
    intro a b
    have h1 : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ A := by
      have := A.mul_mem a.2 (‹A.Normal›.conj_mem ((a : G)⁻¹) (A.inv_mem a.2) (b : G))
      simpa [mul_assoc] using this
    have h2 : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ ρ.ker :=
      ρ.ker.mul_mem (‹ρ.ker.Normal›.conj_mem (b : G) b.2 (a : G)) (ρ.ker.inv_mem b.2)
    have h3 := hker _ h1 h2
    show (a : G) * (b : G) = (b : G) * (a : G)
    calc (a : G) * (b : G) = ((a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹) * ((b : G) * (a : G)) := by
          group
      _ = (b : G) * (a : G) := by rw [h3, one_mul]
  set f : ↥A × ↥ρ.ker →* G := MonoidHom.noncommCoprod A.subtype ρ.ker.subtype hcomm with hf
  have hfapp : ∀ x : ↥A × ↥ρ.ker, f x = (x.1 : G) * (x.2 : G) := fun x => rfl
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    rw [MonoidHom.mem_ker, hfapp] at hab
    have h1 : (a : G) = ((b : G))⁻¹ := eq_inv_of_mul_eq_one_left hab
    have hbA : (b : G) ∈ A := by
      have : ((b : G))⁻¹ ∈ A := h1 ▸ a.2
      simpa using A.inv_mem this
    have hb1 : (b : G) = 1 := hker _ hbA b.2
    have ha1 : (a : G) = 1 := by rw [h1, hb1, inv_one]
    simp only [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext ha1, Subtype.ext hb1⟩
  have hsurj : Function.Surjective f := by
    intro g
    have hmem : ((ρ g : ↥A) : G)⁻¹ * g ∈ ρ.ker := by
      show ρ (((ρ g : ↥A) : G)⁻¹ * g) = 1
      rw [map_mul, map_inv, hρ (ρ g)]
      exact inv_mul_cancel _
    refine ⟨(ρ g, ⟨((ρ g : ↥A) : G)⁻¹ * g, hmem⟩), ?_⟩
    rw [hfapp]
    exact mul_inv_cancel_left _ _
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun a b => rfl⟩


private theorem burnsideTA12_retraction {G : Type} [Group G] [Finite G] (hL : CFSG.layer G = ⊤)
    {A : Subgroup G} (hA : CFSG.IsComponent A)
    (hZ : ∀ K : Subgroup G, CFSG.IsComponent K → K ≠ A → Subgroup.center ↥K = ⊥) :
    ∃ ρ : G →* ↥A, (∀ a : ↥A, ρ a = a) ∧
      ∀ K : Subgroup G, CFSG.IsComponent K → K ≠ A → K ≤ ρ.ker := by
  classical
  set a₀ : CFSG.LocalCores.ComponentIndex G := ⟨A, hA⟩ with ha₀
  have hinj : Function.Injective (CFSG.LocalCores.layerMulOnto G) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hcen, hmul⟩ := (CFSG.LocalCores.layer_multiplication.2.2.2.1 x).1 hx
    have hx1 : ∀ K : CFSG.LocalCores.ComponentIndex G, K ≠ a₀ → x K = 1 := by
      intro K hK
      have hKA : K.1 ≠ A := fun h => hK (Subtype.ext h)
      have := hcen K
      rw [hZ K.1 K.2 hKA, Subgroup.mem_bot] at this
      exact this
    have hup : Function.update x a₀ 1 = 1 := by
      funext K
      by_cases hK : K = a₀
      · subst hK
        simp
      · rw [Function.update_of_ne hK]
        exact hx1 K hK
    have h1 : (x a₀ : G) = 1 := by
      have := CFSG.LocalCores.layerMul_eq_mul_update x a₀
      rw [hup, map_one, mul_one, hmul] at this
      exact this.symm
    rw [Subgroup.mem_bot]
    funext K
    by_cases hK : K = a₀
    · subst hK
      exact Subtype.ext h1
    · exact hx1 K hK
  set e₁ := MulEquiv.ofBijective (CFSG.LocalCores.layerMulOnto G)
    ⟨hinj, CFSG.LocalCores.layerMulOnto_surjective⟩ with he₁
  set e₂ : ↥(CFSG.layer G) ≃* G := (MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv with he₂
  set Φ := e₁.trans e₂ with hΦ
  have hΦapp : ∀ x, (Φ x : G) = CFSG.LocalCores.layerMul G x := fun x => rfl
  refine ⟨(Pi.evalMonoidHom (fun K : CFSG.LocalCores.ComponentIndex G => ↥K.1) a₀).comp
    Φ.symm.toMonoidHom, fun a => ?_, fun K hK hKA k hk => ?_⟩
  · have h1 : Φ.symm (a : G) = Pi.mulSingle a₀ a := by
      apply Φ.injective
      rw [MulEquiv.apply_symm_apply]
      have := hΦapp (Pi.mulSingle a₀ a)
      rw [CFSG.LocalCores.layerMul_mulSingle] at this
      exact this.symm
    show (Φ.symm (a : G)) a₀ = a
    rw [h1]
    exact Pi.mulSingle_eq_same (M := fun K : CFSG.LocalCores.ComponentIndex G => ↥K.1) a₀ a
  · set K₀ : CFSG.LocalCores.ComponentIndex G := ⟨K, hK⟩ with hK₀
    have hne : K₀ ≠ a₀ := fun h => hKA (congrArg Subtype.val h)
    have h1 : Φ.symm k = Pi.mulSingle K₀ (⟨k, hk⟩ : ↥K₀.1) := by
      apply Φ.injective
      rw [MulEquiv.apply_symm_apply]
      have := hΦapp (Pi.mulSingle K₀ (⟨k, hk⟩ : ↥K₀.1))
      rw [CFSG.LocalCores.layerMul_mulSingle] at this
      exact this.symm
    show (Φ.symm k) a₀ = 1
    rw [h1]
    exact Pi.mulSingle_eq_of_ne hne.symm _


private theorem burnsideTA12_center_le_component {G : Type} [Group G] [Finite G] (hL : CFSG.layer G = ⊤)
    {A : Subgroup G} (hA : CFSG.IsComponent A)
    (hZ : ∀ K : Subgroup G, CFSG.IsComponent K → K ≠ A → Subgroup.center ↥K = ⊥) :
    Subgroup.center G ≤ A := by
  classical
  intro z hz
  set a₀ : CFSG.LocalCores.ComponentIndex G := ⟨A, hA⟩ with ha₀
  obtain ⟨x, hx⟩ := CFSG.LocalCores.exists_layerMul_eq (hL ▸ Subgroup.mem_top z : z ∈ CFSG.layer G)
  have hzc : z ∈ Subgroup.centralizer (CFSG.layer G : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g _
    exact Subgroup.mem_center_iff.1 hz g
  have hcen := (CFSG.LocalCores.layerMul_mem_centralizer_iff x).1 (hx ▸ hzc)
  have hx1 : ∀ K : CFSG.LocalCores.ComponentIndex G, K ≠ a₀ → x K = 1 := by
    intro K hK
    have hKA : K.1 ≠ A := fun h => hK (Subtype.ext h)
    have := hcen K
    rw [hZ K.1 K.2 hKA, Subgroup.mem_bot] at this
    exact this
  have hup : Function.update x a₀ 1 = 1 := by
    funext K
    by_cases hK : K = a₀
    · subst hK
      simp
    · rw [Function.update_of_ne hK]
      exact hx1 K hK
  have := CFSG.LocalCores.layerMul_eq_mul_update x a₀
  rw [hup, map_one, mul_one, hx] at this
  rw [this]
  exact (x a₀).2

private theorem burnsideTA12_exists_two_subgroup {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : CFSG.IsComponent K) : ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hev : Even (Nat.card ↥K) := CFSG.RankThree.OddKernel.even_card_of_isQuasisimple hK.1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 (even_iff_two_dvd.1 hev)
  have hx2 : ((x : G)) ^ 2 = 1 := by
    have : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    exact congrArg Subtype.val this
  have hx1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    omega
  refine ⟨Subgroup.zpowers (x : G), ?_, ?_, ?_⟩
  · intro h
    exact hx1 (by simpa using Subgroup.zpowers_eq_bot.1 h)
  · have hord : orderOf (x : G) = 2 := orderOf_eq_prime hx2 hx1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  · rw [Subgroup.zpowers_le]
    exact x.2

private theorem burnsideTA12_exists_two_subgroup_of_le {G : Type} [Group G] {L T : Subgroup G}
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hTL : T ≤ L) :
    ∃ T' : Subgroup ↥L, T' ≠ ⊥ ∧ IsPGroup 2 T' := by
  refine ⟨T.subgroupOf L, ?_, ?_⟩
  · intro h
    apply hT
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact disjoint_self.1 (h.mono_right hTL)
  · exact hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm

private theorem burnsideTA12_pRank_component_le {G : Type} [Group G] [Finite G] (hev : evenRank G ≤ 2)
    {A A' : Subgroup G} (hA : CFSG.IsComponent A) (hA' : CFSG.IsComponent A') (hne : A ≠ A')
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : CFSG.Open.pRank r A ≤ 2 := by
  obtain ⟨T, hT, hT2, hTA'⟩ := burnsideTA12_exists_two_subgroup hA'
  have hcomm : ⁅A, A'⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hA hA').resolve_left hne
  have hc : ∀ x ∈ A, ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    have : ⁅x, y⁆ ∈ ⁅A, A'⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hAN : A ≤ Subgroup.normalizer (T : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hh : ∀ h' ∈ T, a * h' * a⁻¹ = h' := fun h' hh' => by
      rw [hc a ha h' (hTA' hh')]
      group
    constructor
    · intro hmem
      rw [hh h hmem]
      exact hmem
    · intro hmem
      have hmem2 : a * h * a⁻¹ ∈ T := hmem
      have h1 := hc a ha _ (hTA' hmem2)
      have h2 : a⁻¹ * (a * h * a⁻¹) * a = a * h * a⁻¹ := by
        rw [mul_assoc, ← h1, inv_mul_cancel_left]
      have h3 : h = a * h * a⁻¹ := by
        calc h = a⁻¹ * (a * h * a⁻¹) * a := by group
          _ = a * h * a⁻¹ := h2
      rw [h3]
      exact hmem2
  exact (CFSG.SectionRank.pRank_mono hr.one_lt hAN).trans
    ((burnsideTA12_pRank_normalizer_le hr hT hT2).trans
      ((burnsideTA12_twoLocalPrimeRank_le_evenRank hr hr2).trans hev))


private theorem burnsideTA12_layer_map_le {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) : (genFittingLayer G).map f ≤ genFittingLayer H := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro component hcomponent
  apply Subgroup.map_le_iff_le_comap.mp
  by_cases hkilled : component ≤ f.ker
  · rw [component.map_eq_bot_iff.mpr hkilled]
    exact bot_le
  · exact CFSG.ComponentClassification.Layer.component_le
      (CFSG.ComponentClassification.LocalComponents.image hcomponent f hf hkilled)

private theorem burnsideTA12_genFittingLayer_top_of_surjective {G H : Type*} [Group G] [Group H]
    (hG : genFittingLayer G = ⊤) (f : G →* H) (hf : Function.Surjective f) :
    genFittingLayer H = ⊤ := by
  have h := burnsideTA12_layer_map_le f hf
  rw [hG, Subgroup.map_top_of_surjective f hf] at h
  exact top_le_iff.mp h

private theorem burnsideTA12_alpha {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hev : evenRank G ≤ 2) (hKG : CFSG.SectionRank.IsKGroupCat G)
    (hprop : ∀ (X : Type) [Group X] [Finite X], IsProperSectionOf X G → TheoremAHolds X)
    (π : G →* S) (hπ : Function.Surjective π) (hL : CFSG.layer G = ⊤)
    {A A' : Subgroup G} (hA : CFSG.IsComponent A) (hA' : CFSG.IsComponent A') (hne : A ≠ A')
    (hZ : ∀ K : Subgroup G, CFSG.IsComponent K → K ≠ A → Subgroup.center ↥K = ⊥)
    (hker : π.ker ≤ Subgroup.center G) : TheoremAConclusion G S p := by
  have hAn : A.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hL hA
  have hcomm : ⁅A, A'⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hA hA').resolve_left hne
  have hAne : A ≠ ⊤ := by
    intro hAtop
    obtain ⟨-, -, a, b, hab⟩ := hA'.1
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hmem : ⁅(b : G), (a : G)⁆ ∈ ⁅A, A'⁆ :=
      Subgroup.commutator_mem_commutator (hAtop ▸ Subgroup.mem_top _) a.2
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hmem.symm
  have hsqt : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r ↥A ≤ 2 := fun r hr hr2 => by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact burnsideTA12_pRank_component_le hev hA hA' hne hr hr2
  have hAprop : IsProperSectionOf ↥A G := burnsideTA12_isProperSectionOf_subgroup A hAne
  have hTA : TheoremAHolds ↥A := hprop ↥A hAprop
  have hevA : evenRank ↥A ≤ 2 :=
    (burnsideTA12_evenRank_le_of_injective A.subtype A.subtype_injective).trans hev
  have hKA : CFSG.SectionRank.IsKGroupCat ↥A := hKG.subgroup A
  have hKle : π.ker ≤ A := hker.trans (burnsideTA12_center_le_component hL hA hZ)
  haveI : π.ker.Normal := MonoidHom.normal_ker π
  set KA : Subgroup ↥A := π.ker.subgroupOf A with hKAdef
  have hsecA : IsSectionOf (↥A ⧸ KA) ↥A := burnsideTA12_isSectionOf_quotient KA
  have hssA : genFittingLayer (↥A ⧸ KA) = ⊤ :=
    burnsideTA12_genFittingLayer_top_of_surjective
      (burnsideTA12_genFittingLayer_top_of_quasisimple hA.1) (QuotientGroup.mk' KA)
      (QuotientGroup.mk'_surjective KA)
  have hconcA := (hTA hevA hKA (↥A ⧸ KA) hsecA hssA).1 p hp hp2
  unfold TheoremAConclusion at hconcA
  obtain ⟨hc1, hc2⟩ := hconcA
  have hl : twoLocalPrimeRank p (↥A ⧸ KA) ≤ twoLocalPrimeRank p ↥A := by
    rcases hc1 with ⟨ha, -⟩ | ⟨-, H', H₁, H₂, n₁, n₂, -, hr3, -⟩
    · exact ha
    · exfalso
      have h1 : CFSG.pRank 3 ↥H' ≤ CFSG.pRank 3 ↥A :=
        burnsideTA12_pRank_le_of_injective (by norm_num) H'.subtype H'.subtype_injective
      have h2 := hsqt 3 Nat.prime_three (by norm_num)
      omega
  have hr : CFSG.pRank p (↥A ⧸ KA) ≤ CFSG.pRank p ↥A := by
    have := hc2 (by rw [burnsideTA12_pRank_top_eq]; exact hsqt p hp hp2)
    simpa only [burnsideTA12_pRank_top_eq] using this
  have hr' : CFSG.Open.pRank p (⊤ : Subgroup (↥A ⧸ KA)) ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥A) := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hr
  obtain ⟨ρ, hρ, hρK⟩ := burnsideTA12_retraction hL hA hZ
  obtain ⟨Ψ, hΨ⟩ := burnsideTA12_directFactor A ρ hρ
  obtain ⟨T₁, hT₁, hT₁2, hT₁A⟩ := burnsideTA12_exists_two_subgroup hA
  obtain ⟨T₂, hT₂, hT₂2, hT₂A'⟩ := burnsideTA12_exists_two_subgroup hA'
  have hX : ∃ T : Subgroup ↥A, T ≠ ⊥ ∧ IsPGroup 2 T :=
    burnsideTA12_exists_two_subgroup_of_le hT₁ hT₁2 hT₁A
  have hY : ∃ T : Subgroup ↥ρ.ker, T ≠ ⊥ ∧ IsPGroup 2 T :=
    burnsideTA12_exists_two_subgroup_of_le hT₂ hT₂2 (hT₂A'.trans (hρK A' hA' hne.symm))
  set θ : G →* (↥A ⧸ KA) × ↥ρ.ker :=
    (MonoidHom.prodMap (QuotientGroup.mk' KA) (MonoidHom.id ↥ρ.ker)).comp Ψ.symm.toMonoidHom
    with hθ
  have hθker : θ.ker = π.ker := by
    ext g
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      obtain ⟨⟨a, b⟩, hab⟩ : ∃ x, Ψ x = g := ⟨Ψ.symm g, Ψ.apply_symm_apply g⟩
      rw [← hab] at h ⊢
      have h' : ((QuotientGroup.mk' KA a), b) = 1 := by
        simpa [hθ] using h
      rw [Prod.mk_eq_one] at h'
      have h1 : a ∈ KA := (QuotientGroup.eq_one_iff a).1 h'.1
      have h2 : b = 1 := h'.2
      rw [hΨ, h2]
      simp only [OneMemClass.coe_one, mul_one]
      exact MonoidHom.mem_ker.1 (Subgroup.mem_subgroupOf.1 h1)
    · intro hg
      have hgA : g ∈ A := hKle hg
      have hΨg : Ψ ((⟨g, hgA⟩ : ↥A), (1 : ↥ρ.ker)) = g := by
        rw [hΨ]
        simp
      have : Ψ.symm g = (⟨g, hgA⟩, 1) := by
        rw [MulEquiv.symm_apply_eq]
        exact hΨg.symm
      have hmemKA : (⟨g, hgA⟩ : ↥A) ∈ KA := hg
      show (MonoidHom.prodMap (QuotientGroup.mk' KA) (MonoidHom.id ↥ρ.ker)) (Ψ.symm g) = 1
      rw [this]
      simp [(QuotientGroup.eq_one_iff _).2 hmemKA]
  have eS : G ⧸ π.ker ≃* S := QuotientGroup.quotientKerEquivOfSurjective π hπ
  have eθ : G ⧸ π.ker ≃* G ⧸ θ.ker := QuotientGroup.quotientMulEquivOfEq hθker.symm
  let ι : G ⧸ π.ker →* (↥A ⧸ KA) × ↥ρ.ker := (QuotientGroup.kerLift θ).comp eθ.toMonoidHom
  have hιinj : Function.Injective ι := (QuotientGroup.kerLift_injective θ).comp eθ.injective
  have hloc : twoLocalPrimeRank p G ≤ 2 :=
    (burnsideTA12_twoLocalPrimeRank_le_evenRank hp hp2).trans hev
  have hS2 : twoLocalPrimeRank p S ≤ twoLocalPrimeRank p G := by
    calc twoLocalPrimeRank p S = twoLocalPrimeRank p (G ⧸ π.ker) :=
          (burnsideTA12_twoLocalPrimeRank_congr hp eS).symm
      _ ≤ twoLocalPrimeRank p ((↥A ⧸ KA) × ↥ρ.ker) :=
          burnsideTA12_twoLocalPrimeRank_le_of_injective hp ι hιinj
      _ ≤ twoLocalPrimeRank p (↥A × ↥ρ.ker) :=
          burnsideTA12_twoLocal_transfer hp hX hY hl hr'
      _ = twoLocalPrimeRank p G := burnsideTA12_twoLocalPrimeRank_congr hp Ψ
  have hpS : CFSG.pRank p S ≤ CFSG.pRank p G := by
    have h1 : CFSG.pRank p S = CFSG.pRank p (G ⧸ π.ker) := (CFSG.pRank_congr_of_mulEquiv eS p).symm
    have h2 : CFSG.pRank p (G ⧸ π.ker) ≤ CFSG.pRank p ((↥A ⧸ KA) × ↥ρ.ker) :=
      burnsideTA12_pRank_le_of_injective hp.one_lt ι hιinj
    have h3 : CFSG.pRank p ((↥A ⧸ KA) × ↥ρ.ker) ≤ CFSG.pRank p (↥A × ↥ρ.ker) := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact (burnsideTA12_pRank_top_prod_le hp).trans
        ((Nat.add_le_add_right hr' _).trans (burnsideTA12_pRank_top_prod_ge hp))
    have h4 : CFSG.pRank p (↥A × ↥ρ.ker) = CFSG.pRank p G := CFSG.pRank_congr_of_mulEquiv Ψ p
    omega
  unfold TheoremAConclusion
  refine ⟨Or.inl ⟨hS2, hloc⟩, fun _ => ?_⟩
  simp only [burnsideTA12_pRank_top_eq]
  exact hpS


private theorem burnsideTA12_isComponentOf_top {G : Type} [Group G] {K : Subgroup G}
    (h : CFSG.IsComponent K) : IsComponentOf K ⊤ :=
  ⟨le_top, (CFSG.Adapters.isSubnormal_top_iff K).2 h.2,
    ⟨Group.isPerfect_def.1 h.1.1, h.1.2.1⟩⟩

private theorem burnsideTA12_centerOf_eq {G : Type} [Group G] (K : Subgroup G) :
    centerOf K = (Subgroup.center ↥K).map K.subtype := by
  ext g
  rw [CFSG.LocalCores.mem_map_center_iff]
  rfl

private theorem burnsideTA12_center_component_le {G : Type} [Group G] [Finite G] (hL : CFSG.layer G = ⊤)
    {K : Subgroup G} (hK : CFSG.IsComponent K) :
    (Subgroup.center ↥K).map K.subtype ≤ Subgroup.center G := by
  intro z hz
  have h := CFSG.LocalCores.center_component_le_centralizer_layer hK hz
  rw [hL, Subgroup.coe_top, Subgroup.centralizer_univ] at h
  exact h

private theorem burnsideTA12_beta (hPair : burnsideTA12_PairFact) {G : Type} [Group G] [Finite G]
    {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hev : evenRank G ≤ 2)
    (hKG : CFSG.SectionRank.IsKGroupCat G) (hC : burnsideTA12_CForSections G)
    (π : G →* S) (hπ : Function.Surjective π)
    (hL : CFSG.layer G = ⊤) (hcenG : IsPGroup p ↥(Subgroup.center G))
    {K₁ K₂ : Subgroup G} (h₁ : CFSG.IsComponent K₁) (h₂ : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂)
    (hZ1 : Subgroup.center ↥K₁ ≠ ⊥) (hZ2 : Subgroup.center ↥K₂ ≠ ⊥)
    (hker : π.ker ≤ Subgroup.center G) (hnoinj : ∀ f : S →* G, ¬ Function.Injective f) :
    TheoremAConclusion G S p := by
  have hPG : ∀ {K : Subgroup G}, CFSG.IsComponent K → IsPGroup p ↥(Subgroup.center ↥K) := by
    intro K hK
    let f : ↥(Subgroup.center ↥K) →* ↥(Subgroup.center G) :=
      ⟨⟨fun z => ⟨(z : K), burnsideTA12_center_component_le hL hK ⟨z, z.2, rfl⟩⟩, rfl⟩,
        fun x y => rfl⟩
    have hf : Function.Injective f := by
      intro x y h
      have h1 : ((x : ↥K) : G) = ((y : ↥K) : G) :=
        congrArg (fun z : ↥(Subgroup.center G) => (z : G)) h
      exact Subtype.ext (Subtype.ext h1)
    exact hcenG.of_injective f hf
  obtain ⟨hp3, hcard, hlay, hrank, hcen, n₁, n₂, hs1, hs2, h31, ho1, h32, ho2, hgcd⟩ :=
    hPair G hev hKG hC K₁ K₂ h₁ h₂ hne p hp hp2 (hPG h₁) (hPG h₂) hZ1 hZ2
  have hsup : K₁ ⊔ K₂ = ⊤ := hlay.symm.trans hL
  haveI hn₁ : K₁.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hL h₁
  haveI hn₂ : K₂.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hL h₂
  have hcomm : ⁅K₁, K₂⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute h₁ h₂).resolve_left hne
  have hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x := by
    intro x hx y hy
    have : ⁅x, y⁆ ∈ ⁅K₁, K₂⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hZG : Subgroup.center G = (Subgroup.center ↥K₁).map K₁.subtype := by
    refine le_antisymm ?_ (burnsideTA12_center_component_le hL h₁)
    intro z hz
    have hz' : z ∈ K₁ ⊔ K₂ := by rw [hsup]; exact Subgroup.mem_top z
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hz'
    have hacen : a ∈ centerOf K₁ := by
      refine ⟨ha, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro x hx
      have h1 := Subgroup.mem_center_iff.1 hz x
      have h2 : x * b = b * x := hc x hx b hb
      calc x * a = x * a * b * b⁻¹ := by group
        _ = x * (a * b) * b⁻¹ := by rw [mul_assoc x a b]
        _ = (a * b) * x * b⁻¹ := by rw [h1]
        _ = a * (b * x) * b⁻¹ := by rw [mul_assoc a b x]
        _ = a * (x * b) * b⁻¹ := by rw [h2]
        _ = a * x := by group
    have hbcen : b ∈ centerOf K₂ := by
      refine ⟨hb, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro y hy
      have h1 := Subgroup.mem_center_iff.1 hz y
      have h2 : a * y = y * a := hc a ha y hy
      calc y * b = a⁻¹ * (a * y) * b := by group
        _ = a⁻¹ * (y * a) * b := by rw [h2]
        _ = a⁻¹ * (y * (a * b)) := by group
        _ = a⁻¹ * ((a * b) * y) := by rw [← h1]
        _ = b * y := by group
    rw [← burnsideTA12_centerOf_eq]
    refine (centerOf K₁).mul_mem hacen ?_
    rw [hcen]
    exact hbcen
  have hcardG : Nat.card (Subgroup.center G) = 3 := by
    rw [hZG, Subgroup.card_map_of_injective K₁.subtype_injective]
    exact hcard
  have hKcases : π.ker = ⊥ ∨ π.ker = Subgroup.center G := by
    have hdvd : Nat.card π.ker ∣ 3 := hcardG ▸ Subgroup.card_dvd_of_le hker
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h)
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hker (by rw [h, hcardG]))
  rcases hKcases with hK | hK
  · exfalso
    have hbij : Function.Bijective π := ⟨(MonoidHom.ker_eq_bot_iff π).1 hK, hπ⟩
    let e : G ≃* S := MulEquiv.ofBijective π hbij
    exact hnoinj e.symm.toMonoidHom e.symm.injective
  · subst hp3
    have eS : G ⧸ π.ker ≃* S := QuotientGroup.quotientKerEquivOfSurjective π hπ
    have eC : G ⧸ Subgroup.center G ≃* ↥(⊤ : Subgroup G) ⧸ Subgroup.center ↥(⊤ : Subgroup G) :=
      (QuotientGroup.congr (Subgroup.center ↥(⊤ : Subgroup G)) (Subgroup.center G)
        Subgroup.topEquiv (Subgroup.map_center_eq Subgroup.topEquiv)).symm
    have eS' : S ≃* ↥(⊤ : Subgroup G) ⧸ Subgroup.center ↥(⊤ : Subgroup G) :=
      eS.symm.trans ((QuotientGroup.quotientMulEquivOfEq hK).trans eC)
    have hrank' : CFSG.pRank 3 ↥(⊤ : Subgroup G) = 3 := by
      rw [← hsup]
      exact hrank
    unfold TheoremAConclusion
    refine ⟨Or.inr ⟨rfl, ⊤, K₁, K₂, n₁, n₂, ⟨eS'⟩, hrank', hsup.symm,
      burnsideTA12_isComponentOf_top h₁, burnsideTA12_isComponentOf_top h₂, hs1, hs2, h31, ho1,
      h32, ho2, hcen, hgcd⟩, fun h => ?_⟩
    omega


private theorem burnsideTA12_quasisimple_of_central (hPair : burnsideTA12_PairFact)
    {G : Type} [Group G] [Finite G] {S : Type} [Group S] [Finite S] {p : ℕ}
    (hmin : IsMinimalCounterexampleToA G S p) (hC : burnsideTA12_CForSections G)
    (π : G →* S) (hπ : Function.Surjective π)
    (hcov : ∀ Y : Subgroup G, Y ≠ ⊤ → Y.map π ≠ ⊤)
    (hH : (Subgroup.center S).comap π = pCore p G)
    (hcen : (Subgroup.center S).comap π ≤ Subgroup.center G) : CFSG.IsQuasisimple G := by
  have hev : evenRank G ≤ 2 := hmin.1
  have hKG : CFSG.SectionRank.IsKGroupCat G := hmin.2.1
  have hp : p.Prime := hmin.2.2.2.2.1
  have hp2 : p ≠ 2 := hmin.2.2.2.2.2.1
  have hnp : ¬ TheoremAConclusion G S p := hmin.2.2.2.2.2.2.1
  have hprop := hmin.2.2.2.2.2.2.2
  have hss : CFSG.layer S = ⊤ := burnsideTA12_layer_eq_top hmin.2.2.2.1
  set H : Subgroup G := (Subgroup.center S).comap π with hHdef
  have hD : burnsideTA12_Data G H := burnsideTA12_data hss π hπ hcov
  haveI := hD.normal
  haveI := hD.perfect
  have hHp : IsPGroup p H := hH ▸ CFSG.pCore_isPGroup
  have hL : CFSG.layer G = ⊤ :=
    CFSG.SectionRank.perfect_central_semisimple_extension hD.perfect H hcen hD.layer_top
  have hcenGH : Subgroup.center G ≤ H := by
    intro z hz
    have hmem : QuotientGroup.mk' H z ∈ Subgroup.center (G ⧸ H) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]
    rw [hD.center_bot, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff z).1 hmem
  have hcenGp : IsPGroup p ↥(Subgroup.center G) := hHp.to_le hcenGH
  have hker : π.ker ≤ Subgroup.center G := by
    intro k hk
    apply hcen
    show π k ∈ Subgroup.center S
    rw [MonoidHom.mem_ker.1 hk]
    exact Subgroup.one_mem _
  have hnoinj := burnsideTA12_no_injective hmin
  by_cases hex : ∃ K₁ K₂ : Subgroup G, CFSG.IsComponent K₁ ∧ CFSG.IsComponent K₂ ∧ K₁ ≠ K₂
  · exfalso
    obtain ⟨K₁, K₂, h₁, h₂, hne⟩ := hex
    by_cases hβ : ∃ A₁ A₂ : Subgroup G, CFSG.IsComponent A₁ ∧ CFSG.IsComponent A₂ ∧ A₁ ≠ A₂ ∧
        Subgroup.center ↥A₁ ≠ ⊥ ∧ Subgroup.center ↥A₂ ≠ ⊥
    · obtain ⟨A₁, A₂, hA₁, hA₂, hA12, hZ1, hZ2⟩ := hβ
      exact hnp (burnsideTA12_beta hPair hp hp2 hev hKG hC π hπ hL hcenGp hA₁ hA₂ hA12 hZ1 hZ2
        hker hnoinj)
    · push Not at hβ
      obtain ⟨A, hA, hZA⟩ : ∃ A : Subgroup G, CFSG.IsComponent A ∧
          ∀ K : Subgroup G, CFSG.IsComponent K → K ≠ A → Subgroup.center ↥K = ⊥ := by
        by_cases hc : ∃ A₀ : Subgroup G, CFSG.IsComponent A₀ ∧ Subgroup.center ↥A₀ ≠ ⊥
        · obtain ⟨A₀, hA₀, hZ₀⟩ := hc
          exact ⟨A₀, hA₀, fun K hK hKA => hβ A₀ K hA₀ hK (Ne.symm hKA) hZ₀⟩
        · push Not at hc
          exact ⟨K₁, h₁, fun K hK _ => hc K hK⟩
      obtain ⟨A', hA', hAA'⟩ : ∃ A' : Subgroup G, CFSG.IsComponent A' ∧ A ≠ A' := by
        by_cases h : K₁ = A
        · exact ⟨K₂, h₂, fun h' => hne (h.trans h')⟩
        · exact ⟨K₁, h₁, fun h' => h h'.symm⟩
      exact hnp (burnsideTA12_alpha hp hp2 hev hKG hprop π hπ hL hA hA' hAA' hZA hker)
  · push Not at hex
    by_cases hc : ∃ K : Subgroup G, CFSG.IsComponent K
    · obtain ⟨K₀, hK₀⟩ := hc
      have hall : ∀ K : Subgroup G, CFSG.IsComponent K → K = K₀ := fun K hK =>
        hex K K₀ hK hK₀
      have hle : CFSG.layer G ≤ K₀ := by
        rw [CFSG.layer.eq_sSup]
        exact sSup_le fun K hK => (hall K hK).le
      rw [hL] at hle
      have hK₀top : K₀ = ⊤ := top_le_iff.1 hle
      subst hK₀top
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv hK₀.1
    · exfalso
      push Not at hc
      have h1 : CFSG.layer G = ⊥ := CFSG.LocalCores.layer_eq_bot_of_forall hc
      rw [hL] at h1
      haveI : Subsingleton G := ⟨fun a b => by
        have ha : a ∈ (⊤ : Subgroup G) := Subgroup.mem_top a
        have hb : b ∈ (⊤ : Subgroup G) := Subgroup.mem_top b
        rw [h1, Subgroup.mem_bot] at ha hb
        rw [ha, hb]⟩
      haveI : Subsingleton S := hπ.subsingleton
      exact hnoinj 1 (fun a b _ => Subsingleton.elim a b)


private theorem burnsideTA12_exists_counterexample {G : Type} [Group G] [Finite G]
    (hmin : IsMinimalCounterexampleABC G) (hnA : ¬ TheoremAHolds G) :
    ∃ (S : Type) (_ : Group S) (_ : Finite S) (p : ℕ), IsMinimalCounterexampleToA G S p := by
  have hev : evenRank G ≤ 2 := by
    by_contra h
    exact hnA fun h' => absurd h' h
  have hKG : CFSG.SectionRank.IsKGroupCat G := by
    by_contra h
    exact hnA fun _ h' => absurd h' h
  obtain ⟨S, _, _, hSsec, hSss, hnot⟩ : ∃ (S : Type) (_ : Group S) (_ : Finite S),
      IsSectionOf S G ∧ genFittingLayer S = ⊤ ∧
      ¬ ((∀ p : ℕ, p.Prime → p ≠ 2 → TheoremAConclusion G S p) ∧
        (CFSG.IsStronglyQuasithin G → CFSG.IsStronglyQuasithin S)) := by
    by_contra hcon
    push Not at hcon
    refine hnA ?_
    intro _ _ S _ _ hs hss
    exact hcon S _ _ hs hss
  obtain ⟨p, hp, hp2, hnp⟩ : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ TheoremAConclusion G S p := by
    by_contra hcon
    push Not at hcon
    refine hnot ⟨fun p hp hp2 => hcon p hp hp2, fun hsqt q hq hq2 => ?_⟩
    have hc := hcon q hq hq2
    unfold TheoremAConclusion at hc
    have h2 := hc.2
    simp only [burnsideTA12_pRank_top_eq] at h2
    have h3 := hsqt q hq hq2
    exact (h2 h3).trans h3
  exact ⟨S, ‹_›, ‹_›, p, hev, hKG, hSsec, hSss, hp, hp2, hnp, fun X _ _ hX => (hmin.2 X hX).1⟩

private theorem burnsideTA12_a_2_12_of_facts
    (hR2F : burnsideTA12_Rank2Fact) (hCover : burnsideTA12_CoverFact)
    (hPair : burnsideTA12_PairFact) (h11 : A_2_11) : A_2_12 := by
  intro G _ _ hmin hnA
  obtain ⟨S, _, _, p, hmin'⟩ := burnsideTA12_exists_counterexample hmin hnA
  obtain ⟨π, hπ, hcov, hH⟩ := burnsideTA12_cover h11 hmin'
  by_cases hcen : (Subgroup.center S).comap π ≤ Subgroup.center G
  · exact burnsideTA12_quasisimple_of_central hPair hmin' (fun X _ _ hX => (hmin.2 X hX).2.2) π hπ
      hcov hH hcen
  · exact (burnsideTA12_noncentral_false hR2F hCover hmin' π hπ hcov hH hcen).elim

end BurnsideTA12

section BurnsideTA12cov

open CFSG.ASVolI.ChA
open CFSG.Blueprint
open scoped commutatorElement MatrixGroups

private theorem burnsideTA12_card_le_three_pow_of_injective {G α K : Type*} [Finite G] [Fintype α]
    [Field K]
    (φ : G → α → K) (hφ : Function.Injective φ) (h3 : ∀ g a, φ g a ^ 3 = 1) :
    Nat.card G ≤ 3 ^ Fintype.card α := by
  classical
  set S : Finset K := (Polynomial.nthRoots 3 (1 : K)).toFinset
  have hS : S.card ≤ 3 := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)
  let ψ : G → (α → S) := fun g a =>
    ⟨φ g a, by rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]; exact h3 g a⟩
  have hψ : Function.Injective ψ := fun g g' h =>
    hφ (funext fun a => congrArg Subtype.val (congrFun h a))
  calc Nat.card G ≤ Nat.card (α → S) := Nat.card_le_card_of_injective ψ hψ
    _ = S.card ^ Fintype.card α := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe]
    _ ≤ 3 ^ Fintype.card α := Nat.pow_le_pow_left hS _

open Polynomial Module Matrix in
private theorem burnsideTA12_exists_common_eigenbasis_pow_three {K : Type*} [Field K] [IsAlgClosed K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (h3 : (3 : K) ≠ 0) (E : Subgroup (GL ι K))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1) :
    ∃ (b : Module.Basis ι K (ι → K)) (d : GL ι K → ι → K),
      ∀ x ∈ E, ∀ a, (x : Matrix ι ι K) *ᵥ b a = d x a • b a := by
  classical
  set f : E → Module.End K (ι → K) :=
    fun x => Matrix.toLinAlgEquiv' ((x : GL ι K) : Matrix ι ι K) with hfdef
  have hfcomm : ∀ i j, Commute (f i) (f j) := fun i j => by
    change Matrix.toLinAlgEquiv' _ * Matrix.toLinAlgEquiv' _ =
      Matrix.toLinAlgEquiv' _ * Matrix.toLinAlgEquiv' _
    rw [← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, hcomm _ i.2 _ j.2]
  have hf3 : ∀ i, f i ^ 3 = 1 := fun i => by
    change (Matrix.toLinAlgEquiv' _) ^ 3 = 1
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hexp _ i.2, Units.val_one, map_one]
  have hsep : (X ^ 3 - C (1 : K)).Separable :=
    separable_X_pow_sub_C 1 (by exact_mod_cast h3) one_ne_zero
  have hss : ∀ i, (f i).IsSemisimple := fun i =>
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hf3 i])
  set W : (E → K) → Submodule K (ι → K) := fun χ => ⨅ i, (f i).maxGenEigenspace (χ i) with hW
  have hind : iSupIndep W :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hfcomm j i) φ)
  have htop : ⨆ χ, W χ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      (fun i j _ => hfcomm i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  set b₀ := hint.collectedBasis (fun χ => Module.finBasis K (W χ))
  let e := b₀.indexEquiv (Pi.basisFun K ι)
  refine ⟨b₀.reindex e, fun x a => if hx : x ∈ E then (e.symm a).1 ⟨x, hx⟩ else 0, ?_⟩
  intro x hx a
  have hmem : b₀.reindex e a ∈ W (e.symm a).1 := by
    rw [Module.Basis.reindex_apply]
    exact hint.collectedBasis_mem _ _
  have h1 : b₀.reindex e a ∈ (f ⟨x, hx⟩).maxGenEigenspace ((e.symm a).1 ⟨x, hx⟩) :=
    (Submodule.mem_iInf _).mp hmem ⟨x, hx⟩
  rw [(hss ⟨x, hx⟩).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
    Module.End.mem_eigenspace_iff] at h1
  simp only [hx, ↓reduceDIte]
  rw [← h1]
  rfl

open Module Matrix in
private theorem burnsideTA12_card_le_of_det_eq_one_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (h3 : (3 : K) ≠ 0) (a₀ : ι)
    (E : Subgroup (GL ι K)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hdet : ∀ x ∈ E, (x : Matrix ι ι K).det = 1) [Finite E] :
    Nat.card E ≤ 3 ^ (Fintype.card ι - 1) := by
  classical
  obtain ⟨b, d, hb⟩ := burnsideTA12_exists_common_eigenbasis_pow_three h3 E hcomm hexp
  have eigen_mul : ∀ {x y : GL ι K}, x ∈ E → y ∈ E → ∀ a, d (x * y) a = d x a * d y a := by
    intro x y hx hy a
    have h1 := hb (x * y) (E.mul_mem hx hy) a
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb y hy a, Matrix.mulVec_smul, hb x hx a,
      smul_smul] at h1
    rw [mul_comm]
    exact (smul_left_injective K (b.ne_zero a) h1).symm
  have eigen_one : ∀ a, d 1 a = 1 := by
    intro a
    have h0 := hb 1 E.one_mem a
    rw [Units.val_one, Matrix.one_mulVec] at h0
    exact smul_left_injective K (b.ne_zero a) (show d 1 a • b a = (1 : K) • b a by
      rw [← h0, one_smul])
  have eigen_pow_three : ∀ {x : GL ι K}, x ∈ E → x ^ 3 = 1 → ∀ a, d x a ^ 3 = 1 := by
    intro x hx hx3 a
    have h := eigen_mul (E.mul_mem hx hx) hx a
    have h1 := eigen_mul hx hx a
    have hx3' : x * x * x = 1 := by rw [mul_assoc, ← pow_three, hx3]
    rw [hx3', eigen_one a, h1] at h
    rw [h]
    ring
  have eigen_ext : ∀ {x y : GL ι K}, x ∈ E → y ∈ E → (∀ a, d x a = d y a) → x = y := by
    intro x y hx hy h
    apply Units.ext
    apply Matrix.toLin'.injective
    apply b.ext
    intro a
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hb x hx a, hb y hy a, h a]
  have eigen_det : ∀ {x : GL ι K}, x ∈ E → (x : Matrix ι ι K).det = ∏ a, d x a := by
    intro x hx
    rw [← LinearMap.det_toLin', ← LinearMap.det_toMatrix b,
      show LinearMap.toMatrix b b (Matrix.toLin' (x : Matrix ι ι K)) =
        Matrix.diagonal (d x) from ?_, Matrix.det_diagonal]
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hb x hx j, map_smul, b.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have h := burnsideTA12_card_le_three_pow_of_injective (α := {a : ι // a ≠ a₀})
    (fun (x : E) a => d x a)
    (fun x y hxy => by
      have hxy' : ∀ a, a ≠ a₀ → d x a = d y a := fun a ha => congrFun hxy ⟨a, ha⟩
      apply Subtype.ext
      refine eigen_ext x.2 y.2 fun a => ?_
      by_cases ha : a = a₀
      · subst ha
        have hx := (eigen_det x.2).symm.trans (hdet x x.2)
        have hy := (eigen_det y.2).symm.trans (hdet y y.2)
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)] at hx hy
        have hp : ∏ c ∈ Finset.univ.erase a, d x c = ∏ c ∈ Finset.univ.erase a, d y c :=
          Finset.prod_congr rfl fun c hc => hxy' c (Finset.ne_of_mem_erase hc)
        rw [hp] at hx
        have hne : ∏ c ∈ Finset.univ.erase a, d y c ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hy
          exact zero_ne_one hy
        exact mul_right_cancel₀ hne (hx.trans hy.symm)
      · exact hxy' a ha)
    (fun x a => eigen_pow_three x.2 (hexp x x.2) a)
  rwa [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h

private theorem burnsideTA12_card_le_of_det_eq_one {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (h3 : (3 : K) ≠ 0) (a₀ : ι) (E : Subgroup (GL ι K)) [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hdet : ∀ x ∈ E, (x : Matrix ι ι K).det = 1) :
    Nat.card E ≤ 3 ^ (Fintype.card ι - 1) := by
  set L := AlgebraicClosure K
  set Φ := Matrix.GeneralLinearGroup.map (n := ι) (algebraMap K L)
  have hΦ : Function.Injective Φ := fun _ _ h =>
    Units.ext (Matrix.map_injective (algebraMap K L).injective (congrArg Units.val h))
  have h3' : (3 : L) ≠ 0 := by
    intro h
    apply h3
    apply (algebraMap K L).injective
    rw [map_ofNat, h, map_zero]
  have : Finite (E.map Φ) := Finite.of_surjective _ (Φ.subgroupMap_surjective E)
  have h := burnsideTA12_card_le_of_det_eq_one_of_isAlgClosed h3' a₀ (E.map Φ)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one])
    (by
      rintro _ ⟨x, hx, rfl⟩
      change ((x : Matrix ι ι K).map (algebraMap K L)).det = 1
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet x hx, map_one])
  rwa [Subgroup.card_map_of_injective hΦ] at h


private theorem burnsideTA12_pRank_three_le_two_of_det {X : Type} [Group X] [Finite X] {K : Type}
    [Field K] (h3K : (3 : K) ≠ 0) (ι : X →* GL (Fin 3) K) (hι : Function.Injective ι)
    (hdet : ∀ x, ((ι x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1) :
    CFSG.pRank 3 X ≤ 2 := by
  refine csSup_le' ?_
  rintro r ⟨B, hB, hr⟩
  obtain ⟨hBc, hBe⟩ := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 B).mp hB
  set E : Subgroup (GL (Fin 3) K) := B.map ι with hEdef
  haveI hfin : Finite E := Finite.of_surjective _ (ι.subgroupMap_surjective B)
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩))
  have hexp : ∀ x ∈ E, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hBe x hx, map_one]
  have hdet' : ∀ x ∈ E, (x : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rintro _ ⟨x, -, rfl⟩
    exact hdet x
  have hbound := burnsideTA12_card_le_of_det_eq_one h3K (0 : Fin 3) E hcomm hexp hdet'
  rw [Fintype.card_fin, hEdef, Subgroup.card_map_of_injective hι, hr] at hbound
  have h32 : 3 ^ r ≤ 3 ^ 2 := by simpa using hbound
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h32


private theorem burnsideTA12_card_center_dvd_hopf {K : Type} [Group K] [Finite K] [Group.IsPerfect K] :
    Nat.card (Subgroup.center K) ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (K ⧸ Subgroup.center K)) := by
  have hq : Function.Surjective (QuotientGroup.mk' (Subgroup.center K)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (Subgroup.center K)).ker ≤ Subgroup.center K :=
    (QuotientGroup.ker_mk' _).le
  have hmap := CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift
    (QuotientGroup.mk' (Subgroup.center K)) hq hker
  rw [QuotientGroup.ker_mk'] at hmap
  set L := CFSG.RankThree.PerfectCover.hopfLift (QuotientGroup.mk' (Subgroup.center K)) hq hker
    with hL
  have h1 := Subgroup.card_map_dvd
    (H := CFSG.RankThree.PerfectCover.hopfMultiplier (K ⧸ Subgroup.center K)) L
  rw [hmap] at h1
  exact h1


@[expose] def burnsideTA12_Rows : Prop :=
  ∀ (X : Type) [Group X] (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ),
    (t = .PSL ∨ (t = .PSU ∧ n = 3)) → StatedClassicalModel X t n p f →
    commutator X = ⊤ ∧ Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
      CFSG.Blueprint.Multiplier.generic t n p f × CFSG.Blueprint.Multiplier.exceptional t n p f)

private theorem burnsideTA12_card_hopfMultiplier_psl_three (hR : burnsideTA12_Rows)
    {J : Type} [Group J] {p n : ℕ} (hp2 : p ≠ 2) (hm : StatedClassicalModel J .PSL 3 p n) :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier J) = Nat.gcd 3 (p ^ n - 1) := by
  obtain ⟨-, ⟨e⟩⟩ := hR J .PSL 3 p n (Or.inl rfl) hm
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 3 p n = (Nat.gcd 3 (p ^ n - 1), 1) := rfl
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 p n = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess J).toEquiv,
    Nat.card_congr e.toEquiv, Nat.card_prod]
  unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp only [Nat.card_prod, Nat.card_zmod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _)]
  simp

private theorem burnsideTA12_card_hopfMultiplier_psu_three (hR : burnsideTA12_Rows)
    {J : Type} [Group J] {p n : ℕ} (hm : StatedClassicalModel J .PSU 3 p n) :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier J) = Nat.gcd 3 (p ^ n + 1) := by
  obtain ⟨-, ⟨e⟩⟩ := hR J .PSU 3 p n (Or.inr ⟨rfl, rfl⟩) hm
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 p n = (Nat.gcd 3 (p ^ n + 1), 1) := rfl
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 p n = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess J).toEquiv,
    Nat.card_congr e.toEquiv, Nat.card_prod]
  unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp only [Nat.card_prod, Nat.card_zmod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _)]
  simp

private theorem burnsideTA12_l3Cover (hR : burnsideTA12_Rows) : CFSG.GH74.GLS.LU.Local.L3Cover := by
  intro J _ _ δ p n hp hp2 hδ h5 hJ E _ _ hE π hπ hker
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at h5
    · exact h
  rcases hJ with ⟨rfl, F, _, _, hF, ⟨e⟩⟩ | ⟨rfl, F, _, _, hF, ⟨e⟩⟩
  · refine ⟨fun _ => ⟨F, inferInstance, inferInstance, hF, ?_⟩, fun h => absurd h (by norm_num)⟩
    obtain ⟨p₀, hp₀, hk₀⟩ := CFSG.GH74.GLS.LU.Local.exists_cover_psl_three e
    have hadm : StatedLieAdmissible .PSL 3 p n :=
      ⟨hp, hn, by norm_num, fun h => by simp at h, fun h => by simp at h⟩
    have hcardM := burnsideTA12_card_hopfMultiplier_psl_three hR hp2
      (J := J) ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e⟩⟩
    have : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier J) := Nat.finite_of_card_ne_zero (by
      rw [hcardM]
      exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
    have hS₀ : Group.IsPerfect SL(3, F) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
    refine CFSG.GH74.GLS.LU.Local.exists_surjective_of_card_hopfMultiplier_le hS₀ hE p₀ hp₀ hk₀.le
      π hπ hker ?_
    rw [hcardM, hk₀, CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 3 (by norm_num),
      hF]
  · refine ⟨fun h => absurd h (by norm_num), fun _ => ⟨F, inferInstance, inferInstance, hF, ?_⟩⟩
    obtain ⟨p₀, hp₀, hk₀⟩ := CFSG.GH74.GLS.LU.Local.exists_cover_psu_three e
    have hadm : StatedLieAdmissible .PSU 3 p n :=
      ⟨hp, hn, le_rfl, fun h => by
        simp only [Prod.mk.injEq, true_and] at h
        omega⟩
    have hcardM := burnsideTA12_card_hopfMultiplier_psu_three hR
      (J := J) ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e⟩⟩
    have : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier J) := Nat.finite_of_card_ne_zero (by
      rw [hcardM]
      exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
    have : Fact p.Prime := ⟨hp⟩
    have hS₀ : Group.IsPerfect (StatedSU 3 (p ^ n) F) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF le_rfl (fun h => by
        simp only [Prod.mk.injEq, true_and] at h
        omega)
    refine CFSG.GH74.GLS.LU.Local.exists_surjective_of_card_hopfMultiplier_le hS₀ hE p₀ hp₀ (by
      rw [hk₀]
      exact CFSG.LieType.Universal.Unitary.statedScalars_subgroupOf_le_center 3 (p ^ n)) π hπ
      hker ?_
    rw [hcardM, hk₀, CFSG.GH74.GLS.LU.Local.card_scalars_statedSU_three hp hn hF]

private theorem burnsideTA12_cover_psl3 (hR : burnsideTA12_Rows)
    {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple S) {s f : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hf : 1 ≤ f)
    (hmod : StatedClassicalModel (S ⧸ Subgroup.center S) .PSL 3 s f)
    (hZ3 : Nat.card (Subgroup.center S) = 3) : CFSG.pRank 3 S ≤ 2 := by
  haveI : Group.IsPerfect S := hq.1
  have hcardM := burnsideTA12_card_hopfMultiplier_psl_three hR hs2 hmod
  obtain ⟨hadm, F, iF, iFin, hF, ⟨e⟩⟩ := hmod
  have hdvd : Nat.card (Subgroup.center S) ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (S ⧸ Subgroup.center S)) := burnsideTA12_card_center_dvd_hopf
  rw [hcardM, hZ3] at hdvd
  have h3q : 3 ∣ s ^ f - 1 := (Nat.dvd_gcd_iff.1 hdvd).2
  have hodd : Odd (s ^ f) := (hs.odd_of_ne_two hs2).pow
  have hq3 : 3 ≤ s ^ f := by
    calc 3 ≤ s := by have := hs.two_le; omega
      _ ≤ s ^ f := Nat.le_self_pow (by omega) s
  have hq5 : 5 ≤ s ^ f := by
    obtain ⟨k, hk⟩ := h3q
    obtain ⟨j, hj⟩ := hodd
    omega
  have hs3 : s ≠ 3 := by
    rintro rfl
    have : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    omega
  obtain ⟨hl1, -⟩ := burnsideTA12_l3Cover hR (S ⧸ Subgroup.center S) 1 s f hs hs2
    (Or.inl rfl) hq5 (Or.inl ⟨rfl, F, iF, iFin, hF, ⟨e⟩⟩) S hq.1
    (QuotientGroup.mk' (Subgroup.center S)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _).le
  obtain ⟨F', iF', iFin', hF', α, hα⟩ := hl1 rfl
  have hS : Nat.card S = Nat.card (S ⧸ Subgroup.center S) * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S), hZ3]
  obtain ⟨p₀, hp₀, hk₀⟩ := CFSG.GH74.GLS.LU.Local.exists_cover_psl_three e
  have hcenSL : Nat.card (Subgroup.center SL(3, F)) = 3 := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 3 (by norm_num), hF]
    exact Nat.gcd_eq_left h3q
  have hSLF : Nat.card SL(3, F) = Nat.card (S ⧸ Subgroup.center S) * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup p₀.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective p₀ hp₀).toEquiv, hk₀, hcenSL]
  have hSLF' : Nat.card SL(3, F') = Nat.card SL(3, F) := by
    rw [← CFSG.Open.StatedAPI.card_statedSL, ← CFSG.Open.StatedAPI.card_statedSL,
      CFSG.Open.StatedAPI.card_statedSL_three, CFSG.Open.StatedAPI.card_statedSL_three, hF, hF']
  have hbij : Function.Bijective α :=
    hα.bijective_of_nat_card_le (by rw [hSLF', hSLF, ← hS])
  let eα : SL(3, F') ≃* S := MulEquiv.ofBijective α hbij
  have hchar : ringChar F' = s := burnsideTA12_ringChar_eq hs (by omega) hF'
  haveI : CharP F' s := hchar ▸ ringChar.charP F'
  have h3F' : (3 : F') ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : F') = 0 := by exact_mod_cast h
    exact hs3 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).1
      ((CharP.cast_eq_zero_iff F' s 3).1 h'))
  rw [← CFSG.pRank_congr_of_mulEquiv eα 3]
  exact burnsideTA12_pRank_three_le_two_of_det h3F' Matrix.SpecialLinearGroup.toGL
    Matrix.SpecialLinearGroup.toGL_injective (fun x => by
      simpa using Matrix.SpecialLinearGroup.det_coe x)


private theorem burnsideTA12_cover_psu3 (hR : burnsideTA12_Rows)
    {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple S) {s f : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hf : 1 ≤ f)
    (hmod : StatedClassicalModel (S ⧸ Subgroup.center S) .PSU 3 s f)
    (hZ3 : Nat.card (Subgroup.center S) = 3) : CFSG.pRank 3 S ≤ 2 := by
  haveI : Group.IsPerfect S := hq.1
  have hcardM := burnsideTA12_card_hopfMultiplier_psu_three hR hmod
  obtain ⟨hadm, F, iF, iFin, hF, ⟨e⟩⟩ := hmod
  have hdvd : Nat.card (Subgroup.center S) ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (S ⧸ Subgroup.center S)) := burnsideTA12_card_center_dvd_hopf
  rw [hcardM, hZ3] at hdvd
  have h3q : 3 ∣ s ^ f + 1 := (Nat.dvd_gcd_iff.1 hdvd).2
  have hodd : Odd (s ^ f) := (hs.odd_of_ne_two hs2).pow
  have hq3 : 3 ≤ s ^ f := by
    calc 3 ≤ s := by have := hs.two_le; omega
      _ ≤ s ^ f := Nat.le_self_pow (by omega) s
  have hq5 : 5 ≤ s ^ f := by
    obtain ⟨k, hk⟩ := h3q
    obtain ⟨j, hj⟩ := hodd
    omega
  have hs3 : s ≠ 3 := by
    rintro rfl
    have : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    omega
  obtain ⟨-, hl1⟩ := burnsideTA12_l3Cover hR (S ⧸ Subgroup.center S) (-1) s f hs hs2
    (Or.inr rfl) hq5 (Or.inr ⟨rfl, F, iF, iFin, hF, ⟨e⟩⟩) S hq.1
    (QuotientGroup.mk' (Subgroup.center S)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _).le
  obtain ⟨F', iF', iFin', hF', α, hα⟩ := hl1 rfl
  have hS : Nat.card S = Nat.card (S ⧸ Subgroup.center S) * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S), hZ3]
  obtain ⟨p₀, hp₀, hk₀⟩ := CFSG.GH74.GLS.LU.Local.exists_cover_psu_three e
  have hscal : Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (s ^ f) F)) = 3 := by
    rw [CFSG.GH74.GLS.LU.Local.card_scalars_statedSU_three hs hf hF]
    exact Nat.gcd_eq_left h3q
  have hSUF : Nat.card ↥(StatedSU 3 (s ^ f) F) = Nat.card (S ⧸ Subgroup.center S) * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup p₀.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective p₀ hp₀).toEquiv, hk₀, hscal]
  have hSUF' : Nat.card ↥(StatedSU 3 (s ^ f) F') = Nat.card ↥(StatedSU 3 (s ^ f) F) := by
    rw [CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hF',
      CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hF]
  have hbij : Function.Bijective α :=
    hα.bijective_of_nat_card_le (by rw [hSUF', hSUF, ← hS])
  let eα : ↥(StatedSU 3 (s ^ f) F') ≃* S := MulEquiv.ofBijective α hbij
  have hchar : ringChar F' = s := by
    refine burnsideTA12_ringChar_eq hs (f := 2 * f) (by omega) ?_
    rw [hF', ← pow_mul, mul_comm]
  haveI : CharP F' s := hchar ▸ ringChar.charP F'
  have h3F' : (3 : F') ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : F') = 0 := by exact_mod_cast h
    exact hs3 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).1
      ((CharP.cast_eq_zero_iff F' s 3).1 h'))
  rw [← CFSG.pRank_congr_of_mulEquiv eα 3]
  exact burnsideTA12_pRank_three_le_two_of_det h3F' (StatedSU 3 (s ^ f) F').subtype
    (StatedSU 3 (s ^ f) F').subtype_injective (fun x => CFSG.Open.StatedAPI.det_of_mem_statedSU x.2)

private theorem burnsideTA12_pRank_three_cover_alternating {n : ℕ} (hn6 : 6 ≤ n) (hn8 : n ≤ 8)
    {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    (π : K →* alternatingGroup (Fin n)) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center K) : CFSG.pRank 3 K = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q₀, hQ₀⟩ := CFSG.SectionRank.exists_sylow_eq_sylowThreeAlt hn6 hn8
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hπ 3 Q₀
  have hmap : (P : Subgroup K).map π = (Q₀ : Subgroup (alternatingGroup (Fin n))) := by
    rw [← Sylow.coe_mapSurjective hπ P, hP]
  have hQel : CFSG.Open.IsElemAbelian 3 (Q₀ : Subgroup (alternatingGroup (Fin n))) :=
    hQ₀ ▸ CFSG.SectionRank.isElemAbelian_sylowThreeAlt hn6
  have hQcard : Nat.card (Q₀ : Subgroup (alternatingGroup (Fin n))) = 3 ^ 2 :=
    hQ₀ ▸ CFSG.SectionRank.card_sylowThreeAlt hn6
  obtain ⟨C⟩ : Nonempty (Sylow 3 π.ker) := inferInstance
  obtain ⟨-, hCle⟩ :=
    CFSG.ShultStronglyClosedTI.central_cover_elementary_rank_two_sylow_kernel_bound
      π hπ hC C Q₀ hQel hQcard
  set A : Subgroup K := (C : Subgroup π.ker).map π.ker.subtype
  have hAZ : A ≤ Subgroup.center K := (Subgroup.map_subtype_le _).trans hC
  have hAP : A ≤ (P : Subgroup K) :=
    CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow P A hAZ (C.isPGroup'.map π.ker.subtype)
  have hker := CFSG.ShultStronglyClosedTI.central_kernel_sylow_restriction π hC C P
  have hder := CFSG.ShultStronglyClosedTI.central_kernel_sylow_restriction_le_derived π hC C P
  have hkercard :
      Nat.card (π.subgroupMap (P : Subgroup K)).ker = Nat.card (C : Subgroup π.ker) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv]
    exact (Nat.card_congr ((C : Subgroup π.ker).equivMapOfInjective π.ker.subtype
      Subtype.coe_injective).toEquiv).symm
  have hcardP : Nat.card (P : Subgroup K) = 3 ^ 2 * Nat.card (C : Subgroup π.ker) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (π.subgroupMap (P : Subgroup K)).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
        (MonoidHom.subgroupMap_surjective π (P : Subgroup K))).toEquiv,
      Nat.card_congr (MulEquiv.subgroupCongr hmap).toEquiv, hQcard, hkercard]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 C.isPGroup'
  have hk1 : k ≤ 1 := by
    by_contra h
    push Not at h
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← (CFSG.SectionRank.pRank_sylow P).1]
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le (by norm_num) fun E hEP hE => ?_
    by_contra hlt
    push Not at hlt
    have hEle : Nat.card E ≤ Nat.card (P : Subgroup K) := Subgroup.card_le_of_le hEP
    interval_cases k
    · rw [hk] at hcardP
      omega
    · rw [hk] at hcardP
      have hdvd : Nat.card E ∣ 27 := by
        have := Subgroup.card_dvd_of_le hEP
        rwa [show Nat.card (P : Subgroup K) = 27 by omega] at this
      have hE27 : Nat.card E = 27 := by
        have h27 : Nat.card E ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd
        generalize Nat.card E = d at hdvd h27 hlt
        interval_cases d <;> omega
      have hEP' : E = (P : Subgroup K) :=
        Subgroup.eq_of_le_of_card_ge hEP (by omega)
      have hcomm : IsMulCommutative ↥(P : Subgroup K) := hEP' ▸ hE.1
      have hbot : (π.subgroupMap (P : Subgroup K)).ker ≤ ⊥ := by
        have := hder
        rwa [commutator_eq_bot] at this
      have h1 : Nat.card (π.subgroupMap (P : Subgroup K)).ker = 1 := by
        rw [le_bot_iff.mp hbot]
        exact Subgroup.card_bot
      omega
  · by_contra hlt
    push Not at hlt
    have hnc : ¬ IsCyclic ↥(P : Subgroup K) := by
      intro hcyc
      have h1 : IsCyclic ↥((P : Subgroup K).map π) :=
        isCyclic_of_surjective (π.subgroupMap (P : Subgroup K))
          (MonoidHom.subgroupMap_surjective π (P : Subgroup K))
      rw [hmap] at h1
      obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.1 h1
      have hg3 : g ^ 3 = 1 := Subtype.ext (hQel.2 _ g.2)
      have := orderOf_dvd_of_pow_eq_one hg3
      rw [hg, hQcard] at this
      omega
    haveI : Fact (IsPGroup 3 ↥(P : Subgroup K)) := ⟨P.isPGroup'⟩
    obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
    have hSel' := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 S).1 hSel
    have h2 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3)
      (Subgroup.map_subtype_le S)
      (CFSG.SectionRank.isElemAbelian_map hSel' (P : Subgroup K).subtype)
      (by rw [Subgroup.card_map_of_injective (P : Subgroup K).subtype_injective, hScard])
    omega

private theorem burnsideTA12_cover_of_equiv {K S : Type} [Group K] [Group S]
    (e : K ⧸ Subgroup.center K ≃* S) :
    ∃ π : K →* S, Function.Surjective π ∧ π.ker = Subgroup.center K :=
  ⟨e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), by ext g; simp⟩

private theorem burnsideTA12_I_2_2_two {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) :
    (Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 7))) → CFSG.pRank 3 K = 2 := by
  haveI : Group.IsPerfect K := hK.1
  rintro (he | he)
  · obtain ⟨e⟩ := he
    obtain ⟨π, hπ, hker⟩ := burnsideTA12_cover_of_equiv e
    exact burnsideTA12_pRank_three_cover_alternating (by norm_num) (by norm_num) π hπ hker.le
  · obtain ⟨e⟩ := he
    obtain ⟨π, hπ, hker⟩ := burnsideTA12_cover_of_equiv e
    exact burnsideTA12_pRank_three_cover_alternating (by norm_num) (by norm_num) π hπ hker.le


private theorem burnsideTA12_card_hopf_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier X) =
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier Y) :=
  Nat.card_congr ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).symm.trans
    ((CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).trans
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess Y))).toEquiv

private theorem burnsideTA12_card_hopf_of_rows (hR : burnsideTA12_Rows)
    {J : Type} [Group J] {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (ht : t = .PSL ∨ (t = .PSU ∧ n = 3)) (hm : StatedClassicalModel J t n p f) :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier J) =
      (CFSG.Blueprint.Multiplier.genericOrders t n p f).1 *
        (CFSG.Blueprint.Multiplier.genericOrders t n p f).2 *
      ((CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨e⟩⟩ := hR J t n p f ht hm
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess J).toEquiv,
    Nat.card_congr e.toEquiv, Nat.card_prod]
  unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
  simp only [Nat.card_prod, Nat.card_zmod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _)]


private theorem burnsideTA12_exc_psl2 {s f : ℕ} (hs2 : s ≠ 2) (h92 : ¬ (s = 3 ∧ f = 2)) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 s f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | simp_all

private theorem burnsideTA12_exc_psl3 {s f : ℕ} (hs2 : s ≠ 2) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 s f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | simp_all

private theorem burnsideTA12_exc_psu3 {s f : ℕ} :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 s f = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | simp_all


@[expose] def burnsideTA12_RankTwoList : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    twoRank G = 2 →
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 2 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSU 3 p f) ∨
    StatedClassicalModel G .PSU 3 2 2 ∨
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (G ≃* StatedM11)

@[expose] def burnsideTA12_M11OddCover : Prop :=
  ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* ↥StatedM11),
    Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥

private theorem burnsideTA12_coverFact_of (hList : burnsideTA12_RankTwoList)
    (hR : burnsideTA12_Rows)
    (hA6 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 6))) = 6)
    (hA7 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 7))) = 6)
    (hM11 : burnsideTA12_M11OddCover) :
    burnsideTA12_CoverFact := by
  intro S _ _ p hp hp2 hq hr2 hZ hZp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect S := hq.1
  haveI : IsSimpleGroup (S ⧸ Subgroup.center S) := hq.2.1
  have hnab : ∃ a b : S ⧸ Subgroup.center S, a * b ≠ b * a := hq.2.2
  have hdvd := burnsideTA12_card_center_dvd_hopf (K := S)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hZp
  have hk1 : 1 ≤ k := by
    by_contra h
    have h0 : k = 0 := by omega
    rw [h0, pow_zero] at hk
    exact hZ (Subgroup.card_eq_one.1 hk)
  have hpk : p ∣ Nat.card (Subgroup.center S) := by
    rw [hk]
    exact dvd_pow_self p (by omega)
  have key : ∀ M : ℕ, Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (S ⧸ Subgroup.center S)) = M → p ∣ M := fun M hM => hM ▸ hpk.trans hdvd
  have hnd2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have hnd1 : ¬ p ∣ 1 := fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)
  have hp3_of_dvd_six : p ∣ 6 → p = 3 := by
    intro h
    have h6 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h6] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h3
    · exact absurd h2 hnd2
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
  have hp3_of_dvd_three : p ∣ 3 → p = 3 := fun h =>
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
  rcases hList (S ⧸ Subgroup.center S) hnab hr2 with
    ⟨s, f, hs, hs2, hf, hmod⟩ | ⟨s, f, hs, hs2, hf, hmod⟩ | ⟨s, f, hs, hs2, hf, hmod⟩ | hmod |
    he7 | he11
  ·
    have hcard := burnsideTA12_card_hopf_of_rows hR (Or.inl rfl) hmod
    by_cases h92 : s = 3 ∧ f = 2
    · obtain ⟨rfl, rfl⟩ := h92
      obtain ⟨e6⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine hmod
      have h6 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (S ⧸ Subgroup.center S)) =
          6 := (burnsideTA12_card_hopf_congr e6).trans hA6
      have hp3 := hp3_of_dvd_six (key 6 h6)
      subst hp3
      rw [burnsideTA12_I_2_2_two hq (Or.inl ⟨e6⟩)]
    · exfalso
      have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 s f = (1, 1) :=
        burnsideTA12_exc_psl2 hs2 h92
      have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 2 s f =
          (Nat.gcd 2 (s ^ f - 1), 1) := rfl
      rw [hgen, hexc] at hcard
      have hodd : Odd (s ^ f) := (hs.odd_of_ne_two hs2).pow
      have hg : Nat.gcd 2 (s ^ f - 1) = 2 := by
        obtain ⟨j, hj⟩ := hodd
        exact Nat.gcd_eq_left ⟨j, by omega⟩
      simp only [hg] at hcard
      exact hnd2 (key 2 (by simpa using hcard))
  ·
    have hcard := burnsideTA12_card_hopf_of_rows hR (Or.inl rfl) hmod
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 s f = (1, 1) :=
      burnsideTA12_exc_psl3 hs2
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 3 s f =
        (Nat.gcd 3 (s ^ f - 1), 1) := rfl
    rw [hgen, hexc] at hcard
    have hcard' : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (S ⧸ Subgroup.center S)) =
        Nat.gcd 3 (s ^ f - 1) := by simpa using hcard
    have h3 : p ∣ 3 := (key _ hcard').trans (Nat.gcd_dvd_left _ _)
    have hp3 := hp3_of_dvd_three h3
    subst hp3
    have hZ3 : Nat.card (Subgroup.center S) = 3 := by
      have hd3 : Nat.card (Subgroup.center S) ∣ 3 :=
        (hcard' ▸ hdvd).trans (Nat.gcd_dvd_left _ _)
      rcases (Nat.dvd_prime Nat.prime_three).1 hd3 with h | h
      · exact absurd (Subgroup.card_eq_one.1 h) hZ
      · exact h
    exact burnsideTA12_cover_psl3 hR hq hs hs2 hf hmod hZ3
  ·
    have hcard := burnsideTA12_card_hopf_of_rows hR (Or.inr ⟨rfl, rfl⟩) hmod
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 s f = (1, 1) :=
      burnsideTA12_exc_psu3
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 s f =
        (Nat.gcd 3 (s ^ f + 1), 1) := rfl
    rw [hgen, hexc] at hcard
    have hcard' : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (S ⧸ Subgroup.center S)) =
        Nat.gcd 3 (s ^ f + 1) := by simpa using hcard
    have h3 : p ∣ 3 := (key _ hcard').trans (Nat.gcd_dvd_left _ _)
    have hp3 := hp3_of_dvd_three h3
    subst hp3
    have hZ3 : Nat.card (Subgroup.center S) = 3 := by
      have hd3 : Nat.card (Subgroup.center S) ∣ 3 :=
        (hcard' ▸ hdvd).trans (Nat.gcd_dvd_left _ _)
      rcases (Nat.dvd_prime Nat.prime_three).1 hd3 with h | h
      · exact absurd (Subgroup.card_eq_one.1 h) hZ
      · exact h
    exact burnsideTA12_cover_psu3 hR hq hs hs2 hf hmod hZ3
  ·
    exfalso
    have hcard := burnsideTA12_card_hopf_of_rows hR (Or.inr ⟨rfl, rfl⟩) hmod
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 2 2 = (1, 1) := rfl
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 2 2 = (1, 1) := by
      show (Nat.gcd 3 (2 ^ 2 + 1), 1) = (1, 1)
      norm_num
    rw [hgen, hexc] at hcard
    exact hnd1 (key 1 (by simpa using hcard))
  ·
    obtain ⟨e⟩ := he7
    have h6 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (S ⧸ Subgroup.center S)) =
        6 := (burnsideTA12_card_hopf_congr e).trans hA7
    have hp3 := hp3_of_dvd_six (key 6 h6)
    subst hp3
    rw [burnsideTA12_I_2_2_two hq (Or.inr ⟨e⟩)]
  ·
    exfalso
    obtain ⟨e⟩ := he11
    obtain ⟨π, hπ, hker⟩ := burnsideTA12_cover_of_equiv e
    have hodd : Odd (Nat.card π.ker) := by
      rw [hker, hk]
      exact (hp.odd_of_ne_two hp2).pow
    exact hZ (hker ▸ hM11 S π hπ hker.le hodd)

private theorem burnsideTA12_rankTwoList :
    burnsideTA12_RankTwoList := by
  intro G _ _ _ hn hr
  exact CFSG.Milestones.lr_rank_two_isomorphism_types G hn hr

private theorem burnsideTA12_rows :
    burnsideTA12_Rows := by
  intro X _ t n p f ht hm
  rcases ht with rfl | ⟨rfl, rfl⟩
  · exact CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row hm
  · exact CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row hm (by decide)

private theorem burnsideTA12_hopf_alternating_six :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 6))) = 6 :=
  CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six.2

private theorem burnsideTA12_hopf_alternating_seven :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 7))) = 6 :=
  CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_seven.2

private theorem burnsideTA12_m11OddCover :
    burnsideTA12_M11OddCover := by
  intro E _ _ _ π hπ hker hodd
  let e : ↥StatedM11 ≃* ↥CFSG.Blueprint.NativeSporadic.M11 :=
    MulEquiv.subgroupCongr CFSG.Semidihedral.GL2Recognition.statedM11_eq_nativeM11
  have hker' : ((e : ↥StatedM11 →* ↥CFSG.Blueprint.NativeSporadic.M11).comp π).ker = π.ker :=
    MonoidHom.ker_mulEquiv_comp π e
  have h := CFSG.QuasithinUnique.Ch1.M11_perfect_odd_cover_trivial
    ((e : ↥StatedM11 →* ↥CFSG.Blueprint.NativeSporadic.M11).comp π)
    (e.surjective.comp hπ) (hker'.symm ▸ hker) (hker'.symm ▸ hodd)
  rwa [hker'] at h

private theorem burnsideTA12_coverFact :
    burnsideTA12_CoverFact :=
  burnsideTA12_coverFact_of burnsideTA12_rankTwoList burnsideTA12_rows
    burnsideTA12_hopf_alternating_six burnsideTA12_hopf_alternating_seven burnsideTA12_m11OddCover


end BurnsideTA12cov

section BurnsideTA12pair

open CFSG.ASVolI.ChA
open Subgroup CFSG.SectionRank.QTK CFSG.SectionRank.QTK.CoverB CFSG.SectionRank.QTK.CentreFact

variable {H : Type} [Group H] [Finite H]

private theorem burnsideTA12_exists_E9 {L : Subgroup H} (hL : CFSG.IsComponent L)
    (hZ : Nat.card (center ↥L) = 3) :
    ∃ E : Subgroup H, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ E ≤ L := by
  haveI : Group.IsPerfect ↥L := hL.1.1
  obtain ⟨g, hg, hgZ⟩ := CFSG.SectionRank.exists_orderOf_not_mem_center_of_card_center
    (Or.inr hZ) (p := 3) Nat.prime_three (by norm_num) (by
      have : 3 ∣ Nat.card (center ↥L) := by rw [hZ]
      exact this.trans (Subgroup.card_subgroup_dvd_card _))
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_sq_of_lift Nat.prime_three hg3 hgZ
    (fun h => absurd (by rw [hZ]) h)
  refine ⟨E.map L.subtype, isElemAbelian_map _ hE, ?_, map_subtype_le E⟩
  rw [Subgroup.card_map_of_injective L.subtype_injective, hEc]

private theorem burnsideTA12_isPGroup_zpowers_of_sq {X : Type*} [Group X] {x : X} (hx : x ^ 2 = 1) :
    IsPGroup 2 (zpowers x) := by
  intro g
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  change (g : X) ^ 2 ^ 1 = 1
  rw [← hm, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

private theorem burnsideTA12_mem_normalizer_zpowers {X : Type*} [Group X] {g x : X} (h : Commute x g) :
    x ∈ normalizer ((zpowers g : Subgroup X) : Set X) := by
  refine Subgroup.centralizer_le_normalizer ((zpowers g : Subgroup X) : Set X)
    (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact (h.symm.zpow_left m).eq

private theorem burnsideTA12_false_of_normalizing (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {R : Subgroup H} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hRL : R ≤ L₁) {F₂ : Subgroup H}
    (hF₂ : CFSG.Open.IsElemAbelian r F₂) (hF₂c : Nat.card F₂ = r ^ 2) (hF₂L : F₂ ≤ L₂) {y : H}
    (hyr : y ^ r = 1) (hyL : y ∉ L₂) (hyN : y ∈ normalizer (R : Set H))
    (hyF : ∀ g ∈ F₂, Commute y g) : False := by
  have hF₂N : F₂ ≤ normalizer (R : Set H) := hF₂L.trans (le_normalizer_of_commuting hc hRL)
  obtain ⟨F, hF, hFc, hFN⟩ := exists_elemAbelian_sup hr hF₂ hF₂c hyr hyF
    (fun h => hyL (hF₂L h)) (K := normalizer (R : Set H)) hyN hF₂N
  have := le_two_of_evenRank_le_two he hR hR2 hr hr2 hF hFN hFc
  omega

private theorem burnsideTA12_false_of_extra_element (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {t : H}
    (htL : t ∈ L₁) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) {F₂ : Subgroup H}
    (hF₂ : CFSG.Open.IsElemAbelian r F₂) (hF₂c : Nat.card F₂ = r ^ 2) (hF₂L : F₂ ≤ L₂) {y : H}
    (hyr : y ^ r = 1) (hyL : y ∉ L₂) (hyt : Commute y t) (hyF : ∀ g ∈ F₂, Commute y g) :
    False :=
  burnsideTA12_false_of_normalizing he hc hr hr2
    (fun h => ht1 (Subgroup.mem_bot.mp (h ▸ mem_zpowers t)))
    (burnsideTA12_isPGroup_zpowers_of_sq ht2) (zpowers_le.2 htL) hF₂ hF₂c hF₂L hyr hyL
    (burnsideTA12_mem_normalizer_zpowers hyt) hyF

private theorem burnsideTA12_false_of_lift (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {y : ↥L₁}
    (hy : y ^ r = 1) (hyZ : y ∉ center ↥L₁) {R₂ : Subgroup ↥L₁} (hR₂ : R₂ ≠ ⊥)
    (hR₂2 : IsPGroup 2 R₂) (hyN : y ∈ normalizer (R₂ : Set ↥L₁)) {E₂ : Subgroup H}
    (hE₂ : CFSG.Open.IsElemAbelian r E₂) (hE₂c : Nat.card E₂ = r ^ 2) (hE₂L : E₂ ≤ L₂) :
    False := by
  obtain ⟨hRh, hRh2, hRhL, hyhN⟩ := map_two_subgroup hR₂ hR₂2 hyN
  have hyh : ((y : H)) ^ r = 1 := by rw [← SubgroupClass.coe_pow, hy, OneMemClass.coe_one]
  exact burnsideTA12_false_of_normalizing he hc hr hr2 hRh hRh2 hRhL hE₂ hE₂c hE₂L hyh
    (fun h => hyZ (mem_center_of_mem_commuting hc h)) hyhN
    (fun e he' => hc _ y.2 e (hE₂L he'))

@[expose] def burnsideTA12_RLLift (Y : Type) [Group Y] : Prop :=
  ∃ y : Y, y ^ 3 = 1 ∧ y ∉ center Y ∧
    ∃ R : Subgroup Y, R ≠ ⊥ ∧ IsPGroup 2 R ∧ y ∈ normalizer (R : Set Y)

private theorem burnsideTA12_false_of_RLLift (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (h₂ : CFSG.IsComponent L₂) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b)
    (hZ₂ : Nat.card (center ↥L₂) = 3) (hL : burnsideTA12_RLLift ↥L₁) : False := by
  obtain ⟨y, hy, hyZ, R₂, hR₂, hR₂2, hyN⟩ := hL
  obtain ⟨E₂, hE₂, hE₂c, hE₂L⟩ := burnsideTA12_exists_E9 h₂ hZ₂
  exact burnsideTA12_false_of_lift he hc Nat.prime_three (by norm_num) hy hyZ hR₂ hR₂2 hyN hE₂
    hE₂c hE₂L

private theorem burnsideTA12_centerOf_eq_of_card (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (h₁ : CFSG.IsComponent L₁) (h₂ : CFSG.IsComponent L₂)
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) (hZ₁ : Nat.card (center ↥L₁) = 3)
    (hZ₂ : Nat.card (center ↥L₂) = 3) : centerOf L₁ = centerOf L₂ := by
  rw [burnsideTA12_centerOf_eq, burnsideTA12_centerOf_eq]
  set Z₁ : Subgroup H := (center ↥L₁).map L₁.subtype with hZ₁def
  set Z₂ : Subgroup H := (center ↥L₂).map L₂.subtype with hZ₂def
  by_contra hne
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc1 : Nat.card Z₁ = 3 := by
    rw [hZ₁def, Subgroup.card_map_of_injective L₁.subtype_injective, hZ₁]
  have hc2 : Nat.card Z₂ = 3 := by
    rw [hZ₂def, Subgroup.card_map_of_injective L₂.subtype_injective, hZ₂]
  have hinf : ∀ x ∈ Z₁, x ∈ Z₂ → x = 1 := by
    intro x hx1 hx2
    by_contra hx
    have hle : Z₁ ⊓ Z₂ = Z₁ := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
      have hd : Nat.card ↥(Z₁ ⊓ Z₂) ∣ 3 := by
        rw [← hc1]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
      · exfalso
        have h1 : Z₁ ⊓ Z₂ = ⊥ := Subgroup.eq_bot_of_card_eq _ h
        exact hx (Subgroup.mem_bot.1 (h1 ▸ Subgroup.mem_inf.2 ⟨hx1, hx2⟩))
      · rw [h, hc1]
    have hle2 : Z₁ ⊓ Z₂ = Z₂ := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
      have : Nat.card ↥(Z₁ ⊓ Z₂) = Nat.card ↥Z₁ := by rw [hle]
      rw [this, hc1, hc2]
    exact hne (hle.symm.trans hle2)
  obtain ⟨z₁, hz₁⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z₁) 3 (by rw [hc1])
  have hz₁3 : ((z₁ : ↥Z₁) : H) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (z₁ : H)
    rwa [Subgroup.orderOf_coe, hz₁] at h
  have hz₁1 : ((z₁ : ↥Z₁) : H) ≠ 1 := fun h => by
    have h1 : orderOf ((z₁ : ↥Z₁) : H) = 1 := by rw [h, orderOf_one]
    rw [Subgroup.orderOf_coe, hz₁] at h1
    omega
  obtain ⟨w, hwZ, hw⟩ := (Subgroup.mem_map.1 z₁.2)
  obtain ⟨R, hR, hR2, hRL⟩ :=
    CFSG.SectionRank.QTK.CentreFact.layer_exists_two_subgroup_le_component h₁
  have hzN : ((z₁ : ↥Z₁) : H) ∈ normalizer (R : Set H) := by
    refine Subgroup.centralizer_le_normalizer (R : Set H)
      (Subgroup.mem_centralizer_iff.2 fun g hg => ?_)
    have h := Subgroup.mem_center_iff.1 hwZ ⟨g, hRL hg⟩
    have h' := congrArg (fun x : ↥L₁ => (x : H)) h
    simp only [Subgroup.coe_mul] at h'
    rw [← hw]
    exact h'
  have hzL₂ : ((z₁ : ↥Z₁) : H) ∉ L₂ := by
    intro hz2
    have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, Commute a b := fun a ha b hb => (hc b hb a ha).symm
    have hw1 : (w : H) ∈ L₂ := by rw [Subgroup.coe_subtype] at hw; rw [hw]; exact hz2
    have hwc : (⟨(w : H), hw1⟩ : ↥L₂) ∈ center ↥L₂ :=
      mem_center_of_mem_commuting hc' w.2
    refine hz₁1 (hinf _ z₁.2 ?_)
    rw [← hw]
    exact ⟨_, hwc, rfl⟩
  obtain ⟨E₂, hE₂, hE₂c, hE₂L⟩ := burnsideTA12_exists_E9 h₂ hZ₂
  exact burnsideTA12_false_of_normalizing he hc Nat.prime_three (by norm_num) hR hR2 hRL hE₂
    hE₂c hE₂L hz₁3 hzL₂ hzN (fun g hg => by
      rw [← hw]
      exact hc _ w.2 g (hE₂L hg))

private theorem burnsideTA12_quot_equiv {Y S : Type} [Group Y] [Group S] (φ : Y ≃* S) (Z : Subgroup S)
    [Z.Normal] (hZ : center S = Z) : Nonempty (Y ⧸ center Y ≃* S ⧸ Z) :=
  ⟨QuotientGroup.congr (center Y) Z φ (by rw [Subgroup.map_center_eq φ, hZ])⟩

private theorem burnsideTA12_center_statedSL_eq {K : Type} [Field K] (n : ℕ) :
    center ↥(StatedSL n K) = (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) := by
  rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars n K,
    Subgroup.map_center_eq (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K)]

open CFSG.Open.StatedCenterThree in
private theorem burnsideTA12_center_statedSU_le_scalars {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) :
    center ↥(StatedSU 3 q K) ≤ (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K) := by
  intro z hz
  have hq2 := two_le_of_card_eq_sq hK
  have hq : q ≠ 0 := by omega
  obtain ⟨a, ha⟩ := exists_orderOf_eq hK
  have haq : a ^ (q + 1) = 1 := ha ▸ pow_orderOf_eq_one a
  have ha1 : (a : K) ≠ 1 := fun h => by
    have : a = 1 := Units.ext h
    rw [this, orderOf_one] at ha
    omega
  have ha2 : (a : K) ≠ ((a⁻¹ : Kˣ) : K) := fun h => by
    have h' : a ^ 2 = 1 := by
      rw [sq]
      nth_rw 2 [Units.ext h]
      exact mul_inv_cancel a
    have := orderOf_dvd_of_pow_eq_one h'
    rw [ha] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hb1 : ((a⁻¹ : Kˣ) : K) ≠ 1 := fun h => ha1 (by
    have : a⁻¹ = 1 := Units.ext h
    rw [inv_eq_one.mp this, Units.val_one])
  have hinj : Function.Injective ![(a : K), ((a⁻¹ : Kˣ) : K), 1] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin 3) (Fin 3) K,
      M = (((z : ↥(StatedSU 3 q K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  have hcomm : ∀ g : ↥(StatedSU 3 q K), ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
      M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun g => by
    have := Subgroup.mem_center_iff.mp hz g
    rw [hMdef]
    exact congrArg
      (fun x : ↥(StatedSU 3 q K) => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) this
  have hD := hcomm ⟨diagGL a, diagGL_mem hq haq⟩
  have hdiag := eq_diagonal_of_commute hinj hD.symm
  have hP := hcomm ⟨cyc3GL, cyc3GL_mem hq⟩
  change cyc3 * M = M * cyc3 at hP
  rw [hdiag] at hP
  obtain ⟨h1, h2⟩ := eq_of_diagonal_commute_cyc3 hP.symm
  have hMs : M = Matrix.scalar (Fin 3) (M 0 0) := by
    rw [hdiag, Matrix.scalar_apply]
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact h1
    · exact h2
  have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSU (z : ↥(StatedSU 3 q K)).2
  rw [← hMdef] at hdet
  rw [hMs, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  have hne : M 0 0 ≠ 0 := fun h0 => by rw [h0] at hdet; simp at hdet
  refine Subgroup.mem_subgroupOf.2 ⟨Units.mk0 (M 0 0) hne, ?_⟩
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  rw [← hMdef]
  exact hMs.symm

private theorem burnsideTA12_center_statedSU_eq {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) :
    center ↥(StatedSU 3 q K) = (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K) :=
  le_antisymm (burnsideTA12_center_statedSU_le_scalars hK)
    (CFSG.LieType.Universal.Unitary.statedScalars_subgroupOf_le_center 3 q)

private theorem burnsideTA12_RLLift_of_real {Y : Type} [Group Y] [Finite Y]
    (h : RealLocalElement (Y ⧸ center Y) 3) : burnsideTA12_RLLift Y := by
  obtain ⟨R, hR, hR2, x, hxN, hx, d, hd⟩ := h
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  obtain ⟨y, hy3, hyx⟩ :=
    exists_lift_pow_eq_one Nat.prime_three (by norm_num) hx3 (Or.inl ⟨d, hd⟩)
  obtain ⟨R₂, hR₂, hR₂2, hR₂N⟩ := exists_two_subgroup_normalized hR hR2
  refine ⟨y, hy3, ?_, R₂, hR₂, hR₂2, hR₂N y (by rw [hyx]; exact hxN)⟩
  intro hyZ
  have h1 : (y : Y ⧸ center Y) = 1 := (QuotientGroup.eq_one_iff y).2 hyZ
  rw [hyx] at h1
  rw [h1, orderOf_one] at hx
  omega

private theorem burnsideTA12_RLLift_of_isSL3 {Y : Type} [Group Y] [Finite Y] {q : ℕ}
    (h : CFSG.Quasithin.IsSL3 q Y) : burnsideTA12_RLLift Y := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  obtain ⟨e⟩ := burnsideTA12_quot_equiv φ _ (burnsideTA12_center_statedSL_eq 3)
  exact burnsideTA12_RLLift_of_real
    (RealLocalElement.of_mulEquiv e
      CFSG.SectionRank.QTK.CentreFact.LayerPair.realLocalElement_psl_three)

private theorem burnsideTA12_RLLift_of_isSU3_odd {Y : Type} [Group Y] [Finite Y] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : CFSG.Quasithin.IsSU3 (p ^ f) Y) :
    burnsideTA12_RLLift Y := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow hp hK
  obtain ⟨e⟩ := burnsideTA12_quot_equiv φ _ (burnsideTA12_center_statedSU_eq hK)
  exact burnsideTA12_RLLift_of_real
    (RealLocalElement.of_mulEquiv e
      (CFSG.SectionRank.QTK.CentreFact.LayerPair.realLocalElement_psu_three_odd (f := f) hp2))

private theorem burnsideTA12_false_of_isSU3_two {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.IsQuasisimple Y) (h : CFSG.Quasithin.IsSU3 2 Y) : False := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow (f := 1) Nat.prime_two
    (by rw [hK]; norm_num)
  have hcard : Nat.card Y = 216 := by
    have h2 := CFSG.SectionRank.OddCover.card_statedSU_three (K := K) (p := 2) (f := 1)
      (by rw [hK]; norm_num)
    rw [pow_one] at h2
    rw [Nat.card_congr φ.toEquiv, h2]
    norm_num
  have hsolv : Group.IsSolvable Y := by
    refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    rw [hcard]
    have h216 : Nat.primeFactors 216 = {2, 3} := by
      rw [show (216 : ℕ) = 2 ^ 3 * 3 ^ 3 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
      rfl
    rw [h216]
    decide
  have hn : Nontrivial Y := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hp : Group.IsPerfect Y := hq.1
  exact Group.IsPerfect.not_isSolvable Y hsolv

private theorem burnsideTA12_rl_or_su3 {Y : Type} [Group Y] [Finite Y] (hq : CFSG.IsQuasisimple Y)
    (hA : CFSG.Quasithin.A36Case2List Y) :
    burnsideTA12_RLLift Y ∨ ∃ f : ℕ, 3 ≤ f ∧ Odd f ∧ IsSUn 3 (2 ^ f) Y := by
  rcases hA with ⟨s, p, e, hp, he1, hcond, hSL⟩ | hA6 | hA7 | hM22
  · cases s
    · by_cases hp2 : p = 2
      · subst hp2
        right
        have hmod : Int.ModEq 3 ((2 ^ e : ℕ) : ℤ) (-1) := by
          rcases hcond with ⟨-, h⟩ | ⟨h, -⟩
          · simpa using h
          · exact absurd rfl h
        have hodd : Odd e := by
          rcases Nat.even_or_odd e with ⟨k, hk⟩ | hk
          · exfalso
            have h4 : ((2 ^ e : ℕ) : ℤ) ≡ 1 [ZMOD 3] := by
              rw [hk, ← two_mul, pow_mul]
              push_cast
              have : (2 : ℤ) ^ 2 ≡ 1 [ZMOD 3] := by decide
              simpa using this.pow k
            have := h4.symm.trans hmod
            revert this
            decide
          · exact hk
        have he3 : 3 ≤ e := by
          obtain ⟨k, hk⟩ := hodd
          by_contra hlt
          have : e = 1 := by omega
          subst this
          exact burnsideTA12_false_of_isSU3_two hq (by rw [pow_one] at hSL; exact hSL)
        exact ⟨e, he3, hodd, hSL⟩
      · exact Or.inl (burnsideTA12_RLLift_of_isSU3_odd hp hp2 (f := e) hSL)
    · exact Or.inl (burnsideTA12_RLLift_of_isSL3 hSL)
  · obtain ⟨-, -, ⟨e⟩⟩ := hA6
    exact Or.inl (burnsideTA12_RLLift_of_real (RealLocalElement.of_mulEquiv e
      (CFSG.SectionRank.QTK.CentreFact.LayerPair.realLocalElement_alternating_six_seven
        (Or.inl rfl))))
  · obtain ⟨-, -, ⟨e⟩⟩ := hA7
    exact Or.inl (burnsideTA12_RLLift_of_real (RealLocalElement.of_mulEquiv e
      (CFSG.SectionRank.QTK.CentreFact.LayerPair.realLocalElement_alternating_six_seven
        (Or.inr rfl))))
  · obtain ⟨-, -, ⟨e⟩⟩ := hM22
    exact Or.inl (burnsideTA12_RLLift_of_real (RealLocalElement.of_mulEquiv e
      (CFSG.SectionRank.QTK.CentreFact.LayerPair.realLocalElement_mathieu (s := .M22)
        (Or.inr (Or.inl rfl)))))

private theorem burnsideTA12_isProperSectionOf_subgroup_quotient {G : Type} [Group G] [Finite G]
    (L : Subgroup G) (hL : L ≠ ⊤) (N : Subgroup ↥L) [N.Normal] : IsProperSectionOf (↥L ⧸ N) G := by
  have hN : (N.map L.subtype).subgroupOf L = N :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective N
  haveI hnorm : ((N.map L.subtype).subgroupOf L).Normal := by rw [hN]; infer_instance
  refine ⟨⟨L, N.map L.subtype, hnorm, ⟨QuotientGroup.quotientMulEquivOfEq hN.symm⟩⟩, ?_⟩
  have h1 : Nat.card (↥L ⧸ N) ≤ Nat.card ↥L := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hN : 0 < Nat.card N := Nat.card_pos
    nlinarith [Nat.card_pos (α := ↥L ⧸ N)]
  exact lt_of_le_of_lt h1 (lt_of_le_of_ne (Subgroup.card_le_card_group L) fun h =>
    hL ((Subgroup.card_eq_iff_eq_top L).mp h))

private theorem burnsideTA12_ne_top_of_partner {L₁ L₂ : Subgroup H} (h₂ : CFSG.IsComponent L₂)
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) : L₁ ≠ ⊤ := by
  intro htop
  have hab : ∀ a ∈ L₂, ∀ b ∈ L₂, a * b = b * a := fun a _ b hb =>
    (hc a (htop ▸ Subgroup.mem_top a) b hb).eq
  obtain ⟨a, b, hne⟩ := h₂.1.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext (hab a a.2 b b.2)))

private theorem burnsideTA12_comp_data (hCat : CFSG.SectionRank.CatalogStepHyp)
    (hTC : CFSG.QuasithinUnique.Vol2Native.ThreeCoverFactCat)
    (hev : CFSG.Open.evenRank H ≤ 2) (hK : CFSG.SectionRank.IsKGroupCat H)
    (hC : burnsideTA12_CForSections H) {L₁ L₂ : Subgroup H} (h₁ : CFSG.IsComponent L₁)
    (h₂ : CFSG.IsComponent L₂) (hne : L₁ ≠ L₂) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrZ : IsPGroup r ↥(center ↥L₁)) (hZ : center ↥L₁ ≠ ⊥) :
    r = 3 ∧ Nat.card (center ↥L₁) = 3 ∧ CFSG.Quasithin.A36Case2List ↥L₁ := by
  have hc := layer_commute_of_distinct_components h₁ h₂ hne
  have hq : CFSG.IsQuasisimple ↥L₁ := h₁.1
  have hsqt : CFSG.IsStronglyQuasithin ↥L₁ := fun s hs hs2 => by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact layer_pRank_component_le_two hev h₁ h₂ hne hs hs2
  have hKL : CFSG.SectionRank.IsKGroupCat ↥L₁ := hK.subgroup L₁
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hrZ
  have hodd : Odd (Nat.card (center ↥L₁)) := by
    rw [hk]
    exact (hr.odd_of_ne_two hr2).pow
  have hcat := hCat ↥L₁ hq ⟨hsqt, hKL⟩ hodd
  have hZ3 : Nat.card (center ↥L₁) = 3 := by
    rcases hcat.1 with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hZ
    · exact h
  have hr3 : r = 3 := by
    have hk1 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      omega
    have : r ∣ 3 := by
      rw [← hZ3, hk]
      exact dvd_pow_self r hk1
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 this
  refine ⟨hr3, hZ3, hTC ↥L₁ hq hZ3 ?_⟩
  have hsimple : IsSimpleGroup (↥L₁ ⧸ center ↥L₁) := hq.2.1
  have hsec := burnsideTA12_isProperSectionOf_subgroup_quotient L₁
    (burnsideTA12_ne_top_of_partner h₂ hc) (center ↥L₁)
  have hKq : CFSG.SectionRank.IsKGroupCat (↥L₁ ⧸ center ↥L₁) :=
    CFSG.SectionRank.K_group_section_closure hK L₁ (center ↥L₁) (MulEquiv.refl _)
  exact hC _ hsec hsimple hq.2.2 ⟨hcat.2 (center ↥L₁) le_rfl, hKq⟩

private theorem burnsideTA12_exists_zeta {K : Type} [Field K] [Finite K] {q d : ℕ}
    (hK : Nat.card K = q ^ 2) (hd : d ∣ q + 1) : ∃ ζ : Kˣ, orderOf ζ = d ∧ ζ ^ (q + 1) = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hcard : Nat.card Kˣ = q ^ 2 - 1 := by rw [Nat.card_units, hK]
  have hq2 : 2 ≤ q := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hK
  have hN : q ^ 2 - 1 = (q - 1) * (q + 1) := CFSG.Open.StatedCenterThree.sq_sub_one_eq (by omega)
  have hdN : d ∣ q ^ 2 - 1 := by rw [hN]; exact hd.mul_left _
  have hN0 : q ^ 2 - 1 ≠ 0 := by rw [hN]; exact Nat.mul_ne_zero (by omega) (by omega)
  have hd0 : d ≠ 0 := fun h => by rw [h] at hdN; exact hN0 (Nat.eq_zero_of_zero_dvd hdN)
  set m := (q ^ 2 - 1) / d with hm
  have hm0 : m ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdN) (Nat.pos_of_ne_zero hd0)
    omega
  have hmdvd : m ∣ orderOf g := by rw [hg, hcard]; exact Nat.div_dvd_of_dvd hdN
  have hord : orderOf (g ^ m) = d := by
    rw [orderOf_pow_of_dvd hm0 hmdvd, hg, hcard, hm]
    exact Nat.div_div_self hdN hN0
  exact ⟨g ^ m, hord, orderOf_dvd_iff_pow_eq_one.1 (by rw [hord]; exact hd)⟩

private theorem burnsideTA12_diag_mem {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0) {d : Fin 3 → Kˣ}
    (hd : d 0 * d 1 * d 2 = 1) (hdq : ∀ i, d i ^ (q + 1) = 1) :
    CFSG.SectionRank.ClassicalEven.torusDiag d ∈ StatedSU 3 q K :=
  CFSG.SectionRank.ClassicalEven.torusDiag_mem_SU hq (by rw [Fin.prod_univ_three]; exact hd)
    (funext fun i => hdq i)

open CFSG.SectionRank.ClassicalEven CFSG.RankThree.PartTwo.Census Matrix in
private theorem burnsideTA12_su3_witness_s {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (hd : s ∣ 2 ^ f + 1) :
    (∃ x t : StatedSU 3 (2 ^ f) K, orderOf x = s ∧ t ^ 2 = 1 ∧ t ≠ 1 ∧ Commute x t) ∧
    ∃ E : Subgroup ↥(StatedSU 3 (2 ^ f) K), CFSG.Open.IsElemAbelian s E ∧
      Nat.card E = s ^ 2 := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : CharP K 2 := hU.charP
  have hq : (2 ^ f : ℕ) ≠ 0 := by positivity
  obtain ⟨ζ, hζ, hζq⟩ := burnsideTA12_exists_zeta hK hd
  have hζs : ζ ^ s = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζ
    exact hs.one_lt.ne hζ
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at this
    exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).1 this)
  set d : Fin 3 → Kˣ := ![ζ, ζ, ζ⁻¹ ^ 2] with hd_def
  have hdprod : d 0 * d 1 * d 2 = 1 := by
    show ζ * ζ * ζ⁻¹ ^ 2 = 1
    rw [← pow_two, ← mul_pow, mul_inv_cancel, one_pow]
  have hdq : ∀ i, d i ^ (2 ^ f + 1) = 1 := by
    intro i
    fin_cases i
    · exact hζq
    · exact hζq
    · show (ζ⁻¹ ^ 2) ^ (2 ^ f + 1) = 1
      rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζq, inv_one, one_pow]
  set x : StatedSU 3 (2 ^ f) K := ⟨torusDiag d, burnsideTA12_diag_mem hq hdprod hdq⟩ with hx_def
  have hxs : x ^ s = 1 := Subtype.ext (by
    change (torusDiag d : GL (Fin 3) K) ^ s = 1
    rw [← map_pow, ← map_one (torusDiag (K := K) (ι := Fin 3))]
    congr 1
    funext i
    fin_cases i
    · exact hζs
    · exact hζs
    · show (ζ⁻¹ ^ 2) ^ s = 1
      rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζs, inv_one, one_pow])
  have hx1 : x ≠ 1 := fun h => by
    have h1 : (torusDiag d : GL (Fin 3) K) = 1 := congrArg Subtype.val h
    rw [← map_one (torusDiag (K := K) (ι := Fin 3))] at h1
    exact hζ1 (congrFun (torusDiag_injective h1) 0)
  haveI : Fact s.Prime := ⟨hs⟩
  have hxord : orderOf x = s := orderOf_eq_prime hxs hx1
  set t : StatedSU 3 (2 ^ f) K := ⟨swapGL (K := K) (by norm_num), swapGL_mem_statedSU hU _⟩
    with ht_def
  have ht2 : t ^ 2 = 1 := Subtype.ext (Units.ext (by
    rw [pow_two]
    change (1 + swapBlock 3 K) * (1 + swapBlock 3 K) = 1
    exact one_add_mul_one_add (swapBlock_mul_self (by norm_num))))
  have ht1 : t ≠ 1 := fun h => by
    have h1 := congrArg (fun y : StatedSU 3 (2 ^ f) K =>
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
    have h01 := congrFun (congrFun h1 0) 1
    simp [t, coe_swapGL, swapBlock] at h01
  have hd01 : ∀ i j : Fin 3, i.val < 2 → j.val < 2 → ((d i : Kˣ) : K) = ((d j : Kˣ) : K) := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;> simp_all [d]
  have hxt : x * t = t * x := Subtype.ext (Units.ext (by
    change (torusDiag d : Matrix (Fin 3) (Fin 3) K) * (1 + swapBlock 3 K) =
      (1 + swapBlock 3 K) * (torusDiag d : Matrix (Fin 3) (Fin 3) K)
    rw [coe_torusDiag]
    exact diagonal_mul_swap hd01))
  refine ⟨⟨x, t, hxord, ht2, ht1, hxt⟩, ?_⟩
  set d' : Fin 3 → Kˣ := ![ζ, ζ⁻¹, 1] with hd'_def
  have hd'prod : d' 0 * d' 1 * d' 2 = 1 := by
    show ζ * ζ⁻¹ * 1 = 1
    rw [mul_inv_cancel, one_mul]
  have hd'q : ∀ i, d' i ^ (2 ^ f + 1) = 1 := by
    intro i
    fin_cases i
    · exact hζq
    · show ζ⁻¹ ^ (2 ^ f + 1) = 1
      rw [inv_pow, hζq, inv_one]
    · exact one_pow _
  set x' : StatedSU 3 (2 ^ f) K := ⟨torusDiag d', burnsideTA12_diag_mem hq hd'prod hd'q⟩
    with hx'_def
  have hx's : x' ^ s = 1 := Subtype.ext (by
    change (torusDiag d' : GL (Fin 3) K) ^ s = 1
    rw [← map_pow, ← map_one (torusDiag (K := K) (ι := Fin 3))]
    congr 1
    funext i
    fin_cases i
    · exact hζs
    · show ζ⁻¹ ^ s = 1
      rw [inv_pow, hζs, inv_one]
    · exact one_pow _)
  have hcomm : ∀ g ∈ zpowers x, Commute x' g := by
    intro g hg
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (show Commute x' x from Subtype.ext (by
      change (torusDiag d' : GL (Fin 3) K) * torusDiag d = torusDiag d * torusDiag d'
      rw [← map_mul, ← map_mul, mul_comm])).zpow_right m
  have hx'n : x' ∉ zpowers x := fun h => by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h
    have h1 : ((x ^ m : StatedSU 3 (2 ^ f) K) : GL (Fin 3) K) = (x' : GL (Fin 3) K) :=
      congrArg Subtype.val hm
    have h2 : torusDiag (d ^ m) = torusDiag d' := by
      rw [map_zpow]
      exact h1
    have h3 := torusDiag_injective h2
    have e0 := congrFun h3 0
    have e1 := congrFun h3 1
    simp only [Pi.pow_apply, hd_def, hd'_def, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at e0 e1
    apply hζ2
    have : ζ = ζ⁻¹ := e0.symm.trans e1
    rw [pow_two]
    calc ζ * ζ = ζ * ζ⁻¹⁻¹ := by rw [inv_inv]
      _ = ζ * ζ⁻¹⁻¹ := rfl
      _ = 1 := by rw [← this, mul_inv_cancel]
  have hxel : CFSG.Open.IsElemAbelian s (zpowers x) := CFSG.Open.isElemAbelian_zpowers hxs
  obtain ⟨F, hF, hFc, -⟩ := CFSG.SectionRank.QTK.CoverB.exists_elemAbelian_sup hs (k := 1) hxel
    (by rw [Nat.card_zpowers, hxord, pow_one]) hx's hcomm hx'n
    (K := ⊤) (Subgroup.mem_top _) le_top
  exact ⟨F, hF, hFc⟩

open CFSG.SectionRank.ClassicalEven CFSG.RankThree.PartTwo.Census Matrix in
private theorem burnsideTA12_su3_data9 {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (h9 : 9 ∣ 2 ^ f + 1) :
    ∃ x t e : StatedSU 3 (2 ^ f) K, t ^ 2 = 1 ∧ t ≠ 1 ∧ Commute x t ∧ Commute x e ∧
      e ^ 3 = 1 ∧ x ^ 3 ∈ Subgroup.center (StatedSU 3 (2 ^ f) K) ∧ x ^ 3 ≠ 1 ∧
      e ∉ zpowers (x ^ 3) := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : CharP K 2 := hU.charP
  have hq : (2 ^ f : ℕ) ≠ 0 := by positivity
  obtain ⟨ζ, hζ, hζq⟩ := burnsideTA12_exists_zeta hK h9
  have hζ9 : ζ ^ 9 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ3 : ζ ^ 3 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at this
    omega
  set d : Fin 3 → Kˣ := ![ζ, ζ, ζ⁻¹ ^ 2] with hd_def
  have hdprod : d 0 * d 1 * d 2 = 1 := by
    show ζ * ζ * ζ⁻¹ ^ 2 = 1
    rw [← pow_two, ← mul_pow, mul_inv_cancel, one_pow]
  have hdq : ∀ i, d i ^ (2 ^ f + 1) = 1 := by
    intro i
    fin_cases i
    · exact hζq
    · exact hζq
    · show (ζ⁻¹ ^ 2) ^ (2 ^ f + 1) = 1
      rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζq, inv_one, one_pow]
  set d' : Fin 3 → Kˣ := ![1, ζ ^ 3, (ζ ^ 3)⁻¹] with hd'_def
  have hd'prod : d' 0 * d' 1 * d' 2 = 1 := by
    show 1 * ζ ^ 3 * (ζ ^ 3)⁻¹ = 1
    rw [one_mul, mul_inv_cancel]
  have hd'q : ∀ i, d' i ^ (2 ^ f + 1) = 1 := by
    intro i
    fin_cases i
    · exact one_pow _
    · show (ζ ^ 3) ^ (2 ^ f + 1) = 1
      rw [← pow_mul, mul_comm, pow_mul, hζq, one_pow]
    · show ((ζ ^ 3)⁻¹) ^ (2 ^ f + 1) = 1
      rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hζq, one_pow, inv_one]
  have hd'3 : d' ^ 3 = 1 := by
    funext i
    fin_cases i
    · exact one_pow _
    · show (ζ ^ 3) ^ 3 = 1
      rw [← pow_mul]; exact hζ9
    · show ((ζ ^ 3)⁻¹) ^ 3 = 1
      rw [inv_pow, ← pow_mul, show 3 * 3 = 9 from rfl, hζ9, inv_one]
  have hinv : ((ζ ^ 2) ^ 3)⁻¹ = ζ ^ 3 := by
    rw [← pow_mul]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact hζ9)
  have hd3 : d ^ 3 = fun _ => ζ ^ 3 := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · show (ζ⁻¹ ^ 2) ^ 3 = ζ ^ 3
      rw [inv_pow, ← hinv]
      simp
  set x : StatedSU 3 (2 ^ f) K := ⟨torusDiag d, burnsideTA12_diag_mem hq hdprod hdq⟩ with hx_def
  set e : StatedSU 3 (2 ^ f) K := ⟨torusDiag d', burnsideTA12_diag_mem hq hd'prod hd'q⟩
    with he_def
  set t : StatedSU 3 (2 ^ f) K := ⟨swapGL (K := K) (by norm_num), swapGL_mem_statedSU hU _⟩
    with ht_def
  have hd01 : ∀ i j : Fin 3, i.val < 2 → j.val < 2 → ((d i : Kˣ) : K) = ((d j : Kˣ) : K) := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;> simp_all [d]
  have hxt : x * t = t * x := Subtype.ext (Units.ext (by
    change (torusDiag d : Matrix (Fin 3) (Fin 3) K) * (1 + swapBlock 3 K) =
      (1 + swapBlock 3 K) * (torusDiag d : Matrix (Fin 3) (Fin 3) K)
    rw [coe_torusDiag]
    exact diagonal_mul_swap hd01))
  have ht2 : t ^ 2 = 1 := Subtype.ext (Units.ext (by
    rw [pow_two]
    change (1 + swapBlock 3 K) * (1 + swapBlock 3 K) = 1
    exact one_add_mul_one_add (swapBlock_mul_self (by norm_num))))
  set T := (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ f) K) with hT
  have hx3 : x ^ 3 ∈ T := by
    rw [Subgroup.mem_subgroupOf]
    refine ⟨ζ ^ 3, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    change Matrix.scalar (Fin 3) ((ζ ^ 3 : Kˣ) : K) =
      ((torusDiag d ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [← map_pow, hd3, coe_torusDiag]
    rfl
  have hscal : ∀ y : StatedSU 3 (2 ^ f) K, y ∈ T →
      ∃ c : K, ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c :=
    fun y hy => by
      obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hy
      exact ⟨c, by rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]⟩
  have htT : t ∉ T := fun h => by
    obtain ⟨c, hc⟩ := hscal t h
    change 1 + swapBlock 3 K = _ at hc
    have h01 := congrFun (congrFun hc 0) 1
    simp [swapBlock, Matrix.scalar_apply] at h01
  have heT : e ∉ T := fun h => by
    obtain ⟨c, hc⟩ := hscal e h
    change (torusDiag d' : Matrix (Fin 3) (Fin 3) K) = _ at hc
    rw [coe_torusDiag] at hc
    have h0 := congrFun (congrFun hc 0) 0
    have h1 := congrFun (congrFun hc 1) 1
    simp only [diagonal_apply_eq, Matrix.scalar_apply] at h0 h1
    apply hζ3
    apply Units.ext
    simpa [hd'_def] using h1.trans h0.symm
  refine ⟨x, t, e, ht2, fun h => htT (h ▸ T.one_mem), hxt, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext (Units.ext (by
      change (torusDiag d : Matrix (Fin 3) (Fin 3) K) * torusDiag d' =
        (torusDiag d' : Matrix (Fin 3) (Fin 3) K) * torusDiag d
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_comm]))
  · refine Subtype.ext (Units.ext ?_)
    change ((torusDiag d' ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [← map_pow, hd'3, map_one]
    rfl
  · exact CFSG.LieType.Universal.Unitary.statedScalars_subgroupOf_le_center 3 (2 ^ f) hx3
  · intro h
    have h1 := congrArg (fun y : StatedSU 3 (2 ^ f) K => (y : GL (Fin 3) K)) h
    change torusDiag d ^ 3 = 1 at h1
    rw [← map_pow, ← map_one (torusDiag (K := K) (ι := Fin 3))] at h1
    have h2 := congrFun (torusDiag_injective h1) 0
    rw [hd3] at h2
    exact hζ3 h2
  · intro h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
    apply heT
    rw [← hm]
    exact T.zpow_mem hx3 m

private theorem burnsideTA12_center_pow_three {Y : Type} [Group Y] (hZ : Nat.card (center Y) = 3)
    {z : Y} (hz : z ∈ center Y) : z ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := ↥(center Y)) (x := ⟨z, hz⟩)
  rw [hZ] at h
  simpa using congrArg Subtype.val h

private theorem burnsideTA12_gcd_cond (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) (hZ₁ : Nat.card (center ↥L₁) = 3) {f₁ f₂ : ℕ}
    (h₁ : IsSUn 3 (2 ^ f₁) ↥L₁) (h₂ : IsSUn 3 (2 ^ f₂) ↥L₂) (hf₁ : 3 ≤ f₁) (ho₁ : Odd f₁)
    (hf₂ : 3 ≤ f₂) (ho₂ : Odd f₂) : Nat.gcd f₁ f₂ = 1 ∨ Nat.gcd f₁ f₂ = 3 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hd1, hd3⟩ := hcon
  have hdf₁ : Nat.gcd f₁ f₂ ∣ f₁ := Nat.gcd_dvd_left _ _
  have hdf₂ : Nat.gcd f₁ f₂ ∣ f₂ := Nat.gcd_dvd_right _ _
  have hdodd : Odd (Nat.gcd f₁ f₂) := ho₁.of_dvd_nat hdf₁
  have hd0 : Nat.gcd f₁ f₂ ≠ 0 := fun h => by rw [h] at hdodd; exact absurd hdodd (by decide)
  have hd2 : 2 ≤ Nat.gcd f₁ f₂ := by omega
  obtain ⟨s, hs, hsd, hs3⟩ := CFSG.Quasithin.A3Facts.exists_prime_dvd_two_pow_add_one hd2 hd3
  have hs2 : s ≠ 2 := by
    rintro rfl
    have h2d : 2 ∣ 2 ^ Nat.gcd f₁ f₂ := dvd_pow_self 2 hd0
    have : 2 ∣ 1 := (Nat.dvd_add_right h2d).1 hsd
    omega
  have hsf : ∀ {f : ℕ}, Odd f → Nat.gcd f₁ f₂ ∣ f → s ∣ 2 ^ f + 1 := by
    intro f hf hdf
    obtain ⟨m, hm⟩ := hdf
    have hmodd : Odd m := by
      rw [hm] at hf
      exact (Nat.odd_mul.1 hf).2
    have := Odd.nat_add_dvd_pow_add_pow (2 ^ Nat.gcd f₁ f₂) 1 hmodd
    rw [one_pow, ← pow_mul, ← hm] at this
    exact hsd.trans this
  have hsf₁ := hsf ho₁ hdf₁
  have hsf₂ := hsf ho₂ hdf₂
  obtain ⟨K₁, _, _, hK₁, ⟨φ₁⟩⟩ := h₁
  obtain ⟨K₂, _, _, hK₂, ⟨φ₂⟩⟩ := h₂
  obtain ⟨⟨x, t, hxo, ht2, ht1, hxt⟩, -⟩ :=
    burnsideTA12_su3_witness_s (by omega) hK₁ hs hs2 hsf₁
  obtain ⟨-, E, hE, hEc⟩ := burnsideTA12_su3_witness_s (by omega) hK₂ hs hs2 hsf₂
  set ι₁ : StatedSU 3 (2 ^ f₁) K₁ →* H := L₁.subtype.comp φ₁.symm.toMonoidHom with hι₁
  set ι₂ : StatedSU 3 (2 ^ f₂) K₂ →* H := L₂.subtype.comp φ₂.symm.toMonoidHom with hι₂
  have hι₁i : Function.Injective ι₁ := L₁.subtype_injective.comp φ₁.symm.injective
  have hι₂i : Function.Injective ι₂ := L₂.subtype_injective.comp φ₂.symm.injective
  have hι₁L : ∀ g, ι₁ g ∈ L₁ := fun g => (φ₁.symm g).2
  have hι₂L : ∀ g, ι₂ g ∈ L₂ := fun g => (φ₂.symm g).2
  have hxs : (ι₁ x) ^ s = 1 := by
    rw [← map_pow, ← hxo, pow_orderOf_eq_one, map_one]
  refine burnsideTA12_false_of_extra_element he hc hs hs2 (t := ι₁ t) (hι₁L t)
    (by rw [← map_pow, ht2, map_one]) (fun h => ht1 (hι₁i (by rw [h, map_one])))
    (F₂ := E.map ι₂) (CFSG.SectionRank.isElemAbelian_map hE ι₂)
    (by rw [Subgroup.card_map_of_injective hι₂i, hEc]) ?_ hxs ?_ ?_ ?_
  · rintro _ ⟨g, -, rfl⟩
    exact hι₂L g
  · intro hxL
    have hw : φ₁.symm x ∈ center ↥L₁ :=
      mem_center_of_mem_commuting hc (y := φ₁.symm x) hxL
    have h3 : (φ₁.symm x) ^ 3 = 1 := burnsideTA12_center_pow_three hZ₁ hw
    have hord : orderOf (φ₁.symm x) = s := by rw [MulEquiv.orderOf_eq, hxo]
    have : s ∣ 3 := hord ▸ orderOf_dvd_of_pow_eq_one h3
    exact hs3 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).1 this)
  · exact hxt.map ι₁
  · rintro _ ⟨g, -, rfl⟩
    exact hc _ (hι₁L x) _ (hι₂L g)

private theorem burnsideTA12_false_of_pair_data (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) (hZ₁ : Nat.card (center ↥L₁) = 3)
    (hZ₂ : Nat.card (center ↥L₂) = 3)
    (hZeq : (center ↥L₁).map L₁.subtype = (center ↥L₂).map L₂.subtype)
    {x₁ t₁ : ↥L₁} (ht2 : t₁ ^ 2 = 1) (ht1 : t₁ ≠ 1) (hxt : Commute x₁ t₁)
    (hx₁c : x₁ ^ 3 ∈ center ↥L₁) (hx₁3 : x₁ ^ 3 ≠ 1) {x₂ e₂ : ↥L₂} (hxe : Commute x₂ e₂)
    (he3 : e₂ ^ 3 = 1) (hx₂c : x₂ ^ 3 ∈ center ↥L₂) (hx₂3 : x₂ ^ 3 ≠ 1)
    (hexω : e₂ ∉ zpowers (x₂ ^ 3)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hω3 : (x₂ ^ 3) ^ 3 = 1 := burnsideTA12_center_pow_three hZ₂ hx₂c
  have hωord : orderOf (x₂ ^ 3) = 3 := orderOf_eq_prime hω3 hx₂3
  have hZgen : center ↥L₂ = zpowers (x₂ ^ 3) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hx₂c) ?_
    rw [Nat.card_zpowers, hωord, hZ₂]
  obtain ⟨F₀, hF₀, hF₀c, hF₀K⟩ := exists_elemAbelian_sup Nat.prime_three (k := 1)
    (CFSG.Open.isElemAbelian_zpowers hω3) (by rw [Nat.card_zpowers, hωord, pow_one]) he3
    (fun g hg => by
      have hgz : g ∈ center ↥L₂ := by rw [hZgen]; exact hg
      exact Subgroup.mem_center_iff.mp hgz e₂)
    hexω (K := centralizer ({x₂} : Set ↥L₂))
    (Subgroup.mem_centralizer_singleton_iff.2 hxe.eq.symm)
    (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 ((Commute.refl x₂).pow_left 3).eq))
  set F₂ : Subgroup H := F₀.map L₂.subtype with hF₂def
  have hF₂ : CFSG.Open.IsElemAbelian 3 F₂ := CFSG.SectionRank.isElemAbelian_map hF₀ L₂.subtype
  have hF₂c : Nat.card F₂ = 3 ^ 2 := by
    rw [hF₂def, Subgroup.card_map_of_injective L₂.subtype_injective, hF₀c]
  have hF₂L : F₂ ≤ L₂ := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  have hF₂x : ∀ g ∈ F₂, Commute g (x₂ : H) := by
    rintro _ ⟨g, hg, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hF₀K hg)
    show (g : H) * x₂ = x₂ * g
    exact congrArg Subtype.val h
  have hωH : ((x₁ ^ 3 : ↥L₁) : H) ∈ (center ↥L₂).map L₂.subtype := by
    rw [← hZeq]
    exact ⟨_, hx₁c, rfl⟩
  obtain ⟨z, hz, hzω⟩ := hωH
  rw [hZgen] at hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hk' : (x₂ : H) ^ (3 * k) = ((x₁ ^ 3 : ↥L₁) : H) := by
    have h1 : ((x₂ ^ 3) ^ k : ↥L₂) = z := hk
    rw [zpow_mul, zpow_ofNat]
    rw [← hzω, ← h1]
    simp
  have hxx₂ : Commute (x₁ : H) (x₂ : H) := hc _ x₁.2 _ x₂.2
  set y : H := (x₁ : H) * (x₂ : H) ^ (-k) with hy
  have hy3 : y ^ 3 = 1 := by
    rw [hy, (hxx₂.zpow_right (-k)).mul_pow]
    have h3 : ((x₂ : H) ^ (-k)) ^ 3 = ((x₂ : H) ^ (3 * k))⁻¹ := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]
      congr 1
      push_cast
      ring
    rw [h3, hk', ← SubgroupClass.coe_pow]
    exact mul_inv_cancel _
  have hyL : y ∉ L₂ := by
    intro hy2
    have hxL₂ : (x₁ : H) ∈ L₂ := by
      have h4 : (x₁ : H) = y * (x₂ : H) ^ k := by
        rw [hy, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
      rw [h4]
      exact L₂.mul_mem hy2 (L₂.zpow_mem x₂.2 k)
    have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, Commute a b := fun a ha b hb => (hc b hb a ha).symm
    have hw : (⟨(x₁ : H), hxL₂⟩ : ↥L₂) ∈ center ↥L₂ := mem_center_of_mem_commuting hc' x₁.2
    have hw' : x₁ ∈ center ↥L₁ := mem_center_of_mem_commuting hc (y := x₁) hxL₂
    exact hx₁3 (by
      have := burnsideTA12_center_pow_three hZ₁ hw'
      exact this)
  have ht2H : (t₁ : H) ^ 2 = 1 := by rw [← SubgroupClass.coe_pow, ht2]; rfl
  have ht1H : (t₁ : H) ≠ 1 := fun h => ht1 (Subtype.ext (by simpa using h))
  have hyt : Commute y (t₁ : H) :=
    Commute.mul_left (congrArg Subtype.val hxt.eq)
      ((hc _ t₁.2 _ x₂.2).symm.zpow_left (-k))
  have hyF : ∀ g ∈ F₂, Commute y g := fun g hg =>
    Commute.mul_left (hc _ x₁.2 g (hF₂L hg)) ((hF₂x g hg).symm.zpow_left (-k))
  exact burnsideTA12_false_of_extra_element he hc Nat.prime_three (by norm_num) t₁.2 ht2H ht1H
    hF₂ hF₂c hF₂L hy3 hyL hyt hyF

private theorem burnsideTA12_center_symm {A B : Type} [Group A] [Group B] (φ : A ≃* B) {z : B}
    (hz : z ∈ center B) : φ.symm z ∈ center A := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  apply φ.injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
  exact hz (φ g)

private theorem burnsideTA12_false_of_both_nine (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) (hZ₁ : Nat.card (center ↥L₁) = 3)
    (hZ₂ : Nat.card (center ↥L₂) = 3)
    (hZeq : (center ↥L₁).map L₁.subtype = (center ↥L₂).map L₂.subtype) {f₁ f₂ : ℕ}
    (h₁ : IsSUn 3 (2 ^ f₁) ↥L₁) (h₂ : IsSUn 3 (2 ^ f₂) ↥L₂) (hf₁ : 1 ≤ f₁) (hf₂ : 1 ≤ f₂)
    (h9₁ : 9 ∣ 2 ^ f₁ + 1) (h9₂ : 9 ∣ 2 ^ f₂ + 1) : False := by
  obtain ⟨K₁, _, _, hK₁, ⟨φ₁⟩⟩ := h₁
  obtain ⟨K₂, _, _, hK₂, ⟨φ₂⟩⟩ := h₂
  obtain ⟨x, t, e, ht2, ht1, hxt, -, -, hx3c, hx3, -⟩ := burnsideTA12_su3_data9 hf₁ hK₁ h9₁
  obtain ⟨x', t', e', -, -, -, hxe', he3', hx3c', hx3', hex'⟩ :=
    burnsideTA12_su3_data9 hf₂ hK₂ h9₂
  refine burnsideTA12_false_of_pair_data he hc hZ₁ hZ₂ hZeq (x₁ := φ₁.symm x) (t₁ := φ₁.symm t)
    (by rw [← map_pow, ht2, map_one]) (fun h => ht1 (φ₁.symm.injective (by rw [h, map_one])))
    (hxt.map φ₁.symm) ?_ ?_ (x₂ := φ₂.symm x') (e₂ := φ₂.symm e') (hxe'.map φ₂.symm)
    (by rw [← map_pow, he3', map_one]) ?_ ?_ ?_
  · rw [← map_pow]
    exact burnsideTA12_center_symm φ₁ hx3c
  · rw [← map_pow]
    exact fun h => hx3 (φ₁.symm.injective (by rw [h, map_one]))
  · rw [← map_pow]
    exact burnsideTA12_center_symm φ₂ hx3c'
  · rw [← map_pow]
    exact fun h => hx3' (φ₂.symm.injective (by rw [h, map_one]))
  · intro h
    apply hex'
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h
    refine Subgroup.mem_zpowers_iff.2 ⟨m, φ₂.symm.injective ?_⟩
    rw [map_zpow, map_pow, hm]

private theorem burnsideTA12_mem_sup_of_commute {A B : Subgroup H}
    (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b) {x : H} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [← Subgroup.closure_eq A, ← Subgroup.closure_eq B, ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, (mul_one y).symm⟩
    · exact ⟨1, A.one_mem, y, hy, (one_mul y).symm⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    obtain ⟨a', ha', b', hb', rfl⟩ := hz
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    have hba : b * a' = a' * b := (hc a' ha' b hb).eq.symm
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hba]
      _ = a * a' * (b * b') := by group
  | inv y _ hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have hba : b * a = a * b := (hc a ha b hb).eq.symm
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hba]

private theorem burnsideTA12_card_le_of_quotient {H₀ : Subgroup H} (N : Subgroup ↥H₀) [N.Normal]
    {A : Subgroup H} (hA : A ≤ H₀) (hAel : CFSG.Open.IsElemAbelian 3 A) {m : ℕ}
    (hm : ∀ Ē : Subgroup (↥H₀ ⧸ N), CFSG.Open.IsElemAbelian 3 Ē → Nat.card Ē ≤ m) :
    Nat.card A ≤ Nat.card ↥(A ⊓ N.map H₀.subtype) * m := by
  set A'' : Subgroup ↥H₀ := A.subgroupOf H₀ with hA''
  set f : ↥A'' →* ↥H₀ ⧸ N := (QuotientGroup.mk' N).comp A''.subtype with hf
  have h1 : Nat.card ↥A'' = Nat.card A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have h2 := Subgroup.card_ker_mul_card_range f
  have hrange : f.range = A''.map (QuotientGroup.mk' N) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hel : CFSG.Open.IsElemAbelian 3 (A''.map (QuotientGroup.mk' N)) :=
    (hAel.subgroupOf H₀).map _
  have h3 : Nat.card f.range ≤ m := by rw [hrange]; exact hm _ hel
  have h4 : Nat.card f.ker ≤ Nat.card ↥(A ⊓ N.map H₀.subtype) := by
    refine Nat.card_le_card_of_injective
      (fun a : ↥f.ker => (⟨a.1.1.1, ?_⟩ : ↥(A ⊓ N.map H₀.subtype))) ?_
    · refine Subgroup.mem_inf.2 ⟨a.1.2, ?_⟩
      have ha : (QuotientGroup.mk' N) a.1.1 = 1 := a.2
      exact ⟨_, (QuotientGroup.eq_one_iff _).1 ha, rfl⟩
    · intro a b hab
      have h' : a.1.1.1 = b.1.1.1 := Subtype.mk.inj hab
      exact Subtype.ext (Subtype.ext (Subtype.ext h'))
  calc Nat.card A = Nat.card ↥A'' := h1.symm
    _ = Nat.card f.ker * Nat.card f.range := h2.symm
    _ ≤ Nat.card ↥(A ⊓ N.map H₀.subtype) * m := Nat.mul_le_mul h4 h3

private theorem burnsideTA12_rank_sup_le {L₁ L₂ : Subgroup H} (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b)
    [hN : (L₂.subgroupOf (L₁ ⊔ L₂)).Normal] {Z : Subgroup H} (hZ : Nat.card Z = 3)
    (hZ₁ : Z ≤ L₁) (hZ₂ : Z ≤ L₂) (hinf : ∀ x ∈ L₁, x ∈ L₂ → x ∈ Z)
    (hi₁ : ∀ E : Subgroup H, CFSG.Open.IsElemAbelian 3 E → E ≤ L₁ → Nat.card E ≤ 9)
    (hi₂ : ∀ E : Subgroup H, CFSG.Open.IsElemAbelian 3 E → E ≤ L₂ → Nat.card E ≤ 9)
    (hii : ∀ Ē : Subgroup (↥(L₁ ⊔ L₂) ⧸ L₂.subgroupOf (L₁ ⊔ L₂)),
      CFSG.Open.IsElemAbelian 3 Ē → Nat.card Ē ≤ 9)
    (hiii : ∀ v ∈ L₂, v ^ 3 ∈ Z → v ^ 3 = 1) {A : Subgroup H} (hA : A ≤ L₁ ⊔ L₂)
    (hAel : CFSG.Open.IsElemAbelian 3 A) : Nat.card A ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hgt
  push Not at hgt
  have hZel : CFSG.Open.IsElemAbelian 3 Z := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · exact (hc _ (hZ₁ x.2) _ (hZ₂ y.2)).eq
    · have h := pow_card_eq_one' (G := ↥Z) (x := ⟨x, hx⟩)
      rw [hZ] at h
      simpa using congrArg Subtype.val h
  have hZc : ∀ z ∈ Z, ∀ x ∈ L₁ ⊔ L₂, z * x = x * z := by
    intro z hz x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := burnsideTA12_mem_sup_of_commute hc hx
    have h1 : z * u = u * z := (hc u hu z (hZ₂ hz)).eq.symm
    have h2 : z * v = v * z := (hc z (hZ₁ hz) v hv).eq
    calc z * (u * v) = (z * u) * v := by group
      _ = u * (z * v) := by rw [h1]; group
      _ = u * (v * z) := by rw [h2]
      _ = u * v * z := by group
  set A' : Subgroup H := A ⊔ Z with hA'
  have hA'el : CFSG.Open.IsElemAbelian 3 A' :=
    CFSG.Open.IsElemAbelian.sup_of_commute hAel hZel fun a ha z hz => (hZc z hz a (hA ha)).symm
  have hA'H : A' ≤ L₁ ⊔ L₂ := sup_le hA (hZ₁.trans le_sup_left)
  have hAA' : A ≤ A' := le_sup_left
  have hZA' : Z ≤ A' := le_sup_right
  have h81 : 81 ≤ Nat.card A' := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.Open.IsElemAbelian.isPGroup hA'el)
    have h27 : 27 < Nat.card A' := lt_of_lt_of_le hgt (Subgroup.card_le_of_le hAA')
    by_contra hlt
    have hk3 : k ≤ 3 := by
      by_contra h4
      push Not at h4
      have : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h4
      omega
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    omega
  set E₂ : Subgroup H := A' ⊓ L₂ with hE₂
  set E₁ : Subgroup H := A' ⊓ L₁ with hE₁
  have hE₂el : CFSG.Open.IsElemAbelian 3 E₂ := CFSG.Open.IsElemAbelian.mono hA'el inf_le_left
  have hE₁el : CFSG.Open.IsElemAbelian 3 E₁ := CFSG.Open.IsElemAbelian.mono hA'el inf_le_left
  have hZE₁ : Z ≤ E₁ := le_inf hZA' hZ₁
  have hZE₂ : Z ≤ E₂ := le_inf hZA' hZ₂
  have h9₁ : Nat.card E₁ ≤ 9 := hi₁ E₁ hE₁el inf_le_right
  have h9₂ : Nat.card E₂ ≤ 9 := hi₂ E₂ hE₂el inf_le_right
  have hcount := burnsideTA12_card_le_of_quotient (L₂.subgroupOf (L₁ ⊔ L₂)) hA'H hA'el hii
  have hmap : (L₂.subgroupOf (L₁ ⊔ L₂)).map (L₁ ⊔ L₂).subtype = L₂ :=
    Subgroup.map_subgroupOf_eq_of_le le_sup_right
  rw [hmap] at hcount
  have hE₂c : Nat.card E₂ = 3 ^ 2 := by
    have h9 : 9 ≤ Nat.card E₂ := by
      by_contra hlt
      push Not at hlt
      have : Nat.card A' ≤ Nat.card E₂ * 9 := hcount
      omega
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (CFSG.Open.IsElemAbelian.isPGroup hE₂el)
    have hj2 : j = 2 := by
      have h9' : 3 ^ j = 9 := by omega
      have : 3 ^ j = 3 ^ 2 := by rw [h9']; norm_num
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) this
    rw [hj, hj2]
  have hfac : ∀ a ∈ A', ∃ u ∈ E₁, ∃ v ∈ E₂, a = u * v := by
    intro a ha
    obtain ⟨u, hu, v, hv, rfl⟩ := burnsideTA12_mem_sup_of_commute hc (hA'H ha)
    have hcomm_v : ∀ e ∈ E₂, Commute v e := by
      intro e he
      have h1 : u * v * e = e * (u * v) :=
        CFSG.Open.IsElemAbelian.comm hA'el ha (Subgroup.mem_inf.1 he).1
      have h2 : e * u = u * e := (hc u hu e (Subgroup.mem_inf.1 he).2).eq.symm
      have h3 : u * (v * e) = u * (e * v) := by
        calc u * (v * e) = u * v * e := by group
          _ = e * (u * v) := h1
          _ = (e * u) * v := by group
          _ = (u * e) * v := by rw [h2]
          _ = u * (e * v) := by group
      exact mul_left_cancel h3
    have hv3 : v ^ 3 = 1 := by
      apply hiii v hv
      have h3 : (u * v) ^ 3 = 1 := hA'el.2 _ ha
      have huv : u * v = v * u := (hc u hu v hv).eq
      rw [(hc u hu v hv).mul_pow] at h3
      have h4 : v ^ 3 = (u ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h3
      exact hinf _ (h4 ▸ L₁.inv_mem (L₁.pow_mem hu 3)) (L₂.pow_mem hv 3)
    have hvE₂ : v ∈ E₂ := by
      by_contra hvn
      obtain ⟨F, hF, hFc, hFL⟩ := CFSG.SectionRank.QTK.CoverB.exists_elemAbelian_sup
        Nat.prime_three (k := 2) hE₂el hE₂c hv3 hcomm_v hvn (K := L₂) hv inf_le_right
      have := hi₂ F hF hFL
      rw [hFc] at this
      omega
    have huA : u ∈ A' := by
      have h1 : u = (u * v) * v⁻¹ := by group
      rw [h1]
      exact A'.mul_mem ha (A'.inv_mem (Subgroup.mem_inf.1 hvE₂).1)
    exact ⟨u, ⟨huA, hu⟩, v, hvE₂, rfl⟩
  let Ψ : ↥E₁ × ↥E₂ →* H := MonoidHom.noncommCoprod E₁.subtype E₂.subtype
    (fun x y => hc _ (Subgroup.mem_inf.1 x.2).2 _ (Subgroup.mem_inf.1 y.2).2)
  have hAΨ : A' ≤ Ψ.range := by
    intro a ha
    obtain ⟨u, hu, v, hv, rfl⟩ := hfac a ha
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
  have hker : 3 ≤ Nat.card Ψ.ker := by
    rw [← hZ]
    refine Nat.card_le_card_of_injective
      (fun z : ↥Z => (⟨(⟨(z : H), hZE₁ z.2⟩, ⟨(z : H)⁻¹, Z.inv_mem z.2 |> hZE₂⟩), ?_⟩ : ↥Ψ.ker)) ?_
    · change (z : H) * (z : H)⁻¹ = 1
      exact mul_inv_cancel _
    · intro x y hxy
      have h' := congrArg (fun w : ↥Ψ.ker => ((w.1.1 : ↥E₁) : H)) hxy
      exact Subtype.ext h'
  have hmul := Subgroup.card_ker_mul_card_range Ψ
  have hprod : Nat.card (↥E₁ × ↥E₂) = Nat.card E₁ * Nat.card E₂ := Nat.card_prod _ _
  have hAr : Nat.card A' ≤ Nat.card Ψ.range := Subgroup.card_le_of_le hAΨ
  have hbound : 3 * Nat.card A' ≤ Nat.card Ψ.ker * Nat.card Ψ.range :=
    Nat.mul_le_mul hker hAr
  rw [hmul, hprod] at hbound
  have : Nat.card E₁ * Nat.card E₂ ≤ 9 * 9 := Nat.mul_le_mul h9₁ h9₂
  omega

open Polynomial in
private theorem burnsideTA12_cube_root_of_det_one {K : Type} [Field K] (M : Matrix (Fin 3) (Fin 3) K)
    (hdet : M.det = 1) {c : K} (hc1 : c ≠ 1) (hM : M ^ 3 = Matrix.scalar (Fin 3) c) :
    ∃ a : K, a ^ 3 = c := by
  by_contra hno
  push Not at hno
  set P : K[X] := X ^ 3 - C c with hP
  have hPmonic : P.Monic := Polynomial.monic_X_pow_sub_C c (by norm_num)
  have hPdeg : P.natDegree = 3 := Polynomial.natDegree_X_pow_sub_C
  have hPirr : Irreducible P := by
    rw [hPmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    refine Multiset.eq_zero_of_forall_notMem fun a ha => ?_
    rw [Polynomial.mem_roots hPmonic.ne_zero, Polynomial.IsRoot, hP] at ha
    simp only [eval_sub, eval_pow, eval_X, eval_C] at ha
    exact hno a (sub_eq_zero.1 ha)
  set χ : K[X] := M.charpoly with hχ
  have hχmon : χ.Monic := Matrix.charpoly_monic M
  have hχdeg : χ.natDegree = 3 := by
    have h := Matrix.charpoly_natDegree_eq_dim M
    rw [Fintype.card_fin] at h
    exact h
  have hχ0 : χ.coeff 0 = -1 := by
    have h := Matrix.det_eq_sign_charpoly_coeff M
    rw [hdet, Fintype.card_fin] at h
    have h' : (1 : K) = -(χ.coeff 0) := by
      rw [h]; ring
    linear_combination h'
  set pol : K[X] := χ - P with hpol
  have hdeg : pol.natDegree ≤ 2 := by
    have hlt : pol.degree < χ.degree := by
      refine Polynomial.degree_sub_lt ?_ hχmon.ne_zero ?_
      · rw [Polynomial.degree_eq_natDegree hχmon.ne_zero,
          Polynomial.degree_eq_natDegree hPmonic.ne_zero, hχdeg, hPdeg]
      · rw [hχmon.leadingCoeff, hPmonic.leadingCoeff]
    rw [Polynomial.degree_eq_natDegree hχmon.ne_zero, hχdeg] at hlt
    by_cases h0 : pol = 0
    · rw [h0]; simp
    · rw [Polynomial.degree_eq_natDegree h0] at hlt
      have : pol.natDegree < 3 := by exact_mod_cast hlt
      omega
  have hpol0 : pol ≠ 0 := by
    intro h0
    have h1 : pol.coeff 0 = 0 := by rw [h0]; simp
    have h2 : pol.coeff 0 = c - 1 := by
      rw [hpol, Polynomial.coeff_sub, hχ0, hP]
      simp
      ring
    exact hc1 (sub_eq_zero.1 (h2 ▸ h1))
  have hnd : ¬ P ∣ pol := fun hd => by
    have := Polynomial.natDegree_le_of_dvd hd hpol0
    omega
  obtain ⟨a, b, hab⟩ := (hPirr.coprime_iff_not_dvd).2 hnd
  have hscal : (algebraMap K (Matrix (Fin 3) (Fin 3) K)) c = Matrix.scalar (Fin 3) c := by
    ext i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  have hAP : Polynomial.aeval M P = 0 := by
    rw [hP, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hscal, hM, sub_self]
  have hApol : Polynomial.aeval M pol = 0 := by
    rw [hpol, map_sub, hAP, sub_zero, hχ]
    exact Matrix.aeval_self_charpoly M
  have h1 := congrArg (Polynomial.aeval M) hab
  rw [map_add, map_mul, map_mul, hAP, hApol, mul_zero, mul_zero, add_zero, map_one] at h1
  exact zero_ne_one h1

private theorem burnsideTA12_two_pow_odd_mod_three {f : ℕ} (hf : Odd f) : 2 ^ f % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hf
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

private theorem burnsideTA12_no_order_nine {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : q % 3 = 2) (h9 : ¬ 9 ∣ q + 1)
    (M : Matrix (Fin 3) (Fin 3) K) (hdet : M.det = 1) {c : Kˣ} (hc3 : c ^ 3 = 1)
    (hM : M ^ 3 = Matrix.scalar (Fin 3) (c : K)) : c = 1 := by
  by_contra hc1
  have hc1' : (c : K) ≠ 1 := fun h => hc1 (Units.ext h)
  obtain ⟨a, ha⟩ := burnsideTA12_cube_root_of_det_one M hdet hc1' hM
  have ha0 : a ≠ 0 := by
    rintro rfl
    have : (c : K) = 0 := by rw [← ha]; norm_num
    exact c.ne_zero this
  set u : Kˣ := Units.mk0 a ha0 with hu
  have hu3 : u ^ 3 = c := Units.ext (by simpa [hu] using ha)
  have hu9 : u ^ 9 = 1 := by
    rw [show 9 = 3 * 3 from rfl, pow_mul, hu3, hc3]
  have hu3' : u ^ 3 ≠ 1 := by rw [hu3]; exact hc1
  have hord9 : 9 ∣ orderOf u := by
    have h1 : orderOf u ∣ 9 := orderOf_dvd_of_pow_eq_one hu9
    have h2 : ¬ orderOf u ∣ 3 := fun h => hu3' (orderOf_dvd_iff_pow_eq_one.1 h)
    have h3 := Nat.le_of_dvd (by norm_num) h1
    have h4 : 0 < orderOf u := orderOf_pos u
    interval_cases hh : orderOf u <;> simp_all <;> omega
  have hq2 : 2 ≤ q := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hK
  have hdvd : 9 ∣ (q - 1) * (q + 1) := by
    have h1 : orderOf u ∣ Nat.card Kˣ := orderOf_dvd_natCard u
    rw [Nat.card_units, hK, CFSG.Open.StatedCenterThree.sq_sub_one_eq (by omega)] at h1
    exact hord9.trans h1
  have hcop : Nat.Coprime 9 (q - 1) := by
    have h3 : Nat.Coprime 3 (q - 1) := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      omega
    simpa using Nat.Coprime.pow_left 2 h3
  exact h9 (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd)

private theorem burnsideTA12_su3_no_order_nine {K : Type} [Field K] [Finite K] {f : ℕ} (hf : Odd f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (h9 : ¬ 9 ∣ 2 ^ f + 1) {v : StatedSU 3 (2 ^ f) K}
    (hv : v ^ 3 ∈ center ↥(StatedSU 3 (2 ^ f) K)) : v ^ 3 = 1 := by
  rw [burnsideTA12_center_statedSU_eq hK] at hv
  obtain ⟨c, hcv⟩ := Subgroup.mem_subgroupOf.1 hv
  have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSU v.2
  set M : Matrix (Fin 3) (Fin 3) K := ((v : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hMdef
  have hM3 : M ^ 3 = Matrix.scalar (Fin 3) (c : K) := by
    have h1 : (((v ^ 3 : StatedSU 3 (2 ^ f) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        M ^ 3 := by
      rw [hMdef]
      simp [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    rw [← h1, ← hcv, Matrix.GeneralLinearGroup.coe_scalar]
  have hc3 : c ^ 3 = 1 := by
    have h1 : (M ^ 3).det = 1 := by rw [Matrix.det_pow, hdet, one_pow]
    rw [hM3, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h1
    exact Units.ext (by simpa using h1)
  have hc1 : c = 1 :=
    burnsideTA12_no_order_nine hK (burnsideTA12_two_pow_odd_mod_three hf) h9 M hdet hc3 hM3
  refine Subtype.ext ?_
  have h1 : ((v ^ 3 : StatedSU 3 (2 ^ f) K) : GL (Fin 3) K) = 1 := by
    rw [← hcv, hc1, map_one]
  exact h1

private theorem burnsideTA12_card_le_of_pRank_le {X : Type} [Group X] [Finite X] (h : CFSG.pRank 3 X ≤ 2)
    {E : Subgroup X} (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.Open.IsElemAbelian.isPGroup hE)
  have hk2 : k ≤ 2 := by
    have h1 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (le_top : E ≤ ⊤) hE hk
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h1
    omega
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

private theorem burnsideTA12_card_le_of_le_pRank {L : Subgroup H} (h : CFSG.pRank 3 ↥L ≤ 2)
    {E : Subgroup H} (hEL : E ≤ L) (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have h1 := burnsideTA12_card_le_of_pRank_le h (CFSG.Open.IsElemAbelian.subgroupOf hE L)
  have h2 : Nat.card (E.subgroupOf L) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  omega

private theorem burnsideTA12_pRank_le_two_of_isSUn {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (h : IsSUn 3 (2 ^ f) Y) : CFSG.pRank 3 Y ≤ 2 := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  haveI : CharP K 2 := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow Nat.prime_two hK
  have h3K : (3 : K) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K 2 3).1 h'
    omega
  exact burnsideTA12_pRank_three_le_two_of_det h3K
    ((StatedSU 3 (2 ^ f) K).subtype.comp φ.toMonoidHom)
    ((StatedSU 3 (2 ^ f) K).subtype_injective.comp φ.injective)
    (fun x => CFSG.Open.StatedAPI.det_of_mem_statedSU (φ x).2)

private theorem burnsideTA12_normal_subgroupOf_sup {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) : (L₂.subgroupOf (L₁ ⊔ L₂)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨u, hu, v, hv, hg⟩ := burnsideTA12_mem_sup_of_commute hc g.2
  have hg' : (g : H) = u * v := hg
  show (g : H) * (n : H) * (g : H)⁻¹ ∈ L₂
  have hvn : v * (n : H) * v⁻¹ ∈ L₂ := L₂.mul_mem (L₂.mul_mem hv hn) (L₂.inv_mem hv)
  have hcomm : u * (v * (n : H) * v⁻¹) = (v * (n : H) * v⁻¹) * u := (hc u hu _ hvn).eq
  have h1 : (g : H) * (n : H) * (g : H)⁻¹ = v * (n : H) * v⁻¹ := by
    rw [hg']
    calc u * v * (n : H) * (u * v)⁻¹ = u * (v * n * v⁻¹) * u⁻¹ := by group
      _ = (v * n * v⁻¹) * u * u⁻¹ := by rw [hcomm]
      _ = v * n * v⁻¹ := by group
  rw [h1]
  exact hvn

private theorem burnsideTA12_quotient_equiv {L₁ L₂ : Subgroup H} (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b)
    [hN : (L₂.subgroupOf (L₁ ⊔ L₂)).Normal]
    (hker : ∀ u : ↥L₁, (u : H) ∈ L₂ ↔ u ∈ center ↥L₁) :
    Nonempty (↥L₁ ⧸ center ↥L₁ ≃* ↥(L₁ ⊔ L₂) ⧸ L₂.subgroupOf (L₁ ⊔ L₂)) := by
  set θ : ↥L₁ →* ↥(L₁ ⊔ L₂) ⧸ L₂.subgroupOf (L₁ ⊔ L₂) :=
    (QuotientGroup.mk' (L₂.subgroupOf (L₁ ⊔ L₂))).comp (Subgroup.inclusion le_sup_left) with hθ
  have hsurj : Function.Surjective θ := by
    intro x
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨u, hu, v, hv, hx⟩ := burnsideTA12_mem_sup_of_commute hc x₀.2
    refine ⟨⟨u, hu⟩, ?_⟩
    change QuotientGroup.mk (Subgroup.inclusion le_sup_left ⟨u, hu⟩) = QuotientGroup.mk x₀
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : (((Subgroup.inclusion le_sup_left ⟨u, hu⟩)⁻¹ * x₀ : ↥(L₁ ⊔ L₂)) : H) = v := by
      have hx' : (x₀ : H) = u * v := hx
      show u⁻¹ * (x₀ : H) = v
      rw [hx']
      group
    rw [h1]
    exact hv
  have hkerθ : θ.ker = center ↥L₁ := by
    ext u
    rw [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hker u
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerθ.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hsurj)⟩

private theorem burnsideTA12_center_map {A B : Type} [Group A] [Group B] (φ : A ≃* B) {z : A}
    (hz : z ∈ center A) : φ z ∈ center B := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨a, rfl⟩ := φ.surjective g
  rw [← map_mul, ← map_mul, hz a]

private theorem burnsideTA12_hiii {L₂ : Subgroup H} {f : ℕ} (hf : Odd f) (h₂ : IsSUn 3 (2 ^ f) ↥L₂)
    (h9 : ¬ 9 ∣ 2 ^ f + 1) :
    ∀ v ∈ L₂, v ^ 3 ∈ (center ↥L₂).map L₂.subtype → v ^ 3 = 1 := by
  intro v hv hvZ
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h₂
  obtain ⟨c, hc, hcv⟩ := Subgroup.mem_map.1 hvZ
  have hw3 : (⟨v, hv⟩ : ↥L₂) ^ 3 = c := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hcv.symm)
  have hcen : φ ((⟨v, hv⟩ : ↥L₂) ^ 3) ∈ center ↥(StatedSU 3 (2 ^ f) K) := by
    rw [hw3]
    exact burnsideTA12_center_map φ hc
  have h1 := burnsideTA12_su3_no_order_nine hf hK h9 (v := φ ⟨v, hv⟩) (by
    rw [← map_pow]
    exact hcen)
  have h2 : (⟨v, hv⟩ : ↥L₂) ^ 3 = 1 := φ.injective (by rw [map_pow, h1, map_one])
  have h3 := congrArg Subtype.val h2
  simpa using h3

private theorem burnsideTA12_hii {L₁ L₂ : Subgroup H} (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b)
    [hN : (L₂.subgroupOf (L₁ ⊔ L₂)).Normal] {f : ℕ} (hf : Odd f) (h₁ : IsSUn 3 (2 ^ f) ↥L₁)
    (hker : ∀ u : ↥L₁, (u : H) ∈ L₂ ↔ u ∈ center ↥L₁) :
    ∀ Ē : Subgroup (↥(L₁ ⊔ L₂) ⧸ L₂.subgroupOf (L₁ ⊔ L₂)),
      CFSG.Open.IsElemAbelian 3 Ē → Nat.card Ē ≤ 9 := by
  intro Ē hĒ
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h₁
  obtain ⟨e⟩ := burnsideTA12_quotient_equiv hc hker
  obtain ⟨e'⟩ := burnsideTA12_quot_equiv φ _ (burnsideTA12_center_statedSU_eq hK)
  have hf1 : 1 ≤ f := by obtain ⟨k, hk⟩ := hf; omega
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  have h3 : 3 ∣ 2 ^ f + 1 := by
    have := burnsideTA12_two_pow_odd_mod_three hf
    omega
  have hrank := CFSG.LieType.SeitzGeneration.pRank_three_projSU_three_le hU h3
  have heq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) (e.symm.trans e')
  refine burnsideTA12_card_le_of_pRank_le ?_ hĒ
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, heq]
  exact hrank

private theorem burnsideTA12_rank_pair_aux {L₁ L₂ : Subgroup H} (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b)
    (hZ : Nat.card ((center ↥L₂).map L₂.subtype) = 3)
    (hZ₁ : (center ↥L₂).map L₂.subtype ≤ L₁)
    (hinf : ∀ x ∈ L₁, x ∈ L₂ → x ∈ (center ↥L₂).map L₂.subtype)
    (hker₁ : ∀ u : ↥L₁, (u : H) ∈ L₂ ↔ u ∈ center ↥L₁) {f₁ f₂ : ℕ} (hf₁ : Odd f₁)
    (hf₂ : Odd f₂) (h₁ : IsSUn 3 (2 ^ f₁) ↥L₁) (h₂ : IsSUn 3 (2 ^ f₂) ↥L₂)
    (h9 : ¬ 9 ∣ 2 ^ f₂ + 1) {A : Subgroup H} (hA : A ≤ L₁ ⊔ L₂)
    (hAel : CFSG.Open.IsElemAbelian 3 A) : Nat.card A ≤ 27 := by
  haveI := burnsideTA12_normal_subgroupOf_sup hc
  exact burnsideTA12_rank_sup_le hc (Z := (center ↥L₂).map L₂.subtype) hZ hZ₁
    (Subgroup.map_subtype_le _) hinf
    (fun E hE hEL =>
      burnsideTA12_card_le_of_le_pRank (burnsideTA12_pRank_le_two_of_isSUn h₁) hEL hE)
    (fun E hE hEL =>
      burnsideTA12_card_le_of_le_pRank (burnsideTA12_pRank_le_two_of_isSUn h₂) hEL hE)
    (burnsideTA12_hii hc hf₁ h₁ hker₁) (burnsideTA12_hiii hf₂ h₂ h9) hA hAel

private theorem burnsideTA12_exists_noncentral_three {L : Subgroup H} (hL : CFSG.IsComponent L)
    (hZ : Nat.card (center ↥L) = 3) : ∃ g : ↥L, g ^ 3 = 1 ∧ g ∉ center ↥L := by
  haveI : Group.IsPerfect ↥L := hL.1.1
  obtain ⟨g, hg, hgZ⟩ := CFSG.SectionRank.exists_orderOf_not_mem_center_of_card_center
    (Or.inr hZ) (p := 3) Nat.prime_three (by norm_num) (by
      have : 3 ∣ Nat.card (center ↥L) := by rw [hZ]
      exact this.trans (Subgroup.card_subgroup_dvd_card _))
  exact ⟨g, by rw [← hg]; exact pow_orderOf_eq_one g, hgZ⟩

private theorem burnsideTA12_exists_E27 {L₁ L₂ : Subgroup H} (h₁ : CFSG.IsComponent L₁)
    (h₂ : CFSG.IsComponent L₂) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b)
    (hZ₁ : Nat.card (center ↥L₁) = 3) (hZ₂ : Nat.card (center ↥L₂) = 3) :
    ∃ F : Subgroup H, CFSG.Open.IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 3 ∧ F ≤ L₁ ⊔ L₂ := by
  obtain ⟨g, hg3, hgZ⟩ := burnsideTA12_exists_noncentral_three h₁ hZ₁
  obtain ⟨E₂, hE₂, hE₂c, hE₂L⟩ := burnsideTA12_exists_E9 h₂ hZ₂
  have hgH : ((g : ↥L₁) : H) ^ 3 = 1 := by rw [← SubgroupClass.coe_pow, hg3]; rfl
  obtain ⟨F, hF, hFc, hFK⟩ := CFSG.SectionRank.QTK.CoverB.exists_elemAbelian_sup Nat.prime_three
    (k := 2) hE₂ hE₂c hgH (fun e he => hc _ g.2 e (hE₂L he))
    (fun h => hgZ (mem_center_of_mem_commuting hc (hE₂L h)))
    (K := L₁ ⊔ L₂) ((le_sup_left : L₁ ≤ L₁ ⊔ L₂) g.2) (hE₂L.trans le_sup_right)
  exact ⟨F, hF, hFc, hFK⟩

private theorem burnsideTA12_pRank_pair (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (c₁ : CFSG.IsComponent L₁) (c₂ : CFSG.IsComponent L₂)
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) (hZ₁ : Nat.card (center ↥L₁) = 3)
    (hZ₂ : Nat.card (center ↥L₂) = 3)
    (hZeq : (center ↥L₁).map L₁.subtype = (center ↥L₂).map L₂.subtype) {f₁ f₂ : ℕ}
    (hf₁ : Odd f₁) (hf₂ : Odd f₂) (h₁ : IsSUn 3 (2 ^ f₁) ↥L₁) (h₂ : IsSUn 3 (2 ^ f₂) ↥L₂) :
    CFSG.Open.pRank 3 (L₁ ⊔ L₂) = 3 := by
  have hf₁1 : 1 ≤ f₁ := by obtain ⟨k, hk⟩ := hf₁; omega
  have hf₂1 : 1 ≤ f₂ := by obtain ⟨k, hk⟩ := hf₂; omega
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, Commute a b := fun a ha b hb => (hc b hb a ha).symm
  have hboth : ¬ (9 ∣ 2 ^ f₁ + 1 ∧ 9 ∣ 2 ^ f₂ + 1) := fun ⟨h9₁, h9₂⟩ =>
    burnsideTA12_false_of_both_nine he hc hZ₁ hZ₂ hZeq h₁ h₂ hf₁1 hf₂1 h9₁ h9₂
  have hZ₁L₂ : ∀ u : ↥L₁, u ∈ center ↥L₁ → (u : H) ∈ L₂ := fun u hu => by
    have : (u : H) ∈ (center ↥L₁).map L₁.subtype := ⟨u, hu, rfl⟩
    rw [hZeq] at this
    exact Subgroup.map_subtype_le _ this
  have hZ₂L₁ : ∀ u : ↥L₂, u ∈ center ↥L₂ → (u : H) ∈ L₁ := fun u hu => by
    have : (u : H) ∈ (center ↥L₂).map L₂.subtype := ⟨u, hu, rfl⟩
    rw [← hZeq] at this
    exact Subgroup.map_subtype_le _ this
  have hker₁ : ∀ u : ↥L₁, (u : H) ∈ L₂ ↔ u ∈ center ↥L₁ := fun u =>
    ⟨fun h => mem_center_of_mem_commuting hc h, hZ₁L₂ u⟩
  have hker₂ : ∀ u : ↥L₂, (u : H) ∈ L₁ ↔ u ∈ center ↥L₂ := fun u =>
    ⟨fun h => mem_center_of_mem_commuting hc' h, hZ₂L₁ u⟩
  have hcard₂ : Nat.card ((center ↥L₂).map L₂.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective L₂.subtype_injective, hZ₂]
  have hcard₁ : Nat.card ((center ↥L₁).map L₁.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective L₁.subtype_injective, hZ₁]
  have hbound : ∀ A : Subgroup H, A ≤ L₁ ⊔ L₂ → CFSG.Open.IsElemAbelian 3 A → Nat.card A ≤ 27 := by
    intro A hA hAel
    by_cases h9₂ : 9 ∣ 2 ^ f₂ + 1
    · have h9₁ : ¬ 9 ∣ 2 ^ f₁ + 1 := fun h => hboth ⟨h, h9₂⟩
      refine burnsideTA12_rank_pair_aux hc' hcard₁ ?_ ?_ hker₂ hf₂ hf₁ h₂ h₁ h9₁
        (sup_comm L₁ L₂ ▸ hA) hAel
      · rw [hZeq]; exact Subgroup.map_subtype_le _
      · intro x hx₂ hx₁
        exact ⟨⟨x, hx₁⟩, mem_center_of_mem_commuting hc hx₂, rfl⟩
    · refine burnsideTA12_rank_pair_aux hc hcard₂ ?_ ?_ hker₁ hf₁ hf₂ h₁ h₂ h9₂ hA hAel
      · rw [← hZeq]; exact Subgroup.map_subtype_le _
      · intro x hx₁ hx₂
        exact ⟨⟨x, hx₂⟩, mem_center_of_mem_commuting hc' hx₁, rfl⟩
  apply le_antisymm
  · refine csSup_le' ?_
    rintro k ⟨E, hEle, hE, hk⟩
    have h27 := hbound E hEle hE
    rw [hk] at h27
    by_contra hlt
    push Not at hlt
    have : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  · obtain ⟨F, hF, hFc, hFle⟩ := burnsideTA12_exists_E27 c₁ c₂ hc hZ₁ hZ₂
    exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hFle hF hFc

private theorem burnsideTA12_pairFact_of (hCat : CFSG.SectionRank.CatalogStepHyp)
    (hTC : CFSG.QuasithinUnique.Vol2Native.ThreeCoverFactCat) : burnsideTA12_PairFact := by
  intro G _ _ hev hK hC L₁ L₂ h₁ h₂ hne r hr hr2 hrZ₁ hrZ₂ hZ₁ hZ₂
  have hc := layer_commute_of_distinct_components h₁ h₂ hne
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, Commute a b := fun a ha b hb => (hc b hb a ha).symm
  obtain ⟨hr3, hcard₁, hA₁⟩ := burnsideTA12_comp_data hCat hTC hev hK hC h₁ h₂ hne hr hr2 hrZ₁ hZ₁
  obtain ⟨-, hcard₂, hA₂⟩ :=
    burnsideTA12_comp_data hCat hTC hev hK hC h₂ h₁ hne.symm hr hr2 hrZ₂ hZ₂
  obtain ⟨n₁, hn₁3, hn₁o, hS₁⟩ : ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ IsSUn 3 (2 ^ n) ↥L₁ := by
    rcases burnsideTA12_rl_or_su3 h₁.1 hA₁ with hRL | h
    · exact (burnsideTA12_false_of_RLLift hev h₂ hc hcard₂ hRL).elim
    · exact h
  obtain ⟨n₂, hn₂3, hn₂o, hS₂⟩ : ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ IsSUn 3 (2 ^ n) ↥L₂ := by
    rcases burnsideTA12_rl_or_su3 h₂.1 hA₂ with hRL | h
    · exact (burnsideTA12_false_of_RLLift hev h₁ hc' hcard₁ hRL).elim
    · exact h
  have hcen : centerOf L₁ = centerOf L₂ :=
    burnsideTA12_centerOf_eq_of_card hev h₁ h₂ hc hcard₁ hcard₂
  have hZeq : (center ↥L₁).map L₁.subtype = (center ↥L₂).map L₂.subtype := by
    rw [← burnsideTA12_centerOf_eq, ← burnsideTA12_centerOf_eq]
    exact hcen
  have hrank : CFSG.Open.pRank 3 (L₁ ⊔ L₂) = 3 :=
    burnsideTA12_pRank_pair hev h₁ h₂ hc hcard₁ hcard₂ hZeq hn₁o hn₂o hS₁ hS₂
  refine ⟨hr3, hcard₁, layer_eq_sup_of_pRank_three hev h₁ h₂ hrank, ?_, hcen, n₁, n₂, hS₁, hS₂,
    hn₁3, hn₁o, hn₂3, hn₂o, burnsideTA12_gcd_cond hev hc hcard₁ hS₁ hS₂ hn₁3 hn₁o hn₂3 hn₂o⟩
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact hrank

end BurnsideTA12pair


section


theorem burnsideTA12_a_2_12_of
    (hR2F : burnsideTA12_Rank2Fact) (h11 : A_2_11) : A_2_12 :=
  burnsideTA12_a_2_12_of_facts hR2F burnsideTA12_coverFact
    (burnsideTA12_pairFact_of CFSG.SectionRank.catalogStepHyp
      CFSG.QuasithinUnique.Vol2Native.threeCoverFactCat) h11

end

end BurnsideTA12

section TheoremAFinalA212


theorem as_A_2_12
    : A_2_12 :=
  burnsideTA12_a_2_12_of burnsideTA11_rank_two_dichotomy as_A_2_11

end TheoremAFinalA212

section TheoremAFinalA21


theorem as_A_2_1
    : A_2_1 :=
  a_2_1_of_reduction as_A_2_11 as_A_2_12 as_I_1_3 as_I_1_4

end TheoremAFinalA21

section TheoremAFinalVacuous


private theorem burnsideTAF_not_minimalCounterexampleABC
    (G : Type) [Group G] [Finite G] :
    ¬ IsMinimalCounterexampleABC G := by
  rintro ⟨h, -⟩
  rcases h with hA | hB | hC
  · exact hA (as_A_2_1 G)
  · exact hB (as_A_2_2 G)
  · exact hC fun hs hn hsq => by
      haveI := hs
      exact CFSG.Milestones.cl_lit_sqtk_simple_list_simple G hn hsq

theorem as_A_2_13
    : A_2_13 := fun G _ _ h => absurd h (burnsideTAF_not_minimalCounterexampleABC G)

theorem as_A_2_16
    : A_2_16 := fun G _ _ h => absurd h (burnsideTAF_not_minimalCounterexampleABC G)

theorem as_A_2_17
    : A_2_17 := fun G _ _ h => absurd h (burnsideTAF_not_minimalCounterexampleABC G)

theorem as_A_2_18
    : A_2_18 := fun G _ _ h => absurd h (burnsideTAF_not_minimalCounterexampleABC G)

theorem as_A_2_19
    : A_2_19 := fun G _ _ h => absurd h (burnsideTAF_not_minimalCounterexampleABC G)

end TheoremAFinalVacuous

end CFSG.ASVolI
