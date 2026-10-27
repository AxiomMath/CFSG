
module

public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.Open.SQTKSimpleListTauCeti
public import CFSG.Milestones.CL_LIT_SQTK_simple_listBase
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement Matrix

structure SQTKHyp (G : Type) [Group G] : Prop where
  finite : Finite G
  sqt : CFSG.Open.SQTKTauCeti.StronglyQuasithin G
  kgroup : CFSG.SectionRank.IsKGroupCat G
  o2 : CFSG.pCore 2 G = ⊥

@[expose] def SQTKGroup (X : Type) [Group X] [Finite X] : Prop :=
  CFSG.Open.SQTKTauCeti.StronglyQuasithin X ∧ CFSG.SectionRank.IsKGroupCat X

section Vocabulary

abbrev A23List (S : Type) [Group S] : Prop :=
  CFSG.Milestones.SQTKSimpleList S

@[expose] def IsAlt (n : ℕ) (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* alternatingGroup (Fin n))

@[expose] def IsSporadic (s : TauCeti.SporadicName) (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier s)

@[expose] def IsPSL (n p e : ℕ) (X : Type) [Group X] : Prop := StatedClassicalModel X .PSL n p e

@[expose] def IsPSU (n p e : ℕ) (X : Type) [Group X] : Prop := StatedClassicalModel X .PSU n p e

@[expose] def IsPSLEps3 (s : Bool) (p e : ℕ) (X : Type) [Group X] : Prop :=
  match s with
  | true => IsPSL 3 p e X
  | false => IsPSU 3 p e X

@[expose] def IsPSp4 (p e : ℕ) (X : Type) [Group X] : Prop := StatedClassicalModel X .PSp 2 p e

@[expose] def IsG2 (p e : ℕ) (X : Type) [Group X] : Prop :=
  CFSG.Blueprint.ChevalleyExceptionalModel X .G2 p e

@[expose] def Is3D4 (p e : ℕ) (X : Type) [Group X] : Prop :=
  CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 p e

@[expose] def Is2F4 (e : ℕ) (X : Type) [Group X] : Prop :=
  CFSG.Blueprint.ReeTitsModel X .twistedF4 2 e

@[expose] def IsTits (X : Type) [Group X] : Prop := CFSG.Blueprint.ReeTitsModel X .Tits 2 1

@[expose] def IsSz (e : ℕ) (X : Type) [Group X] : Prop := CFSG.Blueprint.SuzukiModel X 2 e

@[expose] def IsHat (X S : Type) [Group X] [Group S] : Prop :=
  CFSG.IsQuasisimple X ∧ Nat.card (Subgroup.center X) = 3 ∧
    Nonempty (X ⧸ Subgroup.center X ≃* S)

@[expose] def IsSL3 (q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
    Nonempty (X ≃* ↥(StatedSL 3 K))

@[expose] def IsSU3 (q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ 2 ∧
    Nonempty (X ≃* ↥(StatedSU 3 q K))

@[expose] def IsSLEps3 (s : Bool) (q : ℕ) (X : Type) [Group X] : Prop :=
  match s with
  | true => IsSL3 q X
  | false => IsSU3 q X

@[expose] def IsSL2 (p : ℕ) (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))

@[expose] def IsHomocyclicRank2 (p : ℕ) (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧
    Nonempty (X ≃* (Multiplicative (ZMod (p ^ n)) × Multiplicative (ZMod (p ^ n))))

@[expose] def IsExt (X : Type) [Group X] (PV PY : ∀ (V : Type) [Group V], Prop) : Prop :=
  ∃ (V : Subgroup X) (_ : V.Normal), PV ↥V ∧ PY (X ⧸ V)

@[expose] def IsE2 (n : ℕ) (V : Type) [Group V] : Prop := IsElemAbelianOfRank 2 n V

@[expose] def IsExtraspecial2 (m : ℕ) (V : Type) [Group V] : Prop :=
  CFSG.IsExtraspecial 2 V ∧ Nat.card V = 2 ^ (1 + 2 * m)

@[expose] def IsParabolic2 {G : Type} [Group G] (L P : Subgroup G) : Prop :=
  P ≤ L ∧ ∃ S : Subgroup G, CFSG.QuasithinUnique.IsSylowTwoOf S L ∧
    L ⊓ Subgroup.normalizer (S : Set G) ≤ P

@[expose] def IsMaxParabolic2 {G : Type} [Group G] (L P : Subgroup G) : Prop :=
  IsParabolic2 L P ∧ P ≠ L ∧ ∀ Q : Subgroup G, IsParabolic2 L Q → Q ≠ L → P ≤ Q → Q = P

@[expose] def thetaOf {G : Type} [Group G] (H : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ H ∧ orderOf x = 3}

@[expose] def conjSubgroups {H : Type} [Group H] (K : Subgroup H) : Set (Subgroup H) :=
  {K' | ∃ h : H, K' = K.map (MulAut.conj h).toMonoidHom}

@[expose] def IsQuasithin (H : Type) [Group H] [Finite H] : Prop := evenRank H ≤ 2

@[expose] def conjSubgroupsBy {G : Type} [Group G] (T K : Subgroup G) : Set (Subgroup G) :=
  {K' | ∃ t ∈ T, K' = K.map (MulAut.conj t).toMonoidHom}

@[expose] def ActsTriviallyOnFrattiniQuotient {X : Type} [Group X] (P : Subgroup X) (x : X) :
    Prop :=
  ∀ d ∈ P, d⁻¹ * (x * d * x⁻¹) ∈ frattiniIn P

@[expose] def A36Case2List (X : Type) [Group X] : Prop :=
  (∃ (s : Bool) (p e : ℕ), p.Prime ∧ 1 ≤ e ∧
      ((p = 2 ∧ Int.ModEq 3 ((p ^ e : ℕ) : ℤ) (if s then 1 else -1)) ∨ (p ≠ 2 ∧ e = 1)) ∧
      IsSLEps3 s (p ^ e) X) ∨
    IsHat X (alternatingGroup (Fin 6)) ∨ IsHat X (alternatingGroup (Fin 7)) ∨
    IsHat X (CFSG.Blueprint.NativeSporadic.Carrier .M22)

@[expose] def NaturalSL2Action (p : ℕ) (X : Type) [Group X] (F : Subgroup X) [F.Normal] : Prop :=
  ∃ (e : F ≃* Multiplicative (Fin 2 → ZMod p))
    (ψ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)),
    Function.Surjective ψ ∧ ψ.ker = F ∧
    ∀ (x : X) (f : F), e (MulAut.conjNormal x f) =
      Multiplicative.ofAdd
        ((((ψ x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p))) *ᵥ (Multiplicative.toAdd (e f)))

@[expose] def A36Case3 (X : Type) [Group X] : Prop :=
  ∃ p : ℕ, p.Prime ∧ 3 < p ∧ CFSG.generalizedFitting X = CFSG.fittingSubgroup X ∧
    IsElemAbelianOfRank p 2 ↥(CFSG.fittingSubgroup X) ∧
    NaturalSL2Action p X (CFSG.fittingSubgroup X)

@[expose] def A36Case4 (X : Type) [Group X] : Prop :=
  CFSG.generalizedFitting X = CFSG.fittingSubgroup X ∧
    Group.IsNilpotent ↥(CFSG.fittingSubgroup X) ∧ IsSL2 5 (X ⧸ CFSG.fittingSubgroup X) ∧
    ∀ p : ℕ, p.Prime → p ∣ Nat.card (CFSG.fittingSubgroup X) →
      (p % 5 = 1 ∨ p % 5 = 4 ∨ p = 5) ∧
      (IsPOnePlusTwo p ↥(CFSG.pCore p X) ∨ IsHomocyclicRank2 p ↥(CFSG.pCore p X))

@[expose] def A36Common (X : Type) [Group X] : Prop :=
  CFSG.fittingSubgroup X = CFSG.oddCore X ∧
    CFSG.IsQuasisimple (X ⧸ CFSG.fittingSubgroup X) ∧
    ((CFSG.generalizedFitting X = CFSG.fittingSubgroup X ∧
        (CFSG.fittingSubgroup X).relIndex (CFSG.solvableRadical X) = 2) ∨
      (CFSG.fittingSubgroup X = Subgroup.center X ∧
        CFSG.fittingSubgroup X = CFSG.solvableRadical X ∧
        (Nat.card (CFSG.fittingSubgroup X) = 1 ∨ Nat.card (CFSG.fittingSubgroup X) = 3))) ∧
    ⁅CFSG.solvableRadical X, CFSG.solvableRadical X⁆ = ⁅CFSG.fittingSubgroup X, (⊤ : Subgroup X)⁆ ∧
    CFSG.IsQuasisimple (X ⧸ ⁅CFSG.solvableRadical X, CFSG.solvableRadical X⁆)

@[expose] def A36Conclusion {G : Type} [Group G] (L : Subgroup G) : Prop :=
  (CFSG.IsComponent L ∧ IsSimpleGroup ↥L ∧ A23List ↥L) ∨
    (CFSG.IsComponent L ∧ Nat.card (Subgroup.center ↥L) = 3 ∧ A36Case2List ↥L) ∨
    A36Case3 ↥L ∨ A36Case4 ↥L

@[expose] def A36Extra (X : Type) [Group X] : Prop :=
  ∀ q : ℕ, q.Prime → q ∣ Nat.card (CFSG.fittingSubgroup X) →
    ∃ P : Subgroup ↥(CFSG.pCore q X), IsSupercritical q P ∧
      (∀ α : MulAut ↥(CFSG.pCore q X), (orderOf α).Coprime q →
        (∀ x ∈ P, x⁻¹ * α x ∈ frattiniIn P) → α = 1) ∧
      (IsElemAbelianOfRank q 2 ↥P ∨ IsPOnePlusTwo q ↥P) ∧
      ∀ x : X, ActsTriviallyOnFrattiniQuotient (P.map (CFSG.pCore q X).subtype) x ↔
        x ∈ CFSG.fittingSubgroup X

@[expose] def A36Strong {G : Type} [Group G] (L : Subgroup G) : Prop :=
  A36Conclusion L ∧ A36Common ↥L ∧ ((A36Case3 ↥L ∨ A36Case4 ↥L) → A36Extra ↥L)

@[expose] def A36Statement (G : Type) [Group G] : Prop :=
  ∀ L ∈ cComp (⊤ : Subgroup G), A36Strong L

@[expose] def A37Statement (G : Type) [Group G] : Prop :=
  ∀ L₁ ∈ cComp (⊤ : Subgroup G), ∀ L₂ ∈ cComp (⊤ : Subgroup G), L₁ ≠ L₂ → ⁅L₁, L₂⁆ = ⊥

@[expose] def A38Part12 (H : Type) [Group H] [Finite H] : Prop :=
  IsQuasithin H → CFSG.SectionRank.IsKGroupCat H →
    ∀ K : Subgroup H, CFSG.IsComponent K → CFSG.pCore 2 ↥K = ⊥ → ¬ K.Normal →
      ((Set.ncard (conjSubgroups K) = 2 ∧
          ∀ t : H, t ∉ Subgroup.normalizer (K : Set H) →
            conjClosure K ⊤ = K ⊔ K.map (MulAut.conj t).toMonoidHom) ∧
        ((∃ n, IsPSL 2 2 n ↥K) ∨ (∃ n, IsSz n ↥K) ∨ IsSporadic .J1 ↥K ∨
          (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧ IsPSL 2 p e ↥K) ∨ IsSU3 8 ↥K))

@[expose] def A38Types (X : Type) [Group X] : Prop :=
  (∃ n, IsPSL 2 2 n X) ∨ (∃ n, IsSz n X) ∨ IsSporadic .J1 X ∨
    (∃ p : ℕ, p.Prime ∧ 3 < p ∧ IsPSL 2 p 1 X)

@[expose] def A38Part3 (G : Type) [Group G] : Prop :=
  ∀ L ∈ cComp (⊤ : Subgroup G),
    (L.Normal ∨
      (A38Types ↥L ∧ ∃ t : G, t ∉ Subgroup.normalizer (L : Set G) ∧
        ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
        L ⊓ L.map (MulAut.conj t).toMonoidHom = ⊥ ∧
        conjClosure L ⊤ = L ⊔ L.map (MulAut.conj t).toMonoidHom)) ∧
    ∀ T : Subgroup G, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ →
      ((L.Normal ∧ conjSubgroupsBy T L = {L} ∧ cComp (L ⊔ T) = {L}) ∨
        (∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) ∧
          conjSubgroupsBy T L = {L, L.map (MulAut.conj t).toMonoidHom} ∧
          cComp (L ⊔ T) = {L, L.map (MulAut.conj t).toMonoidHom} ∧
          ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
          L ⊓ L.map (MulAut.conj t).toMonoidHom = ⊥ ∧
          T ≤ Subgroup.normalizer ((L ⊔ L.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) ∧
          L ⊔ T = (L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊔ T))

@[expose] def A39Statement (G : Type) [Group G] : Prop :=
  cCompSpan (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G) ∧
    CFSG.layer (↥(cCompSpan (⊤ : Subgroup G)) ⧸ CFSG.oddCore ↥(cCompSpan (⊤ : Subgroup G))) = ⊤

end Vocabulary

end CFSG.Quasithin
