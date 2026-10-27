module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F12

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC6 (calCGS)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

open Classical in
@[expose] noncomputable def pRankMod (p : ℕ) (M N : Subgroup G) : ℕ :=
  if h : (N.subgroupOf M).Normal then
    haveI := h
    CFSG.Open.pRank p (⊤ : Subgroup (↥M ⧸ N.subgroupOf M))
  else 0

@[expose] def HasCompFactor (H : Subgroup G) (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∃ (L : Type) (_ : Group L), CFSG.Quasithin.E1.IsCompositionFactor ↥H L ∧ P L

@[expose] def IsLieOver (X : Type) [Group X] (n : ℕ) : Prop :=
  ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ), CFSG.Blueprint.LieModel X t m 2 n

@[expose] def Gam (i : ℕ) (X V : Subgroup G) : Set (Subgroup G) :=
  {A | A ≤ X ∧ ∃ (U : Subgroup G) (g : G), U ≤ V ∧ Nat.card V = 2 ^ i * Nat.card U ∧
    A = U.map (MulAut.conj g).toMonoidHom}

@[expose] def Wi (i : ℕ) (X V : Subgroup G) : Subgroup G :=
  ⨆ A ∈ Gam i X V, A

@[expose] def Ci (i : ℕ) (X V : Subgroup G) : Subgroup G :=
  X ⊓ centralizer ((Wi i X V : Subgroup G) : Set G)

@[expose] def InCalA (k : ℕ) (H U A : Subgroup G) : Prop :=
  H ⊓ centralizer (U : Set G) ≤ A ∧ A ≤ H ∧ ¬ A ≤ centralizer (U : Set G) ∧
    (∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ centralizer (U : Set G)) ∧
    (∀ x ∈ A, x * x ∈ centralizer (U : Set G)) ∧
    ∀ B : Subgroup G, H ⊓ centralizer (U : Set G) ≤ B → B ≤ A → B.relIndex A < 2 ^ k →
      U ⊓ centralizer (A : Set G) = U ⊓ centralizer (B : Set G)

structure Hyp124 (D : Data G) (H₀ : Subgroup G) : Prop where
  le_T : D.T ≤ H₀
  not_le_M : ¬ H₀ ≤ D.M
  fstar : Fstar H₀ = pCoreOf 2 H₀
  noOddRankOne : ¬ ∃ n : ℕ, Odd n ∧ 1 < n ∧
    HasCompFactor H₀ (fun X => IsL2 X n ∨ IsSz X n ∨ IsL3 X n)
  noBig : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M →
    ¬ HasCompFactor H₀ (fun X => (∃ n : ℕ, 2 < n ∧ IsLieOver X n) ∨ Is3D4 X 1 ∨ Is3D4 X 2 ∨
      IsU4 X 2 ∨ IsU5 X 2 ∨ IsOmega8m X 2 ∨ IsAlt X 9)

@[expose] def Hyp125 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  Hyp123 D.M D.T V₀ V ∧ ∃ H₀ : Subgroup G, Hyp124 D H₀

section EPrint

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E1

@[expose] def ETwoPrint (Q : Type) [Group Q] (Ta B : Subgroup Q) : Prop :=
  IsTwoClosed (solvableRadical Q) ∧ CFSG.Open.pCore 2 (Q ⧸ oInftyE Q) = ⊤ ∧
    twoResidual (⊤ : Subgroup Q) = perfectCore (⊤ : Subgroup Q) ∧
    ∃ L : Subgroup (Q ⧸ solvableRadical Q), CFSG.IsComponent L ∧
      CFSG.layer (Q ⧸ solvableRadical Q) =
        ⨆ t ∈ Ta.map (QuotientGroup.mk' (solvableRadical Q)), L.map (MulAut.conj t).toMonoidHom ∧
      (L = ⁅L, barRad Q B⁆ ∨
        (¬ barRad Q B ≤ Subgroup.normalizer (L : Set (Q ⧸ solvableRadical Q)) ∧
          Nat.card (barRad Q B) = 2))

@[expose] def IsEP (i : ℕ) (H T A K : Subgroup G) : Prop :=
  K ≤ H ∧ tauOf H T A ≤ T ⊓ K ∧ IsSylowIn 2 (T ⊓ K) K ∧
    ((EOne ↥K (A.subgroupOf K) ∧ Nat.card (barO2 ↥K (A.subgroupOf K)) ≤ 2 ^ i) ∨
     (ETwoPrint ↥K ((tauOf H T A).subgroupOf K) (A.subgroupOf K) ∧
       Nat.card (barRad ↥K (A.subgroupOf K)) ≤ 2 ^ i))

@[expose] def eGenP (i : ℕ) (H T : Subgroup G) (Ω : Set (Subgroup G)) : Subgroup G :=
  ⨆ A ∈ Ω, ⨆ (_ : A ≤ T), ⨆ K ∈ {K : Subgroup G | IsEP i H T A K}, K

@[expose] def InEForP (i : ℕ) (H T : Subgroup G) : Prop :=
  ∀ Ω : Set (Subgroup G), IsInvColl H Ω → Ω.Nonempty → (∀ A ∈ Ω, A ≠ ⊥) →
    eGenP i H T Ω ⊔ (H ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)) = H

end EPrint

@[expose] def InEP (j : ℕ) (H : Subgroup G) : Prop :=
  ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T H → InEForP j H T

@[expose] def InFFor (j : ℕ) (H T : Subgroup G) : Prop :=
  ∀ Ω : Set (Subgroup G), CFSG.Quasithin.E1.IsInvColl H Ω → Ω.Nonempty → (∀ A ∈ Ω, A ≠ ⊥) →
    ((eGenP j H T Ω : Subgroup G) : Set G) * (T : Set G) = (H : Set G)

@[expose] def InF (j : ℕ) (H : Subgroup G) : Prop :=
  ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T H → InFFor j H T

@[expose] def autNL {Q : Type} [Group Q] (S L : Subgroup Q) : Subgroup Q :=
  (S ⊓ normalizer (L : Set Q)) ⊔ L

@[expose] def autC {Q : Type} [Group Q] (S L : Subgroup Q) : Subgroup Q :=
  autNL S L ⊓ centralizer (L : Set Q)

@[expose] def R1214 (D : Data G) : Prop :=
  (∃ H₀ : Subgroup G, Hyp124 D H₀) →
  ∀ U₀ U₁ U₂ U₃ : Subgroup G, InCalV D.M U₀ → InCalV D.M U₁ → InCalV D.M U₂ → InCalV D.M U₃ →
    U₀ = U₁ ⊔ U₂ → U₀ ≠ U₁ → U₀ ≠ U₂ → U₀ ≠ U₃ →
    ∀ p ∈ D.sig, 1 < pRankMod p D.M (centralizer (U₀ : Set G)) →
      ¬ CFSG.CGT.Timmesfeld75.IsTI U₁ ∨ ¬ CFSG.CGT.Timmesfeld75.IsTI U₂

@[expose] def IsComponentModO2 (M L : Subgroup G) : Prop :=
  pCoreOf 2 M ≤ L ∧ L ≤ M ∧ IsSubnormal L M ∧
    ∃ h : ((pCoreOf 2 M).subgroupOf L).Normal,
      @IsQuasisimple (↥L ⧸ (pCoreOf 2 M).subgroupOf L) (@QuotientGroup.Quotient.group _ _ _ h)

@[expose] def ClassicalEvenAltG2 (X : Type) [Group X] : Prop :=
  (IsQuasisimple X ∧ ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ),
      (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t m 2 f) ∨
    (IsQuasisimple X ∧ ∃ n : ℕ, IsAlt (X ⧸ Subgroup.center X) n) ∨ ∃ n : ℕ, IsG2 X n

@[expose] def jOf (T : Subgroup G) : Subgroup G :=
  CFSG.inSubgroup (fun K _ => CFSG.elemThompson K 2) T

end CFSG.LocalAnalysis.UniquenessCase.UC22.F12
