module

public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.LocalAnalysis.RankThreeUC.Assembly
public import CFSG.RankThree.PartOne.S12.Hyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

structure StandingGe3 (G : Type) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Open.IsKProper G
  charTwo : CFSG.Open.IsCharTwoType G
  rank : 3 ≤ CFSG.Open.evenRank G

structure Data (G : Type) [Group G] [Finite G] where
  M : Subgroup G
  T : Subgroup G
  sig : Set ℕ
  sig1 : Set ℕ
  sig2 : Set ℕ
  sig3 : Set ℕ
  standing : StandingGe3 G
  maxLocal : rankThreeIsMaxTwoLocal M
  sylowM : CFSG.ABGLocalTools.IsSylowOf 2 T M
  sylowG : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤
  normalizer_le : normalizer (T : Set G) ≤ M
  sig_prime : ∀ p ∈ sig, p.Prime ∧ p ≠ 2
  sig_rank : ∀ p ∈ sig, 2 ≤ CFSG.Open.pRank p M
  sig_sub : sig = sig1 ∪ sig2 ∪ sig3

namespace Data

variable {G : Type} [Group G] [Finite G] (D : Data G)

@[expose] noncomputable def k : ℕ := kParam D.M

@[expose] def Z : Subgroup G := CFSG.RankThree.PartOne.omegaOneCenterIn D.T

@[expose] def U : Subgroup G := uCore D.M D.T

end Data

section Basic

variable {G : Type} [Group G] [Finite G]

@[expose] def calMOf (X : Subgroup G) : Set (Subgroup G) :=
  {N | rankThreeIsMaxTwoLocal N ∧ X ≤ N}

@[expose] def calNOf (X : Subgroup G) : Set (Subgroup G) :=
  {N | IsCoatom N ∧ X ≤ N}

@[expose] def UniqueMax (M X : Subgroup G) : Prop :=
  calMOf X = {M}

abbrev Bar2 (L : Subgroup G) : Type := ↥L ⧸ CFSG.pCore 2 ↥L

@[expose] def calC (M : Subgroup G) : Set (Subgroup G) :=
  {L | CFSG.Open.IsSubnormal L M ∧ ⁅L, L⁆ = L ∧ CFSG.Open.IsQuasisimple (Bar2 L)}

@[expose] def Opp (p : ℕ) (X : Subgroup G) : Subgroup G :=
  CFSG.RankThree.PartOne.pElementSubgroup p X

@[expose] def OInf (H : Subgroup G) : Subgroup G :=
  (CFSG.solvableRadical ↥H).map H.subtype

@[expose] def Fstar (H : Subgroup G) : Subgroup G :=
  (genFittingFStar ↥H).map H.subtype

@[expose] def Permutes (H T : Subgroup G) : Prop :=
  (H : Set G) * (T : Set G) = (T : Set G) * (H : Set G)

@[expose] def IrrOn (N E : Subgroup G) : Prop :=
  ∀ W : Subgroup G, W ≤ E → N ≤ normalizer (W : Set G) → W = ⊥ ∨ W = E

@[expose] def InvertedOutside (M L X : Subgroup G) : Prop :=
  ∃ t ∈ L, t ∉ M ∧ (∃ k : ℕ, orderOf t = 2 ^ k) ∧ ∀ x ∈ X, t * x * t⁻¹ = x⁻¹

end Basic

section Section20

variable {G : Type} [Group G] [Finite G]

@[expose] def calL (T M : Subgroup G) : Set (Subgroup G) :=
  {L | T ≤ normalizer (L : Set G) ∧ ⁅L, L⁆ = L ∧ L ⊔ T ∈ hSet T M ∧
    ∃ K ∈ calC L, L = ⨆ t : T, K.map (MulAut.conj (t : G)).toMonoidHom}

@[expose] def calLOf (T M H : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ calL T M ∧ CFSG.Open.IsSubnormal L H}

@[expose] def calLStar (T M : Subgroup G) : Set (Subgroup G) :=
  {L | Maximal (· ∈ calL T M) L}

@[expose] def calLLow (T M : Subgroup G) : Set (Subgroup G) :=
  {L | Minimal (· ∈ calL T M) L}

@[expose] def calB (T M L : Subgroup G) : Set (Subgroup G) :=
  {B | B ≤ L ∧ IsCyclic B ∧ Squarefree (Nat.card B) ∧ Odd (Nat.card B) ∧ Permutes B T ∧
    InvertedOutside M L B}

@[expose] def calB1 (T M L : Subgroup G) : Set (Subgroup G) :=
  {A | A ≤ L ∧ IsMulCommutative A ∧
    ∃ B C : Subgroup G, B ∈ calB T M L ∧ IsMulCommutative C ∧ Odd (Nat.card C) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card C → ∃ P : Sylow p C, Nat.card P = p ^ 2 ∧ ¬ IsCyclic P) ∧
      A = B ⊔ C ∧ Permutes A T ∧ InvertedOutside M L A ∧
      ∀ p : ℕ, p.Prime → p ∣ Nat.card C → IrrOn (T ⊓ normalizer (A : Set G)) (CFSG.Open.pCoreOf p A)}

end Section20

section Weak

variable {G : Type} [Group G] [Finite G]

@[expose] def InCalV (M V : Subgroup G) : Prop :=
  V ≠ ⊥ ∧ V ≤ M ∧ M ≤ normalizer (V : Set G) ∧ CFSG.Open.IsElemAbelian 2 V

@[expose] def InCalV1 (M T V : Subgroup G) : Prop :=
  InCalV M V ∧ UniqueMax M (M ⊓ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G))

@[expose] def TwoReduced (M V : Subgroup G) : Prop :=
  ∀ K : Subgroup G, K ≤ M → M ≤ normalizer (K : Set G) → M ⊓ centralizer (V : Set G) ≤ K →
    (∃ n : ℕ, ((centralizer (V : Set G)).subgroupOf K).index = 2 ^ n) →
      K ≤ centralizer (V : Set G)

@[expose] def InCalW (M T V : Subgroup G) : Prop :=
  InCalV1 M T V ∧ 8 ≤ Nat.card V ∧ TwoReduced M V

@[expose] def InCalWStar (M T V : Subgroup G) : Prop :=
  InCalW M T V ∧ ∀ W : Subgroup G, InCalW M T W → W ≤ V → W = V

@[expose] def InCalV0 (M V₀ V : Subgroup G) : Prop :=
  InCalV M V₀ ∧ InCalV M V ∧ V₀ ≤ V ∧ CFSG.CGT.Timmesfeld75.IsTI V₀ ∧
    ¬ CFSG.CGT.Timmesfeld75.IsTI V ∧
    (∀ v ∈ V, v ∉ V₀ → closure {x : G | ∃ m ∈ M, x = m * v * m⁻¹} = V) ∧
    ¬ TwoReduced M V

@[expose] def CentralizersUnique (M T : Subgroup G) : Prop :=
  ∀ z ∈ T, (∀ t ∈ T, z * t = t * z) → z ≠ 1 →
    centralizer ({z} : Set G) ≤ M ∧
      ∀ g : G, g ∉ M → ¬ centralizer ({z} : Set G) ≤ M.map (MulAut.conj g).toMonoidHom

@[expose] def Hyp123 (M T V₀ V : Subgroup G) : Prop :=
  (InCalWStar M T V ∧ V₀ = ⊥) ∨
    (InCalV0 M V₀ V ∧ CentralizersUnique M T ∧ ∀ W : Subgroup G, ¬ InCalW M T W)

@[expose] def CentralizesMod (V₀ V : Subgroup G) (m : G) : Prop :=
  ∀ v ∈ V, m * v * m⁻¹ * v⁻¹ ∈ V₀

@[expose] def centMod (V₀ V : Subgroup G) (m : G) : Set G :=
  {v | v ∈ V ∧ m * v * m⁻¹ * v⁻¹ ∈ V₀}

@[expose] def MBarGT (M V₀ V : Subgroup G) (n : ℕ) : Prop :=
  (∀ m ∈ M, ¬ CentralizesMod V₀ V m → CentralizesMod V₀ V (m * m) →
      2 ^ (n + 1) * Nat.card (centMod V₀ V m) ≤ Nat.card V) ∧
    ((∀ m ∈ M, CentralizesMod V₀ V (m * m) → CentralizesMod V₀ V m) →
      2 ^ (n + 1) * Nat.card V₀ ≤ Nat.card V)

end Weak

section Shapes

open CFSG.Blueprint (LieModel)

@[expose] def CoverOf (X Y : Type) [Group X] [Group Y] : Prop :=
  CFSG.Open.IsQuasisimple X ∧ Nonempty ((X ⧸ Subgroup.center X) ≃* Y)

@[expose] def IsSz (X : Type) [Group X] (f : ℕ) : Prop := LieModel X .twistedB2 0 2 f
@[expose] def IsL2 (X : Type) [Group X] (f : ℕ) : Prop := LieModel X .PSL 2 2 f
@[expose] def IsL3 (X : Type) [Group X] (f : ℕ) : Prop := LieModel X .PSL 3 2 f
@[expose] def IsU3 (X : Type) [Group X] (f : ℕ) : Prop := LieModel X .PSU 3 2 f
@[expose] def IsSp4 (X : Type) [Group X] (f : ℕ) : Prop := LieModel X .PSp 2 2 f
@[expose] def IsU4 (X : Type) [Group X] (f : ℕ) : Prop := LieModel X .PSU 4 2 f
@[expose] def IsU5 (X : Type) [Group X] (f : ℕ) : Prop := LieModel X .PSU 5 2 f
@[expose] def IsOmega8m (X : Type) [Group X] (f : ℕ) : Prop := LieModel X .POmegaMinus 4 2 f
@[expose] def IsG2 (X : Type) [Group X] (f : ℕ) : Prop := LieModel X .G2 0 2 f
@[expose] def Is3D4 (X : Type) [Group X] (f : ℕ) : Prop := LieModel X .trialityD4 0 2 f
@[expose] def IsL2Odd (X : Type) [Group X] (p : ℕ) : Prop := LieModel X .PSL 2 p 1
@[expose] def IsAlt (X : Type) [Group X] (n : ℕ) : Prop := Nonempty (X ≃* alternatingGroup (Fin n))
@[expose] def IsSpor (X : Type) [Group X] (s : TauCeti.SporadicName) : Prop :=
  CFSG.Blueprint.NativeSporadic.IsSporadic X s
@[expose] def IsJ1 (X : Type) [Group X] : Prop := IsSpor X .J1
@[expose] def IsSU3 (X : Type) [Group X] (f : ℕ) : Prop :=
  CFSG.Open.IsQuasisimple X ∧ IsU3 (X ⧸ Subgroup.center X) f
@[expose] def IsSL3 (X : Type) [Group X] (f : ℕ) : Prop :=
  CFSG.Open.IsQuasisimple X ∧ IsL3 (X ⧸ Subgroup.center X) f
@[expose] def IsChev (X : Type) [Group X] (p : ℕ) : Prop :=
  ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n f : ℕ),
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p f ∧ LieModel X t n p f

end Shapes

end CFSG.LocalAnalysis.UniquenessCase.UC22
