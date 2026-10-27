module

public import CFSG.Quasithin.EmptyFaithful.T1515Defs
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.C3Defs
public import CFSG.Quasithin.Vol2.Ch1Local

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure Lemma15117Concl (T M Z₁ : Subgroup G) : Prop where
  sylow : IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁ ⊓ M)
  jS : thompsonJ (s1516 T Z₁) = thompsonJ T
  baumS : baum (s1516 T Z₁) = baum T
  cgs : CGS (baum (s1516 T Z₁)) ≤ M

structure Lemma15118Concl (T Mc M Z₁ : Subgroup G) : Prop where
  one : Z₁ ≤ vE1516 T Mc M ∧
    oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤ mZ1516 Mc Z₁
  two : ¬ (M ⊓ Subgroup.centralizer (Z₁ : Set G)) ≤ mZ1516 Mc Z₁
  three : T ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G)
  four : IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁)
  five : cgsIn (g1_1516 Z₁) (q1_1516 Mc Z₁) = mZ1516 Mc Z₁ ∧
    mZ1516 Mc Z₁ = g1_1516 Z₁ ⊓ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) ∧
    HypC23 (g1_1516 Z₁) (q1_1516 Mc Z₁) (mZ1516 Mc Z₁)
  six : ∀ z : G, z ∈ quasithinOmegaOneCenter T → z ≠ 1 →
    Lemma115Hyp (g1_1516 Z₁) (s1516 T Z₁) Mc z
  seven : IsUniqueM (mZ1516 Mc Z₁ ⊔ T) Mc ∧ CGS (q1_1516 Mc Z₁) ≤ Mc

structure Lemma15118Extra (T Mc M Z₁ : Subgroup G) : Prop where
  two_eq : oTwoUpper (M ⊓ Mc ⊓ g1_1516 Z₁) =
    oTwoUpper (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))
  s_normal : T ≤ Subgroup.normalizer (s1516 T Z₁ : Set G)
  mz_normal : T ≤ Subgroup.normalizer (mZ1516 Mc Z₁ : Set G)

structure Lemma15119Concl (T Mc M Z₁ V₂ : Subgroup G) : Prop where
  one : oddCoreIn (g1_1516 Z₁) = ⊥
  two : ∀ K : Subgroup G, K ≤ g1_1516 Z₁ → Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) →
    mZ1516 Mc Z₁ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ mZ1516 Mc Z₁
  three : oTwoFIn (g1_1516 Z₁) ≤ mZ1516 Mc Z₁
  four : ∀ H : Subgroup G, mZ1516 Mc Z₁ ≤ H → H ≤ g1_1516 Z₁ → oTwoFstarIn H ≤ mZ1516 Mc Z₁ →
    H = mZ1516 Mc Z₁
  five : solvRad (g1_1516 Z₁) ≤ mZ1516 Mc Z₁
  six : ∃ L : Subgroup G, L ∈ cComp (g1_1516 Z₁) ∧
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧ ¬ L ≤ mZ1516 Mc Z₁
  seven : ∀ L : Subgroup G, L ∈ cComp (g1_1516 Z₁) →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → ¬ L ≤ mZ1516 Mc Z₁ →
    oTwoUpper (M ⊓ Subgroup.centralizer (Z₁ : Set G)) ⊔ V₂ ≤ Subgroup.normalizer (L : Set G) ∧
      ⁅L, V₂⁆ ≠ ⊥

structure IsL1519 (Mc Z₁ L : Subgroup G) : Prop where
  comp : L ∈ cComp (g1_1516 Z₁)
  quasi : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  not_le : ¬ L ≤ mZ1516 Mc Z₁

structure IsL1520 (T Mc Z₁ L : Subgroup G) : Prop where
  mem : L ∈ lFamilyOf (g1_1516 Z₁) (s1516 T Z₁)
  quasi : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  not_le : ¬ L ≤ mZ1516 Mc Z₁

theorem IsL1519.isL1520 {T Mc Z₁ L : Subgroup G} (h : IsL1519 Mc Z₁ L)
    (hS : IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁)) (hH : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥) :
    IsL1520 T Mc Z₁ L :=
  ⟨⟨le_of_mem_cComp h.comp, isLocal_of_mem_cComp_of_sylow hS hH h.comp⟩, h.quasi, h.not_le⟩

@[expose] def StabilizesPartition {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : Finset (Finset (Fin n))) :
    Prop :=
  P.image (Finset.image σ) = P

@[expose] def HasWeightTwo (v : Fin 7 → ZMod 2) : Prop :=
  (Finset.univ.filter fun i => v i ≠ 0).card = 2


@[expose] def IsBender1516 (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ IsPSL 2 2 n X) ∨ (∃ e : ℕ, IsSz e X) ∨ (∃ n : ℕ, 2 ≤ n ∧ IsPSU 3 2 n X)

@[expose] def Case15120TwoA (T Mc Z₁ L : Subgroup G) : Prop :=
  IsBlock2 (L ⊔ s1516 T Z₁) L ∧ (IsAltType L 5 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∧
    IsBorelOfBlock L (mZ1516 Mc Z₁ ⊓ L)

@[expose] def Case15120TwoB (T Mc Z₁ L : Subgroup G) : Prop :=
  (IsAlt 7 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
      IsPSL 3 2 1 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
      IsAlt 6 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
      IsPSU 3 3 1 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) ∧
    (L ∈ cComp (g1_1516 Z₁) →
      IsAltBlockType L 7 ∨ IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) ∧
    (L ∈ cComp (g1_1516 Z₁) → (IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) →
      mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
        IsMaxParabolic2 L (mZ1516 Mc Z₁ ⊓ L)) ∧
    (L ∈ cComp (g1_1516 Z₁) →
      ∀ α : ↥L →* alternatingGroup (Fin 7), IsAltBlockTypeWith L 7 α →
        ∃ v : ↥(evenWeight 7), HasWeightTwo (v : Fin 7 → ZMod 2) ∧
          (∀ x : ↥L, (x : G) ∈ s1516 T Z₁ → permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v) ∧
          ∀ x : ↥L, (x : G) ∈ mZ1516 Mc Z₁ ↔ permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v)

@[expose] def Case15120TwoC (Mc Z₁ L : Subgroup G) : Prop :=
  (IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L)) ∧
    IsParabolic2 L (mZ1516 Mc Z₁ ⊓ L) ∧ mZ1516 Mc Z₁ ⊓ L ≠ L

@[expose] def Case15120ThreeA (Mc Z₁ L : Subgroup G) : Prop :=
  (IsBender1516 ↥L ∨ IsSz 3 (↥L ⧸ CFSG.pCore 2 ↥L)) ∧ IsBorelIn L (mZ1516 Mc Z₁ ⊓ L)

@[expose] def Case15120ThreeB (Mc Z₁ L : Subgroup G) : Prop :=
  ((∃ n : ℕ, 1 < n ∧ IsPSL 3 2 n ↥L) ∨ (∃ n : ℕ, 1 < n ∧ IsPSp4 2 n ↥L) ∨
      IsPSL 3 2 2 (↥L ⧸ CFSG.pCore 2 ↥L)) ∧
    (IsBorelIn L (mZ1516 Mc Z₁ ⊓ L) ∨ IsMaxParabolic2 L (mZ1516 Mc Z₁ ⊓ L))

@[expose] def Case15120ThreeC (T Mc Z₁ L : Subgroup G) : Prop :=
  (IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) ∧
    mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G)

@[expose] def Case15120ThreeD (T Mc Z₁ L : Subgroup G) : Prop :=
  (IsSporadic .M11 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .M12 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
      IsSporadic .M22 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .M23 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
      IsSporadic .M24 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .J2 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
      IsSporadic .HS (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .He (↥L ⧸ CFSG.pCore 2 ↥L) ∨
      IsSporadic .Ru (↥L ⧸ CFSG.pCore 2 ↥L)) ∧
    mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G)

@[expose] def Case15120ThreeE (T Mc Z₁ L : Subgroup G) : Prop :=
  (IsPSL 4 2 1 ↥L ∨ IsPSL 5 2 1 ↥L) ∧ IsParabolic2 L (mZ1516 Mc Z₁ ⊓ L) ∧
    mZ1516 Mc Z₁ ⊓ L ≠ L ∧
    L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G) ≤ mZ1516 Mc Z₁ ⊓ L

structure Lemma15120Concl (T Mc M Z₁ L : Subgroup G) : Prop where
  sylow : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L
  one : ¬ L ≤ M
  two : CharTwo L → ⁅L, thompsonJ (s1516 T Z₁)⁆ = L ∧
    (Case15120TwoA T Mc Z₁ L ∨ Case15120TwoB T Mc Z₁ L ∨ Case15120TwoC Mc Z₁ L)
  three : IsComponentOf L (g1_1516 Z₁) → IsPGroup 2 (Subgroup.center ↥L) ∧
    (Case15120ThreeA Mc Z₁ L ∨ Case15120ThreeB Mc Z₁ L ∨ Case15120ThreeC T Mc Z₁ L ∨
      Case15120ThreeD T Mc Z₁ L ∨ Case15120ThreeE T Mc Z₁ L)

@[expose] def Lemma15121Concl (Mc Z₁ L : Subgroup G) : Prop :=
  L ∈ cComp (g1_1516 Z₁) →
    ((CharTwo L ∧ IsBlock2 (g1_1516 Z₁) L ∧ (IsAltType L 5 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type L n)) ∨
      (IsComponentOf L (g1_1516 Z₁) ∧
        (IsBender1516 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ (∃ n : ℕ, IsPSL 3 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
          ∃ n : ℕ, IsPSp4 2 n (↥L ⧸ CFSG.pCore 2 ↥L)))) →
    L ≤ mZ1516 Mc Z₁

@[expose] def CentS15122 (T M Z₁ L : Subgroup G) : Prop :=
  s1516 T Z₁ ⊓ Subgroup.centralizer (oPrimeResidualOf 3 (M ⊓ L) : Set G) =
    s1516 T Z₁ ⊓ Subgroup.centralizer (L : Set G)

@[expose] def Case15122One (T M Mc Z₁ L : Subgroup G) : Prop :=
  IsAltBlockType L 7 ∧ (M ⊓ L) ⊔ (mZ1516 Mc Z₁ ⊓ L) = L ∧ M ⊓ L < L ∧
    ∃ α : ↥L →* alternatingGroup (Fin 7), IsAltBlockTypeWith L 7 α ∧
      (∃ P : Finset (Finset (Fin 7)), IsPartitionOfType P {2, 2, 2, 1} ∧
        (∀ x : ↥L, (x : G) ∈ s1516 T Z₁ →
          StabilizesPartition (α x : Equiv.Perm (Fin 7)) P) ∧
        ∀ x : ↥L, StabilizesPartition (α x : Equiv.Perm (Fin 7)) P → (x : G) ∈ M) ∧
      ∃ v : ↥(evenWeight 7), HasWeightTwo (v : Fin 7 → ZMod 2) ∧
        (∀ x : ↥L, (x : G) ∈ s1516 T Z₁ → permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v) ∧
        ∀ x : ↥L, (x : G) ∈ mZ1516 Mc Z₁ ↔ permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v

@[expose] def Case15122Two (T M Mc Z₁ L : Subgroup G) : Prop :=
  (IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) ∧
    mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
    IsMaxParabolic2 L (mZ1516 Mc Z₁ ⊓ L) ∧ IsMaxParabolic2 L (M ⊓ L) ∧
    mZ1516 Mc Z₁ ⊓ L ≠ M ⊓ L ∧ CentS15122 T M Z₁ L

@[expose] def Case15122Three (M Mc Z₁ L : Subgroup G) : Prop :=
  CharTwo L ∧ (IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L)) ∧
    IsParabolic2 L (mZ1516 Mc Z₁ ⊓ L) ∧ mZ1516 Mc Z₁ ⊓ L ≠ L ∧
    IsParabolic2 L (M ⊓ L) ∧ M ⊓ L ≠ L ∧ (mZ1516 Mc Z₁ ⊓ L) ⊔ (M ⊓ L) = L

@[expose] def Case15122Four (T M Mc Z₁ L : Subgroup G) : Prop :=
  (IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) ∧
    mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G) ∧
    IsMaxParabolic2 L (mZ1516 Mc Z₁ ⊓ L) ∧ IsMaxParabolic2 L (M ⊓ L) ∧
    mZ1516 Mc Z₁ ⊓ L ≠ M ⊓ L ∧ CentS15122 T M Z₁ L

@[expose] def Case15122Five (T M Mc Z₁ L : Subgroup G) : Prop :=
  (IsSporadic .J2 (↥L ⧸ Subgroup.center ↥L) ∨ IsSporadic .He (↥L ⧸ Subgroup.center ↥L) ∨
      IsSporadic .M12 (↥L ⧸ Subgroup.center ↥L) ∨ IsSporadic .M22 (↥L ⧸ Subgroup.center ↥L) ∨
      IsSporadic .M23 (↥L ⧸ Subgroup.center ↥L) ∨ IsSporadic .M24 (↥L ⧸ Subgroup.center ↥L)) ∧
    mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G) ∧
    CentS15122 T M Z₁ L

@[expose] def Case15122Six (T Mc Z₁ L : Subgroup G) : Prop :=
  IsSporadic .M11 ↥L ∧
    mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G) ∧
    oTwoUpper (g1_1516 Z₁ ⊓ Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G)) ≤
      Subgroup.centralizer (L : Set G)

@[expose] def Case15122Seven (T M Mc Z₁ L : Subgroup G) : Prop :=
  (IsPSL 4 2 1 ↥L ∨ IsPSL 5 2 1 ↥L) ∧ (mZ1516 Mc Z₁ ⊓ L) ⊔ (M ⊓ L) = L ∧
    IsParabolic2 L (mZ1516 Mc Z₁ ⊓ L) ∧ mZ1516 Mc Z₁ ⊓ L ≠ L ∧
    L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G) ≤ mZ1516 Mc Z₁ ⊓ L ∧
    IsParabolic2 L (M ⊓ L) ∧ M ⊓ L ≠ L ∧ CentS15122 T M Z₁ L

@[expose] def Lemma15122Concl (T Mc M Z₁ L : Subgroup G) : Prop :=
  Case15122One T M Mc Z₁ L ∨ Case15122Two T M Mc Z₁ L ∨ Case15122Three M Mc Z₁ L ∨
    Case15122Four T M Mc Z₁ L ∨ Case15122Five T M Mc Z₁ L ∨ Case15122Six T Mc Z₁ L ∨
    Case15122Seven T M Mc Z₁ L

@[expose] def Lemma15123Concl (T Mc M : Subgroup G) : Prop :=
  ∀ p : ℕ, (p = 3 ∨ p = 5) → Ce15Six T Mc M p →
    p = 3 ∧ Nonempty (↥(autOn M (V154 T Mc M)) ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2))

structure Lemma15124Concl (T Mc M Z₁ V₁ V₂ L : Subgroup G) : Prop where
  one : Ce15Four T Mc M ∨ Ce15Six T Mc M 3
  z1_le : Z₁ ≤ V₁
  two : ¬ IsLnBlock L 3
  three : ∀ Y₀ : Subgroup G, oTwoUpper Y₀ = Y₀ → Y₀ ≤ oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) →
    ¬ Y₀ ≤ mZ1516 Mc Z₁ →
      ⁅V₂, Y₀⁆ = V₂ ∧ (Y₀ ⊓ Subgroup.centralizer (V₂ : Set G)).relIndex Y₀ = 3
  three' : ⁅V₂, oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁)⁆ = V₂
  four : V₁ ≤ s1516 T Z₁ ⊓ Subgroup.centralizer (oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) : Set G)

structure Lemma15125Concl (T Z₁ V₁ L : Subgroup G) : Prop where
  one : L = oPrimeResidualOf 3 (g1_1516 Z₁)
  two : ¬ IsSporadic .M11 ↥L
  three : ¬ V₁ ≤ Subgroup.centralizer (L : Set G)
  four : (Subgroup.centralizer (V₁ : Set G) ⊓ s1516 T Z₁).relIndex (s1516 T Z₁) = 2
  five : ¬ IsAltBlockType L 7
  six : (s1516 T Z₁).relIndex T = 2

@[expose] def Lemma15126Concl (L : Subgroup G) : Prop :=
  CharTwo L ∧ (IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L))

@[expose] def uOf1527 (Z₂ L : Subgroup G) : Subgroup G := conjClosure Z₂ L

@[expose] def uLOf1527 (Z₂ L : Subgroup G) : Subgroup G := ⁅uOf1527 Z₂ L, L⁆

@[expose] def zUOf1528 (Z₂ L : Subgroup G) : Subgroup G :=
  (Z₂ ⊔ (uOf1527 Z₂ L ⊓ Subgroup.centralizer (L : Set G))) ⊓ uLOf1527 Z₂ L

@[expose] def Alt15127 {V : Type} [CommGroup V] (Ls : Subgroup (MulAut V)) (UL : Subgroup V) :
    Prop :=
  (∃ Z : Subgroup V, Z ≤ fixV Ls ⊓ UL ∧ Nat.card Z ≤ 2 ∧ SLExteriorTwo Ls UL Z 4) ∨
    SLExteriorTwo Ls UL ⊥ 5 ∨ (∃ n : ℕ, SumNatDual Ls UL n) ∨
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ∃ k : ℕ, 1 ≤ k ∧ k ≤ n - 1 ∧
      DirectSumOfCopies Ls UL ⊥ (FFModel.nat (StatedSL n (ZMod 2))) k

@[expose] def Lemma15127Concl (Z₂ L : Subgroup G) : Prop :=
  ∃ hU : IsElemAbelian 2 (uOf1527 Z₂ L),
    @Alt15127 ↥(uOf1527 Z₂ L) (commGroupOfElemAbelian hU) (autOn L (uOf1527 Z₂ L))
      ((uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L))

@[expose] def IsNaturalUL (L UL : Subgroup G) : Prop :=
  ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
    IsNaturalSection L UL ⊥ ((L ⊓ Subgroup.centralizer (UL : Set G)).subgroupOf L)
      (StatedSL n (ZMod 2))

@[expose] def Lemma15128Concl (T Mc Z₁ Z₂ L : Subgroup G) : Prop :=
  IsNaturalUL L (uLOf1527 Z₂ L) ∧ Nat.card (zUOf1528 Z₂ L) = 2 ∧
    mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
    mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.normalizer (zUOf1528 Z₂ L : Set G)

@[expose] def Lemma15129Concl (Z₂ L : Subgroup G) : Prop :=
  ¬ IsNaturalUL L (uLOf1527 Z₂ L)

end CFSG.Quasithin
