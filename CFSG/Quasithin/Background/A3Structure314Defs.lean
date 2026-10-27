module

public import CFSG.Quasithin.Background.A3Structure313
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def IsSylowOf (p : ℕ) {G : Type} [Group G] (S L : Subgroup G) : Prop :=
  S ≤ L ∧ IsPGroup p S ∧ ¬ p ∣ (S.subgroupOf L).index

@[expose] def IsMaxParabolicOf (p : ℕ) {G : Type} [Group G] (L P : Subgroup G) : Prop :=
  (P ≤ L ∧ ∃ S : Subgroup G, IsSylowOf p S L ∧ L ⊓ Subgroup.normalizer (S : Set G) ≤ P) ∧
    P ≠ L ∧ ∀ Q : Subgroup G, (Q ≤ L ∧ ∃ S : Subgroup G, IsSylowOf p S L ∧
      L ⊓ Subgroup.normalizer (S : Set G) ≤ Q) → Q ≠ L → P ≤ Q → Q = P

@[expose] def IsTwoCentralInvolution {G : Type} [Group G] (L : Subgroup G) (z : G) : Prop :=
  z ∈ L ∧ orderOf z = 2 ∧ ∃ S : Subgroup G, IsSylowTwoOf S L ∧ z ∈ S ∧ ∀ s ∈ S, s * z = z * s

@[expose] def StabilizesFivePoints {G : Type} [Group G] (B L : Subgroup G) : Prop :=
  ∃ f : ↥L →* Equiv.Perm (Fin 7), f.range = alternatingGroup (Fin 7) ∧
    f.ker ≤ Subgroup.center ↥L ∧ ∃ S : Finset (Fin 7), S.card = 5 ∧
      ∀ g : ↥L, (g : G) ∈ Subgroup.normalizer (B : Set G) ↔ ∀ x ∈ S, f g x ∈ S

@[expose] def A314Statement {G : Type} [Group G] (T B L : Subgroup G) : Prop :=
  (CFSG.generalizedFitting ↥B = CFSG.pCore 2 ↥B ∧ CFSG.pCore 2 ↥B = CFSG.solvableRadical ↥B ∧
    (IsPSL 3 2 2 ↥L ∨ IsSL3 4 ↥L ∨ IsPSp4 2 2 ↥L ∨ IsG2 2 2 ↥L ∨ Is3D4 2 2 ↥L) ∧
    ∃ P, IsMaxParabolic2 L P ∧ B = perfectCore P) ∨
  (IsAlt 5 ↥B ∧ (IsAlt 7 ↥L ∨ IsHat ↥L (alternatingGroup (Fin 7))) ∧
    StabilizesFivePoints B L) ∨
  (IsAlt 5 ↥B ∧ (IsPSL 2 5 2 ↥L ∨ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
    IsPSL 2 p 1 ↥L)) ∨
  (IsSL2 5 ↥B ∧ (∃ s : Bool, IsPSLEps3 s 5 1 ↥L ∨ IsSLEps3 s 5 ↥L) ∧
    B = perfectCore (L ⊓ Subgroup.centralizer (pCoreOf 2 B : Set G))) ∨
  (IsExt ↥B (fun V _ => IsElemAbelianOfRank 5 2 V) (fun Y _ => IsSL2 5 Y) ∧
    (IsPSL 3 5 1 ↥L ∨ IsSL3 5 ↥L) ∧ ∃ P, IsMaxParabolicOf 5 L P ∧ B = perfectCore P) ∨
  (IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y) ∧ IsBlock2 (B ⊔ T) B ∧ IsLin2Type B 2 ∧
    (IsSporadic .M22 ↥L ∨ IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22))) ∨
  (IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y) ∧ IsBlock2 (B ⊔ T) B ∧ IsLin2Type B 2 ∧
    IsSporadic .M23 ↥L) ∨
  (IsAlt 5 ↥B ∧ IsSporadic .J1 ↥L ∧
    ∃ z : G, z ∈ L ∧ orderOf z = 2 ∧ B = perfectCore (L ⊓ Subgroup.centralizer ({z} : Set G))) ∨
  (IsExt ↥B (fun V _ => IsExtraspecial2 2 V) (fun Y _ => IsAlt 5 Y) ∧ IsSporadic .J2 ↥L ∧
    ∃ z : G, IsTwoCentralInvolution L z ∧ B = L ⊓ Subgroup.centralizer ({z} : Set G)) ∨
  (IsAlt 5 (ModO2 B) ∧ CFSG.generalizedFitting ↥B = CFSG.pCore 2 ↥B ∧ IsSporadic .J4 ↥L) ∨
  (IsExt ↥B (fun V _ => IsZ4StarExtra2 V) (fun Y _ => IsAlt 5 Y) ∧ IsSporadic .HS ↥L ∧
    ∃ z : G, IsTwoCentralInvolution L z ∧
      B = perfectCore (L ⊓ Subgroup.centralizer ({z} : Set G))) ∨
  (IsAlt 5 (ModO2 B) ∧ Nat.card (CFSG.pCore 2 ↥B) = 2 ^ 11 ∧ IsSporadic .Ru ↥L ∧
    ∃ z : G, IsTwoCentralInvolution L z ∧
      B = perfectCore (L ⊓ Subgroup.centralizer ({z} : Set G))) ∨
  (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ L = B ⊔ oddCoreSub L) ∨
  (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
    (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L))

@[expose] def A314ModelFacts : Prop :=
  (∀ (X : Type) [Group X] [Finite X],
    (IsPSL 3 2 1 X ∨ IsPSL 4 2 1 X ∨ IsPSL 3 2 2 X ∨ IsSporadic .M22 X ∨ IsSporadic .M24 X ∨
      ∃ f, IsSz f X) →
    IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ Nat.card X ≠ 60) ∧
  (∀ (n : ℕ) (X : Type) [Group X] [Finite X], IsPSL 2 2 n X →
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) ∧
  (∀ p : ℕ, p.Prime → 3 < p → ∀ (X : Type) [Group X] [Finite X], IsPSL 2 p 1 X →
    IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ Nat.card X = p * (p ^ 2 - 1) / 2)

structure A314Descriptors : Prop where
  lie : ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G), IsRank2LieChar2 ↥L →
    IsMaxParabolic2 L P → IsAlt 5 (ModO2 (perfectCore P)) →
      CFSG.generalizedFitting ↥(perfectCore P) = CFSG.pCore 2 ↥(perfectCore P) ∧
      (IsPSL 3 2 2 ↥L ∨ IsSL3 4 ↥L ∨ IsPSp4 2 2 ↥L ∨ IsG2 2 2 ↥L ∨ Is3D4 2 2 ↥L)
  alt7 : ∀ (G : Type) [Group G] [Finite G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → (IsAlt 7 ↥L ∨ IsHat ↥L (alternatingGroup (Fin 7))) →
    IsAlt 5 ↥B → StabilizesFivePoints B L
  sl3five : ∀ (G : Type) [Group G] [Finite G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → (∃ s : Bool, IsPSLEps3 s 5 1 ↥L ∨ IsSLEps3 s 5 ↥L) →
    IsSL2 5 ↥B → B = perfectCore (L ⊓ Subgroup.centralizer (pCoreOf 2 B : Set G))
  l3five : ∀ (G : Type) [Group G] [Finite G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → (IsPSL 3 5 1 ↥L ∨ IsSL3 5 ↥L) →
    IsExt ↥B (fun V _ => IsElemAbelianOfRank 5 2 V) (fun Y _ => IsSL2 5 Y) →
    ∃ P, IsMaxParabolicOf 5 L P ∧ B = perfectCore P
  mathieu : ∀ (G : Type) [Group G] [Finite G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L →
    (IsSporadic .M22 ↥L ∨ IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨
      IsSporadic .M23 ↥L) →
    IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y) → IsShort2 B ∧ IsLin2Type B 2
  j1 : ∀ (G : Type) [Group G] [Finite G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → IsSporadic .J1 ↥L → IsAlt 5 ↥B →
    ∃ z : G, z ∈ L ∧ orderOf z = 2 ∧ B = perfectCore (L ⊓ Subgroup.centralizer ({z} : Set G))
  j2 : ∀ (G : Type) [Group G] [Finite G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → IsSporadic .J2 ↥L →
    IsExt ↥B (fun V _ => IsExtraspecial2 2 V) (fun Y _ => IsAlt 5 Y) →
    ∃ z : G, IsTwoCentralInvolution L z ∧ B = L ⊓ Subgroup.centralizer ({z} : Set G)
  j4 : ∀ (G : Type) [Group G] [Finite G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → IsSporadic .J4 ↥L → IsAlt 5 (ModO2 B) →
    CFSG.generalizedFitting ↥B = CFSG.pCore 2 ↥B
  hs : ∀ (G : Type) [Group G] [Finite G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → IsSporadic .HS ↥L →
    IsExt ↥B (fun V _ => IsZ4StarExtra2 V) (fun Y _ => IsAlt 5 Y) →
    ∃ z : G, IsTwoCentralInvolution L z ∧
      B = perfectCore (L ⊓ Subgroup.centralizer ({z} : Set G))
  ru : ∀ (G : Type) [Group G] [Finite G] (L T B : Subgroup G), IsSylowTwoOf T L →
    B ∈ lFamily T → B ≤ L → B ≠ L → IsSporadic .Ru ↥L → IsAlt 5 (ModO2 B) →
    Nat.card (CFSG.pCore 2 ↥B) = 2 ^ 11 →
    ∃ z : G, IsTwoCentralInvolution L z ∧
      B = perfectCore (L ⊓ Subgroup.centralizer ({z} : Set G))

structure A314Facts : Prop where
  model : A314ModelFacts
  desc : A314Descriptors

end CFSG.Quasithin
