module

public import CFSG.Open.Catalog
public import CFSG.Open.Defs
public import CFSG.Open.GLADefs
public import CFSG.Open.StatedDefs

public section

namespace CFSG.Yardstones.Md0ec50421ce4

open CFSG.Open

noncomputable section

structure ThmAHyp (G : Type) [Group G] [Finite G] (m : ℕ) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  kProper : IsKProper G
  charTwo : IsCharTwoType G
  evenRank_ge : 4 ≤ evenRank G
  four_le : 4 ≤ m
  weakCore_above : ∀ q ∈ GLABeta (m + 1) G, GLAWeakCoreLocal G q
  weakCore_or_delta : ∀ q ∈ GLABeta m G, GLAWeakCoreLocal G q ∨ GLADeltaZero G q
  delta_witness : ∃ q ∈ GLABeta m G, GLATwoLocalRank q G = m ∧ GLADeltaZero G q

@[expose] def Mu (G : Type) [Group G] [Finite G] (m : ℕ) : Set ℕ :=
  {p | p ∈ GLABeta m G ∧ GLATwoLocalRank p G = m ∧ GLADeltaZero G p}

@[expose] def ThmACtx (G : Type) [Group G] [Finite G] (m : ℕ) : Prop :=
  ThmAHyp G m ∧ ¬ (3 ∈ Mu G m ∧ GLAGF2Type G)

variable {G : Type} [Group G]

@[expose] def IsEssential (p : ℕ) (B : Subgroup G) (x : G) : Prop :=
  x ∈ B ∧ x ≠ 1 ∧ ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
    B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥ ∧
    (p = 3 → IsEmpty (T ≃* QuaternionGroup 2))

@[expose] def IsSTriple [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  GLAIsBmax p B ∧ IsEssential p B x ∧ GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L

@[expose] def CentMod (p : ℕ) (L : Subgroup G) (g : G) : Prop :=
  g ∈ Subgroup.normalizer (L : Set G) ∧
    (⁅L, Subgroup.zpowers g⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p L

@[expose] def closureIn (I H : Subgroup G) : Subgroup G :=
  ⨆ (a : G) (_ : a ∈ H), I.map (MulAut.conj a).toMonoidHom

abbrev Triple (G : Type) [Group G] : Type := Subgroup G × G × Subgroup G

@[expose] def PumpStep (p : ℕ) (t t' : Triple G) : Prop :=
  t.2.1 ∈ t'.1 ∧
    (∀ b ∈ t'.1, ∃ u ∈ t.1 ⊓ t'.1, ∃ v ∈ t'.1, CentMod p t.2.2 v ∧ b = u * v) ∧
    t'.2.1 ∈ t'.1 ∧ CentMod p t.2.2 t'.2.1 ∧
    GLAPComponent p
      (closureIn (GLAPLayer p (t.2.2 ⊓ Subgroup.centralizer ({t'.2.1} : Set G)))
        (GLAPLayer p (Subgroup.centralizer ({t'.2.1} : Set G)))) t'.2.2

@[expose] def PumpRel [Finite G] (p : ℕ) (t t' : Triple G) : Prop :=
  IsSTriple p t.1 t.2.1 t.2.2 ∧ IsSTriple p t'.1 t'.2.1 t'.2.2 ∧ PumpStep p t t'

@[expose] def PumpLe [Finite G] (p : ℕ) (start finish : Triple G) : Prop :=
  IsSTriple p start.1 start.2.1 start.2.2 ∧
    IsSTriple p finish.1 finish.2.1 finish.2.2 ∧
    Relation.ReflTransGen (PumpRel p) start finish

theorem pumpLe_of_reflTransGen [Finite G] {p : ℕ} {start finish : Triple G}
    (hstart : IsSTriple p start.1 start.2.1 start.2.2)
    (hchain : Relation.ReflTransGen (PumpRel p) start finish) : PumpLe p start finish := by
  refine ⟨hstart, ?_, hchain⟩
  induction hchain with
  | refl => exact hstart
  | tail _ hstep _ => exact hstep.2.1

@[expose] def PumpLt [Finite G] (p : ℕ) (t t' : Triple G) : Prop :=
  ∃ s s' : Triple G, Relation.ReflTransGen (PumpRel p) t s ∧ PumpRel p s s' ∧
    ¬ CentMod p s'.2.2 s.2.1 ∧ Relation.ReflTransGen (PumpRel p) s' t'

@[expose] def IsSMax [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  IsSTriple p B x L ∧ ¬ ∃ t' : Triple G, PumpLt p (B, x, L) t'

@[expose] def IsGStar [Finite G] (p : ℕ) (B L : Subgroup G) : Prop :=
  ∃ E : Subgroup G, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
    GLAPLayer p (closureIn L B ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥

abbrev PQuot (p : ℕ) (L : Subgroup G) : Type := ↥L ⧸ GLAPPrimeCore p ↥L

abbrev PSimple (p : ℕ) (L : Subgroup G) : Type := PQuot p L ⧸ Subgroup.center (PQuot p L)

@[expose] def catalogIs (S : Type) [Group S] (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∃ i : TauCeti.CFSGIndex, Q i ∧ Nonempty (S ≃* i.Group)

@[expose] def onLie (P : TauCeti.LieTypeIndex → Prop) : TauCeti.CFSGIndex → Prop
  | .lie i => P i.1
  | _ => False

@[expose] def isAltIndex : TauCeti.CFSGIndex → Prop
  | .alternating _ _ => True
  | _ => False

@[expose] def ambiguousChev (r : ℕ) : TauCeti.CFSGIndex → Prop
  | .alternating n _ => (n = 5 ∧ (r = 2 ∨ r = 5)) ∨ (n = 6 ∧ (r = 2 ∨ r = 3)) ∨ (n = 8 ∧ r = 2)
  | .lie i =>
    match i.1 with
    | .A 1 q => (q.card = 7 ∧ r = 2) ∨ (q.card = 8 ∧ r = 3)
    | .twistedA 2 q => q.card = 3 ∧ r = 2
    | .twistedA 3 q => q.card = 2 ∧ r = 3
    | _ => False
  | _ => False

@[expose] def IsChevSimple (r : ℕ) (S : Type) [Group S] : Prop :=
  catalogIs S (onLie fun d => d.characteristic = r) ∨ catalogIs S (ambiguousChev r)

@[expose] def k2Lie (p : ℕ) : TauCeti.LieTypeIndex → Prop
  | .A 1 q => p = 3 ∧ ¬ 3 ∣ q.card
  | .A 2 q => (p = 3 ∧ q.p = 2 ∧ Even q.exponent) ∨ (p = 13 ∧ q.card = 3)
  | .B 2 q => p = 3 ∧ q.card = 8
  | .B 3 q => p = 3 ∧ q.card = 2
  | .D 4 q => p = 3 ∧ q.card = 2
  | .G2 q => p = 3 ∧ q.card = 8
  | .twistedA 2 q => p = 3 ∧ q.p = 2 ∧ Odd q.exponent ∧ 1 < q.exponent
  | .twistedA 3 q => p = 3 ∧ q.card = 8
  | .twistedA 4 q => p = 3 ∧ q.card = 2
  | .twistedA 5 q => p = 3 ∧ q.card = 2
  | .trialityD4 q => p = 3 ∧ q.card = 2
  | .tits => p = 3 ∨ p = 5
  | .reeF4 k => (p = 3 ∧ k = 1) ∨ (p = 5 ∧ k = 2)
  | .suzuki k => p = 5 ∧ k = 2
  | _ => False

@[expose] def k2Spor (p : ℕ) : TauCeti.SporadicName → Prop
  | .M11 | .J3 | .Co2 | .Co3 | .Suz | .Fi22 | .Fi23 => p = 3
  | .McL | .Ly | .B | .Th => p = 3 ∨ p = 5
  | .ONan | .Fi24Prime => p = 3 ∨ p = 7
  | .M => p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13
  | .HN | .HS | .Ru => p = 5
  | .He => p = 7
  | .J4 | .M12 => p = 11
  | _ => False

@[expose] def k2 (p : ℕ) : TauCeti.CFSGIndex → Prop
  | .alternating n _ => (p = 3 ∧ (n = 5 ∨ n = 9)) ∨ (p = 7 ∧ n = 7)
  | .lie i => k2Lie p i.1
  | .sporadic s => k2Spor p s
  | .cyclic _ _ => False

@[expose] def k3Lie : TauCeti.LieTypeIndex → Prop
  | .A 2 q => q.card % 6 = 1
  | .twistedA 2 q => q.card % 6 = 5
  | _ => False

@[expose] def k3 (p : ℕ) : TauCeti.CFSGIndex → Prop
  | .alternating n _ => p = 3 ∧ (n = 7 ∨ n = 10)
  | .lie i => p = 3 ∧ k3Lie i.1
  | .sporadic s => p = 3 ∧ (s = .M12 ∨ s = .M22)
  | .cyclic _ _ => False

@[expose] def CatalogCentralIsogeny (p : ℕ) (Q : Type) [Group Q]
    (i : TauCeti.CFSGIndex) : Prop :=
  ∃ π : Q →* i.Group, Function.Surjective π ∧
    π.ker ≤ Subgroup.center Q ∧ IsPGroup p π.ker

@[expose] def CentralCoverQuotient (U Q : Type) [Group U] [Group Q] : Prop :=
  Finite U ∧ IsQuasisimple U ∧
    ∃ π : U →* Q, Function.Surjective π ∧ π.ker ≤ Subgroup.center U

@[expose] def SimpleCoverList (Q : Type) [Group Q]
    (P : TauCeti.CFSGIndex → Prop) : Prop :=
  Subgroup.center Q = ⊥ ∧ catalogIs Q P

@[expose] def MaximalOddCover (Q : Type) [Group Q]
    (i : TauCeti.CFSGIndex) : Prop :=
  Finite Q ∧ IsQuasisimple Q ∧ IsSimpleGroup i.Group ∧
    (∃ a b : i.Group, a * b ≠ b * a) ∧
    ∃ π : Q →* i.Group, Function.Surjective π ∧
      π.ker = Subgroup.center Q ∧ IsCyclic (Subgroup.center Q) ∧
      Odd (Nat.card (Subgroup.center Q)) ∧
      ∀ (U : Type) [Group U] [Finite U], IsQuasisimple U →
        ∀ ρ : U →* i.Group, Function.Surjective ρ →
          ρ.ker = Subgroup.center U → Odd (Nat.card (Subgroup.center U)) →
          ∃ f : Q →* U, Function.Surjective f ∧ ρ.comp f = π

@[expose] def HatCoverList (Q : Type) [Group Q]
    (P : TauCeti.CFSGIndex → Prop) : Prop :=
  ∃ i : TauCeti.CFSGIndex, P i ∧ MaximalOddCover Q i ∧
    Nat.card (Subgroup.center Q) = 3

@[expose] def FullLinearCover (unitary : Bool) (d q : ℕ)
    (Q : Type) [Group Q] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K),
    if unitary then
      Nat.card K = q ^ 2 ∧ Nonempty (Q ≃* StatedSU d q K)
    else
      Nat.card K = q ∧ Nonempty (Q ≃* StatedSL d K)

@[expose] def K2LinearCover (p : ℕ) (Q : Type) [Group Q] : Prop :=
  p = 3 ∧
    ((∃ n : ℕ, 1 ≤ n ∧ Even n ∧ FullLinearCover false 3 (2 ^ n) Q) ∨
      (∃ n : ℕ, 1 < n ∧ Odd n ∧ FullLinearCover true 3 (2 ^ n) Q) ∨
      FullLinearCover true 6 2 Q)

@[expose] def K3LinearCover (p : ℕ) (Q : Type) [Group Q] : Prop :=
  p = 3 ∧ ∃ (r f : ℕ), r.Prime ∧ 1 ≤ f ∧
    (((r ^ f) % 6 = 1 ∧ FullLinearCover false 3 (r ^ f) Q) ∨
      ((r ^ f) % 6 = 5 ∧ FullLinearCover true 3 (r ^ f) Q))

@[expose] def k2HatIndex (p : ℕ) : TauCeti.CFSGIndex → Prop
  | .sporadic s => p = 3 ∧
      (s = .J3 ∨ s = .McL ∨ s = .ONan ∨ s = .Suz ∨
        s = .Fi22 ∨ s = .Fi24Prime)
  | _ => False

@[expose] def k3HatIndex (p : ℕ) : TauCeti.CFSGIndex → Prop
  | .alternating n _ => p = 3 ∧ n = 7
  | .sporadic s => p = 3 ∧ s = .M22
  | _ => False

@[expose] def K1Cover (p : ℕ) (Q : Type) [Group Q] : Prop :=
  IsQuasisimple Q ∧ IsChevSimple p (Q ⧸ Subgroup.center Q)

@[expose] def K2Cover (p : ℕ) (Q : Type) [Group Q] : Prop :=
  IsQuasisimple Q ∧
    (SimpleCoverList Q (k2 p) ∨
      SimpleCoverList Q (onLie fun d =>
        match d with
        | .C 2 q => p = 3 ∧ q.card = 8
        | .C 3 q => p = 3 ∧ q.card = 2
        | _ => False) ∨
      K2LinearCover p Q ∨ HatCoverList Q (k2HatIndex p))

@[expose] def K3Cover (p : ℕ) (Q : Type) [Group Q] : Prop :=
  IsQuasisimple Q ∧
    (SimpleCoverList Q (k3 p) ∨ K3LinearCover p Q ∨
      HatCoverList Q (k3HatIndex p))

@[expose] def K4Cover (p : ℕ) (Q : Type) [Group Q] : Prop :=
  Finite Q ∧ IsQuasisimple Q ∧ IsKGroup Q ∧
    ¬ K1Cover p Q ∧ ¬ K2Cover p Q ∧ ¬ K3Cover p Q

open Classical in
@[expose] def fullCoverLevel (p : ℕ) (Q : Type) [Group Q] : ℕ :=
  if K1Cover p Q then 1
  else if K2Cover p Q then 2
  else if K3Cover p Q then 3
  else 4

open Classical in
@[expose] def kLevel (p : ℕ) (S : Type) [Group S] : ℕ :=
  if IsChevSimple p S then 1
  else if catalogIs S (k2 p) then 2
  else if catalogIs S (k3 p) then 3
  else 4

open Classical in
@[expose] def tripleLevel [Finite G] (p : ℕ) (B L : Subgroup G) : ℕ :=
  if IsGStar p B L then 5 else min 4 (fullCoverLevel p (PQuot p L))

@[expose] def dLevel (G : Type) [Group G] [Finite G] (p : ℕ) : ℕ :=
  sSup {j | ∃ (B : Subgroup G) (x : G) (L : Subgroup G), IsSTriple p B x L ∧
    tripleLevel p B L = j}

@[expose] def IsS0 [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  IsSTriple p B x L ∧ tripleLevel p B L = dLevel G p

@[expose] def IsS0Max [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  IsS0 p B x L ∧ IsSMax p B x L ∧ B ≤ Subgroup.normalizer (L : Set G)

@[expose] def CycModSylow (p : ℕ) (L : Subgroup G) : Prop :=
  ∀ S : Subgroup G, (∀ g ∈ S, CentMod p L g) → IsPGroup p S → IsCyclic S

@[expose] def IsSStarMax [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  IsS0Max p B x L ∧ CycModSylow p L

@[expose] def CentModEqZpowers (p : ℕ) (B L : Subgroup G) (x : G) : Prop :=
  ∀ b ∈ B, CentMod p L b ↔ b ∈ Subgroup.zpowers x

@[expose] def IsSCContainment (p : ℕ) (B : Subgroup G) : Prop :=
  ∀ g ∈ Subgroup.centralizer (B : Set G), orderOf g = p → g ∈ B

@[expose] def IsSC (p : ℕ) (B : Subgroup G) : Prop :=
  IsElemAbelian p B ∧ IsSCContainment p B

theorem isSC_iff_containment {p : ℕ} {B : Subgroup G} (hB : IsElemAbelian p B) :
    IsSC p B ↔ IsSCContainment p B :=
  ⟨And.right, fun h => ⟨hB, h⟩⟩

theorem isSC_iff_containment_of_isBmax [Finite G] {p : ℕ} {B : Subgroup G}
    (hB : GLAIsBmax p B) : IsSC p B ↔ IsSCContainment p B :=
  isSC_iff_containment hB.1

theorem not_isSC_iff_not_containment_of_isBmax [Finite G] {p : ℕ} {B : Subgroup G}
    (hB : GLAIsBmax p B) : (¬ IsSC p B) ↔ ¬ IsSCContainment p B :=
  not_congr (isSC_iff_containment_of_isBmax hB)

@[expose] def IsGB [Finite G] (p : ℕ) (B L : Subgroup G) : Prop :=
  ∃ E : Subgroup G, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
    E ≤ Subgroup.normalizer (L : Set G) ∧ GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥

@[expose] def InnerDiagMarking (B L : Subgroup G) : Prop :=
  GLAMarking L (fun _ _ _ I _ θ => B ≤ Subgroup.normalizer (L : Set G) ∧
    ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)

@[expose] def SplitInnerDiagMarking (p : ℕ) (B L : Subgroup G) : Prop :=
  GLAMarking L (fun lab _ _ I _ θ => GLASplit p lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)

@[expose] def SplitInnerDiagMarking16 (p : ℕ) (B L : Subgroup G) : Prop :=
  GLAMarking L (fun lab _ _ I _ θ => GLASplit16 p lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)

@[expose] def isL2 (n : ℕ) : TauCeti.LieTypeIndex → Prop
  | .A 1 q => q.card = n
  | _ => False

@[expose] def InducesInnerMod (p : ℕ) (L : Subgroup G) (g : G) : Prop :=
  ∃ l ∈ L, ∀ y ∈ L, (l⁻¹ * y * l)⁻¹ * (g⁻¹ * y * g) ∈ GLAPPrimeCoreOf p L

@[expose] def Stage3 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  (∀ B : Subgroup G, GLAIsBmax p B → ∃ (x : G) (L : Subgroup G), IsSTriple p B x L) ∧
  (∀ B : Subgroup G, GLAIsBmax p B → ∃ B₀ : Subgroup G, B₀ ≤ B ∧ Nat.card B₀ * p = Nat.card B ∧
    ∀ b ∈ B₀, b ≠ 1 → IsEssential p B b) ∧
  (∀ B D N : Subgroup G, GLAIsBmax p B → D ≤ B → ¬ IsCyclic D → GLAIsMaxTwoLocal N → B ≤ N →
    ∃ D₀ : Subgroup G, D₀ ≤ D ∧ Nat.card D₀ * p = Nat.card D ∧
      (∀ d ∈ D₀, d ≠ 1 → IsEssential p B d) ∧
      (⁅D, pCoreOf 2 N ⊓ Subgroup.centralizer (D₀ : Set G)⁆ : Subgroup G) ≠ ⊥) ∧
  (∀ B : Subgroup G, GLAIsBmax p B →
    (∀ (x : G) (L : Subgroup G), IsEssential p B x →
      GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L → IsChevSimple p (PSimple p L)) →
    IsSC p B) ∧
  (p = 3 → ∀ (B : Subgroup G) (b : G) (L : Subgroup G), GLAIsBmax 3 B → b ∈ B → b ≠ 1 →
    GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L →
    catalogIs (PSimple 3 L) (onLie (isL2 27)) →
    B ≤ Subgroup.normalizer (L : Set G) ∧ ∀ c ∈ B, InducesInnerMod 3 L c)

@[expose] def nGen (B K : Subgroup G) : Subgroup G :=
  ⨆ (T : Subgroup G) (_ : T ≤ K ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G)), T

@[expose] def Stage4Order (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  (∀ t t' : Triple G, PumpLe p t t' →
    Nat.card (PQuot p t.2.2) ≤ Nat.card (PQuot p t'.2.2) ∧
      (PumpLt p t t' ↔ Nat.card (PQuot p t.2.2) < Nat.card (PQuot p t'.2.2))) ∧
  (∀ t t' : Triple G, PumpLe p t t' → IsSMax p t.1 t.2.1 t.2.2 →
    Nonempty (PQuot p t.2.2 ≃* PQuot p t'.2.2) ∧ IsSMax p t'.1 t'.2.1 t'.2.2 ∧
      (t.1 ≤ Subgroup.normalizer (t.2.2 : Set G) →
        t'.1 ≤ Subgroup.normalizer (t'.2.2 : Set G))) ∧
  (∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsS0 p B x L →
    ∃ (B' : Subgroup G) (x' : G) (L' : Subgroup G), IsS0Max p B' x' L' ∧
      PumpLe p (B, x, L) (B', x', L')) ∧
  (∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSTriple p B x L → CycModSylow p L →
    IsSMax p B x L) ∧
  (∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsS0 p B x L → CycModSylow p L →
    IsS0Max p B x L) ∧
  (∀ t t' : Triple G, PumpLe p t t' →
    ¬ nGen t.1 (closureIn t.2.2 t.1) ≤
        GLAPPrimeCoreOf p (Subgroup.centralizer ({t.2.1} : Set G)) →
    ¬ nGen t'.1 (closureIn t'.2.2 t'.1) ≤
        GLAPPrimeCoreOf p (Subgroup.centralizer ({t'.2.1} : Set G))) ∧
  (∀ t t' : Triple G, PumpLe p t t' →
    (IsS0 p t.1 t.2.1 t.2.2 → IsS0 p t'.1 t'.2.1 t'.2.2) ∧
      (IsS0Max p t.1 t.2.1 t.2.2 → IsS0Max p t'.1 t'.2.1 t'.2.2)) ∧
  (dLevel G p ≤ 4 → ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSTriple p B x L →
    B ≤ Subgroup.normalizer (L : Set G))

@[expose] def Stage4 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  (∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsS0 p B x L →
    Odd (Nat.card (⁅L, GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))⁆ : Subgroup G))) ∧
  (∀ (B : Subgroup G) (b : G) (K : Subgroup G), GLAIsBmax p B → b ∈ B → b ≠ 1 →
    GLAPComponent p (Subgroup.centralizer ({b} : Set G)) K → IsGStar p B K →
    Odd (Nat.card (⁅closureIn K B, GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G))⁆ :
      Subgroup G))) ∧
  (dLevel G p ≤ 2 → ∀ (B : Subgroup G) (x : G) (T : Subgroup G), GLAIsBmax p B → x ∈ B →
    x ≠ 1 → T ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) → IsPGroup 2 T →
    B ≤ Subgroup.normalizer (T : Set G) → (⁅T, B⁆ : Subgroup G) = ⊥)

@[expose] def Stage5 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  (∃ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L) ∧
  (∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsS0Max p B x L → CentModEqZpowers p B L x) ∧
  (∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsS0Max p B x L →
    (∃ T : Subgroup G, T ≤ L ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) ∧
      T ≠ ⊥ ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G)) →
    CycModSylow p L)

@[expose] def Stage6 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L →
    ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ IsChevSimple q (PSimple p L)

@[expose] def Stage7 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L →
    ¬ catalogIs (PSimple p L) isAltIndex

@[expose] def Stage8 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  (∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L →
    IsChevSimple 2 (PSimple p L)) ∧
  (p = 3 → GLATwoLocalRank 3 G = 4 → ∀ (x : G) (L : Subgroup G), orderOf x = 3 →
    GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) L →
    ¬ catalogIs (PSimple 3 L) fun i => i = .sporadic .Co2)

@[expose] def Stage9 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  (∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L →
    IsQuasisimple L ∧ IsChevSimple 2 (↥L ⧸ Subgroup.center ↥L)) ∧
  (∀ (B : Subgroup G) (x : G) (L : Subgroup G), GLAIsBmax p B → x ∈ B → x ≠ 1 →
    GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L →
    B ≤ Subgroup.normalizer (L : Set G) → CentModEqZpowers p B L x →
    IsChevSimple 2 (PSimple p L) →
    (IsS0 p B x L ∨ IsGB p B L ∨ (¬ IsSC p B ∧ IsEssential p B x)) → IsQuasisimple L)

@[expose] def StageFacts (G : Type) [Group G] [Finite G] (m : ℕ) : Prop :=
  ∀ q ∈ Mu G m, Stage3 G q ∧ Stage4Order G q ∧ Stage4 G q ∧ Stage5 G q ∧ Stage6 G q ∧
    Stage7 G q ∧ Stage8 G q ∧ Stage9 G q ∧
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax q B x L →
      GLAMarking L (fun _ _ _ _ _ _ => True)

@[expose] def Stage11 (G : Type) [Group G] [Finite G] (m : ℕ) : Prop :=
  ∀ q ∈ Mu G m, ∀ (B : Subgroup G) (x : G) (L : Subgroup G), GLAIsBmax q B → x ∈ B → x ≠ 1 →
    GLAPComponent q (Subgroup.centralizer ({x} : Set G)) L →
    B ≤ Subgroup.normalizer (L : Set G) → CentModEqZpowers q B L x → IsQuasisimple L →
    InnerDiagMarking B L →
    evenRank L ≤ m ∧
      GLAMarking L (fun lab _ _ I _ θ => GLAHalfSplit16 q lab (Subgroup.center L = ⊥) ∧
        B ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)

@[expose] def YS01 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, Stage3 G p

@[expose] def YS02 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
    Stage3 G p → Stage4Order G p

@[expose] def YS03 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
    Stage3 G p → Stage4Order G p → Stage4 G p

@[expose] def YS04 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
    Stage3 G p → Stage4Order G p → Stage4 G p → Stage5 G p

@[expose] def YS05 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
    Stage3 G p → Stage4Order G p → Stage4 G p → Stage5 G p → Stage6 G p ∧ Stage7 G p

@[expose] def YS06 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
    Stage3 G p → Stage4Order G p → Stage4 G p → Stage5 G p → Stage6 G p → Stage7 G p →
      Stage8 G p

@[expose] def YS07 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
    Stage3 G p → Stage4Order G p → Stage4 G p → Stage5 G p → Stage6 G p → Stage7 G p →
      Stage8 G p → Stage9 G p

@[expose] def YS08 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    IsChevSimple 2 (X ⧸ Subgroup.center X) → GLAMarking X (fun _ _ _ _ _ _ => True)

@[expose] def YS08Legacy : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    IsChevSimple 2 (X ⧸ Subgroup.center X) →
      CFSG.Assembly.LargeEvenMarkingLegacy X (fun _ _ _ _ _ _ => True)

@[expose] def YS09 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → ∀ p ∈ Mu G m,
    (∃ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L ∧ InnerDiagMarking B L) ∨
      (p = 3 ∧ ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
        GLASStar 3 B x L ∧ GLAStandardType 3 B x L ∧
          GLAMarking L (fun lab _ _ _ _ _ =>
            (lab.tag = .twA ∧ (lab.rank = 4 ∨ lab.rank = 5) ∧ lab.n = 1) ∨
              ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 4 ∧ lab.n = 1) ∨
              (lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1)))

@[expose] def YS10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m →
    (∀ q ∈ Mu G m, ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
      IsSStarMax q B x L ∧ InnerDiagMarking B L) →
    Stage11 G m ∧ ∃ p ∈ Mu G m, ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
      IsSStarMax p B x L ∧ SplitInnerDiagMarking p B L

@[expose] def YS11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
    ∀ p ∈ Mu G m, ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L →
      SplitInnerDiagMarking p B L →
      (∀ (y : G) (J : Subgroup G), GLAIsNeighborOf p B x L y J →
        B ≤ Subgroup.normalizer (J : Set G) ∧
          GLAMarking J (fun lab _ _ I F θ =>
            GLAHalfSplit p lab (Subgroup.center J = ⊥) ∨
              GLAPrimeField p lab I F (GLAInduces θ fun j j' => (j' : G) = x⁻¹ * j * x))) ∧
      ∀ D K : Subgroup G, GLAStdSub p B x L D K →
        (∃ (y : G) (J : Subgroup G), GLASHat p B y J ∧ GLANeighbor p x y J D K) ∧
          ∀ d ∈ D, d ≠ 1 →
            Odd (Nat.card
              (⁅K, GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G))⁆ : Subgroup G))

@[expose] def YS10Source16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m →
    (∀ q ∈ Mu G m, ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
      IsSStarMax q B x L ∧ InnerDiagMarking B L) →
    Stage11 G m ∧ ∃ p ∈ Mu G m, ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
      IsSStarMax p B x L ∧ SplitInnerDiagMarking16 p B L

@[expose] def YS11Source16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
    ∀ p ∈ Mu G m, ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L →
      SplitInnerDiagMarking16 p B L →
      (∀ (y : G) (J : Subgroup G), GLAIsNeighborOf p B x L y J →
        B ≤ Subgroup.normalizer (J : Set G) ∧
          GLAMarking J (fun lab _ _ I F θ =>
            GLAHalfSplit16 p lab (Subgroup.center J = ⊥) ∨
              GLAPrimeField p lab I F (GLAInduces θ fun j j' => (j' : G) = x⁻¹ * j * x))) ∧
      ∀ D K : Subgroup G, GLAStdSub p B x L D K →
        (∃ (y : G) (J : Subgroup G), GLASHat p B y J ∧ GLANeighbor p x y J D K) ∧
          ∀ d ∈ D, d ≠ 1 →
            Odd (Nat.card
              (⁅closureIn K (GLAPLayer p (Subgroup.centralizer ({d} : Set G))),
                GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G))⁆ : Subgroup G))

end

end CFSG.Yardstones.Md0ec50421ce4
