module

public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Background.G64Statement

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

structure HypC23Cat (H R M : Subgroup G) : Prop where
  sqtk : CFSG.SectionRank.IsSQTKCat ↥H
  radical : IsTwoRadicalIn H R
  le : M ≤ H
  cgs : cgsIn H R ≤ M
  sylow : IsSylowTwoOf R (conjClosure R M)

@[expose] def AutCyclic (S P : Subgroup G) : Prop :=
  ∃ c ∈ S ⊓ Subgroup.normalizer (P : Set G), ∀ s ∈ S ⊓ Subgroup.normalizer (P : Set G),
    ∃ k : ℕ, ∀ x ∈ P, s * x * s⁻¹ = c ^ k * x * (c ^ k)⁻¹

end CFSG.Quasithin.EmptyFaithfulMultiple

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Prop134E9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H S X P : Subgroup G),
    CFSG.SectionRank.IsSQTKCat ↥H → pCoreOf 2 H ≠ ⊥ → IsSylowTwoOf S H → X ≤ H → IsXi S X →
    (pCoreOf 2 X).relIndex X = 9 → P ≤ X → IsPGroup 3 P → Nat.card P = 9 →
    H ≤ Subgroup.normalizer (X : Set G) ∨
    ∃ L : Subgroup G, L ∈ cComp H ∧ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      X ≤ conjClosure L S ∧
      (
        ((∃ t ∈ S ⊓ Subgroup.normalizer (P : Set G), t ∉ Subgroup.normalizer (L : Set G) ∧
            P = (P ⊓ L) ⊔ conjByElt t (P ⊓ L) ∧ (P ⊓ L) ⊓ conjByElt t (P ⊓ L) = ⊥) ∧
          ((∃ n : ℕ, Even n ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) ∨
            ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
              StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 q 1)) ∨
        (S ≤ Subgroup.normalizer (L : Set G) ∧
          (StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 3 1 ∨
            Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(StatedSL 3 (ZMod 3))))) ∨
        (S ≤ Subgroup.normalizer (L : Set G) ∧
          (∃ n : ℕ, Even n ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSp 2 2 n) ∧
          AutCyclic S P) ∨
        (S ≤ Subgroup.normalizer (L : Set G) ∧
          (Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
            StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∨
            StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 5 2 1)))

@[expose] def Prop134E9He : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H S X P : Subgroup G),
    CFSG.SectionRank.IsSQTKCat ↥H → pCoreOf 2 H ≠ ⊥ → IsSylowTwoOf S H → X ≤ H → IsXi S X →
    (pCoreOf 2 X).relIndex X = 9 → P ≤ X → IsPGroup 3 P → Nat.card P = 9 →
    H ≤ Subgroup.normalizer (X : Set G) ∨
    ∃ L : Subgroup G, L ∈ cComp H ∧ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      X ≤ conjClosure L S ∧
      (
        ((∃ t ∈ S ⊓ Subgroup.normalizer (P : Set G), t ∉ Subgroup.normalizer (L : Set G) ∧
            P = (P ⊓ L) ⊔ conjByElt t (P ⊓ L) ∧ (P ⊓ L) ⊓ conjByElt t (P ⊓ L) = ⊥) ∧
          ((∃ n : ℕ, Even n ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) ∨
            ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
              StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 q 1)) ∨
        (S ≤ Subgroup.normalizer (L : Set G) ∧
          (StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 3 1 ∨
            Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(StatedSL 3 (ZMod 3))))) ∨
        (S ≤ Subgroup.normalizer (L : Set G) ∧
          (∃ n : ℕ, Even n ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSp 2 2 n) ∧
          AutCyclic S P) ∨
        (S ≤ Subgroup.normalizer (L : Set G) ∧
          (Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
            StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∨
            StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 5 2 1)) ∨
        (H ≤ Subgroup.normalizer (L : Set G) ∧
          Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)))

@[expose] def C27Special : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M K V : Subgroup G), HypC23Cat H R M → K ∈ cComp H →
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → CharTwo K → ¬ K ≤ M →
    R ≤ Subgroup.normalizer (K : Set G) → V = omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) →
    (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K ∧
    (∃ hV : IsElemAbelian 2 V, ∃ A : Subgroup (MulAut ↥V), A ≤ autOn R V ∧
      @IsFFStarOffender V (commGroupOfElemAbelian hV) (autOn (K ⊔ R) V) A) ∧
    ((∃ n : ℕ, 1 < n ∧ IsLin2Type K n) ∨ IsAltType K 5 ∨ IsAltType K 7 ∨
      (∃ (n : ℕ) (α : ↥K →* alternatingGroup (Fin n)), 5 ≤ n ∧ n ≤ 8 ∧
        IsAltBlockTypeWith K n α) ∨
      IsHatA6Block K ∨ IsExcA7Block K ∨ IsAltBlockType K 6 ∨ IsSp4Block K ∨ IsG2Block K ∨
      (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 ≤ n ∧ Fintype.card F = 2 ^ n ∧
        Nonempty (↥(autOn K V) ≃* ↥(StatedSL 3 F))) ∨
      Nonempty (↥(autOn K V) ≃* ↥(StatedSL 4 (ZMod 2))) ∨
      Nonempty (↥(autOn K V) ≃* ↥(StatedSL 5 (ZMod 2))))

@[expose] def HeAutCentralizer : Prop :=
  ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) →
    ∀ S : Subgroup X, quasithinIsSylowTwo S → ∀ α β : MulAut X, (∀ s ∈ S, α s = s) →
      (∀ s ∈ S, β s = s) → α * β = β * α → α * α = 1 → β * β = 1 → α = 1 ∨ β = 1 ∨ α = β

structure Facts15420 : Prop where
  autPSL2Even : ∀ (X : Type) [Group X] (n : ℕ), StatedClassicalModel X .PSL 2 2 n →
    ∀ S : Subgroup X, quasithinIsSylowTwo S → ∀ y : X, orderOf y = 3 →
      ∀ α : MulAut X, (∀ s ∈ S, α s = s) → α y = y → α = 1
  autPSL2Odd : ∀ (X : Type) [Group X] (q : ℕ), q.Prime → q ≠ 2 →
    StatedClassicalModel X .PSL 2 q 1 → ∀ S : Subgroup X, quasithinIsSylowTwo S →
      ∀ α β γ : MulAut X, (∀ s ∈ S, α s = s) → (∀ s ∈ S, β s = s) → α ≠ 1 → β ≠ 1 → α ≠ β →
        α * β = β * α → α * α = 1 → β * β = 1 → γ * α = α * γ → γ * β = β * γ →
          γ = 1 ∨ γ = α ∨ γ = β ∨ γ = α * β
  autSmallCentralizer : ∀ (X : Type) [Group X],
    (StatedClassicalModel X .PSL 3 3 1 ∨ Nonempty (X ≃* ↥(StatedSL 3 (ZMod 3))) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
      StatedClassicalModel X .PSL 4 2 1 ∨ StatedClassicalModel X .PSL 5 2 1) →
    ∀ S : Subgroup X, quasithinIsSylowTwo S → ∀ α β : MulAut X, (∀ s ∈ S, α s = s) →
      (∀ s ∈ S, β s = s) → α * β = β * α → α * α = 1 → β * β = 1 → α = 1 ∨ β = 1 ∨ α = β
  heartAlt : ∀ m : ℕ, 5 ≤ m → m ≤ 8 → ∀ S : Subgroup (alternatingGroup (Fin m)),
    quasithinIsSylowTwo S → ∃ g : alternatingGroup (Fin m), orderOf g = 3 ∧
      ∀ x : evenWeight m,
        (∀ s ∈ S, permWeight m (s : Equiv.Perm (Fin m)) x - x ∈ constWeight m) →
          permWeight m (g : Equiv.Perm (Fin m)) x - x ∈ constWeight m
  natSp4 : ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = 4 →
    ∀ S : Subgroup ↥(StatedSp 2 F), quasithinIsSylowTwo S → ∃ g : ↥(StatedSp 2 F),
      orderOf g = 3 ∧ ∀ v : Fin 2 ⊕ Fin 2 → F,
        (∀ s ∈ S,
          ((s : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec v = v) →
          ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec v = v
  ffLinear : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
    ∀ Γ L : Subgroup (MulAut V), G64.IsQuotientOfSQTKCat ↥Γ → L ≤ Γ →
      (L.subgroupOf Γ).Normal →
      Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)) = ⊥ →
      ((∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
          Nonempty (↥L ≃* ↥(StatedSL 3 F))) ∨
        Nonempty (↥L ≃* ↥(StatedSL 4 (ZMod 2))) ∨ Nonempty (↥L ≃* ↥(StatedSL 5 (ZMod 2)))) →
      (∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A) →
      ∀ S : Subgroup (MulAut V), IsSylowTwoOf S L →
        ∃ g ∈ L, orderOf g = 3 ∧ ∀ v ∈ fixV S ⊓ commV L, g v = v
  cardPSL2Two : ∀ (X : Type) [Group X] (n : ℕ), StatedClassicalModel X .PSL 2 2 n →
    Nat.card X = 2 ^ n * (4 ^ n - 1)
  cardPSL2Odd : ∀ (X : Type) [Group X] (q : ℕ), q.Prime → q ≠ 2 →
    StatedClassicalModel X .PSL 2 q 1 → 2 * Nat.card X = q * (q ^ 2 - 1)
  cardL33 : ∀ (X : Type) [Group X],
    (StatedClassicalModel X .PSL 3 3 1 ∨ Nonempty (X ≃* ↥(StatedSL 3 (ZMod 3)))) →
      Nat.card X = 5616
  cardM11 : ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) →
    Nat.card X = 7920
  cardL42 : ∀ (X : Type) [Group X], StatedClassicalModel X .PSL 4 2 1 → Nat.card X = 20160
  cardL52 : ∀ (X : Type) [Group X], StatedClassicalModel X .PSL 5 2 1 → Nat.card X = 9999360
  cardU33 : ∀ (X : Type) [Group X], StatedClassicalModel X .PSU 3 3 1 → Nat.card X = 6048
  centerPSL : ∀ (X : Type) [Group X] (n p f : ℕ), StatedClassicalModel X .PSL n p f →
    Subgroup.center X = ⊥
  centerSL33M11 : ∀ (X : Type) [Group X],
    (Nonempty (X ≃* ↥(StatedSL 3 (ZMod 3))) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) → Subgroup.center X = ⊥
  autHe : HeAutCentralizer
  cardHe : ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) →
    Nat.card X = 4030387200
  centerHe : ∀ (X : Type) [Group X],
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) → Subgroup.center X = ⊥

end CFSG.Quasithin.EmptyFaithfulMultiple
