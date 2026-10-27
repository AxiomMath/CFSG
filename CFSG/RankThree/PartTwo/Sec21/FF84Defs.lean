module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

export CFSG.RankThree.PartTwo.Sec21.FF79 (Cen CenS Nor Op Opp setMul IsSylowOf ConjInto conjBy
  IsElemAb IsExtraspecialPlus IsLnq IsTypeLnq IsFullMonomial ControlsFusionIn)

open CFSG.Assembly (KProper InCatalog IsCharTwoType)
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

noncomputable abbrev Theta (H : Subgroup G) : Subgroup G := inSubgroup (aschbacherSolvableCore 3) H

@[expose] def PiStar (X A : Subgroup G) (q : ℕ) : Set (Subgroup G) :=
  {U | U ≤ X ∧ IsPGroup q U ∧ A ≤ Nor U ∧
    ∀ V : Subgroup G, U ≤ V → V ≤ X → IsPGroup q V → A ≤ Nor V → V = U}

structure FF84Hyp [Finite G] (b : G) (L : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ x y : G, x * y ≠ y * x
  char2 : IsCharTwoType G
  ord : orderOf b = 3
  hLC : L ≤ Cen b
  hLN : Cen b ≤ Nor L
  quasi : IsQuasisimple L
  model : IsTypeLnq 4 2 1 L
  cyc : FFCentCyclicSylow L
  nsc : FFNotStronglyClosed b
  rank : localRank 3 G = localRank 3 ↥(Cen b)
  i : ∀ p : ℕ, p.Prime → 3 < p → localRank p G ≤ 2
  ii₁ : FFSylowCommutatorOdd b
  ii₂ : FFSylowHyperplaneOdd b
  iii : KProper InCatalog G

@[expose] def FF84_2_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L : Subgroup G), FF84Hyp b L →
    ∀ B : Subgroup G, IsSylowOf 3 B (Cen b) →
    ∃ b₁ ∈ B ⊓ L, ∃ b₂ ∈ B ⊓ L, B ⊓ L = Subgroup.closure {b₁, b₂} ∧
      IsFullMonomial B b b₁ b₂ ∧ ControlsFusionIn B

@[expose] def FF84_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ : G), FF84Hyp b L →
    IsSylowOf 3 B (Cen b) → b₁ ∈ B ⊓ L → b₂ ∈ B ⊓ L → B ⊓ L = Subgroup.closure {b₁, b₂} →
    IsFullMonomial B b b₁ b₂ →
    Nat.card ↥(L ⊓ Cen b₁) = 18 * Nat.card (Subgroup.center L) ∨
      ∃ K : Subgroup G, b₂ ∈ K ∧ IsTypeLnq 2 2 2 K ∧ Subgroup.zpowers b₁ ⊔ K = L ⊓ Cen b₁ ∧
        Subgroup.zpowers b₁ ⊓ K = ⊥ ∧ K ≤ Cen b₁

@[expose] def FF84_2_3 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], KCore.KGroupNonab InCatalog H →
    ∀ P P₁ P₂ : Subgroup H, IsSylowOf 3 P ⊤ → Nat.card P = 9 → Nat.card P₁ = 3 →
    Nat.card P₂ = 3 → P₁ ⊔ P₂ = P → P₁ ⊓ P₂ = ⊥ →
    IsStronglyClosedIn P (P₁ : Set H) → IsStronglyClosedIn P (P₂ : Set H) →
    Subgroup.normalClosure (P₁ : Set H) ⊓ Subgroup.normalClosure (P₂ : Set H) ≤ pPrimeCore 3 H

structure FF84Sec3 [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ : G) : Prop where
  hyp : FF84Hyp b L
  sylB : IsSylowOf 3 B (Cen b)
  hb₁ : b₁ ∈ B ⊓ L
  hb₂ : b₂ ∈ B ⊓ L
  gen : B ⊓ L = Subgroup.closure {b₁, b₂}
  mono : IsFullMonomial B b b₁ b₂
  fus : ControlsFusionIn B
  caseA : Nat.card ↥(L ⊓ Cen b₁) = 18 * Nat.card (Subgroup.center L)

@[expose] def FF84_3_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ : G),
    FF84Sec3 b L B b₁ b₂ → Opp 3 (Cen b) = ⊥ ∧ Subgroup.center L = ⊥

@[expose] def FF84_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ : G),
    FF84Sec3 b L B b₁ b₂ →
    let S := Opp 3 (Cen (b₁ * b₂))
    IsPGroup 2 S ∧ IsElementaryAbelian 2 S ∧ S ⊓ Cen b = ⊥ ∧
      setMul S (Nor (Subgroup.closure {b, b₁ * b₂})) = Nor (Subgroup.zpowers (b₁ * b₂))

@[expose] def FF84_3_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ : G),
    FF84Sec3 b L B b₁ b₂ →
    Opp 3 (Cen (b₁ * b₂)) = ⊥ ∧ Nor (Subgroup.zpowers (b₁ * b₂)) ≤ Nor (Subgroup.zpowers b) ∧
      ∀ U : Subgroup G, IsPGroup 2 U → B ≤ Nor U →
        (U ⊓ Cen b₁) ⊔ (U ⊓ Cen b₂) ⊔ (U ⊓ Cen b) = U

@[expose] def FF84_3_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ : G),
    FF84Sec3 b L B b₁ b₂ →
    Subgroup.zpowers b ⊔ L = Cen b ∧ Subgroup.zpowers b ⊓ L = ⊥ ∧ CenS B = B

@[expose] def FF84_3_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ : G),
    FF84Sec3 b L B b₁ b₂ →
    ∃ t : G, orderOf t = 2 ∧ t ∈ CenS L ∧ t * b * t⁻¹ = b⁻¹ ∧
      Subgroup.closure {b, t} ⊔ L = Nor (Subgroup.zpowers b) ∧ Subgroup.closure {b, t} ⊓ L = ⊥

@[expose] def FF84_3_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ : G),
    FF84Sec3 b L B b₁ b₂ → ∀ t : G, orderOf t = 2 → t ∈ CenS L → t * b * t⁻¹ = b⁻¹ →
    Subgroup.closure {b, t} ⊔ L = Nor (Subgroup.zpowers b) →
    IsExtraspecialPlus 4 (Op 2 (Cen t))

structure FF84Sec4 [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G) : Prop where
  hyp : FF84Hyp b L
  sylB : IsSylowOf 3 B (Cen b)
  hb₁ : b₁ ∈ B ⊓ L
  hb₂ : b₂ ∈ B ⊓ L
  gen : B ⊓ L = Subgroup.closure {b₁, b₂}
  mono : IsFullMonomial B b b₁ b₂
  fus : ControlsFusionIn B
  hK : b₂ ∈ K ∧ IsTypeLnq 2 2 2 K ∧ Subgroup.zpowers b₁ ⊔ K = L ⊓ Cen b₁ ∧
    Subgroup.zpowers b₁ ⊓ K = ⊥ ∧ K ≤ Cen b₁

@[expose] def FF84_4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ →
    setMul (Opp 3 (Cen (b * b₁))) (Cen (b * b₁) ⊓ Nor (Subgroup.closure {b, b₁})) = Cen (b * b₁) ∧
      Opp 3 (Cen b) ≤ Opp 3 (Cen (b * b₁))

@[expose] def FF84_4_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ →
    Odd (Nat.card (Opp 3 (Cen (b * b₁)))) ∧ Subgroup.center L = ⊥

@[expose] def FF84_4_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ → Opp 3 (Cen b) = ⊥ ∧ Opp 3 (Cen (b * b₁)) = ⊥

@[expose] def FF84_4_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ →
    CenS B = B ∧ Subgroup.zpowers b ⊔ L = Cen b ∧ Subgroup.zpowers b ⊓ L = ⊥

@[expose] def FF84_4_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ →
    ∃ U₁ U₂ : Subgroup G, U₁ ≠ U₂ ∧ PiStar (Cen b) B 2 = {U₁, U₂} ∧ U₁ ⊓ U₂ = ⊥ ∧
      ∀ U ∈ PiStar (Cen b) B 2, IsElemAb 2 4 U ∧ IsElemAb 2 2 (U ⊓ Cen b₁) ∧
        IsElemAb 2 2 (U ⊓ Cen b₂) ∧
        (U ∈ PiStar (Cen b) (Subgroup.zpowers b₁) 2 ∨ U ∈ PiStar (Cen b) (Subgroup.zpowers b₂) 2)

@[expose] def FF84_4_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ → ∀ U ∈ PiStar (Cen b) B 2,
    let S := Op 2 (Nor U)
    S ⊓ Cen (b₁ * b₂) = ⁅S, Subgroup.zpowers b⁆ ∧ IsElemAb 2 6 S ∧ S ∈ PiStar ⊤ B 2 ∧
      (Nor S ⊓ Nor B).relIndex (Nor B) = 2 ∧
      (∃ g ∈ Nor S, conjBy g (Subgroup.zpowers b) = Subgroup.zpowers b₁) ∧
      (∃ g ∈ Nor S, conjBy g (Subgroup.zpowers b) = Subgroup.zpowers b₂) ∧
      ⁅S, Subgroup.zpowers b⁆ ≤ CenS (Subgroup.closure {b₁, b₂})

@[expose] def FF84K0Data (b : G) (S K₀ : Subgroup G) (s t : G) : Prop :=
  K₀ ≤ Nor S ∧ IsLnq 2 2 2 K₀ ∧ b ∈ K₀ ∧
    S ⊓ CenS K₀ = Subgroup.closure {s, t} ∧ s ∈ S ∧ t ∈ S ∧ s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t ∧
    S = Op 2 (Cen s) ∧ S ≠ Op 2 (Cen t) ∧ S ≠ Op 2 (Cen (s * t)) ∧
    (∀ W : Subgroup G, Subgroup.closure {s, t} ≤ W → W ≤ S → K₀ ≤ Nor W →
      W = Subgroup.closure {s, t} ∨ W = S) ∧
    setMul (Op 2 (Nor S ⊓ Cen t)) K₀ = Nor S ⊓ Cen t ∧
    S.relIndex (Op 2 (Nor S ⊓ Cen t)) = 16 ∧
    setMul S K₀ = CenS (Subgroup.closure {s, t})

@[expose] def FF84_4_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ → ∀ U ∈ PiStar (Cen b) B 2,
    let S := Op 2 (Nor U)
    (∃ (Q : Type) (_ : Group Q) (φ : ↥(Nor S) →* Q), StatedClassicalModel Q .PSU 4 2 1 ∧
      Function.Surjective φ ∧ φ.ker = S.subgroupOf (Nor S)) ∧
    ∃ (K₀ : Subgroup G) (s t : G), FF84K0Data b S K₀ s t

@[expose] def FF84MData (b : G) (S : Subgroup G) (s t : G) : Prop :=
  b ∈ Nor S ∧ s ∈ S ∧ t ∈ S ∧ s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t ∧ b ∈ Cen s ∧ b ∈ Cen t ∧
    S = Op 2 (Cen s) ∧ S ≠ Op 2 (Cen t) ∧ S ≠ Op 2 (Cen (s * t)) ∧
    CenS (Subgroup.closure {s, t}) ≤ Nor S ∧
    (∃ (Q : Type) (_ : Group Q) (φ : ↥(CenS (Subgroup.closure {s, t})) →* Q),
      StatedClassicalModel Q .PSL 2 2 2 ∧ Function.Surjective φ ∧
        φ.ker = S.subgroupOf (CenS (Subgroup.closure {s, t}))) ∧
    S ⊓ CenS (CenS (Subgroup.closure {s, t})) = Subgroup.closure {s, t} ∧
    (∀ W : Subgroup G, Subgroup.closure {s, t} ≤ W → W ≤ S →
      CenS (Subgroup.closure {s, t}) ≤ Nor W → W = Subgroup.closure {s, t} ∨ W = S) ∧
    S.relIndex (Op 2 (Nor S ⊓ Cen t)) = 16 ∧
    (∃ (Q : Type) (_ : Group Q) (φ : ↥(Nor S ⊓ Cen t) →* Q),
      StatedClassicalModel Q .PSL 2 2 2 ∧ Function.Surjective φ ∧
        φ.ker = (Op 2 (Nor S ⊓ Cen t)).subgroupOf (Nor S ⊓ Cen t))

@[expose] def FF84_4_10m : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ → ∀ U ∈ PiStar (Cen b) B 2, ∃ s t : G, FF84MData b (Op 2 (Nor U)) s t

@[expose] def FF84_4_11m : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ → ∀ U ∈ PiStar (Cen b) B 2, ∀ s t : G,
      FF84MData b (Op 2 (Nor U)) s t → IsExtraspecialPlus 4 (Op 2 (Cen t))

end CFSG.RankThree.PartTwo.Sec21.FF84
