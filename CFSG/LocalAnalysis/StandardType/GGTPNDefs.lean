module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Datum

@[expose] def GGTPNLocal (p : ℕ) {X : Type*} [Group X] (A : Subgroup (MulAut X)) (σ : MulAut X)
    (J : Subgroup X) : Prop :=
  (IsElemAbelian p A ∧ σ ∈ A ∧ σ ≠ 1 ∧ IsComponentOf J (ggAutFixedSubgroup σ) ∧
    ∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
    ∀ a ∈ A, (∀ j ∈ J, a j = j) → a ∈ Subgroup.zpowers σ

theorem ggTPNLocal_three {X : Type*} [Group X] {A : Subgroup (MulAut X)} {σ : MulAut X}
    {J : Subgroup X} : GGTPNLocal 3 A σ J ↔ GGKLocal A σ J :=
  Iff.rfl

@[expose] def GGTPNLocalCore (p : ℕ) {X : Type*} [Group X] (A : Subgroup (MulAut X))
    (σ : MulAut X) (J : Subgroup X) : Prop :=
  IsElemAbelian p A ∧ σ ∈ A ∧ σ ≠ 1 ∧ IsComponentOf J (ggAutFixedSubgroup σ) ∧
    ∀ a ∈ A, ∀ j ∈ J, a j ∈ J

@[expose] def GGTPNKernel {X : Type*} [Group X] (A : Subgroup (MulAut X)) (σ : MulAut X)
    (J : Subgroup X) : Prop :=
  ∀ a ∈ A, (∀ j ∈ J, a j = j) → a ∈ Subgroup.zpowers σ

theorem ggTPNLocal_of_core_kernel {p : ℕ} {X : Type*} [Group X] {A : Subgroup (MulAut X)}
    {σ : MulAut X} {J : Subgroup X} (hc : GGTPNLocalCore p A σ J) (hk : GGTPNKernel A σ J) :
    GGTPNLocal p A σ J :=
  ⟨hc, hk⟩

@[expose] def GGTPNRank (p : ℕ) (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X)) : Prop :=
  ∃ m : ℕ, Nat.card A = p ^ m ∧
    LargeEvenTwoLocalRank p X ≤ m + (if p ∣ Nat.card (Subgroup.center X) then 1 else 0)

@[expose] def GGTPNSelfCent (p : ℕ) {X : Type*} [Group X] (A : Subgroup (MulAut X)) : Prop :=
  ∀ t : X, (∀ a ∈ A, a t = t) → t ^ p = 1 → (MulAut.conj t : MulAut X) ∈ A

@[expose] def GGTPNOnlyComp (p : ℕ) {X : Type*} [Group X] [Finite X] (σ : MulAut X)
    (J : Subgroup X) : Prop :=
  ∀ J' : Subgroup X, LargeEvenPComponent p (ggAutFixedSubgroup σ) J' → J' = J

@[expose] def GGTPNMarked (p : ℕ) (S : ℕ → LargeEvenLabel → Prop) {X : Type} [Group X]
    (A : Subgroup (MulAut X)) : Prop :=
  LargeEvenMarking X fun lab _ _ I _ θ =>
    S p lab ∧ LargeEvenHalfSplit p lab (Subgroup.center X = ⊥) ∧ GGInducedInn A θ I

@[expose] def GGTPNHalfJ (p : ℕ) {X : Type*} [Group X] (J : Subgroup X) : Prop :=
  LargeEvenMarking ↥J fun lab _ _ _ _ _ => LargeEvenHalfSplit p lab (Subgroup.center ↥J = ⊥)

@[expose] def GGTPNRankOne (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ lab.rank = 1) ∨ (lab.tag = .twD ∧ lab.rank = 2)

@[expose] def GGTPNRankJ {X : Type} [Group X] (J : Subgroup X) : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) →
    ¬ GGTPNRankOne lab

@[expose] def GGTPNCorners (p : ℕ) {X : Type} [Group X] (J : Subgroup X) : Prop :=
  (p = 7 → GGHasLabel ⟨.E6, 0, 1⟩ (X ⧸ Subgroup.center X) → GGTPNHalfJ p J) ∧
    (p = 3 → ∀ n : ℕ, GGHasLabel ⟨.twA, 5, n⟩ (X ⧸ Subgroup.center X) → GGTPNRankJ J)

@[expose] def GGTPNBasic (p : ℕ) (S : ℕ → LargeEvenLabel → Prop) {X : Type} [Group X] [Finite X]
    (A : Subgroup (MulAut X)) (σ : MulAut X) (J : Subgroup X) : Prop :=
  GGTPNLocal p A σ J ∧ p ^ 3 ≤ Nat.card A ∧ GGTPNRank p X A ∧ GGTPNSelfCent p A ∧
    GGTPNOnlyComp p σ J ∧ GGTPNMarked p S A

@[expose] def GGTPNDatum (p : ℕ) (S : ℕ → LargeEvenLabel → Prop) {X : Type} [Group X] [Finite X]
    (A : Subgroup (MulAut X)) (σ : MulAut X) (J : Subgroup X) : Prop :=
  GGTPNBasic p S A σ J ∧ GGTPNCorners p J

@[expose] def GGTPNFlat (p : ℕ) {X : Type*} [Group X] (A Ab : Subgroup (MulAut X))
    (σ : MulAut X) (J : Subgroup X) : Prop :=
  Ab ≤ A ∧ σ ∈ Ab ∧ Nat.card A ≤ p * Nat.card Ab ∧ GGTPNKernel Ab σ J

@[expose] def GGTPNNum (p n : ℕ) {X : Type*} [Group X] (A Ab : Subgroup (MulAut X)) : Prop :=
  p * Nat.card A ≤ n ∧ n ≤ p ^ 2 * Nat.card Ab

@[expose] def GGTPNBasicB (p n : ℕ) (S : ℕ → LargeEvenLabel → Prop) {X : Type} [Group X]
    [Finite X] (A Ab : Subgroup (MulAut X)) (σ : MulAut X) (J : Subgroup X) : Prop :=
  GGTPNLocalCore p A σ J ∧ GGTPNFlat p A Ab σ J ∧ p ^ 3 ≤ Nat.card Ab ∧ GGTPNRank p X Ab ∧
    GGTPNNum p n A Ab ∧ GGTPNSelfCent p A ∧ GGTPNOnlyComp p σ J ∧ GGTPNMarked p S A

@[expose] def GGTPNDatumB (p n : ℕ) (S : ℕ → LargeEvenLabel → Prop) {X : Type} [Group X]
    [Finite X] (A Ab : Subgroup (MulAut X)) (σ : MulAut X) (J : Subgroup X) : Prop :=
  GGTPNBasicB p n S A Ab σ J ∧ GGTPNCorners p J

@[expose] def GGTPNRow (p : ℕ) {X : Type} [Group X] (J : Subgroup X) : Prop :=
  ∃ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labX ∧
    GGTablePRow p labJ labX ∧ GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧
    GGHasLabel labX (X ⧸ Subgroup.center X)

@[expose] def GGTablePKnownOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X))
    (σ : MulAut X) (J : Subgroup X), GGTPNDatum p S A σ J → GGTPNRow p J

@[expose] def GGTablePKnownR (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (A Ab : Subgroup (MulAut X))
    (σ : MulAut X) (J : Subgroup X) (n : ℕ), GGTPNDatumB p n (fun _ _ => True) A Ab σ J →
    ∀ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labX →
      R p n labJ labX → GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
      GGHasLabel labX (X ⧸ Subgroup.center X) → GGTPNRow p J

@[expose] def GGTablePKnownRK (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (A Ab : Subgroup (MulAut X))
    (σ : MulAut X) (J : Subgroup X) (n : ℕ), GGTPNDatumB p n (fun _ _ => True) A Ab σ J →
    GGTPNKernel A σ J → ∀ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ →
      LargeEvenInLambda2 labX → R p n labJ labX → GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
      GGHasLabel labX (X ⧸ Subgroup.center X) → GGTPNRow p J

theorem GGTablePKnownR.toRK {R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (h : GGTablePKnownR R) : GGTablePKnownRK R :=
  fun p hp hp2 X _ _ A Ab σ J n hd _ labJ labX hJ hX hr hhJ hhX =>
    h p hp hp2 X A Ab σ J n hd labJ labX hJ hX hr hhJ hhX

end Datum

section Regimes

theorem ggTPNMarked_mono {p : ℕ} {S S' : ℕ → LargeEvenLabel → Prop} {X : Type} [Group X]
    {A : Subgroup (MulAut X)} (hS : ∀ q lab, S q lab → S' q lab) (h : GGTPNMarked p S A) :
    GGTPNMarked p S' A := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  exact ⟨hX, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, h1, h2⟩ => ⟨hs, hna, θ, hS _ _ h1, h2⟩) hraw⟩

theorem ggTPNMarked_split {p : ℕ} {S₁ S₂ : ℕ → LargeEvenLabel → Prop} {X : Type} [Group X]
    {A : Subgroup (MulAut X)} (h : GGTPNMarked p (fun q lab => S₁ q lab ∨ S₂ q lab) A) :
    GGTPNMarked p S₁ A ∨ GGTPNMarked p S₂ A := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hS, -⟩ := largeEvenRawDatum_exists hraw
  rcases hS with hs | hs
  · exact Or.inl ⟨hX, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs', hna, θ', _, h2⟩ => ⟨hs', hna, θ', hs, h2⟩) hraw⟩
  · exact Or.inr ⟨hX, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs', hna, θ', _, h2⟩ => ⟨hs', hna, θ', hs, h2⟩) hraw⟩

theorem GGTablePKnownOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ q lab, S q lab → S' q lab) (h : GGTablePKnownOn S') : GGTablePKnownOn S :=
  fun p hp hp2 X _ _ A σ J ⟨⟨hloc, hcard, hrank, hself, honly, hm⟩, hcor⟩ =>
    h p hp hp2 X A σ J ⟨⟨hloc, hcard, hrank, hself, honly, ggTPNMarked_mono hS hm⟩, hcor⟩

theorem GGTablePKnownOn.union {S₁ S₂ : ℕ → LargeEvenLabel → Prop}
    (h₁ : GGTablePKnownOn S₁) (h₂ : GGTablePKnownOn S₂) :
    GGTablePKnownOn fun q lab => S₁ q lab ∨ S₂ q lab :=
  fun p hp hp2 X _ _ A σ J ⟨⟨hloc, hcard, hrank, hself, honly, hm⟩, hcor⟩ =>
    (ggTPNMarked_split hm).elim
      (fun hm₁ => h₁ p hp hp2 X A σ J ⟨⟨hloc, hcard, hrank, hself, honly, hm₁⟩, hcor⟩)
      (fun hm₂ => h₂ p hp hp2 X A σ J ⟨⟨hloc, hcard, hrank, hself, honly, hm₂⟩, hcor⟩)

@[expose] def GGTPNTypeAGen (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∨ lab.tag = .twA) ∧ ¬ (p = 7 ∧ lab = ⟨.A, 8, 1⟩)

@[expose] def GGTPNA8Seven (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 7 ∧ lab = ⟨.A, 8, 1⟩

@[expose] def GGTPNTypeBC (_ : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .B ∨ lab.tag = .C

@[expose] def GGTPNTypeD (_ : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∨ lab.tag = .twD

@[expose] def GGTPNE6Three (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E6 ∨ lab.tag = .twE6) ∧ p = 3

@[expose] def GGTPNE6Seven (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ lab.n = 1 ∧ p = 7

@[expose] def GGTPNExcGen (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧
    ¬ GGTPNE6Three p lab ∧ ¬ GGTPNE6Seven p lab

@[expose] def GGTPNSmall (_ : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .G2der ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
    lab.tag = .twF4der ∨ lab.tag = .B2der

theorem ggTPN_regimes_cover (p : ℕ) (lab : LargeEvenLabel) :
    GGTPNTypeAGen p lab ∨ GGTPNA8Seven p lab ∨ GGTPNE6Three p lab ∨ GGTPNE6Seven p lab ∨
      GGTPNExcGen p lab ∨ GGTPNTypeBC p lab ∨ GGTPNTypeD p lab ∨ GGTPNSmall p lab := by
  obtain ⟨t, r, n⟩ := lab
  simp only [GGTPNTypeAGen, GGTPNA8Seven, GGTPNE6Three, GGTPNE6Seven, GGTPNExcGen, GGTPNTypeBC,
    GGTPNTypeD, GGTPNSmall]
  cases t <;> simp <;> tauto

theorem ggTablePKnown_of_pieces (hA : GGTablePKnownOn GGTPNTypeAGen)
    (hA8 : GGTablePKnownOn GGTPNA8Seven) (hE3 : GGTablePKnownOn GGTPNE6Three)
    (hE7 : GGTablePKnownOn GGTPNE6Seven) (hEx : GGTablePKnownOn GGTPNExcGen)
    (hBC : GGTablePKnownOn GGTPNTypeBC) (hD : GGTablePKnownOn GGTPNTypeD)
    (hS : GGTablePKnownOn GGTPNSmall) : GGTablePKnownOn fun _ _ => True :=
  GGTablePKnownOn.mono (fun q lab _ => ggTPN_regimes_cover q lab)
    (hA.union (hA8.union (hE3.union (hE7.union (hEx.union (hBC.union (hD.union hS)))))))

end Regimes

section Transfer

theorem ggInnerDiagOn_le_normalizer {G : Type} [Group G] {Bs K : Subgroup G}
    (h : GGInnerDiagOn Bs K) : Bs ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨-, lab, -, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hN, -⟩ := largeEvenRawDatum_exists hraw
  exact hN

@[expose] def GGTPNTransferB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hc : GGConfig p B Bs x L D J), GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∃ (hJK : J ≤ K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (hx : x ∈ Subgroup.normalizer (K : Set G)),
      GGTPNDatumB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
        (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)

@[expose] def GGTPNTransferI1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
    ∃ (hJK : J ≤ K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (hx : x ∈ Subgroup.normalizer (K : Set G)),
      GGTPNDatum p (fun _ _ => True) (ggAutsOf K Bs hN)
        (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)

@[expose] def GGTPNTrLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hJK : J ≤ K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (hx : x ∈ Subgroup.normalizer (K : Set G)),
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
      GGTPNLocal p (ggAutsOf K Bs hN) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)

@[expose] def GGTPNTrLocalCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hJK : J ≤ K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (hx : x ∈ Subgroup.normalizer (K : Set G)),
      GGTPNLocalCore p (ggAutsOf K Bs hN) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)

@[expose] def GGTPNTrFlat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hc : GGConfig p B Bs x L D J), GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hJK : J ≤ K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (hx : x ∈ Subgroup.normalizer (K : Set G)),
      GGTPNFlat p (ggAutsOf K Bs hN) (ggAutsOf K B (hc.2.1.1.trans hN))
        (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)

@[expose] def GGTPNTrCard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hN : Bs ≤ Subgroup.normalizer (K : Set G)), p ^ 3 ≤ Nat.card (ggAutsOf K Bs hN)

@[expose] def GGTPNTrRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hN : Bs ≤ Subgroup.normalizer (K : Set G)), GGTPNRank p K (ggAutsOf K Bs hN)

@[expose] def GGTPNTrCardB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hc : GGConfig p B Bs x L D J), GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      p ^ 3 ≤ Nat.card (ggAutsOf K B (hc.2.1.1.trans hN))

@[expose] def GGTPNTrRankB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hc : GGConfig p B Bs x L D J), GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      GGTPNRank p K (ggAutsOf K B (hc.2.1.1.trans hN))

@[expose] def GGTPNTrNum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hc : GGConfig p B Bs x L D J), GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      GGTPNNum p (Nat.card Bs) (ggAutsOf K Bs hN) (ggAutsOf K B (hc.2.1.1.trans hN))

@[expose] def GGTPNTrSelfCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hN : Bs ≤ Subgroup.normalizer (K : Set G)), GGTPNSelfCent p (ggAutsOf K Bs hN)

@[expose] def GGTPNTrOnly : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hJK : J ≤ K) (hx : x ∈ Subgroup.normalizer (K : Set G)),
      GGTPNOnlyComp p (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)

@[expose] def GGTPNTrMarked : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∀ (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      GGTPNMarked p (fun _ _ => True) (ggAutsOf K Bs hN)

@[expose] def GGTPNTrHalfJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K → ∀ (_ : J ≤ K), p = 7 →
      GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K) → GGTPNHalfJ p (J.subgroupOf K)

@[expose] def GGTPNTrRankJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K → ∀ (_ : J ≤ K), p = 3 → ∀ n : ℕ,
      GGHasLabel ⟨.twA, 5, n⟩ (K ⧸ Subgroup.center K) → GGTPNRankJ (J.subgroupOf K)

theorem ggTPNTransferB_of_clauses (hSub : GGNbrSubcomponentInput)
    (hLocCore : GGTPNTrLocalCore) (hFlat : GGTPNTrFlat) (hCardB : GGTPNTrCardB)
    (hRankB : GGTPNTrRankB) (hNum : GGTPNTrNum) (hSelf : GGTPNTrSelfCent) (hOnly : GGTPNTrOnly)
    (hMark : GGTPNTrMarked) (hHalf : GGTPNTrHalfJ) (hRk : GGTPNTrRankJ) : GGTPNTransferB := by
  intro G _ _ p B Bs x L D J y K hc hL hK hn
  have hJK : J ≤ K := hSub G p B x L D J hc.1 hc.2.2 y K hn
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := ggInnerDiagOn_le_normalizer hK
  have hx : x ∈ Subgroup.normalizer (K : Set G) := hN (hc.2.1.1 hc.1.2.2.2.2.2.2.1.2.1)
  exact ⟨hJK, hN, hx, ⟨⟨hLocCore G p B Bs x L D J y K hc hL hK hn hJK hN hx,
      hFlat G p B Bs x L D J y K hc hL hK hn hJK hN hx,
      hCardB G p B Bs x L D J y K hc hL hK hn hN, hRankB G p B Bs x L D J y K hc hL hK hn hN,
      hNum G p B Bs x L D J y K hc hL hK hn hN, hSelf G p B Bs x L D J y K hc hL hK hn hN,
      hOnly G p B Bs x L D J y K hc hL hK hn hJK hx, hMark G p B Bs x L D J y K hc hL hK hn hN⟩,
    fun h7 hl => hHalf G p B Bs x L D J y K hc hL hK hn hJK h7 hl,
    fun h3 n hl => hRk G p B Bs x L D J y K hc hL hK hn hJK h3 n hl⟩⟩

theorem ggTPNTransferI1_of_clauses (hSub : GGNbrSubcomponentInput) (hLoc : GGTPNTrLocal)
    (hCard : GGTPNTrCard) (hRank : GGTPNTrRank) (hSelf : GGTPNTrSelfCent) (hOnly : GGTPNTrOnly)
    (hMark : GGTPNTrMarked) (hHalf : GGTPNTrHalfJ) (hRk : GGTPNTrRankJ) : GGTPNTransferI1 := by
  intro G _ _ p B Bs x L D J y K hc hL hK hn hI1
  have hJK : J ≤ K := hSub G p B x L D J hc.1 hc.2.2 y K hn
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := ggInnerDiagOn_le_normalizer hK
  have hx : x ∈ Subgroup.normalizer (K : Set G) := hN (hc.2.1.1 hc.1.2.2.2.2.2.2.1.2.1)
  exact ⟨hJK, hN, hx, ⟨⟨hLoc G p B Bs x L D J y K hc hL hK hn hJK hN hx hI1,
    hCard G p B Bs x L D J y K hc hL hK hn hN, hRank G p B Bs x L D J y K hc hL hK hn hN,
    hSelf G p B Bs x L D J y K hc hL hK hn hN, hOnly G p B Bs x L D J y K hc hL hK hn hJK hx,
    hMark G p B Bs x L D J y K hc hL hK hn hN⟩,
    fun h7 hl => hHalf G p B Bs x L D J y K hc hL hK hn hJK h7 hl,
    fun h3 n hl => hRk G p B Bs x L D J y K hc hL hK hn hJK h3 n hl⟩⟩

theorem ggHasLabel_quotCenter_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {lab : LargeEvenLabel} (h : GGHasLabel lab (A ⧸ Subgroup.center A)) :
    GGHasLabel lab (B ⧸ Subgroup.center B) :=
  ggHasLabel_of_mulEquiv
    (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (by
      ext b
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact (mem_center_iff_of_mulEquiv e a).2 ha
      · intro hb
        exact ⟨e.symm b, (mem_center_iff_of_mulEquiv e _).1 (by simpa using hb), by simp⟩)) h

theorem ggNbrTablePNbrInputI1_of_known (hT : GGTPNTransferI1)
    (hK : GGTablePKnownOn fun _ _ => True) : GGNbrTablePNbrInputI1 := by
  intro G _ _ p B Bs x L D J y K hc hL hKi hn hI1 labJ labK _ _ _ _
  obtain ⟨hJK, hN, hx, hD⟩ := hT G p B Bs x L D J y K hc hL hKi hn hI1
  have hβ := hc.1.2.2.2.2.2.1
  obtain ⟨labJ', labX', hΛJ, hΛX, hrow, hJ', hX'⟩ :=
    hK p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN) _ (J.subgroupOf K) hD
  exact ⟨labJ', labX', hΛJ, hΛX, hrow,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ', hX'⟩

theorem ggNbrTablePNbrInputI1_of_clauses_and_pieces (hSub : GGNbrSubcomponentInput)
    (hLoc : GGTPNTrLocal) (hCard : GGTPNTrCard)
    (hRank : GGTPNTrRank) (hSelf : GGTPNTrSelfCent)
    (hOnly : GGTPNTrOnly) (hMark : GGTPNTrMarked) (hHalf : GGTPNTrHalfJ) (hRk : GGTPNTrRankJ)
    (hA : GGTablePKnownOn GGTPNTypeAGen) (hA8 : GGTablePKnownOn GGTPNA8Seven)
    (hE3 : GGTablePKnownOn GGTPNE6Three) (hE7 : GGTablePKnownOn GGTPNE6Seven)
    (hEx : GGTablePKnownOn GGTPNExcGen) (hBC : GGTablePKnownOn GGTPNTypeBC)
    (hD : GGTablePKnownOn GGTPNTypeD) (hS : GGTablePKnownOn GGTPNSmall) :
    GGNbrTablePNbrInputI1 :=
  ggNbrTablePNbrInputI1_of_known
    (ggTPNTransferI1_of_clauses hSub hLoc hCard hRank hSelf hOnly hMark hHalf hRk)
    (ggTablePKnown_of_pieces hA hA8 hE3 hE7 hEx hBC hD hS)

theorem ggNbrTablePNbrInputOn_of_knownR {R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (hT : GGTPNTransferB) (hK : GGTablePKnownR R) : GGNbrTablePNbrInputOn R := by
  intro G _ _ p B Bs x L D J y K hc hL hKi hn labJ labK hΛJ hΛK hr hhJ hhK
  obtain ⟨hJK, hN, hx, hD⟩ := hT G p B Bs x L D J y K hc hL hKi hn
  have hβ := hc.1.2.2.2.2.2.1
  obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hJ', hX'⟩ :=
    hK p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN) (ggAutsOf K B (hc.2.1.1.trans hN)) _ (J.subgroupOf K)
      (Nat.card Bs) hD labJ labK hΛJ hΛK hr
      (ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ) hhK
  exact ⟨labJ', labX', hΛJ', hΛX', hrow,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ', hX'⟩

end Transfer

section A8Leaf

@[expose] def GGTablePA8SevenKnown : Prop :=
  ∀ (x : Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))
    (E J : Subgroup (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))),
    orderOf x = 7 → x ∈ E → IsElemAbelian 7 E → 7 ^ 3 ≤ Nat.card E →
    IsComponentOf J
      (Subgroup.centralizer ({x} : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))) →
    E ≤ Subgroup.normalizer (J : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))) →
    E ⊓ Subgroup.centralizer (J : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))) =
      Subgroup.zpowers x →
    (∀ J' : Subgroup (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)),
      IsComponentOf J' (Subgroup.centralizer
        ({x} : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))) → 7 ∣ Nat.card J' → J' = J) →
    GGHasLabel ⟨.A, 2, 3⟩ (J ⧸ Subgroup.center J) ∨ GGHasLabel ⟨.A, 5, 1⟩ (J ⧸ Subgroup.center J)

end A8Leaf

end CFSG.StandardType

end
