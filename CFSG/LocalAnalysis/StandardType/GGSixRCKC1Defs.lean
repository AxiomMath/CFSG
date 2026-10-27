module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKOpen
public import CFSG.LocalAnalysis.StandardType.GGK1Lift
public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootNormalizer
public import CFSG.LieType.Universal.Catalog
public import CFSG.LieType.Universal.Spin.Action
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKSmallDefs
public import Certificates.Certificate8064

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open CFSG.StandardType.RCKSmall (RCKSmallTag RCKSmallLabel RCKSmallEmpty)

@[expose] def RCKK1Data {Jb : Type*} [Group Jb] (rb : Jb) (Vb : Subgroup Jb) : Prop :=
  rb ∈ Vb ∧ rb ≠ 1 ∧ IsElemAbelian 2 Vb ∧ Nat.card Vb = 4 ∧
    (∀ v ∈ Vb, v ≠ 1 → ∃ j : Jb, v = j * rb * j⁻¹) ∧ K1Lift.K1b rb Vb

@[expose] def RCKK2 {X : Type} [Group X] (G₀ D J V : Subgroup X) (r : X) : Prop :=
  ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e}) →
    J ≤ K → Odd (Nat.card (Subgroup.center ↥K)) →
      pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤ Subgroup.normalizer (V : Set X)

abbrev RCKPos : Type 1 :=
  ∀ (Jb : Type) [Group Jb], (Jb ⧸ Subgroup.center Jb) → Subgroup (Jb ⧸ Subgroup.center Jb) → Prop

@[expose] def RCKRowK1 (i : GGSixRCKRow) (Pos : RCKPos) : Prop :=
  ∀ (Jb : Type) [Group Jb] [Finite Jb], Odd (Nat.card (Subgroup.center Jb)) →
    LargeEvenMarking Jb (fun lab _ _ _ _ _ => ggSixRCKLabelRow lab = i) →
    ∃ (rb : Jb ⧸ Subgroup.center Jb) (Vb : Subgroup (Jb ⧸ Subgroup.center Jb)),
      RCKK1Data rb Vb ∧ Pos Jb rb Vb

@[expose] def RCKRowK2
    (i : GGSixRCKRow) (Pos : RCKPos) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L : Subgroup X),
    GGSixRCKJRow i J →
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))) →
    p.Prime → p ≠ 2 → IsElemAbelian p A → B₁ ≤ A → D ≤ B₁ → Nat.card D = p ^ 2 →
    A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    B₁ ≤ Subgroup.normalizer (J : Set X) →
    B₁ ⊓ Subgroup.centralizer (J : Set X) = D → p ^ 4 ≤ Nat.card B₁ →
    (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) →
    p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A →
    A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ →
    B₁ ≤ Subgroup.normalizer (L : Set X) →
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) →
    IsComponentOf J (Subgroup.centralizer (D : Set X) ⊓ G₀) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    L ≤ G₀ → (∃ x ∈ D, x ≠ 1 ∧ IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})) →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)) →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    ∀ (rb : ↥J ⧸ Subgroup.center ↥J) (Vb : Subgroup (↥J ⧸ Subgroup.center ↥J)),
      RCKK1Data rb Vb → Pos ↥J rb Vb →
      ∀ (V : Subgroup X) (r : ↥J), (r : X) ∈ V → V ≤ J → IsElemAbelian 2 V → Nat.card V = 4 →
        QuotientGroup.mk' (Subgroup.center ↥J) r = rb →
        (V.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J)) = Vb →
        (∀ v ∈ V, v ≠ 1 → ∃ j ∈ J, v = j * r * j⁻¹) →
        (∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (J : Set X) →
          Y ≤ Subgroup.centralizer {(r : X)} →
          (∀ c ∈ J, c * r = r * c → c ∈ Subgroup.normalizer (Y : Set X)) →
          ∀ v ∈ V, ∀ y ∈ Y, ∃ k : ℤ, ∃ z ∈ Subgroup.centralizer (J : Set X),
            v * y * v⁻¹ * y⁻¹ = (r : X) ^ k * z) →
        RCKK2 G₀ D J V r

@[expose] def FlagAt {U X ι F : Type} [Group U] [Group X] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (B : Option ((ι → F) → (ι → F) → F)) (K R : Subgroup X) : Prop :=
  ∃ (φ : U →* X) (R' : Subgroup U) (W H : Submodule F (ι → F)),
    φ.range = K ∧ φ.ker ≤ Subgroup.center U ∧ R'.map φ = R ∧ (∀ v ∈ R', φ v = 1 → v = 1) ∧
    W ≤ H ∧
    (∀ v ∈ R', v ≠ 1 →
      LinearMap.range (Matrix.toLin' ((j v : Matrix ι ι F) - 1)) = W ∧
      LinearMap.ker (Matrix.toLin' ((j v : Matrix ι ι F) - 1)) = H) ∧
    ∀ b ∈ B, (∀ v ∈ R', ∀ m : ι → F, b m (((j v : Matrix ι ι F) - 1).mulVec m) = 0) ∨
      Module.finrank F W = 1

@[expose] def GGRootPosFlag {X : Type} [Group X] (K R : Subgroup X) : Prop :=
  (∃ m g : ℕ, 1 ≤ g ∧
    FlagAt (Matrix.SpecialLinearGroup.toGL (n := Fin (m + 1)) (R := GaloisField 2 g)) none K R) ∨
  (∃ n g : ℕ, 1 ≤ g ∧
    FlagAt (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * g)) 2 g) n).subtype none K R) ∨
  (∃ n g : ℕ, 1 ≤ g ∧
    FlagAt (CFSG.Open.StatedSp n (GaloisField 2 g)).subtype
      (some fun u v => u ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 g)).mulVec v)) K R) ∨
  (∃ n g : ℕ, 1 ≤ g ∧
    FlagAt (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 g)))
      (some (QuadraticMap.polar (Spin.quadPlus n (GaloisField 2 g)))) K R) ∨
  (∃ n g : ℕ, 1 ≤ g ∧
    FlagAt (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 g)
        (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))
      (some (QuadraticMap.polar (Spin.quadMinus n (GaloisField 2 g)
        (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))) K R)

@[expose] def RCKRootPosKnownFlag :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L : Subgroup X),
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))) →
    p.Prime → p ≠ 2 → IsElemAbelian p A → B₁ ≤ A → D ≤ B₁ → Nat.card D = p ^ 2 →
    A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    B₁ ≤ Subgroup.normalizer (J : Set X) →
    B₁ ⊓ Subgroup.centralizer (J : Set X) = D → p ^ 4 ≤ Nat.card B₁ →
    (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) →
    p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A →
    A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ →
    B₁ ≤ Subgroup.normalizer (L : Set X) →
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) →
    IsComponentOf J (Subgroup.centralizer (D : Set X) ⊓ G₀) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    L ≤ G₀ → (∃ x ∈ D, x ≠ 1 ∧ IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})) →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)) →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    ∀ R Rm : Subgroup X, R ≤ J → Rm ≤ J → GGRootPosJ J R Rm →
      ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e}) →
        J ≤ K → Odd (Nat.card (Subgroup.center ↥K)) →
          K = J ∨ GGRootPosNbr K R ∨ GGRootPosFlag K R

@[expose] def RCKRootPosKnownII :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L : Subgroup X),
    GGSixRCKJRow .II J →
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))) →
    p.Prime → p ≠ 2 → IsElemAbelian p A → B₁ ≤ A → D ≤ B₁ → Nat.card D = p ^ 2 →
    A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    B₁ ≤ Subgroup.normalizer (J : Set X) →
    B₁ ⊓ Subgroup.centralizer (J : Set X) = D → p ^ 4 ≤ Nat.card B₁ →
    (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) →
    p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A →
    A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ →
    B₁ ≤ Subgroup.normalizer (L : Set X) →
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) →
    IsComponentOf J (Subgroup.centralizer (D : Set X) ⊓ G₀) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    L ≤ G₀ → (∃ x ∈ D, x ≠ 1 ∧ IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})) →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)) →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    ∀ R Rm : Subgroup X, R ≤ J → Rm ≤ J → GGRootPosJ J R Rm → Nat.card R = 2 →
      ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e}) →
        J ≤ K → Odd (Nat.card (Subgroup.center ↥K)) → K = J ∨ GGRootPosNbr K R

@[expose] def RCKK2NbrRootSub :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K R : Subgroup X), GGRootPosNbr K R → ∀ r ∈ R, r ≠ 1 →
    pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤ Subgroup.centralizer (R : Set X)

@[expose] def RCKK2FlagRootSub : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K R : Subgroup X), GGRootPosFlag K R → ∀ r ∈ R, r ≠ 1 →
    pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤ Subgroup.centralizer (R : Set X)

@[expose] def RCKK2NbrCollinear :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K R V : Subgroup X), GGRootPosNbr K R → Nat.card R = 2 →
    ∀ r ∈ R, r ≠ 1 → r ∈ V → V ≤ K → IsElemAbelian 2 V → Nat.card V = 4 →
    (∀ v ∈ V, v ≠ 1 → ∃ k ∈ K, v = k * r * k⁻¹) →
    pCoreOf 2 (K ⊓ Subgroup.centralizer ({r} : Set X)) ≤ Subgroup.normalizer (V : Set X)

@[expose] def RCKPosRootSub :
    RCKPos := fun Jb _ _ Vb =>
  ∃ R Rm : Subgroup Jb, GGRootPosJ ⊤ R Rm ∧ Vb ≤ R.map (QuotientGroup.mk' (Subgroup.center Jb))

@[expose] def RCKPosRootElt :
    RCKPos := fun Jb _ rb _ =>
  ∃ R Rm : Subgroup Jb, GGRootPosJ ⊤ R Rm ∧ Nat.card R = 2 ∧
    rb ∈ R.map (QuotientGroup.mk' (Subgroup.center Jb))

@[expose] def RCKRowK1NS (i : GGSixRCKRow) (Pos : RCKPos) : Prop :=
  ∀ (Jb : Type) [Group Jb] [Finite Jb], Odd (Nat.card (Subgroup.center Jb)) →
    LargeEvenMarking Jb (fun lab _ _ _ _ _ => ggSixRCKLabelRow lab = i ∧ ¬ RCKSmallTag lab.tag) →
    ∃ (rb : Jb ⧸ Subgroup.center Jb) (Vb : Subgroup (Jb ⧸ Subgroup.center Jb)),
      RCKK1Data rb Vb ∧ Pos Jb rb Vb

@[expose] def RCKPosShort :
    RCKPos := fun Jb _ rb _ =>
  ∃ (t' : StatedLieTag) (m g : ℕ) (β : Fin (ggU t' m g).D.rank → ℤ) (R : Subgroup Jb),
    (t' = .PSp ∨ t' = .PSU) ∧ 1 ≤ g ∧ β ∈ (ggU t' m g).D.roots ∧
    ¬ GGLongRoot (ggU t' m g).D β ∧ 2 • β ∉ (ggU t' m g).D.roots ∧
    GGRootVia (ggU t' m g) ⊤ R β ∧ rb ∈ R.map (QuotientGroup.mk' (Subgroup.center Jb))

@[expose] def RCKPosCent (c : ℕ) : RCKPos := fun _ _ rb _ =>
  Nat.card (Subgroup.centralizer ({rb} : Set _)) = c

@[expose] def GGSixRootCommKnownLeaves :
    Prop :=
  RCKRowK1NS .I RCKPosRootSub ∧ RCKRowK1 .II RCKPosRootElt ∧ RCKRowK1 .III RCKPosShort ∧
    RCKRowK1 .IIp (RCKPosCent 96) ∧ RCKRootPosKnownFlag ∧ RCKRootPosKnownII ∧ RCKK2NbrRootSub ∧
    RCKK2FlagRootSub ∧ RCKK2NbrCollinear ∧ RCKRowK2 .III RCKPosShort ∧ RCKRowK2 .IIp (RCKPosCent 96)

end CFSG.StandardType.RCKC1
