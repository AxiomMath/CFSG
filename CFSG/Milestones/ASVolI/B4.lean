module

public import CFSG.Milestones.ASVolI.B2
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.B4L3Three
public import CFSG.Open.QuasithinH1NaturalModulesMilestoneDefs
public import CFSG.Quasithin.Background.F918E1
public import CFSG.Quasithin.Background.B412Two
public import CFSG.Quasithin.Background.A7Q528Main
public import CFSG.Quasithin.Background.JonesParshallSLn
public import CFSG.Quasithin.Vol2.Ch10SecV1H
public import CFSG.Quasithin.Background.B4L3Two

public section

namespace CFSG.ASVolI.ChB

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

section DualGen

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]

@[expose] def fixedSubF (A : Subgroup (M ≃ₗ[F] M)) : Submodule F M :=
  ⨅ a ∈ A, LinearMap.ker ((a : M →ₗ[F] M) - LinearMap.id)

@[expose] def commSubF (A : Subgroup (M ≃ₗ[F] M)) : Submodule F M :=
  ⨆ a ∈ A, LinearMap.range ((a : M →ₗ[F] M) - LinearMap.id)

@[expose] def IsQuadraticF (A : Subgroup (M ≃ₗ[F] M)) : Prop :=
  commSubF A ≤ fixedSubF A

@[expose] def dualRep : (M ≃ₗ[F] M) →* (Module.Dual F M ≃ₗ[F] Module.Dual F M) where
  toFun g := g.symm.dualMap
  map_one' := by
    ext f x
    rfl
  map_mul' g h := by
    ext f x
    rfl

end DualGen

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI.ChB

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

section ChiefSeries

variable {V : Type*} [CommGroup V]

@[expose] def HasOneNatChief (G : Subgroup (MulAut V)) (d a : ℕ) : Prop :=
  ∃ (m : ℕ) (S : ℕ → Subgroup V), (∀ i, i ≤ m → ∀ g ∈ G, ∀ x ∈ S i, g x ∈ S i) ∧
    S 0 = ⊥ ∧ S m = ⊤ ∧
    (∀ i, i < m → S i < S (i + 1) ∧ ∀ Z : Subgroup V, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) →
      S i ≤ Z → Z ≤ S (i + 1) → Z = S i ∨ Z = S (i + 1)) ∧
    ∃ j, j < m ∧ (∀ i, i < m → i ≠ j → ∀ g ∈ G, ∀ x ∈ S (i + 1), (g : MulAut V) x * x⁻¹ ∈ S i) ∧
      BinaryNaturalSL G (S (j + 1)) (S j) d a

end ChiefSeries

@[expose] noncomputable def h1CardOfRep {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι]
    [Field K] [Algebra (ZMod 2) K] (φ : G →* Matrix ι ι K) : ℕ :=
  Nat.card (groupCohomology (Rep.of (quasithinH1MatrixRep φ)) 1)

@[expose] noncomputable def orthModel6 : FFModel := FFModel.extSq (ZMod 2) 4

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI.ChB

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped TensorProduct

section B46

variable {K : Type} [Field K]

abbrev NatQ (K : Type) : Type := (Fin 3 → K) × (Fin 3 → K)

abbrev WeylM (K : Type) : Type := K × (Fin 3 → K) × (Fin 3 → K)

@[expose] def qAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (x : NatQ K) : NatQ K :=
  ((γ (0, x.1, x.2, 0)).2.1, (γ (0, x.1, x.2, 0)).2.2.1)

@[expose] def weylAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (x : WeylM K) : WeylM K :=
  ((γ (x.1, x.2.1, x.2.2, x.1)).1, (γ (x.1, x.2.1, x.2.2, x.1)).2.1,
    (γ (x.1, x.2.1, x.2.2, x.1)).2.2.1)

@[expose] def longRootFn (i j : Fin 3) (c : K) (x : quasithinZorn K) : quasithinZorn K :=
  (x.1, x.2.1 + Pi.single i (c * x.2.1 j), x.2.2.1 + Pi.single j (c * x.2.2.1 i), x.2.2.2)

@[expose] def shortRootFn (t : K) (x : quasithinZorn K) : quasithinZorn K :=
  (x.1 + t * x.2.2.1 0, x.2.1 + Pi.single 0 (t * (x.1 + x.2.2.2) + t ^ 2 * x.2.2.1 0),
    x.2.2.1 + Pi.single 2 (t * x.2.1 1) + Pi.single 1 (t * x.2.1 2), x.2.2.2 + t * x.2.2.1 0)

@[expose] def IsRootConj {V : Type} [CommGroup V] (π : ↥(quasithinG2 K) →* MulAut V)
    (f : K → quasithinZorn K → quasithinZorn K) (Z : Subgroup (MulAut V)) : Prop :=
  ∃ g : ↥(quasithinG2 K), ∀ ψ : MulAut V, ψ ∈ Z ↔
    ∃ (c : K) (φ : ↥(quasithinG2 K)),
      (∀ x, (φ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x = f c x) ∧ ψ = π g * π φ * (π g)⁻¹

@[expose] def IsLongRootSub {V : Type} [CommGroup V] (π : ↥(quasithinG2 K) →* MulAut V)
    (Z : Subgroup (MulAut V)) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ IsRootConj π (longRootFn i j) Z

@[expose] def IsShortRootSub {V : Type} [CommGroup V] (π : ↥(quasithinG2 K) →* MulAut V)
    (Z : Subgroup (MulAut V)) : Prop :=
  IsRootConj π shortRootFn Z

@[expose] def IsFPre {V : Type} [CommGroup V] (θ : V →* Multiplicative (NatQ K)) (d : ℕ)
    (X : Subgroup V) : Prop :=
  ∃ S : Submodule K (NatQ K), Module.finrank K S = d ∧
    ∀ v : V, v ∈ X ↔ Multiplicative.toAdd (θ v) ∈ S

variable {V : Type} [CommGroup V]

@[expose] def cPre (C : Subgroup V) (Z : Subgroup (MulAut V)) : Subgroup V :=
  ⨅ z ∈ Z, C.comap ((z : MulAut V).toMonoidHom * (MonoidHom.id V)⁻¹)

end B46

section B46Groups

variable {M : Type*} [Group M]

@[expose] def IsNatGL2Quot (K : Type) [Field K] (P R Y A : Subgroup M) : Prop :=
  R ≤ P ∧ A ≤ Y ∧
    P ≤ Subgroup.normalizer (Y : Set M) ∧ P ≤ Subgroup.normalizer (A : Set M) ∧
  ∃ (_ : (R.subgroupOf P).Normal) (θ' : ↥P ⧸ R.subgroupOf P ≃* GL (Fin 2) K)
      (ζ : ↥Y →* Multiplicative (Fin 2 → K)),
    Function.Surjective ζ ∧ ζ.ker = A.subgroupOf Y ∧
      ∀ (p : ↥P) (y y' : ↥Y), (y' : M) = (p : M) * (y : M) * (p : M)⁻¹ →
        ζ y' = Multiplicative.ofAdd
          (((θ' (QuotientGroup.mk p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
            (Multiplicative.toAdd (ζ y)))

@[expose] def IsNatGL2QuotTw (K : Type) [Field K] (P R Y A : Subgroup M) : Prop :=
  R ≤ P ∧ A ≤ Y ∧
    P ≤ Subgroup.normalizer (Y : Set M) ∧ P ≤ Subgroup.normalizer (A : Set M) ∧
  ∃ (_ : (R.subgroupOf P).Normal) (θ' : ↥P ⧸ R.subgroupOf P ≃* GL (Fin 2) K)
      (ζ : ↥Y →* Multiplicative (Fin 2 → K)),
    Function.Surjective ζ ∧ ζ.ker = A.subgroupOf Y ∧
      ∀ (p : ↥P) (y y' : ↥Y), (y' : M) = (p : M) * (y : M) * (p : M)⁻¹ →
        ζ y' = Multiplicative.ofAdd
          ((((θ' (QuotientGroup.mk p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) •
            (((θ' (QuotientGroup.mk p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
              (Multiplicative.toAdd (ζ y))))

@[expose] def IsSpecial2 (R Z : Subgroup M) : Prop :=
  IsPGroup 2 R ∧ centerOf R = Z ∧ ⁅R, R⁆ = Z ∧ (frattini ↥R).map R.subtype = Z ∧ Z ≠ ⊥

@[expose] def IsStrongClosedWrt (Z R G : Subgroup M) : Prop :=
  ∀ x ∈ Z, ∀ g ∈ G, g * x * g⁻¹ ∈ R → g * x * g⁻¹ ∈ Z

end B46Groups

section B46Module

variable {V : Type} [CommGroup V]

@[expose] def IsNatGL2SecMod (K : Type) [Field K] (P R : Subgroup (MulAut V)) (Y C : Subgroup V) :
    Prop :=
  R ≤ P ∧ C ≤ Y ∧
    (∀ p ∈ P, ∀ y ∈ Y, (p : MulAut V) y ∈ Y) ∧
    (∀ p ∈ P, ∀ c ∈ C, (p : MulAut V) c ∈ C) ∧
  ∃ (_ : (R.subgroupOf P).Normal) (θ' : ↥P ⧸ R.subgroupOf P ≃* GL (Fin 2) K)
      (ζ : ↥Y →* Multiplicative (Fin 2 → K)),
    Function.Surjective ζ ∧ ζ.ker = C.subgroupOf Y ∧
      ∀ (p : ↥P) (y y' : ↥Y), (y' : V) = (p : MulAut V) (y : V) →
        ζ y' = Multiplicative.ofAdd
          (((θ' (QuotientGroup.mk p) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
            (Multiplicative.toAdd (ζ y)))

section B46Cfg

variable {V : Type} [CommGroup V] {K : Type} [Field K]

@[expose] def B46Cfg1 (G L : Subgroup (MulAut V)) (θ : V →* Multiplicative (NatQ K))
    (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V)
    (A₁ : Subgroup (MulAut V)) : Prop :=
  IsFPre θ 1 V₁ ∧ P₁ = L ⊓ stabSub V₁ ∧ R₁ = pCoreOf 2 P₁ ∧ Z₁ = centerOf R₁ ∧
    V₃ = cPre (fixV L) Z₁ ∧ ∀ g : MulAut V, g ∈ A₁ ↔ g ∈ G ∧ ∀ v ∈ V₃, g v * v⁻¹ ∈ fixV L

@[expose] def B46Cfg2 (G L P₁ : Subgroup (MulAut V)) (T Z₂ P₂ R₂ : Subgroup (MulAut V))
    (V₂ : Subgroup V) : Prop :=
  IsSylowTwoOf T G ∧ T ⊓ L ≤ P₁ ∧ Z₂ = centerOf (T ⊓ L) ∧
    P₂ = L ⊓ Subgroup.normalizer (Z₂ : Set (MulAut V)) ∧ R₂ = pCoreOf 2 P₂ ∧
    V₂ = cPre (fixV L) R₂

end B46Cfg

end B46Module

section B49

variable {V : Type} [CommGroup V]

@[expose] def QuotIsoSub (G : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  ∃ φ : V ⧸ U ≃* ↥U, ∀ g ∈ G, ∀ v : V,
    ((φ (QuotientGroup.mk ((g : MulAut V) v)) : ↥U) : V) =
      (g : MulAut V) ((φ (QuotientGroup.mk v) : ↥U) : V)

@[expose] def QuotIsoDual (G : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  ∃ φ : V ⧸ U ≃* DualGrp ↥U, ∀ g ∈ G, ∀ v : V, ∀ u u' : ↥U,
    (g : MulAut V) (u' : V) = (u : V) →
      (φ (QuotientGroup.mk ((g : MulAut V) v))) u = (φ (QuotientGroup.mk v)) u'

@[expose] def SplitsOver (G : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  ∃ U' : Subgroup V, (∀ g ∈ G, ∀ u ∈ U', (g : MulAut V) u ∈ U') ∧ U ⊓ U' = ⊥ ∧ U ⊔ U' = ⊤

@[expose] def IsTransvOnQuot (U : Subgroup V) (f : ℕ) (e : MulAut V) : Prop :=
  Nat.card ↥(commV (Subgroup.zpowers e) ⊔ U) = Nat.card ↥U * 2 ^ f

@[expose] def axisPre (U : Subgroup V) (e : MulAut V) : Set V := {v | e v * v⁻¹ ∈ U}

@[expose] def IsTransvFourGrpFixedAxis (G : Subgroup (MulAut V)) (U : Subgroup V) (f : ℕ)
    (E : Subgroup (MulAut V)) : Prop :=
  E ≤ G ∧ Nat.card E = 4 ∧ (∀ e ∈ E, e ≠ 1 → IsTransvOnQuot U f e) ∧
    ∃ H : Set V, ∀ e ∈ E, e ≠ 1 → axisPre U e = H

@[expose] def InRootGroup {K : Type} [Field K] {n : ℕ} (G : Subgroup (MulAut V))
    (π : ↥(StatedSL n K) →* ↥G) (E : Subgroup (MulAut V)) : Prop :=
  ∃ (g : ↥G) (i j : Fin n), i ≠ j ∧ ∀ e ∈ E, ∃ (s : ↥(StatedSL n K)) (c : K),
    ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + Matrix.single i j c ∧
      ((π s : ↥G) : MulAut V) = (g : MulAut V)⁻¹ * e * (g : MulAut V)

@[expose] def IsSubspaceStab (G : Subgroup (MulAut V)) (U : Subgroup V) (i : ℕ)
    (P : Subgroup (MulAut V)) : Prop :=
  ∃ W : Subgroup V, W ≤ U ∧ Nat.card W = 2 ^ i ∧ P = G ⊓ stabSub W

@[expose] def IsLeviComplement (P M : Subgroup (MulAut V)) : Prop :=
  M ≤ P ∧ M ⊓ pCoreOf 2 P = ⊥ ∧ M ⊔ pCoreOf 2 P = P

end B49

section B414

variable (F : Type) [Field F]

abbrev PGL3 : Type := GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)

@[expose] noncomputable def sl3Sub : Submodule F (Matrix (Fin 3) (Fin 3) F) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 3) F F)

variable {F}

@[expose] def twAdjMat (k : ℕ) (g : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F :=
  ((g : Matrix (Fin 3) (Fin 3) F).det) ^ k •
    ((g : Matrix (Fin 3) (Fin 3) F) * M * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))

@[expose] def IsTwAdjointModule {V : Type} [CommGroup V] (G : Subgroup (MulAut V)) (α : ↥G →* PGL3 F)
    (k : ℕ) : Prop :=
  ∃ β : V ≃* Multiplicative ↥(sl3Sub F),
    ∀ (g : ↥G) (v : V) (g' : GL (Fin 3) F), (QuotientGroup.mk g' : PGL3 F) = α g →
      ((Multiplicative.toAdd (β ((g : MulAut V) v)) : ↥(sl3Sub F)) : Matrix (Fin 3) (Fin 3) F) =
        twAdjMat k g' ((Multiplicative.toAdd (β v) : ↥(sl3Sub F)) : Matrix (Fin 3) (Fin 3) F)

@[expose] def TwAdjointIntertwines {V : Type} [CommGroup V] (G : Subgroup (MulAut V))
    (α : ↥G →* PGL3 F) (k : ℕ) (β : V ≃* Multiplicative ↥(sl3Sub F)) : Prop :=
  ∀ (element : ↥G) (vector : V) (representative : GL (Fin 3) F),
    (QuotientGroup.mk representative : PGL3 F) = α element →
      ((Multiplicative.toAdd (β ((element : MulAut V) vector)) : ↥(sl3Sub F)) :
        Matrix (Fin 3) (Fin 3) F) =
          twAdjMat k representative ((Multiplicative.toAdd (β vector) : ↥(sl3Sub F)) :
            Matrix (Fin 3) (Fin 3) F)

@[expose] def AdjointScalarCompatible {V M : Type} [CommGroup V] [AddCommGroup M] [Module F M]
    (β : V ≃* Multiplicative ↥(sl3Sub F)) (W : Subgroup V)
    (Φ : Multiplicative M ≃* ↥W) : Prop :=
  ∀ (scalar : F) (vector : M),
    β ((Φ (Multiplicative.ofAdd (scalar • vector)) : ↥W) : V) =
      Multiplicative.ofAdd (scalar • Multiplicative.toAdd
        (β ((Φ (Multiplicative.ofAdd vector) : ↥W) : V)))

@[expose] noncomputable def tensAct (A B : Matrix (Fin 2) (Fin 2) F) :
    (Fin 2 → F) ⊗[F] (Fin 2 → F) →ₗ[F] (Fin 2 → F) ⊗[F] (Fin 2 → F) :=
  TensorProduct.map (Matrix.toLin' A) (Matrix.toLin' B)

@[expose] noncomputable def tensActOf {K : Type} [Group K] (π₁ π₂ : K →* ↥(StatedSL 2 F)) (k : K) :
    (Fin 2 → F) ⊗[F] (Fin 2 → F) →ₗ[F] (Fin 2 → F) ⊗[F] (Fin 2 → F) :=
  tensAct (((π₁ k : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
    (((π₂ k : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)

@[expose] def TensorUniserialTrivEnds {K : Type} [Group K] (π₁ π₂ : K →* ↥(StatedSL 2 F)) : Prop :=
  let inv : Submodule F ((Fin 2 → F) ⊗[F] (Fin 2 → F)) → Prop :=
    fun A => ∀ k : K, ∀ m ∈ A, tensActOf π₁ π₂ k m ∈ A
  (∀ A B, inv A → inv B → A ≤ B ∨ B ≤ A) ∧
  (∃ A₀, inv A₀ ∧ A₀ ≠ ⊥ ∧ (∀ k : K, ∀ m ∈ A₀, tensActOf π₁ π₂ k m = m) ∧
    ∀ A, inv A → A ≠ ⊥ → A₀ ≤ A) ∧
  (∃ A₁, inv A₁ ∧ A₁ ≠ ⊤ ∧ (∀ k : K, ∀ m, tensActOf π₁ π₂ k m - m ∈ A₁) ∧
    ∀ A, inv A → A ≠ ⊤ → A ≤ A₁)

@[expose] def IsTensorOfNaturalsUniserialVia {V : Type} [CommGroup V]
    (β : V ≃* Multiplicative ↥(sl3Sub F)) (K : Subgroup (MulAut V)) (W : Subgroup V) : Prop :=
  ∃ π₁ π₂ : ↥K →* ↥(StatedSL 2 F), Function.Surjective π₁ ∧ Function.Surjective π₂ ∧
    ∃ Φ : Multiplicative ((Fin 2 → F) ⊗[F] (Fin 2 → F)) ≃* ↥W,
      (∀ (element : ↥K) (vector : (Fin 2 → F) ⊗[F] (Fin 2 → F)),
        ((Φ (Multiplicative.ofAdd (tensActOf π₁ π₂ element vector)) : ↥W) : V) =
          (element : MulAut V) ((Φ (Multiplicative.ofAdd vector) : ↥W) : V)) ∧
      AdjointScalarCompatible β W Φ ∧ TensorUniserialTrivEnds π₁ π₂

@[expose] def IsNaturalSL2ViaAdjoint {V : Type} [CommGroup V]
    (β : V ≃* Multiplicative ↥(sl3Sub F)) (K : Subgroup (MulAut V)) (W : Subgroup V) : Prop :=
  ∃ π : ↥K →* ↥(StatedSL 2 F), Function.Surjective π ∧
    ∃ Φ : Multiplicative (Fin 2 → F) ≃* ↥W,
      (∀ (element : ↥K) (vector : Fin 2 → F),
        ((Φ (natAct (StatedSL 2 F) (π element) (Multiplicative.ofAdd vector)) : ↥W) : V) =
          (element : MulAut V) ((Φ (Multiplicative.ofAdd vector) : ↥W) : V)) ∧
      AdjointScalarCompatible β W Φ

end B414

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

@[expose] def B_4_7 : Prop :=
  (∀ (F : Type) [Field F] [CharP F 2] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (A : Subgroup (V ≃ₗ[F] V)), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
    (Function.Bijective (Submodule.dualAnnihilator : Submodule F V → Submodule F (Module.Dual F V)) ∧
      (∀ U U' : Submodule F V, U ≤ U' ↔ U'.dualAnnihilator ≤ U.dualAnnihilator) ∧
      (∀ (g : V ≃ₗ[F] V) (U : Submodule F V),
        (U.map (g : V →ₗ[F] V)).dualAnnihilator =
          U.dualAnnihilator.map ((dualRep g : Module.Dual F V ≃ₗ[F] Module.Dual F V) :
            Module.Dual F V →ₗ[F] Module.Dual F V)) ∧
      (∀ U : Submodule F V, Module.finrank F ↥(U.dualAnnihilator) + Module.finrank F ↥U =
        Module.finrank F V)) ∧
    ((commSubF A).dualAnnihilator =
        fixedSubF (M := Module.Dual F V) (A.map (dualRep (F := F) (M := V))) ∧
      (fixedSubF A).dualAnnihilator =
        commSubF (M := Module.Dual F V) (A.map (dualRep (F := F) (M := V)))) ∧
    (IsQuadraticF A ↔ IsQuadraticF (M := Module.Dual F V) (A.map (dualRep (F := F) (M := V))))) ∧
  (∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ A : Subgroup (MulAut V), IsElemAbelian2 A → A ≠ ⊥ → IsQuadratic A →
      rk (commV A) ≤ 2 * rk A → qOf (dualSub A) ≤ 2)

section BurnsideB4a

private theorem burnsideB4a_ann_bij (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] :
    Function.Bijective (Submodule.dualAnnihilator : Submodule F V → Submodule F (Module.Dual F V)) :=
  ⟨fun _ _ h => Subspace.dualAnnihilator_inj.mp h,
    fun Φ => ⟨Φ.dualCoannihilator, Subspace.dualCoannihilator_dualAnnihilator_eq⟩⟩

private theorem burnsideB4a_ann_map (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V]
    (g : V ≃ₗ[F] V) (U : Submodule F V) :
    (U.map (g : V →ₗ[F] V)).dualAnnihilator =
      U.dualAnnihilator.map ((CFSG.ASVolI.ChB.dualRep (F := F) (M := V) g :
        Module.Dual F V ≃ₗ[F] Module.Dual F V) : Module.Dual F V →ₗ[F] Module.Dual F V) := by
  ext f
  rw [Submodule.mem_dualAnnihilator, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨f ∘ₗ (g : V →ₗ[F] V),
      (Submodule.mem_dualAnnihilator _).mpr (fun u hu => h (g u) (Submodule.mem_map_of_mem hu)), ?_⟩
    ext x
    simp [CFSG.ASVolI.ChB.dualRep]
  · rintro ⟨φ, hφ, rfl⟩ w hw
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    have h0 := (Submodule.mem_dualAnnihilator _).mp hφ u hu
    simpa [CFSG.ASVolI.ChB.dualRep] using h0

private theorem burnsideB4a_mem_fixed (F : Type) [Field F] (M : Type) [AddCommGroup M] [Module F M]
    (A : Subgroup (M ≃ₗ[F] M)) (x : M) :
    x ∈ CFSG.ASVolI.ChB.fixedSubF A ↔ ∀ a ∈ A, (a : M →ₗ[F] M) x = x := by
  simp only [CFSG.ASVolI.ChB.fixedSubF, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

private theorem burnsideB4a_comm_mem (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V]
    (A : Subgroup (V ≃ₗ[F] V)) (b : V ≃ₗ[F] V) (hb : b ∈ A) (φ : Module.Dual F V) :
    (((CFSG.ASVolI.ChB.dualRep (F := F) (M := V) b : Module.Dual F V ≃ₗ[F] Module.Dual F V) :
        Module.Dual F V →ₗ[F] Module.Dual F V) -
      (LinearMap.id : Module.Dual F V →ₗ[F] Module.Dual F V)) φ ∈
      CFSG.ASVolI.ChB.commSubF (M := Module.Dual F V)
        (A.map (CFSG.ASVolI.ChB.dualRep (F := F) (M := V))) :=
  Submodule.mem_iSup_of_mem (CFSG.ASVolI.ChB.dualRep (F := F) (M := V) b)
    (Submodule.mem_iSup_of_mem (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩) (LinearMap.mem_range_self _ φ))

private theorem burnsideB4a_ann_comm (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V]
    (A : Subgroup (V ≃ₗ[F] V)) :
    (CFSG.ASVolI.ChB.commSubF A).dualAnnihilator =
      CFSG.ASVolI.ChB.fixedSubF (M := Module.Dual F V)
        (A.map (CFSG.ASVolI.ChB.dualRep (F := F) (M := V))) := by
  ext ψ
  rw [Submodule.mem_dualAnnihilator, burnsideB4a_mem_fixed]
  constructor
  · intro h b hb
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
    have K : ∀ c ∈ A, ∀ x : V, ψ ((c : V →ₗ[F] V) x) = ψ x := by
      intro c hc x
      have hw : ((c : V →ₗ[F] V) - (LinearMap.id : V →ₗ[F] V)) x ∈ CFSG.ASVolI.ChB.commSubF A :=
        Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem hc (LinearMap.mem_range_self _ x))
      have h1 := h _ hw
      rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, sub_eq_zero] at h1
      exact h1
    ext x
    exact K a⁻¹ (A.inv_mem ha) x
  · intro h
    have hle : CFSG.ASVolI.ChB.commSubF A ≤ LinearMap.ker ψ := by
      unfold CFSG.ASVolI.ChB.commSubF
      refine iSup_le fun a => iSup_le fun ha => ?_
      rintro _ ⟨v, rfl⟩
      rw [LinearMap.mem_ker]
      have h1 := congrArg (fun φ : Module.Dual F V => φ v)
        (h (CFSG.ASVolI.ChB.dualRep (a⁻¹ : V ≃ₗ[F] V))
          (Subgroup.mem_map.mpr ⟨a⁻¹, A.inv_mem ha, rfl⟩))
      have h2 : ψ ((a : V →ₗ[F] V) v) = ψ v := h1
      rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, h2, sub_self]
    intro w hw
    exact LinearMap.mem_ker.mp (hle hw)

private theorem burnsideB4a_ann_fixed (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Subgroup (V ≃ₗ[F] V)) :
    (CFSG.ASVolI.ChB.fixedSubF A).dualAnnihilator =
      CFSG.ASVolI.ChB.commSubF (M := Module.Dual F V)
        (A.map (CFSG.ASVolI.ChB.dualRep (F := F) (M := V))) := by
  have key : CFSG.ASVolI.ChB.fixedSubF A =
      (CFSG.ASVolI.ChB.commSubF (M := Module.Dual F V)
        (A.map (CFSG.ASVolI.ChB.dualRep (F := F) (M := V)))).dualCoannihilator := by
    ext x
    rw [Submodule.mem_dualCoannihilator, burnsideB4a_mem_fixed]
    constructor
    · intro hx φ hφ
      have hle : CFSG.ASVolI.ChB.commSubF (M := Module.Dual F V)
          (A.map (CFSG.ASVolI.ChB.dualRep (F := F) (M := V)))
          ≤ LinearMap.ker (Module.Dual.eval F V x) := by
        unfold CFSG.ASVolI.ChB.commSubF
        refine iSup_le fun b => iSup_le fun hb => ?_
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hb
        rintro _ ⟨φ', rfl⟩
        have hax : (a.symm : V ≃ₗ[F] V) x = x := hx (a⁻¹) (A.inv_mem ha)
        rw [LinearMap.mem_ker, Module.Dual.eval_apply]
        simp only [LinearMap.sub_apply, LinearMap.id_apply]
        show φ' (a.symm x) - φ' x = 0
        rw [hax, sub_self]
      have h1 := LinearMap.mem_ker.mp (hle hφ)
      simpa using h1
    · intro hφ a ha
      have key' : ∀ φ' : Module.Dual F V, φ' ((a : V →ₗ[F] V) x) = φ' x := by
        intro φ'
        have hmem := burnsideB4a_comm_mem F V A (a⁻¹) (A.inv_mem ha) φ'
        have h1 := hφ _ hmem
        simp only [LinearMap.sub_apply, LinearMap.id_apply] at h1
        have h2 : φ' ((a : V →ₗ[F] V) x) - φ' x = 0 := h1
        exact sub_eq_zero.mp h2
      have h3 : ∀ φ' : Module.Dual F V, φ' ((a : V →ₗ[F] V) x - x) = 0 := fun φ' => by
        rw [map_sub, key' φ', sub_self]
      exact sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff F _).mp h3)
  rw [key, Subspace.dualCoannihilator_dualAnnihilator_eq]

private theorem burnsideB4a_quad_iff (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Subgroup (V ≃ₗ[F] V)) :
    CFSG.ASVolI.ChB.IsQuadraticF A ↔
      CFSG.ASVolI.ChB.IsQuadraticF (M := Module.Dual F V)
        (A.map (CFSG.ASVolI.ChB.dualRep (F := F) (M := V))) := by
  unfold CFSG.ASVolI.ChB.IsQuadraticF
  rw [← burnsideB4a_ann_comm F V A, ← burnsideB4a_ann_fixed F V A]
  exact (Subspace.dualAnnihilator_le_dualAnnihilator_iff).symm

end BurnsideB4a

theorem as_B_4_7 : B_4_7 := by
  refine ⟨fun F _ _ V _ _ _ A _ _ => ?_, fun V _ _ hV A hel hne hq hrk => ?_⟩
  · refine ⟨⟨burnsideB4a_ann_bij F V,
      fun U U' => Subspace.dualAnnihilator_le_dualAnnihilator_iff.symm,
      fun g U => burnsideB4a_ann_map F V g U,
      fun U => ?_⟩,
      ⟨burnsideB4a_ann_comm F V A, burnsideB4a_ann_fixed F V A⟩,
      burnsideB4a_quad_iff F V A⟩
    rw [add_comm]
    exact Subspace.finrank_add_finrank_dualAnnihilator_eq U
  · have hdim : Nat.card (CFSG.Quasithin.commV A) ≤ Nat.card A ^ 2 := by
      obtain ⟨k, hk⟩ :=
        (CFSG.Quasithin.isPGroup_two_subgroup hV (CFSG.Quasithin.commV A)).exists_card_eq
      obtain ⟨m, hm⟩ := (CFSG.Quasithin.IsElemAbelian2.isPGroup hel).exists_card_eq
      have hk' : CFSG.Quasithin.rk (CFSG.Quasithin.commV A) = k := by
        unfold CFSG.Quasithin.rk
        rw [hk, padicValNat.prime_pow]
      have hm' : CFSG.Quasithin.rk A = m := by
        unfold CFSG.Quasithin.rk
        rw [hm, padicValNat.prime_pow]
      have hkm : k ≤ 2 * m := by
        have h := hrk
        rw [hk', hm'] at h
        exact h
      rw [hk, hm, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h := CFSG.Quasithin.qOf_dualSub_le_two hV A hne hel hq hdim
    exact_mod_cast h

@[expose] def B_4_8 : Prop :=
  (∀ (G : Type) [Group G] (ρ : G →* Matrix (Fin 3) (Fin 3) (ZMod 2)), Function.Injective ρ →
    Nat.card G = 168 → h1CardOfRep ρ = 2) ∧
  (∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), Nat.card V = 16 → BinaryNaturalSL G ⊤ (fixV G) 3 1 →
      IsIndecompModule G →
        (∃ A : Subgroup (MulAut V), IsCenterTransvGroup G A ∧
            {B | IsFFStarOffender G B} = {B | ∃ g ∈ G, B = B1.conjAut g A}) ∧
        qOf G = 1 ∧
        (∀ T : Subgroup (MulAut V), IsSylowTwoOf T G → fixV T = fixV G) ∧
        (∀ a ∈ G, a ≠ 1 → a ^ 2 = 1 →
          commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
            rk (fixV (Subgroup.zpowers a)) = 2)) ∧
  (∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), Nat.card V = 16 → BinaryNaturalSL G (commV G) ⊥ 3 1 →
      IsIndecompModule G →
        (∃ B : Subgroup (MulAut V), IsAxisTransvGroup G B ∧
            {A | IsFFStarOffender G A} = {A | ∃ g ∈ G, A = B1.conjAut g B}) ∧
        qOf G = 1 ∧
        (∀ a ∈ G, a ≠ 1 → a ^ 2 = 1 →
          commV (Subgroup.zpowers a) = fixV (Subgroup.zpowers a) ∧
            rk (fixV (Subgroup.zpowers a)) = 2 ∧ fixV (Subgroup.zpowers a) ≤ commV G)) ∧
  (∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), Nonempty (↥G ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      IsIndecompModule G → HasOneNatChief G 3 1 →
        Nat.card V = 2 ^ 3 ∨ Nat.card V = 2 ^ 4)

section BurnsideB4b

private theorem burnsideB4b_card_groupCohomology_one {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite G] [Finite V] (ρ : Representation (ZMod 2) G V) :
    Nat.card (groupCohomology (Rep.of ρ) 1) =
      2 ^ Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 ρ) := by
  classical
  set A := Rep.of ρ
  have hZ : CFSG.Quasithin.JonesParshall.Z1 ρ = groupCohomology.cocycles₁ A := by
    ext f
    rw [groupCohomology.mem_cocycles₁_iff]
    change (∀ g h, f (g * h) = f g + ρ g (f h)) ↔ _
    constructor <;> intro h g k <;> rw [h g k, add_comm]
  have hB : CFSG.Quasithin.JonesParshall.B1 ρ = groupCohomology.coboundaries₁ A := rfl
  have hsurj : Function.Surjective (groupCohomology.H1π A) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  let φ := (groupCohomology.H1π A).hom
  have hker : LinearMap.ker φ =
      (groupCohomology.coboundaries₁ A).comap (groupCohomology.cocycles₁ A).subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    exact groupCohomology.H1π_eq_zero_iff x
  let e1 : CFSG.Quasithin.JonesParshall.H1 ρ ≃ₗ[ZMod 2]
      (↥(groupCohomology.cocycles₁ A) ⧸ LinearMap.ker φ) :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ hZ) (by
      rw [hker]
      ext x
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [← hB]
        exact hy
      · intro hx
        refine ⟨(LinearEquiv.ofEq _ _ hZ).symm x, ?_, (LinearEquiv.ofEq _ _ hZ).apply_symm_apply x⟩
        rw [hB]
        exact hx)
  let e2 := φ.quotKerEquivOfSurjective hsurj
  have hfin : Finite (CFSG.Quasithin.JonesParshall.H1 ρ) :=
    Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  let := Fintype.ofFinite (CFSG.Quasithin.JonesParshall.H1 ρ)
  rw [← Nat.card_congr (e1.trans e2).toEquiv, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent in
private theorem burnsideB4b_binaryNaturalSL {G : Type} [Group G]
    (ρ : G →* Matrix (Fin 3) (Fin 3) (ZMod 2)) (hinj : Function.Injective ρ)
    (hcard : Nat.card G = 168) :
    CFSG.Quasithin.Explicit.BinaryNaturalSL (quasithinH1MatrixRep ρ) 3 (ZMod 2) .natural := by
  classical
  let φ : G →* ↥(StatedSL 3 (ZMod 2)) :=
    (MonoidHom.toHomUnits ρ).codRestrict _ (fun g => CFSG.Open.StatedAPI.mem_statedSL_zmod_two _)
  have hφinj : Function.Injective φ := by
    intro g h hgh
    apply hinj
    exact congrArg (fun x : ↥(StatedSL 3 (ZMod 2)) =>
      ((x : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) hgh
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have hφbij : Function.Bijective φ := by
    refine hφinj.bijective_of_nat_card_le ?_
    rw [CFSG.Open.StatedAPI.card_statedSL_three_zmod_two, hcard]
  let θ := MulEquiv.ofBijective φ hφbij
  show (CFSG.Quasithin.FFModel.nat (StatedSL 3 (ZMod 2))).IsModel _
  let D := CFSG.Quasithin.FFModel.nat (StatedSL 3 (ZMod 2))
  let e := CFSG.Quasithin.JonesParshall.secEquivAmb D rfl rfl
  let βa : (Fin 3 → ZMod 2) ≃+ Additive D.Amb :=
    (CFSG.Quasithin.JonesParshall.additiveVec 3 (ZMod 2)).symm
  have hamb : ∀ (γ : G) (w : Fin 3 → ZMod 2),
      βa (quasithinH1MatrixRep ρ γ w) =
        Additive.ofMul (D.act (θ γ) (Additive.toMul (βa w))) := fun γ w => rfl
  refine ⟨θ, βa.trans e.symm.toAdditive, ?_, ?_, ?_, ?_⟩
  · exact bot_le
  · intro g m _
    exact Subgroup.mem_top _
  · intro g m hm
    have hm1 : m = 1 := Subgroup.mem_bot.mp hm
    subst hm1
    refine Subgroup.mem_bot.mpr ?_
    show CFSG.Quasithin.natAct (StatedSL 3 (ZMod 2)) g 1 = 1
    simp [CFSG.Quasithin.natAct]
  · intro γ w m hm hw
    have key : ∀ y : Additive D.Amb, e.toAdditive (e.symm.toAdditive y) = y := fun y => by
      show Additive.ofMul (e (e.symm (Additive.toMul y))) = y
      rw [e.apply_symm_apply]
      rfl
    have h1 : βa w = Additive.ofMul (m : D.Amb) := by
      have h := congrArg e.toAdditive hw
      rw [show (βa.trans e.symm.toAdditive) w = e.symm.toAdditive (βa w) from rfl, key] at h
      exact h
    have h2 : βa (quasithinH1MatrixRep ρ γ w) =
        Additive.ofMul (D.act (θ γ) (m : D.Amb)) := by
      rw [hamb, h1]
      rfl
    apply e.toAdditive.injective
    rw [show (βa.trans e.symm.toAdditive) (quasithinH1MatrixRep ρ γ w) =
      e.symm.toAdditive (βa (quasithinH1MatrixRep ρ γ w)) from rfl, key, h2]
    rfl

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent in
private theorem burnsideB4b_h1CardOfRep {G : Type} [Group G]
    (ρ : G →* Matrix (Fin 3) (Fin 3) (ZMod 2)) (hinj : Function.Injective ρ)
    (hcard : Nat.card G = 168) : CFSG.ASVolI.ChB.h1CardOfRep ρ = 2 := by
  have : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have hF : Fintype.card (ZMod 2) = 2 ^ 1 := by rw [ZMod.card]; norm_num
  have h := CFSG.Quasithin.JonesParshall.finrank_H1_SL3 (F := ZMod 2) (a := 1) hF (by norm_num)
    (burnsideB4b_binaryNaturalSL ρ hinj hcard)
  unfold CFSG.ASVolI.ChB.h1CardOfRep
  rw [burnsideB4b_card_groupCohomology_one (quasithinH1MatrixRep ρ), h]
  simp

private theorem burnsideB4b_step {V : Type} [CommGroup V] (G : Subgroup (MulAut V))
    (θ : ↥G ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (K M : Subgroup V)
    (hK : ∀ g ∈ G, ∀ u ∈ K, g u * u⁻¹ ∈ M) (x : V) (hx : ∀ g ∈ G, g x * x⁻¹ ∈ K) :
    ∀ g ∈ G, g x * x⁻¹ ∈ M := by
  let f : ↥G →* V ⧸ M :=
    { toFun := fun g => QuotientGroup.mk ((g : MulAut V) x * x⁻¹)
      map_one' := by
        show (QuotientGroup.mk (((1 : ↥G) : MulAut V) x * x⁻¹) : V ⧸ M) = 1
        rw [Subgroup.coe_one, MulAut.one_apply, mul_inv_cancel]
        rfl
      map_mul' := fun g h => by
        have hu : (h : MulAut V) x * x⁻¹ ∈ K := hx h h.2
        have hM := hK g g.2 _ hu
        show (QuotientGroup.mk (((g * h : ↥G) : MulAut V) x * x⁻¹) : V ⧸ M) =
          QuotientGroup.mk ((g : MulAut V) x * x⁻¹) * QuotientGroup.mk ((h : MulAut V) x * x⁻¹)
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
        have e : (h : MulAut V) x = ((h : MulAut V) x * x⁻¹) * x := by group
        have e2 : (((g * h : ↥G) : MulAut V) x) =
            (g : MulAut V) (((h : MulAut V) x * x⁻¹) * x) := by
          rw [← e]
          rfl
        rw [e2, map_mul]
        convert M.inv_mem hM using 1
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, map_mul, map_inv]
        abel }
  intro g hg
  have h1 : f ⟨g, hg⟩ = 1 := by
    have := CFSG.Quasithin.Vol2.Ch10.V1C.hom_eq_one (f.comp θ.symm.toMonoidHom) (θ ⟨g, hg⟩)
    simpa using this
  exact (QuotientGroup.eq_one_iff _).mp h1

private theorem burnsideB4b_chief_sections {V : Type} [CommGroup V] (G : Subgroup (MulAut V))
    (θ : ↥G ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (h : CFSG.ASVolI.ChB.HasOneNatChief G 3 1) :
    ∃ W₁ W₂ : Subgroup V, W₁ ≤ W₂ ∧ W₁ ≤ CFSG.Quasithin.fixV G ∧ CFSG.Quasithin.commV G ≤ W₂ ∧
      CFSG.Quasithin.BinaryNaturalSL G W₂ W₁ 3 1 := by
  obtain ⟨m, S, hinv, h0, hm, hchief, j, hj, hcent, hnat⟩ := h
  refine ⟨S j, S (j + 1), (hchief j hj).1.le, ?_, ?_, hnat⟩
  · have key : ∀ i, i ≤ j → ∀ x ∈ S i, ∀ g ∈ G, g x * x⁻¹ ∈ (⊥ : Subgroup V) := by
      intro i
      induction i with
      | zero =>
        intro _ x hx g _
        rw [h0, Subgroup.mem_bot] at hx
        subst hx
        simp
      | succ i ih =>
        intro hi x hx g hg
        exact burnsideB4b_step G θ (S i) ⊥ (fun g hg u hu => ih (by omega) u hu g hg) x
          (fun g hg => hcent i (by omega) (by omega) g hg x hx) g hg
    intro x hx
    rw [CFSG.Quasithin.mem_fixV]
    intro g hg
    have := key j le_rfl x hx g hg
    rw [Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this
  · have key : ∀ k, j + 1 ≤ k → k ≤ m → ∀ x ∈ S k, ∀ g ∈ G, g x * x⁻¹ ∈ S (j + 1) := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base =>
        intro _ x hx g hg
        exact (S (j + 1)).mul_mem (hinv (j + 1) (by omega) g hg x hx) ((S (j + 1)).inv_mem hx)
      | succ k hk ih =>
        intro hkm x hx g hg
        exact burnsideB4b_step G θ (S k) (S (j + 1)) (fun g hg u hu => ih (by omega) u hu g hg) x
          (fun g hg => hcent k (by omega) (by omega) g hg x hx) g hg
    unfold CFSG.Quasithin.commV
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, v, rfl⟩
    exact key m (by omega) le_rfl v (by rw [hm]; exact Subgroup.mem_top v) g hg

end BurnsideB4b

section

theorem as_B_4_8 : B_4_8 := by
  refine ⟨fun G _ ρ hinj hcard => burnsideB4b_h1CardOfRep ρ hinj hcard, ?_, ?_, ?_⟩
  · intro V _ _ hV G hcard hnat hind
    exact CFSG.Quasithin.B4_8_2 hV hcard hnat hind
  · intro V _ _ hV G hcard hnat hind
    exact CFSG.Quasithin.B4_8_3 hV hcard hnat hind
  · intro V _ _ hV G hG hind hchief
    obtain ⟨θ⟩ := hG
    obtain ⟨W₁, W₂, h12, h1F, hcW, hnat⟩ := burnsideB4b_chief_sections G θ hchief
    exact CFSG.Quasithin.Vol2.Ch10.as_B_4_8_four_holds V hV G ⟨θ⟩ hind
      ⟨W₁, W₂, h12, h1F, hcW, hnat⟩

end

@[expose] def B_4_10 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G : Subgroup (MulAut V)) (u : V), u ≠ 1 → (∀ t : MulAut V, IsTransvectionWith t u → t ∈ G) →
      ∀ (U : Subgroup V) (L : Subgroup (MulAut V)),
        U = Subgroup.closure {y | ∃ g ∈ G, g u = y} →
        L = Subgroup.closure {x | ∃ g ∈ G, ∃ t : MulAut V, IsTransvectionWith t u ∧ x = g * t * g⁻¹} →
          autSub L U = ⊤

theorem as_B_4_10 : B_4_10 := by
  intro V _ _ hexp G u hu hT U L hU hL
  exact CFSG.Quasithin.b410 hexp G u hu hT U hU L hL

@[expose] def B_4_11 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), Nonempty (↥G ≃* alternatingGroup (Fin 7)) →
      Nontrivial V → (∀ W : Subgroup V, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) →
        Nat.card V ≤ 2 ^ 8 → Nat.card V = 2 ^ 4 ∨ Nat.card V = 2 ^ 6

theorem as_B_4_11 : B_4_11 := by
  intro V _ _ hV G hG _ hirr hcard
  classical
  have h2V : ∀ x : Additive V, (2 : ℕ) • x = 0 := by
    intro x
    apply Multiplicative.ofAdd.injective
    exact hV (Additive.toMul x)
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2V
  obtain ⟨φ⟩ := hG
  have hfix : CFSG.Quasithin.fixV G = ⊥ := by
    rcases hirr (CFSG.Quasithin.fixV G) (fun g hg w hw =>
        CFSG.Quasithin.mem_fixV.mpr fun x hx => by
          rw [CFSG.Quasithin.mem_fixV.mp hw g hg]
          exact CFSG.Quasithin.mem_fixV.mp hw x hx) with h | h
    · exact h
    · exfalso
      have hact : ∀ g ∈ G, ∀ w : V, g w = w := fun g hg w => by
        have hw : w ∈ CFSG.Quasithin.fixV G := by
          rw [h]
          exact Subgroup.mem_top w
        exact CFSG.Quasithin.mem_fixV.mp hw g hg
      have hG1 : ∀ x : ↥G, x = 1 := fun x =>
        Subtype.ext (MulEquiv.ext fun w => hact (x : MulAut V) x.2 w)
      have hsub : Subsingleton ↥G := ⟨fun x y => (hG1 x).trans (hG1 y).symm⟩
      have h1 : Nat.card ↥G = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
      have h2 : Nat.card ↥G = 2520 := by
        rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
        rfl
      omega
  have hcard' : Nat.card V ≤ 2 ^ 12 := le_trans hcard (by norm_num)
  rcases CFSG.Quasithin.A7Q528.classify4 φ hirr hfix hcard' with ⟨β, -⟩ | ⟨j, hj, Ψ, -⟩
  · right
    rw [Nat.card_congr β.toEquiv, CFSG.Quasithin.A7Q528.card_coreMod7]
  · left
    have h4 : Nat.card (Additive V) = 2 ^ 4 := by
      rw [← Nat.card_congr Ψ.toEquiv]
      simp [Nat.card_fun]
    exact h4

@[expose] def B_4_12 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G : Subgroup (MulAut V)) (v : V), Subgroup.closure (orbitOf G v) = ⊤ →
      (∃ U : Subgroup V, (∃ x ∈ U, ∃ y ∈ U, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y) ∧
        ∀ u ∈ U, u ≠ 1 → u ∈ orbitOf G v) →
        (IsTwoTransitiveOn G (orbitOf G v) → {x : V | x ≠ 1} = orbitOf G v) ∧
        ((Nonempty (↥G ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
            Nonempty (↥G ≃* alternatingGroup (Fin 7))) →
          Odd (Nat.card (orbitOf G v)) →
          Nonempty (↥(G ⊓ MulAction.stabilizer (MulAut V) v) ⧸
              CFSG.pCore 2 ↥(G ⊓ MulAction.stabilizer (MulAut V) v) ≃*
            Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
          Nat.card V = 2 ^ 4 ∧ {x : V | x ≠ 1} = orbitOf G v)

theorem as_B_4_12 : B_4_12 := by
  intro V _ _ hV G v hgen hU
  obtain ⟨U, hUx, hUorb⟩ := hU
  have hv1 : v ≠ 1 := by
    rintro rfl
    obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ := hUx
    obtain ⟨g, -, hg⟩ := hUorb x hx hx1
    apply hx1
    rw [← hg, map_one]
  have hsub : ∀ z ∈ CFSG.Quasithin.orbitOf G v, z ≠ 1 := fun z hz hz1 => by
    subst hz1
    exact CFSG.Quasithin.B412.one_not_mem_orbitOf hv1 hz
  refine ⟨fun h2 => ?_, fun hiso hodd hH => ?_⟩
  · ext z
    exact ⟨fun hz => CFSG.Quasithin.orbit_eq_of_twoTransitive hV G v hgen U hUx hUorb h2 z hz,
      fun hz => hsub z hz⟩
  · obtain ⟨hcard, hall⟩ :=
      CFSG.Quasithin.B412.b412_two hV G v hgen ⟨U, hUx, hUorb⟩ hiso hodd hH
    refine ⟨hcard, ?_⟩
    ext z
    exact ⟨fun hz => hall z hz, fun hz => hsub z hz⟩

@[expose] def B_4_13 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G : Subgroup (MulAut V)) (π : orthModel6.Gam ≃* ↥G) (v : V) (H T : Subgroup (MulAut V)),
      v ≠ 1 → Subgroup.closure (orbitOf G v) = ⊤ →
      IsParabolic2 G (G ⊓ MulAction.stabilizer (MulAut V) v) →
      (∃ x : orthModel6.Amb, x ≠ 1 ∧
        ∀ g : MulAut V, g ∈ G ⊓ MulAction.stabilizer (MulAut V) v ↔
          ∃ s : orthModel6.Gam, orthModel6.act s x = x ∧ ((π s : ↥G) : MulAut V) = g) →
      IsParabolic2 G H →
      (∃ (E : Subgroup ↥H) (_ : E.Normal), IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
        Nonempty (↥H ⧸ E ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) →
      IsSylowTwoOf T G → T ≤ G ⊓ MulAction.stabilizer (MulAut V) v → T ≤ H →
      rk ↥(Subgroup.closure (orbitOf H v)) = 3 →
        ∃ β : V ≃* orthModel6.Amb, ∀ (s : orthModel6.Gam) (u : V),
          β (((π s : ↥G) : MulAut V) u) = orthModel6.act s (β u)

@[expose] def B_4_14 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = 4 →
    ∀ (G : Subgroup (MulAut V)) (α : ↥G ≃* PGL3 F),
      Nontrivial V → (∀ W : Subgroup V, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) →
      ∀ P : Subgroup (MulAut V), IsMaxParabolic2 G P →
      ∀ X : Subgroup (MulAut V), X ≤ P → Nat.card X = 3 →
      (∀ x ∈ X, ∀ l ∈ perfectCore P, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 (perfectCore P)) →
      (∀ C₁ C₂ : Subgroup V, C₁ < C₂ →
        (∀ l ∈ perfectCore P, ∀ c ∈ C₁, l c ∈ C₁) → (∀ l ∈ perfectCore P, ∀ c ∈ C₂, l c ∈ C₂) →
        (∀ J : Subgroup V, (∀ l ∈ perfectCore P, ∀ c ∈ J, l c ∈ J) → C₁ ≤ J → J ≤ C₂ →
          J = C₁ ∨ J = C₂) →
        (∃ l ∈ perfectCore P, ∃ c ∈ C₂, l c * c⁻¹ ∉ C₁) →
          BinaryNaturalSL (ChB.autSec (perfectCore P) C₂ C₁) ⊤ ⊥ 2 2) →
        ∃ k : ℕ, k < 3 ∧ ∃ β : V ≃* Multiplicative ↥(sl3Sub F),
          TwAdjointIntertwines G α.toMonoidHom k β ∧
          (k = 0 → IsTensorOfNaturalsUniserialVia β
              (perfectCore P ⊓ Subgroup.centralizer (X : Set (MulAut V))) (fixV X)) ∧
          (k ≠ 0 → IsNaturalSL2ViaAdjoint β
              (perfectCore P ⊓ Subgroup.centralizer (X : Set (MulAut V))) (fixV X)) ∧
          (∀ (otherTwist : ℕ), otherTwist < 3 →
            ∀ otherIdentification : V ≃* Multiplicative ↥(sl3Sub F),
              TwAdjointIntertwines G α.toMonoidHom otherTwist otherIdentification →
                otherTwist = k)

@[expose] def B_4_9 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (n f : ℕ), ((4 ≤ n ∧ f = 1) ∨ (n = 3 ∧ 1 ≤ f)) →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
    ∀ (G : Subgroup (MulAut V)) (U : Subgroup V) (π : ↥(StatedSL n K) →* ↥G),
      (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π →
      (QuotIsoSub G U ∨ QuotIsoDual G U) →
      (∀ E : Subgroup (MulAut V), IsTransvFourGrpFixedAxis G U f E → IsQuadratic E →
        (n = 3 → ¬ InRootGroup G π E) →
        (n = 3 → f = 2 → ∀ E' : Subgroup (MulAut V), IsTransvFourGrpFixedAxis G U f E' →
          ¬ InRootGroup G π E' → IsQuadratic E') →
          SplitsOver G U) ∧
      (∀ T : Subgroup (MulAut V), IsSylowTwoOf T G → ∀ A : Subgroup (MulAut V), IsFFStarOffender T A →
        SplitsOver G U ∧
        (n = 3 → QuotIsoSub G U ∧ qOf G = ((1 : ℚ) : WithTop ℚ)) ∧
        (n = 4 → QuotIsoDual G U → A = Jj T 0 ∧ rk ↥A = 4 ∧ qOf G = ((1 : ℚ) : WithTop ℚ)) ∧
        (n = 5 → QuotIsoDual G U → qOf G = ((5 / 6 : ℚ) : WithTop ℚ) ∧
          ((IsElemAbelian 2 A ∧ Nat.card A = 16 ∧ ∃ P M : Subgroup (MulAut V),
              (IsSubspaceStab G U 1 P ∨ IsSubspaceStab G U 4 P) ∧ IsLeviComplement P M ∧ A ≤ M) ∨
            (IsElemAbelian 2 A ∧ (Nat.card A = 32 ∨ Nat.card A = 64) ∧ ∃ P : Subgroup (MulAut V),
              (IsSubspaceStab G U 2 P ∨ IsSubspaceStab G U 3 P) ∧ A ≤ pCoreOf 2 P))))

@[expose] def B_4_6 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
  ∀ (n : ℕ), 1 ≤ n → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n →
  ∀ (G L : Subgroup (MulAut V)) (π : ↥(quasithinG2 K) →* MulAut V)
    (θ : V →* Multiplicative (NatQ K)),
    Function.Injective π → π.range = L → L ≤ G →
    quasithinGenFitting G = layerOf L → commV (layerOf L) = ⊤ →
    Function.Surjective θ → θ.ker = fixV L →
    (∀ (γ : ↥(quasithinG2 K)) (v : V), θ ((π γ) v) = Multiplicative.ofAdd
      (qAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (θ v)))) →
    ((∀ ψ : Multiplicative (NatQ K) →* Multiplicative (NatQ K),
        (∀ l ∈ L, ∀ v w : V, ψ (θ v) = θ w → ψ (θ (l v)) = θ (l w)) →
          ∃ c : K, ∀ x, ψ x = Multiplicative.ofAdd (c • Multiplicative.toAdd x)) ∧
      (∀ (c : K), ∀ l ∈ L, ∀ v w : V,
        θ w = Multiplicative.ofAdd (c • Multiplicative.toAdd (θ v)) →
          θ (l w) = Multiplicative.ofAdd (c • Multiplicative.toAdd (θ (l v)))) ∧
      Nat.card V ≤ 2 ^ (7 * n) ∧
      (Nat.card V = 2 ^ (7 * n) → ∃ Ψ : V ≃* Multiplicative (WeylM K),
        ∀ (γ : ↥(quasithinG2 K)) (v : V), Ψ ((π γ) v) = Multiplicative.ofAdd
          (weylAct (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd (Ψ v))))) ∧
    (∀ v w : V, θ v ≠ 1 → θ w ≠ 1 → ∃ l ∈ L, θ (l v) = θ w) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
        IsMaxParabolic2 L P₁ ∧ Nat.card R₁ = Nat.card K ^ 5 ∧ IsNatGL2QuotTw K P₁ R₁ Z₁ ⊥ ∧
        IsFPre θ 3 V₃ ∧ (IsElemAbelian 2 A₁ ∧ Nat.card A₁ = Nat.card K ^ 3) ∧
        IsNatGL2Quot K P₁ R₁ R₁ A₁ ∧
        ∀ E : Subgroup V,
          E = ⨆ (Z : Subgroup (MulAut V)) (_ : IsLongRootSub π Z ∧ Z ≤ Z₁), cPre (fixV L) Z →
            IsFPre θ 5 E ∧ commSub E A₁ ⊔ fixV L = V₃) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        (IsElemAbelian 2 Z₂ ∧ Nat.card Z₂ = Nat.card K ∧ IsLongRootSub π Z₂) ∧
        (IsMaxParabolic2 L P₂ ∧ T ⊓ L ≤ P₂ ∧ P₂ ≠ P₁) ∧
        (IsSpecial2 R₂ Z₂ ∧ Nat.card R₂ = Nat.card K ^ 5) ∧
        IsNatGL2SecMod K P₂ R₂ V₂ (fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → V₂ = commV (Subgroup.zpowers z) ⊔ fixV L) ∧
        (∀ z ∈ Z₂, z ≠ 1 → cPre (fixV L) Z₂ = cPre (fixV L) (Subgroup.zpowers z) ∧
          IsFPre θ 4 (cPre (fixV L) Z₂))) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsLongRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
          ∃ l ∈ L, x = l * z * l⁻¹) ∧
        (∃ r : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ r ∈ Z ∧ r ≠ 1) ∧
          (∀ x : MulAut V, (∃ Z : Subgroup (MulAut V), IsShortRootSub π Z ∧ x ∈ Z ∧ x ≠ 1) ↔
            ∃ l ∈ L, x = l * r * l⁻¹) ∧
          ¬ (∃ l ∈ L, r = l * z * l⁻¹) ∧
          ∀ x ∈ L, x ≠ 1 → x ^ 2 = 1 → (∃ l ∈ L, x = l * z * l⁻¹) ∨ (∃ l ∈ L, x = l * r * l⁻¹)) ∧
        (L ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) =
            L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) ∧
          L ⊓ Subgroup.centralizer (Z₂ : Set (MulAut V)) = twoPrimeResidual P₂)) ∧
    (∀ R : Subgroup (MulAut V), IsShortRootSub π R → ∀ r ∈ R, r ≠ 1 →
      L ⊓ Subgroup.centralizer ({r} : Set (MulAut V)) = L ⊓ Subgroup.centralizer (R : Set (MulAut V)) ∧
      ∃ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ ∧ IsIntDirProd A₁ ![Z₁, R] ∧
        (cPre (fixV L) (Subgroup.zpowers r) = V₃ ∧ cPre (fixV L) R = V₃ ∧
          commV (Subgroup.zpowers r) ⊔ fixV L = V₃) ∧
        ∃ L₁ : Subgroup (MulAut V), IsLeviComplement P₁ L₁ ∧
          L ⊓ Subgroup.normalizer (R : Set (MulAut V)) = A₁ ⊔ L₁) ∧
    (∀ i ∈ L, i ≠ 1 → i ^ 2 = 1 →
      cPre (fixV L) (Subgroup.zpowers i) = fixV (Subgroup.zpowers i) ⊔ fixV L) ∧
    (1 < n → ∀ R : Subgroup (MulAut V), IsShortRootSub π R → fixV L ≤ commV R) ∧
    (E3.aParam G = 2 * n ∧ (∀ A ∈ E3.aSet 2 G, A ≤ L) ∧
      ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
        B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
          E3.aSet (2 * n) G = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
          ∀ A ∈ E3.aSet (n + 1) G, ∃ l ∈ L, A.map (MulAut.conj l).toMonoidHom ≤ A₁) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        Set.ncard {X : Subgroup V | ∃ p ∈ P₁, X = V₂.map (p : MulAut V).toMonoidHom} = Nat.card K + 1 ∧
        (∀ p ∈ P₁, V₁ ≤ V₂.map (p : MulAut V).toMonoidHom ∧ V₂.map (p : MulAut V).toMonoidHom ≤ V₃) ∧
        (∀ p ∈ P₁, ∀ p' ∈ P₁, V₂.map (p : MulAut V).toMonoidHom ≠ V₂.map (p' : MulAut V).toMonoidHom →
          V₂.map (p : MulAut V).toMonoidHom ⊓ V₂.map (p' : MulAut V).toMonoidHom = V₁) ∧
        (∀ v ∈ V₃, ∃ p ∈ P₁, v ∈ V₂.map (p : MulAut V).toMonoidHom)) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ z ∈ Z₂, z ≠ 1 →
        (∀ B : Subgroup (MulAut V), B ≤ G → (∀ b ∈ B, b ≠ 1 → ∃ l ∈ L, b = l * z * l⁻¹) →
          ∃ l ∈ L, B.map (MulAut.conj l).toMonoidHom ≤ Z₁) ∧
        IsStrongClosedWrt Z₁ R₁ G) ∧
    (1 < n → ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ → ∀ A ∈ E3.aSet (2 * n - 1) G, A ≤ R₁ → A ≤ A₁) ∧
    (∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
        {A | IsFFStarOffender G A} = {A | ∃ l ∈ L, A = A₁.map (MulAut.conj l).toMonoidHom} ∧
        ffJ T = R₂ ∧ ffJ R₁ = A₁) ∧
    (n = 2 → ∀ (V₁ : Subgroup V) (P₁ R₁ Z₁ : Subgroup (MulAut V)) (V₃ : Subgroup V) (A₁ : Subgroup (MulAut V)),
      B46Cfg1 G L θ V₁ P₁ R₁ Z₁ V₃ A₁ →
      ∀ (T Z₂ P₂ R₂ : Subgroup (MulAut V)) (V₂ : Subgroup V), B46Cfg2 G L P₁ T Z₂ P₂ R₂ V₂ →
      ∀ X : Subgroup (MulAut V), X ≤ G → Nat.card X = 3 → (X : Set (MulAut V)) * (T : Set (MulAut V)) =
          (T : Set (MulAut V)) * (X : Set (MulAut V)) →
        (X ≤ P₁ ⊓ perfectCore P₂ ↔ ⁅X, perfectCore P₁⁆ ≤ R₁))

end CFSG.ASVolI
