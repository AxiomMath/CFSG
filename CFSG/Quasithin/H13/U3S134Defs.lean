module

public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.A6Setting134

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def InW2 (x : A6.P6) : Prop :=
  Multiplicative.toAdd x 0 = Multiplicative.toAdd x 1 ∧
    Multiplicative.toAdd x 2 = Multiplicative.toAdd x 3 ∧
    Multiplicative.toAdd x 4 = Multiplicative.toAdd x 5

instance : DecidablePred InW2 := fun x =>
  inferInstanceAs (Decidable (Multiplicative.toAdd x 0 = Multiplicative.toAdd x 1 ∧
    Multiplicative.toAdd x 2 = Multiplicative.toAdd x 3 ∧
    Multiplicative.toAdd x 4 = Multiplicative.toAdd x 5))

@[expose] def W2sub : Subgroup ↥(G6.coreMod 6) where
  carrier := {y | InW2 (y : A6.P6)}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => (by
    have key : ∀ a b : A6.P6, InW2 a → InW2 b → InW2 (a * b) := by decide +kernel
    exact key _ _ ha hb)
  inv_mem' := fun {a} ha => (by
    have key : ∀ a : A6.P6, InW2 a → InW2 a⁻¹ := by decide +kernel
    exact key _ ha)

variable {G : Type} [Group G]

@[expose] noncomputable def v2Of [Finite G] {T L V : Subgroup G} (S : A6.Setting134 G T L V) :
    Subgroup G :=
  S.pre W2sub

@[expose] noncomputable def l2Of [Finite G] {T L V : Subgroup G} (S : A6.Setting134 G T L V) :
    Subgroup G :=
  L₁Of L (v2Of S)

@[expose] noncomputable def r1Of (T L V : Subgroup G) : Subgroup G :=
  T ⊓ ((pCoreOf 2 (autOn ((L ⊔ T) ⊓ normalizer (fsuV1 T V : Set G)) V)).comap
    (conjAct V)).map (normalizer (V : Set G)).subtype

@[expose] def fanoCoreSub : Subgroup (Multiplicative ((Fin 3 → ZMod 2) → ZMod 2)) where
  carrier := {f | Multiplicative.toAdd f 0 = 0 ∧ ∑ v, Multiplicative.toAdd f v = 0}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    obtain ⟨ha0, has⟩ := ha
    obtain ⟨hb0, hbs⟩ := hb
    refine ⟨?_, ?_⟩
    · show Multiplicative.toAdd (a * b) 0 = 0
      rw [toAdd_mul, Pi.add_apply, ha0, hb0, add_zero]
    · show ∑ v, Multiplicative.toAdd (a * b) v = 0
      simp only [toAdd_mul, Pi.add_apply, Finset.sum_add_distrib, has, hbs, add_zero]
  inv_mem' := fun {a} ha => by
    obtain ⟨ha0, has⟩ := ha
    have hneg : ∀ x : ZMod 2, -x = x := by decide
    refine ⟨?_, ?_⟩
    · show Multiplicative.toAdd a⁻¹ 0 = 0
      rw [toAdd_inv, Pi.neg_apply, hneg, ha0]
    · show ∑ v, Multiplicative.toAdd a⁻¹ v = 0
      simp only [toAdd_inv, Pi.neg_apply, hneg, has]

@[expose] def FFModel.fanoCore : FFModel where
  Gam := ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))
  Amb := Multiplicative ((Fin 3 → ZMod 2) → ZMod 2)
  act g f := Multiplicative.ofAdd fun v => Multiplicative.toAdd f
    ((((g⁻¹ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v)
  sec := fanoCoreSub
  ker := ⊥

@[expose] def IsFanoCore (K₀ V₀ : Subgroup G) : Prop :=
  ∃ _ : IsMulCommutative ↥V₀, FFModel.fanoCore.Realizes (autOn K₀ V₀) ⊤ ⊥

@[expose] def IsSumNatDual3 (K₀ V₀ : Subgroup G) : Prop :=
  ∃ _ : IsMulCommutative ↥V₀, ∃ U₁ U₂ : Subgroup ↥V₀, U₁ ⊔ U₂ = ⊤ ∧ U₁ ⊓ U₂ = ⊥ ∧
    ∃ π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) →* ↥(autOn K₀ V₀),
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))).RealizesVia (autOn K₀ V₀)
        U₁ ⊥ π ∧
      (FFModel.dualNat (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))).RealizesVia
        (autOn K₀ V₀) U₂ ⊥ π

variable [Finite G]

@[expose] def cZ (T X : Subgroup G) : Subgroup G :=
  quasithinOmegaOneCenter T ⊓ centralizer (X : Set G)

@[expose] def v0Of (T H₁ H₂ : Subgroup G) : Subgroup G :=
  conjClosure (quasithinOmegaOneCenter T) (H₁ ⊔ H₂)

structure Hyp1347 (T H₁ H₂ : Subgroup G) : Prop where
  inH₁ : InH T H₁
  inH₂ : InH T H₂
  ne : H₁ ≠ H₂
  s3₁ : quasithinO2QuotientIso H₁ (Perm (Fin 3))
  s3₂ : quasithinO2QuotientIso H₂ (Perm (Fin 3))
  chief : HasTwoNoncentralChiefFactors (oTwoRes H₁) ∨ HasTwoNoncentralChiefFactors (oTwoRes H₂)
  index₁ : Nat.card ↥(quasithinOmegaOneCenter T) = 2 * Nat.card ↥(cZ T H₁)
  index₂ : Nat.card ↥(quasithinOmegaOneCenter T) = 2 * Nat.card ↥(cZ T H₂)
  cent : InH T (H₁ ⊔ H₂) →
    ((H₁ ⊔ H₂) ⊓ centralizer (cZ T (oTwoRes H₁) : Set G) ≤
        normalizer (oTwoRes H₁ : Set G) ∧
      (H₁ ⊔ H₂) ⊓ centralizer (cZ T (oTwoRes H₂) : Set G) ≤
        normalizer (oTwoRes H₂ : Set G)) ∧
    (oTwoRes H₁ = oThreePrimeResidual ((H₁ ⊔ H₂) ⊓ centralizer (cZ T (oTwoRes H₁) : Set G)) ∨
      oTwoRes H₂ = oThreePrimeResidual ((H₁ ⊔ H₂) ⊓ centralizer (cZ T (oTwoRes H₂) : Set G)))

@[expose] def Concl1347i (T H₁ H₂ : Subgroup G) : Prop :=
  (∀ x ∈ H₁ ⊔ H₂, ∃ a ∈ H₁, ∃ b ∈ H₂, x = a * b) ∧
    ⁅oTwoRes H₁, oTwoRes H₂⁆ ≤ pCoreOf 2 (oTwoRes H₁) ⊓ pCoreOf 2 (oTwoRes H₂) ∧
    (quasithinO2QuotientIso (H₁ ⊔ H₂) (Perm (Fin 3) × Perm (Fin 3)) ∨
      F6.IsExtensionOf (↥(H₁ ⊔ H₂) ⧸ CFSG.Open.pCore 2 ↥(H₁ ⊔ H₂)) (Multiplicative (ZMod 2))
        (Multiplicative (ZMod 3 × ZMod 3))) ∧
    ⁅v0Of T H₁ H₂, oTwoRes H₁⁆ ⊔ ⁅v0Of T H₁ H₂, oTwoRes H₂⁆ = v0Of T H₁ H₂ ∧
    ⁅v0Of T H₁ H₂, oTwoRes H₁⁆ ⊓ ⁅v0Of T H₁ H₂, oTwoRes H₂⁆ = ⊥ ∧
    ⁅v0Of T H₁ H₂, oTwoRes H₁⁆ = v0Of T H₁ H₂ ⊓ centralizer (oTwoRes H₂ : Set G) ∧
    ⁅v0Of T H₁ H₂, oTwoRes H₂⁆ = v0Of T H₁ H₂ ⊓ centralizer (oTwoRes H₁ : Set G) ∧
    Nat.card ↥⁅v0Of T H₁ H₂, oTwoRes H₁⁆ = 4 ∧ Nat.card ↥⁅v0Of T H₁ H₂, oTwoRes H₂⁆ = 4

@[expose] def Concl1347ii (T H₁ H₂ : Subgroup G) : Prop :=
  ∃ K₀ : Subgroup G, H₁ ⊔ H₂ = K₀ ⊔ T ∧ quasithinIsCComponent K₀ (H₁ ⊔ H₂) ∧
    quasithinIsMaximalLocal T K₀ ∧ quasithinIsFaithfulLocal T K₀ ∧
    quasithinO2QuotientIso K₀ (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
    H₁ ⊔ H₂ ≤ normalizer (thompsonJ T : Set G) ∧
    (IsSumNatDual3 K₀ (v0Of T H₁ H₂) ∨ IsFanoCore K₀ (v0Of T H₁ H₂))

@[expose] def Concl1347iii (T H₁ H₂ : Subgroup G) : Prop :=
  pCoreOf 2 (H₁ ⊔ H₂) = (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) ∧
    F6.IsExtensionWith (↥(H₁ ⊔ H₂) ⧸ CFSG.Open.pCore 2 ↥(H₁ ⊔ H₂))
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) (fun N => IsPOnePlusTwo 3 ↥N) ∧
    Nat.card ↥(v0Of T H₁ H₂) = 2 ^ 6 ∧ H₁ ⊔ H₂ ≤ normalizer (thompsonJ T : Set G)

@[expose] def Concl1347iv (T H₁ H₂ : Subgroup G) : Prop :=
  ∃ K₀ : Subgroup G, H₁ ⊔ H₂ = K₀ ⊔ T ∧ quasithinIsCComponent K₀ (H₁ ⊔ H₂) ∧
    quasithinO2QuotientIso K₀ ↥(alternatingGroup (Fin 6)) ∧
    H₁ ⊔ H₂ ≤ normalizer (thompsonJi T 0 : Set G) ∧ H₁ ⊔ H₂ ≤ normalizer (thompsonJi T 1 : Set G)

@[expose] def InHz (T L V : Subgroup G) (z : G) (H : Subgroup G) : Prop :=
  InH (L₁Of L (fsuV1 T V) ⊔ T) H ∧ H ≤ centralizer ({z} : Set G) ∧
    ¬ H ≤ normalizer (L : Set G)

@[expose] def Stmt13_4_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (_ : A6.Setting134 G T L V) (z : G),
    z ∈ fsuV1 T V → z ∉ centralizer (L : Set G) →
    ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G) →
    ∀ H VH : Subgroup G, InHz T L V z H → Group.IsSolvable ↥H → IsTwoReducedIn H VH →
      V ⊓ centralizer (L : Set G) ≤ VH →
      quasithinO2QuotientIso L ↥(alternatingGroup (Fin 6)) ∧
      quasithinO2QuotientIso (conjClosure (thompsonJ (r1Of T L V)) H) (Perm (Fin 3)) ∧
      Nat.card ↥⁅VH, conjClosure (thompsonJ (r1Of T L V)) H⁆ = 4 ∧
      H = L₁Of L (fsuV1 T V) ⊔ conjClosure (thompsonJ (r1Of T L V)) H ⊔ T ∧
      quasithinO2QuotientIso H (Perm (Fin 3) × Perm (Fin 3)) ∧
      IsHStar T (normalizer (L : Set G)) (conjClosure (thompsonJ (r1Of T L V)) H ⊔ T) ∧
      ∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X → X ≤ H →
        X = conjClosure (thompsonJ (r1Of T L V)) H ⊔ T

end CFSG.Quasithin.H13.U3
