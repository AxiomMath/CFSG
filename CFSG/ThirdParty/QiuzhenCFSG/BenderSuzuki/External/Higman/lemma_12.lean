module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_10
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_8
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_9
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_11
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_6
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.FrobeniusBilinear
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.CentralExtensionCoordinates
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Invariant
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Maschke
import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.RepresentationTheory.Submodule

namespace CFSG
end CFSG
open CFSG

/-!
# Higman Lemma 12
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open scoped TensorProduct commutatorElement

open PFAppendixIII

universe u

@[expose] public def Lemma12TypeBActorQuadraticData
    {P : Type u} [Group P]
    (T : Additive (LowerCentralFactor P 0) ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor P 0))
    (S : Additive (LowerCentralFactor P 1) ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1))
    (n : ℕ)
    (squareMap : Additive (LowerCentralFactor P 0) →
      Additive (LowerCentralFactor P 1)) : Prop :=
  ∃ (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
      (epsilon : BinaryGaloisField n)
      (quotientCoordinates :
        (BinaryGaloisField n × BinaryGaloisField n) ≃ₗ[ZMod 2]
          Additive (LowerCentralFactor P 0))
      (centerCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2]
        Additive (LowerCentralFactor P 1))
      (lambdaUnit : (BinaryGaloisField n)ˣ),
    epsilon ≠ 0 ∧
    (∃ r : ℕ, Odd r ∧ 0 < r ∧
      ∀ x : BinaryGaloisField n, theta^[r] x = x) ∧
    (∀ a b : BinaryGaloisField n, a ≠ 0 → b ≠ 0 →
      a * theta a + epsilon * a * theta b + b * theta b ≠ 0) ∧
    (∀ a b : BinaryGaloisField n,
      centerCoordinates.symm (squareMap (quotientCoordinates (a, b))) =
        a * theta a + epsilon * a * theta b + b * theta b) ∧
    orderOf lambdaUnit = 2 ^ n - 1 ∧
    (∀ a b : BinaryGaloisField n,
      T (quotientCoordinates (a, b)) =
        quotientCoordinates
          ((lambdaUnit : BinaryGaloisField n) * a,
            (lambdaUnit : BinaryGaloisField n) * b)) ∧
    ∀ z : BinaryGaloisField n,
      S (centerCoordinates z) =
        centerCoordinates
          ((lambdaUnit : BinaryGaloisField n) *
            theta (lambdaUnit : BinaryGaloisField n) * z)
/-- Type-B group coordinates together with the action of one primitive actor on
the two lower-central factors. -/
@[expose] public def Lemma12TypeBActorCoordinates
    {P : Type u} [Group P]
    (T : Additive (LowerCentralFactor P 0) ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor P 0))
    (S : Additive (LowerCentralFactor P 1) ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1))
    (n : ℕ)
    (squareMap : Additive (LowerCentralFactor P 0) →
      Additive (LowerCentralFactor P 1)) : Prop :=
  ∃ (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
      (epsilon : BinaryGaloisField n)
      (tripleLift : BinaryGaloisField n → BinaryGaloisField n →
        BinaryGaloisField n → P)
      (cocycle : BinaryGaloisField n → BinaryGaloisField n →
        BinaryGaloisField n → BinaryGaloisField n → BinaryGaloisField n)
      (quotientCoordinates :
        (BinaryGaloisField n × BinaryGaloisField n) ≃ₗ[ZMod 2]
          Additive (LowerCentralFactor P 0))
      (centerCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2]
        Additive (LowerCentralFactor P 1))
      (lambdaUnit : (BinaryGaloisField n)ˣ),
    epsilon ≠ 0 ∧
    (∃ r : ℕ, Odd r ∧ 0 < r ∧
      ∀ x : BinaryGaloisField n, theta^[r] x = x) ∧
    (∀ a b : BinaryGaloisField n, a ≠ 0 → b ≠ 0 →
      a * theta a + epsilon * a * theta b + b * theta b ≠ 0) ∧
    (∀ a b e f c d : BinaryGaloisField n,
      cocycle (a + e) (b + f) c d =
        cocycle a b c d + cocycle e f c d) ∧
    (∀ a b e f c d : BinaryGaloisField n,
      cocycle a b (e + c) (f + d) =
        cocycle a b e f + cocycle a b c d) ∧
    (∀ a b : BinaryGaloisField n,
      cocycle a b a b =
        a * theta a + epsilon * a * theta b + b * theta b) ∧
    (∀ c a b : BinaryGaloisField n, tripleLift c a b ∈ (⊤ : Subgroup P)) ∧
    tripleLift 0 0 0 = 1 ∧
    (∀ x : P, ∃ c a b : BinaryGaloisField n, x = tripleLift c a b) ∧
    (∀ c a b d e f : BinaryGaloisField n,
      tripleLift c a b = tripleLift d e f → c = d ∧ a = e ∧ b = f) ∧
    (∀ c a b d e f : BinaryGaloisField n,
      tripleLift c a b * tripleLift d e f =
        tripleLift (c + d + cocycle a b e f) (a + e) (b + f)) ∧
    (∀ a b : BinaryGaloisField n,
      centerCoordinates.symm (squareMap (quotientCoordinates (a, b))) =
        a * theta a + epsilon * a * theta b + b * theta b) ∧
    orderOf lambdaUnit = 2 ^ n - 1 ∧
    (∀ a b : BinaryGaloisField n,
      T (quotientCoordinates (a, b)) =
        quotientCoordinates
          ((lambdaUnit : BinaryGaloisField n) * a,
            (lambdaUnit : BinaryGaloisField n) * b)) ∧
    ∀ z : BinaryGaloisField n,
      S (centerCoordinates z) =
        centerCoordinates
          ((lambdaUnit : BinaryGaloisField n) *
            theta (lambdaUnit : BinaryGaloisField n) * z)

@[expose] public def Lemma12TypeBNormalizedData
    {P : Type u} [Group P]
    (xi : MulAut P) (n : ℕ)
    (U V : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)))
    (bracket : Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor P 1))
    (squareMap : Additive (LowerCentralFactor P 0) →
      Additive (LowerCentralFactor P 1)) : Prop :=
  ∃ (eta epsilon : BinaryGaloisField n)
      (uNorm : BinaryGaloisField n ≃ₗ[ZMod 2] U)
      (vNorm : BinaryGaloisField n ≃ₗ[ZMod 2] V)
      (centerCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2]
        Additive (LowerCentralFactor P 1))
      (heta : eta ≠ 0) (_ : epsilon ≠ 0),
    orderOf (Units.mk0 eta heta) = 2 ^ n - 1 ∧
    (∀ a : BinaryGaloisField n,
      lowerCentralFactorLinearAut xi 0
          (uNorm a : Additive (LowerCentralFactor P 0)) =
        (uNorm (eta * a) : Additive (LowerCentralFactor P 0))) ∧
    (∀ b : BinaryGaloisField n,
      lowerCentralFactorLinearAut xi 0
          (vNorm b : Additive (LowerCentralFactor P 0)) =
        (vNorm (eta * b) : Additive (LowerCentralFactor P 0))) ∧
    (∀ z : BinaryGaloisField n,
      lowerCentralFactorLinearAut xi 1 (centerCoordinates z) =
        centerCoordinates (eta ^ 2 * z)) ∧
    (∀ a : BinaryGaloisField n,
      centerCoordinates.symm
          (squareMap (uNorm a : Additive (LowerCentralFactor P 0))) = a ^ 2) ∧
    (∀ b : BinaryGaloisField n,
      centerCoordinates.symm
          (squareMap (vNorm b : Additive (LowerCentralFactor P 0))) = b ^ 2) ∧
    ∀ a b : BinaryGaloisField n,
      centerCoordinates.symm
          (bracket (uNorm a : Additive (LowerCentralFactor P 0))
            (vNorm b : Additive (LowerCentralFactor P 0))) =
        epsilon * a * b

@[expose] public def Lemma12TypeCNormalizedData
    {P : Type u} [Group P]
    (xi : MulAut P) (n : ℕ)
    (U V : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)))
    (bracket : Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor P 1))
    (squareMap : Additive (LowerCentralFactor P 0) →
      Additive (LowerCentralFactor P 1)) : Prop :=
  ∃ (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
      (lambda eta epsilon : BinaryGaloisField n)
      (outerNorm : BinaryGaloisField n ≃ₗ[ZMod 2] V)
      (middleNorm : BinaryGaloisField n ≃ₗ[ZMod 2] U)
      (centerCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2]
        Additive (LowerCentralFactor P 1))
      (hlambda : lambda ≠ 0) (heta : eta ≠ 0)
      (_ : epsilon ≠ 0),
    (∃ r : ℕ, Odd r ∧ 0 < r ∧
      ∀ x : BinaryGaloisField n, theta^[r] x = x) ∧
    (∀ x : BinaryGaloisField n, theta (theta (x ^ 2)) = x) ∧
    orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1 ∧
    orderOf (Units.mk0 eta heta) = 2 ^ n - 1 ∧
    eta ^ 2 = lambda * theta lambda ∧
    (∀ a : BinaryGaloisField n,
      lowerCentralFactorLinearAut xi 0
          (outerNorm a : Additive (LowerCentralFactor P 0)) =
        (outerNorm (lambda * a) : Additive (LowerCentralFactor P 0))) ∧
    (∀ b : BinaryGaloisField n,
      lowerCentralFactorLinearAut xi 0
          (middleNorm b : Additive (LowerCentralFactor P 0)) =
        (middleNorm (eta * b) : Additive (LowerCentralFactor P 0))) ∧
    (∀ z : BinaryGaloisField n,
      lowerCentralFactorLinearAut xi 1 (centerCoordinates z) =
        centerCoordinates (eta ^ 2 * z)) ∧
    (∀ b : BinaryGaloisField n,
      centerCoordinates.symm
          (squareMap (middleNorm b : Additive (LowerCentralFactor P 0))) = b ^ 2) ∧
    ∀ a b : BinaryGaloisField n,
      centerCoordinates.symm
          (bracket (middleNorm b : Additive (LowerCentralFactor P 0))
            (outerNorm a : Additive (LowerCentralFactor P 0))) =
        epsilon * a ^ (2 ^ (n - 1)) * theta (b ^ 2)

@[expose] public def Lemma12ChainActorData
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (g : X) (A B : Subgroup P) : Prop :=
  ∃ (k n : ℕ) (xi : MulAut P)
      (q0 : P →* LowerCentralFactor P 0)
      (U V : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)))
      (bracket : Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
          Additive (LowerCentralFactor P 1))
      (squareMap : Additive (LowerCentralFactor P 0) →
        Additive (LowerCentralFactor P 1)),
    xi = MulDistribMulAction.toMulAut X P (g ^ (2 ^ k)) ∧
    2 ≤ n ∧ q0.ker = B ∧ Function.Surjective q0 ∧
    (∀ p : P, q0 p =
      QuotientGroup.mk' (lowerCentralFactorKernel P 0)
        (Subgroup.topEquiv.symm p)) ∧
    (∀ u : Additive (LowerCentralFactor P 0),
      u ∈ U ↔ u.toMul ∈ A.map q0) ∧
    IsCompl U V ∧ (⊤ : Subgroup P).lowerCentralSeries 1 = B ∧
    lowerCentralFactorKernel P 1 = ⊥ ∧
    (∀ x y : (⊤ : Subgroup P).lowerCentralSeries 0,
      ∀ hcomm : ⁅(x : P), (y : P)⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries 1,
        bracket
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel P 0) x))
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel P 0) y)) =
          Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel P 1)
              ⟨⁅(x : P), (y : P)⁆, hcomm⟩)) ∧
    (∀ x : (⊤ : Subgroup P).lowerCentralSeries 0,
      ∀ hsquare : (x : P) ^ 2 ∈ (⊤ : Subgroup P).lowerCentralSeries 1,
        squareMap
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel P 0) x)) =
          Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel P 1)
              ⟨(x : P) ^ 2, hsquare⟩)) ∧
    (Lemma12TypeBNormalizedData xi n U V bracket squareMap ∨
      Lemma12TypeCNormalizedData xi n U V bracket squareMap)

/-- The length-three factor data needed to split the central quotient into two
actor-invariant summands. -/
@[expose] public def Lemma12SummandData
    (X P : Type u) [Group X] [Group P] [MulDistribMulAction X P]
    (B : Subgroup P) : Prop :=
  ∃ (n : ℕ) (q0 : P →* LowerCentralFactor P 0)
      (U : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0))),
    2 ≤ n ∧ q0.ker = B ∧ Function.Surjective q0 ∧
    (∀ (x : X) (p : P),
      Additive.ofMul (q0 (x • p)) =
        lowerCentralFactorLinearAut
          (MulDistribMulAction.toMulAut X P x) 0
          (Additive.ofMul (q0 p))) ∧
    (∀ (x : X) (v : Additive (LowerCentralFactor P 0)),
      v ∈ U →
        lowerCentralFactorLinearAut
          (MulDistribMulAction.toMulAut X P x) 0 v ∈ U) ∧
    Nat.card U = 2 ^ n ∧ Nat.card B = 2 ^ n ∧
    Nat.card (LowerCentralFactor P 0) = (2 ^ n) ^ 2 ∧
    B ≤ Subgroup.center P ∧
    Nat.card {p : P // p ∈ involutions P} = 2 ^ n - 1

/-- The Type-B spectral branch of Lemma 12, retaining the primitive actor and
its lower-central-factor coordinates before they are erased to the abstract
Type-B group predicate. -/
@[expose] public def Lemma12TypeBActorBranchData
    (X P : Type u) [Group X] [Group P] [MulDistribMulAction X P]
    (actor : X) (B : Subgroup P) : Prop :=
  ∃ (n : ℕ) (xi : MulAut P) (q0 : P →* LowerCentralFactor P 0)
      (squareMap : Additive (LowerCentralFactor P 0) →
        Additive (LowerCentralFactor P 1)),
    n ≠ 0 ∧
    xi = MulDistribMulAction.toMulAut X P actor ∧
    q0.ker = B ∧ Function.Surjective q0 ∧
    (∀ p : P,
      Additive.ofMul (q0 (actor • p)) =
        lowerCentralFactorLinearAut xi 0 (Additive.ofMul (q0 p))) ∧
    (⊤ : Subgroup P).lowerCentralSeries 1 = B ∧
    lowerCentralFactorKernel P 1 = ⊥ ∧
    B ≤ Subgroup.center P ∧
    Nat.card B = 2 ^ n ∧
    Nat.card (LowerCentralFactor P 0) = (2 ^ n) ^ 2 ∧
    Nat.card {p : P // p ∈ involutions P} = 2 ^ n - 1 ∧
    Lemma12TypeBActorCoordinates
      (lowerCentralFactorLinearAut xi 0)
      (lowerCentralFactorLinearAut xi 1) n squareMap

/-- The canonical length-three summands together with the exact actor-module
criterion retained at the spectral branch point of Lemma 12. -/
@[expose] public def Lemma12IsomorphicSummandCriterionData
    (X P : Type u) [Group X] [Group P] [MulDistribMulAction X P]
    (B : Subgroup P) : Prop :=
  ∃ (n : ℕ) (actor : X) (xi : MulAut P)
      (q0 : P →* LowerCentralFactor P 0)
      (U V : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)))
      (xiU : U ≃ₗ[ZMod 2] U) (xiV : V ≃ₗ[ZMod 2] V),
    2 ≤ n ∧
    xi = MulDistribMulAction.toMulAut X P actor ∧
    q0.ker = B ∧ Function.Surjective q0 ∧
    (∀ (x : X) (p : P),
      Additive.ofMul (q0 (x • p)) =
        lowerCentralFactorLinearAut
          (MulDistribMulAction.toMulAut X P x) 0
          (Additive.ofMul (q0 p))) ∧
    IsCompl U V ∧
    (∀ u : U, ((xiU u : U) : Additive (LowerCentralFactor P 0)) =
      lowerCentralFactorLinearAut xi 0
        (u : Additive (LowerCentralFactor P 0))) ∧
    (∀ v : V, ((xiV v : V) : Additive (LowerCentralFactor P 0)) =
      lowerCentralFactorLinearAut xi 0
        (v : Additive (LowerCentralFactor P 0))) ∧
    (∀ W : Submodule (ZMod 2) U,
      (∀ u : U, u ∈ W → xiU u ∈ W) → W = ⊥ ∨ W = ⊤) ∧
    (∀ W : Submodule (ZMod 2) V,
      (∀ v : V, v ∈ W → xiV v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
    Nat.card U = 2 ^ n ∧ Nat.card V = 2 ^ n ∧
    B ≤ Subgroup.center P ∧ Nat.card B = 2 ^ n ∧
    Nat.card (LowerCentralFactor P 0) = (2 ^ n) ^ 2 ∧
    Nat.card {p : P // p ∈ involutions P} = 2 ^ n - 1 ∧
    ((∃ e : U ≃ₗ[ZMod 2] V, ∀ u : U, e (xiU u) = xiV (e u)) →
      Lemma12TypeBActorBranchData X P actor B)

private theorem lemma12_exists_isCompl_invariant_of_odd_linearEquiv
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (T : V ≃ₗ[ZMod 2] V) (hT : Odd (orderOf T))
    (U : Submodule (ZMod 2) V)
    (hU : ∀ v ∈ U, T v ∈ U) :
    ∃ W, IsCompl U W ∧ ∀ v ∈ W, T v ∈ W := by
  classical
  let : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective
      (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
      (fun _ _ h => LinearEquiv.ext (fun v => congrFun h v))
  let C : Subgroup (V ≃ₗ[ZMod 2] V) := Subgroup.zpowers T
  let ρ : Representation (ZMod 2) C V :=
    { toFun := fun c => (c : V ≃ₗ[ZMod 2] V).toLinearMap
      map_one' := by
        ext v
        rfl
      map_mul' := by
        intro a b
        ext v
        rfl }
  have hU_pow : ∀ j : ℕ, ∀ v ∈ U, (T ^ j) v ∈ U := by
    intro j v hv
    induction j with
    | zero => simpa using hv
    | succ j ih =>
        rw [pow_succ', LinearEquiv.mul_apply]
        exact hU _ ih
  have hUinv : U ∈ ρ.invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    intro c
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro v hv
    obtain ⟨j, hj⟩ := mem_powers_iff_mem_zpowers.mpr c.property
    change (c : V ≃ₗ[ZMod 2] V) v ∈ U
    rw [← hj]
    exact hU_pow j v hv
  let Upack : ρ.invtSubmodule := ⟨U, hUinv⟩
  let instAdd : AddCommGroup ρ.asModule :=
    Representation.instAddCommGroupAsModule ρ
  let : AddCommGroup ρ.asModule := instAdd
  let instMod : Module (MonoidAlgebra (ZMod 2) C) ρ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule ρ
  let : Module (MonoidAlgebra (ZMod 2) C) ρ.asModule := instMod
  let : Fintype C := Fintype.ofFinite C
  have hCcard : Fintype.card C = orderOf T := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_zpowers T
  have : NeZero (Fintype.card C : ZMod 2) := by
    constructor
    intro hzero
    have hdiv : 2 ∣ Fintype.card C :=
      (ZMod.natCast_eq_zero_iff (Fintype.card C) 2).1 hzero
    have hodd_card : Odd (Fintype.card C) := hCcard.symm ▸ hT
    exact hodd_card.not_two_dvd_nat hdiv
  let Umod : @Submodule (MonoidAlgebra (ZMod 2) C) ρ.asModule _
      instAdd.toAddCommMonoid instMod :=
    ρ.mapSubmodule Upack
  obtain ⟨Wmod, hUWmod⟩ := @MonoidAlgebra.Submodule.exists_isCompl'
    (ZMod 2) inferInstance C inferInstance inferInstance ρ.asModule instAdd instMod
      inferInstance Umod
  let Wpack : ρ.invtSubmodule := ρ.mapSubmodule.symm Wmod
  let W : Submodule (ZMod 2) V := Wpack
  refine ⟨W, ?_, ?_⟩
  · have hcompl_pack : IsCompl Upack Wpack := by
      exact (ρ.mapSubmodule.isCompl_iff).2
        (by simpa [Umod, Wpack] using hUWmod)
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcompl_pack ⊢
    constructor
    · simpa [Upack, W] using congrArg Subtype.val hcompl_pack.1
    · simpa [Upack, W] using congrArg Subtype.val hcompl_pack.2
  · intro v hv
    let tC : C := ⟨T, Subgroup.mem_zpowers T⟩
    have hmem := (Representation.mem_invtSubmodule (ρ := ρ)).1 Wpack.2 tC
    have hTv :=
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (ρ tC)).1 hmem v
        (by simpa [W] using hv)
    simpa [ρ, tC, W] using hTv

private theorem lemma12_irreducible_pow_two_of_irreducible
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (T : V ≃ₗ[ZMod 2] V) (k : ℕ)
    (hT_irreducible :
      ∀ W : Submodule (ZMod 2) V,
        (∀ v ∈ W, T v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∀ W : Submodule (ZMod 2) V,
      (∀ v ∈ W, (T ^ (2 ^ k)) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  classical
  let : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective
      (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
      (fun _ _ h => LinearEquiv.ext (fun v => congrFun h v))
  have hT_odd : Odd (orderOf T) := by
    rw [← Nat.not_even_iff_odd]
    intro hEven
    let : Fintype (V ≃ₗ[ZMod 2] V) := Fintype.ofFinite _
    obtain ⟨d, hd⟩ := hEven
    have hord : orderOf T = 2 * d := by
      change orderOf T = d + d at hd
      omega
    have hord_pos : 0 < orderOf T :=
      orderOf_pos_iff.mpr (isOfFinOrder_of_finite T)
    have hd_pos : 0 < d := by omega
    let S := T ^ d
    have hS_sq : S ^ 2 = 1 := by
      change (T ^ d) ^ 2 = 1
      rw [← pow_mul, Nat.mul_comm, ← hord, pow_orderOf_eq_one]
    have hS_ne : S ≠ 1 := by
      intro hS
      have hle : orderOf T ≤ d :=
        orderOf_le_of_pow_eq_one hd_pos (by simpa [S] using hS)
      omega
    have hfixed_ne_top : S.fixedSubmodule ≠ ⊤ := by
      intro htop
      have hS_refl : S = LinearEquiv.refl (ZMod 2) V :=
        LinearEquiv.fixedSubmodule_eq_top_iff.mp htop
      apply hS_ne
      simpa only [LinearEquiv.one_eq_refl] using hS_refl
    obtain ⟨v, hv⟩ : ∃ v : V, S v ≠ v := by
      by_contra h
      push Not at h
      apply hS_ne
      ext v
      simpa using h v
    let w := S v - v
    have hw_ne : w ≠ 0 := by
      simpa [w] using sub_ne_zero.mpr hv
    have hS_apply_apply : S (S v) = v := by
      calc
        S (S v) = (S * S) v := by rw [LinearEquiv.mul_apply]
        _ = v := by rw [← pow_two, hS_sq]; rfl
    have hw_fixed : S w = w := by
      dsimp [w]
      rw [map_sub, hS_apply_apply]
      simp only [sub_eq_add_neg, ZModModule.neg_eq_self, add_comm]
    have hw_mem : w ∈ S.fixedSubmodule := by
      rw [LinearMap.mem_fixedSubmodule_iff]
      exact hw_fixed
    have hfixed_ne_bot : S.fixedSubmodule ≠ ⊥ := by
      intro hbot
      have hw_bot : w ∈ (⊥ : Submodule (ZMod 2) V) := by
        rw [← hbot]
        exact hw_mem
      exact hw_ne (by simpa using hw_bot)
    have hfixed_T :
        ∀ z : V, z ∈ S.fixedSubmodule → T z ∈ S.fixedSubmodule := by
      intro z hz
      rw [LinearMap.mem_fixedSubmodule_iff] at hz ⊢
      change S z = z at hz
      change S (T z) = T z
      calc
        S (T z) = (S * T) z := rfl
        _ = (T * S) z := by
          change (T ^ d * T) z = (T * T ^ d) z
          rw [← pow_succ, pow_succ']
        _ = T (S z) := rfl
        _ = T z := by rw [hz]
    rcases hT_irreducible S.fixedSubmodule hfixed_T with hbot | htop
    · exact hfixed_ne_bot hbot
    · exact hfixed_ne_top htop
  have hcoprime : Nat.Coprime (2 ^ k) (orderOf T) :=
    Nat.Coprime.pow_left k hT_odd.coprime_two_left
  obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime (x := T) hcoprime
  intro W hW
  apply hT_irreducible W
  intro v hv
  have hpow_mem : ∀ j : ℕ, ((T ^ (2 ^ k)) ^ j) v ∈ W := by
    intro j
    induction j with
    | zero => simpa using hv
    | succ j ih =>
        rw [pow_succ', LinearEquiv.mul_apply]
        exact hW _ ih
  have hrecover : T = (T ^ (2 ^ k)) ^ r := by
    simpa [pow_mul] using hr.symm
  rw [hrecover]
  exact hpow_mem r

private theorem lemma12_odd_coordinate_degree_of_order_prime_support
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Nontrivial V]
    [Finite V] [Module.Finite (ZMod 2) V]
    (T : V ≃ₗ[ZMod 2] V)
    (hT_irreducible :
      ∀ W : Submodule (ZMod 2) V,
        (∀ v : V, v ∈ W → T v ∈ W) → W = ⊥ ∨ W = ⊤)
    (a n : ℕ) (ha : 0 < a) (hn : 0 < n)
    (hfinrank : Module.finrank (ZMod 2) V = a)
    (hbase_dvd : 2 ^ n - 1 ∣ orderOf T)
    (hfield_dvd : orderOf T ∣ 2 ^ a - 1)
    (hprime_support : ∀ p : ℕ, p.Prime → p ∣ orderOf T →
      p ∣ 2 ^ n - 1) :
    ∃ c : ℕ, Odd c ∧ a = n * c := by
  have hn_dvd_a : n ∣ a := by
    have hdvd : 2 ^ n - 1 ∣ 2 ^ a - 1 := hbase_dvd.trans hfield_dvd
    have hmod : 2 ^ (a % n) - 1 = 0 := by
      rw [← Nat.pow_sub_one_mod_pow_sub_one 2 n a]
      exact Nat.mod_eq_zero_of_dvd hdvd
    have hsmall_pow_pos : 0 < 2 ^ (a % n) := pow_pos (by omega) _
    have hpow_one : 2 ^ (a % n) = 1 := by omega
    have ha_mod : a % n = 0 :=
      (Nat.pow_eq_one.mp hpow_one).resolve_left (by omega)
    exact Nat.dvd_of_mod_eq_zero ha_mod
  obtain ⟨c, hc⟩ := hn_dvd_a
  refine ⟨c, ?_, hc⟩
  rw [← Nat.not_even_iff_odd]
  intro hc_even
  obtain ⟨d, hd⟩ := hc_even
  have ha_even : a = (n * d) * 2 := by
    rw [hc, hd, Nat.mul_add]
    omega
  have hbase_small : 2 ^ n - 1 ∣ 2 ^ (n * d) - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_right n d)
  have hbase_odd : Odd (2 ^ n - 1) := by
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    refine ⟨2 ^ e - 1, ?_⟩
    rw [pow_succ]
    have he_pos : 0 < 2 ^ e := by positivity
    omega
  have hcoprime : Nat.Coprime (orderOf T) (2 ^ (n * d) + 1) := by
    apply Nat.coprime_of_dvd'
    intro p hp hp_order hp_plus
    have hp_base : p ∣ 2 ^ n - 1 := hprime_support p hp hp_order
    have hp_minus : p ∣ 2 ^ (n * d) - 1 := hp_base.trans hbase_small
    have hp_two : p ∣ 2 := by
      apply (Nat.dvd_add_iff_right hp_minus).mpr
      have hpow_pos : 0 < 2 ^ (n * d) := by positivity
      have hadd : 2 ^ (n * d) - 1 + 2 = 2 ^ (n * d) + 1 := by
        omega
      rwa [hadd]
    have hp_eq_two : p = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp hp_two).resolve_left hp.ne_one
    subst p
    exact False.elim (hbase_odd.not_two_dvd_nat hp_base)
  have hfactor :
      2 ^ a - 1 = (2 ^ (n * d) + 1) * (2 ^ (n * d) - 1) := by
    rw [ha_even, pow_mul, pow_two]
    exact mul_self_tsub_one (2 ^ (n * d))
  have horder_small : orderOf T ∣ 2 ^ (n * d) - 1 := by
    apply hcoprime.dvd_mul_left.mp
    rw [← hfactor]
    exact hfield_dvd
  have hdim_dvd : a ∣ n * d := by
    rw [← hfinrank]
    exact lemma5_irreducible_finrank_dvd_of_order_dvd
      T hT_irreducible (n * d) horder_small
  have hnd_pos : 0 < n * d := by omega
  have hle := Nat.le_of_dvd hnd_pos hdim_dvd
  omega

private theorem lemma12_bilinear_span_eq_top_of_nonzero
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (T : V ≃ₗ[ZMod 2] V) (S : W ≃ₗ[ZMod 2] W)
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (hB_equivariant : ∀ x y : V, B (T x) (T y) = S (B x y))
    (hS_irreducible : ∀ R : Submodule (ZMod 2) W,
      (∀ z : W, z ∈ R → S z ∈ R) → R = ⊥ ∨ R = ⊤)
    (hB_nonzero : B ≠ 0) :
    Submodule.span (ZMod 2)
      (Set.range fun p : V × V => B p.1 p.2) = ⊤ := by
  let R : Submodule (ZMod 2) W :=
    Submodule.span (ZMod 2)
      (Set.range fun p : V × V => B p.1 p.2)
  have hR_invariant : ∀ z : W, z ∈ R → S z ∈ R := by
    intro z hz
    refine Submodule.span_induction
      (p := fun z _ => S z ∈ R) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      rw [← hB_equivariant]
      exact Submodule.subset_span ⟨⟨T x, T y⟩, rfl⟩
    · simp
    · intro x y _hx _hy hx hy
      simpa using R.add_mem hx hy
    · intro c x _hx hx
      simpa using R.smul_mem c hx
  have hR_ne_bot : R ≠ ⊥ := by
    intro hR_bot
    apply hB_nonzero
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    have hmem : B x y ∈ R :=
      Submodule.subset_span ⟨⟨x, y⟩, rfl⟩
    rw [hR_bot] at hmem
    simpa using hmem
  rcases hS_irreducible R hR_invariant with hbot | htop
  · exact False.elim (hR_ne_bot hbot)
  · exact htop

set_option maxHeartbeats 800000 in
private theorem lemma12_restricted_square_monomial
    {V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (n : ℕ) (hn : 0 < n)
    (T : V ≃ₗ[ZMod 2] V) (S : W ≃ₗ[ZMod 2] W)
    (lambda nu : BinaryGaloisField n) (hlambda : lambda ≠ 0)
    (hlambda_order : orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1)
    (coordinates : BinaryGaloisField n ≃ₗ[ZMod 2] V)
    (centerCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2] W)
    (hcoordinates : ∀ a, T (coordinates a) = coordinates (lambda * a))
    (hcenterCoordinates : ∀ z, S (centerCoordinates z) =
      centerCoordinates (nu * z))
    (uBasis : Module.Basis (Fin n) (BinaryGaloisField n)
      (BinaryGaloisField n ⊗[ZMod 2] V))
    (centerBasis : Module.Basis (Fin n) (BinaryGaloisField n)
      (BinaryGaloisField n ⊗[ZMod 2] W))
    (huBasis_eigen : ∀ i,
      (T.baseChange (ZMod 2) (BinaryGaloisField n) V V) (uBasis i) =
        lambda ^ (2 ^ (i : ℕ)) • uBasis i)
    (hcenterBasis_eigen : ∀ s,
      (S.baseChange (ZMod 2) (BinaryGaloisField n) W W) (centerBasis s) =
        nu ^ (2 ^ (s : ℕ)) • centerBasis s)
    (q : V → W) (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (hq_zero : q 0 = 0)
    (hq_add : ∀ x y, q (x + y) = q x + q y + B x y)
    (hq_equivariant : ∀ x, q (T x) = S (q x))
    (hq_anisotropic : ∀ x, q x = 0 → x = 0)
    (hq_surjective : Function.Surjective q)
    (hspectrum : B = 0 ∨
      ∃ i j s : Fin n, i ≠ j ∧
        lambda ^ (2 ^ (i : ℕ)) * lambda ^ (2 ^ (j : ℕ)) =
          nu ^ (2 ^ (s : ℕ))) :
    let sigma : BinaryGaloisField n ≃ₐ[ZMod 2] BinaryGaloisField n :=
      FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod 2) (BinaryGaloisField n)
    (∃ i s : Fin n, ∃ c : BinaryGaloisField n,
      B = 0 ∧ lambda ^ (2 ^ (i : ℕ)) = nu ^ (2 ^ (s : ℕ)) ∧
        c ≠ 0 ∧ ∀ a,
        (sigma ^ (s : ℕ)) (centerCoordinates.symm (q (coordinates a))) =
          c * a ^ (2 ^ (i : ℕ))) ∨
    ∃ i j s : Fin n, ∃ c : BinaryGaloisField n,
      i ≠ j ∧
        lambda ^ (2 ^ (i : ℕ)) * lambda ^ (2 ^ (j : ℕ)) =
          nu ^ (2 ^ (s : ℕ)) ∧ c ≠ 0 ∧ ∀ a,
        (sigma ^ (s : ℕ)) (centerCoordinates.symm (q (coordinates a))) =
          c * a ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) := by
  classical
  let sigma : BinaryGaloisField n ≃ₐ[ZMod 2] BinaryGaloisField n :=
    FiniteField.frobeniusAlgEquivOfAlgebraic
      (ZMod 2) (BinaryGaloisField n)
  have hsigma_apply (a : BinaryGaloisField n) (t : ℕ) :
      (sigma ^ t) a = a ^ (2 ^ t) := by
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp [ZMod.card]
  let qBase : BinaryGaloisField n → BinaryGaloisField n :=
    fun a => centerCoordinates.symm (q (coordinates a))
  have hqBase_equivariant (a : BinaryGaloisField n) :
      qBase (lambda * a) = nu * qBase a := by
    apply centerCoordinates.injective
    calc
      centerCoordinates (qBase (lambda * a)) =
          q (coordinates (lambda * a)) := by simp [qBase]
      _ = q (T (coordinates a)) := by rw [hcoordinates]
      _ = S (q (coordinates a)) := hq_equivariant _
      _ = S (centerCoordinates (qBase a)) := by simp [qBase]
      _ = centerCoordinates (nu * qBase a) := hcenterCoordinates _
  have hqBase_zero : qBase 0 = 0 := by simp [qBase, hq_zero]
  have hqBase_one_ne : qBase 1 ≠ 0 := by
    intro hzero
    have hq_one_zero : q (coordinates 1) = 0 := by
      simpa [qBase] using congrArg centerCoordinates hzero
    have hcoord_one_zero := hq_anisotropic (coordinates 1) hq_one_zero
    exact one_ne_zero
      (coordinates.injective (hcoord_one_zero.trans coordinates.map_zero.symm))
  have hlambda_units_card :
      Nat.card (BinaryGaloisField n)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, GaloisField.card 2 n hn.ne']
  have singer_formula (i s : Fin n) (e : ℕ) (he : 0 < e)
      (hseed : lambda ^ e = nu ^ (2 ^ (s : ℕ))) :
      ∃ c : BinaryGaloisField n, c ≠ 0 ∧ ∀ a,
        (sigma ^ (s : ℕ)) (qBase a) = c * a ^ e := by
    let qTwist : BinaryGaloisField n → BinaryGaloisField n :=
      fun a => (sigma ^ (s : ℕ)) (qBase a)
    have hnu_twist : (sigma ^ (s : ℕ)) nu = lambda ^ e := by
      rw [hsigma_apply]
      exact hseed.symm
    have hqTwist_equivariant (a : BinaryGaloisField n) :
        qTwist (lambda * a) = lambda ^ e * qTwist a := by
      dsimp [qTwist]
      rw [hqBase_equivariant, map_mul, hnu_twist]
    have hqTwist_zero : qTwist 0 = 0 := by
      simp [qTwist, hqBase_zero]
    have hqTwist_one_ne : qTwist 1 ≠ 0 := by
      intro hzero
      apply hqBase_one_ne
      apply (sigma ^ (s : ℕ)).injective
      simpa [qTwist] using hzero
    refine ⟨qTwist 1, hqTwist_one_ne, ?_⟩
    exact lemma11_singer_equivariant_function_eq_monomial
      lambda hlambda (hlambda_order.trans hlambda_units_card.symm)
      qTwist hqTwist_zero e he hqTwist_equivariant
  rcases hspectrum with hBzero | hpair
  · left
    let qAdd : V →+ W :=
      { toFun := q
        map_zero' := hq_zero
        map_add' := by
          intro x y
          simpa [hBzero] using hq_add x y }
    let qLinear : V →ₗ[ZMod 2] W := qAdd.toZModLinearMap 2
    let qK := qLinear.baseChange (BinaryGaloisField n)
    let TK := T.baseChange (ZMod 2) (BinaryGaloisField n) V V
    let SK := S.baseChange (ZMod 2) (BinaryGaloisField n) W W
    have hqK_equivariant (x : BinaryGaloisField n ⊗[ZMod 2] V) :
        qK (TK x) = SK (qK x) := by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a x =>
          simp only [qK, TK, SK, qLinear, LinearMap.baseChange_tmul,
            LinearEquiv.baseChange_tmul]
          change a ⊗ₜ[ZMod 2] q (T x) = a ⊗ₜ[ZMod 2] S (q x)
          rw [hq_equivariant]
    have hqK_surjective : Function.Surjective qK := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | add x y hx hy =>
          obtain ⟨x', rfl⟩ := hx
          obtain ⟨y', rfl⟩ := hy
          exact ⟨x' + y', by simp⟩
      | tmul a w =>
          obtain ⟨v, hv⟩ := hq_surjective w
          refine ⟨a ⊗ₜ[ZMod 2] v, ?_⟩
          simp only [qK, qLinear, LinearMap.baseChange_tmul]
          change a ⊗ₜ[ZMod 2] q v = a ⊗ₜ[ZMod 2] w
          rw [hv]
    have hbasis_nonzero : ∃ i : Fin n, qK (uBasis i) ≠ 0 := by
      let i0 : Fin n := ⟨0, hn⟩
      obtain ⟨x, hx⟩ := hqK_surjective (centerBasis i0)
      by_contra h
      push Not at h
      apply centerBasis.ne_zero i0
      rw [← hx, ← uBasis.sum_repr x]
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i _hi
      rw [map_smul, h i, smul_zero]
    obtain ⟨i, hi⟩ := hbasis_nonzero
    have hi_eigen :
        SK (qK (uBasis i)) =
          lambda ^ (2 ^ (i : ℕ)) • qK (uBasis i) := by
      calc
        SK (qK (uBasis i)) = qK (TK (uBasis i)) :=
          (hqK_equivariant (uBasis i)).symm
        _ = qK (lambda ^ (2 ^ (i : ℕ)) • uBasis i) := by
          rw [show TK (uBasis i) =
              lambda ^ (2 ^ (i : ℕ)) • uBasis i by
            simpa [TK] using huBasis_eigen i]
        _ = lambda ^ (2 ^ (i : ℕ)) • qK (uBasis i) := by
          rw [map_smul]
    obtain ⟨s, hs⟩ := lemma6_diagonal_eigenvalue_eq_basis_eigenvalue
      SK.toLinearMap centerBasis
      (fun t : Fin n => nu ^ (2 ^ (t : ℕ)))
      (by
        intro t
        change
          (S.baseChange (ZMod 2) (BinaryGaloisField n) W W) (centerBasis t) = _
        exact hcenterBasis_eigen t)
      (qK (uBasis i)) (lambda ^ (2 ^ (i : ℕ))) hi_eigen hi
    obtain ⟨c, hc, hformula⟩ := singer_formula i s
      (2 ^ (i : ℕ)) (by positivity) hs
    exact ⟨i, s, c, hBzero, hs, hc, by simpa [qBase] using hformula⟩
  · right
    obtain ⟨i, j, s, hij, hseed⟩ := hpair
    let e := 2 ^ (i : ℕ) + 2 ^ (j : ℕ)
    have he : 0 < e := by positivity
    have hseed' : lambda ^ e = nu ^ (2 ^ (s : ℕ)) := by
      simpa [e, pow_add] using hseed
    obtain ⟨c, hc, hformula⟩ := singer_formula i s e he hseed'
    exact ⟨i, j, s, c, hij, hseed, hc,
      by simpa [qBase, e] using hformula⟩


private theorem lemma12_pair_monomial_normalize
    (n : ℕ) (i j s : Fin n) (c : BinaryGaloisField n) (hc : c ≠ 0)
    (q : BinaryGaloisField n → BinaryGaloisField n)
    (hformula : ∀ a,
      ((FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod 2) (BinaryGaloisField n)) ^ (s : ℕ)) (q a) =
          c * a ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ))) :
    let sigma : BinaryGaloisField n ≃ₐ[ZMod 2] BinaryGaloisField n :=
      FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod 2) (BinaryGaloisField n)
    let rho := (sigma ^ (i : ℕ)).symm
    let theta := sigma ^ (j : ℕ) * rho
    ∀ a, c⁻¹ * (sigma ^ (s : ℕ)) (q (rho a)) = a * theta a := by
  let sigma : BinaryGaloisField n ≃ₐ[ZMod 2] BinaryGaloisField n :=
    FiniteField.frobeniusAlgEquivOfAlgebraic
      (ZMod 2) (BinaryGaloisField n)
  let rho := (sigma ^ (i : ℕ)).symm
  let theta := sigma ^ (j : ℕ) * rho
  have hsigma_apply (a : BinaryGaloisField n) (t : ℕ) :
      (sigma ^ t) a = a ^ (2 ^ t) := by
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp [ZMod.card]
  change ∀ a, c⁻¹ * (sigma ^ (s : ℕ)) (q (rho a)) = a * theta a
  intro a
  rw [hformula]
  have hpower : (rho a) ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) =
      a * theta a := by
    rw [pow_add, ← hsigma_apply, ← hsigma_apply]
    simp [rho, theta, AlgEquiv.mul_apply]
  rw [hpower]
  simp [hc]

private theorem lemma12_odd_period_norm_bijective
    (n : ℕ)
    (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
    (hthetaPeriod : ∃ k : ℕ, Odd k ∧ 0 < k ∧
      ∀ x : BinaryGaloisField n, theta^[k] x = x) :
    Function.Bijective (fun x : BinaryGaloisField n => x * theta x) := by
  let K : Type := BinaryGaloisField n
  have hinjective : Function.Injective (fun x : K => x * theta x) := by
    intro x y hxy
    change x * theta x = y * theta y at hxy
    by_cases hx : x = 0
    · subst x
      have hyProd : y * theta y = 0 := by
        simpa using hxy.symm
      rcases mul_eq_zero.mp hyProd with hy | hy
      · exact hy.symm
      · exact (theta.map_eq_zero_iff.mp hy).symm
    have hy : y ≠ 0 := by
      intro hy
      subst y
      have hxProd : x * theta x = 0 := by
        simpa using hxy
      exact (mul_ne_zero hx
        (fun hzero => hx (theta.map_eq_zero_iff.mp hzero))) hxProd
    let z : K := x * y⁻¹
    have hz : z ≠ 0 := mul_ne_zero hx (inv_ne_zero hy)
    have hyProd : y * theta y ≠ 0 :=
      mul_ne_zero hy (fun hzero => hy (theta.map_eq_zero_iff.mp hzero))
    have hnorm : z * theta z = 1 := by
      dsimp only [z]
      rw [map_mul, map_inv₀]
      calc
        x * y⁻¹ * (theta x * (theta y)⁻¹) =
            (x * theta x) * (y * theta y)⁻¹ := by ring
        _ = 1 := by
          rw [hxy]
          exact mul_inv_cancel₀ hyProd
    have htheta_z : theta z = z⁻¹ := by
      apply mul_left_cancel₀ hz
      rw [hnorm, mul_inv_cancel₀ hz]
    have htheta_two : theta (theta z) = z := by
      rw [htheta_z, map_inv₀, htheta_z, inv_inv]
    obtain ⟨k, hkOdd, _hkPos, hkPeriod⟩ := hthetaPeriod
    rcases hkOdd with ⟨m, rfl⟩
    have htheta_two_iter : (theta^[2]) z = z := by
      simpa [Function.iterate_succ_apply] using htheta_two
    have heven : (theta^[2 * m]) z = z := by
      calc
        (theta^[2 * m]) z = ((theta^[2])^[m]) z := by
          rw [Function.iterate_mul]
        _ = z := Function.iterate_fixed htheta_two_iter m
    have hodd : (theta^[2 * m + 1]) z = theta z := by
      rw [show 2 * m + 1 = (2 * m).succ by omega,
        Function.iterate_succ_apply', heven]
    have htheta_fixed : theta z = z :=
      hodd.symm.trans (hkPeriod z)
    have hzinv : z⁻¹ = z := htheta_z.symm.trans htheta_fixed
    have hzsq : z ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 2 [← hzinv]
      exact mul_inv_cancel₀ hz
    have hzOne : z = 1 := by
      rcases sq_eq_one_iff.mp hzsq with hzOne | hzNeg
      · exact hzOne
      · simpa [ZModModule.neg_eq_self] using hzNeg
    have hzdiv : x / y = 1 := by
      simpa [z, div_eq_mul_inv] using hzOne
    exact (div_eq_one_iff_eq hy).mp hzdiv
  exact ⟨hinjective, Finite.injective_iff_surjective.mp hinjective⟩
private theorem lemma12_frobenius_shift_normalize
    (n : ℕ) (hn : 0 < n) (i t base : Fin n)
    (a : BinaryGaloisField n) :
    let sigma : BinaryGaloisField n ≃ₐ[ZMod 2] BinaryGaloisField n :=
      FiniteField.frobeniusAlgEquivOfAlgebraic
        (ZMod 2) (BinaryGaloisField n)
    (sigma ^ (t : ℕ))
        (((sigma ^ (base : ℕ)).symm a) ^ (2 ^ (i : ℕ))) =
      (sigma ^ (((i : ℕ) + (t : ℕ) + (n - (base : ℕ))) % n)) a := by
  let K : Type := BinaryGaloisField n
  let sigma : K ≃ₐ[ZMod 2] K :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  have hsigma_order : orderOf sigma = n := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      GaloisField.finrank 2 (by omega : n ≠ 0)]
  have hsigma_pow : sigma ^ n = 1 := by
    have h := pow_orderOf_eq_one sigma
    simpa only [hsigma_order] using h
  have hsigma_apply (x : K) (m : ℕ) :
      (sigma ^ m) x = x ^ (2 ^ m) := by
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp [ZMod.card]
  let raw := (i : ℕ) + (t : ℕ) + (n - (base : ℕ))
  let norm := raw % n
  have hnorm : sigma ^ norm = sigma ^ raw := by
    apply pow_eq_pow_iff_modEq.mpr
    rw [hsigma_order]
    exact Nat.mod_modEq raw n
  have hraw : raw = ((i : ℕ) + (t : ℕ) + n) - (base : ℕ) := by
    dsimp only [raw]
    omega
  have hcomp : sigma ^ (t : ℕ) * sigma ^ (i : ℕ) *
      (sigma ^ (base : ℕ)).symm = sigma ^ norm := by
    change sigma ^ (t : ℕ) * sigma ^ (i : ℕ) *
      (sigma ^ (base : ℕ))⁻¹ = sigma ^ norm
    rw [hnorm]
    calc
      sigma ^ (t : ℕ) * sigma ^ (i : ℕ) *
            (sigma ^ (base : ℕ))⁻¹ =
          sigma ^ ((t : ℕ) + (i : ℕ)) *
            (sigma ^ (base : ℕ))⁻¹ := by rw [pow_add]
      _ = sigma ^ (((t : ℕ) + (i : ℕ) + n) - (base : ℕ)) := by
        rw [pow_sub sigma (by omega),
          pow_add sigma ((t : ℕ) + (i : ℕ)) n,
          hsigma_pow, mul_one]
      _ = sigma ^ raw := by
        congr 1
        dsimp only [raw]
        omega
  change (sigma ^ (t : ℕ))
      (((sigma ^ (base : ℕ)).symm a) ^ (2 ^ (i : ℕ))) =
    (sigma ^ norm) a
  rw [← hsigma_apply]
  change (sigma ^ (t : ℕ) * sigma ^ (i : ℕ) *
      (sigma ^ (base : ℕ)).symm) a = (sigma ^ norm) a
  rw [hcomp]
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma12_linear_pair_case_core
    {P : Type u} [Group P] [Finite P] [Fact (Nat.Prime 2)]
    [Fact (IsPGroup 2 P)] [Group.IsNilpotent P]
    (xi : MulAut P) (n : ℕ) (hn : 2 ≤ n)
    (U : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)))
    (xiU : U ≃ₗ[ZMod 2] U)
    (hxiU_val : ∀ u : U,
      (xiU u : Additive (LowerCentralFactor P 0)) =
        lowerCentralFactorLinearAut xi 0 u)
    (V : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)))
    (hUV : IsCompl U V)
    (xiV : V ≃ₗ[ZMod 2] V)
    (hxiV_val : ∀ v : V,
      (xiV v : Additive (LowerCentralFactor P 0)) =
        lowerCentralFactorLinearAut xi 0 v)
    (nu : BinaryGaloisField n)
    (centerCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1))
    (hnu : nu ≠ 0)
    (hcenterCoordinates : ∀ alpha : BinaryGaloisField n,
      lowerCentralFactorLinearAut xi 1 (centerCoordinates alpha) =
        centerCoordinates (nu * alpha))
    (bracket : Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor P 1))
    (squareMap : Additive (LowerCentralFactor P 0) →
      Additive (LowerCentralFactor P 1))
    (hbracket_equivariant :
      ∀ v w : Additive (LowerCentralFactor P 0),
        bracket (lowerCentralFactorLinearAut xi 0 v)
            (lowerCentralFactorLinearAut xi 0 w) =
          lowerCentralFactorLinearAut xi 1 (bracket v w))
    (hbracket_self :
      ∀ v : Additive (LowerCentralFactor P 0), bracket v v = 0)
    (hsquare_add :
      ∀ v w : Additive (LowerCentralFactor P 0),
        squareMap (v + w) = squareMap v + squareMap w + bracket v w)
    (hsquare_anisotropic :
      ∀ v : Additive (LowerCentralFactor P 0), squareMap v = 0 → v = 0)
    (hsquare_zero : squareMap 0 = 0)
    (hsquare_xiU_pow :
      ∀ (j : ℕ) (u : U),
        squareMap ((xiU ^ j) u : Additive (LowerCentralFactor P 0)) =
          (lowerCentralFactorLinearAut xi 1 ^ j) (squareMap u))
    (hsquareU_surjective :
      Function.Surjective
        (fun u : U => squareMap (u : Additive (LowerCentralFactor P 0))))
    (hcross_nonzero :
      ∃ u : U, ∃ v : V,
        bracket (u : Additive (LowerCentralFactor P 0))
          (v : Additive (LowerCentralFactor P 0)) ≠ 0)
    (bracketU : U →ₗ[ZMod 2] U →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1))
    (hbracketU_apply : ∀ u v : U,
      bracketU u v = bracket
        (u : Additive (LowerCentralFactor P 0))
        (v : Additive (LowerCentralFactor P 0)))
    (lambda : BinaryGaloisField n)
    (uCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2] U)
    (mu : BinaryGaloisField n)
    (vCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2] V)
    (hmu : mu ≠ 0)
    (hvCoordinates : ∀ alpha : BinaryGaloisField n,
      xiV (vCoordinates alpha) = vCoordinates (mu * alpha))
    (hmu_order : orderOf (Units.mk0 mu hmu) = 2 ^ n - 1)
    (hnu_order : orderOf (Units.mk0 nu hnu) = 2 ^ n - 1)
    (hUlinear :
      ∃ i s : Fin n, ∃ c : BinaryGaloisField n,
        bracketU = 0 ∧
          lambda ^ (2 ^ (i : ℕ)) = nu ^ (2 ^ (s : ℕ)) ∧
          c ≠ 0 ∧
          ∀ a : BinaryGaloisField n,
            (FiniteField.frobeniusAlgEquivOfAlgebraic
                (ZMod 2) (BinaryGaloisField n) ^ (s : ℕ))
                (centerCoordinates.symm
                  (squareMap (uCoordinates a :
                    Additive (LowerCentralFactor P 0)))) =
              c * a ^ (2 ^ (i : ℕ)))
    (hVpair :
      ∃ i j s : Fin n, ∃ c : BinaryGaloisField n,
        i ≠ j ∧
          mu ^ (2 ^ (i : ℕ)) * mu ^ (2 ^ (j : ℕ)) =
            nu ^ (2 ^ (s : ℕ)) ∧
          c ≠ 0 ∧
          ∀ a : BinaryGaloisField n,
            (FiniteField.frobeniusAlgEquivOfAlgebraic
                (ZMod 2) (BinaryGaloisField n) ^ (s : ℕ))
                (centerCoordinates.symm
                  (squareMap (vCoordinates a :
                    Additive (LowerCentralFactor P 0)))) =
              c * a ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ))) :
    (∃ (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
        (epsilon : BinaryGaloisField n)
        (quotientCoordinates :
          (BinaryGaloisField n × BinaryGaloisField n) ≃ₗ[ZMod 2]
            Additive (LowerCentralFactor P 0))
        (finalCenterCoordinates :
          BinaryGaloisField n ≃ₗ[ZMod 2]
            Additive (LowerCentralFactor P 1)),
      epsilon ≠ 0 ∧
      (∃ r : ℕ, Odd r ∧ 0 < r ∧
        ∀ x : BinaryGaloisField n, theta^[r] x = x) ∧
      (∀ x : BinaryGaloisField n, theta (theta (x ^ 2)) = x) ∧
      (∀ rho : BinaryGaloisField n,
        epsilon ≠ rho⁻¹ + theta (rho ^ 2) * rho) ∧
      ∀ a b : BinaryGaloisField n,
        finalCenterCoordinates.symm
            (squareMap (quotientCoordinates (a, b))) =
          a * theta a +
            epsilon * a ^ (2 ^ (n - 1)) * theta (b ^ 2) + b ^ 2) ∧
      Lemma12TypeCNormalizedData xi n U V bracket squareMap := by
  let S := lowerCentralFactorLinearAut xi 1
  let K : Type := BinaryGaloisField n
  let typeCQuadraticData : Prop :=
    ∃ (theta : K ≃+* K) (epsilon : K)
        (quotientCoordinates :
          (K × K) ≃ₗ[ZMod 2] Additive (LowerCentralFactor P 0))
        (finalCenterCoordinates :
          K ≃ₗ[ZMod 2] Additive (LowerCentralFactor P 1)),
      epsilon ≠ 0 ∧
      (∃ r : ℕ, Odd r ∧ 0 < r ∧ ∀ x : K, theta^[r] x = x) ∧
      (∀ x : K, theta (theta (x ^ 2)) = x) ∧
      (∀ rho : K, epsilon ≠ rho⁻¹ + theta (rho ^ 2) * rho) ∧
      ∀ a b : K,
        finalCenterCoordinates.symm
            (squareMap (quotientCoordinates (a, b))) =
          a * theta a +
            epsilon * a ^ (2 ^ (n - 1)) * theta (b ^ 2) + b ^ 2
  have hbracket_symm
      (x y : Additive (LowerCentralFactor P 0)) :
      bracket x y = bracket y x := by
    have hadd_self
        (z : Additive (LowerCentralFactor P 1)) : z + z = 0 := by
      rw [← two_smul (ZMod 2) z]
      simp only [CharTwo.two_eq_zero, zero_smul]
    have hsum : bracket x y + bracket y x = 0 := by
      have h := hbracket_self (x + y)
      simp only [map_add, LinearMap.add_apply] at h
      rw [hbracket_self x, hbracket_self y] at h
      simpa only [zero_add, add_zero, add_assoc, add_comm] using h
    calc
      bracket x y = bracket x y + (bracket y x + bracket y x) := by
        rw [hadd_self, add_zero]
      _ = (bracket x y + bracket y x) + bracket y x := by ac_rfl
      _ = bracket y x := by rw [hsum, zero_add]
  let swappedCrossBracket : V →ₗ[ZMod 2] U →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1) :=
    { toFun := fun v =>
        { toFun := fun u => bracket
            (v : Additive (LowerCentralFactor P 0))
            (u : Additive (LowerCentralFactor P 0))
          map_add' := by
            intro u w
            simp
          map_smul' := by
            intro c u
            simp }
      map_add' := by
        intro v w
        apply LinearMap.ext
        intro u
        simp
      map_smul' := by
        intro c v
        apply LinearMap.ext
        intro u
        simp }
  have hswappedCross_nonzero :
      ∃ v : V, ∃ u : U, swappedCrossBracket v u ≠ 0 := by
    obtain ⟨u, v, huv⟩ := hcross_nonzero
    refine ⟨v, u, ?_⟩
    change bracket
        (v : Additive (LowerCentralFactor P 0))
        (u : Additive (LowerCentralFactor P 0)) ≠ 0
    rw [hbracket_symm]
    exact huv
  have hswappedCross_equivariant (v : V) (u : U) :
      swappedCrossBracket (xiV v) (xiU u) =
        S (swappedCrossBracket v u) := by
    change bracket
        ((xiV v : V) : Additive (LowerCentralFactor P 0))
        ((xiU u : U) : Additive (LowerCentralFactor P 0)) = _
    rw [hxiV_val, hxiU_val, hbracket_equivariant]
    rfl
  have hswappedPairLinearCore :
      typeCQuadraticData ∧
        Lemma12TypeCNormalizedData xi n U V bracket squareMap := by
    rcases hVpair with
      ⟨iuRaw, juRaw, su, cu, hijuRaw, hUseedRaw, hcu, hUformulaRaw⟩
    let forwardGap (i j : Fin n) : ℕ :=
      if i.val ≤ j.val then j.val - i.val else n - (i.val - j.val)
    have horientedPair :
        ∃ iu ju : Fin n,
          iu ≠ ju ∧
          (mu ^ (2 ^ (iu : ℕ)) * mu ^ (2 ^ (ju : ℕ)) =
            nu ^ (2 ^ (su : ℕ))) ∧
          (∀ a : K,
            (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^
                (su : ℕ))
                (centerCoordinates.symm
                  (squareMap (vCoordinates a :
                    Additive (LowerCentralFactor P 0)))) =
              cu * a ^ (2 ^ (iu : ℕ) + 2 ^ (ju : ℕ))) ∧
          0 < forwardGap iu ju ∧ forwardGap iu ju ≤ n / 2 := by
      let d := lemma6_finPairGap iuRaw juRaw
      have hd_pos : 0 < d := lemma6_finPairGap_pos_of_ne hijuRaw
      have hd_lt : d < n := lemma6_finPairGap_lt iuRaw juRaw
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hijuRaw) with hlt | hgt
      · by_cases hsmall : d ≤ n / 2
        · refine ⟨iuRaw, juRaw, hijuRaw, hUseedRaw, hUformulaRaw, ?_, ?_⟩
          · simp only [forwardGap, if_pos hlt.le]
            dsimp only [d, lemma6_finPairGap] at hd_pos
            omega
          · simp only [forwardGap, if_pos hlt.le]
            dsimp only [d, lemma6_finPairGap] at hsmall
            omega
        · have hseedSwap :
              mu ^ (2 ^ (juRaw : ℕ)) *
                  mu ^ (2 ^ (iuRaw : ℕ)) =
                nu ^ (2 ^ (su : ℕ)) := by
            simpa only [mul_comm] using hUseedRaw
          have hformulaSwap : ∀ a : K,
              (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^
                  (su : ℕ))
                  (centerCoordinates.symm
                    (squareMap (vCoordinates a :
                      Additive (LowerCentralFactor P 0)))) =
                cu * a ^ (2 ^ (juRaw : ℕ) + 2 ^ (iuRaw : ℕ)) := by
            intro a
            simpa only [add_comm] using hUformulaRaw a
          refine ⟨juRaw, iuRaw, hijuRaw.symm, hseedSwap,
            hformulaSwap, ?_, ?_⟩
          · simp only [forwardGap, if_neg (Nat.not_le.mpr hlt)]
            dsimp only [d, lemma6_finPairGap] at hd_lt
            omega
          · simp only [forwardGap, if_neg (Nat.not_le.mpr hlt)]
            dsimp only [d, lemma6_finPairGap] at hsmall hd_lt
            omega
      · by_cases hsmall : d ≤ n / 2
        · have hseedSwap :
              mu ^ (2 ^ (juRaw : ℕ)) *
                  mu ^ (2 ^ (iuRaw : ℕ)) =
                nu ^ (2 ^ (su : ℕ)) := by
            simpa only [mul_comm] using hUseedRaw
          have hformulaSwap : ∀ a : K,
              (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^
                  (su : ℕ))
                  (centerCoordinates.symm
                    (squareMap (vCoordinates a :
                      Additive (LowerCentralFactor P 0)))) =
                cu * a ^ (2 ^ (juRaw : ℕ) + 2 ^ (iuRaw : ℕ)) := by
            intro a
            simpa only [add_comm] using hUformulaRaw a
          refine ⟨juRaw, iuRaw, hijuRaw.symm, hseedSwap,
            hformulaSwap, ?_, ?_⟩
          · simp only [forwardGap, if_pos hgt.le]
            omega
          · simp only [forwardGap, if_pos hgt.le]
            dsimp only [d, lemma6_finPairGap] at hsmall
            omega
        · refine ⟨iuRaw, juRaw, hijuRaw, hUseedRaw, hUformulaRaw, ?_, ?_⟩
          · simp only [forwardGap, if_neg (Nat.not_le.mpr hgt)]
            dsimp only [d, lemma6_finPairGap] at hd_lt
            omega
          · simp only [forwardGap, if_neg (Nat.not_le.mpr hgt)]
            dsimp only [d, lemma6_finPairGap] at hsmall hd_lt
            omega
    obtain ⟨iu, ju, hiju, hUseed, hUformula,
      hforwardGap_pos, hforwardGap_le⟩ := horientedPair
    rcases hUlinear with
      ⟨_iv, _sv, _cv, hbracketVZero, _hVseed, _hcv, _hVformula⟩
    let sigma : K ≃ₐ[ZMod 2] K :=
      FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
    let rhoU : K ≃ₐ[ZMod 2] K := (sigma ^ (iu : ℕ)).symm
    let thetaAlg : K ≃ₐ[ZMod 2] K := sigma ^ (ju : ℕ) * rhoU
    let theta : K ≃+* K := thetaAlg.toRingEquiv
    let cUnit : Kˣ := Units.mk0 cu hcu
    let outputTransform : K ≃ₗ[ZMod 2] K :=
      (sigma ^ (su : ℕ)).toLinearEquiv.trans
        ((cUnit⁻¹).mulLeftLinearEquiv (ZMod 2) K)
    let finalCenterCoordinates :
        K ≃ₗ[ZMod 2] Additive (LowerCentralFactor P 1) :=
      outputTransform.symm.trans centerCoordinates
    let uNorm : K ≃ₗ[ZMod 2] ↥V :=
      rhoU.toLinearEquiv.trans vCoordinates
    have huNormSquare (a : K) :
        finalCenterCoordinates.symm
            (squareMap (uNorm a :
              Additive (LowerCentralFactor P 0))) =
          a * theta a := by
      have hnormalize := lemma12_pair_monomial_normalize
        n iu ju su cu hcu
        (fun x : K => centerCoordinates.symm
          (squareMap (vCoordinates x :
            Additive (LowerCentralFactor P 0)))) hUformula a
      change (cUnit.mulLeftLinearEquiv (ZMod 2) K).symm _ = _
      rw [Units.symm_mulLeftLinearEquiv_apply]
      simpa [K, sigma, rhoU, thetaAlg, theta, cUnit, uNorm] using
        hnormalize
    have hthetaPeriod :
        ∃ r : ℕ, Odd r ∧ 0 < r ∧ ∀ x : K, theta^[r] x = x := by
      let gap := lemma6_finPairGap iu ju
      let e := 2 ^ (iu : ℕ) + 2 ^ (ju : ℕ)
      have he_pos : 0 < e := by simp [e]
      have hsigma_apply (x : K) (t : ℕ) :
          (sigma ^ t) x = x ^ (2 ^ t) := by
        rw [AlgEquiv.coe_pow,
          FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
        simp [ZMod.card]
      have hsigma_order : orderOf sigma = n := by
        rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
          GaloisField.finrank 2 (by omega : n ≠ 0)]
      have hlambda_field_order : orderOf mu = 2 ^ n - 1 := by
        calc
          orderOf mu = orderOf (Units.mk0 mu hmu) := by
            simpa using (orderOf_units
              (G := K) (y := Units.mk0 mu hmu))
          _ = 2 ^ n - 1 := hmu_order
      have hnu_twist : (sigma ^ (su : ℕ)) nu = mu ^ e := by
        rw [hsigma_apply]
        simpa [e, pow_add] using hUseed.symm
      have hlambda_e_order : orderOf (mu ^ e) = 2 ^ n - 1 := by
        calc
          orderOf (mu ^ e) = orderOf ((sigma ^ (su : ℕ)) nu) := by
            rw [hnu_twist]
          _ = orderOf nu := orderOf_injective
            (sigma ^ (su : ℕ)).toAlgHom.toMonoidHom
            (sigma ^ (su : ℕ)).injective nu
          _ = orderOf (Units.mk0 nu hnu) := by
            simpa using (orderOf_units
              (G := K) (y := Units.mk0 nu hnu))
          _ = 2 ^ n - 1 := hnu_order
      have hcop_e : Nat.Coprime (2 ^ n - 1) e := by
        have hformula := orderOf_pow' mu he_pos.ne'
        rw [hlambda_field_order] at hformula
        have hdiv : (2 ^ n - 1) / (2 ^ n - 1).gcd e = 2 ^ n - 1 :=
          hformula.symm.trans hlambda_e_order
        have hcancel := Nat.div_mul_cancel
          (Nat.gcd_dvd_left (2 ^ n - 1) e)
        rw [hdiv] at hcancel
        have hq_pos : 0 < 2 ^ n - 1 := by
          have hpow : 1 < 2 ^ n :=
            one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega)
          omega
        apply Nat.coprime_iff_gcd_eq_one.mpr
        apply (mul_left_cancel_iff_of_pos hq_pos).mp
        simpa using hcancel
      have hgap_dvd : 2 ^ gap + 1 ∣ e := by
        dsimp only [gap, e, lemma6_finPairGap]
        rcases le_total (iu : ℕ) (ju : ℕ) with hij | hji
        · refine ⟨2 ^ (iu : ℕ), ?_⟩
          calc
            2 ^ (iu : ℕ) + 2 ^ (ju : ℕ) =
                2 ^ (iu : ℕ) + 2 ^ ((iu : ℕ) + ((ju : ℕ) - (iu : ℕ))) := by
                  rw [Nat.add_sub_of_le hij]
            _ = (2 ^ (((iu : ℕ) - (ju : ℕ)) +
                  ((ju : ℕ) - (iu : ℕ))) + 1) * 2 ^ (iu : ℕ) := by
                  rw [Nat.sub_eq_zero_of_le hij, zero_add, pow_add]
                  ring
        · refine ⟨2 ^ (ju : ℕ), ?_⟩
          calc
            2 ^ (iu : ℕ) + 2 ^ (ju : ℕ) =
                2 ^ ((ju : ℕ) + ((iu : ℕ) - (ju : ℕ))) + 2 ^ (ju : ℕ) := by
                  rw [Nat.add_sub_of_le hji]
            _ = (2 ^ (((iu : ℕ) - (ju : ℕ)) +
                  ((ju : ℕ) - (iu : ℕ))) + 1) * 2 ^ (ju : ℕ) := by
                  rw [Nat.sub_eq_zero_of_le hji, add_zero, pow_add]
                  ring
      have hcop_gap : Nat.Coprime (2 ^ n - 1) (2 ^ gap + 1) :=
        hcop_e.of_dvd_right hgap_dvd
      let period := n / n.gcd gap
      have hperiod_odd : Odd period := by
        let d := n.gcd gap
        have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left gap (by omega)
        have hquot_coprime : (n / d).Coprime (gap / d) := by
          simpa [d] using Nat.coprime_div_gcd_div_gcd hd_pos
        apply Nat.not_even_iff_odd.mp
        intro hn_even
        have htwo_dvd : 2 ∣ n / d := by
          rcases (show Even (n / d) by
            simpa [period, d] using hn_even) with ⟨k, hk⟩
          exact ⟨k, by omega⟩
        have hgap_odd : Odd (gap / d) := by
          apply Nat.Coprime.odd_of_left
          exact Nat.Coprime.of_dvd htwo_dvd (dvd_refl _) hquot_coprime
        have hd_dvd_n : d ∣ n := by
          simpa [d] using Nat.gcd_dvd_left n gap
        have hd_dvd_gap : d ∣ gap := by
          simpa [d] using Nat.gcd_dvd_right n gap
        have hn_eq : d * (n / d) = n := Nat.mul_div_cancel' hd_dvd_n
        have hgap_eq : d * (gap / d) = gap :=
          Nat.mul_div_cancel' hd_dvd_gap
        let c := 2 ^ d + 1
        have hc_base : c ∣ (2 ^ d) ^ 2 - 1 := by
          refine ⟨2 ^ d - 1, ?_⟩
          simpa [c, pow_two] using mul_self_tsub_one (2 ^ d)
        have hc_dvd_n : c ∣ 2 ^ n - 1 := by
          have h := hc_base.trans
            (Nat.pow_sub_one_dvd_pow_sub_one (2 ^ d) htwo_dvd)
          simpa [c, ← pow_mul, hn_eq] using h
        have hc_dvd_gap : c ∣ 2 ^ gap + 1 := by
          have h := hgap_odd.nat_add_dvd_pow_add_pow (2 ^ d) 1
          simpa [c, ← pow_mul, hgap_eq] using h
        have hc_one := Nat.eq_one_of_dvd_coprimes
          hcop_gap hc_dvd_n hc_dvd_gap
        have hc_gt : 1 < c := by simp [c]
        exact (ne_of_gt hc_gt) hc_one
      have hsigma_gap_order : orderOf (sigma ^ gap) = period := by
        dsimp [period]
        rw [orderOf_pow, hsigma_order]
      have hthetaAlg_gap :
          thetaAlg = sigma ^ gap ∨ thetaAlg = (sigma ^ gap)⁻¹ := by
        rcases le_total (iu : ℕ) (ju : ℕ) with hij | hji
        · left
          change sigma ^ (ju : ℕ) * (sigma ^ (iu : ℕ))⁻¹ = sigma ^ gap
          rw [← pow_sub sigma hij]
          congr 1
          simp [gap, lemma6_finPairGap, Nat.sub_eq_zero_of_le hij]
        · right
          change sigma ^ (ju : ℕ) * (sigma ^ (iu : ℕ))⁻¹ =
            (sigma ^ gap)⁻¹
          rw [show gap = (iu : ℕ) - (ju : ℕ) by
            simp [gap, lemma6_finPairGap, Nat.sub_eq_zero_of_le hji]]
          rw [pow_sub sigma hji, mul_inv_rev, inv_inv]
      have hthetaAlg_order : orderOf thetaAlg = period := by
        rcases hthetaAlg_gap with hthetaAlg | hthetaAlg
        · rw [hthetaAlg, hsigma_gap_order]
        · rw [hthetaAlg, orderOf_inv, hsigma_gap_order]
      have hthetaAlg_pow : thetaAlg ^ period = 1 := by
        rw [← hthetaAlg_order]
        exact pow_orderOf_eq_one thetaAlg
      refine ⟨period, hperiod_odd, hperiod_odd.pos, ?_⟩
      intro x
      have h := DFunLike.congr_fun hthetaAlg_pow x
      simpa [theta, AlgEquiv.coe_pow] using h
    have hbracketV_zero (a b : K) :
        bracket (uCoordinates a : Additive (LowerCentralFactor P 0))
            (uCoordinates b : Additive (LowerCentralFactor P 0)) = 0 := by
      rw [← hbracketU_apply]
      simp [hbracketVZero]
    let vSquare : K →ₗ[ZMod 2] K :=
      { toFun := fun b => finalCenterCoordinates.symm
            (squareMap (uCoordinates b :
              Additive (LowerCentralFactor P 0)))
        map_add' := by
          intro a b
          rw [uCoordinates.map_add]
          change finalCenterCoordinates.symm
              (squareMap ((uCoordinates a :
                Additive (LowerCentralFactor P 0)) +
              (uCoordinates b :
                Additive (LowerCentralFactor P 0)))) = _
          rw [hsquare_add, hbracketV_zero, add_zero, map_add]
        map_smul' := by
          intro c b
          have hc : c = 0 ∨ c = 1 := by
            fin_cases c
            · left
              rfl
            · right
              rfl
          rcases hc with rfl | rfl
          · simp [hsquare_zero]
          · simp only [RingHom.id_apply, one_smul] }
    have hvSquare_injective : Function.Injective vSquare := by
      intro a b hab
      have hzero : vSquare (a - b) = 0 := by
        rw [map_sub, hab, sub_self]
      have hsquareZero :
          squareMap (uCoordinates (a - b) :
            Additive (LowerCentralFactor P 0)) = 0 := by
        apply finalCenterCoordinates.symm.injective
        simpa [vSquare] using hzero
      have hvZero : uCoordinates (a - b) = 0 := by
        apply Subtype.ext
        exact hsquare_anisotropic _ hsquareZero
      have habZero : a - b = 0 := by
        apply uCoordinates.injective
        simpa using hvZero
      exact sub_eq_zero.mp habZero
    have hvSquare_surjective : Function.Surjective vSquare := by
      intro z
      obtain ⟨v, hv⟩ := hsquareU_surjective
        (finalCenterCoordinates z)
      refine ⟨uCoordinates.symm v, ?_⟩
      change finalCenterCoordinates.symm
          (squareMap (uCoordinates (uCoordinates.symm v) :
            Additive (LowerCentralFactor P 0))) = z
      rw [uCoordinates.apply_symm_apply]
      calc
        finalCenterCoordinates.symm
            (squareMap (v : Additive (LowerCentralFactor P 0))) =
          finalCenterCoordinates.symm (finalCenterCoordinates z) :=
            congrArg finalCenterCoordinates.symm hv
        _ = z := finalCenterCoordinates.symm_apply_apply z
    let vSquareEquiv : K ≃ₗ[ZMod 2] K :=
      LinearEquiv.ofBijective vSquare
        ⟨hvSquare_injective, hvSquare_surjective⟩
    let vNorm : K ≃ₗ[ZMod 2] ↥U :=
      (sigma.toLinearEquiv.trans vSquareEquiv.symm).trans uCoordinates
    have hvNormSquare (b : K) :
        finalCenterCoordinates.symm
            (squareMap (vNorm b :
              Additive (LowerCentralFactor P 0))) =
          b ^ 2 := by
      change vSquareEquiv (vSquareEquiv.symm (sigma b)) = b ^ 2
      rw [vSquareEquiv.apply_symm_apply]
      rfl
    let lambdaNorm : K := (sigma ^ (iu : ℕ)) mu
    let nuNorm : K := (sigma ^ (su : ℕ)) nu
    let eta : K := sigma.symm nuNorm
    have hlambdaNorm : lambdaNorm ≠ 0 := by
      exact (sigma ^ (iu : ℕ)).map_ne_zero_iff.mpr hmu
    have hnuNorm : nuNorm ≠ 0 := by
      exact (sigma ^ (su : ℕ)).map_ne_zero_iff.mpr hnu
    have heta : eta ≠ 0 := by
      intro hzero
      apply hnuNorm
      have h := congrArg sigma hzero
      simpa [eta] using h
    have hUActor (a : K) :
        xiV (uNorm a) = uNorm (lambdaNorm * a) := by
      change xiV (vCoordinates (rhoU a)) =
        vCoordinates (rhoU (lambdaNorm * a))
      rw [hvCoordinates]
      apply congrArg vCoordinates
      rw [map_mul]
      congr 1
      change mu =
        (sigma ^ (iu : ℕ)).symm ((sigma ^ (iu : ℕ)) mu)
      exact ((sigma ^ (iu : ℕ)).symm_apply_apply mu).symm
    have hcenterActor (z : K) :
        S (finalCenterCoordinates z) =
          finalCenterCoordinates (nuNorm * z) := by
      change S (centerCoordinates (outputTransform.symm z)) =
        centerCoordinates (outputTransform.symm (nuNorm * z))
      rw [hcenterCoordinates]
      apply congrArg centerCoordinates
      apply outputTransform.injective
      rw [outputTransform.apply_symm_apply]
      change cu⁻¹ * (sigma ^ (su : ℕ))
          (nu * outputTransform.symm z) = nuNorm * z
      rw [map_mul]
      have hz := outputTransform.apply_symm_apply z
      change cu⁻¹ * (sigma ^ (su : ℕ))
          (outputTransform.symm z) = z at hz
      have hnuNorm_def : (sigma ^ (su : ℕ)) nu = nuNorm := rfl
      rw [hnuNorm_def]
      calc
        cu⁻¹ * (nuNorm * (sigma ^ (su : ℕ))
            (outputTransform.symm z)) =
            nuNorm * (cu⁻¹ * (sigma ^ (su : ℕ))
              (outputTransform.symm z)) := by ring
        _ = nuNorm * z := by rw [hz]
    have hnuNormFormula :
        nuNorm = lambdaNorm * theta lambdaNorm := by
      have hsigma_apply (x : K) (t : ℕ) :
          (sigma ^ t) x = x ^ (2 ^ t) := by
        rw [AlgEquiv.coe_pow,
          FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
        simp [ZMod.card]
      change (sigma ^ (su : ℕ)) nu =
        (sigma ^ (iu : ℕ)) mu *
          (sigma ^ (ju : ℕ) * (sigma ^ (iu : ℕ)).symm)
            ((sigma ^ (iu : ℕ)) mu)
      rw [AlgEquiv.mul_apply, (sigma ^ (iu : ℕ)).symm_apply_apply]
      calc
        (sigma ^ (su : ℕ)) nu = nu ^ (2 ^ (su : ℕ)) :=
          hsigma_apply nu (su : ℕ)
        _ = mu ^ (2 ^ (iu : ℕ)) *
            mu ^ (2 ^ (ju : ℕ)) := hUseed.symm
        _ = (sigma ^ (iu : ℕ)) mu *
            (sigma ^ (ju : ℕ)) mu := by
          rw [hsigma_apply, hsigma_apply]
    have hetaSquare : eta ^ 2 = nuNorm := by
      change sigma eta = nuNorm
      exact sigma.apply_symm_apply nuNorm
    have hlambdaNormOrder :
        orderOf (Units.mk0 lambdaNorm hlambdaNorm) = 2 ^ n - 1 := by
      let sigmaUnits : Kˣ →* Kˣ :=
        Units.map (sigma ^ (iu : ℕ)).toRingEquiv.toMonoidHom
      have hsigmaUnits : Function.Injective sigmaUnits :=
        Units.map_injective (sigma ^ (iu : ℕ)).injective
      have hmap :
          sigmaUnits (Units.mk0 mu hmu) =
            Units.mk0 lambdaNorm hlambdaNorm := by
        apply Units.ext
        rfl
      calc
        orderOf (Units.mk0 lambdaNorm hlambdaNorm) =
            orderOf (sigmaUnits (Units.mk0 mu hmu)) := by rw [hmap]
        _ = orderOf (Units.mk0 mu hmu) :=
          orderOf_injective sigmaUnits hsigmaUnits _
        _ = 2 ^ n - 1 := hmu_order
    have hetaOrder :
        orderOf (Units.mk0 eta heta) = 2 ^ n - 1 := by
      have hnuNormOrder :
          orderOf (Units.mk0 nuNorm hnuNorm) = 2 ^ n - 1 := by
        let sigmaUnits : Kˣ →* Kˣ :=
          Units.map (sigma ^ (su : ℕ)).toRingEquiv.toMonoidHom
        have hsigmaUnits : Function.Injective sigmaUnits :=
          Units.map_injective (sigma ^ (su : ℕ)).injective
        have hmap :
            sigmaUnits (Units.mk0 nu hnu) =
              Units.mk0 nuNorm hnuNorm := by
          apply Units.ext
          rfl
        calc
          orderOf (Units.mk0 nuNorm hnuNorm) =
              orderOf (sigmaUnits (Units.mk0 nu hnu)) := by rw [hmap]
          _ = orderOf (Units.mk0 nu hnu) :=
            orderOf_injective sigmaUnits hsigmaUnits _
          _ = 2 ^ n - 1 := hnu_order
      let sigmaUnits : Kˣ →* Kˣ := Units.map sigma.toRingEquiv.toMonoidHom
      have hsigmaUnits : Function.Injective sigmaUnits :=
        Units.map_injective sigma.injective
      have hmap :
          sigmaUnits (Units.mk0 eta heta) =
            Units.mk0 nuNorm hnuNorm := by
        apply Units.ext
        exact sigma.apply_symm_apply nuNorm
      rw [← hnuNormOrder, ← hmap]
      exact (orderOf_injective sigmaUnits hsigmaUnits _).symm
    have hVActor (b : K) :
        xiU (vNorm b) = vNorm (eta * b) := by
      have hbracketV_all (u v : U) :
          bracket (u : Additive (LowerCentralFactor P 0))
              (v : Additive (LowerCentralFactor P 0)) = 0 := by
        rw [← hbracketU_apply]
        simp [hbracketVZero]
      have hsquareV_injective : Function.Injective
          (fun v : U => squareMap
            (v : Additive (LowerCentralFactor P 0))) := by
        intro u v huv
        change squareMap (u : Additive (LowerCentralFactor P 0)) =
          squareMap (v : Additive (LowerCentralFactor P 0)) at huv
        apply Subtype.ext
        have hsumzero :
            squareMap ((u : Additive (LowerCentralFactor P 0)) +
              (v : Additive (LowerCentralFactor P 0))) = 0 := by
          rw [hsquare_add, huv, hbracketV_all,
            ZModModule.add_self, zero_add]
        have hsum := hsquare_anisotropic _ hsumzero
        exact (eq_neg_of_add_eq_zero_left hsum).trans
          (ZModModule.neg_eq_self _)
      have hcenterActorCoordinate
          (z : Additive (LowerCentralFactor P 1)) :
          finalCenterCoordinates.symm (S z) =
            nuNorm * finalCenterCoordinates.symm z := by
        calc
          finalCenterCoordinates.symm (S z) =
              finalCenterCoordinates.symm
                (S (finalCenterCoordinates
                  (finalCenterCoordinates.symm z))) := by
            rw [finalCenterCoordinates.apply_symm_apply]
          _ = finalCenterCoordinates.symm
                (finalCenterCoordinates
                  (nuNorm * finalCenterCoordinates.symm z)) := by
            rw [hcenterActor]
          _ = nuNorm * finalCenterCoordinates.symm z :=
            finalCenterCoordinates.symm_apply_apply _
      apply hsquareV_injective
      apply finalCenterCoordinates.symm.injective
      have hactor := hsquare_xiU_pow 1 (vNorm b)
      simp only [pow_one] at hactor
      calc
        finalCenterCoordinates.symm
              (squareMap (xiU (vNorm b) :
                Additive (LowerCentralFactor P 0))) =
            finalCenterCoordinates.symm
              (S (squareMap (vNorm b :
                Additive (LowerCentralFactor P 0)))) := by
          rw [hactor]
        _ = nuNorm * finalCenterCoordinates.symm
              (squareMap (vNorm b :
                Additive (LowerCentralFactor P 0))) :=
          hcenterActorCoordinate _
        _ = nuNorm * b ^ 2 := by rw [hvNormSquare]
        _ = (eta * b) ^ 2 := by rw [mul_pow, hetaSquare]
        _ = finalCenterCoordinates.symm
              (squareMap (vNorm (eta * b) :
                Additive (LowerCentralFactor P 0))) :=
          (hvNormSquare _).symm
    let normalizedCross : K →ₗ[ZMod 2] K →ₗ[ZMod 2] K :=
      { toFun := fun a =>
          { toFun := fun b => finalCenterCoordinates.symm
              (swappedCrossBracket (uNorm a) (vNorm b))
            map_add' := by
              intro b c
              simp
            map_smul' := by
              intro c b
              simp }
        map_add' := by
          intro a b
          apply LinearMap.ext
          intro c
          simp
        map_smul' := by
          intro c a
          apply LinearMap.ext
          intro b
          simp }
    obtain ⟨normalizedCoeff, hnormalizedCrossExpansionRaw,
        hnormalizedSupport⟩ :=
      PFAppendixIII.frobeniusBilinear_expansion_with_support_of_equivariant
        n (by omega) normalizedCross lambdaNorm eta nuNorm (by
          intro a b
          change finalCenterCoordinates.symm
              (swappedCrossBracket (uNorm (lambdaNorm * a))
                (vNorm (eta * b))) =
            nuNorm * finalCenterCoordinates.symm
              (swappedCrossBracket (uNorm a) (vNorm b))
          apply finalCenterCoordinates.injective
          calc
            finalCenterCoordinates
                  (finalCenterCoordinates.symm
                    (swappedCrossBracket (uNorm (lambdaNorm * a))
                      (vNorm (eta * b)))) =
                swappedCrossBracket (uNorm (lambdaNorm * a))
                  (vNorm (eta * b)) :=
              finalCenterCoordinates.apply_symm_apply _
            _ = swappedCrossBracket (xiV (uNorm a)) (xiU (vNorm b)) := by
              rw [hUActor, hVActor]
            _ = S (swappedCrossBracket (uNorm a) (vNorm b)) :=
              hswappedCross_equivariant _ _
            _ = S (finalCenterCoordinates
                (finalCenterCoordinates.symm
                  (swappedCrossBracket (uNorm a) (vNorm b)))) := by
              rw [finalCenterCoordinates.apply_symm_apply]
            _ = finalCenterCoordinates
                (nuNorm * finalCenterCoordinates.symm
                  (swappedCrossBracket (uNorm a) (vNorm b))) :=
              hcenterActor _)
    have hnormalizedCrossExpansion :
        ∀ a b : K,
          finalCenterCoordinates.symm
              (swappedCrossBracket (uNorm a) (vNorm b)) =
            ∑ i : Fin n, ∑ j : Fin n,
              normalizedCoeff i j * a ^ (2 ^ (i : ℕ)) *
                b ^ (2 ^ (j : ℕ)) := by
      simpa [K, normalizedCross] using hnormalizedCrossExpansionRaw
    have hmixedSupportedPowers :
        (∀ x : K, theta (theta (x ^ 2)) = x) ∧
          ∀ i j : Fin n, normalizedCoeff i j ≠ 0 →
            (∀ a : K,
              a ^ (2 ^ (i : ℕ)) = a ^ (2 ^ (n - 1))) ∧
            ∀ b : K,
              b ^ (2 ^ (j : ℕ)) = theta (b ^ 2) := by
      let r := forwardGap iu ju
      have hsigma_order_mixed : orderOf sigma = n := by
        rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
          GaloisField.finrank 2 (by omega : n ≠ 0)]
      have hr_pos : 0 < r := by simpa [r] using hforwardGap_pos
      have hr_le : r ≤ n / 2 := by simpa [r] using hforwardGap_le
      have hthetaFrobenius : thetaAlg = sigma ^ r := by
        have hpow_n : sigma ^ n = 1 := by
          have := pow_orderOf_eq_one sigma
          simpa only [hsigma_order_mixed] using this
        by_cases hij : (iu : ℕ) ≤ (ju : ℕ)
        · change sigma ^ (ju : ℕ) * (sigma ^ (iu : ℕ))⁻¹ = sigma ^ r
          rw [← pow_sub sigma hij]
          congr 1
          simp only [r, forwardGap, if_pos hij]
        · have hji : (ju : ℕ) ≤ (iu : ℕ) := by omega
          have hd_le : (iu : ℕ) - (ju : ℕ) ≤ n := by omega
          change sigma ^ (ju : ℕ) * (sigma ^ (iu : ℕ))⁻¹ = sigma ^ r
          rw [show r = n - ((iu : ℕ) - (ju : ℕ)) by
            simp only [r, forwardGap, if_neg hij]]
          calc
            sigma ^ (ju : ℕ) * (sigma ^ (iu : ℕ))⁻¹ =
                (sigma ^ ((iu : ℕ) - (ju : ℕ)))⁻¹ := by
              rw [pow_sub sigma hji, mul_inv_rev, inv_inv]
            _ = sigma ^ (n - ((iu : ℕ) - (ju : ℕ))) := by
              symm
              rw [pow_sub sigma hd_le, hpow_n, one_mul]
      have hn_three : 3 ≤ n := by
        by_contra hn_three
        have hn_eq : n = 2 := by omega
        have hr_eq : r = 1 := by omega
        obtain ⟨period, hperiod_odd, _hperiod_pos, hperiod⟩ :=
          hthetaPeriod
        have hthetaAlg_pow : thetaAlg ^ period = 1 := by
          apply AlgEquiv.ext
          intro x
          simpa [theta, AlgEquiv.coe_pow] using hperiod x
        have hthetaAlg_order : orderOf thetaAlg = 2 := by
          calc
            orderOf thetaAlg = orderOf (sigma ^ r) := by
              rw [hthetaFrobenius]
            _ = orderOf sigma := by rw [hr_eq, pow_one]
            _ = 2 := hsigma_order_mixed.trans hn_eq
        have htwo_dvd : 2 ∣ period := by
          rw [← hthetaAlg_order]
          exact (orderOf_dvd_iff_pow_eq_one).2 hthetaAlg_pow
        rcases htwo_dvd with ⟨k, hk⟩
        rcases hperiod_odd with ⟨l, hl⟩
        omega
      have hmixedExponentModEq :
          ∀ i j : Fin n, normalizedCoeff i j ≠ 0 →
            Nat.ModEq (2 ^ n - 1)
              (2 ^ ((i : ℕ) + 1) + 2 ^ (j : ℕ) +
                2 ^ (r + (j : ℕ)))
              (2 ^ 1 + 2 ^ (r + 1)) := by
        have hsigma_apply (x : K) (t : ℕ) :
            (sigma ^ t) x = x ^ (2 ^ t) := by
          rw [AlgEquiv.coe_pow,
            FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
          simp [ZMod.card]
        have htheta_lambda :
            theta lambdaNorm = lambdaNorm ^ (2 ^ r) := by
          change thetaAlg lambdaNorm = _
          rw [hthetaFrobenius, hsigma_apply]
        have hnu_pow (t : ℕ) :
            nuNorm ^ (2 ^ t) =
              lambdaNorm ^ (2 ^ t + 2 ^ (r + t)) := by
          calc
            nuNorm ^ (2 ^ t) =
                (lambdaNorm * theta lambdaNorm) ^ (2 ^ t) := by
              rw [hnuNormFormula]
            _ = lambdaNorm ^ (2 ^ t) *
                (lambdaNorm ^ (2 ^ r)) ^ (2 ^ t) := by
              rw [mul_pow, htheta_lambda]
            _ = lambdaNorm ^ (2 ^ t) *
                lambdaNorm ^ (2 ^ r * 2 ^ t) := by
              rw [← pow_mul]
            _ = lambdaNorm ^ (2 ^ t + 2 ^ r * 2 ^ t) := by
              rw [pow_add]
            _ = lambdaNorm ^ (2 ^ t + 2 ^ (r + t)) := by
              congr 1
              rw [pow_add]
        intro i j hij
        have hlambda_sq :
            (lambdaNorm ^ (2 ^ (i : ℕ))) ^ 2 =
              lambdaNorm ^ (2 ^ ((i : ℕ) + 1)) := by
          calc
            (lambdaNorm ^ (2 ^ (i : ℕ))) ^ 2 =
                lambdaNorm ^ (2 ^ (i : ℕ) * 2) :=
              (pow_mul lambdaNorm (2 ^ (i : ℕ)) 2).symm
            _ = lambdaNorm ^ (2 ^ ((i : ℕ) + 1)) := by
              rw [pow_succ]
        have heta_sq_pow :
            (eta ^ (2 ^ (j : ℕ))) ^ 2 =
              nuNorm ^ (2 ^ (j : ℕ)) := by
          calc
            (eta ^ (2 ^ (j : ℕ))) ^ 2 =
                eta ^ (2 ^ (j : ℕ) * 2) :=
              (pow_mul eta (2 ^ (j : ℕ)) 2).symm
            _ = eta ^ (2 * 2 ^ (j : ℕ)) := by rw [Nat.mul_comm]
            _ = (eta ^ 2) ^ (2 ^ (j : ℕ)) :=
              pow_mul eta 2 (2 ^ (j : ℕ))
            _ = nuNorm ^ (2 ^ (j : ℕ)) := by rw [hetaSquare]
        have hsupport_sq := congrArg (fun z : K => z ^ 2)
          (hnormalizedSupport i j hij)
        have hsq :
            lambdaNorm ^ (2 ^ ((i : ℕ) + 1)) *
                nuNorm ^ (2 ^ (j : ℕ)) = nuNorm ^ 2 := by
          calc
            lambdaNorm ^ (2 ^ ((i : ℕ) + 1)) *
                nuNorm ^ (2 ^ (j : ℕ)) =
                (lambdaNorm ^ (2 ^ (i : ℕ))) ^ 2 *
                  (eta ^ (2 ^ (j : ℕ))) ^ 2 := by
              rw [hlambda_sq, heta_sq_pow]
            _ = (lambdaNorm ^ (2 ^ (i : ℕ)) *
                eta ^ (2 ^ (j : ℕ))) ^ 2 := by rw [mul_pow]
            _ = nuNorm ^ 2 := hsupport_sq
        have hnu_sq :
            nuNorm ^ 2 =
              lambdaNorm ^ (2 ^ 1 + 2 ^ (r + 1)) := by
          simpa using hnu_pow 1
        have hlambdaEq := hsq
        rw [hnu_pow (j : ℕ), hnu_sq, ← pow_add] at hlambdaEq
        have hlambdaEq' :
            lambdaNorm ^
                (2 ^ ((i : ℕ) + 1) + 2 ^ (j : ℕ) +
                  2 ^ (r + (j : ℕ))) =
              lambdaNorm ^ (2 ^ 1 + 2 ^ (r + 1)) := by
          simpa only [add_assoc] using hlambdaEq
        have hunit :
            (Units.mk0 lambdaNorm hlambdaNorm) ^
                (2 ^ ((i : ℕ) + 1) + 2 ^ (j : ℕ) +
                  2 ^ (r + (j : ℕ))) =
              (Units.mk0 lambdaNorm hlambdaNorm) ^
                (2 ^ 1 + 2 ^ (r + 1)) := by
          apply Units.ext
          simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using
            hlambdaEq'
        have hmod := pow_eq_pow_iff_modEq.mp hunit
        simpa only [hlambdaNormOrder] using hmod
      have hmixedIndexCore :
          ∀ i j : Fin n, normalizedCoeff i j ≠ 0 →
            ((i : ℕ) + 1) % n = 0 ∧
              (j : ℕ) = r + 1 ∧ (2 * r + 1) % n = 0 := by
        have hn_pos : 0 < n := by omega
        have hr_lt_n : r < n := by omega
        have hr_succ_lt_n : r + 1 < n := by omega
        have hsucc_mod_inj (x y : ℕ) (hx : x < n) (hy : y < n)
            (hxy : (x + 1) % n = (y + 1) % n) : x = y := by
          have hmod : Nat.ModEq n (x + 1) (y + 1) := by
            change (x + 1) % n = (y + 1) % n
            exact hxy
          have hcancel : Nat.ModEq n x y :=
            Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) hmod
          exact hcancel.eq_of_lt_of_lt hx hy
        intro i j hij
        let a := ((i : ℕ) + 1) % n
        let c := (r + (j : ℕ)) % n
        have ha_lt : a < n := Nat.mod_lt _ hn_pos
        have hc_lt : c < n := Nat.mod_lt _ hn_pos
        have hreduce :
            Nat.ModEq (2 ^ n - 1)
              (2 ^ ((i : ℕ) + 1) + 2 ^ (j : ℕ) +
                2 ^ (r + (j : ℕ)))
              (2 ^ a + 2 ^ (j : ℕ) + 2 ^ c) := by
          have h := ((lemma6_two_pow_modEq_cyclic n ((i : ℕ) + 1)).add
            (lemma6_two_pow_modEq_cyclic n (j : ℕ))).add
              (lemma6_two_pow_modEq_cyclic n (r + (j : ℕ)))
          simpa only [a, c, Nat.mod_eq_of_lt j.isLt] using h
        have hcyclic :
            Nat.ModEq (2 ^ n - 1)
              (2 ^ a + 2 ^ (j : ℕ) + 2 ^ c)
              (2 ^ 1 + 2 ^ (r + 1)) :=
          hreduce.symm.trans (hmixedExponentModEq i j hij)
        have hjc : (j : ℕ) ≠ c := by
          intro hjc
          have hsum : Nat.ModEq n (r + (j : ℕ)) (j : ℕ) := by
            change (r + (j : ℕ)) % n = (j : ℕ) % n
            rw [Nat.mod_eq_of_lt j.isLt]
            simpa only [c] using hjc.symm
          have hr_mod : Nat.ModEq n r 0 :=
            Nat.ModEq.add_right_cancel (Nat.ModEq.refl (j : ℕ)) (by
              simpa only [Nat.zero_add] using hsum)
          have hr_zero : r = 0 :=
            hr_mod.eq_of_lt_of_lt hr_lt_n hn_pos
          omega
        have hordered (x y z : ℕ) (hxy : x < y) (hyz : y < z)
            (hz : z < n) :
            ¬ Nat.ModEq (2 ^ n - 1)
              (2 ^ x + 2 ^ y + 2 ^ z)
              (2 ^ 1 + 2 ^ (r + 1)) :=
          lemma6_triple_two_pow_not_modEq_pair_two_pow
            n x y z 1 (r + 1) hxy hyz hz (by omega) hr_succ_lt_n
        have hcollision : a = (j : ℕ) ∨ a = c := by
          by_cases haj : a = (j : ℕ)
          · exact Or.inl haj
          by_cases hac : a = c
          · exact Or.inr hac
          exfalso
          rcases lt_or_gt_of_ne haj with haj_lt | hja_lt
          · rcases lt_or_gt_of_ne hjc with hjc_lt | hcj_lt
            · exact (hordered a (j : ℕ) c haj_lt hjc_lt hc_lt)
                (by simpa only [add_assoc, add_comm, add_left_comm] using
                  hcyclic)
            · rcases lt_or_gt_of_ne hac with hac_lt | hca_lt
              · exact (hordered a c (j : ℕ) hac_lt hcj_lt j.isLt)
                  (by simpa only [add_assoc, add_comm, add_left_comm] using
                    hcyclic)
              · exact (hordered c a (j : ℕ) hca_lt haj_lt j.isLt)
                  (by simpa only [add_assoc, add_comm, add_left_comm] using
                    hcyclic)
          · rcases lt_or_gt_of_ne hac with hac_lt | hca_lt
            · exact (hordered (j : ℕ) a c hja_lt hac_lt hc_lt)
                (by simpa only [add_assoc, add_comm, add_left_comm] using
                  hcyclic)
            · rcases lt_or_gt_of_ne hjc with hjc_lt | hcj_lt
              · exact (hordered (j : ℕ) c a hjc_lt hca_lt ha_lt)
                  (by simpa only [add_assoc, add_comm, add_left_comm] using
                    hcyclic)
              · exact (hordered c (j : ℕ) a hcj_lt hja_lt ha_lt)
                  (by simpa only [add_assoc, add_comm, add_left_comm] using
                    hcyclic)
        rcases hcollision with haj | hac
        · have hrepeat :
              Nat.ModEq (2 ^ n - 1)
                (2 ^ c + 2 ^ a + 2 ^ a)
                (2 ^ 1 + 2 ^ (r + 1)) := by
            simpa only [haj, add_assoc, add_comm, add_left_comm] using
              hcyclic
          rcases lemma6_repeated_two_pow_collision_classify
              n c a 1 (r + 1) hn_pos hc_lt ha_lt (by omega)
                hr_succ_lt_n hrepeat with hfirst | hsecond
          · have ha_eq_r : a = r :=
              hsucc_mod_inj a r ha_lt hr_lt_n (by
                simpa only [Nat.mod_eq_of_lt hr_succ_lt_n] using
                  hfirst.2)
            have hj_eq_r : (j : ℕ) = r := haj.symm.trans ha_eq_r
            have htwor_mod : (2 * r) % n = 1 := by
              simpa only [c, hj_eq_r, two_mul] using hfirst.1
            have htwor_le : 2 * r ≤ n := by omega
            by_cases htwor_lt : 2 * r < n
            · rw [Nat.mod_eq_of_lt htwor_lt] at htwor_mod
              omega
            · have htwor_eq : 2 * r = n := by omega
              rw [htwor_eq, Nat.mod_self] at htwor_mod
              omega
          · have hone_lt : 1 < n := by omega
            have ha_zero : a = 0 :=
              hsucc_mod_inj a 0 ha_lt hn_pos (by
                simpa only [Nat.zero_add, Nat.mod_eq_of_lt hone_lt] using
                  hsecond.2)
            have hj_zero : (j : ℕ) = 0 := haj.symm.trans ha_zero
            have hc_eq_r : c = r := by
              simp only [c, hj_zero, Nat.add_zero,
                Nat.mod_eq_of_lt hr_lt_n]
            omega
        · have hrepeat :
              Nat.ModEq (2 ^ n - 1)
                (2 ^ (j : ℕ) + 2 ^ a + 2 ^ a)
                (2 ^ 1 + 2 ^ (r + 1)) := by
            simpa only [hac, add_assoc, add_comm, add_left_comm] using
              hcyclic
          rcases lemma6_repeated_two_pow_collision_classify
              n (j : ℕ) a 1 (r + 1) hn_pos j.isLt ha_lt (by omega)
                hr_succ_lt_n hrepeat with hfirst | hsecond
          · have ha_eq_r : a = r :=
              hsucc_mod_inj a r ha_lt hr_lt_n (by
                simpa only [Nat.mod_eq_of_lt hr_succ_lt_n] using
                  hfirst.2)
            have hc_eq_succ : c = r + 1 := by
              simp only [c, hfirst.1, Nat.mod_eq_of_lt hr_succ_lt_n]
            omega
          · have hone_lt : 1 < n := by omega
            have ha_zero : a = 0 :=
              hsucc_mod_inj a 0 ha_lt hn_pos (by
                simpa only [Nat.zero_add, Nat.mod_eq_of_lt hone_lt] using
                  hsecond.2)
            have hc_zero : c = 0 := hac.symm.trans ha_zero
            have htwor_succ : (2 * r + 1) % n = 0 := by
              simpa only [c, hsecond.1, two_mul, add_assoc] using hc_zero
            exact ⟨by simpa only [a] using ha_zero,
              hsecond.1, htwor_succ⟩
      have hsupportedExists :
          ∃ i j : Fin n, normalizedCoeff i j ≠ 0 := by
        by_contra hexists
        have hcoeff_zero (i j : Fin n) : normalizedCoeff i j = 0 := by
          by_contra hij
          exact hexists ⟨i, j, hij⟩
        obtain ⟨u, v, huv⟩ := hswappedCross_nonzero
        have hzero :
            finalCenterCoordinates.symm (swappedCrossBracket u v) = 0 := by
          have h := hnormalizedCrossExpansion
            (uNorm.symm u) (vNorm.symm v)
          rw [uNorm.apply_symm_apply, vNorm.apply_symm_apply] at h
          rw [h]
          simp [hcoeff_zero]
        apply huv
        apply finalCenterCoordinates.symm.injective
        simpa using hzero
      have hthetaSquare : ∀ x : K, theta (theta (x ^ 2)) = x := by
        obtain ⟨i, j, hij⟩ := hsupportedExists
        have hthird := (hmixedIndexCore i j hij).2.2
        have hmod_n : Nat.ModEq n (2 * r + 1) 0 := by
          change (2 * r + 1) % n = 0 % n
          simpa using hthird
        have hmod_sigma :
            Nat.ModEq (orderOf sigma) (2 * r + 1) 0 := by
          simpa only [hsigma_order_mixed] using hmod_n
        have hsigma_pow : sigma ^ (2 * r + 1) = 1 := by
          simpa using (pow_eq_pow_iff_modEq.mpr hmod_sigma)
        have hsigma_apply (x : K) (t : ℕ) :
            (sigma ^ t) x = x ^ (2 ^ t) := by
          rw [AlgEquiv.coe_pow,
            FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
          simp [ZMod.card]
        have htheta_apply (x : K) :
            theta x = x ^ (2 ^ r) := by
          change thetaAlg x = _
          rw [hthetaFrobenius, hsigma_apply]
        have hexponent :
            2 * (2 ^ r * 2 ^ r) = 2 ^ (2 * r + 1) := by
          rw [show 2 * r = r + r by omega, pow_succ, pow_add]
          ring
        intro x
        calc
          theta (theta (x ^ 2)) =
              ((x ^ 2) ^ (2 ^ r)) ^ (2 ^ r) := by
            rw [htheta_apply, htheta_apply]
          _ = x ^ (2 * (2 ^ r * 2 ^ r)) := by
            rw [pow_mul, pow_mul]
          _ = x ^ (2 ^ (2 * r + 1)) := by rw [hexponent]
          _ = (sigma ^ (2 * r + 1)) x :=
            (hsigma_apply x (2 * r + 1)).symm
          _ = x := by rw [hsigma_pow]; rfl
      have hsupportedPowers :
          ∀ i j : Fin n, normalizedCoeff i j ≠ 0 →
            (∀ a : K,
              a ^ (2 ^ (i : ℕ)) = a ^ (2 ^ (n - 1))) ∧
            ∀ b : K,
              b ^ (2 ^ (j : ℕ)) = theta (b ^ 2) := by
        have hsigma_apply (x : K) (t : ℕ) :
            (sigma ^ t) x = x ^ (2 ^ t) := by
          rw [AlgEquiv.coe_pow,
            FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
          simp [ZMod.card]
        have htheta_apply (x : K) :
            theta x = x ^ (2 ^ r) := by
          change thetaAlg x = _
          rw [hthetaFrobenius, hsigma_apply]
        intro i j hij
        have hindices := hmixedIndexCore i j hij
        have hi_eq : (i : ℕ) = n - 1 := by
          have hi_succ_le : (i : ℕ) + 1 ≤ n := by omega
          by_cases hi_succ_lt : (i : ℕ) + 1 < n
          · rw [Nat.mod_eq_of_lt hi_succ_lt] at hindices
            omega
          · omega
        refine ⟨?_, ?_⟩
        · intro a
          rw [hi_eq]
        · intro b
          rw [hindices.2.1]
          calc
            b ^ (2 ^ (r + 1)) = b ^ (2 ^ r * 2) := by rw [pow_succ]
            _ = b ^ (2 * 2 ^ r) := by rw [Nat.mul_comm]
            _ = (b ^ 2) ^ (2 ^ r) := pow_mul b 2 (2 ^ r)
            _ = theta (b ^ 2) := (htheta_apply (b ^ 2)).symm
      exact ⟨hthetaSquare, hsupportedPowers⟩
    obtain ⟨hthetaSquare, hmixedSupportedPowers⟩ :=
      hmixedSupportedPowers
    have hcrossTerm :
        ∃ epsilon : K, epsilon ≠ 0 ∧
          ∀ a b : K,
            finalCenterCoordinates.symm
                (swappedCrossBracket (uNorm a) (vNorm b)) =
              epsilon * a ^ (2 ^ (n - 1)) * theta (b ^ 2) := by
      let epsilon : K := ∑ i : Fin n, ∑ j : Fin n, normalizedCoeff i j
      have hformula (a b : K) :
          finalCenterCoordinates.symm
              (swappedCrossBracket (uNorm a) (vNorm b)) =
            epsilon * a ^ (2 ^ (n - 1)) * theta (b ^ 2) := by
        rw [hnormalizedCrossExpansion]
        calc
          (∑ i : Fin n, ∑ j : Fin n,
              normalizedCoeff i j * a ^ (2 ^ (i : ℕ)) *
                b ^ (2 ^ (j : ℕ))) =
              ∑ i : Fin n, ∑ j : Fin n,
                normalizedCoeff i j * a ^ (2 ^ (n - 1)) *
                  theta (b ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases hij : normalizedCoeff i j = 0
            · simp [hij]
            · rw [(hmixedSupportedPowers i j hij).1 a,
                (hmixedSupportedPowers i j hij).2 b]
          _ = epsilon * a ^ (2 ^ (n - 1)) * theta (b ^ 2) := by
            dsimp only [epsilon]
            rw [Finset.sum_mul, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.sum_mul, Finset.sum_mul]
      have hepsilon : epsilon ≠ 0 := by
        intro hepsilon
        obtain ⟨u, v, huv⟩ := hswappedCross_nonzero
        have hzero :
            finalCenterCoordinates.symm (swappedCrossBracket u v) = 0 := by
          have h := hformula (uNorm.symm u) (vNorm.symm v)
          rw [uNorm.apply_symm_apply, vNorm.apply_symm_apply,
            hepsilon] at h
          simpa using h
        apply huv
        apply finalCenterCoordinates.symm.injective
        simpa using hzero
      exact ⟨epsilon, hepsilon, hformula⟩
    obtain ⟨epsilon, hepsilon, hcrossTerm⟩ := hcrossTerm
    have hsquareRoot (x : K) :
        (x ^ 2) ^ (2 ^ (n - 1)) = x := by
      have hsigma_order : orderOf sigma = n := by
        rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
          GaloisField.finrank 2 (by omega : n ≠ 0)]
      have hsigma_pow : sigma ^ n = 1 := by
        have := pow_orderOf_eq_one sigma
        simpa only [hsigma_order] using this
      have hsigma_apply (x : K) (t : ℕ) :
          (sigma ^ t) x = x ^ (2 ^ t) := by
        rw [AlgEquiv.coe_pow,
          FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
        simp [ZMod.card]
      have htwo_pow : 2 ^ n = 2 ^ (n - 1) * 2 := by
        calc
          2 ^ n = 2 ^ (n - 1 + 1) := by
            congr 1
            omega
          _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
      calc
        (x ^ 2) ^ (2 ^ (n - 1)) =
            x ^ (2 * 2 ^ (n - 1)) :=
          (pow_mul x 2 (2 ^ (n - 1))).symm
        _ = x ^ (2 ^ n) := by
          congr 1
          rw [htwo_pow, Nat.mul_comm]
        _ = (sigma ^ n) x := (hsigma_apply x n).symm
        _ = x := by rw [hsigma_pow]; rfl
    let quotientCoordinates :
        (K × K) ≃ₗ[ZMod 2] Additive (LowerCentralFactor P 0) :=
      (uNorm.prodCongr vNorm).trans
        (Submodule.prodEquivOfIsCompl V U hUV.symm)
    have hq (a b : K) :
        finalCenterCoordinates.symm
            (squareMap (quotientCoordinates (a, b))) =
          a * theta a +
            epsilon * a ^ (2 ^ (n - 1)) * theta (b ^ 2) + b ^ 2 := by
      change finalCenterCoordinates.symm
          (squareMap ((uNorm a : Additive (LowerCentralFactor P 0)) +
            (vNorm b : Additive (LowerCentralFactor P 0)))) = _
      rw [hsquare_add]
      simp only [map_add]
      change
        finalCenterCoordinates.symm
            (squareMap (uNorm a :
              Additive (LowerCentralFactor P 0))) +
          finalCenterCoordinates.symm
            (squareMap (vNorm b :
              Additive (LowerCentralFactor P 0))) +
          finalCenterCoordinates.symm
            (swappedCrossBracket (uNorm a) (vNorm b)) = _
      rw [huNormSquare, hvNormSquare, hcrossTerm]
      ring
    have havoid :
        ∀ rho : K, epsilon ≠ rho⁻¹ + theta (rho ^ 2) * rho := by
      intro rho heq
      by_cases hrho : rho = 0
      · subst rho
        apply hepsilon
        simpa using heq
      · have hcenterZero :
            finalCenterCoordinates.symm
                (squareMap (quotientCoordinates (rho ^ 2, 1))) = 0 := by
          rw [hq, hsquareRoot, heq, add_mul, inv_mul_cancel₀ hrho]
          simp only [map_one, one_pow, mul_one]
          calc
            rho ^ 2 * theta (rho ^ 2) +
                (1 + theta (rho ^ 2) * rho * rho) + 1 =
              (rho ^ 2 * theta (rho ^ 2) +
                rho ^ 2 * theta (rho ^ 2)) + (1 + 1) := by
                  ring
            _ = 0 := by
              rw [ZModModule.add_self, ZModModule.add_self, zero_add]
        have hsquareZero :
            squareMap (quotientCoordinates (rho ^ 2, 1)) = 0 := by
          apply finalCenterCoordinates.symm.injective
          simpa using hcenterZero
        have hquotientZero :
            quotientCoordinates (rho ^ 2, 1) = 0 :=
          hsquare_anisotropic _ hsquareZero
        have hpZero : (rho ^ 2, (1 : K)) = 0 :=
          quotientCoordinates.map_eq_zero_iff.mp hquotientZero
        exact one_ne_zero (congrArg Prod.snd hpZero)
    refine ⟨
      ⟨theta, epsilon, quotientCoordinates, finalCenterCoordinates,
        hepsilon, hthetaPeriod, hthetaSquare, havoid, hq⟩, ?_⟩
    refine ⟨theta, lambdaNorm, eta, epsilon, uNorm, vNorm,
      finalCenterCoordinates, hlambdaNorm, heta, hepsilon,
      hthetaPeriod, hthetaSquare, hlambdaNormOrder, hetaOrder,
      hetaSquare.trans hnuNormFormula, ?_, ?_, ?_, hvNormSquare, ?_⟩
    · intro a
      rw [← hxiV_val, hUActor]
    · intro b
      rw [← hxiU_val, hVActor]
    · intro z
      simpa only [S, hetaSquare] using hcenterActor z
    · intro a b
      rw [hbracket_symm]
      exact hcrossTerm a b
  exact hswappedPairLinearCore

private lemma lemma12_modEq_eq_of_pos_of_le
    {m x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hxle : x ≤ m) (hyle : y ≤ m) (hmod : Nat.ModEq m x y) :
    x = y := by
  rcases hxle.eq_or_lt with hxEq | hxlt
  · rcases hyle.eq_or_lt with hyEq | hylt
    · exact hxEq.trans hyEq.symm
    · rw [hxEq] at hmod
      change m % m = y % m at hmod
      rw [Nat.mod_self, Nat.mod_eq_of_lt hylt] at hmod
      omega
  · rcases hyle.eq_or_lt with hyEq | hylt
    · rw [hyEq] at hmod
      change x % m = m % m at hmod
      rw [Nat.mod_self, Nat.mod_eq_of_lt hxlt] at hmod
      omega
    · exact hmod.eq_of_lt_of_lt hxlt hylt

private lemma lemma12_sum_range_two_pow (n : ℕ) :
    (∑ i ∈ Finset.range n, 2 ^ i) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have hp : 0 < 2 ^ n := Nat.two_pow_pos n
      omega

private theorem lemma12_finset_two_pow_sum_injective
    (n : ℕ) (A B : Finset ℕ)
    (hA : A ⊆ Finset.range n) (hB : B ⊆ Finset.range n)
    (heq : (∑ i ∈ A, 2 ^ i) = ∑ i ∈ B, 2 ^ i) :
    A = B := by
  induction n generalizing A B with
  | zero =>
      have hAe : A = ∅ := Finset.subset_empty.mp (by simpa using hA)
      have hBe : B = ∅ := Finset.subset_empty.mp (by simpa using hB)
      rw [hAe, hBe]
  | succ n ih =>
      by_cases hnA : n ∈ A
      · by_cases hnB : n ∈ B
        · have hplus :
              (∑ i ∈ A.erase n, 2 ^ i) + 2 ^ n =
                (∑ i ∈ B.erase n, 2 ^ i) + 2 ^ n := by
            calc
              (∑ i ∈ A.erase n, 2 ^ i) + 2 ^ n =
                  ∑ i ∈ A, 2 ^ i := Finset.sum_erase_add A _ hnA
              _ = ∑ i ∈ B, 2 ^ i := heq
              _ = (∑ i ∈ B.erase n, 2 ^ i) + 2 ^ n :=
                (Finset.sum_erase_add B _ hnB).symm
          have heq' :
              (∑ i ∈ A.erase n, 2 ^ i) =
                ∑ i ∈ B.erase n, 2 ^ i := by omega
          have hAsub : A.erase n ⊆ Finset.range n := by
            intro x hx
            have hxA := Finset.mem_of_mem_erase hx
            have hxn := Finset.ne_of_mem_erase hx
            have hxlt : x < n + 1 := Finset.mem_range.mp (hA hxA)
            exact Finset.mem_range.mpr (by omega)
          have hBsub : B.erase n ⊆ Finset.range n := by
            intro x hx
            have hxB := Finset.mem_of_mem_erase hx
            have hxn := Finset.ne_of_mem_erase hx
            have hxlt : x < n + 1 := Finset.mem_range.mp (hB hxB)
            exact Finset.mem_range.mpr (by omega)
          have herase := ih (A.erase n) (B.erase n) hAsub hBsub heq'
          calc
            A = insert n (A.erase n) := (Finset.insert_erase hnA).symm
            _ = insert n (B.erase n) := by rw [herase]
            _ = B := Finset.insert_erase hnB
        · have hBsub : B ⊆ Finset.range n := by
            intro x hx
            have hxlt : x < n + 1 := Finset.mem_range.mp (hB hx)
            have hxne : x ≠ n := by
              intro hxn
              subst x
              exact hnB hx
            exact Finset.mem_range.mpr (by omega)
          have hBupper :
              (∑ i ∈ B, 2 ^ i) ≤ 2 ^ n - 1 := by
            rw [← lemma12_sum_range_two_pow n]
            exact Finset.sum_le_sum_of_subset hBsub
          have hAlower : 2 ^ n ≤ ∑ i ∈ A, 2 ^ i := by
            calc
              2 ^ n ≤ (∑ i ∈ A.erase n, 2 ^ i) + 2 ^ n := by omega
              _ = ∑ i ∈ A, 2 ^ i := Finset.sum_erase_add A _ hnA
          have hp : 0 < 2 ^ n := Nat.two_pow_pos n
          omega
      · by_cases hnB : n ∈ B
        · have hAsub : A ⊆ Finset.range n := by
            intro x hx
            have hxlt : x < n + 1 := Finset.mem_range.mp (hA hx)
            have hxne : x ≠ n := by
              intro hxn
              subst x
              exact hnA hx
            exact Finset.mem_range.mpr (by omega)
          have hAupper :
              (∑ i ∈ A, 2 ^ i) ≤ 2 ^ n - 1 := by
            rw [← lemma12_sum_range_two_pow n]
            exact Finset.sum_le_sum_of_subset hAsub
          have hBlower : 2 ^ n ≤ ∑ i ∈ B, 2 ^ i := by
            calc
              2 ^ n ≤ (∑ i ∈ B.erase n, 2 ^ i) + 2 ^ n := by omega
              _ = ∑ i ∈ B, 2 ^ i := Finset.sum_erase_add B _ hnB
          have hp : 0 < 2 ^ n := Nat.two_pow_pos n
          omega
        · have hAsub : A ⊆ Finset.range n := by
            intro x hx
            have hxlt : x < n + 1 := Finset.mem_range.mp (hA hx)
            have hxne : x ≠ n := by
              intro hxn
              subst x
              exact hnA hx
            exact Finset.mem_range.mpr (by omega)
          have hBsub : B ⊆ Finset.range n := by
            intro x hx
            have hxlt : x < n + 1 := Finset.mem_range.mp (hB hx)
            have hxne : x ≠ n := by
              intro hxn
              subst x
              exact hnB hx
            exact Finset.mem_range.mpr (by omega)
          exact ih A B hAsub hBsub heq

private theorem lemma12_cyclic_two_pow_normalize
    (n : ℕ) (hn : 0 < n) (l : Multiset (Fin n)) :
    ∃ t : Finset (Fin n),
      (l ≠ 0 → t.Nonempty) ∧
      t.card ≤ l.card ∧
      (t.card = l.card → l.Nodup) ∧
      Nat.ModEq (2 ^ n - 1)
        ((l.map fun i => 2 ^ i.val).sum)
        (∑ i ∈ t, 2 ^ i.val) := by
  classical
  induction hcard : l.card using Nat.strong_induction_on generalizing l with
  | h k ih =>
    by_cases hnodup : l.Nodup
    · refine ⟨l.toFinset, ?_, ?_, ?_, ?_⟩
      · intro hl
        exact Multiset.toFinset_nonempty.mpr hl
      · rw [Multiset.toFinset_card_of_nodup hnodup, hcard]
      · intro _hcard
        exact hnodup
      · have heq :
            ((l.map fun i => 2 ^ i.val).sum) =
              ∑ i ∈ l.toFinset, 2 ^ i.val := by
          change (l.map fun i => 2 ^ i.val).sum =
            (l.dedup.map fun i => 2 ^ i.val).sum
          rw [Multiset.dedup_eq_self.mpr hnodup]
        exact heq ▸ Nat.ModEq.refl _
    · have hshape : ∃ a rest, l = a ::ₘ a ::ₘ rest := by
        rw [Multiset.nodup_iff_ne_cons_cons] at hnodup
        push Not at hnodup
        exact hnodup
      obtain ⟨a, rest, hl⟩ := hshape
      let a' : Fin n := ⟨(a.val + 1) % n, Nat.mod_lt _ hn⟩
      have hlt : (a' ::ₘ rest).card < k := by
        rw [← hcard, hl]
        simp
      obtain ⟨t, ht_nonempty, ht_card, ht_nodup, ht_mod⟩ :=
        ih (a' ::ₘ rest).card hlt (a' ::ₘ rest) rfl
      refine ⟨t, ?_, ?_, ?_, ?_⟩
      · intro _hl
        exact ht_nonempty (by simp)
      · exact ht_card.trans (Nat.le_of_lt hlt)
      · intro ht_eq
        have hlt' : t.card < k := lt_of_le_of_lt ht_card hlt
        omega
      · have hcarry := lemma6_two_pow_add_self_modEq_cyclic
          n a.val hn a.isLt
        have hrest : Nat.ModEq (2 ^ n - 1)
            ((rest.map fun i => 2 ^ i.val).sum)
            ((rest.map fun i => 2 ^ i.val).sum) :=
          Nat.ModEq.refl _
        have hstep := hcarry.add hrest
        have hstep' : Nat.ModEq (2 ^ n - 1)
            (((a ::ₘ a ::ₘ rest).map fun i => 2 ^ i.val).sum)
            (((a' ::ₘ rest).map fun i => 2 ^ i.val).sum) := by
          simpa only [Multiset.map_cons, Multiset.sum_cons, a',
            add_assoc] using hstep
        rw [hl]
        exact hstep'.trans ht_mod

set_option maxHeartbeats 800000 in
private theorem lemma12_distinct_pair_support
    (n r s i j : ℕ)
    (hn : 0 < n)
    (hr_pos : 0 < r) (hr_le : r ≤ n / 2)
    (hs_pos : 0 < s) (hs_le : s ≤ n / 2)
    (hdiff : r ≠ s) (hi : i < n) (hj : j < n)
    (hmod : Nat.ModEq (2 ^ n - 1)
      (2 ^ i + 2 ^ ((i + s) % n) +
        2 ^ j + 2 ^ ((j + r) % n))
      (2 ^ 0 + 2 ^ r + 2 ^ s + 2 ^ (r + s))) :
    (i = 0 ∨ i = r ∨ i = s ∨ i = r + s) ∧
    ((i + s) % n = 0 ∨ (i + s) % n = r ∨
      (i + s) % n = s ∨ (i + s) % n = r + s) ∧
    (j = 0 ∨ j = r ∨ j = s ∨ j = r + s) ∧
    ((j + r) % n = 0 ∨ (j + r) % n = r ∨
      (j + r) % n = s ∨ (j + r) % n = r + s) ∧
    i ≠ (i + s) % n ∧ i ≠ j ∧ i ≠ (j + r) % n ∧
    (i + s) % n ≠ j ∧ (i + s) % n ≠ (j + r) % n ∧
    j ≠ (j + r) % n ∧
    ((i + s < n ∧ (i + s) % n = i + s) ∨
      (n ≤ i + s ∧ (i + s) % n = i + s - n)) ∧
    ((j + r < n ∧ (j + r) % n = j + r) ∨
      (n ≤ j + r ∧ (j + r) % n = j + r - n)) := by
  classical
  have hrs_lt : r + s < n := by omega
  let iF : Fin n := ⟨i, hi⟩
  let isF : Fin n := ⟨(i + s) % n, Nat.mod_lt _ hn⟩
  let jF : Fin n := ⟨j, hj⟩
  let jrF : Fin n := ⟨(j + r) % n, Nat.mod_lt _ hn⟩
  let l : Multiset (Fin n) := {iF, isF, jF, jrF}
  let R : Finset ℕ := {0, r, s, r + s}
  have h0mem : 0 ∉ ({r, s, r + s} : Finset ℕ) := by
    simp
    omega
  have hrmem : r ∉ ({s, r + s} : Finset ℕ) := by
    simp
    omega
  have hsmem : s ∉ ({r + s} : Finset ℕ) := by
    simp
    omega
  have hRcard : R.card = 4 := by
    dsimp only [R]
    rw [Finset.card_insert_of_notMem h0mem,
      Finset.card_insert_of_notMem hrmem,
      Finset.card_insert_of_notMem hsmem]
    simp
  have hRsum :
      (∑ x ∈ R, 2 ^ x) =
        2 ^ 0 + 2 ^ r + 2 ^ s + 2 ^ (r + s) := by
    dsimp only [R]
    rw [Finset.sum_insert h0mem, Finset.sum_insert hrmem,
      Finset.sum_insert hsmem]
    simp
    ring
  have hRsub : R ⊆ Finset.range n := by
    intro x hx
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      exact Finset.mem_range.mpr (by omega)
  obtain ⟨t, ht_nonempty, ht_card, ht_nodup, ht_mod⟩ :=
    lemma12_cyclic_two_pow_normalize n hn l
  let T : Finset ℕ := t.image Fin.val
  have hTcard : T.card = t.card := by
    exact Finset.card_image_of_injective t Fin.val_injective
  have hTsum :
      (∑ x ∈ T, 2 ^ x) = ∑ x ∈ t, 2 ^ x.val := by
    exact Finset.sum_image Fin.val_injective.injOn
  have hTsub : T ⊆ Finset.range n := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, _hy, rfl⟩
    exact Finset.mem_range.mpr y.isLt
  have hTne : T.Nonempty := by
    apply Finset.Nonempty.image
    exact ht_nonempty (by simp [l])
  have hTpos : 0 < ∑ x ∈ T, 2 ^ x :=
    Finset.sum_pos (fun x _hx => Nat.two_pow_pos x) hTne
  have hRne : R.Nonempty := by
    refine ⟨0, ?_⟩
    simp [R]
  have hRpos : 0 < ∑ x ∈ R, 2 ^ x :=
    Finset.sum_pos (fun x _hx => Nat.two_pow_pos x) hRne
  have hTle : (∑ x ∈ T, 2 ^ x) ≤ 2 ^ n - 1 := by
    rw [← lemma12_sum_range_two_pow n]
    exact Finset.sum_le_sum_of_subset hTsub
  have hRle : (∑ x ∈ R, 2 ^ x) ≤ 2 ^ n - 1 := by
    rw [← lemma12_sum_range_two_pow n]
    exact Finset.sum_le_sum_of_subset hRsub
  have hlmod : Nat.ModEq (2 ^ n - 1)
      ((l.map fun x => 2 ^ x.val).sum)
      (2 ^ 0 + 2 ^ r + 2 ^ s + 2 ^ (r + s)) := by
    simpa only [l, iF, isF, jF, jrF, Multiset.insert_eq_cons,
      Multiset.map_cons,
      Multiset.map_singleton, Multiset.map_zero, Multiset.sum_cons,
      Multiset.sum_singleton, Multiset.sum_zero,
      Fin.val_mk, add_zero, add_assoc] using hmod
  have hTRmod : Nat.ModEq (2 ^ n - 1)
      (∑ x ∈ T, 2 ^ x) (∑ x ∈ R, 2 ^ x) := by
    rw [hTsum, hRsum]
    exact ht_mod.symm.trans hlmod
  have hTRsum :
      (∑ x ∈ T, 2 ^ x) = ∑ x ∈ R, 2 ^ x :=
    lemma12_modEq_eq_of_pos_of_le hTpos hRpos hTle hRle hTRmod
  have hTR : T = R :=
    lemma12_finset_two_pow_sum_injective n T R hTsub hRsub hTRsum
  have ht_card_four : t.card = 4 := by
    rw [← hTcard, hTR, hRcard]
  have hl_nodup : l.Nodup := by
    apply ht_nodup
    simpa [l] using ht_card_four
  have hl_nodup' :
      (¬iF = isF ∧ ¬iF = jF ∧ ¬iF = jrF) ∧
        (¬isF = jF ∧ ¬isF = jrF) ∧ ¬jF = jrF := by
    simpa [l] using hl_nodup
  let L : Finset ℕ := l.toFinset.image Fin.val
  have hLsum :
      (∑ x ∈ L, 2 ^ x) = (l.map fun x => 2 ^ x.val).sum := by
    rw [Finset.sum_image Fin.val_injective.injOn]
    change (l.dedup.map fun x => 2 ^ x.val).sum =
      (l.map fun x => 2 ^ x.val).sum
    rw [Multiset.dedup_eq_self.mpr hl_nodup]
  have hLsub : L ⊆ Finset.range n := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, _hy, rfl⟩
    exact Finset.mem_range.mpr y.isLt
  have hLne : L.Nonempty := by
    apply Finset.Nonempty.image
    exact Multiset.toFinset_nonempty.mpr (by simp [l])
  have hLpos : 0 < ∑ x ∈ L, 2 ^ x :=
    Finset.sum_pos (fun x _hx => Nat.two_pow_pos x) hLne
  have hLle : (∑ x ∈ L, 2 ^ x) ≤ 2 ^ n - 1 := by
    rw [← lemma12_sum_range_two_pow n]
    exact Finset.sum_le_sum_of_subset hLsub
  have hLRmod : Nat.ModEq (2 ^ n - 1)
      (∑ x ∈ L, 2 ^ x) (∑ x ∈ R, 2 ^ x) := by
    rw [hLsum, hRsum]
    exact hlmod
  have hLRsum :
      (∑ x ∈ L, 2 ^ x) = ∑ x ∈ R, 2 ^ x :=
    lemma12_modEq_eq_of_pos_of_le hLpos hRpos hLle hRle hLRmod
  have hLR : L = R :=
    lemma12_finset_two_pow_sum_injective n L R hLsub hRsub hLRsum
  have hmemL (x : Fin n) (hx : x ∈ l) : x.val ∈ L := by
    apply Finset.mem_image.mpr
    exact ⟨x, Multiset.mem_toFinset.mpr hx, rfl⟩
  have hiR : i ∈ R := by
    rw [← hLR]
    exact hmemL iF (by simp [l])
  have hisR : (i + s) % n ∈ R := by
    rw [← hLR]
    exact hmemL isF (by simp [l])
  have hjR : j ∈ R := by
    rw [← hLR]
    exact hmemL jF (by simp [l])
  have hjrR : (j + r) % n ∈ R := by
    rw [← hLR]
    exact hmemL jrF (by simp [l])
  have hA : i = 0 ∨ i = r ∨ i = s ∨ i = r + s := by
    simpa only [R, Finset.mem_insert, Finset.mem_singleton] using hiR
  have hB : (i + s) % n = 0 ∨ (i + s) % n = r ∨
      (i + s) % n = s ∨ (i + s) % n = r + s := by
    simpa only [R, Finset.mem_insert, Finset.mem_singleton] using hisR
  have hC : j = 0 ∨ j = r ∨ j = s ∨ j = r + s := by
    simpa only [R, Finset.mem_insert, Finset.mem_singleton] using hjR
  have hD : (j + r) % n = 0 ∨ (j + r) % n = r ∨
      (j + r) % n = s ∨ (j + r) % n = r + s := by
    simpa only [R, Finset.mem_insert, Finset.mem_singleton] using hjrR
  have hAB : i ≠ (i + s) % n := by
    intro h
    exact hl_nodup'.1.1 (Fin.ext h)
  have hAC : i ≠ j := by
    intro h
    exact hl_nodup'.1.2.1 (Fin.ext h)
  have hAD : i ≠ (j + r) % n := by
    intro h
    exact hl_nodup'.1.2.2 (Fin.ext h)
  have hBC : (i + s) % n ≠ j := by
    intro h
    exact hl_nodup'.2.1.1 (Fin.ext h)
  have hBD : (i + s) % n ≠ (j + r) % n := by
    intro h
    exact hl_nodup'.2.1.2 (Fin.ext h)
  have hCD : j ≠ (j + r) % n := by
    intro h
    exact hl_nodup'.2.2 (Fin.ext h)
  have hBform : ((i + s < n ∧ (i + s) % n = i + s) ∨
      (n ≤ i + s ∧ (i + s) % n = i + s - n)) := by
    by_cases hlt : i + s < n
    · exact Or.inl ⟨hlt, Nat.mod_eq_of_lt hlt⟩
    · right
      have hle : n ≤ i + s := by omega
      refine ⟨hle, ?_⟩
      rw [Nat.mod_eq_sub_mod hle]
      exact Nat.mod_eq_of_lt (by omega)
  have hDform : ((j + r < n ∧ (j + r) % n = j + r) ∨
      (n ≤ j + r ∧ (j + r) % n = j + r - n)) := by
    by_cases hlt : j + r < n
    · exact Or.inl ⟨hlt, Nat.mod_eq_of_lt hlt⟩
    · right
      have hle : n ≤ j + r := by omega
      refine ⟨hle, ?_⟩
      rw [Nat.mod_eq_sub_mod hle]
      exact Nat.mod_eq_of_lt (by omega)
  exact ⟨hA, hB, hC, hD, hAB, hAC, hAD, hBC, hBD, hCD,
    hBform, hDform⟩

set_option maxHeartbeats 800000 in
private theorem lemma12_distinct_pair_gap_classify_basic
    (n r s i j : ℕ)
    (hn : 0 < n)
    (hr_pos : 0 < r) (hr_le : r ≤ n / 2)
    (hs_pos : 0 < s) (hs_le : s ≤ n / 2)
    (hdiff : r ≠ s) (hi : i < n) (hj : j < n)
    (hmod : Nat.ModEq (2 ^ n - 1)
      (2 ^ i + 2 ^ ((i + s) % n) +
        2 ^ j + 2 ^ ((j + r) % n))
      (2 ^ 0 + 2 ^ r + 2 ^ s + 2 ^ (r + s))) :
    (s = 2 * r ∧ n = 5 * r) ∨
      (r = 2 * s ∧ n = 5 * s) := by
  obtain ⟨hA, hB, hC, hD, _hAB, _hAC, _hAD, _hBC, _hBD, _hCD,
      hBform, hDform⟩ :=
    lemma12_distinct_pair_support n r s i j hn hr_pos hr_le hs_pos hs_le
      hdiff hi hj hmod
  rcases hBform with hBform | hBform <;>
    rcases hDform with hDform | hDform <;>
      rcases hA with hA | hA | hA | hA <;>
        rcases hB with hB | hB | hB | hB <;>
          rcases hC with hC | hC | hC | hC <;>
            rcases hD with hD | hD | hD | hD <;> omega

set_option maxHeartbeats 800000 in
private theorem lemma12_distinct_pair_gap_classify
    (n r s i j : ℕ)
    (hn : 0 < n)
    (hr_pos : 0 < r) (hr_le : r ≤ n / 2)
    (hs_pos : 0 < s) (hs_le : s ≤ n / 2)
    (hdiff : r ≠ s) (hi : i < n) (hj : j < n)
    (hmod : Nat.ModEq (2 ^ n - 1)
      (2 ^ i + 2 ^ ((i + s) % n) +
        2 ^ j + 2 ^ ((j + r) % n))
      (2 ^ 0 + 2 ^ r + 2 ^ s + 2 ^ (r + s))) :
    (s = 2 * r ∧ n = 5 * r ∧ i = 3 * r ∧ j = r) ∨
      (r = 2 * s ∧ n = 5 * s ∧ i = s ∧ j = 3 * s) := by
  have hgap := lemma12_distinct_pair_gap_classify_basic
    n r s i j hn hr_pos hr_le hs_pos hs_le hdiff hi hj hmod
  obtain ⟨hA, hB, hC, hD, hAB, hAC, hAD, hBC, hBD, hCD,
      hBform, hDform⟩ :=
    lemma12_distinct_pair_support n r s i j hn hr_pos hr_le hs_pos hs_le
      hdiff hi hj hmod
  rcases hgap with hforward | hreverse
  · rcases hforward with ⟨hsr, hn5⟩
    have hiChoices : i = 0 ∨ i = r ∨ i = 3 * r := by
      rcases hBform with hBform | hBform <;>
        rcases hA with hA | hA | hA | hA <;>
          rcases hB with hB | hB | hB | hB <;> omega
    have hjChoices : j = 0 ∨ j = r ∨ j = 2 * r := by
      rcases hDform with hDform | hDform <;>
        rcases hC with hC | hC | hC | hC <;>
          rcases hD with hD | hD | hD | hD <;> omega
    have hij : i = 3 * r ∧ j = r := by
      rcases hBform with hBform | hBform <;>
        rcases hDform with hDform | hDform <;>
          rcases hiChoices with hiChoices | hiChoices | hiChoices <;>
            rcases hjChoices with hjChoices | hjChoices | hjChoices <;> omega
    exact Or.inl ⟨hsr, hn5, hij.1, hij.2⟩
  · rcases hreverse with ⟨hrs, hn5⟩
    have hiChoices : i = 0 ∨ i = s ∨ i = 2 * s := by
      rcases hBform with hBform | hBform <;>
        rcases hA with hA | hA | hA | hA <;>
          rcases hB with hB | hB | hB | hB <;> omega
    have hjChoices : j = 0 ∨ j = s ∨ j = 3 * s := by
      rcases hDform with hDform | hDform <;>
        rcases hC with hC | hC | hC | hC <;>
          rcases hD with hD | hD | hD | hD <;> omega
    have hij : i = s ∧ j = 3 * s := by
      rcases hBform with hBform | hBform <;>
        rcases hDform with hDform | hDform <;>
          rcases hiChoices with hiChoices | hiChoices | hiChoices <;>
            rcases hjChoices with hjChoices | hjChoices | hjChoices <;> omega
    exact Or.inr ⟨hrs, hn5, hij.1, hij.2⟩
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma12_distinct_pair_gap_of_cross_seed
    (n r s : ℕ) (hn : 2 ≤ n)
    (hr_pos : 0 < r) (hr_le : r ≤ n / 2)
    (hs_pos : 0 < s) (hs_le : s ≤ n / 2) (hdiff : r ≠ s)
    (lambda mu nu : BinaryGaloisField n) (hlambda : lambda ≠ 0)
    (hlambda_order : orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1)
    (iu ju su iv jv sv i j : Fin n)
    (hrGap :
      (if iu.val ≤ ju.val then ju.val - iu.val else n - (iu.val - ju.val)) = r)
    (hsGap :
      (if iv.val ≤ jv.val then jv.val - iv.val else n - (iv.val - jv.val)) = s)
    (hUseed : lambda ^ (2 ^ (iu : ℕ)) * lambda ^ (2 ^ (ju : ℕ)) =
      nu ^ (2 ^ (su : ℕ)))
    (hVseed : mu ^ (2 ^ (iv : ℕ)) * mu ^ (2 ^ (jv : ℕ)) =
      nu ^ (2 ^ (sv : ℕ)))
    (hcrossSeed : lambda ^ (2 ^ (i : ℕ)) * mu ^ (2 ^ (j : ℕ)) = nu) :
    let iNorm := ((i : ℕ) + (su : ℕ) + (n - (iu : ℕ))) % n
    let jNorm := ((j : ℕ) + (sv : ℕ) + (n - (iv : ℕ))) % n
    (s = 2 * r ∧ n = 5 * r ∧ iNorm = 3 * r ∧ jNorm = r) ∨
      (r = 2 * s ∧ n = 5 * s ∧ iNorm = s ∧ jNorm = 3 * s) := by
  let K : Type := BinaryGaloisField n
  let sigma : K ≃ₐ[ZMod 2] K :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  let forwardGap (a b : Fin n) : ℕ :=
    if a.val ≤ b.val then b.val - a.val else n - (a.val - b.val)
  have hn_pos : 0 < n := by omega
  have hsigma_order : orderOf sigma = n := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      GaloisField.finrank 2 (by omega : n ≠ 0)]
  have hsigma_pow : sigma ^ n = 1 := by
    have h := pow_orderOf_eq_one sigma
    simpa only [hsigma_order] using h
  have hsigma_apply (x : K) (t : ℕ) :
      (sigma ^ t) x = x ^ (2 ^ t) := by
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp [ZMod.card]
  have hsigmaForward (a b : Fin n) :
      sigma ^ forwardGap a b * sigma ^ (a : ℕ) = sigma ^ (b : ℕ) := by
    have hthetaOfGap :
        sigma ^ (b : ℕ) * (sigma ^ (a : ℕ))⁻¹ =
          sigma ^ forwardGap a b := by
      by_cases hab : (a : ℕ) ≤ (b : ℕ)
      · rw [← pow_sub sigma hab]
        congr 1
        simp only [forwardGap, if_pos hab]
      · have hba : (b : ℕ) ≤ (a : ℕ) := by omega
        have hd_le : (a : ℕ) - (b : ℕ) ≤ n := by omega
        rw [show forwardGap a b = n - ((a : ℕ) - (b : ℕ)) by
          simp only [forwardGap, if_neg hab]]
        calc
          sigma ^ (b : ℕ) * (sigma ^ (a : ℕ))⁻¹ =
              (sigma ^ ((a : ℕ) - (b : ℕ)))⁻¹ := by
            rw [pow_sub sigma hba, mul_inv_rev, inv_inv]
          _ = sigma ^ (n - ((a : ℕ) - (b : ℕ))) := by
            symm
            rw [pow_sub sigma hd_le, hsigma_pow, one_mul]
    rw [← hthetaOfGap]
    group
  let tauU : K ≃ₐ[ZMod 2] K :=
    (sigma ^ (su : ℕ))⁻¹ * sigma ^ (iu : ℕ)
  let tauV : K ≃ₐ[ZMod 2] K :=
    (sigma ^ (sv : ℕ))⁻¹ * sigma ^ (iv : ℕ)
  let lambdaNorm : K := tauU lambda
  let muNorm : K := tauV mu
  have hlambdaNorm : lambdaNorm ≠ 0 := tauU.map_ne_zero_iff.mpr hlambda
  have hsuLambdaNorm :
      (sigma ^ (su : ℕ)) lambdaNorm = (sigma ^ (iu : ℕ)) lambda := by
    change (sigma ^ (su : ℕ) * tauU) lambda = (sigma ^ (iu : ℕ)) lambda
    congr 1
    dsimp only [tauU]
    group
  have hsuLambdaShift :
      (sigma ^ (su : ℕ)) ((sigma ^ r) lambdaNorm) =
        (sigma ^ (ju : ℕ)) lambda := by
    change (sigma ^ (su : ℕ) * sigma ^ r * tauU) lambda =
      (sigma ^ (ju : ℕ)) lambda
    have hgap : sigma ^ r * sigma ^ (iu : ℕ) = sigma ^ (ju : ℕ) := by
      rw [← hrGap]
      exact hsigmaForward iu ju
    have hcomp :
        sigma ^ (su : ℕ) * sigma ^ r * tauU =
          sigma ^ r * sigma ^ (iu : ℕ) := by
      dsimp only [tauU]
      group
    rw [hcomp, hgap]
  have hsvMuNorm :
      (sigma ^ (sv : ℕ)) muNorm = (sigma ^ (iv : ℕ)) mu := by
    change (sigma ^ (sv : ℕ) * tauV) mu = (sigma ^ (iv : ℕ)) mu
    congr 1
    dsimp only [tauV]
    group
  have hsvMuShift :
      (sigma ^ (sv : ℕ)) ((sigma ^ s) muNorm) =
        (sigma ^ (jv : ℕ)) mu := by
    change (sigma ^ (sv : ℕ) * sigma ^ s * tauV) mu =
      (sigma ^ (jv : ℕ)) mu
    have hgap : sigma ^ s * sigma ^ (iv : ℕ) = sigma ^ (jv : ℕ) := by
      rw [← hsGap]
      exact hsigmaForward iv jv
    have hcomp :
        sigma ^ (sv : ℕ) * sigma ^ s * tauV =
          sigma ^ s * sigma ^ (iv : ℕ) := by
      dsimp only [tauV]
      group
    rw [hcomp, hgap]
  have hnuU : nu = lambdaNorm * (sigma ^ r) lambdaNorm := by
    apply (sigma ^ (su : ℕ)).injective
    calc
      (sigma ^ (su : ℕ)) nu = nu ^ (2 ^ (su : ℕ)) :=
        hsigma_apply nu (su : ℕ)
      _ = lambda ^ (2 ^ (iu : ℕ)) * lambda ^ (2 ^ (ju : ℕ)) :=
        hUseed.symm
      _ = (sigma ^ (iu : ℕ)) lambda * (sigma ^ (ju : ℕ)) lambda := by
        rw [hsigma_apply, hsigma_apply]
      _ = (sigma ^ (su : ℕ)) lambdaNorm *
          (sigma ^ (su : ℕ)) ((sigma ^ r) lambdaNorm) := by
        rw [hsuLambdaNorm, hsuLambdaShift]
      _ = (sigma ^ (su : ℕ)) (lambdaNorm * (sigma ^ r) lambdaNorm) := by
        rw [map_mul]
  have hnuV : nu = muNorm * (sigma ^ s) muNorm := by
    apply (sigma ^ (sv : ℕ)).injective
    calc
      (sigma ^ (sv : ℕ)) nu = nu ^ (2 ^ (sv : ℕ)) :=
        hsigma_apply nu (sv : ℕ)
      _ = mu ^ (2 ^ (iv : ℕ)) * mu ^ (2 ^ (jv : ℕ)) := hVseed.symm
      _ = (sigma ^ (iv : ℕ)) mu * (sigma ^ (jv : ℕ)) mu := by
        rw [hsigma_apply, hsigma_apply]
      _ = (sigma ^ (sv : ℕ)) muNorm *
          (sigma ^ (sv : ℕ)) ((sigma ^ s) muNorm) := by
        rw [hsvMuNorm, hsvMuShift]
      _ = (sigma ^ (sv : ℕ)) (muNorm * (sigma ^ s) muNorm) := by
        rw [map_mul]
  let iRaw : ℕ := (i : ℕ) + (su : ℕ) + (n - (iu : ℕ))
  let jRaw : ℕ := (j : ℕ) + (sv : ℕ) + (n - (iv : ℕ))
  let iNorm : ℕ := iRaw % n
  let jNorm : ℕ := jRaw % n
  have hiNorm_lt : iNorm < n := Nat.mod_lt _ hn_pos
  have hjNorm_lt : jNorm < n := Nat.mod_lt _ hn_pos
  have hsigma_iNorm : sigma ^ iNorm = sigma ^ iRaw := by
    apply pow_eq_pow_iff_modEq.mpr
    rw [hsigma_order]
    exact Nat.mod_modEq iRaw n
  have hsigma_jNorm : sigma ^ jNorm = sigma ^ jRaw := by
    apply pow_eq_pow_iff_modEq.mpr
    rw [hsigma_order]
    exact Nat.mod_modEq jRaw n
  have hiComp : sigma ^ iNorm * tauU = sigma ^ (i : ℕ) := by
    rw [hsigma_iNorm]
    have hiRaw :
        iRaw = ((i : ℕ) + (su : ℕ) + n) - (iu : ℕ) := by
      dsimp only [iRaw]
      omega
    rw [hiRaw, pow_sub sigma (by omega), pow_add, pow_add, hsigma_pow]
    dsimp only [tauU]
    group
  have hjComp : sigma ^ jNorm * tauV = sigma ^ (j : ℕ) := by
    rw [hsigma_jNorm]
    have hjRaw :
        jRaw = ((j : ℕ) + (sv : ℕ) + n) - (iv : ℕ) := by
      dsimp only [jRaw]
      omega
    rw [hjRaw, pow_sub sigma (by omega), pow_add, pow_add, hsigma_pow]
    dsimp only [tauV]
    group
  have hlambdaCross :
      lambdaNorm ^ (2 ^ iNorm) = lambda ^ (2 ^ (i : ℕ)) := by
    calc
      lambdaNorm ^ (2 ^ iNorm) = (sigma ^ iNorm) lambdaNorm :=
        (hsigma_apply lambdaNorm iNorm).symm
      _ = (sigma ^ (i : ℕ)) lambda := by
        change (sigma ^ iNorm * tauU) lambda = (sigma ^ (i : ℕ)) lambda
        rw [hiComp]
      _ = lambda ^ (2 ^ (i : ℕ)) := hsigma_apply lambda (i : ℕ)
  have hmuCross : muNorm ^ (2 ^ jNorm) = mu ^ (2 ^ (j : ℕ)) := by
    calc
      muNorm ^ (2 ^ jNorm) = (sigma ^ jNorm) muNorm :=
        (hsigma_apply muNorm jNorm).symm
      _ = (sigma ^ (j : ℕ)) mu := by
        change (sigma ^ jNorm * tauV) mu = (sigma ^ (j : ℕ)) mu
        rw [hjComp]
      _ = mu ^ (2 ^ (j : ℕ)) := hsigma_apply mu (j : ℕ)
  have hcrossNorm :
      lambdaNorm ^ (2 ^ iNorm) * muNorm ^ (2 ^ jNorm) = nu := by
    rw [hlambdaCross, hmuCross]
    exact hcrossSeed
  have hnuUPow : lambdaNorm ^ (1 + 2 ^ r) = nu := by
    calc
      lambdaNorm ^ (1 + 2 ^ r) =
          lambdaNorm * lambdaNorm ^ (2 ^ r) := by rw [pow_add]; simp
      _ = lambdaNorm * (sigma ^ r) lambdaNorm := by rw [hsigma_apply]
      _ = nu := hnuU.symm
  have hnuVPow : muNorm ^ (1 + 2 ^ s) = nu := by
    calc
      muNorm ^ (1 + 2 ^ s) = muNorm * muNorm ^ (2 ^ s) := by
        rw [pow_add]
        simp
      _ = muNorm * (sigma ^ s) muNorm := by rw [hsigma_apply]
      _ = nu := hnuV.symm
  have hmuPower :
      (muNorm ^ (2 ^ jNorm)) ^ (1 + 2 ^ s) =
        lambdaNorm ^ ((1 + 2 ^ r) * 2 ^ jNorm) := by
    calc
      (muNorm ^ (2 ^ jNorm)) ^ (1 + 2 ^ s) =
          (muNorm ^ (1 + 2 ^ s)) ^ (2 ^ jNorm) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      _ = nu ^ (2 ^ jNorm) := by rw [hnuVPow]
      _ = (lambdaNorm ^ (1 + 2 ^ r)) ^ (2 ^ jNorm) := by rw [hnuUPow]
      _ = lambdaNorm ^ ((1 + 2 ^ r) * 2 ^ jNorm) := by rw [← pow_mul]
  have hleft :
      (lambdaNorm ^ (2 ^ iNorm) * muNorm ^ (2 ^ jNorm)) ^ (1 + 2 ^ s) =
        lambdaNorm ^
          (2 ^ iNorm + 2 ^ (iNorm + s) +
            2 ^ jNorm + 2 ^ (jNorm + r)) := by
    calc
      (lambdaNorm ^ (2 ^ iNorm) * muNorm ^ (2 ^ jNorm)) ^ (1 + 2 ^ s) =
          (lambdaNorm ^ (2 ^ iNorm)) ^ (1 + 2 ^ s) *
            (muNorm ^ (2 ^ jNorm)) ^ (1 + 2 ^ s) := by rw [mul_pow]
      _ = lambdaNorm ^ (2 ^ iNorm * (1 + 2 ^ s)) *
          lambdaNorm ^ ((1 + 2 ^ r) * 2 ^ jNorm) := by
        rw [← pow_mul, hmuPower]
      _ = lambdaNorm ^
          (2 ^ iNorm * (1 + 2 ^ s) + (1 + 2 ^ r) * 2 ^ jNorm) := by
        rw [pow_add]
      _ = lambdaNorm ^
          (2 ^ iNorm + 2 ^ (iNorm + s) +
            2 ^ jNorm + 2 ^ (jNorm + r)) := by
        congr 1
        rw [pow_add, pow_add]
        ring
  have hright :
      nu ^ (1 + 2 ^ s) =
        lambdaNorm ^ (2 ^ 0 + 2 ^ r + 2 ^ s + 2 ^ (r + s)) := by
    calc
      nu ^ (1 + 2 ^ s) =
          (lambdaNorm ^ (1 + 2 ^ r)) ^ (1 + 2 ^ s) := by rw [hnuUPow]
      _ = lambdaNorm ^ ((1 + 2 ^ r) * (1 + 2 ^ s)) := by rw [← pow_mul]
      _ = lambdaNorm ^ (2 ^ 0 + 2 ^ r + 2 ^ s + 2 ^ (r + s)) := by
        congr 1
        rw [pow_add]
        simp
        ring
  have hpower :
      lambdaNorm ^
          (2 ^ iNorm + 2 ^ (iNorm + s) +
            2 ^ jNorm + 2 ^ (jNorm + r)) =
        lambdaNorm ^ (2 ^ 0 + 2 ^ r + 2 ^ s + 2 ^ (r + s)) :=
    hleft.symm.trans
      ((congrArg (fun z : K => z ^ (1 + 2 ^ s)) hcrossNorm).trans hright)
  let tauUnits : Kˣ →* Kˣ := Units.map tauU.toRingEquiv.toMonoidHom
  have htauUnits_injective : Function.Injective tauUnits :=
    Units.map_injective tauU.injective
  have htauUnits :
      tauUnits (Units.mk0 lambda hlambda) = Units.mk0 lambdaNorm hlambdaNorm := by
    apply Units.ext
    rfl
  have hlambdaNormOrder :
      orderOf (Units.mk0 lambdaNorm hlambdaNorm) = 2 ^ n - 1 := by
    calc
      orderOf (Units.mk0 lambdaNorm hlambdaNorm) =
          orderOf (tauUnits (Units.mk0 lambda hlambda)) := by rw [htauUnits]
      _ = orderOf (Units.mk0 lambda hlambda) :=
        orderOf_injective tauUnits htauUnits_injective _
      _ = 2 ^ n - 1 := hlambda_order
  have hunit :
      (Units.mk0 lambdaNorm hlambdaNorm) ^
          (2 ^ iNorm + 2 ^ (iNorm + s) +
            2 ^ jNorm + 2 ^ (jNorm + r)) =
        (Units.mk0 lambdaNorm hlambdaNorm) ^
          (2 ^ 0 + 2 ^ r + 2 ^ s + 2 ^ (r + s)) := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using hpower
  have hmodRaw : Nat.ModEq (2 ^ n - 1)
      (2 ^ iNorm + 2 ^ (iNorm + s) +
        2 ^ jNorm + 2 ^ (jNorm + r))
      (2 ^ 0 + 2 ^ r + 2 ^ s + 2 ^ (r + s)) := by
    have hmod := pow_eq_pow_iff_modEq.mp hunit
    simpa only [hlambdaNormOrder] using hmod
  have hreduce : Nat.ModEq (2 ^ n - 1)
      (2 ^ iNorm + 2 ^ (iNorm + s) +
        2 ^ jNorm + 2 ^ (jNorm + r))
      (2 ^ iNorm + 2 ^ ((iNorm + s) % n) +
        2 ^ jNorm + 2 ^ ((jNorm + r) % n)) := by
    have h := (((lemma6_two_pow_modEq_cyclic n iNorm).add
      (lemma6_two_pow_modEq_cyclic n (iNorm + s))).add
        (lemma6_two_pow_modEq_cyclic n jNorm)).add
          (lemma6_two_pow_modEq_cyclic n (jNorm + r))
    simpa only [Nat.mod_eq_of_lt hiNorm_lt, Nat.mod_eq_of_lt hjNorm_lt,
      add_assoc] using h
  exact lemma12_distinct_pair_gap_classify n r s iNorm jNorm hn_pos
    hr_pos hr_le hs_pos hs_le hdiff hiNorm_lt hjNorm_lt
    (hreduce.symm.trans hmodRaw)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma12_same_pair_typeB_core
    {P : Type u} [Group P] [Finite P] [Fact (Nat.Prime 2)]
    [Fact (IsPGroup 2 P)] [Group.IsNilpotent P]
    (n : ℕ) (hn : 2 ≤ n)
    (U V : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)))
    (hUV : IsCompl U V)
    (S : Additive (LowerCentralFactor P 1) ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1))
    (xiU : U ≃ₗ[ZMod 2] U) (xiV : V ≃ₗ[ZMod 2] V)
    (T : Additive (LowerCentralFactor P 0) ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor P 0))
    (hT_u : ∀ u : U,
      T (u : Additive (LowerCentralFactor P 0)) =
        (xiU u : Additive (LowerCentralFactor P 0)))
    (hT_v : ∀ v : V,
      T (v : Additive (LowerCentralFactor P 0)) =
        (xiV v : Additive (LowerCentralFactor P 0)))
    (nu : BinaryGaloisField n)
    (centerCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1))
    (hnu : nu ≠ 0)
    (hcenterCoordinates : ∀ alpha : BinaryGaloisField n,
      S (centerCoordinates alpha) = centerCoordinates (nu * alpha))
    (bracket : Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor P 1))
    (squareMap : Additive (LowerCentralFactor P 0) →
      Additive (LowerCentralFactor P 1))
    (hsquare_add : ∀ v w : Additive (LowerCentralFactor P 0),
      squareMap (v + w) = squareMap v + squareMap w + bracket v w)
    (hsquare_anisotropic : ∀ v : Additive (LowerCentralFactor P 0),
      squareMap v = 0 → v = 0)
    (hsquare_xiV_pow : ∀ (j : ℕ) (v : V),
      squareMap ((xiV ^ j) v : Additive (LowerCentralFactor P 0)) =
        (S ^ j) (squareMap (v : Additive (LowerCentralFactor P 0))))
    (hcross_nonzero : ∃ u : U, ∃ v : V,
      bracket (u : Additive (LowerCentralFactor P 0))
        (v : Additive (LowerCentralFactor P 0)) ≠ 0)
    (hbracket_cross_equivariant : ∀ (u : U) (v : V),
      bracket (xiU u : Additive (LowerCentralFactor P 0))
          (xiV v : Additive (LowerCentralFactor P 0)) =
        S (bracket (u : Additive (LowerCentralFactor P 0))
          (v : Additive (LowerCentralFactor P 0))))
    (lambda : BinaryGaloisField n) (hlambda : lambda ≠ 0)
    (hlambda_order : orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1)
    (hnu_order : orderOf (Units.mk0 nu hnu) = 2 ^ n - 1)
    (uCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2] U)
    (huCoordinates : ∀ alpha : BinaryGaloisField n,
      xiU (uCoordinates alpha) = uCoordinates (lambda * alpha))
    (vCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2] V)
    (iu ju su iv jv sv : Fin n)
    (cu cv : BinaryGaloisField n) (hcu : cu ≠ 0) (hcv : cv ≠ 0)
    (hUseed : lambda ^ (2 ^ (iu : ℕ)) * lambda ^ (2 ^ (ju : ℕ)) =
      nu ^ (2 ^ (su : ℕ)))
    (hUformula : ∀ a : BinaryGaloisField n,
      (FiniteField.frobeniusAlgEquivOfAlgebraic
          (ZMod 2) (BinaryGaloisField n) ^ (su : ℕ))
          (centerCoordinates.symm
            (squareMap (uCoordinates a : Additive (LowerCentralFactor P 0)))) =
        cu * a ^ (2 ^ (iu : ℕ) + 2 ^ (ju : ℕ)))
    (hVformula : ∀ b : BinaryGaloisField n,
      (FiniteField.frobeniusAlgEquivOfAlgebraic
          (ZMod 2) (BinaryGaloisField n) ^ (sv : ℕ))
          (centerCoordinates.symm
            (squareMap (vCoordinates b : Additive (LowerCentralFactor P 0)))) =
        cv * b ^ (2 ^ (iv : ℕ) + 2 ^ (jv : ℕ)))
    (hUgap_pos : 0 <
      (if iu.val ≤ ju.val then ju.val - iu.val else n - (iu.val - ju.val)))
    (hUgap_le :
      (if iu.val ≤ ju.val then ju.val - iu.val else n - (iu.val - ju.val)) ≤ n / 2)
    (hsameGap :
      (if iu.val ≤ ju.val then ju.val - iu.val else n - (iu.val - ju.val)) =
        (if iv.val ≤ jv.val then jv.val - iv.val else n - (iv.val - jv.val))) :
    Lemma12TypeBActorQuadraticData T S n squareMap := by
  let K : Type := BinaryGaloisField n
  let typeBQuadraticData : Prop :=
    Lemma12TypeBActorQuadraticData T S n squareMap
  let crossBracket : U →ₗ[ZMod 2] V →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1) :=
    { toFun := fun u =>
        { toFun := fun v => bracket
            (u : Additive (LowerCentralFactor P 0))
            (v : Additive (LowerCentralFactor P 0))
          map_add' := by
            intro v w
            exact (bracket
              (u : Additive (LowerCentralFactor P 0))).map_add v w
          map_smul' := by
            intro c v
            exact (bracket
              (u : Additive (LowerCentralFactor P 0))).map_smul c v }
      map_add' := by
        intro u w
        apply LinearMap.ext
        intro v
        change bracket
            ((u : Additive (LowerCentralFactor P 0)) + w) v = _
        rw [map_add, LinearMap.add_apply]
        rfl
      map_smul' := by
        intro c u
        apply LinearMap.ext
        intro v
        change bracket
            (c • (u : Additive (LowerCentralFactor P 0))) v = _
        rw [map_smul, LinearMap.smul_apply]
        rfl }
  have hcross_equivariant (u : U) (v : V) :
      crossBracket (xiU u) (xiV v) = S (crossBracket u v) := by
    exact hbracket_cross_equivariant u v
  let forwardGap (i j : Fin n) : ℕ :=
    if i.val ≤ j.val then j.val - i.val else n - (i.val - j.val)
  let r := forwardGap iu ju
  let s := forwardGap iv jv
  have hr_pos : 0 < r := by simpa [r, forwardGap] using hUgap_pos
  have hr_le : r ≤ n / 2 := by simpa [r, forwardGap] using hUgap_le
  have hd : 0 < n := by omega
  have hsame : r = s := by simpa [r, s, forwardGap] using hsameGap
  let sigma : K ≃ₐ[ZMod 2] K :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  let rhoU : K ≃ₐ[ZMod 2] K := (sigma ^ (iu : ℕ)).symm
  let thetaAlg : K ≃ₐ[ZMod 2] K := sigma ^ (ju : ℕ) * rhoU
  let theta : K ≃+* K := thetaAlg.toRingEquiv
  let cUnit : Kˣ := Units.mk0 cu hcu
  let outputTransform : K ≃ₗ[ZMod 2] K :=
    (sigma ^ (su : ℕ)).toLinearEquiv.trans
      ((cUnit⁻¹).mulLeftLinearEquiv (ZMod 2) K)
  let finalCenterCoordinates :
      K ≃ₗ[ZMod 2] Additive (LowerCentralFactor P 1) :=
    outputTransform.symm.trans centerCoordinates
  let uNorm : K ≃ₗ[ZMod 2] ↥U :=
    rhoU.toLinearEquiv.trans uCoordinates
  have huNormSquare (a : K) :
      finalCenterCoordinates.symm
          (squareMap (uNorm a :
            Additive (LowerCentralFactor P 0))) =
        a * theta a := by
    have hnormalize := lemma12_pair_monomial_normalize
      n iu ju su cu hcu
      (fun x : K => centerCoordinates.symm
        (squareMap (uCoordinates x :
          Additive (LowerCentralFactor P 0)))) hUformula a
    change (cUnit.mulLeftLinearEquiv (ZMod 2) K).symm _ = _
    rw [Units.symm_mulLeftLinearEquiv_apply]
    simpa [K, sigma, rhoU, thetaAlg, theta, cUnit, uNorm] using
      hnormalize
  have hthetaPeriod :
      ∃ k : ℕ, Odd k ∧ 0 < k ∧ ∀ x : K, theta^[k] x = x := by
    let gap := lemma6_finPairGap iu ju
    let e := 2 ^ (iu : ℕ) + 2 ^ (ju : ℕ)
    have he_pos : 0 < e := by simp [e]
    have hsigma_apply (x : K) (t : ℕ) :
        (sigma ^ t) x = x ^ (2 ^ t) := by
      rw [AlgEquiv.coe_pow,
        FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
      simp [ZMod.card]
    have hsigma_order : orderOf sigma = n := by
      rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
        GaloisField.finrank 2 (by omega : n ≠ 0)]
    have hlambda_field_order : orderOf lambda = 2 ^ n - 1 := by
      calc
        orderOf lambda = orderOf (Units.mk0 lambda hlambda) := by
          simpa using (orderOf_units
            (G := K) (y := Units.mk0 lambda hlambda))
        _ = 2 ^ n - 1 := hlambda_order
    have hnu_twist : (sigma ^ (su : ℕ)) nu = lambda ^ e := by
      rw [hsigma_apply]
      simpa [e, pow_add] using hUseed.symm
    have hlambda_e_order : orderOf (lambda ^ e) = 2 ^ n - 1 := by
      calc
        orderOf (lambda ^ e) = orderOf ((sigma ^ (su : ℕ)) nu) := by
          rw [hnu_twist]
        _ = orderOf nu := orderOf_injective
          (sigma ^ (su : ℕ)).toAlgHom.toMonoidHom
          (sigma ^ (su : ℕ)).injective nu
        _ = orderOf (Units.mk0 nu hnu) := by
          simpa using (orderOf_units
            (G := K) (y := Units.mk0 nu hnu))
        _ = 2 ^ n - 1 := hnu_order
    have hcop_e : Nat.Coprime (2 ^ n - 1) e := by
      have hformula := orderOf_pow' lambda he_pos.ne'
      rw [hlambda_field_order] at hformula
      have hdiv : (2 ^ n - 1) / (2 ^ n - 1).gcd e = 2 ^ n - 1 :=
        hformula.symm.trans hlambda_e_order
      have hcancel := Nat.div_mul_cancel
        (Nat.gcd_dvd_left (2 ^ n - 1) e)
      rw [hdiv] at hcancel
      have hq_pos : 0 < 2 ^ n - 1 := by
        have hpow : 1 < 2 ^ n :=
          one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega)
        omega
      apply Nat.coprime_iff_gcd_eq_one.mpr
      apply (mul_left_cancel_iff_of_pos hq_pos).mp
      simpa using hcancel
    have hgap_dvd : 2 ^ gap + 1 ∣ e := by
      dsimp only [gap, e, lemma6_finPairGap]
      rcases le_total (iu : ℕ) (ju : ℕ) with hij | hji
      · refine ⟨2 ^ (iu : ℕ), ?_⟩
        calc
          2 ^ (iu : ℕ) + 2 ^ (ju : ℕ) =
              2 ^ (iu : ℕ) + 2 ^ ((iu : ℕ) + ((ju : ℕ) - (iu : ℕ))) := by
                rw [Nat.add_sub_of_le hij]
          _ = (2 ^ (((iu : ℕ) - (ju : ℕ)) +
                ((ju : ℕ) - (iu : ℕ))) + 1) * 2 ^ (iu : ℕ) := by
                rw [Nat.sub_eq_zero_of_le hij, zero_add, pow_add]
                ring
      · refine ⟨2 ^ (ju : ℕ), ?_⟩
        calc
          2 ^ (iu : ℕ) + 2 ^ (ju : ℕ) =
              2 ^ ((ju : ℕ) + ((iu : ℕ) - (ju : ℕ))) + 2 ^ (ju : ℕ) := by
                rw [Nat.add_sub_of_le hji]
          _ = (2 ^ (((iu : ℕ) - (ju : ℕ)) +
                ((ju : ℕ) - (iu : ℕ))) + 1) * 2 ^ (ju : ℕ) := by
                rw [Nat.sub_eq_zero_of_le hji, add_zero, pow_add]
                ring
    have hcop_gap : Nat.Coprime (2 ^ n - 1) (2 ^ gap + 1) :=
      hcop_e.of_dvd_right hgap_dvd
    let period := n / n.gcd gap
    have hperiod_odd : Odd period := by
      let d := n.gcd gap
      have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left gap (by omega)
      have hquot_coprime : (n / d).Coprime (gap / d) := by
        simpa [d] using Nat.coprime_div_gcd_div_gcd hd_pos
      apply Nat.not_even_iff_odd.mp
      intro hn_even
      have htwo_dvd : 2 ∣ n / d := by
        rcases (show Even (n / d) by
          simpa [period, d] using hn_even) with ⟨k, hk⟩
        exact ⟨k, by omega⟩
      have hgap_odd : Odd (gap / d) := by
        apply Nat.Coprime.odd_of_left
        exact Nat.Coprime.of_dvd htwo_dvd (dvd_refl _) hquot_coprime
      have hd_dvd_n : d ∣ n := by
        simpa [d] using Nat.gcd_dvd_left n gap
      have hd_dvd_gap : d ∣ gap := by
        simpa [d] using Nat.gcd_dvd_right n gap
      have hn_eq : d * (n / d) = n := Nat.mul_div_cancel' hd_dvd_n
      have hgap_eq : d * (gap / d) = gap :=
        Nat.mul_div_cancel' hd_dvd_gap
      let c := 2 ^ d + 1
      have hc_base : c ∣ (2 ^ d) ^ 2 - 1 := by
        refine ⟨2 ^ d - 1, ?_⟩
        simpa [c, pow_two] using mul_self_tsub_one (2 ^ d)
      have hc_dvd_n : c ∣ 2 ^ n - 1 := by
        have h := hc_base.trans
          (Nat.pow_sub_one_dvd_pow_sub_one (2 ^ d) htwo_dvd)
        simpa [c, ← pow_mul, hn_eq] using h
      have hc_dvd_gap : c ∣ 2 ^ gap + 1 := by
        have h := hgap_odd.nat_add_dvd_pow_add_pow (2 ^ d) 1
        simpa [c, ← pow_mul, hgap_eq] using h
      have hc_one := Nat.eq_one_of_dvd_coprimes
        hcop_gap hc_dvd_n hc_dvd_gap
      have hc_gt : 1 < c := by simp [c]
      exact (ne_of_gt hc_gt) hc_one
    have hsigma_gap_order : orderOf (sigma ^ gap) = period := by
      dsimp [period]
      rw [orderOf_pow, hsigma_order]
    have hthetaAlg_gap :
        thetaAlg = sigma ^ gap ∨ thetaAlg = (sigma ^ gap)⁻¹ := by
      rcases le_total (iu : ℕ) (ju : ℕ) with hij | hji
      · left
        change sigma ^ (ju : ℕ) * (sigma ^ (iu : ℕ))⁻¹ = sigma ^ gap
        rw [← pow_sub sigma hij]
        congr 1
        simp [gap, lemma6_finPairGap, Nat.sub_eq_zero_of_le hij]
      · right
        change sigma ^ (ju : ℕ) * (sigma ^ (iu : ℕ))⁻¹ =
          (sigma ^ gap)⁻¹
        rw [show gap = (iu : ℕ) - (ju : ℕ) by
          simp [gap, lemma6_finPairGap, Nat.sub_eq_zero_of_le hji]]
        rw [pow_sub sigma hji, mul_inv_rev, inv_inv]
    have hthetaAlg_order : orderOf thetaAlg = period := by
      rcases hthetaAlg_gap with hthetaAlg | hthetaAlg
      · rw [hthetaAlg, hsigma_gap_order]
      · rw [hthetaAlg, orderOf_inv, hsigma_gap_order]
    have hthetaAlg_pow : thetaAlg ^ period = 1 := by
      rw [← hthetaAlg_order]
      exact pow_orderOf_eq_one thetaAlg
    refine ⟨period, hperiod_odd, hperiod_odd.pos, ?_⟩
    intro x
    have h := DFunLike.congr_fun hthetaAlg_pow x
    simpa [theta, AlgEquiv.coe_pow] using h
  have hsamePairCompletion : typeBQuadraticData := by
    have hthetaNorm_bijective :
        Function.Bijective (fun x : K => x * theta x) := by
      have hinjective :
          Function.Injective (fun x : K => x * theta x) := by
        intro x y hxy
        change x * theta x = y * theta y at hxy
        by_cases hx : x = 0
        · subst x
          have hyProd : y * theta y = 0 := by
            simpa using hxy.symm
          rcases mul_eq_zero.mp hyProd with hy | hy
          · exact hy.symm
          · exact (theta.map_eq_zero_iff.mp hy).symm
        have hy : y ≠ 0 := by
          intro hy
          subst y
          have hxProd : x * theta x = 0 := by
            simpa using hxy
          exact (mul_ne_zero hx (fun hzero => hx (theta.map_eq_zero_iff.mp hzero))) hxProd
        let z : K := x * y⁻¹
        have hz : z ≠ 0 := mul_ne_zero hx (inv_ne_zero hy)
        have hyProd : y * theta y ≠ 0 :=
          mul_ne_zero hy (fun hzero => hy (theta.map_eq_zero_iff.mp hzero))
        have hnorm : z * theta z = 1 := by
          dsimp only [z]
          rw [map_mul, map_inv₀]
          calc
            x * y⁻¹ * (theta x * (theta y)⁻¹) =
                (x * theta x) * (y * theta y)⁻¹ := by ring
            _ = 1 := by
              rw [hxy]
              exact mul_inv_cancel₀ hyProd
        have htheta_z : theta z = z⁻¹ := by
          apply mul_left_cancel₀ hz
          rw [hnorm, mul_inv_cancel₀ hz]
        have htheta_two : theta (theta z) = z := by
          rw [htheta_z, map_inv₀, htheta_z, inv_inv]
        obtain ⟨k, hkOdd, _hkPos, hkPeriod⟩ := hthetaPeriod
        rcases hkOdd with ⟨m, rfl⟩
        have htheta_two_iter : (theta^[2]) z = z := by
          simpa [Function.iterate_succ_apply] using htheta_two
        have heven : (theta^[2 * m]) z = z := by
          calc
            (theta^[2 * m]) z = ((theta^[2])^[m]) z := by
              rw [Function.iterate_mul]
            _ = z := Function.iterate_fixed htheta_two_iter m
        have hodd : (theta^[2 * m + 1]) z = theta z := by
          rw [show 2 * m + 1 = (2 * m).succ by omega,
            Function.iterate_succ_apply', heven]
        have htheta_fixed : theta z = z :=
          hodd.symm.trans (hkPeriod z)
        have hzinv : z⁻¹ = z := htheta_z.symm.trans htheta_fixed
        have hzsq : z ^ 2 = 1 := by
          rw [pow_two]
          nth_rw 2 [← hzinv]
          exact mul_inv_cancel₀ hz
        have hzOne : z = 1 := by
          rcases sq_eq_one_iff.mp hzsq with hzOne | hzNeg
          · exact hzOne
          · simpa [ZModModule.neg_eq_self] using hzNeg
        have hzdiv : x / y = 1 := by
          simpa [z, div_eq_mul_inv] using hzOne
        exact (div_eq_one_iff_eq hy).mp hzdiv
      exact ⟨hinjective,
        Finite.injective_iff_surjective.mp hinjective⟩
    have hVNormalization :
        ∃ vNorm : K ≃ₗ[ZMod 2] ↥V,
          ∀ b : K,
            finalCenterCoordinates.symm
                (squareMap (vNorm b :
                  Additive (LowerCentralFactor P 0))) =
              b * theta b := by
      have hsigma_order : orderOf sigma = n := by
        rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
          GaloisField.finrank 2 (by omega : n ≠ 0)]
      have hsigma_pow : sigma ^ n = 1 := by
        have := pow_orderOf_eq_one sigma
        simpa only [hsigma_order] using this
      have hthetaOfGap (i j : Fin n) :
          sigma ^ (j : ℕ) * (sigma ^ (i : ℕ)).symm =
            sigma ^ forwardGap i j := by
        change sigma ^ (j : ℕ) * (sigma ^ (i : ℕ))⁻¹ =
          sigma ^ forwardGap i j
        by_cases hij : (i : ℕ) ≤ (j : ℕ)
        · rw [← pow_sub sigma hij]
          congr 1
          simp only [forwardGap, if_pos hij]
        · have hji : (j : ℕ) ≤ (i : ℕ) := by omega
          have hd_le : (i : ℕ) - (j : ℕ) ≤ n := by omega
          rw [show forwardGap i j = n - ((i : ℕ) - (j : ℕ)) by
            simp only [forwardGap, if_neg hij]]
          calc
            sigma ^ (j : ℕ) * (sigma ^ (i : ℕ))⁻¹ =
                (sigma ^ ((i : ℕ) - (j : ℕ)))⁻¹ := by
              rw [pow_sub sigma hji, mul_inv_rev, inv_inv]
            _ = sigma ^ (n - ((i : ℕ) - (j : ℕ))) := by
              symm
              rw [pow_sub sigma hd_le, hsigma_pow, one_mul]
      let rhoV : K ≃ₐ[ZMod 2] K := (sigma ^ (iv : ℕ)).symm
      let thetaVAlg : K ≃ₐ[ZMod 2] K :=
        sigma ^ (jv : ℕ) * rhoV
      let thetaV : K ≃+* K := thetaVAlg.toRingEquiv
      have hthetaVAlg_eq : thetaVAlg = thetaAlg := by
        calc
          thetaVAlg = sigma ^ s := by
            simpa only [thetaVAlg, rhoV] using hthetaOfGap iv jv
          _ = sigma ^ r := by rw [hsame]
          _ = thetaAlg := by
            simpa only [thetaAlg, rhoU] using
              (hthetaOfGap iu ju).symm
      have hthetaV_eq : thetaV = theta := by
        simpa only [thetaV, theta] using
          congrArg (fun e : K ≃ₐ[ZMod 2] K => e.toRingEquiv)
            hthetaVAlg_eq
      let vUnit : Kˣ := Units.mk0 cv hcv
      let vOutputTransform : K ≃ₗ[ZMod 2] K :=
        (sigma ^ (sv : ℕ)).toLinearEquiv.trans
          ((vUnit⁻¹).mulLeftLinearEquiv (ZMod 2) K)
      let vOwnCenterCoordinates :
          K ≃ₗ[ZMod 2] Additive (LowerCentralFactor P 1) :=
        vOutputTransform.symm.trans centerCoordinates
      let vOwnNorm : K ≃ₗ[ZMod 2] ↥V :=
        rhoV.toLinearEquiv.trans vCoordinates
      have hvOwnSquare (b : K) :
          vOwnCenterCoordinates.symm
              (squareMap (vOwnNorm b :
                Additive (LowerCentralFactor P 0))) =
            b * theta b := by
        have hnormalize := lemma12_pair_monomial_normalize
          n iv jv sv cv hcv
          (fun x : K => centerCoordinates.symm
            (squareMap (vCoordinates x :
              Additive (LowerCentralFactor P 0)))) hVformula b
        have hv :
            vOwnCenterCoordinates.symm
                (squareMap (vOwnNorm b :
                  Additive (LowerCentralFactor P 0))) =
              b * thetaV b := by
          change (vUnit.mulLeftLinearEquiv (ZMod 2) K).symm _ = _
          rw [Units.symm_mulLeftLinearEquiv_apply]
          simpa [K, sigma, rhoV, thetaVAlg, thetaV, vUnit, vOwnNorm]
            using hnormalize
        simpa only [hthetaV_eq] using hv
      let psi : K ≃ₐ[ZMod 2] K :=
        sigma ^ (su : ℕ) * (sigma ^ (sv : ℕ)).symm
      have hpsiThetaAlg : psi * thetaAlg = thetaAlg * psi := by
        dsimp only [psi, thetaAlg, rhoU]
        change sigma ^ (su : ℕ) * (sigma ^ (sv : ℕ))⁻¹ *
            sigma ^ (ju : ℕ) * (sigma ^ (iu : ℕ))⁻¹ =
          sigma ^ (ju : ℕ) * (sigma ^ (iu : ℕ))⁻¹ *
            sigma ^ (su : ℕ) * (sigma ^ (sv : ℕ))⁻¹
        group
      have hpsi_theta (x : K) : psi (theta x) = theta (psi x) := by
        change psi (thetaAlg x) = thetaAlg (psi x)
        simpa only [AlgEquiv.mul_apply] using
          DFunLike.congr_fun hpsiThetaAlg x
      let delta : K := cu⁻¹ * psi cv
      have hdelta : delta ≠ 0 := by
        exact mul_ne_zero (inv_ne_zero hcu)
          (psi.map_ne_zero_iff.mpr hcv)
      have hcenterTransition
          (z : Additive (LowerCentralFactor P 1)) :
          finalCenterCoordinates.symm z =
            delta * psi (vOwnCenterCoordinates.symm z) := by
        change cu⁻¹ * (sigma ^ (su : ℕ))
            (centerCoordinates.symm z) =
          (cu⁻¹ * psi cv) *
            psi (cv⁻¹ * (sigma ^ (sv : ℕ))
              (centerCoordinates.symm z))
        rw [map_mul, map_inv₀]
        simp only [psi, AlgEquiv.mul_apply,
          AlgEquiv.symm_apply_apply]
        have hcv' :
            (sigma ^ (su : ℕ))
                ((sigma ^ (sv : ℕ)).symm cv) ≠ 0 :=
          (sigma ^ (su : ℕ)).map_ne_zero_iff.mpr
            ((sigma ^ (sv : ℕ)).symm.map_ne_zero_iff.mpr hcv)
        field_simp
      obtain ⟨w, hw⟩ := hthetaNorm_bijective.2 delta⁻¹
      change w * theta w = delta⁻¹ at hw
      have hw_ne : w ≠ 0 := by
        intro hwZero
        subst w
        apply inv_ne_zero hdelta
        simpa using hw.symm
      let t : K := psi.symm w
      have ht : t ≠ 0 := psi.symm.map_ne_zero_iff.mpr hw_ne
      let tUnit : Kˣ := Units.mk0 t ht
      let inputTransform : K ≃ₗ[ZMod 2] K :=
        psi.symm.toLinearEquiv.trans
          (tUnit.mulLeftLinearEquiv (ZMod 2) K)
      let vNorm : K ≃ₗ[ZMod 2] ↥V :=
        inputTransform.trans vOwnNorm
      have hinput_apply (b : K) :
          inputTransform b = t * psi.symm b := by
        rfl
      have hpsi_t : psi t = w := by
        simp only [t, psi.apply_symm_apply]
      have hpsi_input (b : K) : psi (inputTransform b) = w * b := by
        rw [hinput_apply, map_mul, hpsi_t, psi.apply_symm_apply]
      have hinputNorm (b : K) :
          delta * psi
              (inputTransform b * theta (inputTransform b)) =
            b * theta b := by
        rw [map_mul, hpsi_input, hpsi_theta, hpsi_input, map_mul]
        calc
          delta * (w * b * (theta w * theta b)) =
              (delta * (w * theta w)) * (b * theta b) := by ring
          _ = b * theta b := by
            rw [hw, mul_inv_cancel₀ hdelta, one_mul]
      refine ⟨vNorm, ?_⟩
      intro b
      change finalCenterCoordinates.symm
          (squareMap (vOwnNorm (inputTransform b) :
            Additive (LowerCentralFactor P 0))) = b * theta b
      rw [hcenterTransition, hvOwnSquare]
      exact hinputNorm b
    obtain ⟨vNorm, hvNormSquare⟩ := hVNormalization
    have hcommonActorData :
        ∃ (lambdaUnit : Kˣ) (nuNorm : K),
          nuNorm ≠ 0 ∧
          orderOf lambdaUnit = 2 ^ n - 1 ∧
          nuNorm = (lambdaUnit : K) * theta (lambdaUnit : K) ∧
          (∀ a : K,
            xiU (uNorm a) =
              uNorm ((lambdaUnit : K) * a)) ∧
          (∀ b : K,
            xiV (vNorm b) =
              vNorm ((lambdaUnit : K) * b)) ∧
          ∀ z : K,
            S (finalCenterCoordinates z) =
              finalCenterCoordinates (nuNorm * z) := by
      let lambdaNorm : K := (sigma ^ (iu : ℕ)) lambda
      let nuNorm : K := (sigma ^ (su : ℕ)) nu
      have hlambdaNorm : lambdaNorm ≠ 0 := by
        exact (sigma ^ (iu : ℕ)).map_ne_zero_iff.mpr hlambda
      have hnuNorm : nuNorm ≠ 0 := by
        exact (sigma ^ (su : ℕ)).map_ne_zero_iff.mpr hnu
      have hUActor (a : K) :
          xiU (uNorm a) = uNorm (lambdaNorm * a) := by
        change xiU (uCoordinates (rhoU a)) =
          uCoordinates (rhoU (lambdaNorm * a))
        rw [huCoordinates]
        apply congrArg uCoordinates
        rw [map_mul]
        congr 1
        change lambda =
          (sigma ^ (iu : ℕ)).symm
            ((sigma ^ (iu : ℕ)) lambda)
        exact ((sigma ^ (iu : ℕ)).symm_apply_apply lambda).symm
      have hcenterActor (z : K) :
          S (finalCenterCoordinates z) =
            finalCenterCoordinates (nuNorm * z) := by
        change S (centerCoordinates (outputTransform.symm z)) =
          centerCoordinates (outputTransform.symm (nuNorm * z))
        rw [hcenterCoordinates]
        apply congrArg centerCoordinates
        apply outputTransform.injective
        rw [outputTransform.apply_symm_apply]
        change cu⁻¹ * (sigma ^ (su : ℕ))
            (nu * outputTransform.symm z) = nuNorm * z
        rw [map_mul]
        have hz := outputTransform.apply_symm_apply z
        change cu⁻¹ * (sigma ^ (su : ℕ))
            (outputTransform.symm z) = z at hz
        have hnuNorm_def :
            (sigma ^ (su : ℕ)) nu = nuNorm := rfl
        rw [hnuNorm_def]
        calc
          cu⁻¹ * (nuNorm * (sigma ^ (su : ℕ))
              (outputTransform.symm z)) =
              nuNorm * (cu⁻¹ * (sigma ^ (su : ℕ))
                (outputTransform.symm z)) := by ring
          _ = nuNorm * z := by rw [hz]
      have hnuNormFormula :
          nuNorm = lambdaNorm * theta lambdaNorm := by
        have hsigma_apply (x : K) (t : ℕ) :
            (sigma ^ t) x = x ^ (2 ^ t) := by
          rw [AlgEquiv.coe_pow,
            FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
          simp [ZMod.card]
        change (sigma ^ (su : ℕ)) nu =
          (sigma ^ (iu : ℕ)) lambda *
            (sigma ^ (ju : ℕ) * (sigma ^ (iu : ℕ)).symm)
              ((sigma ^ (iu : ℕ)) lambda)
        rw [AlgEquiv.mul_apply,
          (sigma ^ (iu : ℕ)).symm_apply_apply]
        calc
          (sigma ^ (su : ℕ)) nu = nu ^ (2 ^ (su : ℕ)) :=
            hsigma_apply nu (su : ℕ)
          _ = lambda ^ (2 ^ (iu : ℕ)) *
              lambda ^ (2 ^ (ju : ℕ)) := hUseed.symm
          _ = (sigma ^ (iu : ℕ)) lambda *
              (sigma ^ (ju : ℕ)) lambda := by
            rw [hsigma_apply, hsigma_apply]
      have hlambdaNormOrder :
          orderOf (Units.mk0 lambdaNorm hlambdaNorm) =
            2 ^ n - 1 := by
        let sigmaUnits : Kˣ →* Kˣ :=
          Units.map (sigma ^ (iu : ℕ)).toRingEquiv.toMonoidHom
        have hsigmaUnits : Function.Injective sigmaUnits :=
          Units.map_injective (sigma ^ (iu : ℕ)).injective
        have hmap :
            sigmaUnits (Units.mk0 lambda hlambda) =
              Units.mk0 lambdaNorm hlambdaNorm := by
          apply Units.ext
          rfl
        calc
          orderOf (Units.mk0 lambdaNorm hlambdaNorm) =
              orderOf (sigmaUnits
                (Units.mk0 lambda hlambda)) := by rw [hmap]
          _ = orderOf (Units.mk0 lambda hlambda) :=
            orderOf_injective sigmaUnits hsigmaUnits _
          _ = 2 ^ n - 1 := hlambda_order
      have hcenterActorCoordinate
          (z : Additive (LowerCentralFactor P 1)) :
          finalCenterCoordinates.symm (S z) =
            nuNorm * finalCenterCoordinates.symm z := by
        calc
          finalCenterCoordinates.symm (S z) =
              finalCenterCoordinates.symm
                (S (finalCenterCoordinates
                  (finalCenterCoordinates.symm z))) := by
            rw [finalCenterCoordinates.apply_symm_apply]
          _ = finalCenterCoordinates.symm
                (finalCenterCoordinates
                  (nuNorm * finalCenterCoordinates.symm z)) := by
            rw [hcenterActor]
          _ = nuNorm * finalCenterCoordinates.symm z :=
            finalCenterCoordinates.symm_apply_apply _
      have hVActor (b : K) :
          xiV (vNorm b) = vNorm (lambdaNorm * b) := by
        apply vNorm.symm.injective
        simp only [vNorm.symm_apply_apply]
        apply hthetaNorm_bijective.1
        calc
          vNorm.symm (xiV (vNorm b)) *
                theta (vNorm.symm (xiV (vNorm b))) =
              finalCenterCoordinates.symm
                (squareMap (vNorm
                  (vNorm.symm (xiV (vNorm b))) :
                    Additive (LowerCentralFactor P 0))) :=
            (hvNormSquare _).symm
          _ = finalCenterCoordinates.symm
                (squareMap (xiV (vNorm b) :
                  Additive (LowerCentralFactor P 0))) := by
            rw [vNorm.apply_symm_apply]
          _ = finalCenterCoordinates.symm
                (S (squareMap (vNorm b :
                  Additive (LowerCentralFactor P 0)))) := by
            have hactor := hsquare_xiV_pow 1 (vNorm b)
            simpa only [pow_one] using congrArg
              finalCenterCoordinates.symm hactor
          _ = nuNorm * finalCenterCoordinates.symm
                (squareMap (vNorm b :
                  Additive (LowerCentralFactor P 0))) :=
            hcenterActorCoordinate _
          _ = nuNorm * (b * theta b) := by
            rw [hvNormSquare]
          _ = (lambdaNorm * b) *
                theta (lambdaNorm * b) := by
            rw [hnuNormFormula, map_mul]
            ring
      exact ⟨Units.mk0 lambdaNorm hlambdaNorm, nuNorm, hnuNorm,
        hlambdaNormOrder, hnuNormFormula, hUActor, hVActor,
        hcenterActor⟩
    obtain ⟨lambdaUnit, nuNorm, hnuNorm, hlambdaUnitOrder,
      hnuNormFormula, hUActor, hVActor, hcenterActor⟩ :=
      hcommonActorData
    let normalizedCross : K →ₗ[ZMod 2] K →ₗ[ZMod 2] K :=
      { toFun := fun a =>
          { toFun := fun b => finalCenterCoordinates.symm
              (crossBracket (uNorm a) (vNorm b))
            map_add' := by
              intro b c
              simp
            map_smul' := by
              intro c b
              simp }
        map_add' := by
          intro a b
          apply LinearMap.ext
          intro c
          simp
        map_smul' := by
          intro c a
          apply LinearMap.ext
          intro b
          simp }
    obtain ⟨normalizedCoeff, hnormalizedCrossExpansionRaw,
        hnormalizedSupport⟩ :=
      PFAppendixIII.frobeniusBilinear_expansion_with_support_of_equivariant
        n (by omega) normalizedCross (lambdaUnit : K)
          (lambdaUnit : K) nuNorm (by
            intro a b
            change finalCenterCoordinates.symm
                (crossBracket
                  (uNorm ((lambdaUnit : K) * a))
                  (vNorm ((lambdaUnit : K) * b))) =
              nuNorm * finalCenterCoordinates.symm
                (crossBracket (uNorm a) (vNorm b))
            apply finalCenterCoordinates.injective
            calc
              finalCenterCoordinates
                    (finalCenterCoordinates.symm
                      (crossBracket
                        (uNorm ((lambdaUnit : K) * a))
                        (vNorm ((lambdaUnit : K) * b)))) =
                  crossBracket
                    (uNorm ((lambdaUnit : K) * a))
                    (vNorm ((lambdaUnit : K) * b)) :=
                finalCenterCoordinates.apply_symm_apply _
              _ = crossBracket (xiU (uNorm a)) (xiV (vNorm b)) := by
                rw [hUActor, hVActor]
              _ = S (crossBracket (uNorm a) (vNorm b)) :=
                hcross_equivariant _ _
              _ = S (finalCenterCoordinates
                  (finalCenterCoordinates.symm
                    (crossBracket (uNorm a) (vNorm b)))) := by
                rw [finalCenterCoordinates.apply_symm_apply]
              _ = finalCenterCoordinates
                  (nuNorm * finalCenterCoordinates.symm
                    (crossBracket (uNorm a) (vNorm b))) :=
                hcenterActor _)
    have hnormalizedCrossExpansion :
        ∀ a b : K,
          finalCenterCoordinates.symm
              (crossBracket (uNorm a) (vNorm b)) =
            ∑ i : Fin n, ∑ j : Fin n,
              normalizedCoeff i j * a ^ (2 ^ (i : ℕ)) *
                b ^ (2 ^ (j : ℕ)) := by
      simpa [K, normalizedCross] using hnormalizedCrossExpansionRaw
    have hsameSupportedPowers :
        ∀ i j : Fin n, normalizedCoeff i j ≠ 0 →
          ((∀ a : K, a ^ (2 ^ (i : ℕ)) = a) ∧
            ∀ b : K, b ^ (2 ^ (j : ℕ)) = theta b) ∨
          ((∀ a : K, a ^ (2 ^ (i : ℕ)) = theta a) ∧
            ∀ b : K, b ^ (2 ^ (j : ℕ)) = b) := by
      have hsigma_order : orderOf sigma = n := by
        rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
          GaloisField.finrank 2 (by omega : n ≠ 0)]
      have hsigma_pow : sigma ^ n = 1 := by
        have h := pow_orderOf_eq_one sigma
        simpa only [hsigma_order] using h
      have hthetaAlg_eq : thetaAlg = sigma ^ r := by
        change sigma ^ (ju : ℕ) * (sigma ^ (iu : ℕ))⁻¹ =
          sigma ^ forwardGap iu ju
        by_cases hij : (iu : ℕ) ≤ (ju : ℕ)
        · rw [← pow_sub sigma hij]
          congr 1
          simp only [forwardGap, if_pos hij]
        · have hji : (ju : ℕ) ≤ (iu : ℕ) := by omega
          have hd_le : (iu : ℕ) - (ju : ℕ) ≤ n := by omega
          rw [show forwardGap iu ju =
            n - ((iu : ℕ) - (ju : ℕ)) by
              simp only [forwardGap, if_neg hij]]
          calc
            sigma ^ (ju : ℕ) * (sigma ^ (iu : ℕ))⁻¹ =
                (sigma ^ ((iu : ℕ) - (ju : ℕ)))⁻¹ := by
              rw [pow_sub sigma hji, mul_inv_rev, inv_inv]
            _ = sigma ^ (n - ((iu : ℕ) - (ju : ℕ))) := by
              symm
              rw [pow_sub sigma hd_le, hsigma_pow, one_mul]
      have hthetaFrobenius (x : K) :
          theta x = x ^ (2 ^ r) := by
        change thetaAlg x = _
        rw [hthetaAlg_eq, AlgEquiv.coe_pow,
          FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
        simp [ZMod.card]
      have hr_lt : r < n := by omega
      intro i j hij
      have hpower :
          (lambdaUnit : K) ^
                (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) =
            (lambdaUnit : K) ^ (2 ^ 0 + 2 ^ r) := by
        calc
          (lambdaUnit : K) ^
                (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) =
              (lambdaUnit : K) ^ (2 ^ (i : ℕ)) *
                (lambdaUnit : K) ^ (2 ^ (j : ℕ)) := by
            rw [pow_add]
          _ = nuNorm := hnormalizedSupport i j hij
          _ = (lambdaUnit : K) *
                theta (lambdaUnit : K) := hnuNormFormula
          _ = (lambdaUnit : K) ^ (2 ^ 0 + 2 ^ r) := by
            rw [hthetaFrobenius, pow_add]
            simp
      have hunit :
          lambdaUnit ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) =
            lambdaUnit ^ (2 ^ 0 + 2 ^ r) := by
        apply Units.ext
        simpa only [Units.val_pow_eq_pow_val] using hpower
      have hmod : Nat.ModEq (2 ^ n - 1)
          (2 ^ (i : ℕ) + 2 ^ (j : ℕ))
          (2 ^ 0 + 2 ^ r) := by
        have h := pow_eq_pow_iff_modEq.mp hunit
        simpa only [hlambdaUnitOrder] using h
      have hij_ne : (i : ℕ) ≠ (j : ℕ) := by
        intro heq
        have hmodRepeated : Nat.ModEq (2 ^ n - 1)
            (2 ^ (i : ℕ) + 2 ^ (i : ℕ))
            (2 ^ 0 + 2 ^ r) := by
          simpa only [heq] using hmod
        have hsingle : Nat.ModEq (2 ^ n - 1)
            (2 ^ (((i : ℕ) + 1) % n))
            (2 ^ 0 + 2 ^ r) :=
          (lemma6_two_pow_add_self_modEq_cyclic n (i : ℕ)
            hd i.isLt).symm.trans hmodRepeated
        exact (lemma6_single_two_pow_not_modEq_pair_two_pow
          n (((i : ℕ) + 1) % n) 0 r
          (Nat.mod_lt _ hd) hr_pos hr_lt) hsingle
      have horient :
          ((i : ℕ) = 0 ∧ (j : ℕ) = r) ∨
            ((i : ℕ) = r ∧ (j : ℕ) = 0) := by
        rcases lt_or_gt_of_ne hij_ne with hij_lt | hji_lt
        · exact lemma6_pair_two_pow_modEq_classify
            n (i : ℕ) (j : ℕ) 0 r i.isLt j.isLt hij_ne
              hr_pos hr_lt hmod
        · have hmod' : Nat.ModEq (2 ^ n - 1)
              (2 ^ (j : ℕ) + 2 ^ (i : ℕ))
              (2 ^ 0 + 2 ^ r) := by
            simpa only [add_comm] using hmod
          rcases lemma6_pair_two_pow_modEq_classify
              n (j : ℕ) (i : ℕ) 0 r j.isLt i.isLt
                hij_ne.symm hr_pos hr_lt hmod' with hfirst | hsecond
          · exact Or.inr ⟨hfirst.2, hfirst.1⟩
          · exact Or.inl ⟨hsecond.2, hsecond.1⟩
      rcases horient with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · left
        constructor
        · intro a
          rw [hi]
          simp
        · intro b
          rw [hj]
          exact (hthetaFrobenius b).symm
      · right
        constructor
        · intro a
          rw [hi]
          exact (hthetaFrobenius a).symm
        · intro b
          rw [hj]
          simp
    have htwoTermCross :
        ∃ epsilon delta : K,
          (epsilon ≠ 0 ∨ delta ≠ 0) ∧
          ∀ a b : K,
            finalCenterCoordinates.symm
                (crossBracket (uNorm a) (vNorm b)) =
              epsilon * a * theta b + delta * theta a * b := by
      classical
      let firstSupport (i j : Fin n) : Prop :=
        (∀ a : K, a ^ (2 ^ (i : ℕ)) = a) ∧
          ∀ b : K, b ^ (2 ^ (j : ℕ)) = theta b
      let epsilon : K := ∑ i : Fin n, ∑ j : Fin n,
        if firstSupport i j then normalizedCoeff i j else 0
      let delta : K := ∑ i : Fin n, ∑ j : Fin n,
        if firstSupport i j then 0 else normalizedCoeff i j
      have hformula (a b : K) :
          finalCenterCoordinates.symm
              (crossBracket (uNorm a) (vNorm b)) =
            epsilon * a * theta b + delta * theta a * b := by
        rw [hnormalizedCrossExpansion]
        calc
          (∑ i : Fin n, ∑ j : Fin n,
              normalizedCoeff i j * a ^ (2 ^ (i : ℕ)) *
                b ^ (2 ^ (j : ℕ))) =
              ∑ i : Fin n, ∑ j : Fin n,
                ((if firstSupport i j then normalizedCoeff i j else 0) *
                    a * theta b +
                  (if firstSupport i j then 0 else normalizedCoeff i j) *
                    theta a * b) := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases hcoeff : normalizedCoeff i j = 0
            · simp [hcoeff]
            · by_cases hfirst : firstSupport i j
              · simp only [if_pos hfirst, hfirst.1 a, hfirst.2 b,
                  zero_mul, add_zero]
              · have hsecond :=
                  (hsameSupportedPowers i j hcoeff).resolve_left hfirst
                simp only [if_neg hfirst, hsecond.1 a, hsecond.2 b,
                  zero_mul, zero_add]
          _ = epsilon * a * theta b + delta * theta a * b := by
            simp only [epsilon, delta, Finset.sum_add_distrib,
              ← Finset.sum_mul, mul_assoc]
      have hnonzero : epsilon ≠ 0 ∨ delta ≠ 0 := by
        by_contra hboth
        push Not at hboth
        obtain ⟨u, v, huv⟩ := hcross_nonzero
        have hzero :
            finalCenterCoordinates.symm (crossBracket u v) = 0 := by
          have h := hformula (uNorm.symm u) (vNorm.symm v)
          rw [uNorm.apply_symm_apply, vNorm.apply_symm_apply,
            hboth.1, hboth.2] at h
          simpa using h
        apply huv
        change crossBracket u v = 0
        apply finalCenterCoordinates.symm.injective
        simpa using hzero
      exact ⟨epsilon, delta, hnonzero, hformula⟩
    obtain ⟨epsilonRaw, deltaRaw, hcrossRawNonzero,
      htwoTermCross⟩ := htwoTermCross
    have hcomplementShear :
        ∃ (epsilon : K)
            (quotientCoordinates :
              (K × K) ≃ₗ[ZMod 2]
                Additive (LowerCentralFactor P 0)),
          epsilon ≠ 0 ∧
          (∀ a b : K,
            finalCenterCoordinates.symm
                (squareMap (quotientCoordinates (a, b))) =
              a * theta a + epsilon * a * theta b +
                b * theta b) ∧
          ∀ a b : K,
            T (quotientCoordinates (a, b)) =
              quotientCoordinates
                ((lambdaUnit : K) * a, (lambdaUnit : K) * b) := by
      let baseCoordinates :
          (K × K) ≃ₗ[ZMod 2]
            Additive (LowerCentralFactor P 0) :=
        (uNorm.prodCongr vNorm).trans
          (Submodule.prodEquivOfIsCompl U V hUV)
      have hbaseActor (a b : K) :
          T (baseCoordinates (a, b)) =
            baseCoordinates
              ((lambdaUnit : K) * a, (lambdaUnit : K) * b) := by
        change T ((uNorm a : Additive (LowerCentralFactor P 0)) +
            (vNorm b : Additive (LowerCentralFactor P 0))) =
          (uNorm ((lambdaUnit : K) * a) :
              Additive (LowerCentralFactor P 0)) +
            (vNorm ((lambdaUnit : K) * b) :
              Additive (LowerCentralFactor P 0))
        rw [map_add, hT_u, hT_v, hUActor, hVActor]
      have hbaseSquare (a b : K) :
          finalCenterCoordinates.symm
              (squareMap (baseCoordinates (a, b))) =
            a * theta a + epsilonRaw * a * theta b +
              deltaRaw * theta a * b + b * theta b := by
        change finalCenterCoordinates.symm
          (squareMap ((uNorm a :
              Additive (LowerCentralFactor P 0)) +
            (vNorm b : Additive (LowerCentralFactor P 0)))) = _
        rw [hsquare_add]
        simp only [map_add]
        change
          finalCenterCoordinates.symm
              (squareMap (uNorm a :
                Additive (LowerCentralFactor P 0))) +
            finalCenterCoordinates.symm
              (squareMap (vNorm b :
                Additive (LowerCentralFactor P 0))) +
            finalCenterCoordinates.symm
              (crossBracket (uNorm a) (vNorm b)) = _
        rw [huNormSquare, hvNormSquare, htwoTermCross]
        ring
      have hshearEquiv :
          ∃ shear : (K × K) ≃ₗ[ZMod 2] (K × K),
            ∀ a b : K, shear (a, b) =
              (a + deltaRaw * b, b) := by
        let shearMap : (K × K) →ₗ[ZMod 2] (K × K) :=
          { toFun := fun x =>
              (x.1 + deltaRaw * x.2, x.2)
            map_add' := by
              intro x y
              apply Prod.ext
              · dsimp
                ring
              · rfl
            map_smul' := by
              intro c x
              fin_cases c <;> simp }
        have hinjective : Function.Injective shearMap := by
          intro x y hxy
          have hsecondRaw :=
            congrArg (fun z : K × K => z.2) hxy
          change x.2 = y.2 at hsecondRaw
          have hsecond : x.2 = y.2 := hsecondRaw
          have hfirstRaw :=
            congrArg (fun z : K × K => z.1) hxy
          change x.1 + deltaRaw * x.2 =
            y.1 + deltaRaw * y.2 at hfirstRaw
          have hfirst : x.1 = y.1 := by
            rw [hsecond] at hfirstRaw
            exact add_right_cancel hfirstRaw
          exact Prod.ext hfirst hsecond
        have hsurjective : Function.Surjective shearMap := by
          intro y
          refine ⟨(y.1 + deltaRaw * y.2, y.2), ?_⟩
          apply Prod.ext
          · change (y.1 + deltaRaw * y.2) +
              deltaRaw * y.2 = y.1
            rw [add_assoc, ZModModule.add_self, add_zero]
          · rfl
        let shear : (K × K) ≃ₗ[ZMod 2] (K × K) :=
          LinearEquiv.ofBijective shearMap
            ⟨hinjective, hsurjective⟩
        refine ⟨shear, ?_⟩
        intro a b
        rfl
      obtain ⟨shear, hshear⟩ := hshearEquiv
      let shearedCoordinates := shear.trans baseCoordinates
      let t : K := 1 + epsilonRaw * deltaRaw
      have hshearedSquare (a b : K) :
          finalCenterCoordinates.symm
              (squareMap (shearedCoordinates (a, b))) =
            a * theta a +
              (epsilonRaw + theta deltaRaw) * a * theta b +
                t * (b * theta b) := by
        change finalCenterCoordinates.symm
          (squareMap (baseCoordinates
            (shear (a, b)))) = _
        rw [hshear, hbaseSquare, map_add, map_mul]
        dsimp [t]
        calc
          (a + deltaRaw * b) * (theta a + theta deltaRaw * theta b) +
                epsilonRaw * (a + deltaRaw * b) * theta b +
                deltaRaw * (theta a + theta deltaRaw * theta b) * b +
              b * theta b =
            (a * theta a + (epsilonRaw + theta deltaRaw) * a * theta b +
                (1 + epsilonRaw * deltaRaw) * (b * theta b)) +
              (deltaRaw * b * theta a + deltaRaw * b * theta a) +
              (deltaRaw * b * theta deltaRaw * theta b +
                deltaRaw * b * theta deltaRaw * theta b) := by ring
          _ = a * theta a +
                (epsilonRaw + theta deltaRaw) * a * theta b +
                  (1 + epsilonRaw * deltaRaw) * (b * theta b) := by
            simp only [ZModModule.add_self, add_zero]
      have ht : t ≠ 0 := by
        intro htZero
        have hcenterZero :
            finalCenterCoordinates.symm
                (squareMap (shearedCoordinates (0, 1))) = 0 := by
          rw [hshearedSquare, htZero]
          simp
        have hsquareZero :
            squareMap (shearedCoordinates (0, 1)) = 0 := by
          apply finalCenterCoordinates.symm.injective
          simpa using hcenterZero
        have hquotientZero : shearedCoordinates (0, 1) = 0 :=
          hsquare_anisotropic _ hsquareZero
        have hpairZero : ((0, 1) : K × K) = 0 := by
          apply shearedCoordinates.injective
          simp at hquotientZero
        have hone : (1 : K) = 0 := by
          simpa using congrArg Prod.snd hpairZero
        exact one_ne_zero hone
      obtain ⟨w, hw⟩ := hthetaNorm_bijective.2 t⁻¹
      change w * theta w = t⁻¹ at hw
      have hw_ne : w ≠ 0 := by
        intro hwZero
        subst w
        apply inv_ne_zero ht
        simpa using hw.symm
      let wUnit : Kˣ := Units.mk0 w hw_ne
      let scale : (K × K) ≃ₗ[ZMod 2] (K × K) :=
        (LinearEquiv.refl (ZMod 2) K).prodCongr
          (wUnit.mulLeftLinearEquiv (ZMod 2) K)
      let quotientCoordinates := scale.trans shearedCoordinates
      let epsilon : K :=
        (epsilonRaw + theta deltaRaw) * theta w
      have hfinalSquare (a b : K) :
          finalCenterCoordinates.symm
              (squareMap (quotientCoordinates (a, b))) =
            a * theta a + epsilon * a * theta b +
              b * theta b := by
        change finalCenterCoordinates.symm
          (squareMap (shearedCoordinates (a, w * b))) = _
        rw [hshearedSquare, map_mul]
        have hnorm : t * (w * theta w) = 1 := by
          rw [hw, mul_inv_cancel₀ ht]
        dsimp [epsilon]
        calc
          a * theta a +
                (epsilonRaw + theta deltaRaw) * a *
                  (theta w * theta b) +
              t * (w * b * (theta w * theta b)) =
            a * theta a +
                ((epsilonRaw + theta deltaRaw) * theta w) *
                  a * theta b +
              (t * (w * theta w)) * (b * theta b) := by
            ring
          _ = a * theta a +
              ((epsilonRaw + theta deltaRaw) * theta w) *
                a * theta b + b * theta b := by
            rw [hnorm, one_mul]
      have hepsilon : epsilon ≠ 0 := by
        intro hepsilonZero
        have hcenterZero :
            finalCenterCoordinates.symm
                (squareMap (quotientCoordinates (1, 1))) = 0 := by
          rw [hfinalSquare, hepsilonZero]
          simpa using (ZModModule.add_self (1 : K))
        have hsquareZero :
            squareMap (quotientCoordinates (1, 1)) = 0 := by
          apply finalCenterCoordinates.symm.injective
          simpa using hcenterZero
        have hquotientZero : quotientCoordinates (1, 1) = 0 :=
          hsquare_anisotropic _ hsquareZero
        have hpairZero : ((1, 1) : K × K) = 0 := by
          apply quotientCoordinates.injective
          simp at hquotientZero
        have hone : (1 : K) = 0 := by
          simpa using congrArg Prod.fst hpairZero
        exact one_ne_zero hone
      refine ⟨epsilon, quotientCoordinates, hepsilon, hfinalSquare, ?_⟩
      intro a b
      change T (baseCoordinates (shear (a, w * b))) =
        baseCoordinates
          (shear ((lambdaUnit : K) * a,
            w * ((lambdaUnit : K) * b)))
      rw [hbaseActor]
      apply congrArg baseCoordinates
      rw [hshear, hshear]
      apply Prod.ext <;> dsimp <;> ring
    obtain ⟨epsilon, quotientCoordinates, hepsilon, hq,
      hquotientActor⟩ := hcomplementShear
    have hanisotropic :
        ∀ a b : K, a ≠ 0 → b ≠ 0 →
          a * theta a + epsilon * a * theta b +
              b * theta b ≠ 0 := by
      intro a b ha _hb hzero
      have hcenterZero :
          finalCenterCoordinates.symm
              (squareMap (quotientCoordinates (a, b))) = 0 := by
        rw [hq]
        exact hzero
      have hsquareZero :
          squareMap (quotientCoordinates (a, b)) = 0 := by
        apply finalCenterCoordinates.symm.injective
        simpa using hcenterZero
      have hquotientZero : quotientCoordinates (a, b) = 0 :=
        hsquare_anisotropic _ hsquareZero
      have habZero : (a, b) = 0 := by
        apply quotientCoordinates.injective
        simpa using hquotientZero
      exact ha (congrArg Prod.fst habZero)
    refine ⟨theta, epsilon, quotientCoordinates,
      finalCenterCoordinates, lambdaUnit, hepsilon, hthetaPeriod,
      hanisotropic, hq, hlambdaUnitOrder, hquotientActor, ?_⟩
    intro z
    simpa only [hnuNormFormula] using hcenterActor z
  exact hsamePairCompletion

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma12_distinct_pair_typeD_forward_data
    {P : Type u} [Group P] [Finite P] [Fact (Nat.Prime 2)]
    [Fact (IsPGroup 2 P)] [Group.IsNilpotent P]
    (n : ℕ) (hn : 2 ≤ n)
    (U V : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)))
    (squareMap : Additive (LowerCentralFactor P 0) →
      Additive (LowerCentralFactor P 1))
    (crossBracket : U →ₗ[ZMod 2] V →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1))
    (hcross_nonzero : ∃ u : U, ∃ v : V, crossBracket u v ≠ 0)
    (centerCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1))
    (uCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2] U)
    (vCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2] V)
    (iu ju su iv jv sv : Fin n)
    (cu cv : BinaryGaloisField n) (hcu : cu ≠ 0) (hcv : cv ≠ 0)
    (hUformula : ∀ a : BinaryGaloisField n,
      (FiniteField.frobeniusAlgEquivOfAlgebraic
          (ZMod 2) (BinaryGaloisField n) ^ (su : ℕ))
          (centerCoordinates.symm
            (squareMap (uCoordinates a :
              Additive (LowerCentralFactor P 0)))) =
        cu * a ^ (2 ^ (iu : ℕ) + 2 ^ (ju : ℕ)))
    (hVformula : ∀ b : BinaryGaloisField n,
      (FiniteField.frobeniusAlgEquivOfAlgebraic
          (ZMod 2) (BinaryGaloisField n) ^ (sv : ℕ))
          (centerCoordinates.symm
            (squareMap (vCoordinates b :
              Additive (LowerCentralFactor P 0)))) =
        cv * b ^ (2 ^ (iv : ℕ) + 2 ^ (jv : ℕ)))
    (r s : ℕ)
    (hrGap :
      (if iu.val ≤ ju.val then ju.val - iu.val else n - (iu.val - ju.val)) = r)
    (hsGap :
      (if iv.val ≤ jv.val then jv.val - iv.val else n - (iv.val - jv.val)) = s)
    (hr_pos : 0 < r) (_ : 0 < s)
    (hsr : s = 2 * r) (hn5 : n = 5 * r)
    (crossCoeff : Fin n → Fin n → BinaryGaloisField n)
    (hcrossExpansion : ∀ a b : BinaryGaloisField n,
      centerCoordinates.symm
          (crossBracket (uCoordinates a) (vCoordinates b)) =
        ∑ i : Fin n, ∑ j : Fin n,
          crossCoeff i j * a ^ (2 ^ (i : ℕ)) * b ^ (2 ^ (j : ℕ)))
    (hnormalizedSupport : ∀ i j : Fin n, crossCoeff i j ≠ 0 →
      ((i : ℕ) + (su : ℕ) + (n - (iu : ℕ))) % n = 3 * r ∧
      ((j : ℕ) + (sv : ℕ) + (n - (iv : ℕ))) % n = r) :
    ∃ (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
        (epsilon : BinaryGaloisField n)
        (uD : BinaryGaloisField n ≃ₗ[ZMod 2] U)
        (vD : BinaryGaloisField n ≃ₗ[ZMod 2] V)
        (centerD : BinaryGaloisField n ≃ₗ[ZMod 2]
          Additive (LowerCentralFactor P 1)),
      epsilon ≠ 0 ∧
      (∀ x : BinaryGaloisField n, theta^[5] x = x) ∧
      (∃ x : BinaryGaloisField n, theta x ≠ x) ∧
      (∀ a : BinaryGaloisField n, centerD.symm
        (squareMap (uD a : Additive (LowerCentralFactor P 0))) =
          a * theta a) ∧
      (∀ b : BinaryGaloisField n, centerD.symm
        (squareMap (vD b : Additive (LowerCentralFactor P 0))) =
          b * theta^[2] b) ∧
      ∀ a b : BinaryGaloisField n, centerD.symm
        (crossBracket (uD a) (vD b)) =
          epsilon * theta^[3] a * theta b := by
      let K : Type := BinaryGaloisField n
      have hd : 0 < n := by omega
      let sigma : K ≃ₐ[ZMod 2] K :=
        FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
      have hsigma_order : orderOf sigma = n := by
        rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
          GaloisField.finrank 2 (by omega : n ≠ 0)]
      have hsigma_pow : sigma ^ n = 1 := by
        have h := pow_orderOf_eq_one sigma
        simpa only [hsigma_order] using h
      let forwardGap (i j : Fin n) : ℕ :=
        if i.val ≤ j.val then j.val - i.val else n - (i.val - j.val)
      have hthetaOfGap (i j : Fin n) :
          sigma ^ (j : ℕ) * (sigma ^ (i : ℕ)).symm =
            sigma ^ forwardGap i j := by
        change sigma ^ (j : ℕ) * (sigma ^ (i : ℕ))⁻¹ =
          sigma ^ forwardGap i j
        by_cases hij : (i : ℕ) ≤ (j : ℕ)
        · rw [← pow_sub sigma hij]
          congr 1
          simp only [forwardGap, if_pos hij]
        · have hji : (j : ℕ) ≤ (i : ℕ) := by omega
          have hle : (i : ℕ) - (j : ℕ) ≤ n := by omega
          rw [show forwardGap i j = n - ((i : ℕ) - (j : ℕ)) by
            simp only [forwardGap, if_neg hij]]
          calc
            sigma ^ (j : ℕ) * (sigma ^ (i : ℕ))⁻¹ =
                (sigma ^ ((i : ℕ) - (j : ℕ)))⁻¹ := by
              rw [pow_sub sigma hji, mul_inv_rev, inv_inv]
            _ = sigma ^ (n - ((i : ℕ) - (j : ℕ))) := by
              symm
              rw [pow_sub sigma hle, hsigma_pow, one_mul]
      let rhoU : K ≃ₐ[ZMod 2] K := (sigma ^ (iu : ℕ)).symm
      let thetaAlg : K ≃ₐ[ZMod 2] K := sigma ^ (ju : ℕ) * rhoU
      let theta : K ≃+* K := thetaAlg.toRingEquiv
      have hthetaAlg_eq : thetaAlg = sigma ^ r := by
        calc
          thetaAlg = sigma ^ forwardGap iu ju := by
            simpa only [thetaAlg, rhoU] using hthetaOfGap iu ju
          _ = sigma ^ r := by
            rw [show forwardGap iu ju = r by
              simpa [forwardGap] using hrGap]
      have hthetaAlg_pow : thetaAlg ^ 5 = 1 := by
        rw [hthetaAlg_eq, ← pow_mul]
        have hrexp : r * 5 = n := by omega
        rw [hrexp, hsigma_pow]
      have hthetaFive : ∀ x : K, theta^[5] x = x := by
        intro x
        have h := DFunLike.congr_fun hthetaAlg_pow x
        simpa [theta, AlgEquiv.coe_pow] using h
      have hthetaNontrivial : ∃ x : K, theta x ≠ x := by
        by_contra hfixed
        push Not at hfixed
        have hthetaAlg_one : thetaAlg = 1 := by
          ext x
          simpa [theta] using hfixed x
        have hsigma_r : sigma ^ r = 1 := by
          rw [← hthetaAlg_eq, hthetaAlg_one]
        have hn_dvd_r : n ∣ r := by
          rw [← hsigma_order]
          exact (orderOf_dvd_iff_pow_eq_one).2 hsigma_r
        have hnr := Nat.le_of_dvd hr_pos hn_dvd_r
        omega
      let cUnit : Kˣ := Units.mk0 cu hcu
      let outputTransform : K ≃ₗ[ZMod 2] K :=
        (sigma ^ (su : ℕ)).toLinearEquiv.trans
          ((cUnit⁻¹).mulLeftLinearEquiv (ZMod 2) K)
      let centerD : K ≃ₗ[ZMod 2]
          Additive (LowerCentralFactor P 1) :=
        outputTransform.symm.trans centerCoordinates
      let uD : K ≃ₗ[ZMod 2] U :=
        rhoU.toLinearEquiv.trans uCoordinates
      have huD (a : K) : centerD.symm
          (squareMap (uD a : Additive (LowerCentralFactor P 0))) =
            a * theta a := by
        have hnormalize := lemma12_pair_monomial_normalize
          n iu ju su cu hcu
          (fun x : K => centerCoordinates.symm
            (squareMap (uCoordinates x :
              Additive (LowerCentralFactor P 0)))) hUformula a
        change (cUnit.mulLeftLinearEquiv (ZMod 2) K).symm _ = _
        rw [Units.symm_mulLeftLinearEquiv_apply]
        simpa [K, sigma, rhoU, thetaAlg, theta, cUnit, uD] using
          hnormalize
      let rhoV : K ≃ₐ[ZMod 2] K := (sigma ^ (iv : ℕ)).symm
      let thetaVAlg : K ≃ₐ[ZMod 2] K := sigma ^ (jv : ℕ) * rhoV
      let thetaV : K ≃+* K := thetaVAlg.toRingEquiv
      have hthetaVAlg_eq : thetaVAlg = thetaAlg ^ 2 := by
        calc
          thetaVAlg = sigma ^ forwardGap iv jv := by
            simpa only [thetaVAlg, rhoV] using hthetaOfGap iv jv
          _ = sigma ^ s := by
            rw [show forwardGap iv jv = s by
              simpa [forwardGap] using hsGap]
          _ = sigma ^ (2 * r) := by rw [hsr]
          _ = sigma ^ (r * 2) := by congr 1; omega
          _ = (sigma ^ r) ^ 2 := by rw [pow_mul]
          _ = thetaAlg ^ 2 := by rw [hthetaAlg_eq]
      have hthetaV_apply (x : K) : thetaV x = theta^[2] x := by
        change thetaVAlg x = thetaAlg (thetaAlg x)
        rw [hthetaVAlg_eq]
        rfl
      have hthetaVAlg_pow : thetaVAlg ^ 5 = 1 := by
        rw [hthetaVAlg_eq, ← pow_mul]
        have hexp : 2 * 5 = 5 * 2 := by omega
        rw [hexp, pow_mul, hthetaAlg_pow, one_pow]
      have hthetaVPeriod :
          ∃ k : ℕ, Odd k ∧ 0 < k ∧ ∀ x : K, thetaV^[k] x = x := by
        refine ⟨5, ⟨2, by norm_num⟩, by norm_num, ?_⟩
        intro x
        have h := DFunLike.congr_fun hthetaVAlg_pow x
        simpa [thetaV, AlgEquiv.coe_pow] using h
      have hthetaVNorm :=
        lemma12_odd_period_norm_bijective n thetaV hthetaVPeriod
      let vUnit : Kˣ := Units.mk0 cv hcv
      let vOutputTransform : K ≃ₗ[ZMod 2] K :=
        (sigma ^ (sv : ℕ)).toLinearEquiv.trans
          ((vUnit⁻¹).mulLeftLinearEquiv (ZMod 2) K)
      let vOwnCenter : K ≃ₗ[ZMod 2]
          Additive (LowerCentralFactor P 1) :=
        vOutputTransform.symm.trans centerCoordinates
      let vOwn : K ≃ₗ[ZMod 2] V :=
        rhoV.toLinearEquiv.trans vCoordinates
      have hvOwn (b : K) : vOwnCenter.symm
          (squareMap (vOwn b : Additive (LowerCentralFactor P 0))) =
            b * thetaV b := by
        have hnormalize := lemma12_pair_monomial_normalize
          n iv jv sv cv hcv
          (fun x : K => centerCoordinates.symm
            (squareMap (vCoordinates x :
              Additive (LowerCentralFactor P 0)))) hVformula b
        change (vUnit.mulLeftLinearEquiv (ZMod 2) K).symm _ = _
        rw [Units.symm_mulLeftLinearEquiv_apply]
        simpa [K, sigma, rhoV, thetaVAlg, thetaV, vUnit, vOwn] using
          hnormalize
      let psi : K ≃ₐ[ZMod 2] K :=
        sigma ^ (su : ℕ) * (sigma ^ (sv : ℕ)).symm
      have hpsiThetaVAlg : psi * thetaVAlg = thetaVAlg * psi := by
        dsimp only [psi, thetaVAlg, rhoV]
        change sigma ^ (su : ℕ) * (sigma ^ (sv : ℕ))⁻¹ *
            sigma ^ (jv : ℕ) * (sigma ^ (iv : ℕ))⁻¹ =
          sigma ^ (jv : ℕ) * (sigma ^ (iv : ℕ))⁻¹ *
            sigma ^ (su : ℕ) * (sigma ^ (sv : ℕ))⁻¹
        group
      have hpsiThetaV (x : K) : psi (thetaV x) = thetaV (psi x) := by
        change psi (thetaVAlg x) = thetaVAlg (psi x)
        simpa only [AlgEquiv.mul_apply] using
          DFunLike.congr_fun hpsiThetaVAlg x
      let delta : K := cu⁻¹ * psi cv
      have hdelta : delta ≠ 0 :=
        mul_ne_zero (inv_ne_zero hcu) (psi.map_ne_zero_iff.mpr hcv)
      have hcenterTransition
          (z : Additive (LowerCentralFactor P 1)) :
          centerD.symm z = delta * psi (vOwnCenter.symm z) := by
        change cu⁻¹ * (sigma ^ (su : ℕ))
            (centerCoordinates.symm z) =
          (cu⁻¹ * psi cv) *
            psi (cv⁻¹ * (sigma ^ (sv : ℕ))
              (centerCoordinates.symm z))
        rw [map_mul, map_inv₀]
        simp only [psi, AlgEquiv.mul_apply, AlgEquiv.symm_apply_apply]
        have hcv' :
            (sigma ^ (su : ℕ)) ((sigma ^ (sv : ℕ)).symm cv) ≠ 0 :=
          (sigma ^ (su : ℕ)).map_ne_zero_iff.mpr
            ((sigma ^ (sv : ℕ)).symm.map_ne_zero_iff.mpr hcv)
        field_simp
      obtain ⟨w, hw⟩ := hthetaVNorm.2 delta⁻¹
      change w * thetaV w = delta⁻¹ at hw
      have hw_ne : w ≠ 0 := by
        intro hwZero
        subst w
        apply inv_ne_zero hdelta
        simpa using hw.symm
      let t : K := psi.symm w
      have ht : t ≠ 0 := psi.symm.map_ne_zero_iff.mpr hw_ne
      let tUnit : Kˣ := Units.mk0 t ht
      let inputTransform : K ≃ₗ[ZMod 2] K :=
        psi.symm.toLinearEquiv.trans
          (tUnit.mulLeftLinearEquiv (ZMod 2) K)
      let vD : K ≃ₗ[ZMod 2] V := inputTransform.trans vOwn
      have hinput_apply (b : K) :
          inputTransform b = t * psi.symm b := by rfl
      have hpsi_t : psi t = w := by
        simp only [t, psi.apply_symm_apply]
      have hpsi_input (b : K) : psi (inputTransform b) = w * b := by
        rw [hinput_apply, map_mul, hpsi_t, psi.apply_symm_apply]
      have hinputNorm (b : K) :
          delta * psi
              (inputTransform b * thetaV (inputTransform b)) =
            b * thetaV b := by
        rw [map_mul, hpsi_input, hpsiThetaV, hpsi_input, map_mul]
        calc
          delta * (w * b * (thetaV w * thetaV b)) =
              (delta * (w * thetaV w)) * (b * thetaV b) := by ring
          _ = b * thetaV b := by
            rw [hw, mul_inv_cancel₀ hdelta, one_mul]
      have hvD (b : K) : centerD.symm
          (squareMap (vD b : Additive (LowerCentralFactor P 0))) =
            b * theta^[2] b := by
        change centerD.symm
          (squareMap (vOwn (inputTransform b) :
            Additive (LowerCentralFactor P 0))) = _
        rw [hcenterTransition, hvOwn]
        rw [hinputNorm, hthetaV_apply]
      have hsigma_apply (x : K) (m : ℕ) :
          (sigma ^ m) x = x ^ (2 ^ m) := by
        rw [AlgEquiv.coe_pow,
          FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
        simp [ZMod.card]
      let iNorm (i : Fin n) : ℕ :=
        ((i : ℕ) + (su : ℕ) + (n - (iu : ℕ))) % n
      let jNorm (j : Fin n) : ℕ :=
        ((j : ℕ) + (sv : ℕ) + (n - (iv : ℕ))) % n
      have hnormalizedSupport' (i j : Fin n)
          (hcoeff : crossCoeff i j ≠ 0) :
          iNorm i = 3 * r ∧ jNorm j = r := by
        simpa [iNorm, jNorm] using hnormalizedSupport i j hcoeff
      have hUShift (i : Fin n) (a : K) :
          (sigma ^ (su : ℕ))
              ((rhoU a) ^ (2 ^ (i : ℕ))) =
            (sigma ^ (iNorm i)) a := by
        simpa [sigma, rhoU, iNorm] using
          lemma12_frobenius_shift_normalize n hd i su iu a
      have hVShift (j : Fin n) (b : K) :
          (sigma ^ (su : ℕ))
              ((rhoV (psi.symm b)) ^ (2 ^ (j : ℕ))) =
            (sigma ^ (jNorm j)) b := by
        calc
          (sigma ^ (su : ℕ))
                ((rhoV (psi.symm b)) ^ (2 ^ (j : ℕ))) =
              (sigma ^ (sv : ℕ))
                (((sigma ^ (iv : ℕ)).symm b) ^
                  (2 ^ (j : ℕ))) := by
            rw [← hsigma_apply, ← hsigma_apply]
            change (sigma ^ (su : ℕ) * sigma ^ (j : ℕ) *
                rhoV * psi.symm) b =
              (sigma ^ (sv : ℕ) * sigma ^ (j : ℕ) *
                (sigma ^ (iv : ℕ)).symm) b
            congr 1
            dsimp only [rhoV, psi]
            change sigma ^ (su : ℕ) * sigma ^ (j : ℕ) *
                (sigma ^ (iv : ℕ))⁻¹ *
                  (sigma ^ (su : ℕ) *
                    (sigma ^ (sv : ℕ))⁻¹)⁻¹ =
              sigma ^ (sv : ℕ) * sigma ^ (j : ℕ) *
                (sigma ^ (iv : ℕ))⁻¹
            group
          _ = (sigma ^ (jNorm j)) b := by
            simpa [sigma, jNorm] using
              lemma12_frobenius_shift_normalize n hd j sv iv b
      have hthetaOne (x : K) : (sigma ^ r) x = theta x := by
        rw [← hthetaAlg_eq]
        rfl
      have hthetaThree (x : K) :
          (sigma ^ (3 * r)) x = theta^[3] x := by
        have hpow : sigma ^ (3 * r) = thetaAlg ^ 3 := by
          calc
            sigma ^ (3 * r) = sigma ^ (r * 3) := by congr 1; omega
            _ = (sigma ^ r) ^ 3 := by rw [pow_mul]
            _ = thetaAlg ^ 3 := by rw [← hthetaAlg_eq]
        rw [hpow]
        simp [theta, AlgEquiv.coe_pow]
      let transformedCoeff (i j : Fin n) : K :=
        cu⁻¹ * (sigma ^ (su : ℕ))
          (crossCoeff i j * (rhoV t) ^ (2 ^ (j : ℕ)))
      have hterm (i j : Fin n) (a b : K)
          (hcoeff : crossCoeff i j ≠ 0) :
          cu⁻¹ * (sigma ^ (su : ℕ))
              (crossCoeff i j * (rhoU a) ^ (2 ^ (i : ℕ)) *
                (rhoV (inputTransform b)) ^ (2 ^ (j : ℕ))) =
            transformedCoeff i j * theta^[3] a * theta b := by
        rw [hinput_apply]
        calc
          cu⁻¹ * (sigma ^ (su : ℕ))
                (crossCoeff i j * (rhoU a) ^ (2 ^ (i : ℕ)) *
                  (rhoV (t * psi.symm b)) ^ (2 ^ (j : ℕ))) =
              cu⁻¹ * (sigma ^ (su : ℕ))
                ((crossCoeff i j * (rhoV t) ^ (2 ^ (j : ℕ))) *
                  (rhoU a) ^ (2 ^ (i : ℕ)) *
                    (rhoV (psi.symm b)) ^ (2 ^ (j : ℕ))) := by
            congr 2
            rw [map_mul, mul_pow]
            ring
          _ = transformedCoeff i j *
                (sigma ^ (su : ℕ))
                  ((rhoU a) ^ (2 ^ (i : ℕ))) *
                (sigma ^ (su : ℕ))
                  ((rhoV (psi.symm b)) ^ (2 ^ (j : ℕ))) := by
            dsimp only [transformedCoeff]
            rw [map_mul, map_mul]
            ring
          _ = transformedCoeff i j * theta^[3] a * theta b := by
            obtain ⟨hi, hj⟩ := hnormalizedSupport' i j hcoeff
            rw [hUShift, hVShift, hi, hj, hthetaThree, hthetaOne]
      have hcrossRaw (a b : K) : centerD.symm
          (crossBracket (uD a) (vD b)) =
            ∑ i : Fin n, ∑ j : Fin n,
              transformedCoeff i j * theta^[3] a * theta b := by
        change cu⁻¹ * (sigma ^ (su : ℕ))
            (centerCoordinates.symm
              (crossBracket (uCoordinates (rhoU a))
                (vCoordinates (rhoV (inputTransform b))))) = _
        rw [hcrossExpansion]
        simp only [map_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hcoeff : crossCoeff i j = 0
        · simp [hcoeff, transformedCoeff]
        · exact hterm i j a b hcoeff
      let epsilon : K := ∑ i : Fin n, ∑ j : Fin n,
        transformedCoeff i j
      have hcrossD (a b : K) : centerD.symm
          (crossBracket (uD a) (vD b)) =
            epsilon * theta^[3] a * theta b := by
        simpa only [epsilon, ← Finset.sum_mul] using hcrossRaw a b
      have hepsilon : epsilon ≠ 0 := by
        intro hepsilonZero
        obtain ⟨u, v, huv⟩ := hcross_nonzero
        have hzero : centerD.symm (crossBracket u v) = 0 := by
          have h := hcrossD (uD.symm u) (vD.symm v)
          rw [uD.apply_symm_apply, vD.apply_symm_apply,
            hepsilonZero] at h
          simpa using h
        apply huv
        apply centerD.symm.injective
        simpa using hzero
      exact ⟨theta, epsilon, uD, vD, centerD, hepsilon,
        hthetaFive, hthetaNontrivial, huD, hvD, hcrossD⟩
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma12_distinct_pair_typeD_normal_form_core
    {P : Type u} [Group P] [Finite P] [Fact (Nat.Prime 2)]
    [Fact (IsPGroup 2 P)] [Group.IsNilpotent P]
    (n : ℕ) (hn : 2 ≤ n)
    (U V : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)))
    (hUV : IsCompl U V)
    (squareMap : Additive (LowerCentralFactor P 0) →
      Additive (LowerCentralFactor P 1))
    (crossBracket : U →ₗ[ZMod 2] V →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1))
    (hsquare_add_cross : ∀ (u : U) (v : V),
      squareMap ((u : Additive (LowerCentralFactor P 0)) +
          (v : Additive (LowerCentralFactor P 0))) =
        squareMap (u : Additive (LowerCentralFactor P 0)) +
          squareMap (v : Additive (LowerCentralFactor P 0)) +
            crossBracket u v)
    (hcross_nonzero : ∃ u : U, ∃ v : V, crossBracket u v ≠ 0)
    (lambda mu nu : BinaryGaloisField n) (hlambda : lambda ≠ 0)
    (hlambda_order : orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1)
    (centerCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1))
    (uCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2] U)
    (vCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2] V)
    (iu ju su iv jv sv : Fin n)
    (cu cv : BinaryGaloisField n) (hcu : cu ≠ 0) (hcv : cv ≠ 0)
    (hUseed : lambda ^ (2 ^ (iu : ℕ)) * lambda ^ (2 ^ (ju : ℕ)) =
      nu ^ (2 ^ (su : ℕ)))
    (hVseed : mu ^ (2 ^ (iv : ℕ)) * mu ^ (2 ^ (jv : ℕ)) =
      nu ^ (2 ^ (sv : ℕ)))
    (hUformula : ∀ a : BinaryGaloisField n,
      (FiniteField.frobeniusAlgEquivOfAlgebraic
          (ZMod 2) (BinaryGaloisField n) ^ (su : ℕ))
          (centerCoordinates.symm
            (squareMap (uCoordinates a :
              Additive (LowerCentralFactor P 0)))) =
        cu * a ^ (2 ^ (iu : ℕ) + 2 ^ (ju : ℕ)))
    (hVformula : ∀ b : BinaryGaloisField n,
      (FiniteField.frobeniusAlgEquivOfAlgebraic
          (ZMod 2) (BinaryGaloisField n) ^ (sv : ℕ))
          (centerCoordinates.symm
            (squareMap (vCoordinates b :
              Additive (LowerCentralFactor P 0)))) =
        cv * b ^ (2 ^ (iv : ℕ) + 2 ^ (jv : ℕ)))
    (r s : ℕ)
    (hrGap :
      (if iu.val ≤ ju.val then ju.val - iu.val else n - (iu.val - ju.val)) = r)
    (hsGap :
      (if iv.val ≤ jv.val then jv.val - iv.val else n - (iv.val - jv.val)) = s)
    (hr_pos : 0 < r) (hs_pos : 0 < s)
    (hgapClassification :
      (s = 2 * r ∧ n = 5 * r) ∨ (r = 2 * s ∧ n = 5 * s))
    (crossCoeff : Fin n → Fin n → BinaryGaloisField n)
    (hcrossExpansion : ∀ a b : BinaryGaloisField n,
      centerCoordinates.symm
          (crossBracket (uCoordinates a) (vCoordinates b)) =
        ∑ i : Fin n, ∑ j : Fin n,
          crossCoeff i j * a ^ (2 ^ (i : ℕ)) * b ^ (2 ^ (j : ℕ)))
    (hcrossCoefficientSupport : ∀ i j : Fin n, crossCoeff i j ≠ 0 →
      lambda ^ (2 ^ (i : ℕ)) * mu ^ (2 ^ (j : ℕ)) = nu) :
    ∃ (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
        (epsilon : BinaryGaloisField n)
        (quotientCoordinates :
          (BinaryGaloisField n × BinaryGaloisField n) ≃ₗ[ZMod 2]
            Additive (LowerCentralFactor P 0))
        (finalCenterCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2]
          Additive (LowerCentralFactor P 1)),
      epsilon ≠ 0 ∧
      (∀ x : BinaryGaloisField n, theta^[5] x = x) ∧
      (∃ x : BinaryGaloisField n, theta x ≠ x) ∧
      ∀ a b : BinaryGaloisField n,
        finalCenterCoordinates.symm
            (squareMap (quotientCoordinates (a, b))) =
          a * theta a + epsilon * theta^[3] a * theta b +
            b * theta^[2] b := by
  let K : Type := BinaryGaloisField n
  rcases hgapClassification with hforward | hreverse
  · rcases hforward with ⟨hsr, hn5⟩
    have hr_le : r ≤ n / 2 := by omega
    have hs_le : s ≤ n / 2 := by omega
    have hdiff : r ≠ s := by omega
    have hforwardSupport (i j : Fin n)
        (hcoeff : crossCoeff i j ≠ 0) :
        ((i : ℕ) + (su : ℕ) + (n - (iu : ℕ))) % n = 3 * r ∧
        ((j : ℕ) + (sv : ℕ) + (n - (iv : ℕ))) % n = r := by
      have hfull := lemma12_distinct_pair_gap_of_cross_seed
        n r s hn hr_pos hr_le hs_pos hs_le hdiff
        lambda mu nu hlambda hlambda_order
        iu ju su iv jv sv i j hrGap hsGap hUseed hVseed
        (hcrossCoefficientSupport i j hcoeff)
      rcases hfull with hgood | himpossible
      · exact ⟨hgood.2.2.1, hgood.2.2.2⟩
      · omega
    obtain ⟨theta, epsilon, uD, vD, centerD, hepsilon,
        hthetaFive, hthetaNontrivial, huD, hvD, hcrossD⟩ :=
      lemma12_distinct_pair_typeD_forward_data
        n hn U V squareMap crossBracket hcross_nonzero
        centerCoordinates uCoordinates vCoordinates
        iu ju su iv jv sv cu cv hcu hcv hUformula hVformula
        r s hrGap hsGap hr_pos hs_pos hsr hn5
        crossCoeff hcrossExpansion hforwardSupport
    let quotientCoordinates :
        (K × K) ≃ₗ[ZMod 2]
          Additive (LowerCentralFactor P 0) :=
      (uD.prodCongr vD).trans
        (Submodule.prodEquivOfIsCompl U V hUV)
    refine ⟨theta, epsilon, quotientCoordinates, centerD,
      hepsilon, hthetaFive, hthetaNontrivial, ?_⟩
    intro a b
    change centerD.symm
      (squareMap ((uD a :
          Additive (LowerCentralFactor P 0)) +
        (vD b : Additive (LowerCentralFactor P 0)))) = _
    rw [hsquare_add_cross]
    simp only [map_add]
    rw [huD, hvD, hcrossD]
    ring
  · rcases hreverse with ⟨hrs, hn5⟩
    let reverseCross : V →ₗ[ZMod 2] U →ₗ[ZMod 2]
        Additive (LowerCentralFactor P 1) :=
      { toFun := fun v =>
          { toFun := fun u => crossBracket u v
            map_add' := by
              intro u w
              change crossBracket (u + w) v = _
              rw [map_add, LinearMap.add_apply]
            map_smul' := by
              intro c u
              change crossBracket (c • u) v = _
              rw [map_smul, LinearMap.smul_apply]
              simp only [RingHom.id_apply] }
        map_add' := by
          intro v w
          apply LinearMap.ext
          intro u
          exact (crossBracket u).map_add v w
        map_smul' := by
          intro c v
          apply LinearMap.ext
          intro u
          exact (crossBracket u).map_smul c v }
    have hreverse_nonzero : ∃ v : V, ∃ u : U, reverseCross v u ≠ 0 := by
      obtain ⟨u, v, huv⟩ := hcross_nonzero
      exact ⟨v, u, huv⟩
    let reverseCoeff : Fin n → Fin n → K := fun i j => crossCoeff j i
    have hreverseExpansion (a b : K) :
        centerCoordinates.symm
            (reverseCross (vCoordinates a) (uCoordinates b)) =
          ∑ i : Fin n, ∑ j : Fin n,
            reverseCoeff i j * a ^ (2 ^ (i : ℕ)) *
              b ^ (2 ^ (j : ℕ)) := by
      change centerCoordinates.symm
          (crossBracket (uCoordinates b) (vCoordinates a)) = _
      rw [hcrossExpansion, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      dsimp only [reverseCoeff]
      ring
    have hr_le : r ≤ n / 2 := by omega
    have hs_le : s ≤ n / 2 := by omega
    have hdiff : r ≠ s := by omega
    have hreverseSupport (i j : Fin n)
        (hcoeff : reverseCoeff i j ≠ 0) :
        ((i : ℕ) + (sv : ℕ) + (n - (iv : ℕ))) % n = 3 * s ∧
        ((j : ℕ) + (su : ℕ) + (n - (iu : ℕ))) % n = s := by
      have hcoeff' : crossCoeff j i ≠ 0 := by
        simpa [reverseCoeff] using hcoeff
      have hfull := lemma12_distinct_pair_gap_of_cross_seed
        n r s hn hr_pos hr_le hs_pos hs_le hdiff
        lambda mu nu hlambda hlambda_order
        iu ju su iv jv sv j i hrGap hsGap hUseed hVseed
        (hcrossCoefficientSupport j i hcoeff')
      rcases hfull with himpossible | hgood
      · omega
      · exact ⟨hgood.2.2.2, hgood.2.2.1⟩
    obtain ⟨theta, epsilon, vD, uD, centerD, hepsilon,
        hthetaFive, hthetaNontrivial, hvD, huD, hcrossReverse⟩ :=
      lemma12_distinct_pair_typeD_forward_data
        n hn V U squareMap reverseCross hreverse_nonzero
        centerCoordinates vCoordinates uCoordinates
        iv jv sv iu ju su cv cu hcv hcu hVformula hUformula
        s r hsGap hrGap hs_pos hr_pos hrs hn5
        reverseCoeff hreverseExpansion hreverseSupport
    have hcrossD (a b : K) : centerD.symm
        (crossBracket (uD b) (vD a)) =
          epsilon * theta^[3] a * theta b := by
      simpa [reverseCross] using hcrossReverse a b
    let quotientCoordinates :
        (K × K) ≃ₗ[ZMod 2]
          Additive (LowerCentralFactor P 0) :=
      (vD.prodCongr uD).trans
        (Submodule.prodEquivOfIsCompl V U hUV.symm)
    refine ⟨theta, epsilon, quotientCoordinates, centerD,
      hepsilon, hthetaFive, hthetaNontrivial, ?_⟩
    intro a b
    change centerD.symm
      (squareMap ((vD a :
          Additive (LowerCentralFactor P 0)) +
        (uD b : Additive (LowerCentralFactor P 0)))) = _
    rw [add_comm, hsquare_add_cross]
    simp only [map_add]
    rw [huD, hvD, hcrossD]
    ring
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma12_typeD_avoid_of_anisotropic
    (n : ℕ) {V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (squareMap : V → W)
    (hsquare_anisotropic : ∀ v : V, squareMap v = 0 → v = 0)
    (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
    (epsilon : BinaryGaloisField n)
    (quotientCoordinates :
      (BinaryGaloisField n × BinaryGaloisField n) ≃ₗ[ZMod 2] V)
    (centerCoordinates : BinaryGaloisField n ≃ₗ[ZMod 2] W)
    (hepsilon : epsilon ≠ 0)
    (hthetaFive : ∀ x : BinaryGaloisField n, theta^[5] x = x)
    (hq : ∀ a b : BinaryGaloisField n,
      centerCoordinates.symm (squareMap (quotientCoordinates (a, b))) =
        a * theta a + epsilon * theta^[3] a * theta b +
          b * theta^[2] b) :
    ∀ rho : BinaryGaloisField n,
      epsilon ≠ rho⁻¹ + theta^[4] rho * theta rho * rho⁻¹ := by
  intro rho heq
  by_cases hrho : rho = 0
  · subst rho
    simp at heq
    exact hepsilon heq
  let b : BinaryGaloisField n := theta^[4] rho
  have htheta_b : theta b = rho := by
    simpa [b, Function.iterate_succ_apply'] using hthetaFive rho
  have htheta2_b : theta^[2] b = theta rho := by
    simpa [Function.iterate_succ_apply'] using congrArg theta htheta_b
  have hcenterZero :
      centerCoordinates.symm (squareMap (quotientCoordinates (1, b))) = 0 := by
    rw [hq, heq, htheta_b, htheta2_b]
    dsimp only [b]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      map_one, mul_one]
    have hinv : rho⁻¹ * rho = 1 := inv_mul_cancel₀ hrho
    calc
      1 + (rho⁻¹ + theta^[4] rho * theta rho * rho⁻¹) * rho +
            theta^[4] rho * theta rho =
          1 + (rho⁻¹ * rho +
            (theta^[4] rho * theta rho) * (rho⁻¹ * rho)) +
              theta^[4] rho * theta rho := by ring
      _ = 0 := by
        rw [hinv]
        simp only [mul_one]
        rw [show 1 + (1 + theta^[4] rho * theta rho) +
            theta^[4] rho * theta rho =
          (1 + 1) +
            (theta^[4] rho * theta rho + theta^[4] rho * theta rho) by ac_rfl]
        simp only [ZModModule.add_self]
  have hsquareZero : squareMap (quotientCoordinates (1, b)) = 0 := by
    apply centerCoordinates.symm.injective
    simpa using hcenterZero
  have hquotientZero : quotientCoordinates (1, b) = 0 :=
    hsquare_anisotropic _ hsquareZero
  have hpairZero : ((1, b) : BinaryGaloisField n × BinaryGaloisField n) = 0 := by
    apply quotientCoordinates.injective
    simp at hquotientZero
  exact (one_ne_zero : (1 : BinaryGaloisField n) ≠ 0)
    (by simpa using congrArg Prod.fst hpairZero)
private theorem lemma12_eigenvalue_frobenius_conjugate_of_equivariant_linearEquiv
    (n : ℕ) (hn : 0 < n)
    (lambda mu : BinaryGaloisField n)
    (f : BinaryGaloisField n ≃ₗ[ZMod 2] BinaryGaloisField n)
    (hf : ∀ a : BinaryGaloisField n,
      f (lambda * a) = mu * f a) :
    ∃ i : Fin n, lambda ^ (2 ^ (i : ℕ)) = mu := by
  classical
  let B : BinaryGaloisField n →ₗ[ZMod 2]
      BinaryGaloisField n →ₗ[ZMod 2] BinaryGaloisField n :=
    { toFun := fun a =>
        { toFun := fun b => f a * b
          map_add' := by
            intro b c
            rw [mul_add]
          map_smul' := by
            intro c b
            rw [Algebra.smul_def, Algebra.smul_def]
            simp [RingHom.id_apply]
            ring }
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro c
        simp [add_mul]
      map_smul' := by
        intro c a
        apply LinearMap.ext
        intro b
        rw [map_smul]
        simp [LinearMap.smul_apply, RingHom.id_apply] }
  have hB_equivariant (a b : BinaryGaloisField n) :
      B (lambda * a) (1 * b) = mu * B a b := by
    change f (lambda * a) * (1 * b) = mu * (f a * b)
    rw [hf]
    ring
  obtain ⟨coeff, hcoeffExpansion, hcoeffSupport⟩ :=
    PFAppendixIII.frobeniusBilinear_expansion_with_support_of_equivariant
      n hn B lambda 1 mu hB_equivariant
  have hf_one : f (1 : BinaryGaloisField n) ≠ 0 := by
    intro h
    have h' : f (1 : BinaryGaloisField n) = f 0 := by simp at h
    exact one_ne_zero (f.injective h')
  have hcoeff_nonzero : ∃ i j : Fin n, coeff i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hf_one
    have hexp := hcoeffExpansion 1 1
    simp [B, h] at hexp
  obtain ⟨i, j, hij⟩ := hcoeff_nonzero
  refine ⟨i, ?_⟩
  simpa using hcoeffSupport i j hij

private theorem lemma12_linear_pair_not_frobenius_conjugate
    (n : ℕ) (hn : 0 < n)
    (lambda mu nu : BinaryGaloisField n) (hlambda : lambda ≠ 0)
    (hlambdaOrder : orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1)
    (t iu su iv jv sv : Fin n)
    (ht : lambda ^ (2 ^ (t : ℕ)) = mu)
    (hlinear : lambda ^ (2 ^ (iu : ℕ)) = nu ^ (2 ^ (su : ℕ)))
    (hpair : mu ^ (2 ^ (iv : ℕ)) * mu ^ (2 ^ (jv : ℕ)) =
      nu ^ (2 ^ (sv : ℕ)))
    (hivjv : iv ≠ jv) : False := by
  have hpowEq :
      lambda ^ (2 ^ ((iu : ℕ) + (sv : ℕ))) =
        lambda ^
          (2 ^ ((t : ℕ) + (iv : ℕ) + (su : ℕ)) +
            2 ^ ((t : ℕ) + (jv : ℕ) + (su : ℕ))) := by
    calc
      lambda ^ (2 ^ ((iu : ℕ) + (sv : ℕ))) =
          (lambda ^ (2 ^ (iu : ℕ))) ^ (2 ^ (sv : ℕ)) := by
            rw [pow_add, pow_mul]
      _ = (nu ^ (2 ^ (su : ℕ))) ^ (2 ^ (sv : ℕ)) := by
        rw [hlinear]
      _ = (nu ^ (2 ^ (sv : ℕ))) ^ (2 ^ (su : ℕ)) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      _ = (mu ^ (2 ^ (iv : ℕ)) * mu ^ (2 ^ (jv : ℕ))) ^
          (2 ^ (su : ℕ)) := by rw [hpair]
      _ = ((lambda ^ (2 ^ (t : ℕ))) ^ (2 ^ (iv : ℕ)) *
          (lambda ^ (2 ^ (t : ℕ))) ^ (2 ^ (jv : ℕ))) ^
            (2 ^ (su : ℕ)) := by rw [ht]
      _ = lambda ^
          (2 ^ ((t : ℕ) + (iv : ℕ) + (su : ℕ)) +
            2 ^ ((t : ℕ) + (jv : ℕ) + (su : ℕ))) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
          pow_add]
        congr 1 <;> congr 1 <;> simp only [pow_add] <;> ring
  let lambdaUnit : (BinaryGaloisField n)ˣ := Units.mk0 lambda hlambda
  have hunit :
      lambdaUnit ^ (2 ^ ((iu : ℕ) + (sv : ℕ))) =
        lambdaUnit ^
          (2 ^ ((t : ℕ) + (iv : ℕ) + (su : ℕ)) +
            2 ^ ((t : ℕ) + (jv : ℕ) + (su : ℕ))) := by
    apply Units.ext
    simpa [lambdaUnit] using hpowEq
  have hmodRaw := pow_eq_pow_iff_modEq.mp hunit
  change Nat.ModEq (orderOf lambdaUnit)
      (2 ^ ((iu : ℕ) + (sv : ℕ)))
      (2 ^ ((t : ℕ) + (iv : ℕ) + (su : ℕ)) +
        2 ^ ((t : ℕ) + (jv : ℕ) + (su : ℕ))) at hmodRaw
  rw [hlambdaOrder] at hmodRaw
  let c := ((iu : ℕ) + (sv : ℕ)) % n
  let i := ((t : ℕ) + (iv : ℕ) + (su : ℕ)) % n
  let j := ((t : ℕ) + (jv : ℕ) + (su : ℕ)) % n
  have hleft := lemma6_two_pow_modEq_cyclic n ((iu : ℕ) + (sv : ℕ))
  have hright :=
    (lemma6_two_pow_modEq_cyclic n
      ((t : ℕ) + (iv : ℕ) + (su : ℕ))).add
      (lemma6_two_pow_modEq_cyclic n
        ((t : ℕ) + (jv : ℕ) + (su : ℕ)))
  change Nat.ModEq (2 ^ n - 1)
      (2 ^ ((iu : ℕ) + (sv : ℕ))) (2 ^ c) at hleft
  change Nat.ModEq (2 ^ n - 1)
      (2 ^ ((t : ℕ) + (iv : ℕ) + (su : ℕ)) +
        2 ^ ((t : ℕ) + (jv : ℕ) + (su : ℕ)))
      (2 ^ i + 2 ^ j) at hright
  have hmod : Nat.ModEq (2 ^ n - 1) (2 ^ c) (2 ^ i + 2 ^ j) :=
    hleft.symm.trans (hmodRaw.trans hright)
  have hij : i ≠ j := by
    intro hij
    have hmodN : Nat.ModEq n
        ((t : ℕ) + (iv : ℕ) + (su : ℕ))
        ((t : ℕ) + (jv : ℕ) + (su : ℕ)) := by
      change i = j
      exact hij
    have hshift : Nat.ModEq n
        ((iv : ℕ) + ((t : ℕ) + (su : ℕ)))
        ((jv : ℕ) + ((t : ℕ) + (su : ℕ))) := by
      simpa only [add_assoc, add_comm, add_left_comm] using hmodN
    have hcancel : Nat.ModEq n (iv : ℕ) (jv : ℕ) :=
      Nat.ModEq.add_right_cancel
        (Nat.ModEq.refl ((t : ℕ) + (su : ℕ))) hshift
    exact hivjv (Fin.ext (hcancel.eq_of_lt_of_lt iv.isLt jv.isLt))
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact lemma6_single_two_pow_not_modEq_pair_two_pow
      n c i j (Nat.mod_lt _ hn) hijlt (Nat.mod_lt _ hn) hmod
  · exact lemma6_single_two_pow_not_modEq_pair_two_pow
      n c j i (Nat.mod_lt _ hn) hjilt (Nat.mod_lt _ hn)
        (by simpa only [add_comm] using hmod)

private theorem lemma12_pair_supported_of_frobenius_conjugate
    (n : ℕ) (hn : 0 < n)
    (lambda mu nu : BinaryGaloisField n) (hlambda : lambda ≠ 0)
    (hlambdaOrder : orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1)
    (t iu ju su iv jv sv : Fin n)
    (hiju : iu ≠ ju) (hijv : iv ≠ jv)
    (ht : lambda ^ (2 ^ (t : ℕ)) = mu)
    (hUseed : lambda ^ (2 ^ (iu : ℕ)) * lambda ^ (2 ^ (ju : ℕ)) =
      nu ^ (2 ^ (su : ℕ)))
    (hVseed : mu ^ (2 ^ (iv : ℕ)) * mu ^ (2 ^ (jv : ℕ)) =
      nu ^ (2 ^ (sv : ℕ))) :
    lemma6_finPairSupported (lemma6_finPairGap iu ju) iv jv := by
  let lambdaUnit : (BinaryGaloisField n)ˣ := Units.mk0 lambda hlambda
  have hUseedPow :
      lambda ^ (2 ^ (iu : ℕ) + 2 ^ (ju : ℕ)) =
        nu ^ (2 ^ (su : ℕ)) := by
    simpa only [pow_add] using hUseed
  have hVseedPow :
      mu ^ (2 ^ (iv : ℕ) + 2 ^ (jv : ℕ)) =
        nu ^ (2 ^ (sv : ℕ)) := by
    simpa only [pow_add] using hVseed
  have hpowEq :
      lambda ^
          ((2 ^ (iu : ℕ) + 2 ^ (ju : ℕ)) * 2 ^ (sv : ℕ)) =
        lambda ^
          ((2 ^ (iv : ℕ) + 2 ^ (jv : ℕ)) *
            2 ^ ((t : ℕ) + (su : ℕ))) := by
    calc
      lambda ^
          ((2 ^ (iu : ℕ) + 2 ^ (ju : ℕ)) * 2 ^ (sv : ℕ)) =
          (lambda ^ (2 ^ (iu : ℕ) + 2 ^ (ju : ℕ))) ^
            (2 ^ (sv : ℕ)) := by rw [pow_mul]
      _ = (nu ^ (2 ^ (su : ℕ))) ^ (2 ^ (sv : ℕ)) := by
        rw [hUseedPow]
      _ = (nu ^ (2 ^ (sv : ℕ))) ^ (2 ^ (su : ℕ)) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      _ = (mu ^ (2 ^ (iv : ℕ) + 2 ^ (jv : ℕ))) ^
          (2 ^ (su : ℕ)) := by rw [hVseedPow]
      _ = ((lambda ^ (2 ^ (t : ℕ))) ^
          (2 ^ (iv : ℕ) + 2 ^ (jv : ℕ))) ^
            (2 ^ (su : ℕ)) := by rw [ht]
      _ = lambda ^
          ((2 ^ (iv : ℕ) + 2 ^ (jv : ℕ)) *
            2 ^ ((t : ℕ) + (su : ℕ))) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        simp only [pow_add]
        ring
  have hunit :
      lambdaUnit ^
          ((2 ^ (iu : ℕ) + 2 ^ (ju : ℕ)) * 2 ^ (sv : ℕ)) =
        lambdaUnit ^
          ((2 ^ (iv : ℕ) + 2 ^ (jv : ℕ)) *
            2 ^ ((t : ℕ) + (su : ℕ))) := by
    apply Units.ext
    simpa [lambdaUnit] using hpowEq
  have hmod := pow_eq_pow_iff_modEq.mp hunit
  change Nat.ModEq (orderOf lambdaUnit)
      ((2 ^ (iu : ℕ) + 2 ^ (ju : ℕ)) * 2 ^ (sv : ℕ))
      ((2 ^ (iv : ℕ) + 2 ^ (jv : ℕ)) *
        2 ^ ((t : ℕ) + (su : ℕ))) at hmod
  rw [hlambdaOrder] at hmod
  exact lemma6_finPairSupported_of_scaled_pair_modEq
    hn iu ju iv jv hiju hijv (sv : ℕ) ((t : ℕ) + (su : ℕ)) hmod

private theorem lemma12_forward_pair_gap_eq_of_supported
    {n : ℕ} (iu ju iv jv : Fin n)
    (hUgap_pos : 0 < if iu.val ≤ ju.val then ju.val - iu.val
      else n - (iu.val - ju.val))
    (hUgap_le : (if iu.val ≤ ju.val then ju.val - iu.val
      else n - (iu.val - ju.val)) ≤ n / 2)
    (hVgap_pos : 0 < if iv.val ≤ jv.val then jv.val - iv.val
      else n - (iv.val - jv.val))
    (hVgap_le : (if iv.val ≤ jv.val then jv.val - iv.val
      else n - (iv.val - jv.val)) ≤ n / 2)
    (hsupported : lemma6_finPairSupported (lemma6_finPairGap iu ju) iv jv) :
    (if iu.val ≤ ju.val then ju.val - iu.val else n - (iu.val - ju.val)) =
      if iv.val ≤ jv.val then jv.val - iv.val else n - (iv.val - jv.val) := by
  simp only [lemma6_finPairSupported, lemma6_finPairGap] at hsupported
  split_ifs at hUgap_pos hUgap_le hVgap_pos hVgap_le ⊢ <;>
    rcases hsupported with hsupported | hsupported <;> omega

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 8000000 in
 /-- Higman Lemma 12: a Suzuki `2`-group of Omega-length three is type B, C, or
D. -/
public theorem lemma12_chain_typeBCD_with_isomorphic_criterion
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (_hP : IsSuzukiTwoGroup P)
    (_hXcyclic : IsCyclic X) (_hXfaithful : FaithfulSMul X P)
    (_hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    (_hXprimeSupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card X →
      p ∣ Nat.card {x : P // x ∈ involutions P})
    (g : X) (hg : ∀ x : X, x ∈ Subgroup.zpowers g)
    {A B : Subgroup P}
    (hupper :
      A < ⊤ ∧ (⊤ : Subgroup P).Normal ∧ A.Normal ∧
        IsXInvariantSubgroup X (⊤ : Subgroup P) ∧
        IsXInvariantSubgroup X A ∧
        ∀ L : Subgroup P, L.Normal → IsXInvariantSubgroup X L →
          A ≤ L → L ≤ ⊤ → L = A ∨ L = ⊤)
    (hmiddle :
      B < A ∧ A.Normal ∧ B.Normal ∧
        IsXInvariantSubgroup X A ∧ IsXInvariantSubgroup X B ∧
        ∀ L : Subgroup P, L.Normal → IsXInvariantSubgroup X L →
          B ≤ L → L ≤ A → L = B ∨ L = A)
    (hlower :
      (⊥ : Subgroup P) < B ∧ B.Normal ∧ (⊥ : Subgroup P).Normal ∧
        IsXInvariantSubgroup X B ∧
        IsXInvariantSubgroup X (⊥ : Subgroup P) ∧
        ∀ L : Subgroup P, L.Normal → IsXInvariantSubgroup X L →
          ⊥ ≤ L → L ≤ B → L = ⊥ ∨ L = B) :
    (IsSuzukiTwoTypeB (⊤ : Subgroup P) ∨
      IsSuzukiTwoTypeC (⊤ : Subgroup P) ∨
        IsSuzukiTwoTypeD (⊤ : Subgroup P)) ∧
      ((∃ actor : X, Lemma12TypeBActorBranchData X P actor B) ∨
        IsSuzukiTwoTypeC (⊤ : Subgroup P) ∨
          IsSuzukiTwoTypeD (⊤ : Subgroup P)) ∧
      Lemma12SummandData X P B ∧
      Lemma12IsomorphicSummandCriterionData X P B ∧
      (IsMulCommutative A → Lemma12ChainActorData g A B) := by
  classical
  let : Finite P := finite_of_isSuzukiTwoGroup _hP
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 P) := ⟨isPGroup_of_isSuzukiTwoGroup _hP⟩
  let : Group.IsNilpotent P :=
    IsPGroup.isNilpotent (isPGroup_of_isSuzukiTwoGroup _hP)
  have hB_abelian : IsMulCommutative B := by
    let : B.Normal := hlower.2.1
    let D : Subgroup P := (commutator B).map B.subtype
    have hB_ne : B ≠ ⊥ := ne_of_gt hlower.1
    have hD_lt : D < B := by
      rw [show D = ⁅B, B⁆ by exact B.map_subtype_commutator]
      exact Group.IsSolvable.commutator_lt_of_ne_bot hB_ne
    have hD_normal : D.Normal := by
      dsimp [D]
      infer_instance
    have hD_X : IsXInvariantSubgroup X D := by
      let : IsInvariant X P B := ⟨hlower.2.2.2.1⟩
      have hforward : ∀ x : X, ∀ p : P, p ∈ D → x • p ∈ D := by
        intro x p hp
        rcases hp with ⟨b, hb, rfl⟩
        refine ⟨x • b, ?_, rfl⟩
        exact
          (Subgroup.characteristic_iff_le_comap.mp
            (show (commutator B).Characteristic from inferInstance)
            (MulDistribMulAction.toMulAut X B x)) hb
      intro x p
      constructor
      · exact hforward x p
      · intro hp
        have hpinv := hforward x⁻¹ (x • p) hp
        simpa [smul_smul] using hpinv
    have hD_bot : D = ⊥ := by
      rcases hlower.2.2.2.2.2 D hD_normal hD_X bot_le hD_lt.le with hbot | hB
      · exact hbot
      · exact False.elim (hD_lt.ne hB)
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
    apply Subtype.ext
    have hmem : ⁅(x : P), (y : P)⁆ ∈ D := by
      rw [show D = ⁅B, B⁆ by exact B.map_subtype_commutator]
      exact Subgroup.commutator_mem_commutator x.property y.property
    rw [hD_bot] at hmem
    have hcomm_one : ⁅(x : P), (y : P)⁆ = 1 := by
      simpa using hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hcomm_one
  have hB_exponent_two : ∀ x : B, x ^ 2 = 1 := by
    let : B.Normal := hlower.2.1
    let : Fact (IsPGroup 2 B) :=
      ⟨(isPGroup_of_isSuzukiTwoGroup _hP).to_subgroup B⟩
    let S : Subgroup B := squaresSubgroup B
    have hS_le_frattini : S ≤ frattini B := by
      change squaresSubgroup B ≤ frattini B
      rw [squaresSubgroup, Subgroup.closure_le]
      rintro _ ⟨z, rfl⟩
      rw [frattini_eq_closure_commutator_union_powers
        (R := B) (p := 2)]
      exact Subgroup.subset_closure (Or.inr ⟨z, rfl⟩)
    have hB_ne_bot : B ≠ ⊥ := ne_of_gt hlower.1
    have hfrattini_ne_top : frattini B ≠ ⊤ := by
      intro htop
      have hbot_top : (⊥ : Subgroup B) = ⊤ :=
        frattini_nongenerating (G := B) (K := ⊥) (by simp [htop])
      apply hB_ne_bot
      apply le_antisymm
      · intro b hb
        let bB : B := ⟨b, hb⟩
        have hbBot : bB ∈ (⊥ : Subgroup B) := by
          rw [hbot_top]
          trivial
        have hbOne : bB = 1 := by simpa using hbBot
        simpa [bB] using congrArg (fun z : B => (z : P)) hbOne
      · exact bot_le
    have hS_lt_top : S < ⊤ :=
      lt_of_le_of_lt hS_le_frattini
        (lt_top_iff_ne_top.mpr hfrattini_ne_top)
    let D : Subgroup P := S.map B.subtype
    have hD_normal : D.Normal := by
      dsimp [D, S]
      infer_instance
    have hD_X : IsXInvariantSubgroup X D := by
      let : IsInvariant X P B := ⟨hlower.2.2.2.1⟩
      have hforward : ∀ x : X, ∀ p : P, p ∈ D → x • p ∈ D := by
        intro x p hp
        rcases hp with ⟨b, hb, rfl⟩
        refine ⟨x • b, ?_, rfl⟩
        exact
          (Subgroup.characteristic_iff_le_comap.mp
            (squaresSubgroupCharacteristic B)
            (MulDistribMulAction.toMulAut X B x)) hb
      intro x p
      constructor
      · exact hforward x p
      · intro hp
        have hpinv := hforward x⁻¹ (x • p) hp
        simpa [smul_smul] using hpinv
    have hD_lt_B : D < B := by
      have hD_le : D ≤ B := by
        rintro _ ⟨b, _hb, rfl⟩
        exact b.property
      refine lt_of_le_of_ne hD_le ?_
      intro hDB
      have htopmap : (⊤ : Subgroup B).map B.subtype = B := by
        apply le_antisymm
        · rintro _ ⟨b, _hb, rfl⟩
          exact b.property
        · intro b hb
          exact ⟨⟨b, hb⟩, trivial, rfl⟩
      apply hS_lt_top.ne
      apply Subgroup.map_injective B.subtype_injective
      rw [htopmap]
      exact hDB
    have hD_bot : D = ⊥ := by
      rcases hlower.2.2.2.2.2 D hD_normal hD_X bot_le hD_lt_B.le with hbot | hB
      · exact hbot
      · exact False.elim (hD_lt_B.ne hB)
    have hS_bot : S = ⊥ := by
      apply Subgroup.map_injective B.subtype_injective
      rw [Subgroup.map_bot]
      exact hD_bot
    intro x
    have hx : x ^ 2 ∈ S := Subgroup.subset_closure ⟨x, rfl⟩
    rw [hS_bot] at hx
    simpa using hx
  let PhiTop : Subgroup P :=
    (frattini (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype
  let Phi : Subgroup P := frattini P
  have hPhiTop_eq_Phi : PhiTop = Phi := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact
        (frattini_le_comap_frattini_of_surjective
          (φ := (⊤ : Subgroup P).subtype) (by
            intro p
            exact ⟨⟨p, trivial⟩, rfl⟩)) hz
    · intro hp
      have hz :=
        (frattini_le_comap_frattini_of_surjective
          (φ := (Subgroup.topEquiv (G := P)).symm.toMonoidHom)
          (Subgroup.topEquiv (G := P)).symm.surjective) hp
      exact ⟨(Subgroup.topEquiv (G := P)).symm p, hz, by simp⟩
  have hmaximal_abelian :
      ∃ M : Subgroup P,
        M.Normal ∧ IsMulCommutative M ∧ IsXInvariantSubgroup X M ∧
          B ≤ M ∧
          ∀ C : Subgroup P, C.Normal → IsMulCommutative C →
            IsXInvariantSubgroup X C → M < C → False := by
    let : Fintype (Subgroup P) := Fintype.ofFinite _
    let S : Finset (Subgroup P) :=
      Finset.univ.filter fun M =>
        M.Normal ∧ IsMulCommutative M ∧
          IsXInvariantSubgroup X M ∧ B ≤ M
    have hB_mem : B ∈ S := by
      change B ∈ Finset.univ.filter (fun M : Subgroup P =>
        M.Normal ∧ IsMulCommutative M ∧
          IsXInvariantSubgroup X M ∧ B ≤ M)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hmiddle.2.2.1, hB_abelian,
        hmiddle.2.2.2.2.1, le_rfl⟩
    obtain ⟨M, hMmax⟩ := Finset.exists_maximal (s := S) ⟨B, hB_mem⟩
    have hMdata := (Finset.mem_filter.mp hMmax.1).2
    refine ⟨M, hMdata.1, hMdata.2.1, hMdata.2.2.1,
      hMdata.2.2.2, ?_⟩
    intro C hC_normal hC_abelian hC_X hMC
    have hC_mem : C ∈ S := by
      change C ∈ Finset.univ.filter (fun M : Subgroup P =>
        M.Normal ∧ IsMulCommutative M ∧
          IsXInvariantSubgroup X M ∧ B ≤ M)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hC_normal, hC_abelian, hC_X,
        hMdata.2.2.2.trans hMC.le⟩
    exact hMC.2 (hMmax.2 hC_mem hMC.le)
  obtain ⟨M, hM_normal, hM_abelian, hM_X, hB_le_M, hM_max⟩ :=
    hmaximal_abelian
  have hM_data :
      (∀ x : M, x ^ 4 = 1) ∧ PhiTop ≤ M :=
    lemma9_maximal_abelian_contains_frattini
      _hP _hXcyclic _hXfaithful _hXtrans
        hM_normal hM_abelian hM_X hM_max
  have hPhi_le_M : Phi ≤ M := by
    rw [← hPhiTop_eq_Phi]
    exact hM_data.2
  have hPhi_abelian : IsMulCommutative Phi := by
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
    let mx : M := ⟨x, hPhi_le_M x.property⟩
    let my : M := ⟨y, hPhi_le_M y.property⟩
    apply Subtype.ext
    change (x : P) * (y : P) = (y : P) * (x : P)
    exact congrArg Subtype.val (hM_abelian.is_comm.comm mx my)
  have hPhi_normal : Phi.Normal := by
    dsimp [Phi]
    infer_instance
  have hPhi_X : IsXInvariantSubgroup X Phi := by
    change ∀ x : X, ∀ a : P, a ∈ frattini P ↔ x • a ∈ frattini P
    exact (isInvariant_of_characteristic (A := X) (G := P)
      (frattini P)).invariant
  have hPhi_le_A : Phi ≤ A := by
    let C : Subgroup P := A ⊔ Phi
    have hC_normal : C.Normal := by
      let : A.Normal := hmiddle.2.1
      let : Phi.Normal := hPhi_normal
      dsimp [C]
      infer_instance
    have hC_X : IsXInvariantSubgroup X C := by
      let : IsInvariant X P A := ⟨hmiddle.2.2.2.1⟩
      let : IsInvariant X P Phi := ⟨hPhi_X⟩
      exact (isInvariant_sup A Phi).invariant
    rcases hupper.2.2.2.2.2 C hC_normal hC_X le_sup_left le_top with
      hC_A | hC_top
    · exact le_sup_right.trans (le_of_eq hC_A)
    · have hA_top : A = ⊤ :=
        frattini_nongenerating (G := P) (K := A) (by
          simpa [C, Phi] using hC_top)
      exact False.elim (hupper.1.ne hA_top)
  let D : Subgroup P := commutator P
  have hD_normal : D.Normal := by
    dsimp [D]
    infer_instance
  have hD_X : IsXInvariantSubgroup X D := by
    change ∀ x : X, ∀ a : P, a ∈ commutator P ↔ x • a ∈ commutator P
    exact (isInvariant_of_characteristic (A := X) (G := P)
      (commutator P)).invariant
  have hD_ne : D ≠ ⊥ := by
    intro hD_bot
    apply _hP.2.1
    have hcenter_top : Subgroup.center P = ⊤ :=
      (commutator_eq_bot_iff_center_eq_top P).mp (by simpa [D] using hD_bot)
    let : CommGroup P := Group.commGroupOfCenterEqTop hcenter_top
    exact IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => mul_comm x y
  have hB_le_D : B ≤ D := by
    have hall := lemma1_involutions_mem_of_nontrivial_invariant
      _hP _hXtrans hD_X hD_ne
    intro b hb
    by_cases hb_one : b = 1
    · subst b
      exact D.one_mem
    · apply hall b
      refine ⟨hb_one, ?_⟩
      let bB : B := ⟨b, hb⟩
      simpa [bB] using congrArg Subtype.val (hB_exponent_two bB)
  have hD_le_Phi : D ≤ Phi := by
    simpa [D, Phi] using
      (commutator_le_frattini_of_isPGroup (R := P) (p := 2))
  have hB_le_Phi : B ≤ Phi := hB_le_D.trans hD_le_Phi
  have hPhi_eq_B : Phi = B := by
    rcases hmiddle.2.2.2.2.2 Phi hPhi_normal hPhi_X
        hB_le_Phi hPhi_le_A with hPhi_B | hPhi_A
    · exact hPhi_B
    · let : A.Normal := hmiddle.2.1
      let : Fact (IsPGroup 2 A) :=
        ⟨(isPGroup_of_isSuzukiTwoGroup _hP).to_subgroup A⟩
      have hA_abelian : IsMulCommutative A := by
        rw [← hPhi_A]
        exact hPhi_abelian
      have hA_le_M : A ≤ M := by
        rw [← hPhi_A]
        exact hPhi_le_M
      have hfrattini :
          A = (frattini (⊤ : Subgroup P)).map
            (⊤ : Subgroup P).subtype :=
        hPhi_A.symm.trans hPhiTop_eq_Phi.symm
      have hcomm_map_eq_D :
          (commutator (⊤ : Subgroup P)).map
              (⊤ : Subgroup P).subtype = D := by
        simpa [D, commutator_def] using
          (Subgroup.map_subtype_commutator (⊤ : Subgroup P))
      have hD_le_A : D ≤ A := hD_le_Phi.trans (le_of_eq hPhi_A)
      have hA_exponent_two : ∀ x : A, x ^ 2 = 1 := by
        rcases hmiddle.2.2.2.2.2 D hD_normal hD_X
            hB_le_D hD_le_A with hD_B | hD_A
        · by_contra hA_two
          push Not at hA_two
          let PhiA : Subgroup P := (frattini A).map A.subtype
          have hPhiA_eq_squares :
              PhiA = Subgroup.closure
                {x : P | ∃ a : A, (a : P) ^ 2 = x} := by
            let : IsMulCommutative A := hA_abelian
            let : CommGroup A := IsMulCommutative.instCommGroup
            let Asq : Subgroup A := (powMonoidHom 2 : A →* A).range
            have hPhi_internal : frattini A = Asq := by
              have hcomm : commutator A = ⊥ := by
                rw [commutator_eq_bot_iff_center_eq_top]
                apply eq_top_iff.mpr
                intro x _hx
                exact Subgroup.mem_center_iff.mpr
                  (fun y => ((IsMulCommutative.is_comm (M := A)).comm x y).symm)
              rw [frattini_eq_closure_commutator_union_powers
                (R := A) (p := 2)]
              apply le_antisymm
              · rw [Subgroup.closure_le]
                intro x hx
                rcases hx with hxcomm | hxpow
                · have hxbot : x ∈ (⊥ : Subgroup A) := by
                    simpa [hcomm] using hxcomm
                  have hx1 : x = 1 := by simpa using hxbot
                  subst x
                  exact ⟨1, by simp⟩
                · simpa [Asq, powMonoidHom] using hxpow
              · intro x hx
                exact Subgroup.subset_closure
                  (Or.inr (by simpa [Asq, powMonoidHom] using hx))
            change (frattini A).map A.subtype = _
            rw [hPhi_internal]
            apply le_antisymm
            · rintro x hx
              rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
              rcases MonoidHom.mem_range.mp hy with ⟨a, rfl⟩
              exact Subgroup.subset_closure ⟨a, by simp [powMonoidHom]⟩
            · rw [Subgroup.closure_le]
              rintro x ⟨a, rfl⟩
              exact Subgroup.mem_map.mpr
                ⟨a ^ 2, MonoidHom.mem_range.mpr
                  ⟨a, by simp [powMonoidHom]⟩, rfl⟩
          have hPhiA_normal : PhiA.Normal := by
            constructor
            intro z hz p
            rcases hz with ⟨a, ha, rfl⟩
            let ap : A := MulAut.conjNormal (H := A) p a
            have hap : ap ∈ frattini A :=
              (Subgroup.characteristic_iff_le_comap.mp
                (frattini_characteristic (G := A))
                (MulAut.conjNormal (H := A) p)) ha
            refine ⟨ap, hap, ?_⟩
            simp [ap, MulAut.conjNormal_apply]
          have hPhiA_X : IsXInvariantSubgroup X PhiA := by
            let : IsInvariant X P A := ⟨hmiddle.2.2.2.1⟩
            have hforward : ∀ x : X, ∀ p : P,
                p ∈ PhiA → x • p ∈ PhiA := by
              intro x p hp
              rcases hp with ⟨a, ha, rfl⟩
              refine ⟨x • a, ?_, rfl⟩
              exact
                (Subgroup.characteristic_iff_le_comap.mp
                  (frattini_characteristic (G := A))
                  (MulDistribMulAction.toMulAut X A x)) ha
            intro x p
            constructor
            · exact hforward x p
            · intro hp
              have hpinv := hforward x⁻¹ (x • p) hp
              simpa [smul_smul] using hpinv
          have hPhiA_le_B : PhiA ≤ B := by
            rw [hPhiA_eq_squares, Subgroup.closure_le]
            rintro _ ⟨a, rfl⟩
            have ha4 : (a : P) ^ 4 = 1 := by
              let aM : M := ⟨a, hA_le_M a.property⟩
              simpa [aM] using congrArg Subtype.val (hM_data.1 aM)
            by_cases ha2 : (a : P) ^ 2 = 1
            · rw [ha2]
              exact B.one_mem
            · apply lemma1_involutions_mem_of_nontrivial_invariant
                _hP _hXtrans hmiddle.2.2.2.2.1 (ne_of_gt hlower.1)
              exact ⟨ha2, by
                calc
                  ((a : P) ^ 2) ^ 2 = (a : P) ^ 4 := by group
                  _ = 1 := ha4⟩
          have hPhiA_ne : PhiA ≠ ⊥ := by
            obtain ⟨a, ha⟩ := hA_two
            intro hPhiA_bot
            have ha_mem : (a : P) ^ 2 ∈ PhiA := by
              rw [hPhiA_eq_squares]
              exact Subgroup.subset_closure ⟨a, rfl⟩
            rw [hPhiA_bot] at ha_mem
            apply ha
            apply Subtype.ext
            simpa using ha_mem
          have hPhiA_eq_B : PhiA = B := by
            rcases hlower.2.2.2.2.2 PhiA hPhiA_normal hPhiA_X
                bot_le hPhiA_le_B with hbot | hB
            · exact False.elim (hPhiA_ne hbot)
            · exact hB
          have htop_abelian : IsMulCommutative (⊤ : Subgroup P) :=
            lemma7_cover_commutator_case_abelian
              _hP _hXcyclic _hXfaithful _hXtrans
                hmiddle.2.1 hA_abelian hmiddle.2.2.2.1
                hupper.2.1 hupper.2.2.2.1 hupper.1
                (by
                  intro C hC_normal hC_X hAC hCtop
                  rcases hupper.2.2.2.2.2 C hC_normal hC_X
                      hAC.le hCtop.le with hC_A | hC_top
                  · exact hAC.ne hC_A.symm
                  · exact hCtop.ne hC_top)
                hfrattini (by
                  rw [hcomm_map_eq_D, hD_B, ← hPhiA_eq_B,
                    hPhiA_eq_squares])
          apply _hP.2.1
          refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
          let xt : (⊤ : Subgroup P) := ⟨x, trivial⟩
          let yt : (⊤ : Subgroup P) := ⟨y, trivial⟩
          exact congrArg Subtype.val
            ((@IsMulCommutative.is_comm _ _ htop_abelian).comm xt yt)
        · exact lemma8_cover_commutator_case_exponent_two
            _hP _hXcyclic _hXfaithful _hXtrans
              hmiddle.2.1 hA_abelian hmiddle.2.2.2.1
              hupper.2.1 hupper.2.2.2.1 hupper.1
              (by
                intro C hC_normal hC_X hAC hCtop
                rcases hupper.2.2.2.2.2 C hC_normal hC_X
                    hAC.le hCtop.le with hC_A | hC_top
                · exact hAC.ne hC_A.symm
                · exact hCtop.ne hC_top)
              (hcomm_map_eq_D.trans hD_A)
      have hA_le_B : A ≤ B := by
        have hall := lemma1_involutions_mem_of_nontrivial_invariant
          _hP _hXtrans hmiddle.2.2.2.2.1 (ne_of_gt hlower.1)
        intro a ha
        by_cases ha_one : a = 1
        · subst a
          exact B.one_mem
        · apply hall a
          refine ⟨ha_one, ?_⟩
          let aA : A := ⟨a, ha⟩
          simpa [aA] using congrArg Subtype.val (hA_exponent_two aA)
      exact False.elim (hmiddle.1.2 hA_le_B)
  have hD_eq_B : D = B := by
    apply le_antisymm
    · rw [← hPhi_eq_B]
      exact hD_le_Phi
    · exact hB_le_D
  have hcommutator_eq_B : commutator P = B := by
    simpa [D] using hD_eq_B
  have hL1_eq_B : (⊤ : Subgroup P).lowerCentralSeries 1 = B := by
    rw [Subgroup.top_lowerCentralSeries_one]
    exact hcommutator_eq_B
  have hclass_two : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥ := by
    have hL2_normal : ((⊤ : Subgroup P).lowerCentralSeries 2).Normal := by infer_instance
    have hL2_X : IsXInvariantSubgroup X ((⊤ : Subgroup P).lowerCentralSeries 2) :=
      (isInvariant_of_characteristic (A := X) (G := P)
        ((⊤ : Subgroup P).lowerCentralSeries 2)).invariant
    have hL2_le_B : (⊤ : Subgroup P).lowerCentralSeries 2 ≤ B := by
      calc
        (⊤ : Subgroup P).lowerCentralSeries 2 ≤ (⊤ : Subgroup P).lowerCentralSeries 1 :=
          (⊤ : Subgroup P).lowerCentralSeries_antitone (by omega)
        _ = B := hL1_eq_B
    rcases hlower.2.2.2.2.2 ((⊤ : Subgroup P).lowerCentralSeries 2) hL2_normal hL2_X
        bot_le hL2_le_B with hbot | hB
    · exact hbot
    · exfalso
      have hstable : ∀ n : ℕ, 1 ≤ n → (⊤ : Subgroup P).lowerCentralSeries n = B := by
        intro n hn
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
        induction k with
        | zero => simpa using hL1_eq_B
        | succ k ih =>
            change ⁅(⊤ : Subgroup P).lowerCentralSeries (1 + k), (⊤ : Subgroup P)⁆ = B
            rw [ih (by omega)]
            calc
              ⁅B, (⊤ : Subgroup P)⁆ =
                  ⁅(⊤ : Subgroup P).lowerCentralSeries 1, (⊤ : Subgroup P)⁆ := by
                    rw [hL1_eq_B]
              _ = (⊤ : Subgroup P).lowerCentralSeries 2 := rfl
              _ = B := hB
      let c := Group.nilpotencyClass P
      have hc_pos : 0 < c := by
        apply Nat.pos_of_ne_zero
        intro hc
        have hsub : Subsingleton P :=
          (Group.nilpotencyClass_zero_iff_subsingleton (G := P)).mp hc
        rcases _hP.2.2.1 with ⟨x, y, _hx, _hy, hxy⟩
        exact hxy (hsub.elim x y)
      have hcB : (⊤ : Subgroup P).lowerCentralSeries c = B := hstable c (by omega)
      have hcbot : (⊤ : Subgroup P).lowerCentralSeries c = ⊥ := by
        dsimp [c]
        exact Subgroup.lowerCentralSeries_nilpotencyClass
      exact hlower.1.ne (hcB.symm.trans hcbot).symm
  have hB_le_center : B ≤ Subgroup.center P := by
    rw [← hcommutator_eq_B]
    have hclass := hclass_two
    rw [show 2 = 1 + 1 by omega, Subgroup.lowerCentralSeries_succ,
      Subgroup.top_lowerCentralSeries_one] at hclass
    change ⁅commutator P, (⊤ : Subgroup P)⁆ = ⊥ at hclass
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hclass
    simpa [← Subgroup.centralizer_univ, ← Subgroup.coe_top] using hclass
  have hsquares_le_B : squaresSubgroup P ≤ B := by
    rw [squaresSubgroup, Subgroup.closure_le]
    rintro _ ⟨y, rfl⟩
    rw [← hPhi_eq_B]
    exact pth_power_mem_frattini_of_isPGroup (R := P) (p := 2) y
  have hkernel1_bot : lowerCentralFactorKernel P 1 = ⊥ := by
    apply le_antisymm
    · rw [lowerCentralFactorKernel]
      apply sup_le
      · rw [squaresSubgroup, Subgroup.closure_le]
        rintro _ ⟨x, rfl⟩
        change x ^ 2 = 1
        apply Subtype.ext
        change (x : P) ^ 2 = 1
        let b : B := ⟨x, hL1_eq_B ▸ x.property⟩
        simpa [b] using congrArg Subtype.val (hB_exponent_two b)
      · intro x hx
        change (x : P) ∈ (⊤ : Subgroup P).lowerCentralSeries 2 at hx
        rw [hclass_two] at hx
        simpa using hx
    · exact bot_le
  have hkernel0_map_B :
      (lowerCentralFactorKernel P 0).map
          ((⊤ : Subgroup P).lowerCentralSeries 0).subtype = B := by
    have hsquares_map :
        (squaresSubgroup ((⊤ : Subgroup P).lowerCentralSeries 0)).map
            ((⊤ : Subgroup P).lowerCentralSeries 0).subtype = squaresSubgroup P := by
      apply le_antisymm
      · rw [squaresSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
        exact Subgroup.subset_closure ⟨(y : P), rfl⟩
      · rw [squaresSubgroup, Subgroup.closure_le]
        rintro _ ⟨y, rfl⟩
        let yt : (⊤ : Subgroup P).lowerCentralSeries 0 := ⟨y, trivial⟩
        exact ⟨yt ^ 2, Subgroup.subset_closure ⟨yt, rfl⟩, rfl⟩
    have hnext_map :
        (((⊤ : Subgroup P).lowerCentralSeries 1).subgroupOf
            ((⊤ : Subgroup P).lowerCentralSeries 0)).map
              ((⊤ : Subgroup P).lowerCentralSeries 0).subtype = (⊤ : Subgroup P).lowerCentralSeries 1 :=
      Subgroup.map_subgroupOf_eq_of_le
        ((⊤ : Subgroup P).lowerCentralSeries_antitone (by omega : 0 ≤ 1))
    rw [lowerCentralFactorKernel, Subgroup.map_sup, hsquares_map, hnext_map,
      hL1_eq_B]
    exact sup_eq_right.mpr (by simpa [hL1_eq_B] using hsquares_le_B)
  have hfactor1_card :
      ∃ n : ℕ, 2 ≤ n ∧ Nat.card (LowerCentralFactor P 1) = 2 ^ n := by
    let n := Module.finrank (ZMod 2) (Additive (LowerCentralFactor P 1))
    have hcard : Nat.card (LowerCentralFactor P 1) = 2 ^ n := by
      have h := Module.natCard_eq_pow_finrank
        (K := ZMod 2) (V := Additive (LowerCentralFactor P 1))
      exact (Nat.card_congr Additive.toMul).symm.trans (by simpa [n] using h)
    have hfactor_card_eq_B :
        Nat.card (LowerCentralFactor P 1) = Nat.card B := by
      change Nat.card
          (((⊤ : Subgroup P).lowerCentralSeries 1) ⧸ lowerCentralFactorKernel P 1) =
        Nat.card B
      rw [hkernel1_bot]
      calc
        Nat.card (((⊤ : Subgroup P).lowerCentralSeries 1) ⧸
              (⊥ : Subgroup ((⊤ : Subgroup P).lowerCentralSeries 1))) =
            Nat.card ((⊤ : Subgroup P).lowerCentralSeries 1) := by
              exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
        _ = Nat.card B := Nat.card_congr
          (Set.equivOfEq (congrArg (fun S : Subgroup P => (S : Set P))
            hL1_eq_B))
    rcases _hP.2.2.1 with ⟨x, y, hx, hy, hxy⟩
    have hxB : x ∈ B :=
      lemma1_involutions_mem_of_nontrivial_invariant
        _hP _hXtrans hlower.2.2.2.1 (ne_of_gt hlower.1) x hx
    have hyB : y ∈ B :=
      lemma1_involutions_mem_of_nontrivial_invariant
        _hP _hXtrans hlower.2.2.2.1 (ne_of_gt hlower.1) y hy
    let oneB : B := ⟨1, B.one_mem⟩
    let xB : B := ⟨x, hxB⟩
    let yB : B := ⟨y, hyB⟩
    have hx_ne : oneB ≠ xB := by
      intro h
      exact hx.ne_one (congrArg Subtype.val h).symm
    have hy_ne : oneB ≠ yB := by
      intro h
      exact hy.ne_one (congrArg Subtype.val h).symm
    have hxy_ne : xB ≠ yB := by
      intro h
      exact hxy (congrArg Subtype.val h)
    let : Fintype B := Fintype.ofFinite B
    have hthree : ({oneB, xB, yB} : Finset B).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hx_ne, hy_ne])]
      rw [Finset.card_insert_of_notMem (by simp [hxy_ne])]
      simp
    have hle : 3 ≤ Nat.card (LowerCentralFactor P 1) := by
      rw [hfactor_card_eq_B, Nat.card_eq_fintype_card, ← hthree]
      exact Finset.card_le_card (Finset.subset_univ _)
    refine ⟨n, ?_, hcard⟩
    by_contra hn
    have hnle : n ≤ 1 := by omega
    rw [hcard] at hle
    interval_cases n <;> norm_num at hle
  let : FaithfulSMul X P := _hXfaithful
  let : Finite X := Finite.of_injective
    (MulDistribMulAction.toMulAut X P) (by
      intro x y hxy
      apply FaithfulSMul.eq_of_smul_eq_smul (α := P)
      intro p
      exact congrArg (fun f : MulAut P => f p) hxy)
  let : IsCyclic X := _hXcyclic
  let tau : MulAut P := MulDistribMulAction.toMulAut X P g
  obtain ⟨k, m, hm_odd, htau_order⟩ :=
    Nat.exists_eq_two_pow_mul_odd (orderOf_pos tau).ne'
  let xi : MulAut P := tau ^ (2 ^ k)
  have hxi_odd : Odd (orderOf xi) := by
    have hk_dvd : 2 ^ k ∣ orderOf tau := by
      rw [htau_order]
      exact dvd_mul_right (2 ^ k) m
    have horder : orderOf (tau ^ (2 ^ k)) = m := by
      rw [orderOf_pow_of_dvd (by positivity : 2 ^ k ≠ 0) hk_dvd,
        htau_order]
      exact Nat.mul_div_cancel_left m (by positivity)
    change Odd (orderOf (tau ^ (2 ^ k)))
    rw [horder]
    exact hm_odd
  have htau_transitive :
      ∀ x : Additive (LowerCentralFactor P 1), x ≠ 0 →
        ∀ y : Additive (LowerCentralFactor P 1), y ≠ 0 →
          ∃ j : ℕ, (lowerCentralFactorLinearAut tau 1 ^ j) x = y := by
    intro x hx y hy
    obtain ⟨a, ha⟩ :=
      QuotientGroup.mk'_surjective (lowerCentralFactorKernel P 1) x.toMul
    obtain ⟨b, hb⟩ :=
      QuotientGroup.mk'_surjective (lowerCentralFactorKernel P 1) y.toMul
    have ha_ne : (a : P) ≠ 1 := by
      intro ha1
      apply hx
      apply Additive.toMul.injective
      change x.toMul = 1
      rw [← ha]
      have ha_one : a = 1 := Subtype.ext ha1
      rw [ha_one]
      exact map_one _
    have hb_ne : (b : P) ≠ 1 := by
      intro hb1
      apply hy
      apply Additive.toMul.injective
      change y.toMul = 1
      rw [← hb]
      have hb_one : b = 1 := Subtype.ext hb1
      rw [hb_one]
      exact map_one _
    let aB : B := ⟨a, hL1_eq_B ▸ a.property⟩
    let bB : B := ⟨b, hL1_eq_B ▸ b.property⟩
    have ha_sq : (a : P) ^ 2 = 1 := by
      simpa [aB] using congrArg Subtype.val (hB_exponent_two aB)
    have hb_sq : (b : P) ^ 2 = 1 := by
      simpa [bB] using congrArg Subtype.val (hB_exponent_two bB)
    obtain ⟨z, hz⟩ :=
      _hXtrans (a : P) ⟨ha_ne, ha_sq⟩ (b : P) ⟨hb_ne, hb_sq⟩
    obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hg z)
    refine ⟨j, ?_⟩
    have hx_repr : x = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel P 1) a) := by
      apply Additive.toMul.injective
      exact ha.symm
    have hy_repr : y = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel P 1) b) := by
      apply Additive.toMul.injective
      exact hb.symm
    rw [← lowerCentralFactorLinearAut_pow, hx_repr, hy_repr,
      lowerCentralFactorLinearAut_ofMul_mk]
    apply Additive.toMul.injective
    apply congrArg (QuotientGroup.mk' (lowerCentralFactorKernel P 1))
    apply Subtype.ext
    change (tau ^ j) (a : P) = (b : P)
    have hpow_aut :
        tau ^ j = MulDistribMulAction.toMulAut X P (g ^ j) := by
      change (MulDistribMulAction.toMulAut X P g) ^ j =
        MulDistribMulAction.toMulAut X P (g ^ j)
      exact (map_pow (MulDistribMulAction.toMulAut X P) g j).symm
    rw [hpow_aut]
    exact hz.symm
  have hxi_transitive :
      ∀ x : Additive (LowerCentralFactor P 1), x ≠ 0 →
        ∀ y : Additive (LowerCentralFactor P 1), y ≠ 0 →
          ∃ j : ℕ, (lowerCentralFactorLinearAut xi 1 ^ j) x = y := by
    let Ttau := lowerCentralFactorLinearAut tau 1
    let Txi := lowerCentralFactorLinearAut xi 1
    have hTxi_pow : Txi = Ttau ^ (2 ^ k) := by
      simpa [Ttau, Txi, xi] using
        (lowerCentralFactorLinearAut_pow tau 1 (2 ^ k))
    obtain ⟨n, hn, hcard⟩ := hfactor1_card
    have horder : orderOf Ttau = 2 ^ n - 1 :=
      lemma4_transitive_linearAut_order Ttau
        (by simpa [Ttau] using htau_transitive) n hn hcard
    have hodd : Odd (orderOf Ttau) := by
      rw [horder]
      obtain ⟨d, hd⟩ :=
        Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      subst n
      refine ⟨2 ^ d - 1, ?_⟩
      rw [pow_succ]
      have hpow_pos : 0 < 2 ^ d := by positivity
      omega
    have hcoprime : Nat.Coprime (2 ^ k) (orderOf Ttau) :=
      Nat.Coprime.pow_left k hodd.coprime_two_left
    obtain ⟨u, hu⟩ :=
      exists_pow_eq_self_of_coprime (x := Ttau) hcoprime
    have hrecover : Ttau = Txi ^ u := by
      simpa [hTxi_pow] using hu.symm
    intro x hx y hy
    obtain ⟨j, hj⟩ := htau_transitive x hx y hy
    refine ⟨u * j, ?_⟩
    simpa [Ttau, Txi, pow_mul, ← hrecover] using hj
  obtain ⟨n, hn, hfactor1_card_n⟩ := hfactor1_card
  let S := lowerCentralFactorLinearAut xi 1
  have hS_order : orderOf S = 2 ^ n - 1 :=
    lemma4_transitive_linearAut_order S
      (by simpa [S] using hxi_transitive) n hn hfactor1_card_n
  let q0 : P →* LowerCentralFactor P 0 :=
    (QuotientGroup.mk' (lowerCentralFactorKernel P 0)).comp
      Subgroup.topEquiv.symm.toMonoidHom
  have hq0_ker : q0.ker = B := by
    ext p
    change QuotientGroup.mk' (lowerCentralFactorKernel P 0)
        (Subgroup.topEquiv.symm p) = 1 ↔ p ∈ B
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← hkernel0_map_B]
    constructor
    · intro hp
      exact ⟨Subgroup.topEquiv.symm p, hp, rfl⟩
    · rintro ⟨z, hz, hzp⟩
      have hz_eq : z = Subgroup.topEquiv.symm p := by
        apply Subtype.ext
        exact hzp
      exact hz_eq ▸ hz
  have hq0_surj : Function.Surjective q0 := by
    intro v
    obtain ⟨z, rfl⟩ :=
      QuotientGroup.mk'_surjective (lowerCentralFactorKernel P 0) v
    refine ⟨Subgroup.topEquiv z, ?_⟩
    exact congrArg (QuotientGroup.mk' (lowerCentralFactorKernel P 0))
      (Subgroup.topEquiv.symm_apply_apply z)
  have hq0_equivariant (x : X) (p : P) :
      Additive.ofMul (q0 (x • p)) =
        lowerCentralFactorLinearAut
          (MulDistribMulAction.toMulAut X P x) 0
          (Additive.ofMul (q0 p)) := by
    change
      Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel P 0)
            (Subgroup.topEquiv.symm (x • p))) =
        lowerCentralFactorLinearAut
          (MulDistribMulAction.toMulAut X P x) 0
          (Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel P 0)
              (Subgroup.topEquiv.symm p)))
    rw [lowerCentralFactorLinearAut_ofMul_mk]
    apply Additive.toMul.injective
    apply congrArg (QuotientGroup.mk' (lowerCentralFactorKernel P 0))
    apply Subtype.ext
    rfl
  let Ugroup : Subgroup (LowerCentralFactor P 0) := A.map q0
  let U : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)) :=
    (Subgroup.toAddSubgroup.trans
      (AddSubgroup.toZModSubmodule (n := 2))) Ugroup
  have hUgroup_ne_bot : Ugroup ≠ ⊥ := by
    intro hU_bot
    have hA_le_B : A ≤ B := by
      intro a ha
      have hqa : q0 a ∈ Ugroup := ⟨a, ha, rfl⟩
      rw [hU_bot] at hqa
      have hq_one : q0 a = 1 := by simpa using hqa
      rw [← hq0_ker]
      exact hq_one
    exact hmiddle.1.2 hA_le_B
  have hUgroup_ne_top : Ugroup ≠ ⊤ := by
    intro hU_top
    have hP_le_A : (⊤ : Subgroup P) ≤ A := by
      intro p _hp
      have hqp : q0 p ∈ Ugroup := by
        rw [hU_top]
        trivial
      rcases hqp with ⟨a, ha, hap⟩
      have hdiff : a⁻¹ * p ∈ q0.ker := by
        change q0 (a⁻¹ * p) = 1
        rw [map_mul, map_inv, hap]
        simp
      rw [hq0_ker] at hdiff
      have hdiffA : a⁻¹ * p ∈ A := hmiddle.1.le hdiff
      have hp_eq : p = a * (a⁻¹ * p) := by group
      rw [hp_eq]
      exact A.mul_mem ha hdiffA
    exact hupper.1.2 hP_le_A
  have htau_actor :
      tau = MulDistribMulAction.toMulAut X P g := rfl
  have hxi_actor :
      xi = MulDistribMulAction.toMulAut X P (g ^ (2 ^ k)) := by
    change (MulDistribMulAction.toMulAut X P g) ^ (2 ^ k) =
      MulDistribMulAction.toMulAut X P (g ^ (2 ^ k))
    exact (map_pow (MulDistribMulAction.toMulAut X P) g (2 ^ k)).symm
  have hU_tau : ∀ v : Additive (LowerCentralFactor P 0),
      v ∈ U → lowerCentralFactorLinearAut tau 0 v ∈ U := by
    intro v hv
    change v.toMul ∈ Ugroup at hv
    change (lowerCentralFactorLinearAut tau 0 v).toMul ∈ Ugroup
    rcases hv with ⟨a, ha, hav⟩
    rw [lowerCentralFactorLinearAut_toMul, ← hav]
    refine ⟨tau a, ?_, ?_⟩
    · rw [htau_actor]
      exact (hmiddle.2.2.2.1 g a).mp ha
    · change lowerCentralFactorMulAut tau 0
          (QuotientGroup.mk' (lowerCentralFactorKernel P 0)
            (Subgroup.topEquiv.symm a)) =
        QuotientGroup.mk' (lowerCentralFactorKernel P 0)
          (Subgroup.topEquiv.symm (tau a))
      rw [lowerCentralFactorMulAut_mk]
      apply congrArg (QuotientGroup.mk' (lowerCentralFactorKernel P 0))
      apply Subtype.ext
      rfl
  let pull :
      Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)) → Subgroup P :=
    fun W =>
      (AddSubgroup.toSubgroup' W.toAddSubgroup).comap q0
  have hpull_mono : Monotone pull := by
    intro W₁ W₂ hW p hp
    change Additive.ofMul (q0 p) ∈ W₂
    apply hW
    change Additive.ofMul (q0 p) ∈ W₁ at hp
    exact hp
  have hpull_injective : Function.Injective pull := by
    intro W₁ W₂ hpull
    ext v
    obtain ⟨p, hp⟩ := hq0_surj v.toMul
    have hmem : p ∈ pull W₁ ↔ p ∈ pull W₂ := by rw [hpull]
    change Additive.ofMul (q0 p) ∈ W₁ ↔
      Additive.ofMul (q0 p) ∈ W₂ at hmem
    simpa [hp] using hmem
  have hpull_bot : pull ⊥ = B := by
    ext p
    change Additive.ofMul (q0 p) ∈
      (⊥ : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0))) ↔ p ∈ B
    rw [← hq0_ker]
    simp
  have hpull_top : pull ⊤ = ⊤ := by
    ext p
    simp [pull]
  have hpull_U : pull U = A := by
    ext p
    change q0 p ∈ Ugroup ↔ p ∈ A
    constructor
    · rintro ⟨a, ha, hap⟩
      have hdiff : a⁻¹ * p ∈ q0.ker := by
        change q0 (a⁻¹ * p) = 1
        rw [map_mul, map_inv, hap]
        simp
      rw [hq0_ker] at hdiff
      have hdiffA : a⁻¹ * p ∈ A := hmiddle.1.le hdiff
      have hp_eq : p = a * (a⁻¹ * p) := by group
      rw [hp_eq]
      exact A.mul_mem ha hdiffA
    · intro hp
      exact ⟨p, hp, rfl⟩
  have hpull_data :
      ∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)),
        (∀ v : Additive (LowerCentralFactor P 0), v ∈ W →
          lowerCentralFactorLinearAut tau 0 v ∈ W) →
        (pull W).Normal ∧ IsXInvariantSubgroup X (pull W) ∧ B ≤ pull W := by
    intro W hW
    have hB_le : B ≤ pull W := by
      rw [← hpull_bot]
      exact hpull_mono bot_le
    have hnormal : (pull W).Normal := by
      constructor
      intro c hc p
      have hcommC : ⁅p, c⁆ ∈ pull W :=
        hB_le (by
          rw [← hcommutator_eq_B]
          exact Subgroup.commutator_mem_commutator
            (show p ∈ (⊤ : Subgroup P) from trivial)
            (show c ∈ (⊤ : Subgroup P) from trivial))
      have hprod := (pull W).mul_mem hcommC hc
      simpa [commutatorElement_def] using hprod
    have hWpow : ∀ j : ℕ,
        ∀ v : Additive (LowerCentralFactor P 0), v ∈ W →
          (lowerCentralFactorLinearAut tau 0 ^ j) v ∈ W := by
      intro j v hv
      induction j with
      | zero => simpa using hv
      | succ j ih =>
          rw [pow_succ', LinearEquiv.mul_apply]
          exact hW _ ih
    have hforward : ∀ x : X, ∀ p : P, p ∈ pull W → x • p ∈ pull W := by
      intro x p hp
      obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hg x)
      change Additive.ofMul (q0 (g ^ j • p)) ∈ W
      change Additive.ofMul (q0 p) ∈ W at hp
      rw [hq0_equivariant]
      have hactW :
          lowerCentralFactorLinearAut
              (MulDistribMulAction.toMulAut X P (g ^ j)) 0
              (Additive.ofMul (q0 p)) ∈ W := by
        rw [map_pow, lowerCentralFactorLinearAut_pow]
        simpa [tau] using hWpow j _ hp
      exact hactW
    have hinvariant : IsXInvariantSubgroup X (pull W) := by
      intro x p
      constructor
      · exact hforward x p
      · intro hp
        have hpinv := hforward x⁻¹ (x • p) hp
        simpa [smul_smul] using hpinv
    exact ⟨hnormal, hinvariant, hB_le⟩
  have htau_lower_composition_irreducible :
      ∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)),
        W ≤ U →
        (∀ v : Additive (LowerCentralFactor P 0), v ∈ W →
          lowerCentralFactorLinearAut tau 0 v ∈ W) →
        W = ⊥ ∨ W = U := by
    intro W hWU hW
    obtain ⟨hWnormal, hWX, hB_le_W⟩ := hpull_data W hW
    rcases hmiddle.2.2.2.2.2 (pull W) hWnormal hWX hB_le_W
        (by rw [← hpull_U]; exact hpull_mono hWU) with hWB | hWA
    · left
      apply hpull_injective
      rw [hWB, hpull_bot]
    · right
      apply hpull_injective
      rw [hWA, hpull_U]
  have htau_upper_composition_irreducible :
      ∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)),
        U ≤ W →
        (∀ v : Additive (LowerCentralFactor P 0), v ∈ W →
          lowerCentralFactorLinearAut tau 0 v ∈ W) →
        W = U ∨ W = ⊤ := by
    intro W hUW hW
    obtain ⟨hWnormal, hWX, _hB_le_W⟩ := hpull_data W hW
    rcases hupper.2.2.2.2.2 (pull W) hWnormal hWX
        (by rw [← hpull_U]; exact hpull_mono hUW) le_top with hWA | hWtop
    · left
      apply hpull_injective
      rw [hWA, hpull_U]
    · right
      apply hpull_injective
      rw [hWtop, hpull_top]
  let tauUMap : U →ₗ[ZMod 2] U :=
    { toFun := fun v => ⟨lowerCentralFactorLinearAut tau 0 v,
        hU_tau v v.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change lowerCentralFactorLinearAut tau 0
            ((x : Additive (LowerCentralFactor P 0)) + y) = _
        exact (lowerCentralFactorLinearAut tau 0).map_add
          (x : Additive (LowerCentralFactor P 0)) y
      map_smul' := by
        intro c x
        apply Subtype.ext
        change lowerCentralFactorLinearAut tau 0
            (c • (x : Additive (LowerCentralFactor P 0))) = _
        exact (lowerCentralFactorLinearAut tau 0).map_smul c
          (x : Additive (LowerCentralFactor P 0)) }
  have htauUMap_injective : Function.Injective tauUMap := by
    intro x y hxy
    apply Subtype.ext
    apply (lowerCentralFactorLinearAut tau 0).injective
    exact congrArg Subtype.val hxy
  let tauU : U ≃ₗ[ZMod 2] U :=
    LinearEquiv.ofBijective tauUMap
      ⟨htauUMap_injective,
        Finite.injective_iff_surjective.mp htauUMap_injective⟩
  have htauU_irreducible :
      ∀ W : Submodule (ZMod 2) U,
        (∀ v : U, v ∈ W → tauU v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let Wambient : Submodule (ZMod 2)
        (Additive (LowerCentralFactor P 0)) := W.map U.subtype
    have hWambient_le : Wambient ≤ U := by
      rintro _ ⟨w, _hw, rfl⟩
      exact w.property
    have hWambient_tau :
        ∀ v : Additive (LowerCentralFactor P 0), v ∈ Wambient →
          lowerCentralFactorLinearAut tau 0 v ∈ Wambient := by
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨tauU w, hW w hw, rfl⟩
    rcases htau_lower_composition_irreducible Wambient hWambient_le
        hWambient_tau with hbot | htop
    · left
      apply Submodule.map_injective_of_injective U.subtype_injective
      simpa [Wambient] using hbot
    · right
      apply Submodule.map_injective_of_injective U.subtype_injective
      simpa [Wambient] using htop
  let xiU : U ≃ₗ[ZMod 2] U := tauU ^ (2 ^ k)
  have hxiU_irreducible :
      ∀ W : Submodule (ZMod 2) U,
        (∀ v : U, v ∈ W → xiU v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    exact lemma12_irreducible_pow_two_of_irreducible
      tauU k htauU_irreducible
  have htauU_pow_val : ∀ j : ℕ, ∀ u : U,
      (((tauU ^ j) u : U) : Additive (LowerCentralFactor P 0)) =
        (lowerCentralFactorLinearAut tau 0 ^ j)
          (u : Additive (LowerCentralFactor P 0)) := by
    intro j u
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [show tauU ^ (j + 1) = tauU * tauU ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply]
        change lowerCentralFactorLinearAut tau 0
            ((((tauU ^ j) u : U) : Additive (LowerCentralFactor P 0))) =
          (lowerCentralFactorLinearAut tau 0 ^ (j + 1)) u
        rw [ih]
        rw [show lowerCentralFactorLinearAut tau 0 ^ (j + 1) =
            lowerCentralFactorLinearAut tau 0 *
              lowerCentralFactorLinearAut tau 0 ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply]
  have hxiU_val (u : U) :
      ((xiU u : U) : Additive (LowerCentralFactor P 0)) =
        lowerCentralFactorLinearAut xi 0
          (u : Additive (LowerCentralFactor P 0)) := by
    rw [show lowerCentralFactorLinearAut xi 0 =
        (lowerCentralFactorLinearAut tau 0) ^ (2 ^ k) by
      simpa [xi] using lowerCentralFactorLinearAut_pow tau 0 (2 ^ k)]
    exact htauU_pow_val (2 ^ k) u
  let tauQMap :
      (Additive (LowerCentralFactor P 0) ⧸ U) →ₗ[ZMod 2]
        (Additive (LowerCentralFactor P 0) ⧸ U) :=
    Submodule.mapQ U U (lowerCentralFactorLinearAut tau 0).toLinearMap
      (by
        intro u hu
        exact hU_tau u hu)
  let : Finite (Additive (LowerCentralFactor P 0) ⧸ U) :=
    Finite.of_surjective U.mkQ U.mkQ_surjective
  have htauQMap_surjective : Function.Surjective tauQMap := by
    intro z
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective U z
    refine ⟨Submodule.Quotient.mk
      ((lowerCentralFactorLinearAut tau 0).symm v), ?_⟩
    rw [show tauQMap = Submodule.mapQ U U
        (lowerCentralFactorLinearAut tau 0).toLinearMap _ from rfl,
      Submodule.mapQ_apply]
    simp
  have htauQMap_injective : Function.Injective tauQMap :=
    Finite.injective_iff_surjective.mpr htauQMap_surjective
  let tauQ :
      (Additive (LowerCentralFactor P 0) ⧸ U) ≃ₗ[ZMod 2]
        (Additive (LowerCentralFactor P 0) ⧸ U) :=
    LinearEquiv.ofBijective tauQMap
      ⟨htauQMap_injective, htauQMap_surjective⟩
  have htauQ_irreducible :
      ∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0) ⧸ U),
        (∀ v : Additive (LowerCentralFactor P 0) ⧸ U,
          v ∈ W → tauQ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let Wambient : Submodule (ZMod 2)
        (Additive (LowerCentralFactor P 0)) := W.comap U.mkQ
    have hU_le_Wambient : U ≤ Wambient := by
      intro u hu
      change U.mkQ u ∈ W
      have hu0 : U.mkQ u = 0 := by
        apply LinearMap.mem_ker.mp
        rw [Submodule.ker_mkQ]
        exact hu
      rw [hu0]
      exact W.zero_mem
    have hWambient_tau :
        ∀ v : Additive (LowerCentralFactor P 0), v ∈ Wambient →
          lowerCentralFactorLinearAut tau 0 v ∈ Wambient := by
      intro v hv
      change U.mkQ v ∈ W at hv
      change U.mkQ (lowerCentralFactorLinearAut tau 0 v) ∈ W
      have htv := hW (U.mkQ v) hv
      simpa [tauQ, tauQMap, Submodule.mapQ_apply] using htv
    rcases htau_upper_composition_irreducible Wambient hU_le_Wambient
        hWambient_tau with hbot | htop
    · left
      apply Submodule.comap_injective_of_surjective (f := U.mkQ)
        (Submodule.Quotient.mk_surjective U)
      simpa [Wambient, Submodule.ker_mkQ] using hbot
    · right
      apply Submodule.comap_injective_of_surjective (f := U.mkQ)
        (Submodule.Quotient.mk_surjective U)
      simpa [Wambient] using htop
  have htauQ_pow_mk : ∀ j : ℕ, ∀ v : Additive (LowerCentralFactor P 0),
      (tauQ ^ j) (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk
          ((lowerCentralFactorLinearAut tau 0 ^ j) v) := by
    intro j v
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [show tauQ ^ (j + 1) = tauQ * tauQ ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply, ih]
        change tauQMap
            (Submodule.Quotient.mk
              ((lowerCentralFactorLinearAut tau 0 ^ j) v)) = _
        rw [show tauQMap = Submodule.mapQ U U
            (lowerCentralFactorLinearAut tau 0).toLinearMap _ from rfl,
          Submodule.mapQ_apply]
        rw [show lowerCentralFactorLinearAut tau 0 ^ (j + 1) =
            lowerCentralFactorLinearAut tau 0 *
              lowerCentralFactorLinearAut tau 0 ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply]
        rfl
  let xiQ :
      (Additive (LowerCentralFactor P 0) ⧸ U) ≃ₗ[ZMod 2]
        (Additive (LowerCentralFactor P 0) ⧸ U) := tauQ ^ (2 ^ k)
  have hxiQ_irreducible :
      ∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0) ⧸ U),
        (∀ v : Additive (LowerCentralFactor P 0) ⧸ U,
          v ∈ W → xiQ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    exact lemma12_irreducible_pow_two_of_irreducible
      tauQ k htauQ_irreducible
  have hxiQ_mk (v : Additive (LowerCentralFactor P 0)) :
      xiQ (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (lowerCentralFactorLinearAut xi 0 v) := by
    rw [show lowerCentralFactorLinearAut xi 0 =
        (lowerCentralFactorLinearAut tau 0) ^ (2 ^ k) by
      simpa [xi] using lowerCentralFactorLinearAut_pow tau 0 (2 ^ k)]
    exact htauQ_pow_mk (2 ^ k) v
  have hU_tau_pow : ∀ j : ℕ,
      ∀ v : Additive (LowerCentralFactor P 0), v ∈ U →
        (lowerCentralFactorLinearAut tau 0 ^ j) v ∈ U := by
    intro j v hv
    induction j with
    | zero => simpa using hv
    | succ j ih =>
        rw [pow_succ', LinearEquiv.mul_apply]
        exact hU_tau _ ih
  have hU_xi : ∀ v : Additive (LowerCentralFactor P 0),
      v ∈ U → lowerCentralFactorLinearAut xi 0 v ∈ U := by
    intro v hv
    rw [show lowerCentralFactorLinearAut xi 0 =
        (lowerCentralFactorLinearAut tau 0) ^ (2 ^ k) by
      simpa [xi] using lowerCentralFactorLinearAut_pow tau 0 (2 ^ k)]
    exact hU_tau_pow (2 ^ k) v hv
  have hU_all : ∀ (x : X) (v : Additive (LowerCentralFactor P 0)),
      v ∈ U →
        lowerCentralFactorLinearAut
          (MulDistribMulAction.toMulAut X P x) 0 v ∈ U := by
    intro x v hv
    change v.toMul ∈ Ugroup at hv
    change (lowerCentralFactorLinearAut
      (MulDistribMulAction.toMulAut X P x) 0 v).toMul ∈ Ugroup
    rcases hv with ⟨a, ha, hav⟩
    rw [lowerCentralFactorLinearAut_toMul, ← hav]
    refine ⟨MulDistribMulAction.toMulAut X P x a, ?_, ?_⟩
    · exact (hmiddle.2.2.2.1 x a).mp ha
    · change lowerCentralFactorMulAut
          (MulDistribMulAction.toMulAut X P x) 0
            (QuotientGroup.mk' (lowerCentralFactorKernel P 0)
              (Subgroup.topEquiv.symm a)) =
        QuotientGroup.mk' (lowerCentralFactorKernel P 0)
          (Subgroup.topEquiv.symm
            (MulDistribMulAction.toMulAut X P x a))
      rw [lowerCentralFactorMulAut_mk]
      apply congrArg (QuotientGroup.mk' (lowerCentralFactorKernel P 0))
      apply Subtype.ext
      rfl
  have hU_ne_bot : U ≠ ⊥ := by
    simpa [U] using hUgroup_ne_bot
  have hU_ne_top : U ≠ ⊤ := by
    simpa [U] using hUgroup_ne_top
  let T0 := lowerCentralFactorLinearAut xi 0
  have hT0_odd : Odd (orderOf T0) := by
    exact hxi_odd.of_dvd_nat
      (orderOf_map_dvd (lowerCentralFactorLinearAutHom (H := P) 0) xi)
  obtain ⟨V, hUV, hV_xi⟩ :=
    lemma12_exists_isCompl_invariant_of_odd_linearEquiv
      T0 hT0_odd U (by simpa [T0] using hU_xi)
  have hV_ne_bot : V ≠ ⊥ := by
    intro hV_bot
    apply hU_ne_top
    apply eq_top_iff.mpr
    intro v _hv
    have hv : v ∈ U ⊔ V := by rw [hUV.sup_eq_top]; trivial
    simpa [hV_bot] using hv
  have hV_ne_top : V ≠ ⊤ := by
    intro hV_top
    apply hU_ne_bot
    apply eq_bot_iff.mpr
    intro v hv
    have hvV : v ∈ V := by rw [hV_top]; trivial
    have hv0 : v ∈ U ⊓ V := ⟨hv, hvV⟩
    rw [hUV.inf_eq_bot] at hv0
    simpa using hv0
  let eQ : (Additive (LowerCentralFactor P 0) ⧸ U) ≃ₗ[ZMod 2] V :=
    Submodule.quotientEquivOfIsCompl U V hUV
  let xiV : V ≃ₗ[ZMod 2] V :=
    eQ.symm.trans (xiQ.trans eQ)
  have hxiV_irreducible :
      ∀ W : Submodule (ZMod 2) V,
        (∀ v : V, v ∈ W → xiV v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let WQ : Submodule (ZMod 2)
        (Additive (LowerCentralFactor P 0) ⧸ U) :=
      W.comap eQ.toLinearMap
    have hWQ_xi :
        ∀ q : Additive (LowerCentralFactor P 0) ⧸ U,
          q ∈ WQ → xiQ q ∈ WQ := by
      intro q hq
      change eQ q ∈ W at hq
      change eQ (xiQ q) ∈ W
      have h := hW (eQ q) hq
      simpa [xiV] using h
    rcases hxiQ_irreducible WQ hWQ_xi with hbot | htop
    · left
      apply Submodule.comap_injective_of_surjective (f := eQ.toLinearMap)
        eQ.surjective
      simpa [WQ] using hbot
    · right
      apply Submodule.comap_injective_of_surjective (f := eQ.toLinearMap)
        eQ.surjective
      simpa [WQ] using htop
  have hxiV_val (v : V) :
      ((xiV v : V) : Additive (LowerCentralFactor P 0)) =
        lowerCentralFactorLinearAut xi 0
          (v : Additive (LowerCentralFactor P 0)) := by
    let w : V := ⟨lowerCentralFactorLinearAut xi 0 v,
      hV_xi v v.property⟩
    have hxiV_eq : xiV v = w := by
      change eQ (xiQ (eQ.symm v)) = w
      rw [show eQ.symm v = Submodule.Quotient.mk
          (v : Additive (LowerCentralFactor P 0)) by rfl,
        hxiQ_mk]
      simpa [eQ, w] using
        (Submodule.quotientEquivOfIsCompl_apply_mk_right
          (p := U) (q := V) hUV w)
    exact congrArg Subtype.val hxiV_eq
  let : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU_ne_bot
  let : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV_ne_bot
  have hfactor1_add_card :
      Nat.card (Additive (LowerCentralFactor P 1)) = 2 ^ n := by
    exact (Nat.card_congr Additive.toMul).trans hfactor1_card_n
  have hfactor1_card_gt :
      1 < Nat.card (Additive (LowerCentralFactor P 1)) := by
    rw [hfactor1_add_card]
    exact one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega)
  let : Nontrivial (Additive (LowerCentralFactor P 1)) :=
    Finite.one_lt_card_iff_nontrivial.mp hfactor1_card_gt
  have hS_irreducible :=
    lemma6_irreducible_of_transitive S (by simpa [S] using hxi_transitive)
  obtain ⟨a, ha, lambda, uCoordinates, uBasis, hU_card,
      hlambda, huCoordinates, huBasis_eigen, huBasis_expansion⟩ :=
    lemma5_irreducible_conjugate_eigenbasis xiU hxiU_irreducible
  obtain ⟨b, hb, mu, vCoordinates, vBasis, hV_card,
      hmu, hvCoordinates, hvBasis_eigen, hvBasis_expansion⟩ :=
    lemma5_irreducible_conjugate_eigenbasis xiV hxiV_irreducible
  obtain ⟨d, hd, nu, centerCoordinates, centerBasis, hcenter_card,
      hnu, hcenterCoordinates, hcenterBasis_eigen,
      hcenterBasis_expansion⟩ :=
    lemma5_irreducible_conjugate_eigenbasis S hS_irreducible
  have hdn : d = n := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    exact hcenter_card.symm.trans hfactor1_add_card
  subst d
  obtain ⟨bracket, bracketK, squareMap, hbracketK_tmul,
      hbracket_equivariant, hbracket_self, hbracket_mk, hbracket_span,
      hsquare_mk, hsquare_equivariant, hsquare_add⟩ :=
    lemma5_square_map_normal_form_quadratic_core xi n
      (by
        change squaresSubgroup P ≤ (⊤ : Subgroup P).lowerCentralSeries 1
        rw [hL1_eq_B]
        exact hsquares_le_B)
  have hsquare_anisotropic :
      ∀ v : Additive (LowerCentralFactor P 0), squareMap v = 0 → v = 0 := by
    intro v hv
    obtain ⟨x, hx⟩ :=
      QuotientGroup.mk'_surjective (lowerCentralFactorKernel P 0) v.toMul
    have hv_repr : v = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel P 0) x) := by
      apply Additive.toMul.injective
      exact hx.symm
    have hxsquare_mem : (x : P) ^ 2 ∈ (⊤ : Subgroup P).lowerCentralSeries 1 := by
      rw [hL1_eq_B]
      exact hsquares_le_B (Subgroup.subset_closure ⟨(x : P), rfl⟩)
    have hmk_zero :
        Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel P 1)
              ⟨(x : P) ^ 2, hxsquare_mem⟩) = 0 := by
      rw [← hsquare_mk x hxsquare_mem, ← hv_repr]
      exact hv
    have hmk_one :
        QuotientGroup.mk' (lowerCentralFactorKernel P 1)
            ⟨(x : P) ^ 2, hxsquare_mem⟩ = 1 := by
      apply Additive.ofMul.injective
      simpa using hmk_zero
    have hsqker :
        (⟨(x : P) ^ 2, hxsquare_mem⟩ : (⊤ : Subgroup P).lowerCentralSeries 1) ∈
          lowerCentralFactorKernel P 1 :=
      (QuotientGroup.eq_one_iff
        (N := lowerCentralFactorKernel P 1)
        (⟨(x : P) ^ 2, hxsquare_mem⟩ : (⊤ : Subgroup P).lowerCentralSeries 1)).mp hmk_one
    rw [hkernel1_bot] at hsqker
    have hxsquare : (x : P) ^ 2 = 1 := by
      have hsquare_one :
          (⟨(x : P) ^ 2, hxsquare_mem⟩ : (⊤ : Subgroup P).lowerCentralSeries 1) = 1 := by
        simpa using hsqker
      exact congrArg Subtype.val hsquare_one
    by_cases hxone : (x : P) = 1
    · apply Additive.toMul.injective
      change v.toMul = 1
      rw [← hx]
      have xone : x = 1 := Subtype.ext hxone
      rw [xone]
      exact map_one _
    · have hxB : (x : P) ∈ B :=
        lemma1_involutions_mem_of_nontrivial_invariant
          _hP _hXtrans hlower.2.2.2.1 (ne_of_gt hlower.1)
            (x : P) ⟨hxone, hxsquare⟩
      have hxmap : (x : P) ∈
          (lowerCentralFactorKernel P 0).map
            ((⊤ : Subgroup P).lowerCentralSeries 0).subtype := by
        rw [hkernel0_map_B]
        exact hxB
      rcases hxmap with ⟨z, hz, hzx⟩
      have hzx' : z = x := by
        apply Subtype.ext
        exact hzx
      have hxker : x ∈ lowerCentralFactorKernel P 0 := hzx' ▸ hz
      have hxquot :
          QuotientGroup.mk' (lowerCentralFactorKernel P 0) x = 1 :=
        (QuotientGroup.eq_one_iff
          (N := lowerCentralFactorKernel P 0) x).mpr hxker
      apply Additive.toMul.injective
      change v.toMul = 1
      rw [← hx]
      exact hxquot
  have hsquare_zero : squareMap 0 = 0 := by
    have h := hsquare_add 0 0
    simpa using h
  have hsquare_xiU_pow : ∀ j : ℕ, ∀ u : U,
      squareMap (((xiU ^ j) u : U) : Additive (LowerCentralFactor P 0)) =
        (S ^ j) (squareMap (u : Additive (LowerCentralFactor P 0))) := by
    intro j u
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [show xiU ^ (j + 1) = xiU * xiU ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply]
        rw [hxiU_val, hsquare_equivariant, ih]
        rw [show S ^ (j + 1) = S * S ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply]
  have hsquare_xiV_pow : ∀ j : ℕ, ∀ v : V,
      squareMap (((xiV ^ j) v : V) : Additive (LowerCentralFactor P 0)) =
        (S ^ j) (squareMap (v : Additive (LowerCentralFactor P 0))) := by
    intro j v
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [show xiV ^ (j + 1) = xiV * xiV ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply]
        rw [hxiV_val, hsquare_equivariant, ih]
        rw [show S ^ (j + 1) = S * S ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply]
  have hsquareU_surjective : Function.Surjective
      (fun u : U => squareMap
        (u : Additive (LowerCentralFactor P 0))) := by
    intro z
    by_cases hz : z = 0
    · exact ⟨0, by simpa [hz] using hsquare_zero⟩
    · obtain ⟨u0, hu0⟩ := exists_ne (0 : U)
      have hsq0 : squareMap
          (u0 : Additive (LowerCentralFactor P 0)) ≠ 0 := by
        intro hzero
        exact hu0 (Subtype.ext (hsquare_anisotropic _ hzero))
      obtain ⟨j, hj⟩ := hxi_transitive _ hsq0 z hz
      refine ⟨(xiU ^ j) u0, ?_⟩
      calc
        squareMap (((xiU ^ j) u0 : U) :
            Additive (LowerCentralFactor P 0)) =
            (S ^ j) (squareMap
              (u0 : Additive (LowerCentralFactor P 0))) :=
          hsquare_xiU_pow j u0
        _ = z := by simpa [S] using hj
  have hsquareV_surjective : Function.Surjective
      (fun v : V => squareMap
        (v : Additive (LowerCentralFactor P 0))) := by
    intro z
    by_cases hz : z = 0
    · exact ⟨0, by simpa [hz] using hsquare_zero⟩
    · obtain ⟨v0, hv0⟩ := exists_ne (0 : V)
      have hsq0 : squareMap
          (v0 : Additive (LowerCentralFactor P 0)) ≠ 0 := by
        intro hzero
        exact hv0 (Subtype.ext (hsquare_anisotropic _ hzero))
      obtain ⟨j, hj⟩ := hxi_transitive _ hsq0 z hz
      refine ⟨(xiV ^ j) v0, ?_⟩
      calc
        squareMap (((xiV ^ j) v0 : V) :
            Additive (LowerCentralFactor P 0)) =
            (S ^ j) (squareMap
              (v0 : Additive (LowerCentralFactor P 0))) :=
          hsquare_xiV_pow j v0
        _ = z := by simpa [S] using hj
  have hcross_nonzero :
      ∃ u : U, ∃ v : V,
        bracket (u : Additive (LowerCentralFactor P 0))
          (v : Additive (LowerCentralFactor P 0)) ≠ 0 := by
    by_contra hzero
    push Not at hzero
    obtain ⟨z, hz⟩ := exists_ne
      (0 : Additive (LowerCentralFactor P 1))
    obtain ⟨u, hu⟩ := hsquareU_surjective z
    obtain ⟨v, hv⟩ := hsquareV_surjective z
    change squareMap (u : Additive (LowerCentralFactor P 0)) = z at hu
    change squareMap (v : Additive (LowerCentralFactor P 0)) = z at hv
    have hzadd : z + z = 0 := by
      nth_rw 2 [← ZModModule.neg_eq_self z]
      exact add_neg_cancel z
    have hsum_square : squareMap
        ((u : Additive (LowerCentralFactor P 0)) +
          (v : Additive (LowerCentralFactor P 0))) = 0 := by
      rw [hsquare_add, hu, hv, hzero u v, add_zero, hzadd]
    have hsum :
        (u : Additive (LowerCentralFactor P 0)) +
          (v : Additive (LowerCentralFactor P 0)) = 0 :=
      hsquare_anisotropic _ hsum_square
    have huv :
        (u : Additive (LowerCentralFactor P 0)) =
          (v : Additive (LowerCentralFactor P 0)) := by
      have hneg :
          (u : Additive (LowerCentralFactor P 0)) =
            -(v : Additive (LowerCentralFactor P 0)) :=
        eq_neg_of_add_eq_zero_left hsum
      simpa only [ZModModule.neg_eq_self] using hneg
    have huV : (u : Additive (LowerCentralFactor P 0)) ∈ V := by
      rw [huv]
      exact v.property
    have huinf : (u : Additive (LowerCentralFactor P 0)) ∈ U ⊓ V :=
      ⟨u.property, huV⟩
    rw [hUV.inf_eq_bot] at huinf
    have hu0 : u = 0 := by
      apply Subtype.ext
      simpa using huinf
    apply hz
    rw [← hu, hu0]
    exact hsquare_zero
  let crossBracket : U →ₗ[ZMod 2] V →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1) :=
    { toFun := fun u =>
        { toFun := fun v => bracket
            (u : Additive (LowerCentralFactor P 0))
            (v : Additive (LowerCentralFactor P 0))
          map_add' := by
            intro v w
            exact (bracket
              (u : Additive (LowerCentralFactor P 0))).map_add v w
          map_smul' := by
            intro c v
            exact (bracket
              (u : Additive (LowerCentralFactor P 0))).map_smul c v }
      map_add' := by
        intro u w
        apply LinearMap.ext
        intro v
        change bracket
            ((u : Additive (LowerCentralFactor P 0)) + w) v = _
        rw [map_add, LinearMap.add_apply]
        rfl
      map_smul' := by
        intro c u
        apply LinearMap.ext
        intro v
        change bracket
            (c • (u : Additive (LowerCentralFactor P 0))) v = _
        rw [map_smul, LinearMap.smul_apply]
        rfl }
  have hcross_equivariant (u : U) (v : V) :
      crossBracket (xiU u) (xiV v) = S (crossBracket u v) := by
    change bracket
        ((xiU u : U) : Additive (LowerCentralFactor P 0))
        ((xiV v : V) : Additive (LowerCentralFactor P 0)) = _
    rw [hxiU_val, hxiV_val, hbracket_equivariant]
    rfl
  have hcross_span : Submodule.span (ZMod 2)
      (Set.range fun p : U × V => crossBracket p.1 p.2) = ⊤ := by
    let R : Submodule (ZMod 2) (Additive (LowerCentralFactor P 1)) :=
      Submodule.span (ZMod 2)
        (Set.range fun p : U × V => crossBracket p.1 p.2)
    have hR_invariant : ∀ z : Additive (LowerCentralFactor P 1),
        z ∈ R → S z ∈ R := by
      intro z hz
      refine Submodule.span_induction
        (p := fun z _ => S z ∈ R) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨⟨u, v⟩, rfl⟩
        rw [← hcross_equivariant]
        exact Submodule.subset_span ⟨⟨xiU u, xiV v⟩, rfl⟩
      · simp
      · intro x y _hx _hy hx hy
        simpa using R.add_mem hx hy
      · intro c x _hx hx
        simpa using R.smul_mem c hx
    have hR_ne_bot : R ≠ ⊥ := by
      intro hR_bot
      obtain ⟨u, v, huv⟩ := hcross_nonzero
      have hmem : crossBracket u v ∈ R :=
        Submodule.subset_span ⟨⟨u, v⟩, rfl⟩
      rw [hR_bot] at hmem
      exact huv (by simpa [crossBracket] using hmem)
    rcases hS_irreducible R hR_invariant with hbot | htop
    · exact False.elim (hR_ne_bot hbot)
    · exact htop
  have hfactor1_card_eq_B :
      Nat.card (LowerCentralFactor P 1) = Nat.card B := by
    change Nat.card
        (((⊤ : Subgroup P).lowerCentralSeries 1) ⧸ lowerCentralFactorKernel P 1) =
      Nat.card B
    rw [hkernel1_bot]
    calc
      Nat.card (((⊤ : Subgroup P).lowerCentralSeries 1) ⧸
            (⊥ : Subgroup ((⊤ : Subgroup P).lowerCentralSeries 1))) =
          Nat.card ((⊤ : Subgroup P).lowerCentralSeries 1) := by
            exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
      _ = Nat.card B := Nat.card_congr
        (Set.equivOfEq (congrArg (fun R : Subgroup P => (R : Set P))
          hL1_eq_B))
  have hB_card : Nat.card B = 2 ^ n :=
    hfactor1_card_eq_B.symm.trans hfactor1_card_n
  let involEquiv : {x : P // x ∈ involutions P} ≃ {b : B // b ≠ 1} :=
    { toFun := fun x =>
        ⟨⟨x, lemma1_involutions_mem_of_nontrivial_invariant
          _hP _hXtrans hlower.2.2.2.1 (ne_of_gt hlower.1)
            x x.property⟩, fun hx => x.property.1 (congrArg Subtype.val hx)⟩
      invFun := fun b =>
        ⟨b.1, ⟨fun hb => b.2 (Subtype.ext hb), by
          simpa using congrArg Subtype.val (hB_exponent_two b.1)⟩⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rfl
      right_inv := by
        intro b
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  have hinvolution_card :
      Nat.card {x : P // x ∈ involutions P} = 2 ^ n - 1 := by
    calc
      Nat.card {x : P // x ∈ involutions P} =
          Nat.card {b : B // b ≠ 1} := Nat.card_congr involEquiv
      _ = Nat.card B - 1 := by
        let : Fintype B := Fintype.ofFinite B
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        simp
      _ = 2 ^ n - 1 := by rw [hB_card]
  let : Fintype X := Fintype.ofFinite X
  have hxi_order_dvd_cardX : orderOf xi ∣ Nat.card X := by
    rw [hxi_actor]
    have hactor_card : orderOf (g ^ (2 ^ k)) ∣ Fintype.card X :=
      orderOf_dvd_card
    exact (orderOf_map_dvd (MulDistribMulAction.toMulAut X P)
      (g ^ (2 ^ k))).trans (by
        simpa [Nat.card_eq_fintype_card] using hactor_card)
  have hxi_prime_support : ∀ p : ℕ, p.Prime → p ∣ orderOf xi →
      p ∣ 2 ^ n - 1 := by
    intro p hp hp_xi
    have hp_inv := _hXprimeSupport p hp
      (hp_xi.trans hxi_order_dvd_cardX)
    simpa [hinvolution_card] using hp_inv
  have hxiU_pow_val_ambient : ∀ j : ℕ, ∀ u : U,
      (((xiU ^ j) u : U) : Additive (LowerCentralFactor P 0)) =
        (lowerCentralFactorLinearAut xi 0 ^ j)
          (u : Additive (LowerCentralFactor P 0)) := by
    intro j u
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [show xiU ^ (j + 1) = xiU * xiU ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply]
        rw [hxiU_val, ih]
        rw [show lowerCentralFactorLinearAut xi 0 ^ (j + 1) =
            lowerCentralFactorLinearAut xi 0 *
              lowerCentralFactorLinearAut xi 0 ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply]
  have hxiV_pow_val_ambient : ∀ j : ℕ, ∀ v : V,
      (((xiV ^ j) v : V) : Additive (LowerCentralFactor P 0)) =
        (lowerCentralFactorLinearAut xi 0 ^ j)
          (v : Additive (LowerCentralFactor P 0)) := by
    intro j v
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [show xiV ^ (j + 1) = xiV * xiV ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply]
        rw [hxiV_val, ih]
        rw [show lowerCentralFactorLinearAut xi 0 ^ (j + 1) =
            lowerCentralFactorLinearAut xi 0 *
              lowerCentralFactorLinearAut xi 0 ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply]
  have hxiU_order_dvd_xi : orderOf xiU ∣ orderOf xi := by
    apply orderOf_dvd_of_pow_eq_one
    apply LinearEquiv.ext
    intro u
    apply Subtype.ext
    rw [hxiU_pow_val_ambient, ← lowerCentralFactorLinearAut_pow,
      pow_orderOf_eq_one]
    exact congrArg (fun f : Additive (LowerCentralFactor P 0) ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor P 0) => f u)
        (map_one (lowerCentralFactorLinearAutHom (H := P) 0))
  have hxiV_order_dvd_xi : orderOf xiV ∣ orderOf xi := by
    apply orderOf_dvd_of_pow_eq_one
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    rw [hxiV_pow_val_ambient, ← lowerCentralFactorLinearAut_pow,
      pow_orderOf_eq_one]
    exact congrArg (fun f : Additive (LowerCentralFactor P 0) ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor P 0) => f v)
        (map_one (lowerCentralFactorLinearAutHom (H := P) 0))
  have hS_order_dvd_xiU : orderOf S ∣ orderOf xiU := by
    apply orderOf_dvd_of_pow_eq_one
    apply LinearEquiv.ext
    intro z
    obtain ⟨u, hu⟩ := hsquareU_surjective z
    change squareMap (u : Additive (LowerCentralFactor P 0)) = z at hu
    have hpow := hsquare_xiU_pow (orderOf xiU) u
    rw [pow_orderOf_eq_one] at hpow
    simpa [hu] using hpow.symm
  have hS_order_dvd_xiV : orderOf S ∣ orderOf xiV := by
    apply orderOf_dvd_of_pow_eq_one
    apply LinearEquiv.ext
    intro z
    obtain ⟨v, hv⟩ := hsquareV_surjective z
    change squareMap (v : Additive (LowerCentralFactor P 0)) = z at hv
    have hpow := hsquare_xiV_pow (orderOf xiV) v
    rw [pow_orderOf_eq_one] at hpow
    simpa [hv] using hpow.symm
  have hU_finrank : Module.finrank (ZMod 2) U = a :=
    uCoordinates.finrank_eq.symm.trans
      (GaloisField.finrank 2 ha.ne')
  have hV_finrank : Module.finrank (ZMod 2) V = b :=
    vCoordinates.finrank_eq.symm.trans
      (GaloisField.finrank 2 hb.ne')
  have hxiU_order_eq_lambda :
      orderOf xiU = orderOf (Units.mk0 lambda hlambda) :=
    lemma6_coordinate_unit_order xiU uCoordinates lambda hlambda
      huCoordinates
  have hxiV_order_eq_mu :
      orderOf xiV = orderOf (Units.mk0 mu hmu) :=
    lemma6_coordinate_unit_order xiV vCoordinates mu hmu
      hvCoordinates
  have hxiU_order_dvd_field : orderOf xiU ∣ 2 ^ a - 1 := by
    rw [hxiU_order_eq_lambda]
    have h := orderOf_dvd_natCard (Units.mk0 lambda hlambda)
    rw [Nat.card_units,
      GaloisField.card 2 a ha.ne'] at h
    exact h
  have hxiV_order_dvd_field : orderOf xiV ∣ 2 ^ b - 1 := by
    rw [hxiV_order_eq_mu]
    have h := orderOf_dvd_natCard (Units.mk0 mu hmu)
    rw [Nat.card_units,
      GaloisField.card 2 b hb.ne'] at h
    exact h
  have hbase_dvd_xiU : 2 ^ n - 1 ∣ orderOf xiU := by
    rw [← hS_order]
    exact hS_order_dvd_xiU
  have hbase_dvd_xiV : 2 ^ n - 1 ∣ orderOf xiV := by
    rw [← hS_order]
    exact hS_order_dvd_xiV
  have hxiU_prime_support : ∀ p : ℕ, p.Prime → p ∣ orderOf xiU →
      p ∣ 2 ^ n - 1 := by
    intro p hp hpU
    exact hxi_prime_support p hp (hpU.trans hxiU_order_dvd_xi)
  have hxiV_prime_support : ∀ p : ℕ, p.Prime → p ∣ orderOf xiV →
      p ∣ 2 ^ n - 1 := by
    intro p hp hpV
    exact hxi_prime_support p hp (hpV.trans hxiV_order_dvd_xi)
  obtain ⟨aDegree, haDegree_odd, ha_eq_n_mul⟩ :=
    lemma12_odd_coordinate_degree_of_order_prime_support
      xiU hxiU_irreducible a n ha (by omega) hU_finrank
      hbase_dvd_xiU hxiU_order_dvd_field hxiU_prime_support
  obtain ⟨bDegree, hbDegree_odd, hb_eq_n_mul⟩ :=
    lemma12_odd_coordinate_degree_of_order_prime_support
      xiV hxiV_irreducible b n hb (by omega) hV_finrank
      hbase_dvd_xiV hxiV_order_dvd_field hxiV_prime_support
  let bracketU : U →ₗ[ZMod 2] U →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1) :=
    { toFun := fun u =>
        { toFun := fun v => bracket
            (u : Additive (LowerCentralFactor P 0))
            (v : Additive (LowerCentralFactor P 0))
          map_add' := by
            intro v w
            exact (bracket
              (u : Additive (LowerCentralFactor P 0))).map_add v w
          map_smul' := by
            intro c v
            exact (bracket
              (u : Additive (LowerCentralFactor P 0))).map_smul c v }
      map_add' := by
        intro u w
        apply LinearMap.ext
        intro v
        change bracket
            ((u : Additive (LowerCentralFactor P 0)) + w) v = _
        rw [map_add, LinearMap.add_apply]
        rfl
      map_smul' := by
        intro c u
        apply LinearMap.ext
        intro v
        change bracket
            (c • (u : Additive (LowerCentralFactor P 0))) v = _
        rw [map_smul, LinearMap.smul_apply]
        rfl }
  let bracketV : V →ₗ[ZMod 2] V →ₗ[ZMod 2]
      Additive (LowerCentralFactor P 1) :=
    { toFun := fun v =>
        { toFun := fun w => bracket
            (v : Additive (LowerCentralFactor P 0))
            (w : Additive (LowerCentralFactor P 0))
          map_add' := by
            intro w z
            exact (bracket
              (v : Additive (LowerCentralFactor P 0))).map_add w z
          map_smul' := by
            intro c w
            exact (bracket
              (v : Additive (LowerCentralFactor P 0))).map_smul c w }
      map_add' := by
        intro v z
        apply LinearMap.ext
        intro w
        change bracket
            ((v : Additive (LowerCentralFactor P 0)) + z) w = _
        rw [map_add, LinearMap.add_apply]
        rfl
      map_smul' := by
        intro c v
        apply LinearMap.ext
        intro w
        change bracket
            (c • (v : Additive (LowerCentralFactor P 0))) w = _
        rw [map_smul, LinearMap.smul_apply]
        rfl }
  have hcenter_finrank : Module.finrank (ZMod 2)
      (Additive (LowerCentralFactor P 1)) = n :=
    centerCoordinates.finrank_eq.symm.trans
      (GaloisField.finrank 2 (by omega : n ≠ 0))
  have ha_eq_n : a = n := by
    by_contra han
    have haDegree_ne_one : aDegree ≠ 1 := by
      intro hdegree
      rw [hdegree, mul_one] at ha_eq_n_mul
      exact han ha_eq_n_mul
    obtain ⟨c, hc⟩ := haDegree_odd
    have haDegree_gt_two : 2 < aDegree := by omega
    have hdim : 2 * Module.finrank (ZMod 2)
          (Additive (LowerCentralFactor P 1)) <
        Module.finrank (ZMod 2) U := by
      rw [hU_finrank, hcenter_finrank, ha_eq_n_mul]
      simpa [Nat.mul_comm] using
        (Nat.mul_lt_mul_left (by omega : 0 < n)).2 haDegree_gt_two
    obtain ⟨u, hu, hqu⟩ := lemma10_exists_nonzero_quadratic_zero
      U (Additive (LowerCentralFactor P 1))
      (fun u : U => squareMap
        (u : Additive (LowerCentralFactor P 0)))
      bracketU (by simpa using hsquare_zero)
      (by
        intro u v
        change squareMap
            ((u : Additive (LowerCentralFactor P 0)) + v) = _
        exact hsquare_add _ _)
      (by
        intro u
        simpa [bracketU] using hbracket_self
          (u : Additive (LowerCentralFactor P 0)))
      hdim
    apply hu
    apply Subtype.ext
    exact hsquare_anisotropic _ hqu
  have hb_eq_n : b = n := by
    by_contra hbn
    have hbDegree_ne_one : bDegree ≠ 1 := by
      intro hdegree
      rw [hdegree, mul_one] at hb_eq_n_mul
      exact hbn hb_eq_n_mul
    obtain ⟨c, hc⟩ := hbDegree_odd
    have hbDegree_gt_two : 2 < bDegree := by omega
    have hdim : 2 * Module.finrank (ZMod 2)
          (Additive (LowerCentralFactor P 1)) <
        Module.finrank (ZMod 2) V := by
      rw [hV_finrank, hcenter_finrank, hb_eq_n_mul]
      simpa [Nat.mul_comm] using
        (Nat.mul_lt_mul_left (by omega : 0 < n)).2 hbDegree_gt_two
    obtain ⟨v, hv, hqv⟩ := lemma10_exists_nonzero_quadratic_zero
      V (Additive (LowerCentralFactor P 1))
      (fun v : V => squareMap
        (v : Additive (LowerCentralFactor P 0)))
      bracketV (by simpa using hsquare_zero)
      (by
        intro v w
        change squareMap
            ((v : Additive (LowerCentralFactor P 0)) + w) = _
        exact hsquare_add _ _)
      (by
        intro v
        simpa [bracketV] using hbracket_self
          (v : Additive (LowerCentralFactor P 0)))
      hdim
    apply hv
    apply Subtype.ext
    exact hsquare_anisotropic _ hqv
  have hxiU_order_dvd_n : orderOf xiU ∣ 2 ^ n - 1 := by
    simpa [ha_eq_n] using hxiU_order_dvd_field
  have hxiV_order_dvd_n : orderOf xiV ∣ 2 ^ n - 1 := by
    simpa [hb_eq_n] using hxiV_order_dvd_field
  cases ha_eq_n.symm
  cases hb_eq_n.symm
  have hxiU_order : orderOf xiU = 2 ^ n - 1 :=
    Nat.dvd_antisymm hxiU_order_dvd_n hbase_dvd_xiU
  have hxiV_order : orderOf xiV = 2 ^ n - 1 :=
    Nat.dvd_antisymm hxiV_order_dvd_n hbase_dvd_xiV
  have hlambda_order :
      orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1 := by
    rw [← hxiU_order_eq_lambda]
    exact hxiU_order
  have hmu_order :
      orderOf (Units.mk0 mu hmu) = 2 ^ n - 1 := by
    rw [← hxiV_order_eq_mu]
    exact hxiV_order
  have hnu_order :
      orderOf (Units.mk0 nu hnu) = 2 ^ n - 1 := by
    rw [← lemma6_coordinate_unit_order S centerCoordinates nu hnu
      hcenterCoordinates]
    exact hS_order
  have hfactor0_card :
      Nat.card (LowerCentralFactor P 0) = (2 ^ n) ^ 2 := by
    change Nat.card (Additive (LowerCentralFactor P 0)) = (2 ^ n) ^ 2
    calc
      Nat.card (Additive (LowerCentralFactor P 0)) = Nat.card (U × V) := by
        exact (Nat.card_congr
          (Submodule.prodEquivOfIsCompl U V hUV).toEquiv).symm
      _ = Nat.card U * Nat.card V := Nat.card_prod U V
      _ = (2 ^ n) ^ 2 := by rw [hU_card, hV_card]; ring
  have hsummandData : Lemma12SummandData X P B := by
    exact ⟨n, q0, U, hn, hq0_ker, hq0_surj, hq0_equivariant,
      hU_all, hU_card, hB_card, hfactor0_card, hB_le_center,
      hinvolution_card⟩
  let xiUK := xiU.baseChange (ZMod 2) (BinaryGaloisField n) U U
  let xiVK := xiV.baseChange (ZMod 2) (BinaryGaloisField n) V V
  let SK := S.baseChange (ZMod 2) (BinaryGaloisField n)
    (Additive (LowerCentralFactor P 1))
    (Additive (LowerCentralFactor P 1))
  let bracketUK := lemma6_scalarExtendBilinear
    (K := BinaryGaloisField n) bracketU
  let bracketVK := lemma6_scalarExtendBilinear
    (K := BinaryGaloisField n) bracketV
  let crossBracketK := lemma6_scalarExtendBilinear
    (K := BinaryGaloisField n) crossBracket
  have hbracketU_equivariant (u v : U) :
      bracketU (xiU u) (xiU v) = S (bracketU u v) := by
    change bracket
      ((xiU u : U) : Additive (LowerCentralFactor P 0))
      ((xiU v : U) : Additive (LowerCentralFactor P 0)) = _
    rw [hxiU_val, hxiU_val, hbracket_equivariant]
    rfl
  have hbracketV_equivariant (v w : V) :
      bracketV (xiV v) (xiV w) = S (bracketV v w) := by
    change bracket
      ((xiV v : V) : Additive (LowerCentralFactor P 0))
      ((xiV w : V) : Additive (LowerCentralFactor P 0)) = _
    rw [hxiV_val, hxiV_val, hbracket_equivariant]
    rfl
  have hbracketUK_equivariant : ∀ x y,
      bracketUK (xiUK x) (xiUK y) = SK (bracketUK x y) :=
    lemma6_scalarExtendBilinear_equivariant
      xiU xiU S bracketU hbracketU_equivariant
  have hbracketVK_equivariant : ∀ x y,
      bracketVK (xiVK x) (xiVK y) = SK (bracketVK x y) :=
    lemma6_scalarExtendBilinear_equivariant
      xiV xiV S bracketV hbracketV_equivariant
  have hcrossBracketK_equivariant : ∀ x y,
      crossBracketK (xiUK x) (xiVK y) = SK (crossBracketK x y) :=
    lemma6_scalarExtendBilinear_equivariant
      xiU xiV S crossBracket hcross_equivariant
  have hbracketU_self (u : U) : bracketU u u = 0 := by
    simpa [bracketU] using hbracket_self
      (u : Additive (LowerCentralFactor P 0))
  have hbracketV_self (v : V) : bracketV v v = 0 := by
    simpa [bracketV] using hbracket_self
      (v : Additive (LowerCentralFactor P 0))
  have hbracketUK_tmul (u v : U) :
      bracketUK
          ((1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] u)
          ((1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] v) =
        (1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] bracketU u v := by
    exact lemma6_scalarExtendBilinear_tmul bracketU u v
  have hbracketVK_tmul (v w : V) :
      bracketVK
          ((1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] v)
          ((1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] w) =
        (1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] bracketV v w := by
    exact lemma6_scalarExtendBilinear_tmul bracketV v w
  have hcrossBracketK_tmul (u : U) (v : V) :
      crossBracketK
          ((1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] u)
          ((1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] v) =
        (1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] crossBracket u v := by
    exact lemma6_scalarExtendBilinear_tmul crossBracket u v
  have hbracketUK_self :=
    lemma6_scalarExtendBilinear_self
      (K := BinaryGaloisField n) bracketU hbracketU_self
  have hbracketVK_self :=
    lemma6_scalarExtendBilinear_self
      (K := BinaryGaloisField n) bracketV hbracketV_self
  let : Nontrivial
      (TensorProduct (ZMod 2) (BinaryGaloisField n)
        (Additive (LowerCentralFactor P 1))) := by
    let i0 : Fin n := ⟨0, by omega⟩
    exact ⟨⟨centerBasis i0, 0, centerBasis.ne_zero i0⟩⟩
  have hU_internal_spectrum :
      bracketU = 0 ∨
        ∃ i j s : Fin n,
          i ≠ j ∧ bracketUK (uBasis i) (uBasis j) ≠ 0 ∧
            lambda ^ (2 ^ (i : ℕ)) * lambda ^ (2 ^ (j : ℕ)) =
              nu ^ (2 ^ (s : ℕ)) := by
    by_cases hzero : bracketU = 0
    · exact Or.inl hzero
    · right
      have hspan := lemma12_bilinear_span_eq_top_of_nonzero
        xiU S bracketU hbracketU_equivariant hS_irreducible hzero
      have hspanK := lemma6_scalarExtendedBilinear_span
        bracketU bracketUK hbracketUK_tmul hspan
      obtain ⟨i, j, hij⟩ :=
        lemma6_exists_basis_pair_ne_zero_of_span_eq_top
          bracketUK uBasis hspanK
      have hij_ne : i ≠ j := by
        intro h
        subst j
        exact hij (hbracketUK_self (uBasis i))
      obtain ⟨s, hs⟩ :=
        lemma6_nonzero_equivariant_bilinear_basis_value_spectrum
          xiUK SK bracketUK hbracketUK_equivariant
          uBasis (fun t : Fin n => lambda ^ (2 ^ (t : ℕ)))
          (by simpa [xiUK] using huBasis_eigen)
          centerBasis (fun t : Fin n => nu ^ (2 ^ (t : ℕ)))
          (by simpa [SK] using hcenterBasis_eigen) i j hij
      exact ⟨i, j, s, hij_ne, hij, hs⟩
  have hV_internal_spectrum :
      bracketV = 0 ∨
        ∃ i j s : Fin n,
          i ≠ j ∧ bracketVK (vBasis i) (vBasis j) ≠ 0 ∧
            mu ^ (2 ^ (i : ℕ)) * mu ^ (2 ^ (j : ℕ)) =
              nu ^ (2 ^ (s : ℕ)) := by
    by_cases hzero : bracketV = 0
    · exact Or.inl hzero
    · right
      have hspan := lemma12_bilinear_span_eq_top_of_nonzero
        xiV S bracketV hbracketV_equivariant hS_irreducible hzero
      have hspanK := lemma6_scalarExtendedBilinear_span
        bracketV bracketVK hbracketVK_tmul hspan
      obtain ⟨i, j, hij⟩ :=
        lemma6_exists_basis_pair_ne_zero_of_span_eq_top
          bracketVK vBasis hspanK
      have hij_ne : i ≠ j := by
        intro h
        subst j
        exact hij (hbracketVK_self (vBasis i))
      obtain ⟨s, hs⟩ :=
        lemma6_nonzero_equivariant_bilinear_basis_value_spectrum
          xiVK SK bracketVK hbracketVK_equivariant
          vBasis (fun t : Fin n => mu ^ (2 ^ (t : ℕ)))
          (by simpa [xiVK] using hvBasis_eigen)
          centerBasis (fun t : Fin n => nu ^ (2 ^ (t : ℕ)))
          (by simpa [SK] using hcenterBasis_eigen) i j hij
      exact ⟨i, j, s, hij_ne, hij, hs⟩
  have hcross_spectrum :
      ∃ i j s : Fin n,
        crossBracketK (uBasis i) (vBasis j) ≠ 0 ∧
          lambda ^ (2 ^ (i : ℕ)) * mu ^ (2 ^ (j : ℕ)) =
            nu ^ (2 ^ (s : ℕ)) := by
    have hspanK := lemma6_scalarExtendedBilinear_span₂
      crossBracket crossBracketK hcrossBracketK_tmul hcross_span
    obtain ⟨i, j, hij⟩ :=
      lemma6_exists_basis_pair_ne_zero_of_span_eq_top₂
        crossBracketK uBasis vBasis hspanK
    obtain ⟨s, hs⟩ :=
      lemma6_nonzero_equivariant_bilinear_basis_value_spectrum₂
        xiUK xiVK SK crossBracketK hcrossBracketK_equivariant
        uBasis (fun t : Fin n => lambda ^ (2 ^ (t : ℕ)))
        (by simpa [xiUK] using huBasis_eigen)
        vBasis (fun t : Fin n => mu ^ (2 ^ (t : ℕ)))
        (by simpa [xiVK] using hvBasis_eigen)
        centerBasis (fun t : Fin n => nu ^ (2 ^ (t : ℕ)))
        (by simpa [SK] using hcenterBasis_eigen) i j hij
    exact ⟨i, j, s, hij, hs⟩
  have hU_monomial := lemma12_restricted_square_monomial
    n (by omega) xiU S lambda nu hlambda hlambda_order
    uCoordinates centerCoordinates huCoordinates hcenterCoordinates
    uBasis centerBasis huBasis_eigen hcenterBasis_eigen
    (fun u : U => squareMap
      (u : Additive (LowerCentralFactor P 0)))
    bracketU (by simpa using hsquare_zero)
    (by
      intro u v
      change squareMap
          ((u : Additive (LowerCentralFactor P 0)) + v) = _
      simpa [bracketU] using hsquare_add
        (u : Additive (LowerCentralFactor P 0))
        (v : Additive (LowerCentralFactor P 0)))
    (by
      intro u
      change squareMap
          ((xiU u : U) : Additive (LowerCentralFactor P 0)) = _
      rw [hxiU_val]
      exact hsquare_equivariant _)
    (by
      intro u hu
      apply Subtype.ext
      exact hsquare_anisotropic _ hu)
    hsquareU_surjective
    (hU_internal_spectrum.imp_right (by
      rintro ⟨i, j, s, hij, _hvalue, hseed⟩
      exact ⟨i, j, s, hij, hseed⟩))
  have hV_monomial := lemma12_restricted_square_monomial
    n (by omega) xiV S mu nu hmu hmu_order
    vCoordinates centerCoordinates hvCoordinates hcenterCoordinates
    vBasis centerBasis hvBasis_eigen hcenterBasis_eigen
    (fun v : V => squareMap
      (v : Additive (LowerCentralFactor P 0)))
    bracketV (by simpa using hsquare_zero)
    (by
      intro v w
      change squareMap
          ((v : Additive (LowerCentralFactor P 0)) + w) = _
      simpa [bracketV] using hsquare_add
        (v : Additive (LowerCentralFactor P 0))
        (w : Additive (LowerCentralFactor P 0)))
    (by
      intro v
      change squareMap
          ((xiV v : V) : Additive (LowerCentralFactor P 0)) = _
      rw [hxiV_val]
      exact hsquare_equivariant _)
    (by
      intro v hv
      apply Subtype.ext
      exact hsquare_anisotropic _ hv)
    hsquareV_surjective
    (hV_internal_spectrum.imp_right (by
      rintro ⟨i, j, s, hij, _hvalue, hseed⟩
      exact ⟨i, j, s, hij, hseed⟩))
  let K := BinaryGaloisField n
  have hcrossExpansion :
      ∃ crossCoeff : Fin n → Fin n → K,
        ∀ a b : K,
          centerCoordinates.symm
              (crossBracket (uCoordinates a) (vCoordinates b)) =
            ∑ i : Fin n, ∑ j : Fin n,
              crossCoeff i j * a ^ (2 ^ (i : ℕ)) *
                b ^ (2 ^ (j : ℕ)) := by
    let crossCoordinate : K →ₗ[ZMod 2] K →ₗ[ZMod 2] K :=
      { toFun := fun a =>
          { toFun := fun b => centerCoordinates.symm
              (crossBracket (uCoordinates a) (vCoordinates b))
            map_add' := by
              intro b c
              simp
            map_smul' := by
              intro c b
              simp }
        map_add' := by
          intro a b
          apply LinearMap.ext
          intro c
          simp
        map_smul' := by
          intro c a
          apply LinearMap.ext
          intro b
          simp }
    simpa [K, crossCoordinate] using
      (PFAppendixIII.frobeniusBilinear_expansion n (by omega) crossCoordinate)
  obtain ⟨crossCoeff, hcrossExpansion⟩ := hcrossExpansion
  have hcrossCoefficientSupport :
      ∀ i j : Fin n, crossCoeff i j ≠ 0 →
        lambda ^ (2 ^ (i : ℕ)) * mu ^ (2 ^ (j : ℕ)) = nu := by
    let sigma : K ≃ₐ[ZMod 2] K :=
      FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
    have hsigma_order : orderOf sigma = n := by
      rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
        GaloisField.finrank 2 (by omega : n ≠ 0)]
    let fhom (i : Fin n) : K →* K := (sigma ^ (i : ℕ)).toMonoidHom
    have hfhom : Function.Injective fhom := by
      intro i j hij
      have hp : sigma ^ (i : ℕ) = sigma ^ (j : ℕ) := by
        apply AlgEquiv.ext
        intro x
        exact DFunLike.congr_fun hij x
      have hmod := pow_eq_pow_iff_modEq.mp hp
      rw [hsigma_order] at hmod
      exact Fin.ext (hmod.eq_of_lt_of_lt i.isLt j.isLt)
    have hfun :
        LinearIndependent K (fun i : Fin n => (fhom i : K → K)) :=
      (linearIndependent_monoidHom K K).comp fhom hfhom
    have hfrob_apply (i : Fin n) (x : K) :
        (fhom i : K → K) x = x ^ (2 ^ (i : ℕ)) := by
      change (sigma ^ (i : ℕ)) x = _
      rw [AlgEquiv.coe_pow,
        FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
      simp [ZMod.card]
    have hcoordinate_equivariant (a b : K) :
        centerCoordinates.symm
            (crossBracket (uCoordinates (lambda * a))
              (vCoordinates (mu * b))) =
          nu * centerCoordinates.symm
            (crossBracket (uCoordinates a) (vCoordinates b)) := by
      apply centerCoordinates.injective
      calc
        centerCoordinates
            (centerCoordinates.symm
              (crossBracket (uCoordinates (lambda * a))
                (vCoordinates (mu * b)))) =
            crossBracket (uCoordinates (lambda * a))
              (vCoordinates (mu * b)) := centerCoordinates.apply_symm_apply _
        _ = crossBracket (xiU (uCoordinates a)) (xiV (vCoordinates b)) := by
          rw [huCoordinates, hvCoordinates]
        _ = S (crossBracket (uCoordinates a) (vCoordinates b)) :=
          hcross_equivariant _ _
        _ = S (centerCoordinates
            (centerCoordinates.symm
              (crossBracket (uCoordinates a) (vCoordinates b)))) := by
          rw [centerCoordinates.apply_symm_apply]
        _ = centerCoordinates
            (nu * centerCoordinates.symm
              (crossBracket (uCoordinates a) (vCoordinates b))) :=
          hcenterCoordinates _
    have houter_eq (a b : K) :
        (∑ i : Fin n,
            (∑ j : Fin n, crossCoeff i j *
              lambda ^ (2 ^ (i : ℕ)) * mu ^ (2 ^ (j : ℕ)) *
                b ^ (2 ^ (j : ℕ))) * a ^ (2 ^ (i : ℕ))) =
          ∑ i : Fin n,
            (∑ j : Fin n, nu * crossCoeff i j *
              b ^ (2 ^ (j : ℕ))) * a ^ (2 ^ (i : ℕ)) := by
      calc
        (∑ i : Fin n,
            (∑ j : Fin n, crossCoeff i j *
              lambda ^ (2 ^ (i : ℕ)) * mu ^ (2 ^ (j : ℕ)) *
                b ^ (2 ^ (j : ℕ))) * a ^ (2 ^ (i : ℕ))) =
            centerCoordinates.symm
              (crossBracket (uCoordinates (lambda * a))
                (vCoordinates (mu * b))) := by
          rw [hcrossExpansion]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [mul_pow, mul_pow]
          ring
        _ = nu * centerCoordinates.symm
              (crossBracket (uCoordinates a) (vCoordinates b)) :=
          hcoordinate_equivariant a b
        _ = ∑ i : Fin n,
            (∑ j : Fin n, nu * crossCoeff i j *
              b ^ (2 ^ (j : ℕ))) * a ^ (2 ^ (i : ℕ)) := by
          rw [hcrossExpansion, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _hj
          ring
    have houter_coeff (i : Fin n) (b : K) :
        (∑ j : Fin n, crossCoeff i j *
            lambda ^ (2 ^ (i : ℕ)) * mu ^ (2 ^ (j : ℕ)) *
              b ^ (2 ^ (j : ℕ))) =
          ∑ j : Fin n, nu * crossCoeff i j *
            b ^ (2 ^ (j : ℕ)) := by
      let g : Fin n → K := fun i =>
        (∑ j : Fin n, crossCoeff i j *
            lambda ^ (2 ^ (i : ℕ)) * mu ^ (2 ^ (j : ℕ)) *
              b ^ (2 ^ (j : ℕ))) -
          ∑ j : Fin n, nu * crossCoeff i j *
            b ^ (2 ^ (j : ℕ))
      have hg : ∑ i : Fin n, g i • (fhom i : K → K) = 0 := by
        funext a
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
          smul_eq_mul, g, hfrob_apply, sub_mul]
        rw [Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr (houter_eq a b)
      exact sub_eq_zero.mp
        (Fintype.linearIndependent_iff.mp hfun g hg i)
    intro i j hij
    let g : Fin n → K := fun j =>
      crossCoeff i j * lambda ^ (2 ^ (i : ℕ)) *
          mu ^ (2 ^ (j : ℕ)) -
        nu * crossCoeff i j
    have hg : ∑ j : Fin n, g j • (fhom j : K → K) = 0 := by
      funext b
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul, g, hfrob_apply, sub_mul]
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (houter_coeff i b)
    have hcoeff := Fintype.linearIndependent_iff.mp hfun g hg j
    apply mul_left_cancel₀ hij
    simpa [g, mul_assoc, mul_comm, mul_left_comm] using sub_eq_zero.mp hcoeff
  let typeBQuadraticData : Prop :=
    Lemma12TypeBActorQuadraticData
      (lowerCentralFactorLinearAut xi 0) S n squareMap
  let typeCQuadraticData : Prop :=
    ∃ (theta : K ≃+* K) (epsilon : K)
        (quotientCoordinates :
          (K × K) ≃ₗ[ZMod 2] Additive (LowerCentralFactor P 0))
        (finalCenterCoordinates :
          K ≃ₗ[ZMod 2] Additive (LowerCentralFactor P 1)),
      epsilon ≠ 0 ∧
      (∃ r : ℕ, Odd r ∧ 0 < r ∧ ∀ x : K, theta^[r] x = x) ∧
      (∀ x : K, theta (theta (x ^ 2)) = x) ∧
      (∀ rho : K, epsilon ≠ rho⁻¹ + theta (rho ^ 2) * rho) ∧
      ∀ a b : K,
        finalCenterCoordinates.symm
            (squareMap (quotientCoordinates (a, b))) =
          a * theta a +
            epsilon * a ^ (2 ^ (n - 1)) * theta (b ^ 2) + b ^ 2
  let typeDQuadraticData : Prop :=
    ∃ (theta : K ≃+* K) (epsilon : K)
        (quotientCoordinates :
          (K × K) ≃ₗ[ZMod 2] Additive (LowerCentralFactor P 0))
        (finalCenterCoordinates :
          K ≃ₗ[ZMod 2] Additive (LowerCentralFactor P 1)),
      epsilon ≠ 0 ∧
      (∀ x : K, theta^[5] x = x) ∧
      (∃ x : K, theta x ≠ x) ∧
      (∀ rho : K,
        epsilon ≠ rho⁻¹ + (theta^[4]) rho * theta rho * rho⁻¹) ∧
      ∀ a b : K,
        finalCenterCoordinates.symm
            (squareMap (quotientCoordinates (a, b))) =
          a * theta a +
            epsilon * (theta^[3]) a * theta b + b * (theta^[2]) b
  have hcoordinateEndpoints :
      (typeBQuadraticData →
        Lemma12TypeBActorCoordinates
          (lowerCentralFactorLinearAut xi 0) S n squareMap) ∧
      (typeCQuadraticData → IsSuzukiTwoTypeC (⊤ : Subgroup P)) ∧
      (typeDQuadraticData → IsSuzukiTwoTypeD (⊤ : Subgroup P)) := by
    have hcoordinatesOfQuadratic
        (quotientCoordinates :
          (K × K) ≃ₗ[ZMod 2] Additive (LowerCentralFactor P 0))
        (finalCenterCoordinates :
          K ≃ₗ[ZMod 2] Additive (LowerCentralFactor P 1))
        (q : K × K → K)
        (hq : ∀ a b : K,
          finalCenterCoordinates.symm
              (squareMap (quotientCoordinates (a, b))) = q (a, b))
        (target : (K × K) →ₗ[ZMod 2] (K × K) →ₗ[ZMod 2] K)
        (htarget : ∀ x : K × K, target x x = q x) :
        ∃ tripleLift : K → K → K → P,
          tripleLift 0 0 0 = 1 ∧
          (∀ x : P, ∃ z a b : K, x = tripleLift z a b) ∧
          (∀ z a b w c d : K,
            tripleLift z a b = tripleLift w c d →
              z = w ∧ a = c ∧ b = d) ∧
          ∀ z a b w c d : K,
            tripleLift z a b * tripleLift w c d =
              tripleLift (z + w + target (a, b) (c, d))
                (a + c) (b + d) := by
      let factorZeroCoordinates : LowerCentralFactor P 0 ≃*
          Multiplicative (K × K) :=
        (MulEquiv.multiplicativeAdditive _).symm.trans
          quotientCoordinates.symm.toAddEquiv.toMultiplicative
      let pi : P →* Multiplicative (K × K) :=
        factorZeroCoordinates.toMonoidHom.comp q0
      have hpi_surj : Function.Surjective pi :=
        factorZeroCoordinates.surjective.comp hq0_surj
      let factorOneEquiv : LowerCentralFactor P 1 ≃*
          (⊤ : Subgroup P).lowerCentralSeries 1 :=
        (QuotientGroup.quotientMulEquivOfEq hkernel1_bot).trans
          (QuotientGroup.quotientBot (G := (⊤ : Subgroup P).lowerCentralSeries 1))
      let centerCoordinatesMul : Multiplicative K ≃*
          LowerCentralFactor P 1 :=
        finalCenterCoordinates.toAddEquiv.toMultiplicative.trans
          (MulEquiv.multiplicativeAdditive _)
      let iota : Multiplicative K →* P :=
        ((⊤ : Subgroup P).lowerCentralSeries 1).subtype.comp
          (factorOneEquiv.toMonoidHom.comp
            centerCoordinatesMul.toMonoidHom)
      have hiota : Function.Injective iota := by
        intro z w h
        apply centerCoordinatesMul.injective
        apply factorOneEquiv.injective
        apply Subtype.ext
        exact h
      have hiota_range : iota.range = B := by
        rw [← hL1_eq_B]
        ext p
        constructor
        · rintro ⟨z, rfl⟩
          exact (factorOneEquiv (centerCoordinatesMul z)).property
        · intro hp
          let p1 : (⊤ : Subgroup P).lowerCentralSeries 1 := ⟨p, hp⟩
          let z : Multiplicative K :=
            centerCoordinatesMul.symm (factorOneEquiv.symm p1)
          refine ⟨z, ?_⟩
          change ((factorOneEquiv (centerCoordinatesMul z) :
            (⊤ : Subgroup P).lowerCentralSeries 1) : P) = p
          have hz :
              centerCoordinatesMul z = factorOneEquiv.symm p1 := by
            simp [z]
          rw [hz]
          exact congrArg Subtype.val (factorOneEquiv.apply_symm_apply p1)
      have hpi_ker : pi.ker = B := by
        rw [← hq0_ker]
        ext p
        change factorZeroCoordinates (q0 p) = 1 ↔ q0 p = 1
        exact factorZeroCoordinates.map_eq_one_iff
      have hexact : iota.range = pi.ker :=
        hiota_range.trans hpi_ker.symm
      have hcentral : iota.range ≤ Subgroup.center P := by
        rw [hiota_range]
        exact hB_le_center
      have hq_forward (x : K × K) :
          finalCenterCoordinates (q x) =
            squareMap (quotientCoordinates x) := by
        apply finalCenterCoordinates.symm.injective
        rw [finalCenterCoordinates.symm_apply_apply]
        exact (hq x.1 x.2).symm
      have hsquare_extension (x : P) :
          iota (Multiplicative.ofAdd (q (pi x).toAdd)) = x ^ 2 := by
        let x0 : (⊤ : Subgroup P).lowerCentralSeries 0 := Subgroup.topEquiv.symm x
        have hx2mem : x ^ 2 ∈ (⊤ : Subgroup P).lowerCentralSeries 1 := by
          rw [hL1_eq_B]
          exact hsquares_le_B (Subgroup.subset_closure ⟨x, rfl⟩)
        have hpi_coordinates :
            quotientCoordinates (pi x).toAdd =
              Additive.ofMul (q0 x) := by
          change quotientCoordinates
              (quotientCoordinates.symm (Additive.ofMul (q0 x))) = _
          exact quotientCoordinates.apply_symm_apply _
        have hcenter_coordinates :
            finalCenterCoordinates (q (pi x).toAdd) =
              Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel P 1)
                  ⟨x ^ 2, hx2mem⟩) := by
          calc
            finalCenterCoordinates (q (pi x).toAdd) =
                squareMap (quotientCoordinates (pi x).toAdd) :=
              hq_forward _
            _ = squareMap (Additive.ofMul (q0 x)) := by
              rw [hpi_coordinates]
            _ = Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel P 1)
                  ⟨x ^ 2, hx2mem⟩) := by
              change squareMap
                  (Additive.ofMul
                    (QuotientGroup.mk' (lowerCentralFactorKernel P 0) x0)) = _
              exact hsquare_mk x0 hx2mem
        have hcenter_mul :
            centerCoordinatesMul
                (Multiplicative.ofAdd (q (pi x).toAdd)) =
              QuotientGroup.mk' (lowerCentralFactorKernel P 1)
                ⟨x ^ 2, hx2mem⟩ := by
          change (finalCenterCoordinates (q (pi x).toAdd)).toMul = _
          exact congrArg Additive.toMul hcenter_coordinates
        have hfactorOne_mk (y : (⊤ : Subgroup P).lowerCentralSeries 1) :
            factorOneEquiv
                (QuotientGroup.mk' (lowerCentralFactorKernel P 1) y) = y := by
          have hmk :
              (QuotientGroup.quotientMulEquivOfEq hkernel1_bot)
                  ((QuotientGroup.mk'
                    (lowerCentralFactorKernel P 1)) y) =
                (QuotientGroup.mk y :
                  (⊤ : Subgroup P).lowerCentralSeries 1 ⧸
                    (⊥ : Subgroup ((⊤ : Subgroup P).lowerCentralSeries 1))) := by
            simpa only [QuotientGroup.mk'_apply] using
              (QuotientGroup.quotientMulEquivOfEq_mk hkernel1_bot y)
          calc
            factorOneEquiv
                ((QuotientGroup.mk'
                  (lowerCentralFactorKernel P 1)) y) =
              QuotientGroup.quotientBot
                ((QuotientGroup.quotientMulEquivOfEq hkernel1_bot)
                  ((QuotientGroup.mk'
                    (lowerCentralFactorKernel P 1)) y)) := by
                rfl
            _ = QuotientGroup.quotientBot
                (QuotientGroup.mk y :
                  (⊤ : Subgroup P).lowerCentralSeries 1 ⧸
                    (⊥ : Subgroup ((⊤ : Subgroup P).lowerCentralSeries 1))) := by
                rw [hmk]
            _ = y := by
              rfl
        change ((factorOneEquiv
          (centerCoordinatesMul
            (Multiplicative.ofAdd (q (pi x).toAdd))) :
              (⊤ : Subgroup P).lowerCentralSeries 1) : P) = x ^ 2
        rw [hcenter_mul, hfactorOne_mk]
      obtain ⟨pairLift, hpairOne, hpairSurj, hpairInj, hpairMul⟩ :=
        exists_coordinates_with_prescribed_bilinear_defect
          iota pi hiota hpi_surj hexact hcentral q hsquare_extension
            target htarget
      let tripleLift : K → K → K → P :=
        fun z a b => pairLift (a, b) z
      refine ⟨tripleLift, ?_, ?_, ?_, ?_⟩
      · change pairLift (0, 0) 0 = 1
        rw [show (0, 0) = (0 : K × K) by ext <;> rfl]
        exact hpairOne
      · intro x
        obtain ⟨ab, z, hx⟩ := hpairSurj x
        exact ⟨z, ab.1, ab.2, by simpa [tripleLift] using hx⟩
      · intro z a b w c d h
        have h' := hpairInj (a, b) z (c, d) w h
        exact ⟨h'.2, congrArg Prod.fst h'.1, congrArg Prod.snd h'.1⟩
      · intro z a b w c d
        exact hpairMul (a, b) z (c, d) w
    have htypeBEndpoint :
        typeBQuadraticData →
          Lemma12TypeBActorCoordinates
            (lowerCentralFactorLinearAut xi 0) S n squareMap := by
      rintro ⟨theta, epsilon, quotientCoordinates,
        finalCenterCoordinates, lambdaUnit, hepsilon, hperiod,
        hanisotropic, hq, hlambdaOrder,
        hquotientActor, hcenterActor⟩
      let q : K × K → K := fun x =>
        x.1 * theta x.1 + epsilon * x.1 * theta x.2 +
          x.2 * theta x.2
      let target : (K × K) →ₗ[ZMod 2] (K × K) →ₗ[ZMod 2] K :=
        { toFun := fun x =>
            { toFun := fun y =>
                x.1 * theta y.1 + epsilon * x.1 * theta y.2 +
                  x.2 * theta y.2
              map_add' := by
                intro y z
                simp only [Prod.fst_add, Prod.snd_add, map_add]
                ring
              map_smul' := by
                intro c y
                have hc : c = 0 ∨ c = 1 := by
                  fin_cases c
                  · left
                    rfl
                  · right
                    rfl
                rcases hc with rfl | rfl
                · simp
                · simp only [RingHom.id_apply, one_smul] }
          map_add' := by
            intro x y
            apply LinearMap.ext
            intro z
            change
              (x.1 + y.1) * theta z.1 +
                  epsilon * (x.1 + y.1) * theta z.2 +
                  (x.2 + y.2) * theta z.2 =
                (x.1 * theta z.1 + epsilon * x.1 * theta z.2 +
                    x.2 * theta z.2) +
                  (y.1 * theta z.1 + epsilon * y.1 * theta z.2 +
                    y.2 * theta z.2)
            ring
          map_smul' := by
            intro c x
            have hc : c = 0 ∨ c = 1 := by
              fin_cases c
              · left
                rfl
              · right
                rfl
            rcases hc with rfl | rfl
            · apply LinearMap.ext
              intro y
              simp
            · apply LinearMap.ext
              intro y
              simp only [RingHom.id_apply, one_smul] }
      have htarget (x : K × K) : target x x = q x := rfl
      obtain ⟨tripleLift, hone, hsurj, hinj, hmul⟩ :=
        hcoordinatesOfQuadratic quotientCoordinates finalCenterCoordinates
          q hq target htarget
      refine ⟨theta, epsilon, tripleLift,
        (fun a b c d => target (a, b) (c, d)),
        quotientCoordinates, finalCenterCoordinates, lambdaUnit,
        hepsilon, hperiod, hanisotropic, ?_, ?_, ?_, ?_, hone,
        hsurj, hinj, hmul, hq, hlambdaOrder, hquotientActor, hcenterActor⟩
      · intro a b e f c d
        simpa using congrArg (fun L => L (c, d))
          (target.map_add (a, b) (e, f))
      · intro a b e f c d
        exact (target (a, b)).map_add (e, f) (c, d)
      · intro a b
        exact htarget (a, b)
      · intro c a b
        trivial
    have htypeCEndpoint :
        typeCQuadraticData → IsSuzukiTwoTypeC (⊤ : Subgroup P) := by
      rintro ⟨theta, epsilon, quotientCoordinates,
        finalCenterCoordinates, hepsilon, hperiod, hthetaSquare, havoid, hq⟩
      let q : K × K → K := fun x =>
        x.1 * theta x.1 +
          epsilon * x.1 ^ (2 ^ (n - 1)) * theta (x.2 ^ 2) + x.2 ^ 2
      let target : (K × K) →ₗ[ZMod 2] (K × K) →ₗ[ZMod 2] K :=
        { toFun := fun x =>
            { toFun := fun y =>
                x.1 * theta y.1 +
                  epsilon * x.1 ^ (2 ^ (n - 1)) * theta (y.2 ^ 2) +
                  x.2 * y.2
              map_add' := by
                intro y z
                simp only [Prod.fst_add, Prod.snd_add, add_pow_char, map_add]
                ring
              map_smul' := by
                intro c y
                have hc : c = 0 ∨ c = 1 := by
                  fin_cases c
                  · left
                    rfl
                  · right
                    rfl
                rcases hc with rfl | rfl
                · simp
                · simp only [RingHom.id_apply, one_smul] }
          map_add' := by
            intro x y
            apply LinearMap.ext
            intro z
            change
              (x.1 + y.1) * theta z.1 +
                  epsilon * (x.1 + y.1) ^ (2 ^ (n - 1)) *
                    theta (z.2 ^ 2) +
                  (x.2 + y.2) * z.2 =
                (x.1 * theta z.1 +
                    epsilon * x.1 ^ (2 ^ (n - 1)) * theta (z.2 ^ 2) +
                    x.2 * z.2) +
                  (y.1 * theta z.1 +
                    epsilon * y.1 ^ (2 ^ (n - 1)) * theta (z.2 ^ 2) +
                    y.2 * z.2)
            rw [add_pow_char_pow]
            ring
          map_smul' := by
            intro c x
            have hc : c = 0 ∨ c = 1 := by
              fin_cases c
              · left
                rfl
              · right
                rfl
            rcases hc with rfl | rfl
            · apply LinearMap.ext
              intro y
              simp
            · apply LinearMap.ext
              intro y
              simp only [RingHom.id_apply, one_smul] }
      have htarget (x : K × K) : target x x = q x := by
        change
          x.1 * theta x.1 +
              epsilon * x.1 ^ (2 ^ (n - 1)) * theta (x.2 ^ 2) +
              x.2 * x.2 =
            x.1 * theta x.1 +
              epsilon * x.1 ^ (2 ^ (n - 1)) * theta (x.2 ^ 2) +
              x.2 ^ 2
        ring
      obtain ⟨tripleLift, hone, hsurj, hinj, hmul⟩ :=
        hcoordinatesOfQuadratic quotientCoordinates finalCenterCoordinates
          q hq target htarget
      refine ⟨n, by omega, theta, epsilon, tripleLift,
        hepsilon, hperiod, hthetaSquare, havoid, ?_, ?_, ?_, ?_, ?_⟩
      · intro z a b
        trivial
      · exact hone
      · intro x _hx
        exact hsurj x
      · exact hinj
      · intro z a b w c d
        simpa [target, add_assoc] using hmul z a b w c d
    have htypeDEndpoint :
        typeDQuadraticData → IsSuzukiTwoTypeD (⊤ : Subgroup P) := by
      rintro ⟨theta, epsilon, quotientCoordinates,
        finalCenterCoordinates, hepsilon, hperiod, hnontrivial, havoid, hq⟩
      let q : K × K → K := fun x =>
        x.1 * theta x.1 +
          epsilon * (theta^[3]) x.1 * theta x.2 +
          x.2 * (theta^[2]) x.2
      let target : (K × K) →ₗ[ZMod 2] (K × K) →ₗ[ZMod 2] K :=
        { toFun := fun x =>
            { toFun := fun y =>
                x.1 * theta y.1 +
                  epsilon * (theta^[3]) x.1 * theta y.2 +
                  x.2 * (theta^[2]) y.2
              map_add' := by
                intro y z
                simp only [Prod.fst_add, Prod.snd_add,
                  Function.iterate_succ_apply, Function.iterate_zero_apply, map_add]
                ring
              map_smul' := by
                intro c y
                have hc : c = 0 ∨ c = 1 := by
                  fin_cases c
                  · left
                    rfl
                  · right
                    rfl
                rcases hc with rfl | rfl
                · simp
                · simp only [RingHom.id_apply, one_smul] }
          map_add' := by
            intro x y
            apply LinearMap.ext
            intro z
            change
              (x.1 + y.1) * theta z.1 +
                  epsilon * (theta^[3]) (x.1 + y.1) * theta z.2 +
                  (x.2 + y.2) * (theta^[2]) z.2 =
                (x.1 * theta z.1 +
                    epsilon * (theta^[3]) x.1 * theta z.2 +
                    x.2 * (theta^[2]) z.2) +
                  (y.1 * theta z.1 +
                    epsilon * (theta^[3]) y.1 * theta z.2 +
                    y.2 * (theta^[2]) z.2)
            simp only [Function.iterate_succ_apply,
              Function.iterate_zero_apply, map_add]
            ring
          map_smul' := by
            intro c x
            have hc : c = 0 ∨ c = 1 := by
              fin_cases c
              · left
                rfl
              · right
                rfl
            rcases hc with rfl | rfl
            · apply LinearMap.ext
              intro y
              simp
            · apply LinearMap.ext
              intro y
              simp only [RingHom.id_apply, one_smul] }
      have htarget (x : K × K) : target x x = q x := rfl
      obtain ⟨tripleLift, hone, hsurj, hinj, hmul⟩ :=
        hcoordinatesOfQuadratic quotientCoordinates finalCenterCoordinates
          q hq target htarget
      refine ⟨n, by omega, theta, epsilon, tripleLift,
        hepsilon, hperiod, hnontrivial, havoid, ?_, ?_, ?_, ?_, ?_⟩
      · intro z a b
        trivial
      · exact hone
      · intro x _hx
        exact hsurj x
      · exact hinj
      · intro z a b w c d
        simpa [target, add_assoc] using hmul z a b w c d
    exact ⟨htypeBEndpoint, htypeCEndpoint, htypeDEndpoint⟩

  have htypeBOfActorCoordinates
      (hform : Lemma12TypeBActorCoordinates
        (lowerCentralFactorLinearAut xi 0) S n squareMap) :
      IsSuzukiTwoTypeB (⊤ : Subgroup P) := by
    rcases hform with
      ⟨theta, epsilon, tripleLift, cocycle, _quotientCoordinates,
        _centerCoordinates, _lambdaUnit, hepsilon, hperiod, hanisotropic,
        haddLeft, haddRight, hdiag, hmem, hone, hsurj, hinj, hmul,
        _hsquare, _hlambdaOrder, _hquotientActor, _hcenterActor⟩
    refine ⟨n, by omega, theta, epsilon, tripleLift, cocycle,
      hepsilon, hperiod, hanisotropic, haddLeft, haddRight, hdiag,
      hmem, hone, ?_, hinj, hmul⟩
    intro x _hx
    exact hsurj x

  have hpackActorData
      (hform : Lemma12TypeBNormalizedData xi n U V bracket squareMap ∨
        Lemma12TypeCNormalizedData xi n U V bracket squareMap) :
      Lemma12ChainActorData g A B := by
    refine ⟨k, n, xi, q0, U, V, bracket, squareMap, hxi_actor, hn,
      hq0_ker, hq0_surj, ?_, ?_, hUV, hL1_eq_B, hkernel1_bot,
      hbracket_mk, hsquare_mk, hform⟩
    · intro p
      rfl
    · intro u
      rfl
  have hpackTypeBActorBranch
      (hform : Lemma12TypeBActorCoordinates
        (lowerCentralFactorLinearAut xi 0) S n squareMap) :
      Lemma12TypeBActorBranchData X P (g ^ (2 ^ k)) B := by
    refine ⟨n, xi, q0, squareMap, (by omega), hxi_actor, hq0_ker, hq0_surj,
      ?_, hL1_eq_B, hkernel1_bot, hB_le_center, hB_card,
      hfactor0_card, hinvolution_card, ?_⟩
    · intro p
      have h := hq0_equivariant (g ^ (2 ^ k)) p
      rw [← hxi_actor] at h
      exact h
    · simpa only [S] using hform
  have hpackCriterionData
      (hcriterion :
        (∃ e : U ≃ₗ[ZMod 2] V, ∀ u : U, e (xiU u) = xiV (e u)) →
          Lemma12TypeBActorBranchData X P (g ^ (2 ^ k)) B) :
      Lemma12IsomorphicSummandCriterionData X P B := by
    exact ⟨n, g ^ (2 ^ k), xi, q0, U, V, xiU, xiV, hn, hxi_actor,
      hq0_ker, hq0_surj, hq0_equivariant, hUV, hxiU_val, hxiV_val,
      hxiU_irreducible, hxiV_irreducible, hU_card, hV_card,
      hB_le_center, hB_card, hfactor0_card, hinvolution_card, hcriterion⟩
  have hcanonicalEigenRelation
      (hiso : ∃ e : U ≃ₗ[ZMod 2] V,
        ∀ u : U, e (xiU u) = xiV (e u)) :
      ∃ t : Fin n, lambda ^ (2 ^ (t : ℕ)) = mu := by
    rcases hiso with ⟨e, he⟩
    let f : K ≃ₗ[ZMod 2] K :=
      uCoordinates.trans (e.trans vCoordinates.symm)
    apply lemma12_eigenvalue_frobenius_conjugate_of_equivariant_linearEquiv
      n (by omega) lambda mu f
    intro a
    change vCoordinates.symm (e (uCoordinates (lambda * a))) =
      mu * vCoordinates.symm (e (uCoordinates a))
    rw [← huCoordinates, he]
    let v : V := e (uCoordinates a)
    have hv := hvCoordinates (vCoordinates.symm v)
    rw [vCoordinates.apply_symm_apply] at hv
    apply vCoordinates.injective
    rw [vCoordinates.apply_symm_apply, hv]
  have hcanonicalEigenRelationSymm
      (hiso : ∃ e : U ≃ₗ[ZMod 2] V,
        ∀ u : U, e (xiU u) = xiV (e u)) :
      ∃ t : Fin n, mu ^ (2 ^ (t : ℕ)) = lambda := by
    rcases hiso with ⟨e, he⟩
    let f : K ≃ₗ[ZMod 2] K :=
      vCoordinates.trans (e.symm.trans uCoordinates.symm)
    apply lemma12_eigenvalue_frobenius_conjugate_of_equivariant_linearEquiv
      n (by omega) mu lambda f
    intro a
    change uCoordinates.symm (e.symm (vCoordinates (mu * a))) =
      lambda * uCoordinates.symm (e.symm (vCoordinates a))
    rw [← hvCoordinates]
    have heSymm (v : V) : e.symm (xiV v) = xiU (e.symm v) := by
      apply e.injective
      rw [e.apply_symm_apply, he, e.apply_symm_apply]
    rw [heSymm]
    let u : U := e.symm (vCoordinates a)
    have hu := huCoordinates (uCoordinates.symm u)
    rw [uCoordinates.apply_symm_apply] at hu
    apply uCoordinates.injective
    rw [uCoordinates.apply_symm_apply, hu]
  rcases hU_monomial with hUlinear | hUpair
  · rcases hV_monomial with hVlinear | hVpair
    · have hlinearLinearCase :
          typeBQuadraticData ∧
            Lemma12TypeBNormalizedData xi n U V bracket squareMap := by
        rcases hUlinear with
          ⟨_iu, _su, _cu, hbracketUZero, _hUeigen, _hcu, _hUformula⟩
        rcases hVlinear with
          ⟨_iv, _sv, _cv, hbracketVZero, _hVeigen, _hcv, _hVformula⟩
        let sigma : K ≃ₐ[ZMod 2] K :=
          FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
        have hnormalizedSquares :
            ∃ (uNorm : K ≃ₗ[ZMod 2] ↥U)
                (vNorm : K ≃ₗ[ZMod 2] ↥V),
              (∀ a : K,
                centerCoordinates.symm (squareMap (uNorm a :
                  Additive (LowerCentralFactor P 0))) = a ^ 2) ∧
              ∀ b : K,
                centerCoordinates.symm (squareMap (vNorm b :
                  Additive (LowerCentralFactor P 0))) = b ^ 2 := by
          have hbracketU_zero (a b : K) :
              bracket (uCoordinates a : Additive (LowerCentralFactor P 0))
                  (uCoordinates b : Additive (LowerCentralFactor P 0)) = 0 := by
            change bracketU (uCoordinates a) (uCoordinates b) = 0
            simp [hbracketUZero]
          have hbracketV_zero (a b : K) :
              bracket (vCoordinates a : Additive (LowerCentralFactor P 0))
                  (vCoordinates b : Additive (LowerCentralFactor P 0)) = 0 := by
            change bracketV (vCoordinates a) (vCoordinates b) = 0
            simp [hbracketVZero]
          let uSquare : K →ₗ[ZMod 2] K :=
            { toFun := fun a => centerCoordinates.symm
                (squareMap (uCoordinates a :
                  Additive (LowerCentralFactor P 0)))
              map_add' := by
                intro a b
                rw [uCoordinates.map_add]
                change centerCoordinates.symm
                    (squareMap ((uCoordinates a :
                      Additive (LowerCentralFactor P 0)) +
                    (uCoordinates b : Additive (LowerCentralFactor P 0)))) = _
                rw [hsquare_add, hbracketU_zero, add_zero, map_add]
              map_smul' := by
                intro c a
                have hc : c = 0 ∨ c = 1 := by
                  fin_cases c
                  · left
                    rfl
                  · right
                    rfl
                rcases hc with rfl | rfl
                · simp [hsquare_zero]
                · simp only [RingHom.id_apply, one_smul] }
          let vSquare : K →ₗ[ZMod 2] K :=
            { toFun := fun b => centerCoordinates.symm
                (squareMap (vCoordinates b :
                  Additive (LowerCentralFactor P 0)))
              map_add' := by
                intro a b
                rw [vCoordinates.map_add]
                change centerCoordinates.symm
                    (squareMap ((vCoordinates a :
                      Additive (LowerCentralFactor P 0)) +
                    (vCoordinates b : Additive (LowerCentralFactor P 0)))) = _
                rw [hsquare_add, hbracketV_zero, add_zero, map_add]
              map_smul' := by
                intro c a
                have hc : c = 0 ∨ c = 1 := by
                  fin_cases c
                  · left
                    rfl
                  · right
                    rfl
                rcases hc with rfl | rfl
                · simp [hsquare_zero]
                · simp only [RingHom.id_apply, one_smul] }
          have huSquare_injective : Function.Injective uSquare := by
            intro a b hab
            have hzero : uSquare (a - b) = 0 := by
              rw [map_sub, hab, sub_self]
            have hsquareZero :
                squareMap (uCoordinates (a - b) :
                  Additive (LowerCentralFactor P 0)) = 0 := by
              simpa [uSquare] using congrArg centerCoordinates hzero
            have huZero : uCoordinates (a - b) = 0 := by
              apply Subtype.ext
              exact hsquare_anisotropic _ hsquareZero
            have habZero : a - b = 0 := by
              apply uCoordinates.injective
              simpa using huZero
            exact sub_eq_zero.mp habZero
          have hvSquare_injective : Function.Injective vSquare := by
            intro a b hab
            have hzero : vSquare (a - b) = 0 := by
              rw [map_sub, hab, sub_self]
            have hsquareZero :
                squareMap (vCoordinates (a - b) :
                  Additive (LowerCentralFactor P 0)) = 0 := by
              simpa [vSquare] using congrArg centerCoordinates hzero
            have hvZero : vCoordinates (a - b) = 0 := by
              apply Subtype.ext
              exact hsquare_anisotropic _ hsquareZero
            have habZero : a - b = 0 := by
              apply vCoordinates.injective
              simpa using hvZero
            exact sub_eq_zero.mp habZero
          have huSquare_surjective : Function.Surjective uSquare := by
            intro z
            obtain ⟨u, hu⟩ := hsquareU_surjective (centerCoordinates z)
            refine ⟨uCoordinates.symm u, ?_⟩
            change centerCoordinates.symm
                (squareMap (uCoordinates (uCoordinates.symm u) :
                  Additive (LowerCentralFactor P 0))) = z
            rw [uCoordinates.apply_symm_apply]
            calc
              centerCoordinates.symm (squareMap (u :
                  Additive (LowerCentralFactor P 0))) =
                  centerCoordinates.symm (centerCoordinates z) :=
                congrArg centerCoordinates.symm hu
              _ = z := centerCoordinates.symm_apply_apply z
          have hvSquare_surjective : Function.Surjective vSquare := by
            intro z
            obtain ⟨v, hv⟩ := hsquareV_surjective (centerCoordinates z)
            refine ⟨vCoordinates.symm v, ?_⟩
            change centerCoordinates.symm
                (squareMap (vCoordinates (vCoordinates.symm v) :
                  Additive (LowerCentralFactor P 0))) = z
            rw [vCoordinates.apply_symm_apply]
            calc
              centerCoordinates.symm (squareMap (v :
                  Additive (LowerCentralFactor P 0))) =
                  centerCoordinates.symm (centerCoordinates z) :=
                congrArg centerCoordinates.symm hv
              _ = z := centerCoordinates.symm_apply_apply z
          let uSquareEquiv : K ≃ₗ[ZMod 2] K :=
            LinearEquiv.ofBijective uSquare
              ⟨huSquare_injective, huSquare_surjective⟩
          let vSquareEquiv : K ≃ₗ[ZMod 2] K :=
            LinearEquiv.ofBijective vSquare
              ⟨hvSquare_injective, hvSquare_surjective⟩
          let uNorm : K ≃ₗ[ZMod 2] ↥U :=
            (sigma.toLinearEquiv.trans uSquareEquiv.symm).trans uCoordinates
          let vNorm : K ≃ₗ[ZMod 2] ↥V :=
            (sigma.toLinearEquiv.trans vSquareEquiv.symm).trans vCoordinates
          refine ⟨uNorm, vNorm, ?_, ?_⟩
          · intro a
            change uSquareEquiv (uSquareEquiv.symm (sigma a)) = a ^ 2
            rw [uSquareEquiv.apply_symm_apply]
            rfl
          · intro b
            change vSquareEquiv (vSquareEquiv.symm (sigma b)) = b ^ 2
            rw [vSquareEquiv.apply_symm_apply]
            rfl
        obtain ⟨uNorm, vNorm, huNormSquare, hvNormSquare⟩ :=
          hnormalizedSquares
        let eta : K := sigma.symm nu
        have heta_nonzero : eta ≠ 0 := by
          intro heta
          have h := congrArg sigma heta
          apply hnu
          simpa [eta] using h
        have heta_square : eta ^ 2 = nu := by
          change sigma eta = nu
          exact sigma.apply_symm_apply nu
        have heta_order :
            orderOf (Units.mk0 eta heta_nonzero) = 2 ^ n - 1 := by
          let sigmaUnits : Kˣ →* Kˣ := Units.map sigma.toRingEquiv.toMonoidHom
          have hsigmaUnits : Function.Injective sigmaUnits :=
            Units.map_injective sigma.injective
          have hmap :
              sigmaUnits (Units.mk0 eta heta_nonzero) =
                Units.mk0 nu hnu := by
            apply Units.ext
            exact sigma.apply_symm_apply nu
          rw [← hnu_order, ← hmap]
          exact (orderOf_injective sigmaUnits hsigmaUnits _).symm
        have hnormalizedActors :
            (∀ a : K, xiU (uNorm a) = uNorm (eta * a)) ∧
              ∀ b : K, xiV (vNorm b) = vNorm (eta * b) := by
          have hbracketU_all (u v : U) :
              bracket (u : Additive (LowerCentralFactor P 0))
                  (v : Additive (LowerCentralFactor P 0)) = 0 := by
            change bracketU u v = 0
            simp [hbracketUZero]
          have hbracketV_all (u v : V) :
              bracket (u : Additive (LowerCentralFactor P 0))
                  (v : Additive (LowerCentralFactor P 0)) = 0 := by
            change bracketV u v = 0
            simp [hbracketVZero]
          have hsquareU_injective : Function.Injective
              (fun u : U => squareMap
                (u : Additive (LowerCentralFactor P 0))) := by
            intro u v huv
            change squareMap (u : Additive (LowerCentralFactor P 0)) =
              squareMap (v : Additive (LowerCentralFactor P 0)) at huv
            apply Subtype.ext
            have hsumzero :
                squareMap ((u : Additive (LowerCentralFactor P 0)) +
                  (v : Additive (LowerCentralFactor P 0))) = 0 := by
              rw [hsquare_add, huv, hbracketU_all,
                ZModModule.add_self, zero_add]
            have hsum := hsquare_anisotropic _ hsumzero
            exact (eq_neg_of_add_eq_zero_left hsum).trans
              (ZModModule.neg_eq_self _)
          have hsquareV_injective : Function.Injective
              (fun v : V => squareMap
                (v : Additive (LowerCentralFactor P 0))) := by
            intro u v huv
            change squareMap (u : Additive (LowerCentralFactor P 0)) =
              squareMap (v : Additive (LowerCentralFactor P 0)) at huv
            apply Subtype.ext
            have hsumzero :
                squareMap ((u : Additive (LowerCentralFactor P 0)) +
                  (v : Additive (LowerCentralFactor P 0))) = 0 := by
              rw [hsquare_add, huv, hbracketV_all,
                ZModModule.add_self, zero_add]
            have hsum := hsquare_anisotropic _ hsumzero
            exact (eq_neg_of_add_eq_zero_left hsum).trans
              (ZModModule.neg_eq_self _)
          have hcenterActor
              (z : Additive (LowerCentralFactor P 1)) :
              centerCoordinates.symm (S z) =
                nu * centerCoordinates.symm z := by
            calc
              centerCoordinates.symm (S z) =
                  centerCoordinates.symm
                    (S (centerCoordinates (centerCoordinates.symm z))) := by
                rw [centerCoordinates.apply_symm_apply]
              _ = centerCoordinates.symm
                    (centerCoordinates
                      (nu * centerCoordinates.symm z)) := by
                rw [hcenterCoordinates]
              _ = nu * centerCoordinates.symm z :=
                centerCoordinates.symm_apply_apply _
          constructor
          · intro a
            apply hsquareU_injective
            apply centerCoordinates.symm.injective
            have hactor := hsquare_xiU_pow 1 (uNorm a)
            simp only [pow_one] at hactor
            calc
              centerCoordinates.symm
                    (squareMap (xiU (uNorm a) :
                      Additive (LowerCentralFactor P 0))) =
                  centerCoordinates.symm
                    (S (squareMap (uNorm a :
                      Additive (LowerCentralFactor P 0)))) := by
                rw [hactor]
              _ = nu * centerCoordinates.symm
                    (squareMap (uNorm a :
                      Additive (LowerCentralFactor P 0))) :=
                hcenterActor _
              _ = nu * a ^ 2 := by rw [huNormSquare]
              _ = (eta * a) ^ 2 := by rw [mul_pow, heta_square]
              _ = centerCoordinates.symm
                    (squareMap (uNorm (eta * a) :
                      Additive (LowerCentralFactor P 0))) :=
                (huNormSquare _).symm
          · intro b
            apply hsquareV_injective
            apply centerCoordinates.symm.injective
            have hactor := hsquare_xiV_pow 1 (vNorm b)
            simp only [pow_one] at hactor
            calc
              centerCoordinates.symm
                    (squareMap (xiV (vNorm b) :
                      Additive (LowerCentralFactor P 0))) =
                  centerCoordinates.symm
                    (S (squareMap (vNorm b :
                      Additive (LowerCentralFactor P 0)))) := by
                rw [hactor]
              _ = nu * centerCoordinates.symm
                    (squareMap (vNorm b :
                      Additive (LowerCentralFactor P 0))) :=
                hcenterActor _
              _ = nu * b ^ 2 := by rw [hvNormSquare]
              _ = (eta * b) ^ 2 := by rw [mul_pow, heta_square]
              _ = centerCoordinates.symm
                    (squareMap (vNorm (eta * b) :
                      Additive (LowerCentralFactor P 0))) :=
                (hvNormSquare _).symm
        have hcrossTerm :
            ∃ epsilon : K, epsilon ≠ 0 ∧
              ∀ a b : K,
                centerCoordinates.symm
                    (crossBracket (uNorm a) (vNorm b)) =
                  epsilon * a * b := by
          classical
          let normalizedCross : K →ₗ[ZMod 2] K →ₗ[ZMod 2] K :=
            { toFun := fun a =>
                { toFun := fun b => centerCoordinates.symm
                    (crossBracket (uNorm a) (vNorm b))
                  map_add' := by
                    intro b c
                    simp
                  map_smul' := by
                    intro c b
                    simp }
              map_add' := by
                intro a b
                apply LinearMap.ext
                intro c
                simp
              map_smul' := by
                intro c a
                apply LinearMap.ext
                intro b
                simp }
          obtain ⟨normalizedCoeff, hnormalizedExpansion,
              hnormalizedSupport⟩ :=
            PFAppendixIII.frobeniusBilinear_expansion_with_support_of_equivariant
              n (by omega) normalizedCross eta eta nu (by
                intro a b
                change centerCoordinates.symm
                    (crossBracket (uNorm (eta * a)) (vNorm (eta * b))) =
                  nu * centerCoordinates.symm
                    (crossBracket (uNorm a) (vNorm b))
                apply centerCoordinates.injective
                calc
                  centerCoordinates
                        (centerCoordinates.symm
                          (crossBracket (uNorm (eta * a))
                            (vNorm (eta * b)))) =
                      crossBracket (uNorm (eta * a)) (vNorm (eta * b)) :=
                    centerCoordinates.apply_symm_apply _
                  _ = crossBracket (xiU (uNorm a)) (xiV (vNorm b)) := by
                    rw [hnormalizedActors.1, hnormalizedActors.2]
                  _ = S (crossBracket (uNorm a) (vNorm b)) :=
                    hcross_equivariant _ _
                  _ = S (centerCoordinates
                      (centerCoordinates.symm
                        (crossBracket (uNorm a) (vNorm b)))) := by
                    rw [centerCoordinates.apply_symm_apply]
                  _ = centerCoordinates
                      (nu * centerCoordinates.symm
                        (crossBracket (uNorm a) (vNorm b))) :=
                    hcenterCoordinates _)
          let i0 : Fin n := ⟨0, by omega⟩
          have hcoefficientIndex (i j : Fin n)
              (hij : normalizedCoeff i j ≠ 0) : i = i0 ∧ j = i0 := by
            have hseed := hnormalizedSupport i j hij
            rw [← heta_square] at hseed
            let etaUnit : Kˣ := Units.mk0 eta heta_nonzero
            have hunit :
                etaUnit ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) =
                  etaUnit ^ 2 := by
              apply Units.ext
              simpa only [K, etaUnit, Units.val_pow_eq_pow_val, Units.val_mk0,
                Units.val_mul, pow_add] using hseed
            have hmod := pow_eq_pow_iff_modEq.mp hunit
            change Nat.ModEq (orderOf (Units.mk0 eta heta_nonzero))
              (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) 2 at hmod
            rw [heta_order] at hmod
            have hfour_le : 2 ^ 2 ≤ 2 ^ n :=
              Nat.pow_le_pow_right (by omega) hn
            norm_num at hfour_le
            have htwo_lt : 2 < 2 ^ n - 1 := by omega
            have hi_le : (i : ℕ) ≤ n - 1 := by omega
            have hj_le : (j : ℕ) ≤ n - 1 := by omega
            have hipow : 2 ^ (i : ℕ) ≤ 2 ^ (n - 1) :=
              Nat.pow_le_pow_right (by omega) hi_le
            have hjpow : 2 ^ (j : ℕ) ≤ 2 ^ (n - 1) :=
              Nat.pow_le_pow_right (by omega) hj_le
            have hdouble :
                2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
              calc
                2 ^ (n - 1) + 2 ^ (n - 1) =
                    2 * 2 ^ (n - 1) := by ring
                _ = 2 ^ ((n - 1) + 1) := by rw [pow_succ']
                _ = 2 ^ n := by rw [Nat.sub_add_cancel (by omega)]
            have hsum_le :
                2 ^ (i : ℕ) + 2 ^ (j : ℕ) ≤ 2 ^ n := by
              calc
                2 ^ (i : ℕ) + 2 ^ (j : ℕ) ≤
                    2 ^ (n - 1) + 2 ^ (n - 1) :=
                  Nat.add_le_add hipow hjpow
                _ = 2 ^ n := hdouble
            have hsum_eq :
                2 ^ (i : ℕ) + 2 ^ (j : ℕ) = 2 := by
              by_cases hlt :
                  2 ^ (i : ℕ) + 2 ^ (j : ℕ) < 2 ^ n - 1
              · exact hmod.eq_of_lt_of_lt hlt htwo_lt
              · have hle :
                    2 ^ n - 1 ≤ 2 ^ (i : ℕ) + 2 ^ (j : ℕ) :=
                  Nat.le_of_not_gt hlt
                have hcases :
                    2 ^ (i : ℕ) + 2 ^ (j : ℕ) = 2 ^ n - 1 ∨
                      2 ^ (i : ℕ) + 2 ^ (j : ℕ) = 2 ^ n := by
                  omega
                rcases hcases with hM | hpow
                · rw [hM] at hmod
                  change (2 ^ n - 1) % (2 ^ n - 1) =
                    2 % (2 ^ n - 1) at hmod
                  rw [Nat.mod_self, Nat.mod_eq_of_lt htwo_lt] at hmod
                  omega
                · rw [hpow] at hmod
                  have hperiod :
                      Nat.ModEq (2 ^ n - 1) (2 ^ n) 1 := by
                    apply Nat.ModEq.symm
                    exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).2
                      (dvd_refl (2 ^ n - 1))
                  have h12 : (1 : ℕ) = 2 :=
                    (hperiod.symm.trans hmod).eq_of_lt_of_lt
                      (by omega) htwo_lt
                  omega
            have hipos : 0 < 2 ^ (i : ℕ) := Nat.two_pow_pos _
            have hjpos : 0 < 2 ^ (j : ℕ) := Nat.two_pow_pos _
            have hi_one : 2 ^ (i : ℕ) = 1 := by omega
            have hj_one : 2 ^ (j : ℕ) = 1 := by omega
            have hi_zero : (i : ℕ) = 0 :=
              Nat.pow_right_injective (by omega)
                (show 2 ^ (i : ℕ) = 2 ^ 0 by
                  simpa only [pow_zero] using hi_one)
            have hj_zero : (j : ℕ) = 0 :=
              Nat.pow_right_injective (by omega)
                (show 2 ^ (j : ℕ) = 2 ^ 0 by
                  simpa only [pow_zero] using hj_one)
            exact ⟨Fin.ext (by simpa [i0] using hi_zero),
              Fin.ext (by simpa [i0] using hj_zero)⟩
          have hnormalizedCoeff_zero (i j : Fin n)
              (hij : i ≠ i0 ∨ j ≠ i0) : normalizedCoeff i j = 0 := by
            by_contra hne
            have hindices := hcoefficientIndex i j hne
            rcases hij with hi | hj
            · exact hi hindices.1
            · exact hj hindices.2
          let epsilon : K := normalizedCoeff i0 i0
          have hformula (a b : K) :
              centerCoordinates.symm
                  (crossBracket (uNorm a) (vNorm b)) =
                epsilon * a * b := by
            change normalizedCross a b = _
            rw [hnormalizedExpansion, Finset.sum_eq_single i0]
            · rw [Finset.sum_eq_single i0]
              · simp [epsilon, i0]
              · intro j _hj hj
                rw [hnormalizedCoeff_zero i0 j
                  (Or.inr (by simpa [i0] using hj))]
                simp
              · simp
            · intro i _hi hi
              apply Finset.sum_eq_zero
              intro j _hj
              rw [hnormalizedCoeff_zero i j
                (Or.inl (by simpa [i0] using hi))]
              simp
            · simp
          have hepsilon : epsilon ≠ 0 := by
            intro hepsilon
            obtain ⟨u, v, huv⟩ := hcross_nonzero
            have hzero :
                centerCoordinates.symm (crossBracket u v) = 0 := by
              have h := hformula (uNorm.symm u) (vNorm.symm v)
              rw [uNorm.apply_symm_apply, vNorm.apply_symm_apply,
                hepsilon] at h
              simpa using h
            apply huv
            change crossBracket u v = 0
            apply centerCoordinates.symm.injective
            simpa using hzero
          exact ⟨epsilon, hepsilon, hformula⟩
        obtain ⟨epsilon, hepsilon, hcrossTerm⟩ := hcrossTerm
        let quotientCoordinates :
            (K × K) ≃ₗ[ZMod 2] Additive (LowerCentralFactor P 0) :=
          (uNorm.prodCongr vNorm).trans
            (Submodule.prodEquivOfIsCompl U V hUV)
        let theta : K ≃+* K := RingEquiv.refl K
        have hq (a b : K) :
            centerCoordinates.symm
                (squareMap (quotientCoordinates (a, b))) =
              a * theta a + epsilon * a * theta b + b * theta b := by
          change centerCoordinates.symm
              (squareMap ((uNorm a : Additive (LowerCentralFactor P 0)) +
                (vNorm b : Additive (LowerCentralFactor P 0)))) = _
          rw [hsquare_add]
          simp only [map_add]
          change
            centerCoordinates.symm
                (squareMap (uNorm a : Additive (LowerCentralFactor P 0))) +
              centerCoordinates.symm
                (squareMap (vNorm b : Additive (LowerCentralFactor P 0))) +
              centerCoordinates.symm (crossBracket (uNorm a) (vNorm b)) = _
          rw [huNormSquare, hvNormSquare, hcrossTerm]
          simp only [theta, RingEquiv.refl_apply]
          ring
        have hanisotropic :
            ∀ a b : K, a ≠ 0 → b ≠ 0 →
              a * theta a + epsilon * a * theta b + b * theta b ≠ 0 := by
          intro a b ha _hb hzero
          have hcenterZero :
              centerCoordinates.symm
                  (squareMap (quotientCoordinates (a, b))) = 0 := by
            rw [hq]
            exact hzero
          have hsquareZero : squareMap (quotientCoordinates (a, b)) = 0 := by
            apply centerCoordinates.symm.injective
            simpa using hcenterZero
          have hquotientZero : quotientCoordinates (a, b) = 0 :=
            hsquare_anisotropic _ hsquareZero
          have habZero : (a, b) = 0 := by
            apply quotientCoordinates.injective
            simpa using hquotientZero
          exact ha (congrArg Prod.fst habZero)
        refine ⟨?_, ?_⟩
        · let etaUnit : Kˣ := Units.mk0 eta heta_nonzero
          refine ⟨theta, epsilon, quotientCoordinates, centerCoordinates,
            etaUnit, hepsilon, ?_, hanisotropic, hq, heta_order, ?_, ?_⟩
          · exact ⟨1, by norm_num, by omega, by intro x; rfl⟩
          · intro a b
            change lowerCentralFactorLinearAut xi 0
                ((uNorm a : Additive (LowerCentralFactor P 0)) +
                  (vNorm b : Additive (LowerCentralFactor P 0))) =
              (uNorm (eta * a) : Additive (LowerCentralFactor P 0)) +
                (vNorm (eta * b) : Additive (LowerCentralFactor P 0))
            rw [map_add, ← hxiU_val, ← hxiV_val,
              hnormalizedActors.1, hnormalizedActors.2]
          · intro z
            change S (centerCoordinates z) =
              centerCoordinates (eta * theta eta * z)
            simpa only [S, theta, RingEquiv.refl_apply, ← pow_two,
              heta_square] using hcenterCoordinates z
        · refine ⟨eta, epsilon, uNorm, vNorm, centerCoordinates,
            heta_nonzero, hepsilon, heta_order, ?_, ?_, ?_,
            huNormSquare, hvNormSquare, hcrossTerm⟩
          · intro a
            rw [← hxiU_val, hnormalizedActors.1]
          · intro b
            rw [← hxiV_val, hnormalizedActors.2]
          · intro z
            simpa only [S, heta_square] using hcenterCoordinates z
      have hBActorCoordinates := hcoordinateEndpoints.1 hlinearLinearCase.1
      have hBEndpoint := htypeBOfActorCoordinates hBActorCoordinates
      exact ⟨Or.inl hBEndpoint,
        Or.inl ⟨g ^ (2 ^ k), hpackTypeBActorBranch hBActorCoordinates⟩,
        hsummandData,
        hpackCriterionData (fun _ =>
          hpackTypeBActorBranch hBActorCoordinates),
        fun _hAcomm => hpackActorData (Or.inl hlinearLinearCase.2)⟩
    · have hlinearPairCase :
          typeCQuadraticData ∧
            Lemma12TypeCNormalizedData xi n U V bracket squareMap := by
        exact (lemma12_linear_pair_case_core
          (xi := xi) (n := n) (hn := hn) (U := U) (xiU := xiU)
          (hxiU_val := hxiU_val) (V := V) (hUV := hUV)
          (xiV := xiV) (hxiV_val := hxiV_val) (nu := nu)
          (centerCoordinates := centerCoordinates) (hnu := hnu)
          (hcenterCoordinates := hcenterCoordinates)
          (bracket := bracket) (squareMap := squareMap)
          (hbracket_equivariant := hbracket_equivariant)
          (hbracket_self := hbracket_self) (hsquare_add := hsquare_add)
          (hsquare_anisotropic := hsquare_anisotropic)
          (hsquare_zero := hsquare_zero)
          (hsquare_xiU_pow := hsquare_xiU_pow)
          (hsquareU_surjective := hsquareU_surjective)
          (hcross_nonzero := hcross_nonzero) (bracketU := bracketU)
          (hbracketU_apply := by intro u v; rfl)
          (lambda := lambda) (uCoordinates := uCoordinates)
          (mu := mu) (vCoordinates := vCoordinates) (hmu := hmu)
          (hvCoordinates := hvCoordinates) (hmu_order := hmu_order)
          (hnu_order := hnu_order) (hUlinear := hUlinear)
          (hVpair := hVpair))
      have hnotIso : ¬ ∃ e : U ≃ₗ[ZMod 2] V,
          ∀ u : U, e (xiU u) = xiV (e u) := by
        intro hiso
        obtain ⟨t, ht⟩ := hcanonicalEigenRelation hiso
        rcases hUlinear with
          ⟨iu, su, _cu, _hbracketUZero, hUseed, _hcu, _hUformula⟩
        rcases hVpair with
          ⟨iv, jv, sv, _cv, hijv, hVseed, _hcv, _hVformula⟩
        exact lemma12_linear_pair_not_frobenius_conjugate
          n (by omega) lambda mu nu hlambda hlambda_order
          t iu su iv jv sv ht hUseed hVseed hijv
      have hCEndpoint := hcoordinateEndpoints.2.1 hlinearPairCase.1
      exact ⟨Or.inr (Or.inl hCEndpoint), Or.inr (Or.inl hCEndpoint),
        hsummandData,
        hpackCriterionData (fun hiso => False.elim (hnotIso hiso)),
        fun _hAcomm => hpackActorData (Or.inr hlinearPairCase.2)⟩
  · have hUpair_not_comm : ¬ IsMulCommutative A := by
      intro hAcomm
      have hbracketUZero : bracketU = 0 := by
        apply LinearMap.ext
        intro u
        apply LinearMap.ext
        intro v
        change bracket
            (u : Additive (LowerCentralFactor P 0))
            (v : Additive (LowerCentralFactor P 0)) = 0
        have huMap := u.property
        have hvMap := v.property
        change Additive.toMul (u : Additive (LowerCentralFactor P 0)) ∈ A.map q0 at huMap
        change Additive.toMul (v : Additive (LowerCentralFactor P 0)) ∈ A.map q0 at hvMap
        rcases huMap with ⟨a, haA, ha⟩
        rcases hvMap with ⟨b, hbA, hb⟩
        let aA : A := ⟨a, haA⟩
        let bA : A := ⟨b, hbA⟩
        have hab : a * b = b * a := by
          simpa [aA, bA] using
            congrArg Subtype.val (hAcomm.is_comm.comm aA bA)
        have hcommOne : ⁅a, b⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.mpr hab
        let aTop : (⊤ : Subgroup P).lowerCentralSeries 0 := ⟨a, trivial⟩
        let bTop : (⊤ : Subgroup P).lowerCentralSeries 0 := ⟨b, trivial⟩
        have hcommMem : ⁅(aTop : P), (bTop : P)⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries 1 := by
          rw [hcommOne]
          exact Subgroup.one_mem _
        have hu :
            (u : Additive (LowerCentralFactor P 0)) =
              Additive.ofMul (q0 a) := by
          apply Additive.toMul.injective
          simpa using ha.symm
        have hv :
            (v : Additive (LowerCentralFactor P 0)) =
              Additive.ofMul (q0 b) := by
          apply Additive.toMul.injective
          simpa using hb.symm
        rw [hu, hv]
        change bracket
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel P 0) aTop))
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel P 0) bTop)) = 0
        rw [hbracket_mk aTop bTop hcommMem]
        have hcommSubtypeOne :
            (⟨⁅(aTop : P), (bTop : P)⁆, hcommMem⟩ :
              (⊤ : Subgroup P).lowerCentralSeries 1) = 1 := by
          apply Subtype.ext
          simpa [aTop, bTop] using hcommOne
        rw [hcommSubtypeOne]
        simp
      rcases hUpair with
        ⟨iu, ju, su, cu, hiju, _hUseed, hcu, hUformula⟩
      let sigma : K ≃ₐ[ZMod 2] K :=
        FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
      have hsquareAdd (a b : K) :
          squareMap (uCoordinates (a + b) :
              Additive (LowerCentralFactor P 0)) =
            squareMap (uCoordinates a :
              Additive (LowerCentralFactor P 0)) +
            squareMap (uCoordinates b :
              Additive (LowerCentralFactor P 0)) := by
        rw [uCoordinates.map_add]
        change squareMap
            ((uCoordinates a : Additive (LowerCentralFactor P 0)) +
              (uCoordinates b : Additive (LowerCentralFactor P 0))) = _
        rw [hsquare_add]
        have hzero :
            bracket
                (uCoordinates a : Additive (LowerCentralFactor P 0))
                (uCoordinates b : Additive (LowerCentralFactor P 0)) = 0 := by
          change bracketU (uCoordinates a) (uCoordinates b) = 0
          rw [hbracketUZero]
          rfl
        rw [hzero, add_zero]
      have hadd :
          (sigma ^ (su : ℕ))
              (centerCoordinates.symm
                (squareMap (uCoordinates (1 + lambda) :
                  Additive (LowerCentralFactor P 0)))) =
            (sigma ^ (su : ℕ))
                (centerCoordinates.symm
                  (squareMap (uCoordinates 1 :
                    Additive (LowerCentralFactor P 0)))) +
              (sigma ^ (su : ℕ))
                (centerCoordinates.symm
                  (squareMap (uCoordinates lambda :
                    Additive (LowerCentralFactor P 0)))) := by
        calc
          _ = (sigma ^ (su : ℕ))
              (centerCoordinates.symm
                (squareMap (uCoordinates 1 :
                    Additive (LowerCentralFactor P 0)) +
                  squareMap (uCoordinates lambda :
                    Additive (LowerCentralFactor P 0)))) :=
            congrArg
              (fun z : Additive (LowerCentralFactor P 1) =>
                (sigma ^ (su : ℕ)) (centerCoordinates.symm z))
              (hsquareAdd 1 lambda)
          _ = _ := by rw [map_add, map_add]
      rw [hUformula (1 + lambda), hUformula 1, hUformula lambda,
        one_pow, pow_add, add_pow_char_pow, add_pow_char_pow] at hadd
      have hsum :
          cu * (lambda ^ (2 ^ (iu : ℕ)) +
            lambda ^ (2 ^ (ju : ℕ))) = 0 := by
        linear_combination hadd
      have hpowsum :
          lambda ^ (2 ^ (iu : ℕ)) +
            lambda ^ (2 ^ (ju : ℕ)) = 0 :=
        (mul_eq_zero.mp hsum).resolve_left hcu
      have hpows :
          lambda ^ (2 ^ (iu : ℕ)) =
            lambda ^ (2 ^ (ju : ℕ)) := by
        have hneg := eq_neg_of_add_eq_zero_left hpowsum
        simpa only [ZModModule.neg_eq_self] using hneg
      let lambdaUnit : Kˣ := Units.mk0 lambda hlambda
      have hunit :
          lambdaUnit ^ (2 ^ (iu : ℕ)) =
            lambdaUnit ^ (2 ^ (ju : ℕ)) := by
        apply Units.ext
        exact hpows
      have hmod := pow_eq_pow_iff_modEq.mp hunit
      change Nat.ModEq (orderOf lambdaUnit)
        (2 ^ (iu : ℕ)) (2 ^ (ju : ℕ)) at hmod
      rw [show orderOf lambdaUnit = 2 ^ n - 1 by exact hlambda_order] at hmod
      have hhalf : 2 ^ (n - 1) < 2 ^ n - 1 := by
        have htwo_le : 2 ≤ 2 ^ (n - 1) := by
          have hpow_le := Nat.pow_le_pow_right
            (by omega : 0 < 2) (by omega : 1 ≤ n - 1)
          simpa using hpow_le
        rw [show n = (n - 1) + 1 by omega, pow_succ]
        rw [show n - 1 + 1 - 1 = n - 1 by omega]
        omega
      have hiPowLt : 2 ^ (iu : ℕ) < 2 ^ n - 1 :=
        lt_of_le_of_lt
          (Nat.pow_le_pow_right (by omega) (by omega : (iu : ℕ) ≤ n - 1))
          hhalf
      have hjPowLt : 2 ^ (ju : ℕ) < 2 ^ n - 1 :=
        lt_of_le_of_lt
          (Nat.pow_le_pow_right (by omega) (by omega : (ju : ℕ) ≤ n - 1))
          hhalf
      have hpowsNat : 2 ^ (iu : ℕ) = 2 ^ (ju : ℕ) :=
        hmod.eq_of_lt_of_lt hiPowLt hjPowLt
      have hijVal : (iu : ℕ) = (ju : ℕ) :=
        Nat.pow_right_injective (by omega) hpowsNat
      exact hiju (Fin.ext hijVal)
    rcases hV_monomial with hVlinear | hVpair
    · have hpairLinearCase : typeCQuadraticData := by
        have hbracket_symm_pair_linear
            (x y : Additive (LowerCentralFactor P 0)) :
            bracket x y = bracket y x := by
          have hadd_self
              (z : Additive (LowerCentralFactor P 1)) : z + z = 0 := by
            rw [← two_smul (ZMod 2) z]
            simp only [CharTwo.two_eq_zero, zero_smul]
          have hsum : bracket x y + bracket y x = 0 := by
            have h := hbracket_self (x + y)
            simp only [map_add, LinearMap.add_apply] at h
            rw [hbracket_self x, hbracket_self y] at h
            simpa only [zero_add, add_zero, add_assoc, add_comm] using h
          calc
            bracket x y = bracket x y + (bracket y x + bracket y x) := by
              rw [hadd_self, add_zero]
            _ = (bracket x y + bracket y x) + bracket y x := by ac_rfl
            _ = bracket y x := by rw [hsum, zero_add]
        have hcross_nonzero_swapped :
            ∃ v : V, ∃ u : U,
              bracket (v : Additive (LowerCentralFactor P 0))
                (u : Additive (LowerCentralFactor P 0)) ≠ 0 := by
          obtain ⟨u, v, huv⟩ := hcross_nonzero
          refine ⟨v, u, ?_⟩
          rw [hbracket_symm_pair_linear]
          exact huv
        exact (lemma12_linear_pair_case_core
          (xi := xi) (n := n) (hn := hn) (U := V) (xiU := xiV)
          (hxiU_val := hxiV_val) (V := U) (hUV := hUV.symm)
          (xiV := xiU) (hxiV_val := hxiU_val) (nu := nu)
          (centerCoordinates := centerCoordinates) (hnu := hnu)
          (hcenterCoordinates := hcenterCoordinates)
          (bracket := bracket) (squareMap := squareMap)
          (hbracket_equivariant := hbracket_equivariant)
          (hbracket_self := hbracket_self) (hsquare_add := hsquare_add)
          (hsquare_anisotropic := hsquare_anisotropic)
          (hsquare_zero := hsquare_zero)
          (hsquare_xiU_pow := hsquare_xiV_pow)
          (hsquareU_surjective := hsquareV_surjective)
          (hcross_nonzero := hcross_nonzero_swapped) (bracketU := bracketV)
          (hbracketU_apply := by intro u v; rfl)
          (lambda := mu) (uCoordinates := vCoordinates)
          (mu := lambda) (vCoordinates := uCoordinates) (hmu := hlambda)
          (hvCoordinates := huCoordinates) (hmu_order := hlambda_order)
          (hnu_order := hnu_order) (hUlinear := hVlinear)
          (hVpair := hUpair)).1
      have hCEndpoint := hcoordinateEndpoints.2.1 hpairLinearCase
      have hnotIso : ¬ ∃ e : U ≃ₗ[ZMod 2] V,
          ∀ u : U, e (xiU u) = xiV (e u) := by
        intro hiso
        obtain ⟨t, ht⟩ := hcanonicalEigenRelationSymm hiso
        rcases hVlinear with
          ⟨iv, sv, _cv, _hbracketVZero, hVseed, _hcv, _hVformula⟩
        rcases hUpair with
          ⟨iu, ju, su, _cu, hiju, hUseed, _hcu, _hUformula⟩
        exact lemma12_linear_pair_not_frobenius_conjugate
          n (by omega) mu lambda nu hmu hmu_order
          t iv sv iu ju su ht hVseed hUseed hiju
      exact ⟨Or.inr (Or.inl hCEndpoint), Or.inr (Or.inl hCEndpoint),
        hsummandData,
        hpackCriterionData (fun hiso => False.elim (hnotIso hiso)),
        fun hAcomm => False.elim (hUpair_not_comm hAcomm)⟩
    · have hpairPairCase :
          typeBQuadraticData ∨
            (typeDQuadraticData ∧
              ¬ ∃ e : U ≃ₗ[ZMod 2] V,
                ∀ u : U, e (xiU u) = xiV (e u)) := by
        rcases hUpair with
          ⟨iuRaw, juRaw, su, cu, hijuRaw, hUseedRaw, hcu, hUformulaRaw⟩
        rcases hVpair with
          ⟨ivRaw, jvRaw, sv, cv, hijvRaw, hVseedRaw, hcv, hVformulaRaw⟩
        let forwardGap (i j : Fin n) : ℕ :=
          if i.val ≤ j.val then j.val - i.val else n - (i.val - j.val)
        have hUCanonicalPairOrientation :
            ∃ iu ju : Fin n,
              iu ≠ ju ∧
              (lambda ^ (2 ^ (iu : ℕ)) * lambda ^ (2 ^ (ju : ℕ)) =
                nu ^ (2 ^ (su : ℕ))) ∧
              (∀ a : K,
                (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^
                    (su : ℕ))
                    (centerCoordinates.symm
                      (squareMap (uCoordinates a :
                        Additive (LowerCentralFactor P 0)))) =
                  cu * a ^ (2 ^ (iu : ℕ) + 2 ^ (ju : ℕ))) ∧
              0 < forwardGap iu ju ∧ forwardGap iu ju ≤ n / 2 := by
          let d := lemma6_finPairGap iuRaw juRaw
          have hd_pos : 0 < d := lemma6_finPairGap_pos_of_ne hijuRaw
          have hd_lt : d < n := lemma6_finPairGap_lt iuRaw juRaw
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hijuRaw) with hlt | hgt
          · by_cases hsmall : d ≤ n / 2
            · refine ⟨iuRaw, juRaw, hijuRaw, hUseedRaw, hUformulaRaw, ?_, ?_⟩
              · simp only [forwardGap, if_pos hlt.le]
                dsimp only [d, lemma6_finPairGap] at hd_pos
                omega
              · simp only [forwardGap, if_pos hlt.le]
                dsimp only [d, lemma6_finPairGap] at hsmall
                omega
            · have hseedSwap :
                  lambda ^ (2 ^ (juRaw : ℕ)) *
                      lambda ^ (2 ^ (iuRaw : ℕ)) =
                    nu ^ (2 ^ (su : ℕ)) := by
                simpa only [mul_comm] using hUseedRaw
              have hformulaSwap : ∀ a : K,
                  (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^
                      (su : ℕ))
                      (centerCoordinates.symm
                        (squareMap (uCoordinates a :
                          Additive (LowerCentralFactor P 0)))) =
                    cu * a ^ (2 ^ (juRaw : ℕ) + 2 ^ (iuRaw : ℕ)) := by
                intro a
                simpa only [add_comm] using hUformulaRaw a
              refine ⟨juRaw, iuRaw, hijuRaw.symm, hseedSwap,
                hformulaSwap, ?_, ?_⟩
              · simp only [forwardGap, if_neg (Nat.not_le.mpr hlt)]
                dsimp only [d, lemma6_finPairGap] at hd_lt
                omega
              · simp only [forwardGap, if_neg (Nat.not_le.mpr hlt)]
                dsimp only [d, lemma6_finPairGap] at hsmall hd_lt
                omega
          · by_cases hsmall : d ≤ n / 2
            · have hseedSwap :
                  lambda ^ (2 ^ (juRaw : ℕ)) *
                      lambda ^ (2 ^ (iuRaw : ℕ)) =
                    nu ^ (2 ^ (su : ℕ)) := by
                simpa only [mul_comm] using hUseedRaw
              have hformulaSwap : ∀ a : K,
                  (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^
                      (su : ℕ))
                      (centerCoordinates.symm
                        (squareMap (uCoordinates a :
                          Additive (LowerCentralFactor P 0)))) =
                    cu * a ^ (2 ^ (juRaw : ℕ) + 2 ^ (iuRaw : ℕ)) := by
                intro a
                simpa only [add_comm] using hUformulaRaw a
              refine ⟨juRaw, iuRaw, hijuRaw.symm, hseedSwap,
                hformulaSwap, ?_, ?_⟩
              · simp only [forwardGap, if_pos hgt.le]
                omega
              · simp only [forwardGap, if_pos hgt.le]
                dsimp only [d, lemma6_finPairGap] at hsmall
                omega
            · refine ⟨iuRaw, juRaw, hijuRaw, hUseedRaw, hUformulaRaw, ?_, ?_⟩
              · simp only [forwardGap, if_neg (Nat.not_le.mpr hgt)]
                dsimp only [d, lemma6_finPairGap] at hd_lt
                omega
              · simp only [forwardGap, if_neg (Nat.not_le.mpr hgt)]
                dsimp only [d, lemma6_finPairGap] at hsmall hd_lt
                omega
        have hVCanonicalPairOrientation :
            ∃ iv jv : Fin n,
              iv ≠ jv ∧
              (mu ^ (2 ^ (iv : ℕ)) * mu ^ (2 ^ (jv : ℕ)) =
                nu ^ (2 ^ (sv : ℕ))) ∧
              (∀ b : K,
                (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^
                    (sv : ℕ))
                    (centerCoordinates.symm
                      (squareMap (vCoordinates b :
                        Additive (LowerCentralFactor P 0)))) =
                  cv * b ^ (2 ^ (iv : ℕ) + 2 ^ (jv : ℕ))) ∧
              0 < forwardGap iv jv ∧ forwardGap iv jv ≤ n / 2 := by
          let d := lemma6_finPairGap ivRaw jvRaw
          have hd_pos : 0 < d := lemma6_finPairGap_pos_of_ne hijvRaw
          have hd_lt : d < n := lemma6_finPairGap_lt ivRaw jvRaw
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hijvRaw) with hlt | hgt
          · by_cases hsmall : d ≤ n / 2
            · refine ⟨ivRaw, jvRaw, hijvRaw, hVseedRaw, hVformulaRaw, ?_, ?_⟩
              · simp only [forwardGap, if_pos hlt.le]
                dsimp only [d, lemma6_finPairGap] at hd_pos
                omega
              · simp only [forwardGap, if_pos hlt.le]
                dsimp only [d, lemma6_finPairGap] at hsmall
                omega
            · have hseedSwap :
                  mu ^ (2 ^ (jvRaw : ℕ)) *
                      mu ^ (2 ^ (ivRaw : ℕ)) =
                    nu ^ (2 ^ (sv : ℕ)) := by
                simpa only [mul_comm] using hVseedRaw
              have hformulaSwap : ∀ a : K,
                  (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^
                      (sv : ℕ))
                      (centerCoordinates.symm
                        (squareMap (vCoordinates a :
                          Additive (LowerCentralFactor P 0)))) =
                    cv * a ^ (2 ^ (jvRaw : ℕ) + 2 ^ (ivRaw : ℕ)) := by
                intro a
                simpa only [add_comm] using hVformulaRaw a
              refine ⟨jvRaw, ivRaw, hijvRaw.symm, hseedSwap,
                hformulaSwap, ?_, ?_⟩
              · simp only [forwardGap, if_neg (Nat.not_le.mpr hlt)]
                dsimp only [d, lemma6_finPairGap] at hd_lt
                omega
              · simp only [forwardGap, if_neg (Nat.not_le.mpr hlt)]
                dsimp only [d, lemma6_finPairGap] at hsmall hd_lt
                omega
          · by_cases hsmall : d ≤ n / 2
            · have hseedSwap :
                  mu ^ (2 ^ (jvRaw : ℕ)) *
                      mu ^ (2 ^ (ivRaw : ℕ)) =
                    nu ^ (2 ^ (sv : ℕ)) := by
                simpa only [mul_comm] using hVseedRaw
              have hformulaSwap : ∀ a : K,
                  (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^
                      (sv : ℕ))
                      (centerCoordinates.symm
                        (squareMap (vCoordinates a :
                          Additive (LowerCentralFactor P 0)))) =
                    cv * a ^ (2 ^ (jvRaw : ℕ) + 2 ^ (ivRaw : ℕ)) := by
                intro a
                simpa only [add_comm] using hVformulaRaw a
              refine ⟨jvRaw, ivRaw, hijvRaw.symm, hseedSwap,
                hformulaSwap, ?_, ?_⟩
              · simp only [forwardGap, if_pos hgt.le]
                omega
              · simp only [forwardGap, if_pos hgt.le]
                dsimp only [d, lemma6_finPairGap] at hsmall
                omega
            · refine ⟨ivRaw, jvRaw, hijvRaw, hVseedRaw, hVformulaRaw, ?_, ?_⟩
              · simp only [forwardGap, if_neg (Nat.not_le.mpr hgt)]
                dsimp only [d, lemma6_finPairGap] at hd_lt
                omega
              · simp only [forwardGap, if_neg (Nat.not_le.mpr hgt)]
                dsimp only [d, lemma6_finPairGap] at hsmall hd_lt
                omega
        obtain ⟨iu, ju, hiju, hUseed, hUformula,
          hUgap_pos, hUgap_le⟩ := hUCanonicalPairOrientation
        obtain ⟨iv, jv, hijv, hVseed, hVformula,
          hVgap_pos, hVgap_le⟩ := hVCanonicalPairOrientation
        have hpairPairCore :
            typeBQuadraticData ∨
              (typeDQuadraticData ∧
                ¬ ∃ e : U ≃ₗ[ZMod 2] V,
                  ∀ u : U, e (xiU u) = xiV (e u)) := by
          let r := forwardGap iu ju
          let s := forwardGap iv jv
          have hr_pos : 0 < r := hUgap_pos
          have hr_le : r ≤ n / 2 := hUgap_le
          have hs_pos : 0 < s := hVgap_pos
          have hs_le : s ≤ n / 2 := hVgap_le
          have hsamePairTypeB (hsame : r = s) :
              typeBQuadraticData := by
            exact lemma12_same_pair_typeB_core
              (n := n) (hn := hn) (U := U) (V := V) (hUV := hUV)
              (S := S) (xiU := xiU) (xiV := xiV)
              (T := lowerCentralFactorLinearAut xi 0)
              (hT_u := fun u => (hxiU_val u).symm)
              (hT_v := fun v => (hxiV_val v).symm) (nu := nu)
              (centerCoordinates := centerCoordinates) (hnu := hnu)
              (hcenterCoordinates := hcenterCoordinates)
              (bracket := bracket) (squareMap := squareMap)
              (hsquare_add := hsquare_add)
              (hsquare_anisotropic := hsquare_anisotropic)
              (hsquare_xiV_pow := hsquare_xiV_pow)
              (hcross_nonzero := hcross_nonzero)
              (hbracket_cross_equivariant := by
                intro u v
                change crossBracket (xiU u) (xiV v) = S (crossBracket u v)
                exact hcross_equivariant u v)
              (lambda := lambda) (hlambda := hlambda)
              (hlambda_order := hlambda_order) (hnu_order := hnu_order)
              (uCoordinates := uCoordinates) (huCoordinates := huCoordinates)
              (vCoordinates := vCoordinates)
              (iu := iu) (ju := ju) (su := su)
              (iv := iv) (jv := jv) (sv := sv)
              (cu := cu) (cv := cv) (hcu := hcu) (hcv := hcv)
              (hUseed := hUseed) (hUformula := hUformula)
              (hVformula := hVformula)
              (hUgap_pos := by simpa only [forwardGap] using hUgap_pos)
              (hUgap_le := by simpa only [forwardGap] using hUgap_le)
              (hsameGap := by simpa only [r, s, forwardGap] using hsame)

          have hdistinctPairTypeD (hdiff : r ≠ s) :
              typeDQuadraticData := by
            have hgapClassification :
                (s = 2 * r ∧ n = 5 * r) ∨
                  (r = 2 * s ∧ n = 5 * s) := by
              have hcrossCoeffNonzero :
                  ∃ iCross jCross : Fin n, crossCoeff iCross jCross ≠ 0 := by
                by_contra hzero
                push Not at hzero
                obtain ⟨u, v, huv⟩ := hcross_nonzero
                have hcoordinateZero :
                    centerCoordinates.symm (crossBracket u v) = 0 := by
                  have h := hcrossExpansion
                    (uCoordinates.symm u) (vCoordinates.symm v)
                  rw [uCoordinates.apply_symm_apply,
                    vCoordinates.apply_symm_apply] at h
                  rw [h]
                  simp [hzero]
                apply huv
                change crossBracket u v = 0
                apply centerCoordinates.symm.injective
                simpa using hcoordinateZero
              obtain ⟨iCross, jCross, hcrossCoeff⟩ := hcrossCoeffNonzero
              have hfull := lemma12_distinct_pair_gap_of_cross_seed
                n r s hn hr_pos hr_le hs_pos hs_le hdiff
                lambda mu nu hlambda hlambda_order
                iu ju su iv jv sv iCross jCross
                (by rfl) (by rfl) hUseed hVseed
                (hcrossCoefficientSupport iCross jCross hcrossCoeff)
              rcases hfull with hforward | hreverse
              · exact Or.inl ⟨hforward.1, hforward.2.1⟩
              · exact Or.inr ⟨hreverse.1, hreverse.2.1⟩
            obtain ⟨theta, epsilon, quotientCoordinates,
                finalCenterCoordinates, hepsilon, hthetaFive,
                hthetaNontrivial, hq⟩ :=
              lemma12_distinct_pair_typeD_normal_form_core
                (n := n) (hn := hn) (U := U) (V := V) (hUV := hUV)
                (squareMap := squareMap) (crossBracket := crossBracket)
                (hsquare_add_cross := by
                  intro u v
                  change squareMap
                      ((u : Additive (LowerCentralFactor P 0)) +
                        (v : Additive (LowerCentralFactor P 0))) =
                    squareMap
                        (u : Additive (LowerCentralFactor P 0)) +
                      squareMap
                        (v : Additive (LowerCentralFactor P 0)) +
                      bracket
                        (u : Additive (LowerCentralFactor P 0))
                        (v : Additive (LowerCentralFactor P 0))
                  exact hsquare_add _ _)
                (hcross_nonzero := by
                  obtain ⟨u, v, huv⟩ := hcross_nonzero
                  refine ⟨u, v, ?_⟩
                  change bracket
                    (u : Additive (LowerCentralFactor P 0))
                    (v : Additive (LowerCentralFactor P 0)) ≠ 0
                  exact huv)
                (lambda := lambda) (mu := mu) (nu := nu)
                (hlambda := hlambda) (hlambda_order := hlambda_order)
                (centerCoordinates := centerCoordinates)
                (uCoordinates := uCoordinates) (vCoordinates := vCoordinates)
                (iu := iu) (ju := ju) (su := su)
                (iv := iv) (jv := jv) (sv := sv)
                (cu := cu) (cv := cv) (hcu := hcu) (hcv := hcv)
                (hUseed := hUseed) (hVseed := hVseed)
                (hUformula := hUformula) (hVformula := hVformula)
                (r := r) (s := s) (hrGap := by rfl) (hsGap := by rfl)
                (hr_pos := hr_pos) (hs_pos := hs_pos)
                (hgapClassification := hgapClassification)
                (crossCoeff := crossCoeff)
                (hcrossExpansion := hcrossExpansion)
                (hcrossCoefficientSupport := hcrossCoefficientSupport)
            have havoid :
                ∀ rho : K, epsilon ≠
                  rho⁻¹ + theta^[4] rho * theta rho * rho⁻¹ :=
              lemma12_typeD_avoid_of_anisotropic n squareMap
                hsquare_anisotropic theta epsilon quotientCoordinates
                  finalCenterCoordinates hepsilon hthetaFive hq
            exact ⟨theta, epsilon, quotientCoordinates,
              finalCenterCoordinates, hepsilon, hthetaFive,
              hthetaNontrivial, havoid, hq⟩
          by_cases hsame : r = s
          · exact Or.inl (hsamePairTypeB hsame)
          · refine Or.inr ⟨hdistinctPairTypeD hsame, ?_⟩
            intro hiso
            obtain ⟨t, ht⟩ := hcanonicalEigenRelation hiso
            have hsupported := lemma12_pair_supported_of_frobenius_conjugate
              n (by omega) lambda mu nu hlambda hlambda_order
              t iu ju su iv jv sv hiju hijv ht hUseed hVseed
            apply hsame
            simpa only [r, s, forwardGap] using
              lemma12_forward_pair_gap_eq_of_supported iu ju iv jv
                hUgap_pos hUgap_le hVgap_pos hVgap_le hsupported
        exact hpairPairCore
      rcases hpairPairCase with hBData | ⟨hDData, hnotIso⟩
      · have hBActorCoordinates := hcoordinateEndpoints.1 hBData
        have hBEndpoint := htypeBOfActorCoordinates hBActorCoordinates
        exact ⟨Or.inl hBEndpoint,
          Or.inl ⟨g ^ (2 ^ k), hpackTypeBActorBranch hBActorCoordinates⟩,
          hsummandData,
          hpackCriterionData (fun _ =>
            hpackTypeBActorBranch hBActorCoordinates),
          fun hAcomm => False.elim (hUpair_not_comm hAcomm)⟩
      · have hDEndpoint := hcoordinateEndpoints.2.2 hDData
        exact ⟨Or.inr (Or.inr hDEndpoint), Or.inr (Or.inr hDEndpoint),
          hsummandData,
          hpackCriterionData (fun hiso => False.elim (hnotIso hiso)),
          fun hAcomm => False.elim (hUpair_not_comm hAcomm)⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Higman Lemma 12 with the historical classification and chain-data
interface. -/
public theorem lemma12_chain_typeBCD
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (_hP : IsSuzukiTwoGroup P)
    (_hXcyclic : IsCyclic X) (_hXfaithful : FaithfulSMul X P)
    (_hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    (_hXprimeSupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card X →
      p ∣ Nat.card {x : P // x ∈ involutions P})
    (g : X) (hg : ∀ x : X, x ∈ Subgroup.zpowers g)
    {A B : Subgroup P}
    (hupper :
      A < ⊤ ∧ (⊤ : Subgroup P).Normal ∧ A.Normal ∧
        IsXInvariantSubgroup X (⊤ : Subgroup P) ∧
        IsXInvariantSubgroup X A ∧
        ∀ L : Subgroup P, L.Normal → IsXInvariantSubgroup X L →
          A ≤ L → L ≤ ⊤ → L = A ∨ L = ⊤)
    (hmiddle :
      B < A ∧ A.Normal ∧ B.Normal ∧
        IsXInvariantSubgroup X A ∧ IsXInvariantSubgroup X B ∧
        ∀ L : Subgroup P, L.Normal → IsXInvariantSubgroup X L →
          B ≤ L → L ≤ A → L = B ∨ L = A)
    (hlower :
      (⊥ : Subgroup P) < B ∧ B.Normal ∧ (⊥ : Subgroup P).Normal ∧
        IsXInvariantSubgroup X B ∧
        IsXInvariantSubgroup X (⊥ : Subgroup P) ∧
        ∀ L : Subgroup P, L.Normal → IsXInvariantSubgroup X L →
          ⊥ ≤ L → L ≤ B → L = ⊥ ∨ L = B) :
    (IsSuzukiTwoTypeB (⊤ : Subgroup P) ∨
      IsSuzukiTwoTypeC (⊤ : Subgroup P) ∨
        IsSuzukiTwoTypeD (⊤ : Subgroup P)) ∧
      ((∃ actor : X, Lemma12TypeBActorBranchData X P actor B) ∨
        IsSuzukiTwoTypeC (⊤ : Subgroup P) ∨
          IsSuzukiTwoTypeD (⊤ : Subgroup P)) ∧
      Lemma12SummandData X P B ∧
      (IsMulCommutative A → Lemma12ChainActorData g A B) := by
  have h := lemma12_chain_typeBCD_with_isomorphic_criterion
    _hP _hXcyclic _hXfaithful _hXtrans _hXprimeSupport
      g hg hupper hmiddle hlower
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
 /-- Higman Lemma 12: a Suzuki `2`-group of Omega-length three is type B, C, or
D. -/
public theorem lemma12_length_three_typeBCD_with_isomorphic_criterion
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (_hP : IsSuzukiTwoGroup P)
    (_hXcyclic : IsCyclic X) (_hXfaithful : FaithfulSMul X P)
    (_hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    (_hXprimeSupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card X →
      p ∣ Nat.card {x : P // x ∈ involutions P})
    (_hLen : OmegaLength X P 3) :
    (IsSuzukiTwoTypeB (⊤ : Subgroup P) ∨
      IsSuzukiTwoTypeC (⊤ : Subgroup P) ∨
        IsSuzukiTwoTypeD (⊤ : Subgroup P)) ∧
      ∃ B : Subgroup P,
        ((∃ actor : X, Lemma12TypeBActorBranchData X P actor B) ∨
          IsSuzukiTwoTypeC (⊤ : Subgroup P) ∨
            IsSuzukiTwoTypeD (⊤ : Subgroup P)) ∧
        Lemma12SummandData X P B ∧
        Lemma12IsomorphicSummandCriterionData X P B := by
  rcases _hLen with ⟨subgroups, htop, hbot, _hle, hsteps⟩
  let A : Subgroup P := subgroups ⟨1, by decide⟩
  let B : Subgroup P := subgroups ⟨2, by decide⟩
  have hupper :
      A < ⊤ ∧ (⊤ : Subgroup P).Normal ∧ A.Normal ∧
        IsXInvariantSubgroup X (⊤ : Subgroup P) ∧
        IsXInvariantSubgroup X A ∧
        ∀ L : Subgroup P, L.Normal → IsXInvariantSubgroup X L →
          A ≤ L → L ≤ ⊤ → L = A ∨ L = ⊤ := by
    have h := hsteps (0 : Fin 3)
    simpa [A, htop] using h
  have hmiddle :
      B < A ∧ A.Normal ∧ B.Normal ∧
        IsXInvariantSubgroup X A ∧ IsXInvariantSubgroup X B ∧
        ∀ L : Subgroup P, L.Normal → IsXInvariantSubgroup X L →
          B ≤ L → L ≤ A → L = B ∨ L = A := by
    have h := hsteps (1 : Fin 3)
    simpa [A, B] using h
  have hlower :
      (⊥ : Subgroup P) < B ∧ B.Normal ∧ (⊥ : Subgroup P).Normal ∧
        IsXInvariantSubgroup X B ∧
        IsXInvariantSubgroup X (⊥ : Subgroup P) ∧
        ∀ L : Subgroup P, L.Normal → IsXInvariantSubgroup X L →
          ⊥ ≤ L → L ≤ B → L = ⊥ ∨ L = B := by
    have hs3 : subgroups (3 : Fin 4) = (⊥ : Subgroup P) := by
      simpa using hbot
    have h := hsteps (2 : Fin 3)
    simpa [B, hs3] using h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := X)
  have hchain := lemma12_chain_typeBCD_with_isomorphic_criterion
    _hP _hXcyclic _hXfaithful
    _hXtrans _hXprimeSupport g hg hupper hmiddle hlower
  exact ⟨hchain.1, B, hchain.2.1, hchain.2.2.1, hchain.2.2.2.1⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Higman Lemma 12 with the historical full-data interface. -/
public theorem lemma12_length_three_typeBCD_full_data
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (_hP : IsSuzukiTwoGroup P)
    (_hXcyclic : IsCyclic X) (_hXfaithful : FaithfulSMul X P)
    (_hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    (_hXprimeSupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card X →
      p ∣ Nat.card {x : P // x ∈ involutions P})
    (_hLen : OmegaLength X P 3) :
    (IsSuzukiTwoTypeB (⊤ : Subgroup P) ∨
      IsSuzukiTwoTypeC (⊤ : Subgroup P) ∨
        IsSuzukiTwoTypeD (⊤ : Subgroup P)) ∧
      ∃ B : Subgroup P,
        ((∃ actor : X, Lemma12TypeBActorBranchData X P actor B) ∨
          IsSuzukiTwoTypeC (⊤ : Subgroup P) ∨
            IsSuzukiTwoTypeD (⊤ : Subgroup P)) ∧
        Lemma12SummandData X P B := by
  rcases lemma12_length_three_typeBCD_with_isomorphic_criterion
      _hP _hXcyclic _hXfaithful _hXtrans _hXprimeSupport _hLen with
    ⟨hclassification, B, hbranch, hsummands, _hcriterion⟩
  exact ⟨hclassification, B, hbranch, hsummands⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Higman Lemma 12 together with the unconditional length-three summand data. -/
public theorem lemma12_length_three_typeBCD_summand_data
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (_hP : IsSuzukiTwoGroup P)
    (_hXcyclic : IsCyclic X) (_hXfaithful : FaithfulSMul X P)
    (_hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    (_hXprimeSupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card X →
      p ∣ Nat.card {x : P // x ∈ involutions P})
    (_hLen : OmegaLength X P 3) :
    (IsSuzukiTwoTypeB (⊤ : Subgroup P) ∨
      IsSuzukiTwoTypeC (⊤ : Subgroup P) ∨
        IsSuzukiTwoTypeD (⊤ : Subgroup P)) ∧
      ∃ B : Subgroup P, Lemma12SummandData X P B := by
  rcases lemma12_length_three_typeBCD_full_data _hP _hXcyclic
      _hXfaithful _hXtrans _hXprimeSupport _hLen with
    ⟨hclassification, B, _hactorClassification, hsummandData⟩
  exact ⟨hclassification, B, hsummandData⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Higman Lemma 12: a Suzuki `2`-group of Omega-length three is type B, C, or
D. -/
public theorem lemma12_length_three_typeBCD
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (_hP : IsSuzukiTwoGroup P)
    (_hXcyclic : IsCyclic X) (_hXfaithful : FaithfulSMul X P)
    (_hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    (_hXprimeSupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card X →
      p ∣ Nat.card {x : P // x ∈ involutions P})
    (_hLen : OmegaLength X P 3) :
    IsSuzukiTwoTypeB (⊤ : Subgroup P) ∨
      IsSuzukiTwoTypeC (⊤ : Subgroup P) ∨
        IsSuzukiTwoTypeD (⊤ : Subgroup P) := by
  exact (lemma12_length_three_typeBCD_summand_data _hP _hXcyclic
    _hXfaithful _hXtrans _hXprimeSupport _hLen).1

end Higman
end External
end CFSG.BenderSuzuki
