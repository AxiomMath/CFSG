module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.lemma_3_1
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert-Blackburn XI.3.3

The statement follows Volume III, physical pages 192-193.  All projective
points and the Suzuki ovoid are written inline, without a wrapper definition.
-/

namespace CFSG.BenderSuzuki
namespace External

open _root_.CFSG.BenderSuzuki.MatrixGroups
open PFAppendixIII
open scoped LinearAlgebra.Projectivization
open scoped Pointwise

/-- The explicit Tits power formula squares to Frobenius on
`GF(2^(2m+1))`. -/
public theorem binaryGaloisField_tits_formula_sq
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    ∀ x, pi (pi x) = x ^ 2 := by
  let K := BinaryGaloisField (2 * m + 1)
  have hK_card : Nat.card K = 2 ^ (2 * m + 1) := by
    simpa [K, BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  intro x
  let fintype : Fintype K := Fintype.ofFinite K
  calc
    pi (pi x) = (pi x) ^ (2 ^ (m + 1)) := hpi (pi x)
    _ = (x ^ (2 ^ (m + 1))) ^ (2 ^ (m + 1)) := by rw [hpi]
    _ = x ^ (2 ^ (m + 1 + (m + 1))) := by rw [← pow_mul, ← pow_add]
    _ = x ^ (2 ^ ((2 * m + 1) + 1)) := by
      congr 2
      omega
    _ = (x ^ (2 ^ (2 * m + 1))) ^ 2 := by rw [pow_succ, pow_mul]
    _ = x ^ 2 := by
      have hx_card : x ^ Nat.card K = x := by
        have hpow : x ^ (@Fintype.card K fintype) = x :=
          @FiniteField.pow_card K (inferInstance : GroupWithZero K) fintype x
        simpa only [@Fintype.card_eq_nat_card K fintype] using hpow
      rw [← hK_card, hx_card]

/-- The normalized finite-point parametrization of the Suzuki ovoid is injective. -/
private theorem suzukiOvoidPoint_injective
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    Function.Injective (fun z : K × K =>
      Projectivization.mk K
        ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
        (by simp)) := by
  let K := BinaryGaloisField (2 * m + 1)
  let p : K × K → ℙ K (Fin 4 → K) := fun z =>
    Projectivization.mk K
      ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
      (by simp)
  change Function.Injective p
  intro z w hzw
  dsimp only [p] at hzw
  rw [Projectivization.mk_eq_mk_iff] at hzw
  rcases hzw with ⟨c, hc⟩
  have hc_one : (c : K) = 1 := by
    have hc3 := congrFun hc (3 : Fin 4)
    simpa [Units.smul_def] using hc3
  apply Prod.ext
  · have hc2 := congrFun hc (2 : Fin 4)
    simpa [Units.smul_def, hc_one] using hc2.symm
  · have hc1 := congrFun hc (1 : Fin 4)
    simpa [Units.smul_def, hc_one] using hc1.symm

/-- The point at infinity is not one of the normalized finite ovoid points. -/
public theorem suzukiOvoidInfinity_not_mem_range
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K × K → ℙ K (Fin 4 → K) := fun z =>
      Projectivization.mk K
        ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
        (by simp)
    pinf ∉ Set.range p := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K × K → ℙ K (Fin 4 → K) := fun z =>
    Projectivization.mk K
      ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
      (by simp)
  change pinf ∉ Set.range p
  intro hpinf
  rcases hpinf with ⟨z, hz⟩
  dsimp only [pinf, p] at hz
  rw [Projectivization.mk_eq_mk_iff] at hz
  rcases hz with ⟨c, hc⟩
  have hc_zero : (c : K) = 0 := by
    have hc3 := congrFun hc (3 : Fin 4)
    simp at hc3
  exact c.ne_zero hc_zero

/-- The Suzuki ovoid has exactly `q ^ 2 + 1` points. -/
private theorem suzukiOvoid_card
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K × K → ℙ K (Fin 4 → K) := fun z =>
      Projectivization.mk K
        ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
        (by simp)
    let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range p
    Nat.card {z // z ∈ O} = (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K × K → ℙ K (Fin 4 → K) := fun z =>
    Projectivization.mk K
      ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
      (by simp)
  let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range p
  change Nat.card {z // z ∈ O} = (2 ^ (2 * m + 1)) ^ 2 + 1
  have hp_inj : Function.Injective p :=
    suzukiOvoidPoint_injective m pi
  have hpinf : pinf ∉ Set.range p :=
    suzukiOvoidInfinity_not_mem_range m pi
  let toO : Option (K × K) → {z // z ∈ O}
    | none => ⟨pinf, Or.inl (Set.mem_singleton pinf)⟩
    | some z => ⟨p z, Or.inr ⟨z, rfl⟩⟩
  have htoO_inj : Function.Injective toO := by
    intro u v huv
    cases u with
    | none =>
      cases v with
      | none => rfl
      | some v =>
        exfalso
        exact hpinf ⟨v, (congrArg Subtype.val huv).symm⟩
    | some u =>
      cases v with
      | none =>
        exfalso
        exact hpinf ⟨u, congrArg Subtype.val huv⟩
      | some v =>
        exact congrArg Option.some (hp_inj (congrArg Subtype.val huv))
  have htoO_surj : Function.Surjective toO := by
    intro z
    rcases z with ⟨z, hz⟩
    change z ∈ {pinf} ∪ Set.range p at hz
    rcases hz with hz | ⟨w, hw⟩
    · have hz_eq : z = pinf := by simpa using hz
      subst z
      exact ⟨none, rfl⟩
    · subst z
      exact ⟨some w, rfl⟩
  let e : Option (K × K) ≃ {z // z ∈ O} :=
    Equiv.ofBijective toO ⟨htoO_inj, htoO_surj⟩
  have hK_card : Nat.card K = 2 ^ (2 * m + 1) := by
    simpa [K, BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  calc
    Nat.card {z // z ∈ O} = Nat.card (Option (K × K)) :=
      Nat.card_congr e.symm
    _ = Nat.card (K × K) + 1 := Finite.card_option
    _ = Nat.card K * Nat.card K + 1 := by rw [Nat.card_prod]
    _ = (2 ^ (2 * m + 1)) ^ 2 + 1 := by rw [hK_card, pow_two]

/-- The odd-degree trace obstruction excludes solutions of `pi z + z = 1`.
This is the anisotropy input in the Weyl-coordinate calculation. -/
private theorem tits_add_eq_one_impossible
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1)) :
    ¬ ∃ z : BinaryGaloisField (2 * m + 1), pi z + z = 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  let toAlg : (K ≃+* K) → (K ≃ₐ[ZMod 2] K) := fun e =>
    AlgEquiv.ofRingEquiv (f := e) (fun x => by
      have hcomp : e.toRingHom.comp (algebraMap (ZMod 2) K) =
          algebraMap (ZMod 2) K := Subsingleton.elim _ _
      exact DFunLike.congr_fun hcomp x)
  have hfinrank : Module.finrank (ZMod 2) K = 2 * m + 1 := by
    simpa [K, BinaryGaloisField] using
      GaloisField.finrank 2 (show 2 * m + 1 ≠ 0 by omega)
  have hcast : ((2 * m + 1 : ℕ) : ZMod 2) = 1 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    exact Or.inl (CharP.cast_eq_zero (ZMod 2) 2)
  rintro ⟨z, hz⟩
  have htrace_pi :
      Algebra.trace (ZMod 2) K (pi z) = Algebra.trace (ZMod 2) K z := by
    exact Algebra.trace_eq_of_algEquiv (toAlg pi) z
  have htrace_one :
      Algebra.trace (ZMod 2) K (1 : K) =
        (Module.finrank (ZMod 2) K : ZMod 2) := by
    simpa using
      (Algebra.trace_algebraMap (R := ZMod 2) (S := K) (1 : ZMod 2))
  have htrace := congrArg (Algebra.trace (ZMod 2) K) hz
  rw [map_add, htrace_pi, htrace_one, hfinrank] at htrace
  rw [CharTwo.add_self_eq_zero, hcast] at htrace
  exact zero_ne_one htrace

/-- The Suzuki norm vanishes only at the zero coordinate pair. -/
public theorem suzukiOvoidNorm_eq_zero
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (x y : BinaryGaloisField (2 * m + 1)) :
    x * y + pi x * x ^ 2 + pi y = 0 ↔ x = 0 ∧ y = 0 := by
  let K := BinaryGaloisField (2 * m + 1)
  constructor
  · intro hnorm
    by_cases hx : x = 0
    · subst x
      simp only [zero_mul, map_zero, zero_mul, zero_add] at hnorm
      exact ⟨rfl, pi.injective (by simpa using hnorm)⟩
    · exfalso
      have hpix : pi x ≠ 0 := (map_ne_zero pi).2 hx
      let c : K := x * pi x
      let z : K := c⁻¹ * y
      have hc : c ≠ 0 := mul_ne_zero hx hpix
      have hy : y = c * z := by
        dsimp only [z]
        rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      have hpi_c : pi c = pi x * x ^ 2 := by
        dsimp only [c]
        rw [map_mul, hpi_sq]
      have hpi_y : pi y = pi c * pi z := by
        rw [hy, map_mul]
      have hfactor : x ^ 2 * pi x * (pi z + z + 1) = 0 := by
        calc
          x ^ 2 * pi x * (pi z + z + 1) =
              x * y + pi x * x ^ 2 + pi y := by
            rw [hpi_y, hy, hpi_c]
            dsimp only [c]
            ring
          _ = 0 := hnorm
      have hprefactor : x ^ 2 * pi x ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hx) hpix
      have hzsum : pi z + z + 1 = 0 :=
        (mul_eq_zero.mp hfactor).resolve_left hprefactor
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero _ 2
      have hz : pi z + z = 1 := by
        linear_combination hzsum - htwo
      exact tits_add_eq_one_impossible m pi ⟨z, hz⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- The reciprocal coordinates obtained from a nonzero Suzuki norm have norm
equal to the reciprocal norm. -/
private theorem suzukiOvoidNorm_inv
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (x y : BinaryGaloisField (2 * m + 1)) :
    let n := x * y + pi x * x ^ 2 + pi y
    n ≠ 0 →
      (n⁻¹ * y) * (n⁻¹ * x) +
          pi (n⁻¹ * y) * (n⁻¹ * y) ^ 2 + pi (n⁻¹ * x) = n⁻¹ := by
  let K := BinaryGaloisField (2 * m + 1)
  dsimp only
  let n : K := x * y + pi x * x ^ 2 + pi y
  change n ≠ 0 →
    (n⁻¹ * y) * (n⁻¹ * x) +
        pi (n⁻¹ * y) * (n⁻¹ * y) ^ 2 + pi (n⁻¹ * x) = n⁻¹
  intro hn
  have hpin : pi n ≠ 0 := (map_ne_zero pi).2 hn
  have hpi_n : pi n = pi x * pi y + x ^ 2 * (pi x) ^ 2 + y ^ 2 := by
    dsimp only [n]
    simp only [map_add, map_mul, map_pow, hpi_sq]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero _ 2
  have hcore :
      pi n * (x * y) + pi y * y ^ 2 + pi x * n ^ 2 = pi n * n := by
    rw [hpi_n]
    dsimp only [n]
    linear_combination
      (pi x * pi y * x * y + (pi x) ^ 2 * x ^ 3 * y) * htwo
  simp only [map_mul, map_inv₀]
  have hd : pi n * n ^ 2 ≠ 0 := mul_ne_zero hpin (pow_ne_zero _ hn)
  apply mul_left_cancel₀ hd
  calc
    (pi n * n ^ 2) *
        ((n⁻¹ * y) * (n⁻¹ * x) +
          (pi n)⁻¹ * pi y * (n⁻¹ * y) ^ 2 + (pi n)⁻¹ * pi x) =
        pi n * (x * y) + pi y * y ^ 2 + pi x * n ^ 2 := by
      field_simp [hn, hpin]
    _ = pi n * n := hcore
    _ = (pi n * n ^ 2) * n⁻¹ := by
      field_simp [hn, hpin]

/-- The Suzuki Weyl element sends the point at infinity to the zero finite
point. -/
public theorem suzukiWeyl_smul_infinity
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    (Matrix.GeneralLinearGroup.toLin (SuzukiWeylGL m)).toLinearEquiv • pinf =
      p 0 0 := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  change (Matrix.GeneralLinearGroup.toLin
    (SuzukiWeylGL m)).toLinearEquiv • pinf = p 0 0
  dsimp only [pinf, p]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;>
    simp [SuzukiWeylGL, SuzukiWeylMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The Suzuki Weyl element sends the zero finite point to the point at
infinity. -/
public theorem suzukiWeyl_smul_zero
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    (Matrix.GeneralLinearGroup.toLin (SuzukiWeylGL m)).toLinearEquiv • p 0 0 =
      pinf := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  change (Matrix.GeneralLinearGroup.toLin
    (SuzukiWeylGL m)).toLinearEquiv • p 0 0 = pinf
  dsimp only [pinf, p]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;>
    simp [SuzukiWeylGL, SuzukiWeylMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Away from the zero finite point, the Suzuki Weyl element acts by the
reciprocal norm-coordinate formula. -/
private theorem suzukiWeyl_smul_finite_of_norm_ne_zero
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (x y : BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let p : K → K → ℙ K (Fin 4 → K) := fun u v =>
      Projectivization.mk K
        ![u * v + pi u * u ^ 2 + pi v, v, u, 1] (by simp)
    let n := x * y + pi x * x ^ 2 + pi y
    n ≠ 0 →
      (Matrix.GeneralLinearGroup.toLin (SuzukiWeylGL m)).toLinearEquiv •
        p x y = p (n⁻¹ * y) (n⁻¹ * x) := by
  let K := BinaryGaloisField (2 * m + 1)
  let p : K → K → ℙ K (Fin 4 → K) := fun u v =>
    Projectivization.mk K
      ![u * v + pi u * u ^ 2 + pi v, v, u, 1] (by simp)
  dsimp only
  let n : K := x * y + pi x * x ^ 2 + pi y
  change n ≠ 0 →
    (Matrix.GeneralLinearGroup.toLin (SuzukiWeylGL m)).toLinearEquiv •
      p x y = p (n⁻¹ * y) (n⁻¹ * x)
  intro hn
  have hnorm_inv :
      (n⁻¹ * y) * (n⁻¹ * x) +
          pi (n⁻¹ * y) * (n⁻¹ * y) ^ 2 + pi (n⁻¹ * x) = n⁻¹ := by
    exact suzukiOvoidNorm_inv m pi hpi_sq x y hn
  dsimp only [p]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨n, ?_⟩
  have hncancel (z : K) : n * (n⁻¹ * z) = z := by
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  funext i
  fin_cases i
  · rw [hnorm_inv]
    simp [SuzukiWeylGL, SuzukiWeylMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    exact mul_inv_cancel₀ hn
  · simp [SuzukiWeylGL, SuzukiWeylMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, hncancel]
  · simp [SuzukiWeylGL, SuzukiWeylMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, hncancel]
  · simp [SuzukiWeylGL, SuzukiWeylMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, n]

/-- Every Suzuki root element fixes the distinguished point at infinity. -/
private theorem suzukiRoot_smul_infinity
    (m : ℕ)
    (a b : BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    (Matrix.GeneralLinearGroup.toLin (SuzukiRootGL m a b)).toLinearEquiv •
        pinf = pinf := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  change (Matrix.GeneralLinearGroup.toLin
    (SuzukiRootGL m a b)).toLinearEquiv • pinf = pinf
  dsimp only [pinf]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;>
    simp [SuzukiRootGL, SuzukiRootMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- A Suzuki root element acts on the normalized finite ovoid coordinates by
the root-group multiplication formula. -/
private theorem suzukiRoot_smul_finite
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b x y : BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let p : K → K → ℙ K (Fin 4 → K) := fun u v =>
      Projectivization.mk K
        ![u * v + pi u * u ^ 2 + pi v, v, u, 1] (by simp)
    (Matrix.GeneralLinearGroup.toLin (SuzukiRootGL m a b)).toLinearEquiv •
        p x y = p (x + a) (y + b + pi a * (x + a)) := by
  let K := BinaryGaloisField (2 * m + 1)
  let p : K → K → ℙ K (Fin 4 → K) := fun u v =>
    Projectivization.mk K
      ![u * v + pi u * u ^ 2 + pi v, v, u, 1] (by simp)
  change (Matrix.GeneralLinearGroup.toLin
    (SuzukiRootGL m a b)).toLinearEquiv • p x y =
      p (x + a) (y + b + pi a * (x + a))
  dsimp only [p]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  have hpow (z : K) : z ^ (2 ^ (m + 1)) = pi z :=
    (hpi_formula z).symm
  have hpow_one (z : K) : z ^ (1 + 2 ^ (m + 1)) = z * pi z := by
    rw [pow_add, hpow, pow_one]
  have hpow_two (z : K) : z ^ (2 + 2 ^ (m + 1)) = z ^ 2 * pi z := by
    rw [pow_add, hpow]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero _ 2
  funext i
  fin_cases i <;>
    simp [SuzukiRootGL, SuzukiRootMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      hpow, hpow_one, hpow_two, map_add, map_mul, hpi_sq,
      CharTwo.add_self_eq_zero]
  linear_combination
    (x ^ 2 * pi a + 2 * x * a * pi a + x * a * pi x +
      a ^ 2 * pi a + a ^ 2 * pi x) * htwo
  ring

/-- Every Suzuki torus element fixes the distinguished point at infinity. -/
public theorem suzukiTorus_smul_infinity
    (m : ℕ)
    (u : (BinaryGaloisField (2 * m + 1))ˣ) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    (Matrix.GeneralLinearGroup.toLin (SuzukiTorusGL m u)).toLinearEquiv •
        pinf = pinf := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  change (Matrix.GeneralLinearGroup.toLin
    (SuzukiTorusGL m u)).toLinearEquiv • pinf = pinf
  dsimp only [pinf]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨(u : K) ^ (1 + 2 ^ m), ?_⟩
  funext i
  fin_cases i <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- A Suzuki torus element rescales the two normalized finite ovoid
coordinates by `u` and `u * pi u`, respectively. -/
public theorem suzukiTorus_smul_finite
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (u : (BinaryGaloisField (2 * m + 1))ˣ)
    (x y : BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let p : K → K → ℙ K (Fin 4 → K) := fun v w =>
      Projectivization.mk K
        ![v * w + pi v * v ^ 2 + pi w, w, v, 1] (by simp)
    (Matrix.GeneralLinearGroup.toLin (SuzukiTorusGL m u)).toLinearEquiv •
        p x y = p ((u : K) * x) ((u : K) * pi (u : K) * y) := by
  let K := BinaryGaloisField (2 * m + 1)
  let p : K → K → ℙ K (Fin 4 → K) := fun v w =>
    Projectivization.mk K
      ![v * w + pi v * v ^ 2 + pi w, w, v, 1] (by simp)
  change (Matrix.GeneralLinearGroup.toLin
    (SuzukiTorusGL m u)).toLinearEquiv • p x y =
      p ((u : K) * x) ((u : K) * pi (u : K) * y)
  dsimp only [p]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨((u : K) ^ (1 + 2 ^ m))⁻¹, ?_⟩
  have hu : (u : K) ≠ 0 := u.ne_zero
  let s : K := (u : K) ^ (2 ^ m)
  have hs : (u : K) ^ (2 ^ m) = s := rfl
  have hs_ne : s ≠ 0 := by
    rw [← hs]
    exact pow_ne_zero _ hu
  have huouter : (u : K) ^ (1 + 2 ^ m) ≠ 0 := pow_ne_zero _ hu
  have hpi_u : pi (u : K) = s ^ 2 := by
    calc
      pi (u : K) = ((u : K) ^ (2 ^ m)) ^ 2 := by
        rw [hpi_formula, pow_succ, pow_mul]
      _ = s ^ 2 := by rw [hs]
  have huouter_formula :
      (u : K) ^ (1 + 2 ^ m) = (u : K) * s := by
    rw [pow_add, pow_one, hs]
  funext i
  fin_cases i <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      map_mul, hpi_sq]
  · rw [hpi_u, huouter_formula]
    have hus_ne : (u : K) * s ≠ 0 := mul_ne_zero hu hs_ne
    have hinner :
        (u : K) * x * ((u : K) * s ^ 2 * y) +
            s ^ 2 * pi x * ((u : K) * x) ^ 2 +
            s ^ 2 * (u : K) ^ 2 * pi y =
          ((u : K) * s) ^ 2 * (x * y + pi x * x ^ 2 + pi y) := by
      ring
    calc
      ((u : K) * s)⁻¹ *
          ((u : K) * x * ((u : K) * s ^ 2 * y) +
            s ^ 2 * pi x * ((u : K) * x) ^ 2 +
            s ^ 2 * (u : K) ^ 2 * pi y) =
          ((u : K) * s)⁻¹ * (((u : K) * s) ^ 2 *
            (x * y + pi x * x ^ 2 + pi y)) := by rw [hinner]
      _ = ((u : K) * s) * (x * y + pi x * x ^ 2 + pi y) := by
        rw [pow_two, mul_assoc]
        exact inv_mul_cancel_left₀ hus_ne _
  · rw [hpi_u, huouter_formula, hs]
    have hus_ne : (u : K) * s ≠ 0 := mul_ne_zero hu hs_ne
    rw [show (u : K) * s ^ 2 * y =
      ((u : K) * s) * (s * y) by ring]
    exact inv_mul_cancel_left₀ hus_ne (s * y)
  · rw [huouter_formula, hs, mul_inv_rev]
    rw [mul_assoc, inv_mul_cancel_left₀ hu]

/-- Each of the three kinds of standard Suzuki generators preserves the
Suzuki ovoid. -/
private theorem suzukiGenerator_smul_mem_ovoid
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∀ A : GL (Fin 4) K, A ∈ SuzukiMatrixGeneratorSet m →
      ∀ z, z ∈ O →
        (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  change ∀ A : GL (Fin 4) K, A ∈ SuzukiMatrixGeneratorSet m →
    ∀ z, z ∈ O →
      (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O
  intro A hA z hz
  change (∃ a b : K, A = SuzukiRootGL m a b) ∨
    (∃ u : Kˣ, A = SuzukiTorusGL m u) ∨ A = SuzukiWeylGL m at hA
  rcases hA with hroot | hrest
  · rcases hroot with ⟨a, b, rfl⟩
    rcases hz with hz | ⟨w, rfl⟩
    · have hz_eq : z = pinf := by simpa using hz
      subst z
      rw [suzukiRoot_smul_infinity]
      exact Or.inl rfl
    · rcases w with ⟨x, y⟩
      rw [suzukiRoot_smul_finite m pi hpi_sq hpi_formula]
      exact Or.inr ⟨(x + a, y + b + pi a * (x + a)), rfl⟩
  · rcases hrest with htorus | hweyl
    · rcases htorus with ⟨u, rfl⟩
      rcases hz with hz | ⟨w, rfl⟩
      · have hz_eq : z = pinf := by simpa using hz
        subst z
        rw [suzukiTorus_smul_infinity]
        exact Or.inl rfl
      · rcases w with ⟨x, y⟩
        rw [suzukiTorus_smul_finite m pi hpi_sq hpi_formula]
        exact Or.inr ⟨((u : K) * x, (u : K) * pi (u : K) * y), rfl⟩
    · subst A
      rcases hz with hz | ⟨w, rfl⟩
      · have hz_eq : z = pinf := by simpa using hz
        subst z
        rw [suzukiWeyl_smul_infinity m pi]
        exact Or.inr ⟨(0, 0), rfl⟩
      · rcases w with ⟨x, y⟩
        let n : K := x * y + pi x * x ^ 2 + pi y
        by_cases hn : n = 0
        · have hxy : x = 0 ∧ y = 0 :=
            (suzukiOvoidNorm_eq_zero m pi hpi_sq x y).1 hn
          rcases hxy with ⟨rfl, rfl⟩
          rw [suzukiWeyl_smul_zero m pi]
          exact Or.inl rfl
        · rw [suzukiWeyl_smul_finite_of_norm_ne_zero m pi hpi_sq x y hn]
          exact Or.inr ⟨(n⁻¹ * y, n⁻¹ * x), rfl⟩

/-- The subgroup generated by the standard Suzuki matrices preserves the
Suzuki ovoid. -/
private theorem suzukiMatrixGroup_smul_mem_ovoid
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∀ g : SuzukiMatrixGroup m, ∀ z, z ∈ O →
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • z ∈ O := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  change ∀ g : SuzukiMatrixGroup m, ∀ z, z ∈ O →
    (Matrix.GeneralLinearGroup.toLin
      (g : GL (Fin 4) K)).toLinearEquiv • z ∈ O
  let S : Subgroup (GL (Fin 4) K) :=
    (MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O).comap
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
  have hO_finite : O.Finite := Set.toFinite O
  have hgenerators : SuzukiMatrixGeneratorSet m ⊆ S := by
    intro A hA
    change Matrix.GeneralLinearGroup.toLin A ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O
    rw [MulAction.mem_stabilizer_set_iff_smul_set_subset hO_finite]
    apply Set.smul_set_subset_iff.2
    intro z hz
    change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O
    exact suzukiGenerator_smul_mem_ovoid
      m pi hpi_sq hpi_formula A hA z hz
  have hclosure : SuzukiMatrixSubgroup m ≤ S := by
    rw [SuzukiMatrixSubgroup, Subgroup.closure_le]
    exact hgenerators
  intro g z hz
  have hgS := hclosure g.property
  change Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K) ∈
    MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O at hgS
  have hsubset :
      Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K) • O ⊆ O :=
    (MulAction.mem_stabilizer_set_iff_smul_set_subset hO_finite).1 hgS
  have hz' := hsubset (Set.smul_mem_smul_set hz)
  change (Matrix.GeneralLinearGroup.toLin
    (g : GL (Fin 4) K)).toLinearEquiv • z ∈ O
  exact hz'

/-- The root element with coordinates `(x,y)` sends `p(x,y)` to the zero
finite point. -/
private theorem suzukiRoot_smul_self_zero
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (x y : BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let p : K → K → ℙ K (Fin 4 → K) := fun u v =>
      Projectivization.mk K
        ![u * v + pi u * u ^ 2 + pi v, v, u, 1] (by simp)
    (Matrix.GeneralLinearGroup.toLin
      (SuzukiRootGL m x y)).toLinearEquiv • p x y = p 0 0 := by
  let K := BinaryGaloisField (2 * m + 1)
  let p : K → K → ℙ K (Fin 4 → K) := fun u v =>
    Projectivization.mk K
      ![u * v + pi u * u ^ 2 + pi v, v, u, 1] (by simp)
  change (Matrix.GeneralLinearGroup.toLin
    (SuzukiRootGL m x y)).toLinearEquiv • p x y = p 0 0
  rw [suzukiRoot_smul_finite m pi hpi_sq hpi_formula]
  have hx0 : x + x = 0 := CharTwo.add_self_eq_zero x
  have hy0 : y + y + pi x * (x + x) = 0 := by
    rw [hx0, CharTwo.add_self_eq_zero y]
    simp
  rw [hy0, hx0]

/-- Every ovoid point can be moved to the point at infinity by an explicit
word in a root element and the Weyl element. -/
private theorem suzukiOvoid_exists_smul_eq_infinity
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∀ z, z ∈ O → ∃ g : SuzukiMatrixGroup m,
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • z = pinf := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  change ∀ z, z ∈ O → ∃ g : SuzukiMatrixGroup m,
    (Matrix.GeneralLinearGroup.toLin
      (g : GL (Fin 4) K)).toLinearEquiv • z = pinf
  intro z hz
  rcases hz with hz | ⟨wxy, rfl⟩
  · have hz_eq : z = pinf := by simpa using hz
    subst z
    let r0 : SuzukiMatrixGroup m :=
      ⟨SuzukiRootGL m 0 0, Subgroup.subset_closure (by
        exact Or.inl ⟨0, 0, rfl⟩)⟩
    refine ⟨r0, ?_⟩
    change (Matrix.GeneralLinearGroup.toLin
      (SuzukiRootGL m 0 0)).toLinearEquiv • pinf = pinf
    exact suzukiRoot_smul_infinity m 0 0
  · rcases wxy with ⟨x, y⟩
    let r : SuzukiMatrixGroup m :=
      ⟨SuzukiRootGL m x y, Subgroup.subset_closure (by
        exact Or.inl ⟨x, y, rfl⟩)⟩
    let w : SuzukiMatrixGroup m :=
      ⟨SuzukiWeylGL m, Subgroup.subset_closure (by
        exact Or.inr (Or.inr rfl))⟩
    have hr :
        (Matrix.GeneralLinearGroup.toLin
          (r : GL (Fin 4) K)).toLinearEquiv • p x y = p 0 0 := by
      change (Matrix.GeneralLinearGroup.toLin
        (SuzukiRootGL m x y)).toLinearEquiv • p x y = p 0 0
      exact suzukiRoot_smul_self_zero m pi hpi_sq hpi_formula x y
    have hw :
        (Matrix.GeneralLinearGroup.toLin
          (w : GL (Fin 4) K)).toLinearEquiv • p 0 0 = pinf := by
      change (Matrix.GeneralLinearGroup.toLin
        (SuzukiWeylGL m)).toLinearEquiv • p 0 0 = pinf
      exact suzukiWeyl_smul_zero m pi
    refine ⟨w * r, ?_⟩
    calc
      (Matrix.GeneralLinearGroup.toLin
          ((w * r : SuzukiMatrixGroup m) : GL (Fin 4) K)).toLinearEquiv •
          p x y =
        (Matrix.GeneralLinearGroup.toLin
          (w : GL (Fin 4) K)).toLinearEquiv •
          ((Matrix.GeneralLinearGroup.toLin
            (r : GL (Fin 4) K)).toLinearEquiv • p x y) := by
              change (Matrix.GeneralLinearGroup.toLin
                ((w : GL (Fin 4) K) * (r : GL (Fin 4) K))).toLinearEquiv •
                  p x y = _
              rw [map_mul]
              change (Matrix.GeneralLinearGroup.toLin (w : GL (Fin 4) K) *
                  Matrix.GeneralLinearGroup.toLin (r : GL (Fin 4) K)) • p x y =
                Matrix.GeneralLinearGroup.toLin (w : GL (Fin 4) K) •
                  (Matrix.GeneralLinearGroup.toLin (r : GL (Fin 4) K) • p x y)
              exact mul_smul _ _ _
      _ = (Matrix.GeneralLinearGroup.toLin
          (w : GL (Fin 4) K)).toLinearEquiv • p 0 0 := by rw [hr]
      _ = pinf := hw

/-- Every ordered pair of distinct ovoid points can be moved to the standard
pair `(pinf, p(0,0))`. -/
private theorem suzukiOvoid_exists_pair_to_standard
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∀ a b, a ∈ O → b ∈ O → a ≠ b →
      ∃ g : SuzukiMatrixGroup m,
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • a = pinf ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • b = p 0 0 := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  change ∀ a b, a ∈ O → b ∈ O → a ≠ b →
    ∃ g : SuzukiMatrixGroup m,
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • a = pinf ∧
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • b = p 0 0
  intro a b ha hb hab
  obtain ⟨ga, hga⟩ :=
    suzukiOvoid_exists_smul_eq_infinity m pi hpi_sq hpi_formula a ha
  have hgb_mem :
      (Matrix.GeneralLinearGroup.toLin
        (ga : GL (Fin 4) K)).toLinearEquiv • b ∈ O :=
    suzukiMatrixGroup_smul_mem_ovoid
      m pi hpi_sq hpi_formula ga b hb
  have hgb_ne :
      (Matrix.GeneralLinearGroup.toLin
        (ga : GL (Fin 4) K)).toLinearEquiv • b ≠ pinf := by
    intro hgb
    have hsame :
        (Matrix.GeneralLinearGroup.toLin
          (ga : GL (Fin 4) K)).toLinearEquiv • b =
        (Matrix.GeneralLinearGroup.toLin
          (ga : GL (Fin 4) K)).toLinearEquiv • a := hgb.trans hga.symm
    have hba : b = a := by
      change Matrix.GeneralLinearGroup.toLin (ga : GL (Fin 4) K) • b =
        Matrix.GeneralLinearGroup.toLin (ga : GL (Fin 4) K) • a at hsame
      exact smul_left_cancel _ hsame
    exact hab hba.symm
  rcases hgb_mem with hgb_inf | ⟨xy, hxy⟩
  · exact False.elim (hgb_ne (by simpa using hgb_inf))
  · rcases xy with ⟨x, y⟩
    let r : SuzukiMatrixGroup m :=
      ⟨SuzukiRootGL m x y, Subgroup.subset_closure (by
        exact Or.inl ⟨x, y, rfl⟩)⟩
    have hr_inf :
        (Matrix.GeneralLinearGroup.toLin
          (r : GL (Fin 4) K)).toLinearEquiv • pinf = pinf := by
      change (Matrix.GeneralLinearGroup.toLin
        (SuzukiRootGL m x y)).toLinearEquiv • pinf = pinf
      exact suzukiRoot_smul_infinity m x y
    have hr_zero :
        (Matrix.GeneralLinearGroup.toLin
          (r : GL (Fin 4) K)).toLinearEquiv • p x y = p 0 0 := by
      change (Matrix.GeneralLinearGroup.toLin
        (SuzukiRootGL m x y)).toLinearEquiv • p x y = p 0 0
      exact suzukiRoot_smul_self_zero m pi hpi_sq hpi_formula x y
    have hcomp (z : ℙ K (Fin 4 → K)) :
        (Matrix.GeneralLinearGroup.toLin
          ((r * ga : SuzukiMatrixGroup m) : GL (Fin 4) K)).toLinearEquiv • z =
        (Matrix.GeneralLinearGroup.toLin
          (r : GL (Fin 4) K)).toLinearEquiv •
          ((Matrix.GeneralLinearGroup.toLin
            (ga : GL (Fin 4) K)).toLinearEquiv • z) := by
      change (Matrix.GeneralLinearGroup.toLin
        ((r : GL (Fin 4) K) * (ga : GL (Fin 4) K))).toLinearEquiv • z = _
      rw [map_mul]
      change (Matrix.GeneralLinearGroup.toLin (r : GL (Fin 4) K) *
          Matrix.GeneralLinearGroup.toLin (ga : GL (Fin 4) K)) • z =
        Matrix.GeneralLinearGroup.toLin (r : GL (Fin 4) K) •
          (Matrix.GeneralLinearGroup.toLin (ga : GL (Fin 4) K) • z)
      exact mul_smul _ _ _
    refine ⟨r * ga, ?_, ?_⟩
    · rw [hcomp, hga, hr_inf]
    · rw [hcomp, ← hxy, hr_zero]

/-- The concrete Suzuki group is two-transitive on its ovoid. -/
private theorem suzukiOvoid_two_transitive
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∀ a b c d, a ∈ O → b ∈ O → c ∈ O → d ∈ O →
      a ≠ b → c ≠ d →
      ∃ g : SuzukiMatrixGroup m,
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • a = c ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • b = d := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  change ∀ a b c d, a ∈ O → b ∈ O → c ∈ O → d ∈ O →
    a ≠ b → c ≠ d →
    ∃ g : SuzukiMatrixGroup m,
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • a = c ∧
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • b = d
  intro a b c d ha hb hc hd hab hcd
  obtain ⟨g₁, hg₁a, hg₁b⟩ :=
    suzukiOvoid_exists_pair_to_standard
      m pi hpi_sq hpi_formula a b ha hb hab
  obtain ⟨g₂, hg₂c, hg₂d⟩ :=
    suzukiOvoid_exists_pair_to_standard
      m pi hpi_sq hpi_formula c d hc hd hcd
  have hinv (z t : ℙ K (Fin 4 → K))
      (hzt : (Matrix.GeneralLinearGroup.toLin
        (g₂ : GL (Fin 4) K)).toLinearEquiv • z = t) :
      (Matrix.GeneralLinearGroup.toLin
        ((g₂⁻¹ : SuzukiMatrixGroup m) : GL (Fin 4) K)).toLinearEquiv • t = z := by
    rw [← hzt]
    change (Matrix.GeneralLinearGroup.toLin
      ((g₂ : GL (Fin 4) K)⁻¹)).toLinearEquiv •
        ((Matrix.GeneralLinearGroup.toLin
          (g₂ : GL (Fin 4) K)).toLinearEquiv • z) = z
    rw [map_inv]
    change (Matrix.GeneralLinearGroup.toLin
      (g₂ : GL (Fin 4) K))⁻¹ •
        (Matrix.GeneralLinearGroup.toLin (g₂ : GL (Fin 4) K) • z) = z
    exact inv_smul_smul _ _
  have hback_c := hinv c pinf hg₂c
  have hback_d := hinv d (p 0 0) hg₂d
  have hcomp (z : ℙ K (Fin 4 → K)) :
      (Matrix.GeneralLinearGroup.toLin
        ((g₂⁻¹ * g₁ : SuzukiMatrixGroup m) : GL (Fin 4) K)).toLinearEquiv • z =
      (Matrix.GeneralLinearGroup.toLin
        ((g₂⁻¹ : SuzukiMatrixGroup m) : GL (Fin 4) K)).toLinearEquiv •
        ((Matrix.GeneralLinearGroup.toLin
          (g₁ : GL (Fin 4) K)).toLinearEquiv • z) := by
    change (Matrix.GeneralLinearGroup.toLin
      ((g₂ : GL (Fin 4) K)⁻¹ * (g₁ : GL (Fin 4) K))).toLinearEquiv • z = _
    rw [map_mul]
    change (Matrix.GeneralLinearGroup.toLin ((g₂ : GL (Fin 4) K)⁻¹) *
        Matrix.GeneralLinearGroup.toLin (g₁ : GL (Fin 4) K)) • z =
      Matrix.GeneralLinearGroup.toLin ((g₂ : GL (Fin 4) K)⁻¹) •
        (Matrix.GeneralLinearGroup.toLin (g₁ : GL (Fin 4) K) • z)
    exact mul_smul _ _ _
  refine ⟨g₂⁻¹ * g₁, ?_, ?_⟩
  · rw [hcomp, hg₁a, hback_c]
  · rw [hcomp, hg₁b, hback_d]

set_option maxHeartbeats 2000000 in
/-- The Suzuki root closure acts regularly on the finite part of the ovoid.

The finite-point coordinates make this explicit: a root element with
coordinates `(a,b)` sends `p(x,y)` to
`p (x+a) (y+b+pi a * (x+a))`. -/
public theorem suzukiRootClosure_regular_on_ovoid_complement
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b : ℙ (BinaryGaloisField (2 * m + 1)) (Fin 4 →
      BinaryGaloisField (2 * m + 1)))
    (ha : a ∈ ({(Projectivization.mk (BinaryGaloisField (2 * m + 1))
      ![1, 0, 0, 0] (by simp))} ∪ Set.range (fun z :
        BinaryGaloisField (2 * m + 1) × BinaryGaloisField (2 * m + 1) =>
          Projectivization.mk (BinaryGaloisField (2 * m + 1))
            ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
            (by simp)) ))
    (hb : b ∈ ({(Projectivization.mk (BinaryGaloisField (2 * m + 1))
      ![1, 0, 0, 0] (by simp))} ∪ Set.range (fun z :
        BinaryGaloisField (2 * m + 1) × BinaryGaloisField (2 * m + 1) =>
          Projectivization.mk (BinaryGaloisField (2 * m + 1))
            ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
            (by simp)) ))
    (ha_ne : a ≠ Projectivization.mk (BinaryGaloisField (2 * m + 1))
      ![1, 0, 0, 0] (by simp))
    (hb_ne : b ≠ Projectivization.mk (BinaryGaloisField (2 * m + 1))
      ![1, 0, 0, 0] (by simp)) :
    ∃! r : Subgroup.closure
        {A | ∃ x y : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m x y},
      (Matrix.GeneralLinearGroup.toLin
        (r : GL (Fin 4) (BinaryGaloisField (2 * m + 1)))).toLinearEquiv • a = b := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x y : K, A = SuzukiRootGL m x y}
  change ∃! r : F,
    (Matrix.GeneralLinearGroup.toLin (r : GL (Fin 4) K)).toLinearEquiv • a = b
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 :=
    binaryGaloisField_tits_formula_sq m pi hpi
  rcases ha with ha_inf | ⟨z, hz⟩
  · exfalso
    apply ha_ne
    simpa [pinf] using ha_inf
  rcases hb with hb_inf | ⟨w, hw⟩
  · exfalso
    apply hb_ne
    simpa [pinf] using hb_inf
  subst a
  subst b
  let aa : K := w.1 + z.1
  let bb : K := w.2 + z.2 + pi aa * w.1
  let r : F := ⟨SuzukiRootGL m aa bb,
    Subgroup.subset_closure ⟨aa, bb, rfl⟩⟩
  refine ⟨r, ?_, ?_⟩
  · change (Matrix.GeneralLinearGroup.toLin
      (SuzukiRootGL m aa bb)).toLinearEquiv • p z.1 z.2 = p w.1 w.2
    rw [suzukiRoot_smul_finite m pi hpi_sq hpi]
    have hxa : z.1 + aa = w.1 := by
      calc
        z.1 + aa = z.1 + (w.1 + z.1) := rfl
        _ = (z.1 + z.1) + w.1 := by ac_rfl
        _ = w.1 := by rw [CharTwo.add_self_eq_zero, zero_add]
    have hya : z.2 + bb + pi aa * (z.1 + aa) = w.2 := by
      rw [hxa]
      dsimp [bb]
      calc
        z.2 + (w.2 + z.2 + pi aa * w.1) + pi aa * w.1 =
            w.2 + (z.2 + z.2) +
              (pi aa * w.1 + pi aa * w.1) := by ac_rfl
        _ = w.2 := by
          rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
          simp
    have hya' : z.2 + bb + pi aa * w.1 = w.2 := by
      simpa [hxa] using hya
    rw [hxa, hya']
  · intro s hs
    rcases (suzukiRootGL_mem_closure_iff m pi hpi_sq hpi
      (s : GL (Fin 4) K)).mp s.property with ⟨c, d, hcd⟩
    have hs' : p (z.1 + c) (z.2 + d + pi c * (z.1 + c)) =
        p w.1 w.2 := by
      change (Matrix.GeneralLinearGroup.toLin
        (s : GL (Fin 4) K)).toLinearEquiv • p z.1 z.2 = p w.1 w.2 at hs
      rw [hcd, suzukiRoot_smul_finite m pi hpi_sq hpi] at hs
      exact hs
    have hcoord : z.1 + c = w.1 ∧
        z.2 + d + pi c * (z.1 + c) = w.2 := by
      dsimp [p] at hs'
      rw [Projectivization.mk_eq_mk_iff] at hs'
      rcases hs' with ⟨u, hu⟩
      have hu3 := congrFun hu (3 : Fin 4)
      have hu_one : (u : K) = 1 := by
        simpa [Units.smul_def] using hu3
      constructor
      · have hu2 := congrFun hu (2 : Fin 4)
        simpa [Units.smul_def, hu_one] using hu2.symm
      · have hu1 := congrFun hu (1 : Fin 4)
        simpa [Units.smul_def, hu_one] using hu1.symm
    have hc : c = aa := by
      have h := hcoord.1
      have hc0 : c = w.1 + z.1 := by
        calc
          c = (z.1 + c) + z.1 := by
            symm
            calc
              (z.1 + c) + z.1 = c + (z.1 + z.1) := by ac_rfl
              _ = c := by rw [CharTwo.add_self_eq_zero, add_zero]
          _ = w.1 + z.1 := by rw [h]
      exact hc0
    have hd : d = bb := by
      rw [hc] at hcoord
      have hxa2 := hcoord.1
      rw [hxa2] at hcoord
      have h := hcoord.2
      have hd0 : d = w.2 + z.2 + pi aa * w.1 := by
        calc
          d = (z.2 + d + pi aa * w.1) + z.2 + pi aa * w.1 := by
            symm
            calc
              (z.2 + d + pi aa * w.1) + z.2 + pi aa * w.1 =
                  d + (z.2 + z.2) +
                    (pi aa * w.1 + pi aa * w.1) := by ac_rfl
              _ = d := by
                rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
                simp
          _ = w.2 + z.2 + pi aa * w.1 := by rw [h]
      exact hd0
    apply Subtype.ext
    calc
      (s : GL (Fin 4) K) = SuzukiRootGL m c d := hcd
      _ = SuzukiRootGL m aa bb := by rw [hc, hd]
      _ = (r : GL (Fin 4) K) := rfl

/-- Every root generator has determinant one. -/
private theorem suzukiRootGL_det_one
    (m : ℕ) (a b : BinaryGaloisField (2 * m + 1)) :
    Matrix.det (SuzukiRootGL m a b :
      Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) = 1 := by
  have htri : (SuzukiRootMatrix m a b).BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [SuzukiRootMatrix] at hij ⊢
  change Matrix.det (SuzukiRootMatrix m a b) = 1
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [SuzukiRootMatrix, Fin.prod_univ_four]

/-- Every torus generator has determinant one. -/
private theorem suzukiTorusGL_det_one
    (m : ℕ) (u : (BinaryGaloisField (2 * m + 1))ˣ) :
    Matrix.det (SuzukiTorusGL m u :
      Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) = 1 := by
  have htri : (SuzukiTorusMatrix m u).BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [SuzukiTorusMatrix] at hij ⊢
  change Matrix.det (SuzukiTorusMatrix m u) = 1
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [SuzukiTorusMatrix, Fin.prod_univ_four, u.ne_zero]

/-- The Weyl generator has determinant one in characteristic two. -/
private theorem suzukiWeylGL_det_one (m : ℕ) :
    Matrix.det (SuzukiWeylGL m :
      Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) = 1 := by
  change Matrix.det (SuzukiWeylMatrix m) = 1
  have h32 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := by decide
  have h31 : Fin.succAbove (3 : Fin 4) (1 : Fin 3) = 1 := by decide
  have h321 :
      Fin.succAbove (3 : Fin 4) (Fin.succAbove (2 : Fin 3) (1 : Fin 2)) = 1 := by
    decide
  simp [SuzukiWeylMatrix, Matrix.det_succ_row_zero,
    Fin.sum_univ_four, Fin.sum_univ_three, Fin.sum_univ_two,
    h32, h31, h321, CharTwo.neg_eq]

/-- Every element of the concrete Suzuki matrix group has determinant one. -/
private theorem suzukiMatrixGroup_det_one
    (m : ℕ) (g : SuzukiMatrixGroup m) :
    Matrix.det ((g : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :
      Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) = 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  have hgenerators : SuzukiMatrixGeneratorSet m ⊆
      (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker := by
    intro A hA
    change Matrix.GeneralLinearGroup.det A = 1
    apply Units.ext
    change Matrix.det (A : Matrix (Fin 4) (Fin 4) K) = 1
    rcases hA with ⟨a, b, rfl⟩ | ⟨u, rfl⟩ | rfl
    · exact suzukiRootGL_det_one m a b
    · exact suzukiTorusGL_det_one m u
    · exact suzukiWeylGL_det_one m
  have hclosure : SuzukiMatrixSubgroup m ≤
      (Matrix.GeneralLinearGroup.det : GL (Fin 4) K →* Kˣ).ker := by
    rw [SuzukiMatrixSubgroup, Subgroup.closure_le]
    exact hgenerators
  have hg := hclosure g.property
  change Matrix.GeneralLinearGroup.det (g : GL (Fin 4) K) = 1 at hg
  exact congrArg Units.val hg

/-- An element of the concrete Suzuki group fixing every ovoid point is the
identity. Five explicit ovoid lines force its matrix to be scalar, and the
determinant-one condition removes that scalar. -/
private theorem suzukiMatrixGroup_faithful_on_ovoid
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∀ g : SuzukiMatrixGroup m,
      (∀ z, z ∈ O →
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • z = z) → g = 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  change ∀ g : SuzukiMatrixGroup m,
    (∀ z, z ∈ O →
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • z = z) → g = 1
  intro g hfix
  let A : GL (Fin 4) K := g
  let e0 : Fin 4 → K := ![1, 0, 0, 0]
  let e3 : Fin 4 → K := ![0, 0, 0, 1]
  let v01 : Fin 4 → K := ![1, 1, 0, 1]
  let v10 : Fin 4 → K := ![1, 0, 1, 1]
  let v11 : Fin 4 → K := ![1, 1, 1, 1]
  have he0 : e0 ≠ 0 := by simp [e0]
  have he3 : e3 ≠ 0 := by simp [e3]
  have hv01 : v01 ≠ 0 := by simp [v01]
  have hv10 : v10 ≠ 0 := by simp [v10]
  have hv11 : v11 ≠ 0 := by simp [v11]
  have he0O : Projectivization.mk K e0 he0 ∈ O := by
    exact Or.inl (by simp [pinf, e0])
  have he3O : Projectivization.mk K e3 he3 ∈ O := by
    exact Or.inr ⟨(0, 0), by simp [p, e3]⟩
  have hv01O : Projectivization.mk K v01 hv01 ∈ O := by
    exact Or.inr ⟨(0, 1), by simp [p, v01]⟩
  have hv10O : Projectivization.mk K v10 hv10 ∈ O := by
    exact Or.inr ⟨(1, 0), by simp [p, v10]⟩
  have hv11O : Projectivization.mk K v11 hv11 ∈ O := by
    exact Or.inr ⟨(1, 1), by
      simp [p, v11, CharTwo.add_self_eq_zero]⟩
  have fixedLine (v : Fin 4 → K) (hv : v ≠ 0)
      (hvO : Projectivization.mk K v hv ∈ O) :
      ∃ c : K, c • v =
        (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • v := by
    have h := hfix (Projectivization.mk K v hv) hvO
    change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv •
      Projectivization.mk K v hv = Projectivization.mk K v hv at h
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at h
    exact h
  obtain ⟨c0, hc0⟩ := fixedLine e0 he0 he0O
  obtain ⟨c3, hc3⟩ := fixedLine e3 he3 he3O
  obtain ⟨d, hd⟩ := fixedLine v01 hv01 hv01O
  obtain ⟨e, he⟩ := fixedLine v10 hv10 hv10O
  obtain ⟨f, hf⟩ := fixedLine v11 hv11 hv11O
  have hc0_0 := congrFun hc0 (0 : Fin 4)
  have hc0_1 := congrFun hc0 (1 : Fin 4)
  have hc0_2 := congrFun hc0 (2 : Fin 4)
  have hc0_3 := congrFun hc0 (3 : Fin 4)
  have hc3_0 := congrFun hc3 (0 : Fin 4)
  have hc3_1 := congrFun hc3 (1 : Fin 4)
  have hc3_2 := congrFun hc3 (2 : Fin 4)
  have hc3_3 := congrFun hc3 (3 : Fin 4)
  have hd_0 := congrFun hd (0 : Fin 4)
  have hd_1 := congrFun hd (1 : Fin 4)
  have hd_2 := congrFun hd (2 : Fin 4)
  have hd_3 := congrFun hd (3 : Fin 4)
  have he_0 := congrFun he (0 : Fin 4)
  have he_1 := congrFun he (1 : Fin 4)
  have he_2 := congrFun he (2 : Fin 4)
  have he_3 := congrFun he (3 : Fin 4)
  have hf_0 := congrFun hf (0 : Fin 4)
  have hf_1 := congrFun hf (1 : Fin 4)
  have hf_2 := congrFun hf (2 : Fin 4)
  have hf_3 := congrFun hf (3 : Fin 4)
  simp [e0, e3, v01, v10, v11,
    Matrix.mulVec,
    dotProduct, Fin.sum_univ_four] at hc0_0 hc0_1 hc0_2 hc0_3 hc3_0 hc3_1 hc3_2 hc3_3 hd_0 hd_1 hd_2 hd_3 he_0 he_1 he_2 he_3 hf_0 hf_1 hf_2 hf_3
  have hA10 : A 1 0 = 0 := hc0_1.symm
  have hA20 : A 2 0 = 0 := hc0_2.symm
  have hA30 : A 3 0 = 0 := hc0_3.symm
  have hA03 : A 0 3 = 0 := hc3_0.symm
  have hA13 : A 1 3 = 0 := hc3_1.symm
  have hA23 : A 2 3 = 0 := hc3_2.symm
  have hA12 : A 1 2 = 0 := by
    linear_combination -he_1 - hA10 - hA13
  have hA21 : A 2 1 = 0 := by
    linear_combination -hd_2 - hA20 - hA23
  have hA11 : A 1 1 = d := by
    linear_combination -hd_1 - hA10 - hA13
  have hA22 : A 2 2 = e := by
    linear_combination -he_2 - hA20 - hA23
  have hdf : d = f := by
    have h := hf_1
    rw [hA10, hA11, hA12, hA13] at h
    simp at h
    exact h.symm
  have hef : e = f := by
    have h := hf_2
    rw [hA20, hA21, hA22, hA23] at h
    simp at h
    exact h.symm
  have hc0f : c0 = f := by
    linear_combination hc0_0 - hd_0 - he_0 + hf_0 - hA03 + hdf + hef
  have hc3f : c3 = f := by
    linear_combination hc3_3 - hd_3 - he_3 + hf_3 - hA30 + hdf + hef
  have hA00 : A 0 0 = f := by
    linear_combination -hc0_0 + hc0f
  have hA33 : A 3 3 = f := by
    linear_combination -hc3_3 + hc3f
  have hA01 : A 0 1 = 0 := by
    linear_combination -hd_0 + hdf - hA00 - hA03
  have hA02 : A 0 2 = 0 := by
    linear_combination -he_0 + hef - hA00 - hA03
  have hA31 : A 3 1 = 0 := by
    linear_combination -hd_3 + hdf - hA30 - hA33
  have hA32 : A 3 2 = 0 := by
    linear_combination -he_3 + hef - hA30 - hA33
  have hscalar : (A : Matrix (Fin 4) (Fin 4) K) = Matrix.scalar (Fin 4) f := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, hA00, hA01, hA02, hA03,
        hA10, hA11, hA12, hA13, hA20, hA21, hA22, hA23,
        hA30, hA31, hA32, hA33, hdf, hef]
  have hdet := suzukiMatrixGroup_det_one m g
  change Matrix.det (A : Matrix (Fin 4) (Fin 4) K) = 1 at hdet
  rw [hscalar] at hdet
  have hf4 : f ^ 4 = 1 := by
    simpa [Matrix.det_diagonal, Fin.prod_univ_four, Matrix.scalar_apply] using hdet
  have hf2 : f ^ 2 = (1 : K) ^ 2 := by
    apply CharTwo.sq_injective
    simpa [← pow_mul] using hf4
  have hfone : f = 1 := CharTwo.sq_injective hf2
  apply Subtype.ext
  apply Units.ext
  change (A : Matrix (Fin 4) (Fin 4) K) = 1
  rw [hscalar, hfone]
  ext i j
  simp [Matrix.scalar_apply]

/-- The polynomial core of the full linear stabilizer calculation for the
Suzuki ovoid. -/
private theorem suzukiOvoid_linear_coordinate_coefficients
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (alpha t w u v c1 c2 : BinaryGaloisField (2 * m + 1))
    (hcurve : ∀ x y,
      alpha * (x * y + pi x * x ^ 2 + pi y) + c1 * y + c2 * x =
        (u * x + t * y) * (v * x + w * y) +
          pi (u * x + t * y) * (u * x + t * y) ^ 2 +
          pi (v * x + w * y)) :
    t = 0 ∧ c1 = 0 ∧ alpha = pi w ∧
      (u ≠ 0 → v = 0 ∧ c2 = 0 ∧ alpha = pi u * u ^ 2) := by
  let K := BinaryGaloisField (2 * m + 1)
  let tExp := 2 ^ (m + 1)
  let q := 2 ^ (2 * m + 1)
  let fintype : Fintype K := Fintype.ofFinite K
  have hK_card : @Fintype.card K fintype = q := by
    rw [@Fintype.card_eq_nat_card K fintype]
    simpa [K, q, BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  have htExp_four : 4 ≤ tExp := by
    dsimp only [tExp]
    have hpow : 2 ^ 2 ≤ 2 ^ (m + 1) := by
      refine Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at hpow ⊢
    exact hpow
  have htwo_pow_m : 2 ≤ 2 ^ m := by
    have hpow : 2 ^ 1 ≤ 2 ^ m := by
      refine Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at hpow ⊢
    exact hpow
  have htExp_lt_q : tExp + 2 < q := by
    calc
      tExp + 2 < tExp + tExp := Nat.add_lt_add_left (by omega) tExp
      _ = tExp * 2 := by omega
      _ ≤ tExp * 2 ^ m := Nat.mul_le_mul_left tExp htwo_pow_m
      _ = q := by
        dsimp only [tExp, q]
        rw [← pow_add]
        congr 1; omega
  let pyLeft : Polynomial K :=
    Polynomial.C alpha * Polynomial.X ^ tExp +
      Polynomial.C c1 * Polynomial.X ^ 1
  let pyRight : Polynomial K :=
    Polynomial.C (t * w) * Polynomial.X ^ 2 +
      Polynomial.C (pi t * t ^ 2) * Polynomial.X ^ (tExp + 2) +
      Polynomial.C (pi w) * Polynomial.X ^ tExp
  have hpy_eval : ∀ y : K,
      Polynomial.eval y pyLeft = Polynomial.eval y pyRight := by
    intro y
    have h := hcurve 0 y
    dsimp only [pyLeft, pyRight]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, zero_mul, zero_add, map_mul,
      hpi_formula, pow_add, pow_one] at h ⊢
    dsimp only [tExp]
    ring_nf at h ⊢
    convert h using 1 <;> ring
  have hpyLeft_deg : pyLeft.natDegree ≤ tExp + 2 := by
    dsimp only [pyLeft]
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact (Polynomial.natDegree_C_mul_X_pow_le alpha tExp).trans (by omega)
    · simpa only [pow_one] using
        (Polynomial.natDegree_C_mul_X_pow_le c1 1).trans (by omega)
  have hpyRight_deg : pyRight.natDegree ≤ tExp + 2 := by
    dsimp only [pyRight]
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · exact (Polynomial.natDegree_C_mul_X_pow_le (t * w) 2).trans (by omega)
      · exact Polynomial.natDegree_C_mul_X_pow_le
          (pi t * t ^ 2) (tExp + 2)
    · exact (Polynomial.natDegree_C_mul_X_pow_le (pi w) tExp).trans (by omega)
  have hpy : pyLeft = pyRight := by
    apply @Polynomial.eq_of_natDegree_lt_card_of_eval_eq K
      (inferInstance : CommRing K) (inferInstance : IsDomain K)
      pyLeft pyRight K fintype (fun x : K => x) Function.injective_id hpy_eval
    rw [hK_card]
    exact (max_le hpyLeft_deg hpyRight_deg).trans_lt htExp_lt_q
  have ht_coeff : pi t * t ^ 2 = 0 := by
    have hcoeff := congrArg
      (fun P : Polynomial K => P.coeff (tExp + 2)) hpy
    simpa only [pyLeft, pyRight, Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow,
      show tExp + 2 ≠ tExp by omega,
      show tExp + 2 ≠ 1 by omega,
      show tExp + 2 ≠ 2 by omega, if_false, if_true, zero_add, add_zero] using hcoeff.symm
  have ht : t = 0 := by
    by_contra ht0
    exact (mul_ne_zero ((map_ne_zero pi).2 ht0)
      (pow_ne_zero _ ht0)) ht_coeff
  have hc1 : c1 = 0 := by
    have hcoeff := congrArg (fun P : Polynomial K => P.coeff 1) hpy
    simpa only [pyLeft, pyRight, Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow,
      show (1 : ℕ) ≠ tExp by omega,
      show (1 : ℕ) ≠ 2 by omega,
      show (1 : ℕ) ≠ tExp + 2 by omega, if_false, if_true, zero_add, add_zero] using hcoeff
  have halpha_w : alpha = pi w := by
    have hcoeff := congrArg (fun P : Polynomial K => P.coeff tExp) hpy
    simpa only [pyLeft, pyRight, Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow,
      show tExp ≠ 1 by omega,
      show tExp ≠ 2 by omega,
      show tExp ≠ tExp + 2 by omega, if_false, if_true, zero_add, add_zero] using hcoeff
  let pxLeft : Polynomial K :=
    Polynomial.C alpha * Polynomial.X ^ (tExp + 2) +
      Polynomial.C c2 * Polynomial.X ^ 1
  let pxRight : Polynomial K :=
    Polynomial.C (u * v) * Polynomial.X ^ 2 +
      Polynomial.C (pi u * u ^ 2) * Polynomial.X ^ (tExp + 2) +
      Polynomial.C (pi v) * Polynomial.X ^ tExp
  have hpx_eval : ∀ x : K,
      Polynomial.eval x pxLeft = Polynomial.eval x pxRight := by
    intro x
    have h := hcurve x 0
    dsimp only [pxLeft, pxRight]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, mul_zero, add_zero, map_mul,
      hpi_formula, mul_pow, pow_add, pow_one] at h ⊢
    dsimp only [tExp]
    have hexp : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [pow_succ]
    rw [hexp] at ⊢
    convert h using 1 <;> ring
  have hpxLeft_deg : pxLeft.natDegree ≤ tExp + 2 := by
    dsimp only [pxLeft]
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact Polynomial.natDegree_C_mul_X_pow_le alpha (tExp + 2)
    · simpa only [pow_one] using
        (Polynomial.natDegree_C_mul_X_pow_le c2 1).trans (by omega)
  have hpxRight_deg : pxRight.natDegree ≤ tExp + 2 := by
    dsimp only [pxRight]
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · exact (Polynomial.natDegree_C_mul_X_pow_le (u * v) 2).trans (by omega)
      · exact Polynomial.natDegree_C_mul_X_pow_le
          (pi u * u ^ 2) (tExp + 2)
    · exact (Polynomial.natDegree_C_mul_X_pow_le (pi v) tExp).trans (by omega)
  have hpx : pxLeft = pxRight := by
    apply @Polynomial.eq_of_natDegree_lt_card_of_eval_eq K
      (inferInstance : CommRing K) (inferInstance : IsDomain K)
      pxLeft pxRight K fintype (fun x : K => x) Function.injective_id hpx_eval
    rw [hK_card]
    exact (max_le hpxLeft_deg hpxRight_deg).trans_lt htExp_lt_q
  refine ⟨ht, hc1, halpha_w, ?_⟩
  intro hu
  have huv : u * v = 0 := by
    have hcoeff := congrArg (fun P : Polynomial K => P.coeff 2) hpx
    simpa only [pxLeft, pxRight, Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow,
      show (2 : ℕ) ≠ tExp + 2 by omega,
      show (2 : ℕ) ≠ 1 by omega,
      show (2 : ℕ) ≠ tExp by omega, if_false, if_true, zero_add, add_zero] using hcoeff.symm
  have hv : v = 0 := (mul_eq_zero.mp huv).resolve_left hu
  have hc2 : c2 = 0 := by
    have hcoeff := congrArg (fun P : Polynomial K => P.coeff 1) hpx
    simpa only [pxLeft, pxRight, Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow,
      show (1 : ℕ) ≠ tExp + 2 by omega,
      show (1 : ℕ) ≠ 2 by omega,
      show (1 : ℕ) ≠ tExp by omega, if_false, if_true, zero_add, add_zero] using hcoeff
  have halpha_u : alpha = pi u * u ^ 2 := by
    have hcoeff := congrArg
      (fun P : Polynomial K => P.coeff (tExp + 2)) hpx
    simpa only [pxLeft, pxRight, Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow,
      show tExp + 2 ≠ 1 by omega,
      show tExp + 2 ≠ 2 by omega,
      show tExp + 2 ≠ tExp by omega, if_false, if_true, zero_add, add_zero] using hcoeff
  exact ⟨hv, hc2, halpha_u⟩

/-- A linear ovoid stabilizer fixing the two standard points is projectively a
Suzuki torus element. -/
private theorem suzukiOvoid_stabilizer_fix_standard_is_torus
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (A : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    (∀ z, z ∈ O ↔
      (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O) →
    (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • pinf = pinf →
    (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • p 0 0 = p 0 0 →
    ∃ u : Kˣ, ∀ z : ℙ K (Fin 4 → K),
      (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z =
        (Matrix.GeneralLinearGroup.toLin
          (SuzukiTorusGL m u)).toLinearEquiv • z := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let vec : K → K → Fin 4 → K := fun x y =>
    ![x * y + pi x * x ^ 2 + pi y, y, x, 1]
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K (vec x y) (by simp [vec])
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let e0 : Fin 4 → K := ![1, 0, 0, 0]
  let e3 : Fin 4 → K := ![0, 0, 0, 1]
  have he0 : e0 ≠ 0 := by simp [e0]
  have he3 : e3 ≠ 0 := by simp [e3]
  change (∀ z, z ∈ O ↔
      (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O) →
    (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • pinf = pinf →
    (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • p 0 0 = p 0 0 →
    ∃ u : Kˣ, ∀ z : ℙ K (Fin 4 → K),
      (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z =
        (Matrix.GeneralLinearGroup.toLin
          (SuzukiTorusGL m u)).toLinearEquiv • z
  intro hpres hinf hzero
  have fixedLine (v : Fin 4 → K) (hv : v ≠ 0)
      (hfix : (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv •
        Projectivization.mk K v hv = Projectivization.mk K v hv) :
      ∃ c : K, c • v =
        (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • v := by
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at hfix
    exact hfix
  have hinf' : (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv •
      Projectivization.mk K e0 he0 = Projectivization.mk K e0 he0 := by
    simpa [pinf, e0] using hinf
  have hzero' : (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv •
      Projectivization.mk K e3 he3 = Projectivization.mk K e3 he3 := by
    simpa [p, vec, e3] using hzero
  obtain ⟨c0, hc0⟩ := fixedLine e0 he0 hinf'
  obtain ⟨c3, hc3⟩ := fixedLine e3 he3 hzero'
  have hc0_0 := congrFun hc0 (0 : Fin 4)
  have hc0_1 := congrFun hc0 (1 : Fin 4)
  have hc0_2 := congrFun hc0 (2 : Fin 4)
  have hc0_3 := congrFun hc0 (3 : Fin 4)
  have hc3_0 := congrFun hc3 (0 : Fin 4)
  have hc3_1 := congrFun hc3 (1 : Fin 4)
  have hc3_2 := congrFun hc3 (2 : Fin 4)
  have hc3_3 := congrFun hc3 (3 : Fin 4)
  simp [e0, e3, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at hc0_0 hc0_1 hc0_2 hc0_3 hc3_0 hc3_1 hc3_2 hc3_3
  have hA00 : A 0 0 = c0 := hc0_0.symm
  have hA10 : A 1 0 = 0 := hc0_1.symm
  have hA20 : A 2 0 = 0 := hc0_2.symm
  have hA30 : A 3 0 = 0 := hc0_3.symm
  have hA03 : A 0 3 = 0 := hc3_0.symm
  have hA13 : A 1 3 = 0 := hc3_1.symm
  have hA23 : A 2 3 = 0 := hc3_2.symm
  have hA33 : A 3 3 = c3 := hc3_3.symm
  have hc3_ne : c3 ≠ 0 := by
    intro hc3z
    have hmapzero :
        (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv e3 = 0 := by
      simpa [hc3z] using hc3.symm
    exact he3 ((Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.injective
      (hmapzero.trans (map_zero _).symm))
  have hfinite (x y : K) :
      ∃ X Y c : K, c ≠ 0 ∧ c • vec X Y =
        (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • vec x y := by
    have hpO : p x y ∈ O := Or.inr ⟨(x, y), rfl⟩
    have himO := (hpres (p x y)).mp hpO
    have hnotinf :
        (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • p x y ≠ pinf := by
      intro hbad
      have hsame :
          (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • p x y =
            (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • pinf :=
        hbad.trans hinf.symm
      have hpinf : p x y = pinf := by
        change Matrix.GeneralLinearGroup.toLin A • p x y =
          Matrix.GeneralLinearGroup.toLin A • pinf at hsame
        exact smul_left_cancel _ hsame
      exact suzukiOvoidInfinity_not_mem_range m pi
        ⟨(x, y), hpinf⟩
    rcases himO with himinf | ⟨XY, hXY⟩
    · exact False.elim (hnotinf (by simpa using himinf))
    · rcases XY with ⟨X, Y⟩
      have hprojective :
          (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • p x y =
            p X Y := hXY.symm
      change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv •
          Projectivization.mk K (vec x y) (by simp [vec]) =
        Projectivization.mk K (vec X Y) (by simp [vec]) at hprojective
      rw [Projectivization.smul_mk,
        Projectivization.mk_eq_mk_iff'] at hprojective
      rcases hprojective with ⟨c, hc⟩
      have hc_ne : c ≠ 0 := by
        intro hcz
        have hmapzero :
            (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv (vec x y) = 0 := by
          simpa [hcz] using hc.symm
        have hvzero : vec x y = 0 :=
          (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.injective
            (hmapzero.trans (map_zero _).symm)
        have hv3 := congrFun hvzero (3 : Fin 4)
        simp [vec] at hv3
      exact ⟨X, Y, c, hc_ne, hc⟩
  have hA31 : A 3 1 = 0 := by
    by_contra h31
    let y : K := c3 * (A 3 1)⁻¹
    rcases hfinite 0 y with ⟨X, Y, c, hc_ne, hc⟩
    have hrow := congrFun hc (3 : Fin 4)
    have hcancel : A 3 1 * y + c3 = 0 := by
      dsimp only [y]
      calc
        A 3 1 * (c3 * (A 3 1)⁻¹) + c3 =
            c3 * (A 3 1 * (A 3 1)⁻¹) + c3 := by ring
        _ = 0 := by
          rw [mul_inv_cancel₀ h31, mul_one, CharTwo.add_self_eq_zero]
    simp [vec, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      hA30, hA33, hcancel] at hrow
    exact hc_ne hrow
  have hA32 : A 3 2 = 0 := by
    by_contra h32
    let x : K := c3 * (A 3 2)⁻¹
    rcases hfinite x 0 with ⟨X, Y, c, hc_ne, hc⟩
    have hrow := congrFun hc (3 : Fin 4)
    have hcancel : A 3 2 * x + c3 = 0 := by
      dsimp only [x]
      calc
        A 3 2 * (c3 * (A 3 2)⁻¹) + c3 =
            c3 * (A 3 2 * (A 3 2)⁻¹) + c3 := by ring
        _ = 0 := by
          rw [mul_inv_cancel₀ h32, mul_one, CharTwo.add_self_eq_zero]
    simp [vec, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      hA30, hA31, hA33, hcancel] at hrow
    exact hc_ne hrow
  let alpha : K := c3⁻¹ * c0
  let t : K := c3⁻¹ * A 2 1
  let w : K := c3⁻¹ * A 1 1
  let u : K := c3⁻¹ * A 2 2
  let v : K := c3⁻¹ * A 1 2
  let c1 : K := c3⁻¹ * A 0 1
  let c2 : K := c3⁻¹ * A 0 2
  have hcurve : ∀ x y : K,
      alpha * (x * y + pi x * x ^ 2 + pi y) + c1 * y + c2 * x =
        (u * x + t * y) * (v * x + w * y) +
          pi (u * x + t * y) * (u * x + t * y) ^ 2 +
          pi (v * x + w * y) := by
    intro x y
    rcases hfinite x y with ⟨X, Y, c, _hc_ne, hc⟩
    have hrow0 := congrFun hc (0 : Fin 4)
    have hrow1 := congrFun hc (1 : Fin 4)
    have hrow2 := congrFun hc (2 : Fin 4)
    have hrow3 := congrFun hc (3 : Fin 4)
    simp [vec, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      hA00, hA10, hA20, hA30, hA03, hA13, hA23, hA31, hA32,
      hA33] at hrow0 hrow1 hrow2 hrow3
    have hc_eq : c = c3 := hrow3
    have hX : X = u * x + t * y := by
      dsimp only [u, t]
      rw [hc_eq] at hrow2
      calc
        X = c3⁻¹ * (c3 * X) := by
          rw [← mul_assoc, inv_mul_cancel₀ hc3_ne, one_mul]
        _ = c3⁻¹ * (A 2 1 * y + A 2 2 * x) := by rw [hrow2]
        _ = (c3⁻¹ * A 2 2) * x + (c3⁻¹ * A 2 1) * y := by ring
    have hY : Y = v * x + w * y := by
      dsimp only [v, w]
      rw [hc_eq] at hrow1
      calc
        Y = c3⁻¹ * (c3 * Y) := by
          rw [← mul_assoc, inv_mul_cancel₀ hc3_ne, one_mul]
        _ = c3⁻¹ * (A 1 1 * y + A 1 2 * x) := by rw [hrow1]
        _ = (c3⁻¹ * A 1 2) * x + (c3⁻¹ * A 1 1) * y := by ring
    dsimp only [alpha, c1, c2]
    rw [hc_eq, hX, hY] at hrow0
    apply mul_left_cancel₀ hc3_ne
    simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ hc3_ne, one_mul]
    convert hrow0.symm using 1 <;> ring
  rcases suzukiOvoid_linear_coordinate_coefficients
    m hm pi hpi_formula alpha t w u v c1 c2 hcurve with
    ⟨ht, hc1, halpha_w, hremaining⟩
  have hA21 : A 2 1 = 0 := by
    exact (mul_eq_zero.mp ht).resolve_left (inv_ne_zero hc3_ne)
  have hA22_ne : A 2 2 ≠ 0 := by
    intro hA22
    let e2 : Fin 4 → K := ![0, 0, 1, 0]
    obtain ⟨z, hz⟩ :=
      (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.surjective e2
    have hz2 := congrFun hz (2 : Fin 4)
    simp [e2, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      hA20, hA21, hA22, hA23] at hz2
  have hu : u ≠ 0 := mul_ne_zero (inv_ne_zero hc3_ne) hA22_ne
  rcases hremaining hu with ⟨hv, hc2, halpha_u⟩
  have hA12 : A 1 2 = 0 :=
    (mul_eq_zero.mp hv).resolve_left (inv_ne_zero hc3_ne)
  have hA01 : A 0 1 = 0 :=
    (mul_eq_zero.mp hc1).resolve_left (inv_ne_zero hc3_ne)
  have hA02 : A 0 2 = 0 :=
    (mul_eq_zero.mp hc2).resolve_left (inv_ne_zero hc3_ne)
  have hw : w = u * pi u := by
    apply pi.injective
    calc
      pi w = alpha := halpha_w.symm
      _ = pi u * u ^ 2 := halpha_u
      _ = pi (u * pi u) := by simp [map_mul, hpi_sq, mul_comm]
  have hc0_scaled : c0 = c3 * (pi u * u ^ 2) := by
    calc
      c0 = (c3 * c3⁻¹) * c0 := by rw [mul_inv_cancel₀ hc3_ne, one_mul]
      _ = c3 * (c3⁻¹ * c0) := by ring
      _ = c3 * alpha := rfl
      _ = c3 * (pi u * u ^ 2) := by rw [halpha_u]
  have hA11_scaled : A 1 1 = c3 * (u * pi u) := by
    calc
      A 1 1 = (c3 * c3⁻¹) * A 1 1 := by
        rw [mul_inv_cancel₀ hc3_ne, one_mul]
      _ = c3 * (c3⁻¹ * A 1 1) := by ring
      _ = c3 * w := rfl
      _ = c3 * (u * pi u) := by rw [hw]
  have hA22_scaled : A 2 2 = c3 * u := by
    calc
      A 2 2 = (c3 * c3⁻¹) * A 2 2 := by
        rw [mul_inv_cancel₀ hc3_ne, one_mul]
      _ = c3 * (c3⁻¹ * A 2 2) := by ring
      _ = c3 * u := rfl
  let uUnit : Kˣ := Units.mk0 u hu
  let outer : K := u ^ (1 + 2 ^ m)
  let scale : K := c3 * outer
  have houter_ne : outer ≠ 0 := pow_ne_zero _ hu
  have hscale_ne : scale ≠ 0 := mul_ne_zero hc3_ne houter_ne
  have hratio : outer * (u ^ (2 ^ m))⁻¹ = u := by
    dsimp only [outer]
    rw [pow_add, pow_one, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hu), mul_one]
  have hmiddle : u ^ (2 ^ m) * outer = u * pi u := by
    dsimp only [outer]
    calc
      u ^ (2 ^ m) * u ^ (1 + 2 ^ m) =
          u ^ (2 ^ m + (1 + 2 ^ m)) := (pow_add _ _ _).symm
      _ = u ^ (1 + 2 ^ (m + 1)) := by
        congr 1
        rw [pow_succ]
        omega
      _ = u * u ^ (2 ^ (m + 1)) := by rw [pow_add, pow_one]
      _ = u * pi u := by rw [hpi_formula]
  have houter_sq : outer * outer = pi u * u ^ 2 := by
    dsimp only [outer]
    calc
      u ^ (1 + 2 ^ m) * u ^ (1 + 2 ^ m) =
          u ^ (2 + 2 ^ (m + 1)) := by
        rw [← pow_two, ← pow_mul]
        congr 1
        rw [pow_succ]
        omega
      _ = pi u * u ^ 2 := by rw [pow_add, hpi_formula]; ring
  have hA00_scale : A 0 0 = scale * outer := by
    dsimp only [scale]
    rw [hA00, hc0_scaled, mul_assoc, houter_sq]
  have hmiddle_comm : outer * u ^ (2 ^ m) = u * pi u := by
    rw [mul_comm, hmiddle]
  have hA11_scale : A 1 1 = scale * u ^ (2 ^ m) := by
    calc
      A 1 1 = c3 * (u * pi u) := hA11_scaled
      _ = c3 * (outer * u ^ (2 ^ m)) := by rw [hmiddle_comm]
      _ = (c3 * outer) * u ^ (2 ^ m) := (mul_assoc _ _ _).symm
      _ = scale * u ^ (2 ^ m) := rfl
  have hA22_scale : A 2 2 = scale * (u ^ (2 ^ m))⁻¹ := by
    calc
      A 2 2 = c3 * u := hA22_scaled
      _ = c3 * (outer * (u ^ (2 ^ m))⁻¹) := by rw [hratio]
      _ = (c3 * outer) * (u ^ (2 ^ m))⁻¹ := (mul_assoc _ _ _).symm
      _ = scale * (u ^ (2 ^ m))⁻¹ := rfl
  have hA33_scale : A 3 3 = scale * outer⁻¹ := by
    dsimp only [scale]
    rw [hA33, mul_assoc, mul_inv_cancel₀ houter_ne, mul_one]
  have hmatrix : (A : Matrix (Fin 4) (Fin 4) K) =
      scale • SuzukiTorusMatrix m uUnit := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SuzukiTorusMatrix, uUnit, outer, hA00_scale, hA01, hA02, hA03,
        hA10, hA11_scale, hA12, hA13, hA20, hA21, hA22_scale,
        hA23, hA30, hA31, hA32, hA33_scale]
  refine ⟨uUnit, ?_⟩
  intro z
  induction z using Projectivization.ind with
  | _ z hz =>
      rw [Projectivization.smul_mk, Projectivization.smul_mk,
        Projectivization.mk_eq_mk_iff']
      refine ⟨scale, ?_⟩
      change scale • (SuzukiTorusMatrix m uUnit).mulVec z =
        (A : Matrix (Fin 4) (Fin 4) K).mulVec z
      rw [hmatrix]
      funext i
      simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mulVec,
        dotProduct, Finset.mul_sum, mul_assoc]

/-- The standard Suzuki Weyl element is an involution. -/
public theorem suzukiWeylGL_mul_self (m : ℕ) :
    SuzukiWeylGL m * SuzukiWeylGL m = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiWeylGL, SuzukiWeylMatrix, Matrix.mul_apply,
      Fin.sum_univ_four]

/-- The Weyl element inverts the split torus. -/
public theorem suzukiWeylGL_conj_torus
    (m : ℕ) (u : (BinaryGaloisField (2 * m + 1))ˣ) :
    SuzukiWeylGL m * SuzukiTorusGL m u * SuzukiWeylGL m =
      SuzukiTorusGL m u⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiWeylGL, SuzukiWeylMatrix, SuzukiTorusGL,
      SuzukiTorusMatrix, Matrix.mul_apply, Fin.sum_univ_four, inv_pow]

/-- The torus parameter in the rank-one Suzuki Gauss decomposition has the
required two diagonal powers. -/
private theorem suzukiBruhat_torus_powers
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (n : BinaryGaloisField (2 * m + 1)) (hn : n ≠ 0) :
    let K := BinaryGaloisField (2 * m + 1)
    let uval : K := pi n * n⁻¹ ^ 2
    let u : Kˣ := Units.mk0 uval (mul_ne_zero ((map_ne_zero pi).2 hn)
      (pow_ne_zero _ (inv_ne_zero hn)))
    ((u : K) ^ (2 ^ m) = n * (pi n)⁻¹) ∧
      ((u : K) ^ (1 + 2 ^ m) = n⁻¹) := by
  let K := BinaryGaloisField (2 * m + 1)
  let uval : K := pi n * n⁻¹ ^ 2
  have hpin : pi n ≠ 0 := (map_ne_zero pi).2 hn
  have huval : uval ≠ 0 :=
    mul_ne_zero hpin (pow_ne_zero _ (inv_ne_zero hn))
  let u : Kˣ := Units.mk0 uval huval
  change (uval ^ (2 ^ m) = n * (pi n)⁻¹) ∧
    (uval ^ (1 + 2 ^ m) = n⁻¹)
  have hpi_uval : pi uval = (n * (pi n)⁻¹) ^ 2 := by
    dsimp only [uval]
    simp only [map_mul, map_pow, map_inv₀, hpi_sq]
    ring
  have hq : uval ^ (2 ^ m) = n * (pi n)⁻¹ := by
    apply CharTwo.sq_injective
    calc
      (uval ^ (2 ^ m)) ^ 2 = uval ^ (2 ^ (m + 1)) := by
        rw [show 2 ^ (m + 1) = 2 ^ m * 2 by rw [pow_succ], pow_mul]
      _ = pi uval := (hpi_formula uval).symm
      _ = (n * (pi n)⁻¹) ^ 2 := hpi_uval
  refine ⟨hq, ?_⟩
  rw [pow_add, pow_one, hq]
  dsimp only [uval]
  calc
    pi n * n⁻¹ ^ 2 * (n * (pi n)⁻¹) =
        (pi n * (pi n)⁻¹) * (n⁻¹ * n) * n⁻¹ := by ring
    _ = n⁻¹ := by rw [mul_inv_cancel₀ hpin, inv_mul_cancel₀ hn]; simp

set_option maxHeartbeats 800000 in
/-- The nontrivial root/Weyl Gauss relation underlying the rank-one Suzuki
Bruhat decomposition. -/
public theorem suzukiWeyl_root_weyl_bruhat
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b : BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let n : K := a * b + pi a * a ^ 2 + pi b
    n ≠ 0 →
      ∃ c d e f : K, ∃ u : Kˣ,
        SuzukiWeylGL m * SuzukiRootGL m a b * SuzukiWeylGL m =
          SuzukiRootGL m c d * SuzukiTorusGL m u *
            SuzukiWeylGL m * SuzukiRootGL m e f := by
  let K := BinaryGaloisField (2 * m + 1)
  dsimp only
  let n : K := a * b + pi a * a ^ 2 + pi b
  change n ≠ 0 → ∃ c d e f : K, ∃ u : Kˣ,
    SuzukiWeylGL m * SuzukiRootGL m a b * SuzukiWeylGL m =
      SuzukiRootGL m c d * SuzukiTorusGL m u *
        SuzukiWeylGL m * SuzukiRootGL m e f
  intro hn
  have hpin : pi n ≠ 0 := (map_ne_zero pi).2 hn
  let s : K := a * pi a + b
  let c : K := n⁻¹ * s
  let y0 : K := n⁻¹ * a
  let d : K := y0 + c * pi c
  let e : K := n⁻¹ * b
  let f : K := n⁻¹ * a
  let uval : K := pi n * n⁻¹ ^ 2
  have huval : uval ≠ 0 :=
    mul_ne_zero hpin (pow_ne_zero _ (inv_ne_zero hn))
  let u : Kˣ := Units.mk0 uval huval
  have hpowers := suzukiBruhat_torus_powers
    m pi hpi_sq hpi_formula n hn
  have hq : (u : K) ^ (2 ^ m) = n * (pi n)⁻¹ := hpowers.1
  have hp : (u : K) ^ (1 + 2 ^ m) = n⁻¹ := hpowers.2
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero _ 2
  have hnorm_as : a * s + pi a * a ^ 2 + pi s = n := by
    dsimp only [s, n]
    simp only [map_add, map_mul, hpi_sq]
    linear_combination (a ^ 2 * pi a) * htwo
  have hright : e * f + pi e * e ^ 2 + pi f = n⁻¹ := by
    dsimp only [e, f]
    exact suzukiOvoidNorm_inv m pi hpi_sq a b hn
  have hleft_coord : c * y0 + pi c * c ^ 2 + pi y0 = n⁻¹ := by
    have h := suzukiOvoidNorm_inv m pi hpi_sq a s
    rw [hnorm_as] at h
    exact h hn
  have hleft_s : c * pi c + d = y0 := by
    dsimp only [d]
    linear_combination (c * pi c) * htwo
  have hleft_n : c ^ 2 * pi c + c * d + pi d = n⁻¹ := by
    dsimp only [d]
    simp only [map_add, map_mul, hpi_sq]
    linear_combination hleft_coord + (c ^ 2 * pi c) * htwo
  have hleft_norm : c * d + pi c * c ^ 2 + pi d = n⁻¹ := by
    calc
      c * d + pi c * c ^ 2 + pi d =
          c ^ 2 * pi c + c * d + pi d := by ring
      _ = n⁻¹ := hleft_n
  have hc_n : c * n = s := by
    dsimp only [c]
    calc
      n⁻¹ * s * n = (n⁻¹ * n) * s := by ring
      _ = s := by rw [inv_mul_cancel₀ hn]; simp
  have hy0_n : y0 * n = a := by
    dsimp only [y0]
    calc
      n⁻¹ * a * n = (n⁻¹ * n) * a := by ring
      _ = a := by rw [inv_mul_cancel₀ hn]; simp
  have hn_e : n * e = b := by
    dsimp only [e]
    calc
      n * (n⁻¹ * b) = (n * n⁻¹) * b := by ring
      _ = b := by rw [mul_inv_cancel₀ hn]; simp
  have hn_f : n * f = a := by
    dsimp only [f]
    calc
      n * (n⁻¹ * a) = (n * n⁻¹) * a := by ring
      _ = a := by rw [mul_inv_cancel₀ hn]; simp
  have hn_explicit : a * b + a ^ 2 * pi a + pi b ≠ 0 := by
    simpa [n, mul_comm] using hn
  have hpin_explicit :
      a ^ 2 * pi a ^ 2 + pi a * pi b + b ^ 2 ≠ 0 := by
    intro hz
    apply hpin
    dsimp only [n]
    simp only [map_add, map_mul, map_pow, hpi_sq]
    linear_combination hz
  have hpi_a_sq : pi (a ^ 2) = pi a ^ 2 := map_pow pi a 2
  have hpoly_d : a * pi n + s * pi s = b * n := by
    dsimp only [s, n]
    simp only [map_add, map_mul, map_pow, hpi_sq]
    linear_combination (a * pi a * pi b + a ^ 3 * pi a ^ 2) * htwo
  have hpoly_T : b * pi b + a * pi n = s * n := by
    dsimp only [s, n]
    simp only [map_add, map_mul, map_pow, hpi_sq]
    linear_combination -(a ^ 2 * b * pi a) * htwo
  have hpoly_11 : a * b + pi s = n := by
    dsimp only [s, n]
    simp only [map_add, map_mul, hpi_sq]
    ring
  have hpoly_21 : s * b + pi n = pi a * n := by
    dsimp only [s, n]
    simp only [map_add, map_mul, hpi_sq, hpi_a_sq]
    linear_combination (b ^ 2) * htwo
  have hpoly_22 : s * a + pi b = n := by
    dsimp only [s, n]
    ring
  have hpoly_12 : a ^ 2 * pi n + pi s * pi b + n ^ 2 = 0 := by
    dsimp only [s, n]
    simp only [map_add, map_mul, hpi_sq, hpi_a_sq]
    linear_combination
      (a ^ 2 * pi a * pi b + a ^ 4 * pi a ^ 2 +
        a ^ 2 * b ^ 2 + pi b ^ 2 + a * b * pi b +
        a ^ 2 * pi a * pi b + a ^ 3 * pi a * b) * htwo
  have hpoly_13 : a * pi n + pi s * s + n * b = 0 := by
    calc
      a * pi n + pi s * s + n * b = b * n + b * n := by
        rw [show pi s * s = s * pi s by ring, hpoly_d]
        ring
      _ = 0 := CharTwo.add_self_eq_zero _
  have hpi_c_mul : pi c * pi n = pi s := by
    dsimp only [c]
    simp only [map_mul, map_inv₀]
    calc
      (pi n)⁻¹ * pi s * pi n = ((pi n)⁻¹ * pi n) * pi s := by ring
      _ = pi s := by rw [inv_mul_cancel₀ hpin]; simp
  have hpi_e_mul : pi e * pi n = pi b := by
    dsimp only [e]
    simp only [map_mul, map_inv₀]
    calc
      (pi n)⁻¹ * pi b * pi n = ((pi n)⁻¹ * pi n) * pi b := by ring
      _ = pi b := by rw [inv_mul_cancel₀ hpin]; simp
  have hpi_c_div : pi c = pi s * (pi n)⁻¹ := by
    calc
      pi c = pi c * (pi n * (pi n)⁻¹) := by
        rw [mul_inv_cancel₀ hpin, mul_one]
      _ = (pi c * pi n) * (pi n)⁻¹ := by ring
      _ = pi s * (pi n)⁻¹ := by rw [hpi_c_mul]
  have hpi_e_div : pi e = pi b * (pi n)⁻¹ := by
    calc
      pi e = pi e * (pi n * (pi n)⁻¹) := by
        rw [mul_inv_cancel₀ hpin, mul_one]
      _ = (pi e * pi n) * (pi n)⁻¹ := by ring
      _ = pi b * (pi n)⁻¹ := by rw [hpi_e_mul]
  have hd_r : d * (pi n * n⁻¹) = e := by
    have hd_mul : d * pi n * n = b * n := by
      dsimp only [d]
      calc
        (y0 + c * pi c) * pi n * n =
            (y0 * n) * pi n + (c * n) * (pi c * pi n) := by ring
        _ = a * pi n + s * pi s := by rw [hy0_n, hc_n, hpi_c_mul]
        _ = b * n := hpoly_d
    have hd_pi : d * pi n = b := by
      exact mul_right_cancel₀ hn hd_mul
    calc
      d * (pi n * n⁻¹) = (d * pi n) * n⁻¹ := by ring
      _ = b * n⁻¹ := by rw [hd_pi]
      _ = e := by dsimp only [e]; ring
  have hT : e * pi e + f = s * (pi n)⁻¹ := by
    have hT_mul : (e * pi e + f) * pi n * n = s * n := by
      calc
        (e * pi e + f) * pi n * n =
            (n * e) * (pi e * pi n) + (n * f) * pi n := by ring
        _ = b * pi b + a * pi n := by rw [hn_e, hn_f, hpi_e_mul]
        _ = s * n := hpoly_T
    have hT_pi : (e * pi e + f) * pi n = s := by
      exact mul_right_cancel₀ hn hT_mul
    calc
      e * pi e + f = (e * pi e + f) * (pi n * (pi n)⁻¹) := by
        rw [mul_inv_cancel₀ hpin, mul_one]
      _ = ((e * pi e + f) * pi n) * (pi n)⁻¹ := by ring
      _ = s * (pi n)⁻¹ := by rw [hT_pi]
  have hc_q : c * (n * (pi n)⁻¹) = s * (pi n)⁻¹ := by
    calc
      c * (n * (pi n)⁻¹) = (c * n) * (pi n)⁻¹ := by ring
      _ = s * (pi n)⁻¹ := by rw [hc_n]
  have h11 :
      (c * pi c + d) * n * e + pi c * (pi n * n⁻¹) = 1 := by
    rw [hleft_s]
    calc
      y0 * n * e + pi c * (pi n * n⁻¹) =
          (a * b + pi s) * n⁻¹ := by
        rw [hy0_n]
        dsimp only [e]
        rw [show pi c * (pi n * n⁻¹) = pi s * n⁻¹ by
          calc
            pi c * (pi n * n⁻¹) = (pi c * pi n) * n⁻¹ := by ring
            _ = pi s * n⁻¹ := by rw [hpi_c_mul]]
        ring
      _ = n * n⁻¹ := by rw [hpoly_11]
      _ = 1 := mul_inv_cancel₀ hn
  have h12 :
      (c * pi c + d) * n * f + pi c * (pi n * n⁻¹) * pi e +
          n * (pi n)⁻¹ = 0 := by
    rw [hleft_s, hpi_c_div, hpi_e_div]
    have hmiddle :
        (pi s * (pi n)⁻¹) * (pi n * n⁻¹) *
            (pi b * (pi n)⁻¹) =
          pi s * pi b * n⁻¹ * (pi n)⁻¹ := by
      calc
        (pi s * (pi n)⁻¹) * (pi n * n⁻¹) *
              (pi b * (pi n)⁻¹) =
            ((pi n)⁻¹ * pi n) *
              (pi s * pi b * n⁻¹ * (pi n)⁻¹) := by ring
        _ = pi s * pi b * n⁻¹ * (pi n)⁻¹ := by
          rw [inv_mul_cancel₀ hpin, one_mul]
    calc
      y0 * n * f +
            (pi s * (pi n)⁻¹) * (pi n * n⁻¹) *
              (pi b * (pi n)⁻¹) + n * (pi n)⁻¹ =
          a ^ 2 * n⁻¹ + pi s * pi b * n⁻¹ * (pi n)⁻¹ +
            n * (pi n)⁻¹ := by
        rw [hy0_n, hmiddle]
        dsimp only [f]
        ring
      _ = (a ^ 2 * pi n + pi s * pi b + n ^ 2) *
            n⁻¹ * (pi n)⁻¹ := by
        have ha_cancel :
            a ^ 2 * pi n * n⁻¹ * (pi n)⁻¹ = a ^ 2 * n⁻¹ := by
          calc
            a ^ 2 * pi n * n⁻¹ * (pi n)⁻¹ =
                (pi n * (pi n)⁻¹) * (a ^ 2 * n⁻¹) := by ring
            _ = a ^ 2 * n⁻¹ := by rw [mul_inv_cancel₀ hpin, one_mul]
        have hn_cancel :
            n ^ 2 * n⁻¹ * (pi n)⁻¹ = n * (pi n)⁻¹ := by
          calc
            n ^ 2 * n⁻¹ * (pi n)⁻¹ =
                (n * n⁻¹) * (n * (pi n)⁻¹) := by ring
            _ = n * (pi n)⁻¹ := by rw [mul_inv_cancel₀ hn, one_mul]
        symm
        calc
          (a ^ 2 * pi n + pi s * pi b + n ^ 2) *
                n⁻¹ * (pi n)⁻¹ =
              a ^ 2 * pi n * n⁻¹ * (pi n)⁻¹ +
                pi s * pi b * n⁻¹ * (pi n)⁻¹ +
                n ^ 2 * n⁻¹ * (pi n)⁻¹ := by ring
          _ = a ^ 2 * n⁻¹ + pi s * pi b * n⁻¹ * (pi n)⁻¹ +
                n * (pi n)⁻¹ := by rw [ha_cancel, hn_cancel]
      _ = 0 := by rw [hpoly_12]; simp
  have h13 :
      (c * pi c + d) * n * (e * f + pi e * e ^ 2 + pi f) +
          pi c * (pi n * n⁻¹) * (e * pi e + f) +
          n * (pi n)⁻¹ * e = 0 := by
    rw [hright, hleft_s, hT, hpi_c_div]
    have hmiddle :
        (pi s * (pi n)⁻¹) * (pi n * n⁻¹) *
            (s * (pi n)⁻¹) =
          pi s * s * n⁻¹ * (pi n)⁻¹ := by
      calc
        (pi s * (pi n)⁻¹) * (pi n * n⁻¹) *
              (s * (pi n)⁻¹) =
            ((pi n)⁻¹ * pi n) *
              (pi s * s * n⁻¹ * (pi n)⁻¹) := by ring
        _ = pi s * s * n⁻¹ * (pi n)⁻¹ := by
          rw [inv_mul_cancel₀ hpin, one_mul]
    have hne_scaled : n * (pi n)⁻¹ * e = b * (pi n)⁻¹ := by
      calc
        n * (pi n)⁻¹ * e = (n * e) * (pi n)⁻¹ := by ring
        _ = b * (pi n)⁻¹ := by rw [hn_e]
    calc
      y0 * n * n⁻¹ +
            (pi s * (pi n)⁻¹) * (pi n * n⁻¹) *
              (s * (pi n)⁻¹) + n * (pi n)⁻¹ * e =
          a * n⁻¹ + pi s * s * n⁻¹ * (pi n)⁻¹ +
            b * (pi n)⁻¹ := by
        rw [hy0_n, hmiddle, hne_scaled]
      _ = (a * pi n + pi s * s + n * b) *
            n⁻¹ * (pi n)⁻¹ := by
        field_simp [hn, hpin]
      _ = 0 := by rw [hpoly_13]; simp
  have h21 : c * n * e + pi n * n⁻¹ = pi a := by
    rw [hc_n]
    dsimp only [e]
    calc
      s * (n⁻¹ * b) + pi n * n⁻¹ = (s * b + pi n) * n⁻¹ := by ring
      _ = (pi a * n) * n⁻¹ := by rw [hpoly_21]
      _ = pi a := by rw [mul_assoc, mul_inv_cancel₀ hn, mul_one]
  have h22 : c * n * f + pi n * n⁻¹ * pi e = 1 := by
    rw [hc_n, hpi_e_div]
    dsimp only [f]
    calc
      s * (n⁻¹ * a) + pi n * n⁻¹ * (pi b * (pi n)⁻¹) =
          (s * a + pi b) * n⁻¹ := by
        have hcancel :
            pi n * n⁻¹ * (pi b * (pi n)⁻¹) = pi b * n⁻¹ := by
          calc
            pi n * n⁻¹ * (pi b * (pi n)⁻¹) =
                (pi n * (pi n)⁻¹) * (pi b * n⁻¹) := by ring
            _ = pi b * n⁻¹ := by rw [mul_inv_cancel₀ hpin, one_mul]
        rw [hcancel]
        ring
      _ = n * n⁻¹ := by
        rw [hpoly_22]
      _ = 1 := mul_inv_cancel₀ hn
  have h23 :
      c * n * (e * f + pi e * e ^ 2 + pi f) +
          pi n * n⁻¹ * (e * pi e + f) = 0 := by
    rw [hright, hT]
    calc
      c * n * n⁻¹ + pi n * n⁻¹ * (s * (pi n)⁻¹) =
          s * n⁻¹ + s * n⁻¹ := by
        rw [hc_n]
        field_simp [hn, hpin]
        ring
      _ = 0 := CharTwo.add_self_eq_zero _
  have h01 :
      (c * d + pi c * c ^ 2 + pi d) * n * e +
          d * (pi n * n⁻¹) = 0 := by
    rw [hleft_norm, hd_r, inv_mul_cancel₀ hn, one_mul]
    exact CharTwo.add_self_eq_zero e
  have h02 :
      (c * d + pi c * c ^ 2 + pi d) * n * f +
          d * (pi n * n⁻¹) * pi e + c * (n * (pi n)⁻¹) = 0 := by
    rw [hleft_norm, hd_r, hc_q, inv_mul_cancel₀ hn, one_mul]
    calc
      f + e * pi e + s * (pi n)⁻¹ =
          (e * pi e + f) + s * (pi n)⁻¹ := by ring
      _ = s * (pi n)⁻¹ + s * (pi n)⁻¹ := by rw [hT]
      _ = 0 := CharTwo.add_self_eq_zero _
  have h03 :
      (c * d + pi c * c ^ 2 + pi d) * n *
            (e * f + pi e * e ^ 2 + pi f) +
          d * (pi n * n⁻¹) * (e * pi e + f) +
          c * (n * (pi n)⁻¹) * e + n⁻¹ = 0 := by
    rw [hleft_norm, hright, hd_r, hc_q,
      inv_mul_cancel₀ hn, one_mul, hT]
    linear_combination (n⁻¹) * htwo +
      (e * (s * (pi n)⁻¹)) * htwo
  have h00_goal :
      1 = (c * d + pi c * c ^ 2 + pi d) * n := by
    rw [hleft_norm, inv_mul_cancel₀ hn]
  have h01_goal :
      0 = (c * d + pi c * c ^ 2 + pi d) * n * e +
        d * (pi n * n⁻¹) := h01.symm
  have h02_goal :
      0 = (c * d + pi c * c ^ 2 + pi d) * n * f +
        d * (pi n * n⁻¹) * pi e + c * (n * (pi n)⁻¹) := h02.symm
  have h03_goal :
      0 = (c * d + pi c * c ^ 2 + pi d) * n *
            (e * f + pi e * e ^ 2 + pi f) +
          d * (pi n * n⁻¹) * (e * pi e + f) +
          c * (n * (pi n)⁻¹) * e + n⁻¹ := h03.symm
  have h10_goal : a = (c * pi c + d) * n := by
    rw [hleft_s, hy0_n]
  have h11_goal :
      1 = (c * pi c + d) * n * e + pi c * (pi n * n⁻¹) := h11.symm
  have h12_goal :
      0 = (c * pi c + d) * n * f +
        pi c * (pi n * n⁻¹) * pi e + n * (pi n)⁻¹ := h12.symm
  have h13_goal :
      0 = (c * pi c + d) * n *
            (e * f + pi e * e ^ 2 + pi f) +
          pi c * (pi n * n⁻¹) * (e * pi e + f) +
          n * (pi n)⁻¹ * e := h13.symm
  have h20_goal : a * pi a + b = c * n := by
    rw [hc_n]
  have h21_goal : pi a = c * n * e + pi n * n⁻¹ := h21.symm
  have h22_goal : 1 = c * n * f + pi n * n⁻¹ * pi e := h22.symm
  have h23_goal :
      0 = c * n * (e * f + pi e * e ^ 2 + pi f) +
        pi n * n⁻¹ * (e * pi e + f) := h23.symm
  have h30_goal : a * b + pi a * a ^ 2 + pi b = n := rfl
  have h31_goal : b = n * e := hn_e.symm
  have h32_goal : a = n * f := hn_f.symm
  have h33_goal :
      1 = n * (e * f + pi e * e ^ 2 + pi f) := by
    rw [hright, mul_inv_cancel₀ hn]
  refine ⟨c, d, e, f, u, ?_⟩
  have hroot (x y : K) :
      SuzukiRootMatrix m x y =
        !![1, x, y, x * y + pi x * x ^ 2 + pi y;
           0, 1, pi x, x * pi x + y;
           0, 0, 1, x;
           0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SuzukiRootMatrix, hpi_formula, pow_add]
    all_goals ring
  have htorus :
      SuzukiTorusMatrix m u =
        !![n⁻¹, 0, 0, 0;
           0, n * (pi n)⁻¹, 0, 0;
           0, 0, pi n * n⁻¹, 0;
           0, 0, 0, n] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SuzukiTorusMatrix, hq, hp]
  ext i j
  change
    (SuzukiWeylMatrix m * SuzukiRootMatrix m a b * SuzukiWeylMatrix m) i j =
      (SuzukiRootMatrix m c d * SuzukiTorusMatrix m u * SuzukiWeylMatrix m *
        SuzukiRootMatrix m e f) i j
  rw [hroot a b, hroot c d, hroot e f, htorus]
  fin_cases i <;> fin_cases j <;>
    simp (config := { zeta := false }) [SuzukiWeylMatrix,
      Matrix.mul_apply, Fin.sum_univ_four]
  all_goals assumption

/-- The split torus normalizes the Suzuki root subgroup. -/
public theorem suzukiTorusClosure_le_normalizer_rootClosure
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let F : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
    let H : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
    H ≤ Subgroup.normalizer F := by
  let K := BinaryGaloisField (2 * m + 1)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  change H ≤ Subgroup.normalizer F
  intro h hh
  rcases (suzukiTorusGL_mem_closure_iff m h).mp hh with ⟨u, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro f
  constructor
  · intro hf
    rcases (suzukiRootGL_mem_closure_iff
      m pi hpi_sq hpi_formula f).mp hf with ⟨a, b, rfl⟩
    rw [suzukiTorusGL_conj_root m pi hpi_sq hpi_formula]
    exact Subgroup.subset_closure ⟨_, _, rfl⟩
  · intro hf
    rcases (suzukiRootGL_mem_closure_iff
      m pi hpi_sq hpi_formula
        (SuzukiTorusGL m u * f * (SuzukiTorusGL m u)⁻¹)).mp hf with
      ⟨a, b, hab⟩
    have hf_eq :
        f = SuzukiTorusGL m u⁻¹ * SuzukiRootGL m a b *
          (SuzukiTorusGL m u⁻¹)⁻¹ := by
      calc
        f = (SuzukiTorusGL m u)⁻¹ *
              (SuzukiTorusGL m u * f * (SuzukiTorusGL m u)⁻¹) *
              SuzukiTorusGL m u := by group
        _ = (SuzukiTorusGL m u)⁻¹ * SuzukiRootGL m a b *
              SuzukiTorusGL m u := by rw [hab]
        _ = SuzukiTorusGL m u⁻¹ * SuzukiRootGL m a b *
              (SuzukiTorusGL m u⁻¹)⁻¹ := by
            rw [suzukiTorusGL_inv m u, suzukiTorusGL_inv m u⁻¹]
            simp
    rw [hf_eq, suzukiTorusGL_conj_root m pi hpi_sq hpi_formula]
    exact Subgroup.subset_closure ⟨_, _, rfl⟩

/-- A normalized product of disjoint finite subgroups has the expected
cardinality. -/
private theorem natCard_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type*} [Group G] (F H : Subgroup G)
    (hnormal : H ≤ Subgroup.normalizer F) (hdisjoint : Disjoint F H) :
    Nat.card (F ⊔ H : Subgroup G) = Nat.card F * Nat.card H := by
  let toB : F × H → ↥(F ⊔ H) := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have htoB_injective : Function.Injective toB := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have htoB_surjective : Function.Surjective toB := by
    intro b
    have hb : (b : G) ∈ (F : Set G) * (H : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left F H hnormal]
      exact b.property
    rcases hb with ⟨f, hf, h, hh, hfh⟩
    refine ⟨(⟨f, hf⟩, ⟨h, hh⟩), ?_⟩
    exact Subtype.ext hfh
  calc
    Nat.card (F ⊔ H : Subgroup G) = Nat.card (F × H) :=
      Nat.card_congr
        (Equiv.ofBijective toB ⟨htoB_injective, htoB_surjective⟩).symm
    _ = Nat.card F * Nat.card H := Nat.card_prod F H


/-- XI.3.2-style rank-one Bruhat decomposition for the concrete generated
Suzuki group. -/
public theorem suzukiMatrixGroup_bruhat_decomposition
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let F : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
    let H : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
    let B : Subgroup (GL (Fin 4) K) := F ⊔ H
    ∀ g : GL (Fin 4) K, g ∈ SuzukiMatrixGroup m →
      g ∈ B ∨ ∃ b f : GL (Fin 4) K,
        b ∈ B ∧ f ∈ F ∧ g = b * SuzukiWeylGL m * f := by
  let K := BinaryGaloisField (2 * m + 1)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  let B : Subgroup (GL (Fin 4) K) := F ⊔ H
  let P : GL (Fin 4) K → Prop := fun g =>
    g ∈ B ∨ ∃ b f : GL (Fin 4) K,
      b ∈ B ∧ f ∈ F ∧ g = b * SuzukiWeylGL m * f
  change ∀ g : GL (Fin 4) K, g ∈ SuzukiMatrixGroup m → P g
  have hF_le_B : F ≤ B := le_sup_left
  have hH_le_B : H ≤ B := le_sup_right
  have hroot_mem (a b : K) : SuzukiRootGL m a b ∈ F :=
    Subgroup.subset_closure ⟨a, b, rfl⟩
  have htorus_mem (u : Kˣ) : SuzukiTorusGL m u ∈ H :=
    Subgroup.subset_closure ⟨u, rfl⟩
  have hH_normalizes_F : H ≤ Subgroup.normalizer F :=
    suzukiTorusClosure_le_normalizer_rootClosure
      m pi hpi_sq hpi_formula
  have hweyl_sq : SuzukiWeylGL m * SuzukiWeylGL m = 1 :=
    suzukiWeylGL_mul_self m
  have hweyl_inv : (SuzukiWeylGL m)⁻¹ = SuzukiWeylGL m := by
    symm
    exact eq_inv_of_mul_eq_one_right hweyl_sq
  have hmul_root : ∀ g : GL (Fin 4) K, P g →
      ∀ a b : K, P (g * SuzukiRootGL m a b) := by
    intro g hg a b
    rcases hg with hgB | ⟨x, y, hxB, hyF, rfl⟩
    · exact Or.inl (B.mul_mem hgB (hF_le_B (hroot_mem a b)))
    · exact Or.inr ⟨x, y * SuzukiRootGL m a b, hxB,
        F.mul_mem hyF (hroot_mem a b), by group⟩
  have hmul_torus : ∀ g : GL (Fin 4) K, P g →
      ∀ u : Kˣ, P (g * SuzukiTorusGL m u) := by
    intro g hg u
    rcases hg with hgB | ⟨x, y, hxB, hyF, rfl⟩
    · exact Or.inl (B.mul_mem hgB (hH_le_B (htorus_mem u)))
    · let y' : GL (Fin 4) K :=
        (SuzukiTorusGL m u)⁻¹ * y * SuzukiTorusGL m u
      have hy'F : y' ∈ F :=
        (((Subgroup.mem_normalizer_iff'').mp
          (hH_normalizes_F (htorus_mem u))) y).mp hyF
      have hweyl_torus :
          SuzukiWeylGL m * SuzukiTorusGL m u =
            SuzukiTorusGL m u⁻¹ * SuzukiWeylGL m := by
        calc
          SuzukiWeylGL m * SuzukiTorusGL m u =
              (SuzukiWeylGL m * SuzukiTorusGL m u * SuzukiWeylGL m) *
                SuzukiWeylGL m := by rw [mul_assoc, hweyl_sq, mul_one]
          _ = SuzukiTorusGL m u⁻¹ * SuzukiWeylGL m := by
            rw [suzukiWeylGL_conj_torus]
      refine Or.inr ⟨x * SuzukiTorusGL m u⁻¹, y',
        B.mul_mem hxB (hH_le_B (htorus_mem u⁻¹)), hy'F, ?_⟩
      dsimp only [y']
      calc
        x * SuzukiWeylGL m * y * SuzukiTorusGL m u =
            x * (SuzukiWeylGL m * SuzukiTorusGL m u) *
              ((SuzukiTorusGL m u)⁻¹ * y * SuzukiTorusGL m u) := by group
        _ = x * (SuzukiTorusGL m u⁻¹ * SuzukiWeylGL m) *
              ((SuzukiTorusGL m u)⁻¹ * y * SuzukiTorusGL m u) := by
            rw [hweyl_torus]
        _ = (x * SuzukiTorusGL m u⁻¹) * SuzukiWeylGL m *
              ((SuzukiTorusGL m u)⁻¹ * y * SuzukiTorusGL m u) := by group
  have hmul_weyl : ∀ g : GL (Fin 4) K, P g →
      P (g * SuzukiWeylGL m) := by
    intro g hg
    rcases hg with hgB | ⟨x, y, hxB, hyF, rfl⟩
    · exact Or.inr ⟨g, 1, hgB, F.one_mem, by simp⟩
    · rcases (suzukiRootGL_mem_closure_iff
        m pi hpi_sq hpi_formula y).mp hyF with ⟨a, b, rfl⟩
      let n : K := a * b + pi a * a ^ 2 + pi b
      by_cases hn : n = 0
      · have hab : a = 0 ∧ b = 0 :=
          (suzukiOvoidNorm_eq_zero m pi hpi_sq a b).mp hn
        rcases hab with ⟨rfl, rfl⟩
        rw [suzukiRootGL_zero_zero, mul_one, mul_assoc, hweyl_sq, mul_one]
        exact Or.inl hxB
      · rcases suzukiWeyl_root_weyl_bruhat
          m pi hpi_sq hpi_formula a b hn with ⟨c, d, e, f, u, hgauss⟩
        refine Or.inr
          ⟨x * (SuzukiRootGL m c d * SuzukiTorusGL m u),
            SuzukiRootGL m e f,
            B.mul_mem hxB (B.mul_mem (hF_le_B (hroot_mem c d))
              (hH_le_B (htorus_mem u))), hroot_mem e f, ?_⟩
        calc
          x * SuzukiWeylGL m * SuzukiRootGL m a b * SuzukiWeylGL m =
              x * (SuzukiWeylGL m * SuzukiRootGL m a b * SuzukiWeylGL m) := by group
          _ = x * (SuzukiRootGL m c d * SuzukiTorusGL m u *
                SuzukiWeylGL m * SuzukiRootGL m e f) := by rw [hgauss]
          _ = x * (SuzukiRootGL m c d * SuzukiTorusGL m u) *
                SuzukiWeylGL m * SuzukiRootGL m e f := by group
  intro g hg
  exact Subgroup.closure_induction_right
    (p := fun x _ => P x)
    (Or.inl B.one_mem)
    (fun x _ A hA hx => by
      rcases hA with hroot | hrest
      · rcases hroot with ⟨a, b, rfl⟩
        exact hmul_root x hx a b
      · rcases hrest with htorus | hweyl
        · rcases htorus with ⟨u, rfl⟩
          exact hmul_torus x hx u
        · subst A
          exact hmul_weyl x hx)
    (fun x _ A hA hx => by
      rcases hA with hroot | hrest
      · rcases hroot with ⟨a, b, rfl⟩
        have hinvF : (SuzukiRootGL m a b)⁻¹ ∈ F :=
          F.inv_mem (hroot_mem a b)
        rcases (suzukiRootGL_mem_closure_iff
          m pi hpi_sq hpi_formula _).mp hinvF with ⟨c, d, hcd⟩
        rw [hcd]
        exact hmul_root x hx c d
      · rcases hrest with htorus | hweyl
        · rcases htorus with ⟨u, rfl⟩
          rw [suzukiTorusGL_inv]
          exact hmul_torus x hx u⁻¹
        · subst A
          rw [hweyl_inv]
          exact hmul_weyl x hx)
    hg

/-- In the concrete Suzuki group, the stabilizer of the point at infinity is
the root subgroup extended by the split torus. -/
private theorem suzukiMatrixGroup_stabilizer_infinity
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let F : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
    let H : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
    ∀ g : SuzukiMatrixGroup m,
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf ↔
        (g : GL (Fin 4) K) ∈ F ⊔ H := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  let B : Subgroup (GL (Fin 4) K) := F ⊔ H
  let S : Subgroup (GL (Fin 4) K) :=
    (MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K)) pinf).comap
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
  change ∀ g : SuzukiMatrixGroup m,
    (Matrix.GeneralLinearGroup.toLin
      (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf ↔
      (g : GL (Fin 4) K) ∈ B
  have hF_le_S : F ≤ S := by
    dsimp only [F]
    rw [Subgroup.closure_le]
    rintro A ⟨a, b, rfl⟩
    change (Matrix.GeneralLinearGroup.toLin
      (SuzukiRootGL m a b)).toLinearEquiv • pinf = pinf
    exact suzukiRoot_smul_infinity m a b
  have hH_le_S : H ≤ S := by
    dsimp only [H]
    rw [Subgroup.closure_le]
    rintro A ⟨u, rfl⟩
    change (Matrix.GeneralLinearGroup.toLin
      (SuzukiTorusGL m u)).toLinearEquiv • pinf = pinf
    exact suzukiTorus_smul_infinity m u
  have hB_le_S : B ≤ S := sup_le hF_le_S hH_le_S
  have hB_fix : ∀ b : GL (Fin 4) K, b ∈ B →
      (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv • pinf = pinf := by
    intro b hb
    exact hB_le_S hb
  have hF_fix : ∀ f : GL (Fin 4) K, f ∈ F →
      (Matrix.GeneralLinearGroup.toLin f).toLinearEquiv • pinf = pinf := by
    intro f hf
    exact hB_fix f ((show F ≤ B from le_sup_left) hf)
  have hmul_smul (x y : GL (Fin 4) K) (z : ℙ K (Fin 4 → K)) :
      (Matrix.GeneralLinearGroup.toLin (x * y)).toLinearEquiv • z =
        (Matrix.GeneralLinearGroup.toLin x).toLinearEquiv •
          ((Matrix.GeneralLinearGroup.toLin y).toLinearEquiv • z) := by
    rw [map_mul]
    change ((Matrix.GeneralLinearGroup.toLin x).toLinearEquiv *
      (Matrix.GeneralLinearGroup.toLin y).toLinearEquiv) • z = _
    exact mul_smul _ _ _
  have hp_ne : p 0 0 ≠ pinf := by
    intro hp
    exact suzukiOvoidInfinity_not_mem_range m pi ⟨(0, 0), hp⟩
  intro g
  constructor
  · intro hgfix
    rcases suzukiMatrixGroup_bruhat_decomposition
      m pi hpi_sq hpi_formula (g : GL (Fin 4) K) g.property with
      hgB | ⟨b, f, hbB, hfF, hgf⟩
    · exact hgB
    · have hbfix := hB_fix b hbB
      have hffix := hF_fix f hfF
      have hbp :
          (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv • p 0 0 =
            pinf := by
        calc
          (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv • p 0 0 =
              (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv •
                ((Matrix.GeneralLinearGroup.toLin
                  (SuzukiWeylGL m)).toLinearEquiv • pinf) := by
                rw [suzukiWeyl_smul_infinity m pi]
          _ = (Matrix.GeneralLinearGroup.toLin
                (b * SuzukiWeylGL m)).toLinearEquiv • pinf := by
              simp only [hmul_smul]
          _ = (Matrix.GeneralLinearGroup.toLin
                (b * SuzukiWeylGL m)).toLinearEquiv •
                  ((Matrix.GeneralLinearGroup.toLin f).toLinearEquiv • pinf) := by
              rw [hffix]
          _ = (Matrix.GeneralLinearGroup.toLin
                (b * SuzukiWeylGL m * f)).toLinearEquiv • pinf := by
              simp only [hmul_smul]
          _ = pinf := by rw [← hgf]; exact hgfix
      have hpinf : p 0 0 = pinf := by
        have hsame :
            (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv • p 0 0 =
              (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv • pinf :=
          hbp.trans hbfix.symm
        change Matrix.GeneralLinearGroup.toLin b • p 0 0 =
          Matrix.GeneralLinearGroup.toLin b • pinf at hsame
        exact smul_left_cancel _ hsame
      exact False.elim (hp_ne hpinf)
  · intro hgB
    exact hB_fix (g : GL (Fin 4) K) hgB

/-- An element fixing both standard ovoid points belongs to the split torus. -/
public theorem suzukiMatrixGroup_mem_torus_of_fix_infinity_zero
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let H : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
    ∀ g : SuzukiMatrixGroup m,
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf →
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • p 0 0 = p 0 0 →
      (g : GL (Fin 4) K) ∈ H := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  let B : Subgroup (GL (Fin 4) K) := F ⊔ H
  change ∀ g : SuzukiMatrixGroup m,
    (Matrix.GeneralLinearGroup.toLin
      (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf →
    (Matrix.GeneralLinearGroup.toLin
      (g : GL (Fin 4) K)).toLinearEquiv • p 0 0 = p 0 0 →
    (g : GL (Fin 4) K) ∈ H
  have hnormal : H ≤ Subgroup.normalizer F :=
    suzukiTorusClosure_le_normalizer_rootClosure
      m pi hpi_sq hpi_formula
  have hmul_smul (x y : GL (Fin 4) K) (z : ℙ K (Fin 4 → K)) :
      (Matrix.GeneralLinearGroup.toLin (x * y)).toLinearEquiv • z =
        (Matrix.GeneralLinearGroup.toLin x).toLinearEquiv •
          ((Matrix.GeneralLinearGroup.toLin y).toLinearEquiv • z) := by
    rw [map_mul]
    change ((Matrix.GeneralLinearGroup.toLin x).toLinearEquiv *
      (Matrix.GeneralLinearGroup.toLin y).toLinearEquiv) • z = _
    exact mul_smul _ _ _
  intro g hginf hgzero
  have hgB : (g : GL (Fin 4) K) ∈ B :=
    (suzukiMatrixGroup_stabilizer_infinity
      m pi hpi_sq hpi_formula g).mp hginf
  have hgFH : (g : GL (Fin 4) K) ∈ (F : Set (GL (Fin 4) K)) * H := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left F H hnormal]
    exact hgB
  rcases hgFH with ⟨f, hfF, h, hhH, hfh⟩
  rcases (suzukiRootGL_mem_closure_iff
    m pi hpi_sq hpi_formula f).mp hfF with ⟨a, b, rfl⟩
  rcases (suzukiTorusGL_mem_closure_iff m h).mp hhH with ⟨u, rfl⟩
  have hfh' : SuzukiRootGL m a b * SuzukiTorusGL m u =
      (g : GL (Fin 4) K) := hfh
  have hroot_zero :
      (Matrix.GeneralLinearGroup.toLin
        (SuzukiRootGL m a b)).toLinearEquiv • p 0 0 =
          p a (b + pi a * a) := by
    simpa only [zero_add] using
      (suzukiRoot_smul_finite m pi hpi_sq hpi_formula a b 0 0)
  have htorus_zero :
      (Matrix.GeneralLinearGroup.toLin
        (SuzukiTorusGL m u)).toLinearEquiv • p 0 0 = p 0 0 := by
    simpa only [p, mul_zero] using
      (suzukiTorus_smul_finite m pi hpi_sq hpi_formula u 0 0)
  have hpoint : p a (b + pi a * a) = p 0 0 := by
    calc
      p a (b + pi a * a) =
          (Matrix.GeneralLinearGroup.toLin
            (SuzukiRootGL m a b)).toLinearEquiv • p 0 0 := hroot_zero.symm
      _ = (Matrix.GeneralLinearGroup.toLin
            (SuzukiRootGL m a b)).toLinearEquiv •
            ((Matrix.GeneralLinearGroup.toLin
              (SuzukiTorusGL m u)).toLinearEquiv • p 0 0) :=
          congrArg (fun z : ℙ K (Fin 4 → K) =>
            (Matrix.GeneralLinearGroup.toLin
              (SuzukiRootGL m a b)).toLinearEquiv • z) htorus_zero.symm
      _ = (Matrix.GeneralLinearGroup.toLin
            (SuzukiRootGL m a b * SuzukiTorusGL m u)).toLinearEquiv •
              p 0 0 := (hmul_smul _ _ _).symm
      _ = p 0 0 := by rw [hfh']; exact hgzero
  have hab : (a, b + pi a * a) = (0, 0) :=
    suzukiOvoidPoint_injective m pi hpoint
  have ha : a = 0 := congrArg Prod.fst hab
  have hb : b = 0 := by
    have hsecond := congrArg Prod.snd hab
    simpa [ha] using hsecond
  rw [← hfh', ha, hb, suzukiRootGL_zero_zero, one_mul]
  exact Subgroup.subset_closure ⟨u, rfl⟩

/-- No nonidentity concrete Suzuki element fixes three distinct ovoid points. -/
private theorem suzukiMatrixGroup_three_point_free
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∀ g : SuzukiMatrixGroup m,
      (∃ a b c, a ∈ O ∧ b ∈ O ∧ c ∈ O ∧
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • a = a ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • b = b ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • c = c) → g = 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  let act : SuzukiMatrixGroup m → ℙ K (Fin 4 → K) →
      ℙ K (Fin 4 → K) := fun g z =>
    (Matrix.GeneralLinearGroup.toLin
      (g : GL (Fin 4) K)).toLinearEquiv • z
  change ∀ g : SuzukiMatrixGroup m,
    (∃ a b c, a ∈ O ∧ b ∈ O ∧ c ∈ O ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      act g a = a ∧ act g b = b ∧ act g c = c) → g = 1
  have hact_mul (x y : SuzukiMatrixGroup m)
      (z : ℙ K (Fin 4 → K)) :
      act (x * y) z = act x (act y z) := by
    dsimp only [act]
    change (Matrix.GeneralLinearGroup.toLin
      ((x : GL (Fin 4) K) * (y : GL (Fin 4) K))).toLinearEquiv • z = _
    rw [map_mul]
    change ((Matrix.GeneralLinearGroup.toLin
      (x : GL (Fin 4) K)).toLinearEquiv *
      (Matrix.GeneralLinearGroup.toLin
        (y : GL (Fin 4) K)).toLinearEquiv) • z = _
    exact mul_smul _ _ _
  have hact_inv_smul (x : SuzukiMatrixGroup m)
      (z : ℙ K (Fin 4 → K)) : act x⁻¹ (act x z) = z := by
    dsimp only [act]
    change (Matrix.GeneralLinearGroup.toLin
      ((x : GL (Fin 4) K)⁻¹)).toLinearEquiv •
        ((Matrix.GeneralLinearGroup.toLin
          (x : GL (Fin 4) K)).toLinearEquiv • z) = z
    rw [map_inv]
    change (Matrix.GeneralLinearGroup.toLin
      (x : GL (Fin 4) K))⁻¹ •
        (Matrix.GeneralLinearGroup.toLin (x : GL (Fin 4) K) • z) = z
    exact inv_smul_smul _ _
  intro g
  rintro ⟨a, b, c, haO, hbO, hcO, hab, hac, hbc, hga, hgb, hgc⟩
  rcases suzukiOvoid_exists_pair_to_standard
    m pi hpi_sq hpi_formula a b haO hbO hab with
    ⟨k, hka, hkb⟩
  change act k a = pinf at hka
  change act k b = p 0 0 at hkb
  let g' : SuzukiMatrixGroup m := k * g * k⁻¹
  have hconj_fix (z : ℙ K (Fin 4 → K)) (hgz : act g z = z) :
      act g' (act k z) = act k z := by
    dsimp only [g']
    rw [hact_mul, hact_inv_smul, hact_mul, hgz]
  have hg'inf : act g' pinf = pinf := by
    rw [← hka]
    exact hconj_fix a hga
  have hg'zero : act g' (p 0 0) = p 0 0 := by
    rw [← hkb]
    exact hconj_fix b hgb
  have hg'H : (g' : GL (Fin 4) K) ∈ H :=
    suzukiMatrixGroup_mem_torus_of_fix_infinity_zero
      m pi hpi_sq hpi_formula g' hg'inf hg'zero
  rcases (suzukiTorusGL_mem_closure_iff
    m (g' : GL (Fin 4) K)).mp hg'H with ⟨u, hgu⟩
  let d : ℙ K (Fin 4 → K) := act k c
  have hdO : d ∈ O := by
    exact suzukiMatrixGroup_smul_mem_ovoid
      m pi hpi_sq hpi_formula k c hcO
  have hdfix : act g' d = d := hconj_fix c hgc
  have hd_ne_inf : d ≠ pinf := by
    intro hd
    have hsame : act k c = act k a := hd.trans hka.symm
    have hca : c = a := by
      dsimp only [act] at hsame
      change Matrix.GeneralLinearGroup.toLin (k : GL (Fin 4) K) • c =
        Matrix.GeneralLinearGroup.toLin (k : GL (Fin 4) K) • a at hsame
      exact smul_left_cancel _ hsame
    exact hac hca.symm
  have hd_ne_zero : d ≠ p 0 0 := by
    intro hd
    have hsame : act k c = act k b := hd.trans hkb.symm
    have hcb : c = b := by
      dsimp only [act] at hsame
      change Matrix.GeneralLinearGroup.toLin (k : GL (Fin 4) K) • c =
        Matrix.GeneralLinearGroup.toLin (k : GL (Fin 4) K) • b at hsame
      exact smul_left_cancel _ hsame
    exact hbc hcb.symm
  rcases hdO with hdinf | ⟨xy, hxy⟩
  · exact False.elim (hd_ne_inf (by simpa using hdinf))
  · rcases xy with ⟨x, y⟩
    have hxy' : p x y = d := hxy
    have hfixxy :
        p ((u : K) * x) ((u : K) * pi (u : K) * y) = p x y := by
      calc
        p ((u : K) * x) ((u : K) * pi (u : K) * y) =
            (Matrix.GeneralLinearGroup.toLin
              (SuzukiTorusGL m u)).toLinearEquiv • p x y := by
          rw [suzukiTorus_smul_finite m pi hpi_sq hpi_formula]
        _ = act g' d := by
          dsimp only [act]
          rw [hgu, hxy']
        _ = d := hdfix
        _ = p x y := hxy'.symm
    have hcoords :
        ((u : K) * x, (u : K) * pi (u : K) * y) = (x, y) :=
      suzukiOvoidPoint_injective m pi hfixxy
    have hxy_ne : (x, y) ≠ (0, 0) := by
      intro hzero
      apply hd_ne_zero
      calc
        d = p x y := hxy'.symm
        _ = p 0 0 := by cases hzero; rfl
    have hu : u = 1 := by
      by_cases hx : x = 0
      · have hy : y ≠ 0 := by
          intro hy
          exact hxy_ne (Prod.ext hx hy)
        apply (binaryGaloisField_tits_norm_eq_one_iff
          m pi hpi_sq u).mp
        apply mul_right_cancel₀ hy
        simpa using congrArg Prod.snd hcoords
      · apply Units.ext
        apply mul_right_cancel₀ hx
        simpa using congrArg Prod.fst hcoords
    have hg'one : g' = 1 := by
      apply Subtype.ext
      rw [hgu, hu]
      exact suzukiTorusGL_one m
    calc
      g = k⁻¹ * g' * k := by dsimp only [g']; group
      _ = 1 := by rw [hg'one]; simp

/-- Cardinality of the concrete Suzuki group from its ovoid orbit and point
stabilizer. -/
private theorem suzukiMatrixGroup_card
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    Nat.card (SuzukiMatrixGroup m) =
      ((2 ^ (2 * m + 1)) ^ 2 + 1) *
        (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
  let K := BinaryGaloisField (2 * m + 1)
  let q := 2 ^ (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  let B : Subgroup (GL (Fin 4) K) := F ⊔ H
  have hK_card : Nat.card K = q := by
    simpa [K, q, BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  rcases huppert_blackburn_XI_3_1 m hm pi hpi_sq with
    ⟨_hpi_unique, _hpi_formula, _hF_pgroup, _hF_pow_four,
      _hF_order_four, _hF_class, hF_card, _hF_typeA, _hroot_mul,
      _hcommutator, _hcommutator_coordinates, htorus_equiv,
      _htorus_conjugation, hdisjoint, _hfixed_point_free⟩
  rcases htorus_equiv with ⟨eH, _heH⟩
  have hF_card' : Nat.card F = q ^ 2 := by
    simpa [F, q] using hF_card
  have hH_card : Nat.card H = q - 1 := by
    calc
      Nat.card H = Nat.card Kˣ := Nat.card_congr eH.symm.toEquiv
      _ = Nat.card K - 1 := Nat.card_units K
      _ = q - 1 := by rw [hK_card]
  have hnormal : H ≤ Subgroup.normalizer F :=
    suzukiTorusClosure_le_normalizer_rootClosure
      m pi hpi_sq hpi_formula
  have hB_card : Nat.card B = q ^ 2 * (q - 1) := by
    calc
      Nat.card B = Nat.card F * Nat.card H := by
        exact natCard_sup_eq_mul_of_disjoint_of_le_normalizer
          F H hnormal hdisjoint
      _ = q ^ 2 * (q - 1) := by rw [hF_card', hH_card]
  have hF_le_G : F ≤ SuzukiMatrixGroup m := by
    dsimp only [F]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hH_le_G : H ≤ SuzukiMatrixGroup m := by
    dsimp only [H]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  have hB_le_G : B ≤ SuzukiMatrixGroup m := sup_le hF_le_G hH_le_G
  let U : Subgroup (SuzukiMatrixGroup m) :=
    B.comap (SuzukiMatrixGroup m).subtype
  have hU_card : Nat.card U = q ^ 2 * (q - 1) := by
    calc
      Nat.card U = Nat.card B := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hB_le_G).toEquiv
      _ = q ^ 2 * (q - 1) := hB_card
  let rho : SuzukiMatrixGroup m →*
      LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (SuzukiMatrixGroup m).subtype
  letI : MulAction (SuzukiMatrixGroup m) (ℙ K (Fin 4 → K)) :=
    MulAction.compHom (ℙ K (Fin 4 → K)) rho
  let Omega : SubMulAction (SuzukiMatrixGroup m) (ℙ K (Fin 4 → K)) :=
    { carrier := O
      smul_mem' := by
        intro g z hz
        change (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • z ∈ O
        exact suzukiMatrixGroup_smul_mem_ovoid
          m pi hpi_sq hpi_formula g z hz }
  let pinfO : Omega := ⟨pinf, Or.inl rfl⟩
  have hU_eq_stabilizer :
      U = MulAction.stabilizer (SuzukiMatrixGroup m) pinfO := by
    ext g
    rw [MulAction.mem_stabilizer_iff, ← Subtype.coe_inj]
    change (g : GL (Fin 4) K) ∈ B ↔
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf
    exact (suzukiMatrixGroup_stabilizer_infinity
      m pi hpi_sq hpi_formula g).symm
  have htwo :
      MulAction.IsMultiplyPretransitive (SuzukiMatrixGroup m) Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    have hab' : (a : ℙ K (Fin 4 → K)) ≠ b := by
      intro h
      exact hab (Subtype.ext h)
    have hcd' : (c : ℙ K (Fin 4 → K)) ≠ d := by
      intro h
      exact hcd (Subtype.ext h)
    rcases suzukiOvoid_two_transitive
      m pi hpi_sq hpi_formula (a : ℙ K (Fin 4 → K)) b c d
        a.property b.property c.property d.property hab' hcd' with
      ⟨g, hga, hgb⟩
    exact ⟨g, Subtype.ext hga, Subtype.ext hgb⟩
  have hOmega_card : Nat.card Omega = q ^ 2 + 1 := by
    change Nat.card {z // z ∈ O} = q ^ 2 + 1
    simpa [O, q] using suzukiOvoid_card m pi
  have hU_index : U.index = q ^ 2 + 1 := by
    have hpre : MulAction.IsPretransitive (SuzukiMatrixGroup m) Omega :=
      @MulAction.isPretransitive_of_is_two_pretransitive
        (SuzukiMatrixGroup m) Omega _ _ htwo
    rw [hU_eq_stabilizer]
    exact (@MulAction.index_stabilizer_of_transitive
      (SuzukiMatrixGroup m) Omega _ _ pinfO hpre).trans hOmega_card
  change Nat.card (SuzukiMatrixGroup m) = (q ^ 2 + 1) * q ^ 2 * (q - 1)
  calc
    Nat.card (SuzukiMatrixGroup m) = Nat.card U * U.index :=
      U.card_mul_index.symm
    _ = (q ^ 2 * (q - 1)) * (q ^ 2 + 1) := by
      rw [hU_card, hU_index]
    _ = (q ^ 2 + 1) * q ^ 2 * (q - 1) := by ring

/-- The full projective-linear stabilizer of the Suzuki ovoid is induced by
the concrete Suzuki group. -/
private theorem suzukiOvoid_linear_stabilizer_recognition
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∀ A : GL (Fin 4) K,
      (∀ z, z ∈ O ↔
        (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O) ↔
        ∃ g : SuzukiMatrixGroup m,
          ∀ z : ℙ K (Fin 4 → K),
            (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z =
              (Matrix.GeneralLinearGroup.toLin
                (g : GL (Fin 4) K)).toLinearEquiv • z := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let act : GL (Fin 4) K → ℙ K (Fin 4 → K) → ℙ K (Fin 4 → K) :=
    fun A z => (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z
  change ∀ A : GL (Fin 4) K,
    (∀ z, z ∈ O ↔ act A z ∈ O) ↔
      ∃ g : SuzukiMatrixGroup m, ∀ z : ℙ K (Fin 4 → K),
        act A z = act (g : GL (Fin 4) K) z
  have hact_mul (A B : GL (Fin 4) K) (z : ℙ K (Fin 4 → K)) :
      act (A * B) z = act A (act B z) := by
    dsimp only [act]
    rw [map_mul]
    change ((Matrix.GeneralLinearGroup.toLin A).toLinearEquiv *
      (Matrix.GeneralLinearGroup.toLin B).toLinearEquiv) • z = _
    exact mul_smul _ _ _
  have hact_inv_smul (A : GL (Fin 4) K) (z : ℙ K (Fin 4 → K)) :
      act A⁻¹ (act A z) = z := by
    dsimp only [act]
    rw [map_inv]
    change (Matrix.GeneralLinearGroup.toLin A)⁻¹ •
      (Matrix.GeneralLinearGroup.toLin A • z) = z
    exact inv_smul_smul _ _
  have hgroup_pres (g : SuzukiMatrixGroup m) :
      ∀ z, z ∈ O ↔ act (g : GL (Fin 4) K) z ∈ O := by
    intro z
    constructor
    · exact suzukiMatrixGroup_smul_mem_ovoid
        m pi hpi_sq hpi_formula g z
    · intro hz
      have hback := suzukiMatrixGroup_smul_mem_ovoid
        m pi hpi_sq hpi_formula g⁻¹
          (act (g : GL (Fin 4) K) z) hz
      change act ((g : GL (Fin 4) K)⁻¹)
        (act (g : GL (Fin 4) K) z) ∈ O at hback
      simpa only [hact_inv_smul] using hback
  intro A
  constructor
  · intro hpres
    have hpinfO : pinf ∈ O := Or.inl rfl
    have hpzeroO : p 0 0 ∈ O := Or.inr ⟨(0, 0), rfl⟩
    have hApinfO : act A pinf ∈ O := (hpres pinf).mp hpinfO
    have hApzeroO : act A (p 0 0) ∈ O := (hpres (p 0 0)).mp hpzeroO
    have hpinf_ne_zero : pinf ≠ p 0 0 := by
      intro h
      exact suzukiOvoidInfinity_not_mem_range m pi ⟨(0, 0), h.symm⟩
    have hA_pair_ne : act A pinf ≠ act A (p 0 0) := by
      intro h
      have hsame : pinf = p 0 0 := by
        dsimp only [act] at h
        change Matrix.GeneralLinearGroup.toLin A • pinf =
          Matrix.GeneralLinearGroup.toLin A • p 0 0 at h
        exact smul_left_cancel _ h
      exact hpinf_ne_zero hsame
    rcases suzukiOvoid_two_transitive
      m pi hpi_sq hpi_formula (act A pinf) (act A (p 0 0))
        pinf (p 0 0) hApinfO hApzeroO hpinfO hpzeroO
        hA_pair_ne hpinf_ne_zero with ⟨k, hkinf, hkzero⟩
    let C : GL (Fin 4) K := (k : GL (Fin 4) K) * A
    have hCpres : ∀ z, z ∈ O ↔ act C z ∈ O := by
      intro z
      rw [show act C z = act (k : GL (Fin 4) K) (act A z) by
        exact hact_mul (k : GL (Fin 4) K) A z]
      exact (hpres z).trans (hgroup_pres k (act A z))
    have hCinf : act C pinf = pinf := by
      rw [show act C pinf = act (k : GL (Fin 4) K) (act A pinf) by
        exact hact_mul (k : GL (Fin 4) K) A pinf]
      exact hkinf
    have hCzero : act C (p 0 0) = p 0 0 := by
      rw [show act C (p 0 0) =
          act (k : GL (Fin 4) K) (act A (p 0 0)) by
        exact hact_mul (k : GL (Fin 4) K) A (p 0 0)]
      exact hkzero
    rcases suzukiOvoid_stabilizer_fix_standard_is_torus
      m hm pi hpi_sq hpi_formula C hCpres hCinf hCzero with
      ⟨u, hCu⟩
    let tu : SuzukiMatrixGroup m :=
      ⟨SuzukiTorusGL m u, Subgroup.subset_closure
        (Or.inr (Or.inl ⟨u, rfl⟩))⟩
    refine ⟨k⁻¹ * tu, ?_⟩
    intro z
    calc
      act A z = act ((k : GL (Fin 4) K)⁻¹)
          (act (k : GL (Fin 4) K) (act A z)) :=
        (hact_inv_smul (k : GL (Fin 4) K) (act A z)).symm
      _ = act ((k : GL (Fin 4) K)⁻¹) (act C z) := by
        rw [hact_mul]
      _ = act ((k : GL (Fin 4) K)⁻¹) (act (SuzukiTorusGL m u) z) := by
        exact congrArg (fun w : ℙ K (Fin 4 → K) =>
          act ((k : GL (Fin 4) K)⁻¹) w) (hCu z)
      _ = act (((k : GL (Fin 4) K)⁻¹) * SuzukiTorusGL m u) z := by
        rw [hact_mul]
      _ = act ((k⁻¹ * tu : SuzukiMatrixGroup m) : GL (Fin 4) K) z := rfl
  · rintro ⟨g, hAg⟩
    intro z
    rw [hAg]
    exact hgroup_pres g z

/-- The preservation, faithfulness, two-transitivity, and cardinality parts of
the natural Suzuki ovoid action do not require a positive parameter.  This
separates the small `m = 0` action from the positive-parameter linear
stabilizer recognition used in `huppert_blackburn_XI_3_3`. -/
public theorem suzukiMatrixGroup_ovoid_action_data
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    (∀ g : SuzukiMatrixGroup m, ∀ z, z ∈ O →
      ((Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • z) ∈ O) ∧
    (∀ g : SuzukiMatrixGroup m,
      (∀ z, z ∈ O →
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • z = z) → g = 1) ∧
    (∀ a b c d, a ∈ O → b ∈ O → c ∈ O → d ∈ O →
      a ≠ b → c ≠ d →
      ∃ g : SuzukiMatrixGroup m,
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • a = c ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • b = d) ∧
    Nat.card {z // z ∈ O} = (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  change
    (∀ g : SuzukiMatrixGroup m, ∀ z, z ∈ O →
      ((Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • z) ∈ O) ∧
    (∀ g : SuzukiMatrixGroup m,
      (∀ z, z ∈ O →
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • z = z) → g = 1) ∧
    (∀ a b c d, a ∈ O → b ∈ O → c ∈ O → d ∈ O →
      a ≠ b → c ≠ d →
      ∃ g : SuzukiMatrixGroup m,
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • a = c ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • b = d) ∧
    Nat.card {z // z ∈ O} = (2 ^ (2 * m + 1)) ^ 2 + 1
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 :=
    binaryGaloisField_tits_formula_sq m pi hpi
  exact ⟨suzukiMatrixGroup_smul_mem_ovoid m pi hpi_sq hpi,
    suzukiMatrixGroup_faithful_on_ovoid m pi,
    suzukiOvoid_two_transitive m pi hpi_sq hpi,
    suzukiOvoid_card m pi⟩

/-- Huppert-Blackburn XI.3.3: the natural Suzuki ovoid action. -/
public theorem huppert_blackburn_XI_3_3
    (m : ℕ) (hm : 0 < m)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    let F : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
    let H : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
    (∀ g : SuzukiMatrixGroup m, ∀ z, z ∈ O →
      ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K)).toLinearEquiv • z) ∈ O) ∧
    (∀ A : GL (Fin 4) K,
      (∀ z, z ∈ O ↔ (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O) ↔
        ∃ g : SuzukiMatrixGroup m,
          ∀ z : ℙ K (Fin 4 → K),
            (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z =
            (Matrix.GeneralLinearGroup.toLin
              (g : GL (Fin 4) K)).toLinearEquiv • z) ∧
    (∀ g : SuzukiMatrixGroup m,
      (∀ z, z ∈ O →
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • z = z) → g = 1) ∧
    (∀ a b c d, a ∈ O → b ∈ O → c ∈ O → d ∈ O →
      a ≠ b → c ≠ d →
      ∃ g : SuzukiMatrixGroup m,
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • a = c ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • b = d) ∧
    (∀ g : SuzukiMatrixGroup m,
      (∃ a b c, a ∈ O ∧ b ∈ O ∧ c ∈ O ∧
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • a = a ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • b = b ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • c = c) → g = 1) ∧
    Nat.card {z // z ∈ O} = (2 ^ (2 * m + 1)) ^ 2 + 1 ∧
    Nat.card (SuzukiMatrixGroup m) =
      ((2 ^ (2 * m + 1)) ^ 2 + 1) *
        (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) ∧
    (∀ g : SuzukiMatrixGroup m,
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf ↔
        (g : GL (Fin 4) K) ∈ F ⊔ H) := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  change
    (∀ g : SuzukiMatrixGroup m, ∀ z, z ∈ O →
      ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K)).toLinearEquiv • z) ∈ O) ∧
    (∀ A : GL (Fin 4) K,
      (∀ z, z ∈ O ↔ (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O) ↔
        ∃ g : SuzukiMatrixGroup m,
          ∀ z : ℙ K (Fin 4 → K),
            (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z =
            (Matrix.GeneralLinearGroup.toLin
              (g : GL (Fin 4) K)).toLinearEquiv • z) ∧
    (∀ g : SuzukiMatrixGroup m,
      (∀ z, z ∈ O →
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • z = z) → g = 1) ∧
    (∀ a b c d, a ∈ O → b ∈ O → c ∈ O → d ∈ O →
      a ≠ b → c ≠ d →
      ∃ g : SuzukiMatrixGroup m,
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • a = c ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • b = d) ∧
    (∀ g : SuzukiMatrixGroup m,
      (∃ a b c, a ∈ O ∧ b ∈ O ∧ c ∈ O ∧
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • a = a ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • b = b ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • c = c) → g = 1) ∧
    Nat.card {z // z ∈ O} = (2 ^ (2 * m + 1)) ^ 2 + 1 ∧
    Nat.card (SuzukiMatrixGroup m) =
      ((2 ^ (2 * m + 1)) ^ 2 + 1) *
        (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) ∧
    (∀ g : SuzukiMatrixGroup m,
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf ↔
        (g : GL (Fin 4) K) ∈ F ⊔ H)
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 := by
    exact binaryGaloisField_tits_formula_sq m pi hpi
  have h_action := by
    exact suzukiMatrixGroup_smul_mem_ovoid m pi hpi_sq hpi
  have h_recognition :
      ∀ A : GL (Fin 4) K,
        (∀ z, z ∈ O ↔
          (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O) ↔
          ∃ g : SuzukiMatrixGroup m,
            ∀ z : ℙ K (Fin 4 → K),
              (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z =
              (Matrix.GeneralLinearGroup.toLin
                (g : GL (Fin 4) K)).toLinearEquiv • z := by
    exact suzukiOvoid_linear_stabilizer_recognition
      m hm pi hpi_sq hpi
  have h_faithful :
      ∀ g : SuzukiMatrixGroup m,
        (∀ z, z ∈ O →
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv • z = z) → g = 1 := by
    exact suzukiMatrixGroup_faithful_on_ovoid m pi
  have h_two_transitive :
      ∀ a b c d, a ∈ O → b ∈ O → c ∈ O → d ∈ O →
        a ≠ b → c ≠ d →
        ∃ g : SuzukiMatrixGroup m,
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv • a = c ∧
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv • b = d := by
    exact suzukiOvoid_two_transitive m pi hpi_sq hpi
  have h_three_point_free :
      ∀ g : SuzukiMatrixGroup m,
        (∃ a b c, a ∈ O ∧ b ∈ O ∧ c ∈ O ∧
          a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv • a = a ∧
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv • b = b ∧
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv • c = c) → g = 1 := by
    exact suzukiMatrixGroup_three_point_free m pi hpi_sq hpi
  have h_card :
      Nat.card {z // z ∈ O} = (2 ^ (2 * m + 1)) ^ 2 + 1 := by
    exact suzukiOvoid_card m pi
  have h_order :
      Nat.card (SuzukiMatrixGroup m) =
        ((2 ^ (2 * m + 1)) ^ 2 + 1) *
          (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
    exact suzukiMatrixGroup_card m hm pi hpi_sq hpi
  have h_stabilizer :
      ∀ g : SuzukiMatrixGroup m,
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf ↔
          (g : GL (Fin 4) K) ∈ F ⊔ H := by
    exact suzukiMatrixGroup_stabilizer_infinity m pi hpi_sq hpi
  exact ⟨h_action, h_recognition, h_faithful, h_two_transitive,
    h_three_point_free, h_card, h_order, h_stabilizer⟩

end External
end CFSG.BenderSuzuki
