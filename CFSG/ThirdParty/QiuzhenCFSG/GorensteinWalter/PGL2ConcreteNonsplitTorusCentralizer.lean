module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NonsplitTorusFieldFixed
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TorusCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.Algebra.Field.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
import Mathlib.Tactic
import Mathlib.Tactic.Group

namespace CFSG
end CFSG
open CFSG

/-!
# The concrete nonsplit torus of `PGL₂(K)` and its dihedral normalizer

The matrices `!![a, b * lam; b, a]` with `lam` a nonsquare in the finite
field `K` form a cyclic nonsplit projective torus of order `|K| + 1`.
This module produces the canonical involution `s` (the image of
`!![0, lam; 1, 0]`) and the reflector `w` (the image of `!![1, 0; 0, -1]`),
with `s ∈ U`, `IsInvolution s`, `w * w = 1`, `w ∉ U`, `w` inverting `U`
by conjugation, and the centralizer of `s` being the dihedral group
`U ⊔ ⟨w⟩`.  The torus `U` is the *concrete* matrix torus
`pgl2ConcreteNonsplitTorus K lam`, whose carrier is the same
`∃ A a b, x = mk A ∧ ↑A = !![a, b * lam; b, a]` predicate as the
`pGammaL2NonsplitTorus` of the fixed-field module (that definition's
body is not exported because it mentions a private helper, so the
concrete copy is used here and the two become definitionally equal
once the private helper is made public).
-/

open scoped Pointwise MatrixGroups

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open Polynomial

universe u

private lemma two_ne_zero_of_odd_card (K : Type u) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  intro h2
  let : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd_char : ringChar K ∣ 2 := (CharP.cast_eq_zero_iff K (ringChar K) 2).mp h2
  have hchar2 : ringChar K = 2 := by
    rcases hdvd_char with ⟨c, hc⟩
    cases c with
    | zero => norm_num at hc
    | succ c =>
        cases c with
        | zero => omega
        | succ c =>
            exfalso
            have hrc_pos : 0 < ringChar K := by
              by_contra h
              have hz : ringChar K = 0 := by omega
              rw [hz] at hc
              norm_num at hc
            have hrc_le : ringChar K ≤ 1 := by nlinarith
            have hrc1 : ringChar K = 1 := by omega
            have hsub : Subsingleton K := (ringChar.ringChar_eq_one (R := K)).mp hrc1
            exact not_subsingleton K hsub
  have hdvd_card : 2 ∣ Fintype.card K :=
    (prime_dvd_char_iff_dvd_card (R := K) (p := 2)).mp (by simpa [hchar2])
  have hprime_dvd : (2 : ℕ) ∣ Nat.card K := by
    simpa [Nat.card_eq_fintype_card] using hdvd_card
  exact hodd.not_two_dvd_nat hprime_dvd

private lemma quad_ne_zero (K : Type u) [Field K] (lam : K) :
    (X ^ 2 - C lam : K[X]) ≠ 0 := by
  intro h
  have hcoeff : (X ^ 2 - C lam).coeff 2 = (0 : K[X]).coeff 2 :=
    congrArg (fun p : K[X] => p.coeff 2) h
  simp at hcoeff

private lemma quad_natDegree (K : Type u) [Field K] (lam : K) :
    (X ^ 2 - C lam : K[X]).natDegree = 2 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_X_pow_sub_C]
  · simp

private lemma emb_det (K : Type u) [Field K] (lam a b : K) :
    (!![a, b * lam; b, a] : Matrix (Fin 2) (Fin 2) K).det =
      a ^ 2 - b ^ 2 * lam := by
  simp [Matrix.det_fin_two, pow_two, mul_comm, mul_left_comm, mul_assoc]

private lemma emb_mul (K : Type u) [Field K] (lam a b c d : K) :
    (!![a, b * lam; b, a] : Matrix (Fin 2) (Fin 2) K) *
      !![c, d * lam; d, c] =
    !![a * c + b * d * lam, (a * d + b * c) * lam;
      a * d + b * c, a * c + b * d * lam] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma emb_diag_conj (K : Type u) [Field K] (lam a b : K) :
    (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) K) *
      !![a, b * lam; b, a] * !![1, 0; 0, -1] =
    !![a, -(b * lam); -b, a] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The concrete standard nonsplit torus of `PGL₂(K)`: the projective image
of the invertible matrices `!![a, b * lam; b, a]`.  Its carrier is the same
predicate as `pGammaL2NonsplitTorus K lam`; this definition is written with
the literal matrix so that its body is exported to other modules. -/
@[expose]
public def pgl2ConcreteNonsplitTorus (K : Type u) [Field K] (lam : K) :
    Subgroup (PGL2 K) where
  carrier := {x : PGL2 K | ∃ (A : GL (Fin 2) K) (a b : K),
    x = Matrix.ProjGenLinGroup.mk A ∧
      (A : Matrix (Fin 2) (Fin 2) K) = !![a, b * lam; b, a]}
  one_mem' := by
    refine ⟨1, 1, 0, ?_, ?_⟩
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  mul_mem' := by
    intro x y hx hy
    rcases hx with ⟨A, a, b, hx, hA⟩
    rcases hy with ⟨B, c, d, hy, hB⟩
    refine ⟨A * B, a * c + b * d * lam, a * d + b * c, ?_, ?_⟩
    · rw [hx, hy]
      simp
    · change (A : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K) =
          !![a * c + b * d * lam, (a * d + b * c) * lam;
            a * d + b * c, a * c + b * d * lam]
      rw [hA, hB]
      exact emb_mul K lam a b c d
  inv_mem' := by
    intro x hx
    rcases hx with ⟨A, a, b, hx, hA⟩
    let d := a ^ 2 - b ^ 2 * lam
    have hd : d ≠ 0 := by
      have hAdet : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := A.det_ne_zero
      rw [hA] at hAdet
      simpa [d, Matrix.det_fin_two, pow_two, mul_comm, mul_left_comm,
        mul_assoc] using hAdet
    refine ⟨A⁻¹, a / d, -b / d, ?_, ?_⟩
    · rw [hx]
      simp
    · have hmul : (A : Matrix (Fin 2) (Fin 2) K) *
          !![a / d, (-b / d) * lam; -b / d, a / d] = 1 := by
        rw [hA]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, d]
        all_goals field_simp [d, hd] <;> ring
      exact (by
        simpa using Matrix.inv_eq_right_inv (A := (A : Matrix (Fin 2) (Fin 2) K))
          (B := !![a / d, (-b / d) * lam; -b / d, a / d]) hmul)

/-- The concrete matrix torus is the same subgroup as the semilinear
fixed-field module's standard nonsplit torus. -/
public theorem pgl2ConcreteNonsplitTorus_eq_pGammaL2NonsplitTorus
    (K : Type u) [Field K] (lam : K) :
    pgl2ConcreteNonsplitTorus K lam = pGammaL2NonsplitTorus K lam := by
  ext x
  change (∃ (A : GL (Fin 2) K) (a b : K),
      x = Matrix.ProjGenLinGroup.mk A ∧
        (A : Matrix (Fin 2) (Fin 2) K) = !![a, b * lam; b, a]) ↔
    x ∈ pGammaL2NonsplitTorus K lam
  exact mem_pGammaL2NonsplitTorus_iff.symm

set_option maxHeartbeats 8000000 in
/-- The standard nonsplit torus involution has dihedral normalizer: its
centralizer is `U ⊔ ⟨w⟩`, where `U` is the concrete nonsplit torus
`pgl2ConcreteNonsplitTorus K lam`. -/
public theorem pgl2_concrete_nonsplit_torus_centralizer_data
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (lam : K) (hlamNS : ¬ IsSquare lam) :
    ∃ s w : PGL2 K,
      IsCyclic (pgl2ConcreteNonsplitTorus K lam) ∧
      Nat.card (pgl2ConcreteNonsplitTorus K lam) = Nat.card K + 1 ∧
      s ∈ pgl2ConcreteNonsplitTorus K lam ∧
      IsInvolution s ∧
      w * w = 1 ∧
      w ∉ pgl2ConcreteNonsplitTorus K lam ∧
      (∀ x : PGL2 K, x ∈ pgl2ConcreteNonsplitTorus K lam → w * x * w⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({s} : Set (PGL2 K)) =
        pgl2ConcreteNonsplitTorus K lam ⊔ Subgroup.zpowers w ∧
      Nat.card ↥(pgl2ConcreteNonsplitTorus K lam ⊔ Subgroup.zpowers w) =
        2 * Nat.card (pgl2ConcreteNonsplitTorus K lam) ∧
      (¬ pgl2ConcreteNonsplitTorus K lam ≤
          (Matrix.ProjectiveSpecialLinearGroup.toPGL
            (n := Fin 2) (R := K)).range) ∧
      ¬ pgl2ConcreteNonsplitTorus K lam ≤ commutator (PGL2 K) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  rcases hK with ⟨p, n, hp, hpodd, hn, hKcard⟩
  have hodd : Odd (Nat.card K) := by
    rw [hKcard]
    exact hpodd.pow
  have hlam0 : lam ≠ 0 := by
    intro h
    subst h
    exact hlamNS IsSquare.zero
  have : Fact (Irreducible (X ^ 2 - C lam : K[X])) := ⟨
    (X_pow_sub_C_irreducible_iff_of_prime (K := K) Nat.prime_two).2 (by
      intro b hb
      exact hlamNS ⟨b, by simpa [pow_two] using hb.symm⟩)⟩
  let f : K[X] := X ^ 2 - C lam
  let E : Type u := AdjoinRoot f
  let : Field E := inferInstance
  let ρ : E := AdjoinRoot.root f
  have hρ2 : ρ ^ 2 = algebraMap K E lam := by
    change ρ ^ 2 = algebraMap K (AdjoinRoot f) lam
    have h := root_X_pow_sub_C_pow (K := K) 2 lam
    simpa [ρ, f, AdjoinRoot.algebraMap_eq] using h
  have hρ_ne_zero : ρ ≠ 0 := by
    have h := root_X_pow_sub_C_ne_zero' (K := K) (n := 2) (a := lam)
      (by norm_num) hlam0
    simpa [ρ, f] using h
  let pb : PowerBasis K E :=
    AdjoinRoot.powerBasis (K := K) (f := f) (quad_ne_zero K lam)
  let b2 : Module.Basis (Fin 2) K E :=
    pb.basis.reindex (finCongr (quad_natDegree K lam))
  have hb0 : (b2 (0 : Fin 2) : E) = 1 := by
    rw [Module.Basis.reindex_apply]
    rw [pb.basis_eq_pow]
    change ρ ^ ((finCongr (quad_natDegree K lam)).symm (0 : Fin 2) : ℕ) = 1
    have hidx : ((finCongr (quad_natDegree K lam)).symm (0 : Fin 2) : ℕ) = 0 := by
      rfl
    rw [hidx]
    simp
  have hb1 : (b2 (1 : Fin 2) : E) = ρ := by
    rw [Module.Basis.reindex_apply]
    rw [pb.basis_eq_pow]
    change ρ ^ ((finCongr (quad_natDegree K lam)).symm (1 : Fin 2) : ℕ) = ρ
    have hidx : ((finCongr (quad_natDegree K lam)).symm (1 : Fin 2) : ℕ) = 1 := by
      rfl
    rw [hidx]
    simp [ρ]
  have hrepr1_0 : b2.repr (1 : E) (0 : Fin 2) = 1 := by
    rw [← hb0]
    simp
  have hrepr1_1 : b2.repr (1 : E) (1 : Fin 2) = 0 := by
    rw [← hb0]
    simp
  have hreprρ_0 : b2.repr ρ (0 : Fin 2) = 0 := by
    rw [← hb1]
    simp
  have hreprρ_1 : b2.repr ρ (1 : Fin 2) = 1 := by
    rw [← hb1]
    simp
  have hrepr_algebraMap0 (a : K) : b2.repr (algebraMap K E a) (0 : Fin 2) = a := by
    rw [Algebra.algebraMap_eq_smul_one, ← hb0]
    simp
  have hrepr_algebraMap1 (a : K) : b2.repr (algebraMap K E a) (1 : Fin 2) = 0 := by
    rw [Algebra.algebraMap_eq_smul_one, ← hb0]
    simp
  let M : Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix b2 ρ
  have hM00 : M 0 0 = 0 := by
    dsimp [M]
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, ← hb1]
    simp
  have hM01 : M 0 1 = lam := by
    dsimp [M]
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb1, ← pow_two, hρ2]
    rw [Algebra.algebraMap_eq_smul_one, ← hb0]
    simp
  have hM10 : M 1 0 = 1 := by
    dsimp [M]
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, ← hb1]
    simp
  have hM11 : M 1 1 = 0 := by
    dsimp [M]
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb1, ← pow_two, hρ2]
    rw [Algebra.algebraMap_eq_smul_one, ← hb0]
    simp
  -- coordinates and multiplication table of E = K[ρ]
  let coord (x : E) : K × K := (b2.repr x 0, b2.repr x 1)
  have hcoord_add (x y : E) :
      coord (x + y) = ((coord x).1 + (coord y).1, (coord x).2 + (coord y).2) := by
    ext <;> simp [coord, map_add]
  have hx_basis (x : E) : x = (b2.repr x 0) • (1 : E) + (b2.repr x 1) • ρ := by
    calc
      x = ∑ i : Fin 2, b2.repr x i • b2 i := (Module.Basis.sum_repr b2 x).symm
      _ = (b2.repr x 0) • (1 : E) + (b2.repr x 1) • ρ := by
        rw [Fin.sum_univ_two]
        simp only [hb0, hb1]
  have hlm (x : E) : Algebra.leftMulMatrix b2 x =
      !![(coord x).1, (coord x).2 * lam; (coord x).2, (coord x).1] := by
    have h00 : (Algebra.leftMulMatrix b2 x) (0 : Fin 2) (0 : Fin 2) =
        (coord x).1 := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hb0]
      simp [coord, hb0]
    have h01 : (Algebra.leftMulMatrix b2 x) (0 : Fin 2) (1 : Fin 2) =
        (coord x).2 * lam := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hb1]
      conv_lhs => rw [hx_basis x]
      rw [add_mul, smul_mul_assoc, smul_mul_assoc]
      have h1ρ : (1 : E) * ρ = ρ := one_mul ρ
      have hρlam : ρ * ρ = algebraMap K E lam := by simpa [pow_two] using hρ2
      rw [h1ρ, hρlam]
      rw [map_add, map_smul, map_smul]
      simp [hreprρ_0, hrepr_algebraMap0, coord, mul_comm, mul_left_comm, mul_assoc]
    have h10 : (Algebra.leftMulMatrix b2 x) (1 : Fin 2) (0 : Fin 2) =
        (coord x).2 := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hb0]
      simp [coord, hb0]
    have h11 : (Algebra.leftMulMatrix b2 x) (1 : Fin 2) (1 : Fin 2) =
        (coord x).1 := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, hb1]
      calc
        b2.repr (x * ρ) 1 = b2.repr
            (((b2.repr x 0) • (1 : E) + (b2.repr x 1) • ρ) * ρ) 1 := by
              exact congrArg (fun z : E => b2.repr (z * ρ) 1) (hx_basis x)
        _ = (b2.repr x 0) := by
          rw [add_mul, smul_mul_assoc, smul_mul_assoc]
          have h1ρ : (1 : E) * ρ = ρ := one_mul ρ
          have hρlam : ρ * ρ = algebraMap K E lam := by simpa [pow_two] using hρ2
          rw [h1ρ, hρlam]
          rw [map_add, map_smul, map_smul]
          simp [hreprρ_1, hrepr_algebraMap1]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  -- torus map from E units
  let emb (a b : K) : Matrix (Fin 2) (Fin 2) K := !![a, b * lam; b, a]
  have hcoord_one : coord (1 : E) = (1, 0) := by
    rw [← hb0]
    simp [coord]
  have hcoord_mul (x y : E) :
      coord (x * y) =
        ((coord x).1 * (coord y).1 + (coord x).2 * (coord y).2 * lam,
         (coord x).1 * (coord y).2 + (coord x).2 * (coord y).1) := by
    have hmv : b2.repr (x * y) = Algebra.leftMulMatrix b2 x *ᵥ b2.repr y :=
      (Algebra.leftMulMatrix_mulVec_repr b2 x y).symm
    rw [hlm x] at hmv
    ext
    · change b2.repr (x * y) 0 =
        (coord x).1 * (coord y).1 + (coord x).2 * (coord y).2 * lam
      rw [hmv]
      simp [coord, Matrix.mulVec, Fin.sum_univ_two, vecHead, vecTail,
        mul_comm, mul_left_comm, mul_assoc] <;> ring
    · change b2.repr (x * y) 1 =
        (coord x).1 * (coord y).2 + (coord x).2 * (coord y).1
      rw [hmv]
      simp [coord, Matrix.mulVec, Fin.sum_univ_two, vecHead, vecTail,
        mul_comm, mul_left_comm, mul_assoc] <;> ring
  have hnorm_ne (x : E) (hx0 : x ≠ 0) : Algebra.norm K x ≠ 0 :=
    (Algebra.norm_ne_zero_iff_of_basis b2).mpr hx0
  have hdet_ne (x : Eˣ) :
      (emb (b2.repr (x : E) 0) (b2.repr (x : E) 1)).det ≠ 0 := by
    have hlmx : Algebra.leftMulMatrix b2 (x : E) =
        emb (b2.repr (x : E) 0) (b2.repr (x : E) 1) := by
      rw [hlm (x : E)]
    rw [← hlmx, ← Algebra.norm_eq_matrix_det b2 (x : E)]
    exact hnorm_ne (x : E) x.ne_zero
  let mulGL (x : Eˣ) : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      (emb (b2.repr (x : E) 0) (b2.repr (x : E) 1)) (hdet_ne x)
  let mulHom : Eˣ →* GL (Fin 2) K :=
    { toFun := mulGL
      map_one' := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        have hrepr0 : b2.repr (1 : E) 0 = 1 := by
          simpa [coord] using (congrArg Prod.fst hcoord_one)
        have hrepr1 : b2.repr (1 : E) 1 = 0 := by
          simpa [coord] using (congrArg Prod.snd hcoord_one)
        fin_cases i <;> fin_cases j <;>
          simp [mulGL, emb, hrepr0, hrepr1]
      map_mul' := by
        intro x y
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        have hrepr0 : b2.repr ((x : E) * y) 0 =
            (b2.repr (x : E) 0) * (b2.repr (y : E) 0) +
              (b2.repr (x : E) 1) * (b2.repr (y : E) 1) * lam := by
          have h := congrArg Prod.fst (hcoord_mul (x : E) (y : E))
          simpa [coord] using h
        have hrepr1 : b2.repr ((x : E) * y) 1 =
            (b2.repr (x : E) 0) * (b2.repr (y : E) 1) +
              (b2.repr (x : E) 1) * (b2.repr (y : E) 0) := by
          have h := congrArg Prod.snd (hcoord_mul (x : E) (y : E))
          simpa [coord] using h
        fin_cases i <;> fin_cases j <;>
          simp [mulGL, emb, hrepr0, hrepr1, emb_mul] <;> ring }
  let torus : Eˣ →* PGL2 K := Matrix.ProjGenLinGroup.mk.comp mulHom
  let U : Subgroup (PGL2 K) := torus.range
  let : Fintype E := Fintype.ofEquiv (Fin 2 → K) b2.equivFun.toEquiv.symm
  let : Finite E := inferInstance
  have hUcyclic : IsCyclic U := by
    exact isCyclic_of_surjective torus.rangeRestrict
      torus.rangeRestrict_surjective
  have hcoord_algebraMap (a : K) : coord (algebraMap K E a) = (a, 0) := by
    rw [Algebra.algebraMap_eq_smul_one, ← hb0]
    simp [coord]
  have hmem_scalar (x : E) (hx : ∃ a : Kˣ,
      Algebra.leftMulMatrix b2 x =
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a : Matrix (Fin 2) (Fin 2) K)) :
      x ∈ (algebraMap K E).range := by
    rcases hx with ⟨a, ha⟩
    have heq := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) ha
    have hlm01 : (Algebra.leftMulMatrix b2 x) (0 : Fin 2) (1 : Fin 2) =
        (b2.repr x 1) * lam := by
      exact congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) (hlm x)
    rw [hlm01] at heq
    simp [emb, Matrix.GeneralLinearGroup.scalar] at heq
    have hcoord1 : (b2.repr x 1) = 0 := heq.resolve_right hlam0
    refine ⟨b2.repr x 0, ?_⟩
    conv_rhs => rw [hx_basis x]
    simp [hcoord1, Algebra.algebraMap_eq_smul_one, hrepr1_0, hrepr1_1]
  have hscalar_inj : Function.Injective
      (Units.map (algebraMap K E).toMonoidHom) := by
    intro a b hab
    apply Units.ext
    have hE : (algebraMap K E (a : K)) = algebraMap K E (b : K) :=
      congrArg (fun z : Eˣ => (z : E)) hab
    have ha : b2.repr (algebraMap K E (a : K)) (0 : Fin 2) = (a : K) := by
      rw [Algebra.algebraMap_eq_smul_one, ← hb0]
      simp
    have hb : b2.repr (algebraMap K E (b : K)) (0 : Fin 2) = (b : K) := by
      rw [Algebra.algebraMap_eq_smul_one, ← hb0]
      simp
    simpa [ha, hb] using congrArg (fun z : E => b2.repr z (0 : Fin 2)) hE
  have hker : torus.ker = (Units.map (algebraMap K E).toMonoidHom).range := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro hx
      have hmk : Matrix.ProjGenLinGroup.mk (mulGL x) = 1 := by
        simpa [torus, mulHom] using hx
      have hsc : mulGL x ∈ Subgroup.center (GL (Fin 2) K) := by
        simpa [Matrix.ProjGenLinGroup.mk_eq_one] using hmk
      have hsc_range : mulGL x ∈ (Matrix.GeneralLinearGroup.scalar (Fin 2)).range := by
        rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar (n := Fin 2) (R := K)]
        exact hsc
      rcases hsc_range with ⟨a, ha⟩
      have hlmx : Algebra.leftMulMatrix b2 (x : E) =
          (Matrix.GeneralLinearGroup.scalar (Fin 2) a : Matrix (Fin 2) (Fin 2) K) := by
        rw [hlm (x : E)]
        simp [ha, mulGL, emb, coord]
      have hxr : (x : E) ∈ (algebraMap K E).range := hmem_scalar (x : E) ⟨a, hlmx⟩
      rcases hxr with ⟨b, hb⟩
      have hb_ne : b ≠ 0 := by
        intro hb0
        have hx0 : (x : E) = 0 := by simpa [hb0] using hb.symm
        exact x.ne_zero hx0
      refine ⟨Units.mk0 b hb_ne, ?_⟩
      apply Units.ext
      exact hb
    · intro hx
      rcases hx with ⟨a, rfl⟩
      change Matrix.ProjGenLinGroup.mk (mulGL (Units.map (algebraMap K E).toMonoidHom a)) = 1
      rw [Matrix.ProjGenLinGroup.mk_eq_one]
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      refine ⟨a, ?_⟩
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [mulGL, emb, hrepr_algebraMap0, hrepr_algebraMap1]
  have hker_card : Nat.card torus.ker = Nat.card K - 1 := by
    rw [hker]
    calc
      Nat.card (Units.map (algebraMap K E).toMonoidHom).range = Nat.card Kˣ :=
        (Nat.card_congr (Equiv.ofInjective
          (Units.map (algebraMap K E).toMonoidHom) hscalar_inj)).symm
      _ = Nat.card K - 1 := by
        simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
  have hE_card : Nat.card E = Nat.card K ^ 2 := by
    calc
      Nat.card E = Nat.card (Fin 2 → K) := Nat.card_congr b2.equivFun.toEquiv
      _ = Nat.card K ^ 2 := by
        rw [Nat.card_fun]
        simp
  have hunits : Nat.card Eˣ = Nat.card E - 1 := by
    simpa [Nat.card_eq_fintype_card] using Fintype.card_units E
  have hq_factor : (Nat.card K - 1) * (Nat.card K + 1) = Nat.card K ^ 2 - 1 := by
    simpa [mul_comm] using (Nat.pow_two_sub_pow_two (Nat.card K) 1).symm
  have hrange_card : Nat.card U = Nat.card K + 1 := by
    have hmul := torus.ker.index_mul_card
    rw [Subgroup.index_ker torus, hker_card] at hmul
    rw [hunits, hE_card] at hmul
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := K)))
    calc
      Nat.card U * (Nat.card K - 1) = Nat.card K ^ 2 - 1 := hmul
      _ = (Nat.card K + 1) * (Nat.card K - 1) := by
        rw [← hq_factor]
        ac_rfl
  let u0 : Eˣ := Units.mk0 ρ hρ_ne_zero
  let s : PGL2 K := torus u0
  have hsU : s ∈ U := ⟨u0, rfl⟩
  have hssq : s * s = 1 := by
    change torus u0 * torus u0 = 1
    rw [← map_mul]
    have huusq : (u0 * u0 : Eˣ) = Units.mk0 (algebraMap K E lam) (by
        intro h
        have hlam' : lam = 0 :=
          (FaithfulSMul.algebraMap_eq_zero_iff (R := K) (A := E)).mp h
        exact hlam0 hlam') := by
      apply Units.ext
      change (ρ : E) * ρ = algebraMap K E lam
      simpa [u0, pow_two] using hρ2
    rw [huusq]
    change Matrix.ProjGenLinGroup.mk (mulGL (Units.mk0 (algebraMap K E lam) _)) = 1
    rw [Matrix.ProjGenLinGroup.mk_eq_one]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨Units.mk0 lam hlam0, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [mulGL, emb, hrepr_algebraMap0, hrepr_algebraMap1]
  have hsne : s ≠ 1 := by
    intro h
    have hmk : Matrix.ProjGenLinGroup.mk (mulGL u0) = 1 := by
      simpa [s, torus, mulHom] using h
    have hsc : mulGL u0 ∈ Subgroup.center (GL (Fin 2) K) := by
      simpa [Matrix.ProjGenLinGroup.mk_eq_one] using hmk
    have hsc_range : mulGL u0 ∈ (Matrix.GeneralLinearGroup.scalar (Fin 2)).range := by
      rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar (n := Fin 2) (R := K)]
      exact hsc
    rcases hsc_range with ⟨a, ha⟩
    have heq := congrArg (fun M : GL (Fin 2) K =>
      ((M : Matrix (Fin 2) (Fin 2) K) 0 1)) ha
    have hM01' : (mulGL u0 : Matrix (Fin 2) (Fin 2) K) 0 1 = lam := by
      have hcoordρ : coord ρ = (0, 1) := by
        rw [← hb1]
        simp [coord]
      simp [u0, mulGL, emb, hcoordρ, coord, hreprρ_1]
    rw [hM01'] at heq
    simp [Matrix.GeneralLinearGroup.scalar] at heq
    exact hlam0 heq.symm
  let wGL : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, -1] (by
      simp [Matrix.det_fin_two])
  let w : PGL2 K := Matrix.ProjGenLinGroup.mk wGL
  have hw_sq : w * w = 1 := by
    change Matrix.ProjGenLinGroup.mk wGL * Matrix.ProjGenLinGroup.mk wGL = 1
    rw [← map_mul]
    have hmat : wGL * wGL = 1 := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [wGL, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hmat, map_one]
  have hw_inv : w⁻¹ = w := (eq_inv_of_mul_eq_one_right hw_sq).symm
  have hw_ne_one : w ≠ 1 := by
    intro h
    have hmk : Matrix.ProjGenLinGroup.mk wGL = 1 := by simpa [w] using h
    have hsc : wGL ∈ Subgroup.center (GL (Fin 2) K) := by
      simpa [Matrix.ProjGenLinGroup.mk_eq_one] using hmk
    have hsc_range : wGL ∈ (Matrix.GeneralLinearGroup.scalar (Fin 2)).range := by
      rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar (n := Fin 2) (R := K)]
      exact hsc
    rcases hsc_range with ⟨a, ha⟩
    have h00 := congrArg (fun M : GL (Fin 2) K =>
      ((M : Matrix (Fin 2) (Fin 2) K) 0 0)) ha
    have h11 := congrArg (fun M : GL (Fin 2) K =>
      ((M : Matrix (Fin 2) (Fin 2) K) 1 1)) ha
    simp [wGL, Matrix.GeneralLinearGroup.scalar] at h00 h11
    have h2 : (2 : K) = 0 := by
      have h12 : (1 : K) = -1 := by
        simpa using congrArg (fun z : Kˣ => (z : K)) (h00.symm.trans h11)
      calc
        (2 : K) = (1 : K) + 1 := by norm_num
        _ = -1 + 1 := by nth_rw 1 [h12]
        _ = 0 := by simp
    exact two_ne_zero_of_odd_card K hodd h2
  have hw_not_mem : w ∉ U := by
    intro hw
    rcases hw with ⟨x, hx⟩
    have hmk : Matrix.ProjGenLinGroup.mk wGL =
        Matrix.ProjGenLinGroup.mk (mulGL x) := by
      simpa [w, torus, mulHom] using hx.symm
    rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hmk with ⟨a, ha⟩
    have h01' : (mulGL x : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
      rw [← ha]
      simp [wGL, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
    have hlm01x : (mulGL x : Matrix (Fin 2) (Fin 2) K) 0 1 =
        (b2.repr (x : E) 1) * lam := by
      simp [mulGL, emb]
    rw [hlm01x] at h01'
    have hcoord1 : (b2.repr (x : E) 1) = 0 :=
      (mul_eq_zero.mp h01').resolve_right hlam0
    have hxsc : (x : E) ∈ (algebraMap K E).range :=
      ⟨b2.repr (x : E) 0, by
        conv_rhs => rw [hx_basis (x : E)]
        simp [hcoord1, Algebra.algebraMap_eq_smul_one, hrepr1_0, hrepr1_1]⟩
    rcases hxsc with ⟨b, hb⟩
    have hb_ne : b ≠ 0 := by
      intro hb0
      have hx0 : (x : E) = 0 := by simpa [hb0] using hb.symm
      exact x.ne_zero hx0
    have hb_ne_E : (algebraMap K E) b ≠ 0 :=
      (FaithfulSMul.algebraMap_eq_zero_iff (R := K) (A := E)).not.mpr hb_ne
    have htorus_scalar : torus (Units.mk0 (algebraMap K E b) hb_ne_E) = 1 := by
      change Matrix.ProjGenLinGroup.mk (mulGL (Units.mk0 (algebraMap K E b) hb_ne_E)) = 1
      rw [Matrix.ProjGenLinGroup.mk_eq_one]
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      refine ⟨Units.mk0 b hb_ne, ?_⟩
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [mulGL, emb, hrepr_algebraMap0, hrepr_algebraMap1]
    have hxunit : x = Units.mk0 (algebraMap K E b) hb_ne_E := Units.ext hb.symm
    have hw1 : w = 1 := by
      rw [← hx, hxunit, htorus_scalar]
    exact hw_ne_one hw1
  have hnorm_emb (x : Eˣ) :
      (b2.repr (x : E) 0) ^ 2 - (b2.repr (x : E) 1) ^ 2 * lam ≠ 0 := by
    rw [← emb_det K lam (b2.repr (x : E) 0) (b2.repr (x : E) 1)]
    change (emb (b2.repr (x : E) 0) (b2.repr (x : E) 1)).det ≠ 0
    have hlmx : Algebra.leftMulMatrix b2 (x : E) =
        emb (b2.repr (x : E) 0) (b2.repr (x : E) 1) := by
      rw [hlm (x : E)]
    rw [← hlmx]
    rw [← Algebra.norm_eq_matrix_det b2 (x : E)]
    exact hnorm_ne (x : E) x.ne_zero
  have hweyl_torus (x : Eˣ) : w * torus x * w⁻¹ = (torus x)⁻¹ := by
    rw [hw_inv]
    change Matrix.ProjGenLinGroup.mk wGL *
        Matrix.ProjGenLinGroup.mk (mulGL x) *
          Matrix.ProjGenLinGroup.mk wGL =
        (Matrix.ProjGenLinGroup.mk (mulGL x))⁻¹
    rw [← map_mul, ← map_mul]
    let a : K := b2.repr (x : E) 0
    let b : K := b2.repr (x : E) 1
    have hconjmat : wGL * (mulGL x : Matrix (Fin 2) (Fin 2) K) * wGL =
        emb a (-b) := by
      rw [show (wGL : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, -1] by simp [wGL]]
      rw [show (mulGL x : Matrix (Fin 2) (Fin 2) K) = emb a b by
        simp [mulGL, a, b]]
      rw [emb_diag_conj K lam a b]
      simp [emb]
    have hprodmat : emb a (-b) * emb a b =
        Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.mk0 (a ^ 2 - b ^ 2 * lam) (by
            simpa [a, b] using hnorm_emb x)) := by
      rw [emb_mul K lam a (-b) a b]
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [emb, Matrix.GeneralLinearGroup.scalar]
      all_goals
        first
        | left; ring
        | ring
    have hdet_neg : (emb a (-b)).det ≠ 0 := by
      rw [emb_det K lam a (-b)]
      convert hnorm_emb x using 1
      ring
    let A : GL (Fin 2) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero (emb a (-b)) hdet_neg
    have hprod : Matrix.ProjGenLinGroup.mk A * Matrix.ProjGenLinGroup.mk (mulGL x) = 1 := by
      rw [← map_mul]
      have hscalar : A * mulGL x =
          Matrix.GeneralLinearGroup.scalar (Fin 2)
            (Units.mk0 (a ^ 2 - b ^ 2 * lam) (by simpa [a, b] using hnorm_emb x)) := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [A, mulGL, emb, a, b, Matrix.GeneralLinearGroup.scalar]
        all_goals
          first
          | left; ring
          | ring
      rw [hscalar, Matrix.ProjGenLinGroup.mk_scalar]
    have hconjGL : wGL * mulGL x * wGL = A := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      simp [A, a, b, hconjmat]
    have hconj : Matrix.ProjGenLinGroup.mk (wGL * mulGL x * wGL) =
        (Matrix.ProjGenLinGroup.mk (mulGL x))⁻¹ := by
      rw [hconjGL]
      exact eq_inv_of_mul_eq_one_left hprod
    exact hconj
  -- centralizer of s
  have hC_ge : U ⊔ Subgroup.zpowers w ≤
      Subgroup.centralizer ({s} : Set (PGL2 K)) := by
    apply sup_le
    · intro x hx
      rcases hx with ⟨u, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      change torus u * torus u0 = torus u0 * torus u
      rw [← map_mul, ← map_mul]
      congr 1
      apply Units.ext
      change (u : E) * ρ = ρ * (u : E)
      rw [mul_comm]
    · apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc
        w * s = (w * s * w⁻¹) * w := by group
        _ = s⁻¹ * w := by rw [hweyl_torus u0]
        _ = s * w := by
          rw [show s⁻¹ = s by exact inv_eq_of_mul_eq_one_right hssq]
  have hC_le : Subgroup.centralizer ({s} : Set (PGL2 K)) ≤
      U ⊔ Subgroup.zpowers w := by
    intro x hx
    rcases Matrix.ProjGenLinGroup.mk_surjective x with ⟨A, rfl⟩
    have hcomm : Matrix.ProjGenLinGroup.mk A * s =
        s * Matrix.ProjGenLinGroup.mk A :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    have hmul : Matrix.ProjGenLinGroup.mk (A * mulGL u0) =
        Matrix.ProjGenLinGroup.mk (mulGL u0 * A) := by
      simpa [s, torus, mulHom, map_mul] using hcomm
    rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hmul with ⟨μ, hμ⟩
    let a : K := (A : Matrix (Fin 2) (Fin 2) K) 0 0
    let b : K := (A : Matrix (Fin 2) (Fin 2) K) 0 1
    let c : K := (A : Matrix (Fin 2) (Fin 2) K) 1 0
    let d : K := (A : Matrix (Fin 2) (Fin 2) K) 1 1
    -- A * M = μ * M * A with M = emb(0,1) = [[0, lam],[1, 0]]
    have hMval : (mulGL u0 : Matrix (Fin 2) (Fin 2) K) =
        !![0, lam; 1, 0] := by
      have hcoordρ : coord ρ = (0, 1) := by
        rw [← hb1]
        simp [coord]
      simp [u0, mulGL, emb, coord, hreprρ_0, hreprρ_1]
    have h00 : b * (μ : K) = lam * c := by
      have heq := congrArg (fun M : GL (Fin 2) K =>
        ((M : Matrix (Fin 2) (Fin 2) K) 0 0)) hμ
      simpa [a, b, c, d, hMval, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] using heq
    have h01 : a * lam * (μ : K) = lam * d := by
      have heq := congrArg (fun M : GL (Fin 2) K =>
        ((M : Matrix (Fin 2) (Fin 2) K) 0 1)) hμ
      simpa [a, b, c, d, hMval, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] using heq
    have h10 : d * (μ : K) = a := by
      have heq := congrArg (fun M : GL (Fin 2) K =>
        ((M : Matrix (Fin 2) (Fin 2) K) 1 0)) hμ
      simpa [a, b, c, d, hMval, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] using heq
    have h11 : c * lam * (μ : K) = b := by
      have heq := congrArg (fun M : GL (Fin 2) K =>
        ((M : Matrix (Fin 2) (Fin 2) K) 1 1)) hμ
      simpa [a, b, c, d, hMval, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] using heq
    have haμ : a * (μ : K) = d := by
      apply mul_right_cancel₀ hlam0
      calc
        (a * (μ : K)) * lam = a * lam * (μ : K) := by ring
        _ = d * lam := by rw [h01]; ring
    have hμsq_a : a * (μ : K) ^ 2 = a := by
      calc
        a * (μ : K) ^ 2 = (a * (μ : K)) * (μ : K) := by ring
        _ = d * (μ : K) := by rw [haμ]
        _ = a := h10
    have hμsq_c : c * (μ : K) ^ 2 = c := by
      apply mul_right_cancel₀ hlam0
      calc
        (c * (μ : K) ^ 2) * lam = c * lam * (μ : K) ^ 2 := by ring
        _ = (c * lam * (μ : K)) * (μ : K) := by ring
        _ = b * (μ : K) := by rw [h11]
        _ = c * lam := by rw [h00]; ring
    have hAne : a ≠ 0 ∨ c ≠ 0 := by
      by_contra h
      push_neg at h
      rcases h with ⟨ha0, hc0⟩
      have hb0 : b = 0 := by
        have hbμ : b * (μ : K) = 0 := by rw [h00, hc0]; simp
        exact (mul_eq_zero.mp hbμ).resolve_right μ.ne_zero
      have hd0 : d = 0 := by
        have hdμ : d * (μ : K) = 0 := by rw [h10, ha0]
        exact (mul_eq_zero.mp hdμ).resolve_right μ.ne_zero
      have hdet : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := A.det_ne_zero
      have hval : (A : Matrix (Fin 2) (Fin 2) K).det = a * d - b * c := by
        simp [a, b, c, d, Matrix.det_fin_two]
      rw [hval, ha0, hb0, hc0, hd0] at hdet
      simpa using hdet
    have hμsq : (μ : K) ^ 2 = 1 := by
      rcases hAne with ha | hc
      · exact mul_right_cancel₀ ha (by simpa [mul_comm] using hμsq_a)
      · exact mul_right_cancel₀ hc (by simpa [mul_comm] using hμsq_c)
    have hμ_unit : (μ : K) = 1 ∨ (μ : K) = -1 := by
      have h : ((μ : K) + 1) * ((μ : K) - 1) = 0 := by
        calc
          ((μ : K) + 1) * ((μ : K) - 1) = (μ : K) ^ 2 - 1 := by ring
          _ = 0 := by rw [hμsq]; simp
      rcases mul_eq_zero.mp h with hplus | hminus
      · right
        exact add_eq_zero_iff_eq_neg.mp hplus
      · left
        exact sub_eq_zero.mp hminus
    by_cases hu1 : (μ : K) = 1
    · have hb : b = lam * c := by simpa [hu1] using h00
      have hd : d = a := by simpa [hu1] using haμ.symm
      have hA_torus : (A : Matrix (Fin 2) (Fin 2) K) = emb a c := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [a, b, c, d, hb, hd, emb, mul_comm, mul_left_comm, mul_assoc]
      have hdet : (emb a c).det ≠ 0 := by
        rw [← hA_torus]
        exact A.det_ne_zero
      let z : E := algebraMap K E a + c • ρ
      have hcoord_z : coord z = (a, c) := by
        rw [hcoord_add (algebraMap K E a) (c • ρ)]
        rw [hcoord_algebraMap a]
        have h1 : coord (c • ρ) = (0, c) := by
          rw [← hb1]
          simp [coord]
        simp [h1]
      have hrepr0 : b2.repr z 0 = a := by
        simpa [coord] using (congrArg Prod.fst hcoord_z)
      have hrepr1 : b2.repr z 1 = c := by
        simpa [coord] using (congrArg Prod.snd hcoord_z)
      have hlm_z : Algebra.leftMulMatrix b2 z = emb a c := by
        rw [hlm z]
        simp [emb, coord, hrepr0, hrepr1]
      have hnorm_z : Algebra.norm K z = a ^ 2 - c ^ 2 * lam := by
        rw [Algebra.norm_eq_matrix_det b2 z, hlm_z]
        exact emb_det K lam a c
      have hnorm_z_ne : Algebra.norm K z ≠ 0 := by
        rw [hnorm_z]
        rwa [← emb_det K lam a c]
      have hz_ne : z ≠ 0 :=
        (Algebra.norm_ne_zero_iff_of_basis b2).1 hnorm_z_ne
      let x : Eˣ := Units.mk0 z hz_ne
      have hxmul : (mulGL x : Matrix (Fin 2) (Fin 2) K) = emb a c := by
        have hr0 : b2.repr (x : E) 0 = a := by simpa [x] using hrepr0
        have hr1 : b2.repr (x : E) 1 = c := by simpa [x] using hrepr1
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mulGL, emb, hr0, hr1]
      have hxeq : A = mulGL x := by
        apply Units.ext
        exact hA_torus.trans hxmul.symm
      have hmk : Matrix.ProjGenLinGroup.mk A = torus x := by
        change Matrix.ProjGenLinGroup.mk A =
          Matrix.ProjGenLinGroup.mk (mulGL x)
        exact congrArg Matrix.ProjGenLinGroup.mk hxeq
      exact (le_sup_left : U ≤ U ⊔ Subgroup.zpowers w) ⟨x, hmk.symm⟩
    · have hu_neg : (μ : K) = -1 := by
        rcases hμ_unit with h1 | hneg
        · exact False.elim (hu1 h1)
        · exact hneg
      have hb : b = -(lam * c) := by
        have hnegb : -b = lam * c := by
          simpa [hu_neg, mul_neg] using h00
        exact neg_eq_iff_eq_neg.mp hnegb
      have hd : d = -a := by
        have hneg : -a = d := by
          simpa [hu_neg, mul_neg] using haμ
        exact hneg.symm
      have hA : (A : Matrix (Fin 2) (Fin 2) K) =
          (wGL : Matrix (Fin 2) (Fin 2) K) * emb a (-c) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [a, b, c, d, hb, hd, wGL, emb, mul_comm, mul_left_comm,
            mul_assoc]
      have hdet : (emb a (-c)).det ≠ 0 := by
        have hdetA : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := A.det_ne_zero
        intro hzero
        apply hdetA
        have hval : (A : Matrix (Fin 2) (Fin 2) K).det =
            -(emb a (-c)).det := by
          rw [hA, Matrix.det_mul]
          have hdetw : (wGL : Matrix (Fin 2) (Fin 2) K).det = -1 := by
            simp [wGL, Matrix.det_fin_two]
          rw [hdetw]
          ring
        rw [hval, hzero]
        simp
      let z : E := algebraMap K E a + (-c) • ρ
      have hcoord_z : coord z = (a, -c) := by
        rw [hcoord_add (algebraMap K E a) ((-c) • ρ)]
        rw [hcoord_algebraMap a]
        have h1 : coord (-(c • ρ)) = (0, -c) := by
          rw [← hb1]
          ext <;> simp [coord, hreprρ_0, hreprρ_1]
        simp [h1]
      have hrepr0 : b2.repr z 0 = a := by
        simpa [coord] using (congrArg Prod.fst hcoord_z)
      have hrepr1 : b2.repr z 1 = -c := by
        simpa [coord] using (congrArg Prod.snd hcoord_z)
      have hlm_z : Algebra.leftMulMatrix b2 z = emb a (-c) := by
        rw [hlm z]
        simp [emb, coord, hrepr0, hrepr1]
      have hnorm_z : Algebra.norm K z = a ^ 2 - c ^ 2 * lam := by
        rw [Algebra.norm_eq_matrix_det b2 z, hlm_z]
        rw [emb_det K lam a (-c)]
        ring
      have hnorm_z_ne : Algebra.norm K z ≠ 0 := by
        rw [hnorm_z]
        have hdet' : a ^ 2 - c ^ 2 * lam ≠ 0 := by
          convert hdet using 1
          rw [emb_det K lam a (-c)]
          ring
        exact hdet'
      have hz_ne : z ≠ 0 :=
        (Algebra.norm_ne_zero_iff_of_basis b2).1 hnorm_z_ne
      let x : Eˣ := Units.mk0 z hz_ne
      have hxmul : (mulGL x : Matrix (Fin 2) (Fin 2) K) = emb a (-c) := by
        have hr0 : b2.repr (x : E) 0 = a := by simpa [x] using hrepr0
        have hr1 : b2.repr (x : E) 1 = -c := by simpa [x] using hrepr1
        ext i j
        fin_cases i <;> fin_cases j <;> simp [mulGL, emb, hr0, hr1]
      have hxeq : A = wGL * mulGL x := by
        apply Units.ext
        calc
          (A : Matrix (Fin 2) (Fin 2) K) =
              (wGL : Matrix (Fin 2) (Fin 2) K) * emb a (-c) := hA
          _ = (wGL : Matrix (Fin 2) (Fin 2) K) *
                (mulGL x : Matrix (Fin 2) (Fin 2) K) := by rw [hxmul]
          _ = ((wGL * mulGL x : GL (Fin 2) K) :
                Matrix (Fin 2) (Fin 2) K) := rfl
      have hmk : Matrix.ProjGenLinGroup.mk A = w * torus x := by
        calc
          Matrix.ProjGenLinGroup.mk A =
              Matrix.ProjGenLinGroup.mk (wGL * mulGL x) :=
            congrArg Matrix.ProjGenLinGroup.mk hxeq
          _ = w * torus x := by
            rw [map_mul]
            simp [w, torus, mulHom]
      have hmem' : Matrix.ProjGenLinGroup.mk A ∈
          Subgroup.zpowers w ⊔ U := by
        rw [hmk]
        exact Subgroup.mul_mem_sup
          (Subgroup.mem_zpowers w) (show torus x ∈ U from ⟨x, rfl⟩)
      have hsup : Subgroup.zpowers w ⊔ U = U ⊔ Subgroup.zpowers w :=
        sup_comm (Subgroup.zpowers w) U
      rw [hsup] at hmem'
      exact hmem'
  have hcross : Odd (Nat.card K) →
      ¬ U ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := K)).range := by
    intro hodd hUle
    have hchar : ringChar K ≠ 2 := by
      intro hchar
      have heven : Fintype.card K % 2 = 0 :=
        FiniteField.even_card_of_char_two hchar
      have hodd' : Odd (Fintype.card K) := by
        simpa [Nat.card_eq_fintype_card] using hodd
      exact hodd'.not_two_dvd_nat (Nat.dvd_of_mod_eq_zero heven)
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
    have ha0 : a ≠ 0 := by
      intro ha0
      subst a
      exact ha IsSquare.zero
    obtain ⟨x, hxnorm⟩ := FiniteField.norm_surjective K E a
    have hx0 : x ≠ 0 := by
      intro hx0
      subst x
      rw [Algebra.norm_zero] at hxnorm
      exact ha0 hxnorm.symm
    let xu : Eˣ := Units.mk0 x hx0
    have hmemU : torus xu ∈ U := ⟨xu, rfl⟩
    have hmemPSL := hUle hmemU
    have hsq : IsSquare ((mulHom xu).det : K) :=
      (pgl2_mk_mem_psl2_range_iff_det_isSquare (mulHom xu)).mp hmemPSL
    apply ha
    have hdet : ((mulHom xu).det : K) = Algebra.norm K x := by
      change Matrix.det (mulHom xu : Matrix (Fin 2) (Fin 2) K) =
        Algebra.norm K x
      rw [show (mulHom xu : Matrix (Fin 2) (Fin 2) K) =
          Algebra.leftMulMatrix b2 (x : E) by
        rw [hlm (x : E)]
        simp [mulHom, mulGL, emb, coord, xu]]
      exact (Algebra.norm_eq_matrix_det b2 x).symm
    rw [hdet, hxnorm] at hsq
    exact hsq
  have hnot_comm : ¬ U ≤ commutator (PGL2 K) := by
    intro hUcomm
    exact hcross hodd (hUcomm.trans (pgl2_commutator_le_psl2_range K))
  have hweyl_U (u : PGL2 K) (hu : u ∈ U) : w * u * w⁻¹ = u⁻¹ := by
    rcases hu with ⟨x, rfl⟩
    exact hweyl_torus x
  have hw_norm : w ∈ Subgroup.normalizer (U : Set (PGL2 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hu'
      rw [hweyl_U h hu']
      exact U.inv_mem hu'
    · intro hwuw
      have hI := hweyl_U (w * h * w⁻¹) hwuw
      have hLHS : w * (w * h * w⁻¹) * w⁻¹ = h := by
        calc
          w * (w * h * w⁻¹) * w⁻¹ = (w * w) * h * (w⁻¹ * w⁻¹) := by group
          _ = h := by rw [hw_inv, hw_sq]; simp
      exact (hI.symm.trans hLHS) ▸ U.inv_mem hwuw
  have hnormal_w : Subgroup.zpowers w ≤ Subgroup.normalizer (U : Set (PGL2 K)) := by
    rw [Subgroup.zpowers_le]
    exact hw_norm
  have hU_disjoint_w : Disjoint U (Subgroup.zpowers w) := by
    rw [disjoint_iff]
    apply le_antisymm
    · change ∀ x : PGL2 K, x ∈ U ⊓ Subgroup.zpowers w →
          x ∈ (⊥ : Subgroup (PGL2 K))
      intro x hx
      rcases hx with ⟨hx1, hx2⟩
      rcases (Subgroup.mem_zpowers_iff.mp hx2) with ⟨n, hn⟩
      rcases Int.even_or_odd n with hEven | hOdd
      · rcases hEven with ⟨m, hm⟩
        exact Subgroup.mem_bot.mpr (by
          rw [← hn]
          rw [show n = 2 * m by omega]
          rw [zpow_mul]
          have hw_sq_zpow : w ^ (2 : ℤ) = 1 := by
            rw [show (2 : ℤ) = (2 : ℕ) by norm_num]
            rw [zpow_natCast]
            simpa [pow_two] using hw_sq
          rw [hw_sq_zpow]
          simp)
      · exfalso
        apply hw_not_mem
        rw [← hn] at hx1
        rcases hOdd with ⟨m, hm⟩
        rw [show n = 2 * m + 1 by omega] at hx1
        have hpow : w ^ (2 * m + 1) = w := by
          rw [zpow_add, zpow_mul]
          have hw_sq_zpow : w ^ (2 : ℤ) = 1 := by
            rw [show (2 : ℤ) = (2 : ℕ) by norm_num]
            rw [zpow_natCast]
            simpa [pow_two] using hw_sq
          rw [hw_sq_zpow]
          simp
        rwa [hpow] at hx1
    · exact bot_le
  have hcard_w : Nat.card (Subgroup.zpowers w) = 2 := by
    have horder : orderOf w = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact (orderOf_eq_prime_iff (p := 2)).2 ⟨by simpa [pow_two] using hw_sq, hw_ne_one⟩
    calc
      Nat.card (Subgroup.zpowers w) = orderOf w := Nat.card_zpowers w
      _ = 2 := horder
  have hjoin_card : Nat.card ↥(U ⊔ Subgroup.zpowers w) = 2 * Nat.card U := by
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer U (Subgroup.zpowers w)
      hnormal_w hU_disjoint_w, hcard_w]
    omega
  have hUle_torus : pgl2ConcreteNonsplitTorus K lam ≤ torus.range := by
    intro x hx
    change ∃ (A : GL (Fin 2) K) (a b : K),
      x = Matrix.ProjGenLinGroup.mk A ∧
        (A : Matrix (Fin 2) (Fin 2) K) = !![a, b * lam; b, a] at hx
    rcases hx with ⟨A, a, b, hx, hA⟩
    let z : E := algebraMap K E a + b • ρ
    have hcoord_z : coord z = (a, b) := by
      rw [hcoord_add (algebraMap K E a) (b • ρ)]
      rw [hcoord_algebraMap a]
      have h1 : coord (b • ρ) = (0, b) := by
        rw [← hb1]
        simp [coord]
      simp [h1]
    have hrepr0 : b2.repr z 0 = a := by
      simpa [coord] using (congrArg Prod.fst hcoord_z)
    have hrepr1 : b2.repr z 1 = b := by
      simpa [coord] using (congrArg Prod.snd hcoord_z)
    have hlm_z : Algebra.leftMulMatrix b2 z = emb a b := by
      rw [hlm z]
      simp [emb, coord, hrepr0, hrepr1]
    have hdetA : (emb a b).det ≠ 0 := by
      change (!![a, b * lam; b, a] : Matrix (Fin 2) (Fin 2) K).det ≠ 0
      rw [← hA]
      exact A.det_ne_zero
    have hnorm_z : Algebra.norm K z = a ^ 2 - b ^ 2 * lam := by
      rw [Algebra.norm_eq_matrix_det b2 z, hlm_z]
      exact emb_det K lam a b
    have hnorm_z_ne : Algebra.norm K z ≠ 0 := by
      rw [hnorm_z]
      rwa [← emb_det K lam a b]
    have hz_ne : z ≠ 0 := (Algebra.norm_ne_zero_iff_of_basis b2).1 hnorm_z_ne
    let xu : Eˣ := Units.mk0 z hz_ne
    have hxmul : (mulGL xu : Matrix (Fin 2) (Fin 2) K) = emb a b := by
      have hr0 : b2.repr (xu : E) 0 = a := by simpa [xu] using hrepr0
      have hr1 : b2.repr (xu : E) 1 = b := by simpa [xu] using hrepr1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [mulGL, emb, hr0, hr1]
    have hxeq : A = mulGL xu := by
      apply Units.ext
      exact hA.trans hxmul.symm
    have hxmem : x = torus xu := by
      change x = Matrix.ProjGenLinGroup.mk (mulGL xu)
      exact hx.trans (congrArg Matrix.ProjGenLinGroup.mk hxeq)
    exact ⟨xu, hxmem.symm⟩
  have hUge_torus : torus.range ≤ pgl2ConcreteNonsplitTorus K lam := by
    intro x hx
    rcases hx with ⟨z, rfl⟩
    change ∃ (A : GL (Fin 2) K) (a b : K),
      Matrix.ProjGenLinGroup.mk (mulGL z) = Matrix.ProjGenLinGroup.mk A ∧
        (A : Matrix (Fin 2) (Fin 2) K) = !![a, b * lam; b, a]
    refine ⟨mulGL z, b2.repr (z : E) 0, b2.repr (z : E) 1, rfl, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mulGL, emb]
  have htorus : pgl2ConcreteNonsplitTorus K lam = torus.range :=
    le_antisymm hUle_torus hUge_torus
  refine ⟨s, w, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htorus]
    exact hUcyclic
  · rw [htorus]
    exact hrange_card
  · rw [htorus]
    exact hsU
  · exact ⟨hsne, by simpa [pow_two] using hssq⟩
  · exact hw_sq
  · intro hw
    apply hw_not_mem
    rw [htorus] at hw
    exact hw
  · intro x hx
    rw [htorus] at hx
    rcases hx with ⟨u, rfl⟩
    exact hweyl_torus u
  · rw [htorus]
    exact le_antisymm hC_le hC_ge
  · rw [htorus]
    exact hjoin_card
  · constructor
    · rw [htorus]
      exact hcross hodd
    · rw [htorus]
      exact hnot_comm
