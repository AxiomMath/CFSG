module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Odd split-torus subgroups fixed by a pure field automorphism

For the standard split torus in `PGL₂(K)`, projective commutation with a
pure coefficient automorphism says that a torus parameter is sent either to
itself or to its negative.  On an invariant subgroup of odd order the
negative alternative is impossible.  Consequently the subgroup embeds in
the units of the fixed subfield.

This is the split-torus matrix core needed in the semilinear half of
Bender's Fact 1.10(ii).
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- The standard determinant-one split torus before passage to projective
coordinates. -/
@[expose] public def pGammaL2SplitTorusSL
    (K : Type u) [Field K] :
    Kˣ →* Matrix.SpecialLinearGroup (Fin 2) K :=
  { toFun := fun a => ⟨!![(a : K), 0; 0, (a⁻¹ : K)], by
      simp [Matrix.det_fin_two]⟩
    map_one' := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    map_mul' := by
      intro a b
      apply Subtype.ext
      ext i j
      change (!![((a * b : Kˣ) : K), 0; 0, (((a * b : Kˣ)⁻¹ : K))] :
          Matrix (Fin 2) (Fin 2) K) i j =
        ((!![(a : K), 0; 0, (a⁻¹ : K)] : Matrix (Fin 2) (Fin 2) K) *
          (!![(b : K), 0; 0, (b⁻¹ : K)] : Matrix (Fin 2) (Fin 2) K)) i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, mul_comm] }

/-- The standard split torus in `PGL₂(K)`. -/
@[expose] public def pGammaL2SplitTorusPGL
    (K : Type u) [Field K] : Kˣ →* PGL2 K :=
  Matrix.ProjGenLinGroup.mk.comp
    ((Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := K)).comp
      (pGammaL2SplitTorusSL K))

private theorem splitTorusPGL_map_field
    (K : Type u) [Field K] (sigma : K ≃+* K) (a : Kˣ) :
    pgl2FieldAut K sigma (pGammaL2SplitTorusPGL K a) =
      pGammaL2SplitTorusPGL K (Units.map sigma.toRingHom a) := by
  change pgl2RingEquiv sigma
      (QuotientGroup.mk' (Subgroup.center
        (Matrix.GeneralLinearGroup (Fin 2) K))
        (Matrix.SpecialLinearGroup.toGL (pGammaL2SplitTorusSL K a))) = _
  rw [pgl2RingEquiv_mk]
  change QuotientGroup.mk' (Subgroup.center
      (Matrix.GeneralLinearGroup (Fin 2) K))
      (Matrix.GeneralLinearGroup.map sigma.toRingHom
        (Matrix.SpecialLinearGroup.toGL (pGammaL2SplitTorusSL K a))) =
    QuotientGroup.mk' (Subgroup.center
      (Matrix.GeneralLinearGroup (Fin 2) K))
      (Matrix.SpecialLinearGroup.toGL
        (pGammaL2SplitTorusSL K (Units.map sigma.toRingHom a)))
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change sigma (((!![(a : K), 0; 0, (a⁻¹ : K)] : Matrix (Fin 2) (Fin 2) K) i j)) =
    ((!![(sigma (a : K)), 0; 0, ((sigma (a : K))⁻¹ : K)] :
      Matrix (Fin 2) (Fin 2) K) i j)
  fin_cases i <;> fin_cases j <;>
    simp [pGammaL2SplitTorusSL, Matrix.GeneralLinearGroup.map]

private theorem pure_field_commute_splitTorus
    (K : Type u) [Field K] (sigma : K ≃+* K) (a : Kˣ)
    (hcomm : Commute
      (SemidirectProduct.inr sigma : PGammaL2 K)
      (SemidirectProduct.inl (pGammaL2SplitTorusPGL K a))) :
    Units.map sigma.toRingHom a = a ∨
      Units.map sigma.toRingHom a = -a := by
  have hmul := hcomm.eq
  rw [SemidirectProduct.mul_def, SemidirectProduct.mul_def] at hmul
  have hproj :
      pgl2FieldAut K sigma (pGammaL2SplitTorusPGL K a) =
        pGammaL2SplitTorusPGL K a := by
    simpa [splitTorusPGL_map_field] using
      congrArg SemidirectProduct.left hmul
  change pgl2RingEquiv sigma
      (QuotientGroup.mk' (Subgroup.center
        (Matrix.GeneralLinearGroup (Fin 2) K))
        (Matrix.SpecialLinearGroup.toGL (pGammaL2SplitTorusSL K a))) =
    QuotientGroup.mk' (Subgroup.center
      (Matrix.GeneralLinearGroup (Fin 2) K))
      (Matrix.SpecialLinearGroup.toGL (pGammaL2SplitTorusSL K a)) at hproj
  rw [pgl2RingEquiv_mk] at hproj
  rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hproj with ⟨r, hr⟩
  have h00 := congrArg (fun B : GL (Fin 2) K =>
    ((B : Matrix (Fin 2) (Fin 2) K) 0 0)) hr
  have h11 := congrArg (fun B : GL (Fin 2) K =>
    ((B : Matrix (Fin 2) (Fin 2) K) 1 1)) hr
  let sa : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![(a : K), 0; 0, (a⁻¹ : K)], by simp [Matrix.det_fin_two]⟩
  have hsa : pGammaL2SplitTorusSL K a = sa := by
    apply Subtype.ext
    rfl
  rw [hsa] at h00 h11
  dsimp [sa] at h00 h11
  have h00' : sigma (a : K) * (r : K) = (a : K) := by
    simpa [pGammaL2SplitTorusSL, Matrix.SpecialLinearGroup.toGL,
      Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two] using h00
  have h11' : sigma (a⁻¹ : K) * (r : K) = (a⁻¹ : K) := by
    simpa [pGammaL2SplitTorusSL, Matrix.SpecialLinearGroup.toGL,
      Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two] using h11
  have hr2 : (r : K) ^ 2 = 1 := by
    calc
      (r : K) ^ 2 =
          (sigma (a : K) * (r : K)) *
            (sigma (a⁻¹ : K) * (r : K)) := by
              rw [map_inv₀]
              field_simp
      _ = (a : K) * (a⁻¹ : K) := by rw [h00', h11']
      _ = 1 := by simp
  rcases (sq_eq_one_iff.mp hr2) with hr | hr
  · left
    apply Units.ext
    change sigma (a : K) = (a : K)
    calc
      sigma (a : K) = sigma (a : K) * (r : K) := by rw [hr, mul_one]
      _ = (a : K) := h00'
  · right
    apply Units.ext
    change sigma (a : K) = (-a : K)
    calc
      sigma (a : K) =
          sigma (a : K) * (r : K) * (r : K)⁻¹ := by field_simp
      _ = (a : K) * (r : K)⁻¹ := by rw [h00']
      _ = -(a : K) := by rw [hr]; simp

private theorem unit_neg_one_ne_one_of_odd_prime_power
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) : (-1 : Kˣ) ≠ 1 := by
  intro h
  have hval := congrArg (fun x : Kˣ => (x : K)) h
  have htwo : (2 : K) = 0 := by
    have hone : (1 : K) = -1 := by simpa using hval.symm
    calc
      (2 : K) = 1 + 1 := by norm_num
      _ = -1 + 1 := by exact congrArg (fun x : K => x + 1) hone
      _ = 0 := by simp
  rcases hK with ⟨p, n, hp, hpodd, _hn, hcard⟩
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype K := Fintype.ofFinite K
  have hcardF : Fintype.card K = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  letI : CharP K p := charP_of_card_eq_prime_pow hcardF
  have hp2 : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp htwo
  rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with hp1 | hp2
  · exact hp.ne_one hp1
  · subst p
    exact hpodd.not_two_dvd_nat (by simp)

private theorem odd_subgroup_units_neg_one_not_mem
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (A : Subgroup Kˣ) (hAodd : Odd (Nat.card A)) :
    (-1 : Kˣ) ∉ A := by
  intro hneg
  have horder : orderOf (-1 : Kˣ) = 2 := by
    apply orderOf_eq_prime (p := 2)
    · simp [pow_two]
    · exact unit_neg_one_ne_one_of_odd_prime_power K hK
  have htwo : (2 : ℕ) ∣ Nat.card A := by
    have hdvd := Subgroup.orderOf_dvd_natCard A hneg
    rw [horder] at hdvd
    exact hdvd
  exact hAodd.not_two_dvd_nat htwo

/-- An odd subgroup of the standard split torus that is invariant under a
coefficient automorphism and projectively centralized by the corresponding
pure semilinear element is fixed pointwise.  Hence its order divides the
order of the unit group of the fixed subfield. -/
public theorem pGammaL2_pureField_oddInvariant_splitTorus_fixedSubfield
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (sigma : K ≃+* K) (A : Subgroup Kˣ)
    (hAodd : Odd (Nat.card A))
    (hAinv : ∀ a : Kˣ, a ∈ A → Units.map sigma.toRingHom a ∈ A)
    (hcomm : ∀ a : Kˣ, a ∈ A →
      Commute
        (SemidirectProduct.inr sigma : PGammaL2 K)
        (SemidirectProduct.inl (pGammaL2SplitTorusPGL K a))) :
    let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
    (∀ a : Kˣ, a ∈ A → Units.map sigma.toRingHom a = a) ∧
      Nat.card A ∣ Nat.card R - 1 := by
  let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
  have hfixed : ∀ a : Kˣ, a ∈ A → Units.map sigma.toRingHom a = a := by
    intro a ha
    rcases pure_field_commute_splitTorus K sigma a (hcomm a ha) with
      hfix | hneg
    · exact hfix
    · have hratio : (-1 : Kˣ) =
          Units.map sigma.toRingHom a * a⁻¹ := by
        rw [hneg]
        apply mul_right_cancel (b := a)
        simp
      have hratioA : Units.map sigma.toRingHom a * a⁻¹ ∈ A :=
        A.mul_mem (hAinv a ha) (A.inv_mem ha)
      exact False.elim ((odd_subgroup_units_neg_one_not_mem K hK A hAodd)
        (by rw [hratio]; exact hratioA))
  let f : A →* Rˣ :=
    { toFun := fun a =>
        Units.mk0
          (⟨((a : Kˣ) : K), by
            change ((a : Kˣ) : K) ∈
              MulAction.fixedPoints (Subgroup.zpowers sigma) K
            rw [MulAction.mem_fixedPoints]
            intro tau
            rcases Subgroup.mem_zpowers_iff.mp tau.2 with ⟨z, hz⟩
            have haFix : ((a : Kˣ) : K) ∈ MulAction.fixedBy K sigma := by
              change sigma ((a : Kˣ) : K) = ((a : Kˣ) : K)
              exact congrArg (fun x : Kˣ => (x : K))
                (hfixed (a : Kˣ) a.2)
            change (tau : K ≃+* K) ((a : Kˣ) : K) = ((a : Kˣ) : K)
            rw [← hz]
            exact MulAction.mem_fixedBy_zpow haFix z⟩)
          (by
            intro ha0
            apply (a : Kˣ).ne_zero
            exact congrArg (fun x : R => (x : K)) ha0)
      map_one' := by
        apply Units.ext
        rfl
      map_mul' := by
        intro a b
        apply Units.ext
        rfl }
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    exact congrArg (fun x : Rˣ => ((x : R) : K)) hab
  refine ⟨hfixed, ?_⟩
  have hdvd : Nat.card A ∣ Nat.card Rˣ :=
    Subgroup.card_dvd_of_injective f hfinj
  simpa [Nat.card_units] using hdvd

end CFSG.GorensteinWalter
