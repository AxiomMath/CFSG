module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_1
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Nilpotent.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Higman Lemma 2
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII
open scoped IsMulCommutative commutatorElement

universe u

private def lemma2_conjAut_restrict
    {P : Type u} [Group P] {A : Subgroup P}
    (hA_normal : A.Normal) (u : P) : MulAut A :=
  letI : A.Normal := hA_normal
  MulAut.conjNormal (H := A) u

private def lemma2_conjDefect
    {P : Type u} [Group P] {A : Subgroup P}
    (hA_normal : A.Normal) (hA_abelian : IsMulCommutative A) (u : P) : A →* A := by
  letI : IsMulCommutative A := hA_abelian
  exact (lemma2_conjAut_restrict hA_normal u).toMonoidHom * (MonoidHom.id A)⁻¹

private theorem lemma2_conjDefect_val
    {P : Type u} [Group P] {A : Subgroup P}
    (hA_normal : A.Normal) (hA_abelian : IsMulCommutative A) (u : P) (a : A) :
    ((lemma2_conjDefect hA_normal hA_abelian u a : A) : P) = ⁅u, (a : P)⁆ := by
  letI : IsMulCommutative A := hA_abelian
  simp [lemma2_conjDefect, lemma2_conjAut_restrict, commutatorElement_def,
    MulAut.conjNormal_apply, mul_assoc]
private theorem lemma2_linearMap_factor_n
    {n r k : ℕ} (f : (Fin r → ZMod n) →ₗ[ZMod n] (Fin r → ZMod n))
    (hf : ∀ x, ∃ y, k • y = f x) :
    ∃ g : (Fin r → ZMod n) →ₗ[ZMod n] (Fin r → ZMod n),
      ∀ x, k • g x = f x := by
  classical
  choose y hy using fun i : Fin r => hf (Pi.basisFun (ZMod n) (Fin r) i)
  let g : (Fin r → ZMod n) →ₗ[ZMod n] (Fin r → ZMod n) :=
    (Pi.basisFun (ZMod n) (Fin r)).constr (ZMod n) y
  have hgf : (k : ZMod n) • g = f := by
    apply (Pi.basisFun (ZMod n) (Fin r)).ext
    intro i
    change (k : ZMod n) • g (Pi.basisFun (ZMod n) (Fin r) i) =
      f (Pi.basisFun (ZMod n) (Fin r) i)
    rw [(Pi.basisFun (ZMod n) (Fin r)).constr_basis (ZMod n) y i]
    simpa [Nat.cast_smul_eq_nsmul] using hy i
  refine ⟨g, fun x => ?_⟩
  have hx := LinearMap.congr_fun hgf x
  simpa [Nat.cast_smul_eq_nsmul] using hx

private def lemma2_transportEndomorphism
    {A : Type*} [CommGroup A] {n r : ℕ}
    (hA : A ≃* Multiplicative (Fin r → ZMod n)) (d : A →* A) :
    (Fin r → ZMod n) →+ (Fin r → ZMod n) where
  toFun x := (hA (d (hA.symm (Multiplicative.ofAdd x)))).toAdd
  map_zero' := by simp
  map_add' x y := by simp

private def lemma2_untransportEndomorphism
    {A : Type*} [CommGroup A] {n r : ℕ}
    (hA : A ≃* Multiplicative (Fin r → ZMod n))
    (g : (Fin r → ZMod n) →+ (Fin r → ZMod n)) : A →* A where
  toFun a := hA.symm (Multiplicative.ofAdd (g (hA a).toAdd))
  map_one' := by simp
  map_mul' a b := by simp

public theorem lemma2_endomorphism_power_root_of_homocyclic
    {A : Type*} [CommGroup A] {n r : ℕ}
    (hA : A ≃* Multiplicative (Fin r → ZMod n)) (k : ℕ) (d : A →* A)
    (hd : ∀ a, ∃ b, b ^ k = d a) :
    ∃ alpha : A →* A, ∀ a, d a = (alpha a) ^ k := by
  let dAdd := lemma2_transportEndomorphism hA d
  let dLin := dAdd.toZModLinearMap n
  have hdLin : ∀ x, ∃ y, k • y = dLin x := by
    intro x
    obtain ⟨b, hb⟩ := hd (hA.symm (Multiplicative.ofAdd x))
    refine ⟨(hA b).toAdd, ?_⟩
    have hb' := congrArg Multiplicative.toAdd (congrArg hA hb)
    simpa [dLin, dAdd, lemma2_transportEndomorphism, ← ofAdd_nsmul] using hb'
  obtain ⟨g, hg⟩ := lemma2_linearMap_factor_n dLin hdLin
  let alpha : A →* A := lemma2_untransportEndomorphism hA g.toAddMonoidHom
  refine ⟨alpha, fun a => ?_⟩
  apply hA.injective
  rw [map_pow]
  rw [show hA (alpha a) = Multiplicative.ofAdd (g (hA a).toAdd) by
    simp [alpha, lemma2_untransportEndomorphism]]
  rw [← ofAdd_nsmul]
  have ha := hg (hA a).toAdd
  apply Multiplicative.toAdd.injective
  simpa [dLin, dAdd, lemma2_transportEndomorphism,
    Nat.cast_smul_eq_nsmul] using ha.symm

private theorem lemma2_powerClosure_eq_range
    {P : Type*} [Group P] {A : Subgroup P}
    (hA_abelian : IsMulCommutative A) (n : ℕ) :
    Subgroup.closure {x : P | ∃ a : A, (a : P) ^ n = x} =
      (powMonoidHom n : A →* A).range.map A.subtype := by
  letI : IsMulCommutative A := hA_abelian
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨a, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨a ^ n, MonoidHom.mem_range.mpr ⟨a, rfl⟩, rfl⟩
  · rintro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases MonoidHom.mem_range.mp hy with ⟨a, rfl⟩
    exact Subgroup.subset_closure ⟨a, rfl⟩

private theorem lemma2_conj_defect_lift_fourth_power
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hP : IsSuzukiTwoGroup P)
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A : Subgroup P} (hA_normal : A.Normal)
    (hA_abelian : IsMulCommutative A) (hA_X : IsXInvariantSubgroup X A)
    (u : P)
    (hu_comm :
      Subgroup.closure {x : P | ∃ a : A, ⁅u, (a : P)⁆ = x} ≤
        Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 4 = x}) :
    ∃ alpha : A →* A,
      ∀ a, lemma2_conjDefect hA_normal hA_abelian u a = (alpha a) ^ 4 := by
  letI : IsMulCommutative A := hA_abelian
  obtain ⟨e, r, ⟨hA⟩, _⟩ :=
    lemma1_abelian_invariant_homocyclic hP hXtrans hA_abelian hA_X
  apply lemma2_endomorphism_power_root_of_homocyclic hA 4
  intro a
  have hcomm :
      ⁅u, (a : P)⁆ ∈
        Subgroup.closure {x : P | ∃ b : A, ⁅u, (b : P)⁆ = x} :=
    Subgroup.subset_closure ⟨a, rfl⟩
  have hpow := hu_comm hcomm
  rw [lemma2_powerClosure_eq_range hA_abelian 4] at hpow
  rcases Subgroup.mem_map.mp hpow with ⟨y, hy, hyval⟩
  rcases MonoidHom.mem_range.mp hy with ⟨b, rfl⟩
  refine ⟨b, ?_⟩
  apply Subtype.ext
  exact hyval.trans (lemma2_conjDefect_val hA_normal hA_abelian u a).symm
private theorem lemma2_one_plus_two_bijective
    {A : Type*} [CommGroup A] {e r : ℕ}
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e))) (alpha : A →* A) :
    Function.Bijective (fun a : A => a * (alpha a) ^ 2) := by
  let alphaAdd := lemma2_transportEndomorphism hA alpha
  let alphaLin := alphaAdd.toZModLinearMap (2 ^ e)
  let t : Module.End (ZMod (2 ^ e)) (Fin r → ZMod (2 ^ e)) :=
    (2 : ZMod (2 ^ e)) • alphaLin
  have htwo_pow : (2 : ZMod (2 ^ e)) ^ e = 0 := by
    change ((2 : ℕ) : ZMod (2 ^ e)) ^ e = 0
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self (2 ^ e)
  have ht_nil : IsNilpotent t := by
    refine ⟨e, ?_⟩
    rw [smul_pow, htwo_pow, zero_smul]
  let betaLin : Module.End (ZMod (2 ^ e)) (Fin r → ZMod (2 ^ e)) :=
    LinearMap.id + t
  have hbeta_bij : Function.Bijective betaLin :=
    (Module.End.isUnit_iff betaLin).mp ht_nil.isUnit_one_add
  have hcoord (a : A) :
      betaLin (hA a).toAdd = (hA (a * (alpha a) ^ 2)).toAdd := by
    ext i
    simp [betaLin, t, alphaLin, alphaAdd, lemma2_transportEndomorphism]
  constructor
  · intro a b hab
    apply hA.injective
    apply Multiplicative.toAdd.injective
    apply hbeta_bij.injective
    rw [hcoord a, hcoord b]
    exact congrArg (fun z : A => (hA z).toAdd) hab
  · intro y
    obtain ⟨x, hx⟩ := hbeta_bij.surjective (hA y).toAdd
    let a : A := hA.symm (Multiplicative.ofAdd x)
    refine ⟨a, ?_⟩
    apply hA.injective
    apply Multiplicative.toAdd.injective
    rw [← hcoord a]
    simpa [a] using hx
private theorem lemma2_choose_square_correction
    {P : Type*} [Group P] {A : Subgroup P}
    (hA_abelian : IsMulCommutative A) {e r : ℕ}
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e)))
    (alpha : A →* A) (u : P)
    (hu_sq : u ^ 2 ∈
      Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x}) :
    ∃ a : A, ((a * (alpha a) ^ 2 : A) : P) ^ 2 = (u ^ 2)⁻¹ := by
  letI : IsMulCommutative A := hA_abelian
  rw [lemma2_powerClosure_eq_range hA_abelian 2] at hu_sq
  rcases Subgroup.mem_map.mp hu_sq with ⟨y, hy, hyval⟩
  rcases MonoidHom.mem_range.mp hy with ⟨c, rfl⟩
  obtain ⟨a, ha⟩ := (lemma2_one_plus_two_bijective hA alpha).surjective c⁻¹
  refine ⟨a, ?_⟩
  have haP := congrArg A.subtype ha
  change (A.subtype (a * (alpha a) ^ 2)) ^ 2 = (u ^ 2)⁻¹
  rw [haP]
  simpa using congrArg Inv.inv hyval

private theorem lemma2_corrected_element_isInvolution
    {P : Type*} [Group P] {A : Subgroup P}
    (hA_normal : A.Normal) (hA_abelian : IsMulCommutative A)
    (u : P) (hu_not : u ∉ A) (alpha : A →* A)
    (hdef : ∀ a, lemma2_conjDefect hA_normal hA_abelian u a = (alpha a) ^ 4)
    (a : A)
    (hcorr : ((a * (alpha a) ^ 2 : A) : P) ^ 2 = (u ^ 2)⁻¹) :
    IsInvolution ((a : P) * u) := by
  letI : IsMulCommutative A := hA_abelian
  have hcomm_alpha : ⁅u, (a : P)⁆ = ((alpha a : A) : P) ^ 4 := by
    rw [← lemma2_conjDefect_val hA_normal hA_abelian u a]
    exact congrArg A.subtype (hdef a)
  have hconj : u * (a : P) * u⁻¹ =
      (a : P) * ((alpha a : A) : P) ^ 4 := by
    have h := congrArg (fun z : P => z * (a : P)) hcomm_alpha
    have hfirst : u * (a : P) * u⁻¹ =
        ((alpha a : A) : P) ^ 4 * (a : P) := by
      simpa [commutatorElement_def, mul_assoc] using h
    calc
      u * (a : P) * u⁻¹ = ((alpha a : A) : P) ^ 4 * (a : P) := hfirst
      _ = (a : P) * ((alpha a : A) : P) ^ 4 := by
        exact congrArg A.subtype (mul_comm ((alpha a) ^ 4) a)
  have hAcalc : a * (a * (alpha a) ^ 4) = (a * (alpha a) ^ 2) ^ 2 := by
    calc
      a * (a * (alpha a) ^ 4) = a ^ 2 * (alpha a) ^ 4 := by
        rw [pow_two]
        ac_rfl
      _ = a ^ 2 * ((alpha a) ^ 2) ^ 2 := by
        rw [show (alpha a) ^ 4 = ((alpha a) ^ 2) ^ 2 by
          exact pow_mul (alpha a) 2 2]
      _ = (a * (alpha a) ^ 2) ^ 2 := (mul_pow a ((alpha a) ^ 2) 2).symm
  constructor
  · intro hau
    have hu : u = (a : P)⁻¹ := by
      calc
        u = (a : P)⁻¹ * ((a : P) * u) := by simp
        _ = (a : P)⁻¹ := by rw [hau]; simp
    apply hu_not
    rw [hu]
    exact A.inv_mem a.property
  · rw [pow_two]
    calc
      (a : P) * u * ((a : P) * u) =
          (a : P) * (u * (a : P) * u⁻¹) * u ^ 2 := by group
      _ = (a : P) * ((a : P) * ((alpha a : A) : P) ^ 4) * u ^ 2 := by
        rw [hconj]
      _ = ((a * (alpha a) ^ 2 : A) : P) ^ 2 * u ^ 2 := by
        simpa using congrArg A.subtype hAcalc
      _ = (u ^ 2)⁻¹ * u ^ 2 := by rw [hcorr]
      _ = 1 := inv_mul_cancel _
/-- Higman Lemma 2: the square/commutator alternative for an abelian normal
`X`-invariant subgroup excludes elements outside `A` satisfying both
constraints. -/
public theorem lemma2_no_external_square_commutator_exception
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hP : IsSuzukiTwoGroup P)
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A : Subgroup P} (hA_normal : A.Normal)
    (hA_abelian : IsMulCommutative A) (hA_X : IsXInvariantSubgroup X A) :
    A ≠ ⊥ →
      ∀ u : P, u ∉ A →
        ¬ (u ^ 2 ∈ Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x} ∧
          Subgroup.closure {x : P | ∃ a : A, ⁅u, (a : P)⁆ = x} ≤
            Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 4 = x}) := by
  intro hA_ne u hu_not
  rintro ⟨hu_sq, hu_comm⟩
  letI : IsMulCommutative A := hA_abelian
  obtain ⟨e, r, ⟨hA⟩, _⟩ :=
    lemma1_abelian_invariant_homocyclic hP hXtrans hA_abelian hA_X
  obtain ⟨alpha, hdef⟩ :=
    lemma2_conj_defect_lift_fourth_power
      hP hXtrans hA_normal hA_abelian hA_X u hu_comm
  obtain ⟨a, hcorr⟩ :=
    lemma2_choose_square_correction hA_abelian hA alpha u hu_sq
  have hau_involution : IsInvolution ((a : P) * u) :=
    lemma2_corrected_element_isInvolution
      hA_normal hA_abelian u hu_not alpha hdef a hcorr
  have hau_mem : (a : P) * u ∈ A :=
    lemma1_involutions_mem_of_nontrivial_invariant
      hP hXtrans hA_X hA_ne ((a : P) * u) hau_involution
  apply hu_not
  have hmul_mem : (a : P)⁻¹ * ((a : P) * u) ∈ A :=
    A.mul_mem (A.inv_mem a.property) hau_mem
  simpa [mul_assoc] using hmul_mem
end Higman
end External
end CFSG.BenderSuzuki
