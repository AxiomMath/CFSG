module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix
open Matrix
open Multiplicative

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

open Finset

private lemma w1369_trace_fixed {E : Type} [Field E] [Finite E] [CharP E 2]
    [Algebra (ZMod 2) E] {a : ℕ} (hcard : Nat.card E = (2 ^ a) ^ 2) {c : E}
    (hc : c ^ (2 ^ a) = c) : Algebra.trace (ZMod 2) E c = 0 := by
  letI : Fintype E := Fintype.ofFinite E
  have hcard' : Fintype.card E = 2 ^ (2 * a) := by
    rw [← Nat.card_eq_fintype_card, hcard]; ring_nf
  have hfr : Module.finrank (ZMod 2) E = 2 * a := by
    have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := E)
    rw [ZMod.card] at hc
    have h : 2 ^ Module.finrank (ZMod 2) E = 2 ^ (2 * a) := by
      rw [← hc, hcard']
    exact Nat.pow_right_injective (le_refl 2) h
  apply (algebraMap (ZMod 2) E).injective
  rw [map_zero, FiniteField.algebraMap_trace_eq_sum_pow, hfr]
  simp only [Nat.card_zmod]
  have hsum : (∑ i ∈ range (2 * a), c ^ 2 ^ i) = 0 := by
    rw [show 2 * a = a + a by omega, Finset.sum_range_add]
    have h2 : (∑ i ∈ range a, c ^ 2 ^ (a + i)) = ∑ i ∈ range a, c ^ 2 ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hpow : 2 ^ (a + i) = 2 ^ a * 2 ^ i := by rw [pow_add]
      rw [hpow, pow_mul, hc]
    rw [h2]
    exact CharTwo.add_self_eq_zero _
  exact hsum

private lemma w1369_frob_bar_bar {E : Type} [Field E] [Finite E] [CharP E 2] {a : ℕ}
    (hcard : Nat.card E = (2 ^ a) ^ 2) (x : E) :
    (iterateFrobenius E 2 a) ((iterateFrobenius E 2 a) x) = x := by
  letI : Fintype E := Fintype.ofFinite E
  rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul]
  rw [show 2 ^ a * 2 ^ a = Nat.card E by rw [← pow_two, ← hcard]]
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

private lemma w1369_su_cond {E : Type} [Field E] [CharP E 2] {m a : ℕ} :
    ∀ A : GL (Fin m) E, A ∈ StatedSU m (2 ^ a) E →
      ((A : Matrix (Fin m) (Fin m) E).map (iterateFrobenius E 2 a))ᵀ *
        (A : Matrix (Fin m) (Fin m) E) = 1 := by
  intro A hA
  let k : Set (GL (Fin m) E) := {A : GL (Fin m) E |
    (A : Matrix (Fin m) (Fin m) E).det = 1 ∧
      ((A : Matrix (Fin m) (Fin m) E).map (· ^ (2 ^ a)))ᵀ *
        (A : Matrix (Fin m) (Fin m) E) = 1}
  change A ∈ Subgroup.closure k at hA
  refine Subgroup.closure_induction (k := k) (p := fun (A : GL (Fin m) E) _ =>
      ((A : Matrix (Fin m) (Fin m) E).map (iterateFrobenius E 2 a))ᵀ *
        (A : Matrix (Fin m) (Fin m) E) = 1) ?_ ?_ ?_ ?_ hA
  · intro x hx
    have hmap : (x : Matrix (Fin m) (Fin m) E).map (iterateFrobenius E 2 a) =
        (x : Matrix (Fin m) (Fin m) E).map (· ^ (2 ^ a)) := by
      ext i j; simp [iterateFrobenius_def]
    rw [hmap]
    exact hx.2
  · simp
  · intro x y hx hy ihx ihy
    rw [GeneralLinearGroup.coe_mul, Matrix.map_mul, Matrix.transpose_mul]
    rw [show ((y : Matrix (Fin m) (Fin m) E).map (iterateFrobenius E 2 a))ᵀ *
            ((x : Matrix (Fin m) (Fin m) E).map (iterateFrobenius E 2 a))ᵀ *
              ((x : Matrix (Fin m) (Fin m) E) * (y : Matrix (Fin m) (Fin m) E)) =
          ((y : Matrix (Fin m) (Fin m) E).map (iterateFrobenius E 2 a))ᵀ *
            ((((x : Matrix (Fin m) (Fin m) E).map (iterateFrobenius E 2 a))ᵀ *
              (x : Matrix (Fin m) (Fin m) E)) * (y : Matrix (Fin m) (Fin m) E)) by
      rw [mul_assoc, mul_assoc]]
    rw [ihx, Matrix.one_mul, ihy]
  · intro x hx ihx
    have hunit : IsUnit (x : Matrix (Fin m) (Fin m) E).det :=
      (Matrix.isUnit_iff_isUnit_det (x : Matrix (Fin m) (Fin m) E)).mp x.isUnit
    have hmul : ((x : Matrix (Fin m) (Fin m) E)⁻¹).map (iterateFrobenius E 2 a) *
        ((x : Matrix (Fin m) (Fin m) E).map (iterateFrobenius E 2 a)) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul]
      · simp
      · exact hunit
    have hmapinv : ((x : Matrix (Fin m) (Fin m) E)⁻¹).map (iterateFrobenius E 2 a) =
        (((x : Matrix (Fin m) (Fin m) E).map (iterateFrobenius E 2 a)))⁻¹ :=
      (Matrix.inv_eq_left_inv hmul).symm
    rw [GeneralLinearGroup.coe_inv, hmapinv, Matrix.transpose_nonsing_inv]
    have hxinv : ((x : Matrix (Fin m) (Fin m) E).map (iterateFrobenius E 2 a))ᵀ =
        (x : Matrix (Fin m) (Fin m) E)⁻¹ := (Matrix.inv_eq_left_inv ihx).symm
    rw [hxinv, Matrix.nonsing_inv_nonsing_inv (A := (x : Matrix (Fin m) (Fin m) E)) hunit]
    exact Matrix.mul_nonsing_inv (A := (x : Matrix (Fin m) (Fin m) E)) hunit

private noncomputable def w1369_herm {E : Type} [Field E] [CharP E 2] {m : ℕ}
    (a : ℕ) (x y : Fin m → E) : E :=
  ∑ i, (iterateFrobenius E 2 a) (x i) * y i

private lemma w1369_herm_add_left {E : Type} [Field E] [CharP E 2] {m : ℕ}
    (a : ℕ) (x x' y : Fin m → E) :
    w1369_herm (E := E) a x y + w1369_herm a x' y = w1369_herm a (x + x') y := by
  simp only [w1369_herm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

private lemma w1369_herm_add_right {E : Type} [Field E] [CharP E 2] {m : ℕ}
    (a : ℕ) (x y y' : Fin m → E) :
    w1369_herm (E := E) a x y + w1369_herm a x y' = w1369_herm a x (y + y') := by
  simp only [w1369_herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma w1369_herm_zero_left {E : Type} [Field E] [CharP E 2] {m : ℕ}
    (a : ℕ) (y : Fin m → E) : w1369_herm (E := E) a 0 y = 0 := by
  simp [w1369_herm]

private lemma w1369_herm_zero_right {E : Type} [Field E] [CharP E 2] {m : ℕ}
    (a : ℕ) (x : Fin m → E) : w1369_herm (E := E) a x 0 = 0 := by
  simp [w1369_herm]

private noncomputable def w1369_trForm {E : Type} [Field E] [CharP E 2] [Algebra (ZMod 2) E]
    {m : ℕ} (a : ℕ) : (Fin m → E) →+ (Fin m → E) →+ ZMod 2 where
  toFun x :=
    { toFun := fun y => Algebra.trace (ZMod 2) E (w1369_herm a x y)
      map_zero' := by simp [w1369_herm_zero_right]
      map_add' := by
        intro y y'
        rw [← w1369_herm_add_right, map_add] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    simp [w1369_herm_zero_left]
  map_add' := by
    intro x x'
    apply AddMonoidHom.ext
    intro y
    change Algebra.trace (ZMod 2) E (w1369_herm a (x + x') y) =
      Algebra.trace (ZMod 2) E (w1369_herm a x y) +
        Algebra.trace (ZMod 2) E (w1369_herm a x' y)
    rw [← w1369_herm_add_left, map_add]

open Multiplicative in
private noncomputable def w1369_mB {E : Type} [Field E] [CharP E 2] [Algebra (ZMod 2) E]
    {m : ℕ} (a : ℕ) :
    Multiplicative (Fin m → E) →* Multiplicative (Fin m → E) →* Multiplicative (ZMod 2) where
  toFun u :=
    { toFun := fun v => ofAdd ((w1369_trForm (E := E) (m := m) a) (toAdd u) (toAdd v))
      map_one' := by
        apply Multiplicative.ext
        simp only [toAdd_ofAdd, toAdd_one, map_zero, ofAdd_zero]
      map_mul' := by
        intro v w
        apply Multiplicative.ext
        simp only [toAdd_ofAdd, toAdd_mul, map_add] }
  map_one' := by
    apply MonoidHom.ext
    intro v
    apply Multiplicative.ext
    change (w1369_trForm (E := E) (m := m) a) (toAdd 1) (toAdd v) = toAdd 1
    rw [toAdd_one, map_zero, toAdd_one]
    rfl
  map_mul' := by
    intro u u'
    apply MonoidHom.ext
    intro v
    apply Multiplicative.ext
    change (w1369_trForm (E := E) (m := m) a) (toAdd (u * u')) (toAdd v) =
      (w1369_trForm (E := E) (m := m) a) (toAdd u) (toAdd v) +
        (w1369_trForm (E := E) (m := m) a) (toAdd u') (toAdd v)
    rw [toAdd_mul, map_add]
    rfl

open Multiplicative in
private lemma w1369_mB_apply {E : Type} [Field E] [CharP E 2] [Algebra (ZMod 2) E]
    {m : ℕ} (a : ℕ) (u v : Multiplicative (Fin m → E)) :
    w1369_mB (E := E) (m := m) a u v =
      ofAdd (Algebra.trace (ZMod 2) E (w1369_herm a (toAdd u) (toAdd v))) := rfl

private lemma w1369_herm_eq_dot {E : Type} [Field E] [CharP E 2] {m : ℕ}
    (a : ℕ) (x y : Fin m → E) :
    w1369_herm (E := E) a x y =
      (fun i => (iterateFrobenius E 2 a) (x i)) ⬝ᵥ y := rfl

private lemma w1369_barVec_mulVec {E : Type} [Field E] [CharP E 2] {m a : ℕ}
    (A : Matrix (Fin m) (Fin m) E) (x : Fin m → E) :
    (fun i => (iterateFrobenius E 2 a) ((A.mulVec x) i)) =
      (A.map (iterateFrobenius E 2 a)).mulVec
        (fun i => (iterateFrobenius E 2 a) (x i)) := by
  ext i
  simp only [Matrix.mulVec, Matrix.map_apply, dotProduct]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => map_mul _ _ _

private lemma w1369_dot_mulVec_mulVec {E : Type} [Field E] [CharP E 2] {m : ℕ}
    (M A : Matrix (Fin m) (Fin m) E) (u y : Fin m → E) :
    (M.mulVec u) ⬝ᵥ (A.mulVec y) = u ⬝ᵥ ((Mᵀ * A).mulVec y) := by
  rw [dotProduct_mulVec, vecMul_mulVec, ← dotProduct_mulVec]

private lemma w1369_herm_inv {E : Type} [Field E] [CharP E 2] {m a : ℕ}
    (A : GL (Fin m) E)
    (hA : ((A : Matrix (Fin m) (Fin m) E).map (iterateFrobenius E 2 a))ᵀ *
      (A : Matrix (Fin m) (Fin m) E) = 1) (x y : Fin m → E) :
    w1369_herm (E := E) a ((A : Matrix (Fin m) (Fin m) E).mulVec x)
        ((A : Matrix (Fin m) (Fin m) E).mulVec y) = w1369_herm a x y := by
  rw [w1369_herm_eq_dot, w1369_herm_eq_dot]
  rw [w1369_barVec_mulVec, w1369_dot_mulVec_mulVec, hA, Matrix.one_mulVec]

open Multiplicative in
private lemma w1369_mB_alt {E : Type} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    {m a : ℕ} (hcard : Nat.card E = (2 ^ a) ^ 2)
    (u : Multiplicative (Fin m → E)) : w1369_mB (E := E) (m := m) a u u = 1 := by
  rw [w1369_mB_apply]
  apply Multiplicative.ext
  simp only [toAdd_ofAdd, toAdd_one]
  have hterm : ∀ i : Fin m, Algebra.trace (ZMod 2) E
      ((iterateFrobenius E 2 a) (toAdd u i) * toAdd u i) = 0 := by
    intro i
    apply w1369_trace_fixed hcard
    have hc : (iterateFrobenius E 2 a)
        ((iterateFrobenius E 2 a) (toAdd u i) * toAdd u i) =
        (iterateFrobenius E 2 a) (toAdd u i) * toAdd u i := by
      rw [map_mul, w1369_frob_bar_bar hcard, mul_comm]
    simpa only [iterateFrobenius_def] using hc
  rw [w1369_herm, map_sum]
  exact Finset.sum_eq_zero fun i _ => hterm i

open Multiplicative in
private lemma w1369_mB_sep {E : Type} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    {m a : ℕ} (hcard : Nat.card E = (2 ^ a) ^ 2)
    (u : Multiplicative (Fin m → E))
    (h : ∀ v, w1369_mB (E := E) (m := m) a u v = 1) : u = 1 := by
  have hx : ∀ y : Fin m → E, Algebra.trace (ZMod 2) E (w1369_herm a (toAdd u) y) = 0 := by
    intro y
    have h1 : ofAdd (Algebra.trace (ZMod 2) E (w1369_herm a (toAdd u) y)) = 1 := by
      simpa only [w1369_mB_apply, toAdd_ofAdd] using h (ofAdd y)
    simpa using congrArg (Multiplicative.toAdd (α := ZMod 2)) h1
  apply Multiplicative.ext
  rw [toAdd_one]
  funext i
  have h0 : (iterateFrobenius E 2 a) (toAdd u i) = 0 := by
    apply (traceForm_nondegenerate (ZMod 2) E).1
    intro lam
    rw [Algebra.traceForm_apply]
    have h1 := hx (Pi.single i lam)
    rw [w1369_herm, Finset.sum_eq_single i, Pi.single_eq_same] at h1
    · exact h1
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  exact (iterateFrobenius E 2 a).injective (h0.trans (map_zero _).symm)

private lemma w1369_toAdd_natAct {E : Type} [Field E] [CharP E 2] {m a : ℕ}
    (γ : ↥(StatedSU m (2 ^ a) E)) (u : Multiplicative (Fin m → E)) :
    Multiplicative.toAdd (natAct (StatedSU m (2 ^ a) E) γ u) =
      (((γ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E)).mulVec
        (Multiplicative.toAdd u) := rfl

open Multiplicative in
private lemma w1369_mB_inv {E : Type} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    {m a : ℕ} (hcard : Nat.card E = (2 ^ a) ^ 2)
    (γ : ↥(StatedSU m (2 ^ a) E)) (u v : Multiplicative (Fin m → E)) :
    w1369_mB (E := E) (m := m) a (natAct (StatedSU m (2 ^ a) E) γ u)
        (natAct (StatedSU m (2 ^ a) E) γ v) = w1369_mB a u v := by
  have hA : (((γ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E).map
        (iterateFrobenius E 2 a))ᵀ * ((γ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) = 1 :=
    w1369_su_cond (γ : GL (Fin m) E) γ.2
  rw [w1369_mB_apply, w1369_mB_apply]
  congr 1
  rw [w1369_toAdd_natAct, w1369_toAdd_natAct]
  exact congrArg (Algebra.trace (ZMod 2) E)
    (w1369_herm_inv (E := E) (m := m) (a := a) γ hA (toAdd u) (toAdd v))

theorem hasSympForm_of_natSUn {K : Subgroup (MulAut W)} {m a : ℕ} (h : NatSUn K ⊤ ⊥ m a) :
    HasSympForm K := by
  obtain ⟨E, hEfield, hEfin, hcard, hreal⟩ := h
  letI : Field E := hEfield
  letI : Finite E := hEfin
  haveI : Fintype E := Fintype.ofFinite E
  have hcard' : Fintype.card E = 2 ^ (2 * a) := by
    rw [← Nat.card_eq_fintype_card, hcard]; ring_nf
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * a) hcard'
  letI : Algebra (ZMod 2) E := ZMod.algebra (R := E) (p := 2)
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨hπsurj, hZU, hkerle, hUinv, hZinv, hsecinv, hkerinv, β, hβsurj, hβker,
    hβequiv⟩ := hπ
  have hβker' : β.ker = ⊥ := by
    ext x
    rw [MonoidHom.mem_ker, hβker x]
    simp
  have hβinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).mp hβker'
  let Msub : Subgroup ↥(FFModel.nat (StatedSU m (2 ^ a) E)).sec :=
    (FFModel.nat (StatedSU m (2 ^ a) E)).ker.subgroupOf
      (FFModel.nat (StatedSU m (2 ^ a) E)).sec
  let Q := (↥(FFModel.nat (StatedSU m (2 ^ a) E)).sec) ⧸ Msub
  have hmk_inj : Function.Injective (QuotientGroup.mk' Msub) := by
    intro x y hxy
    obtain ⟨z, hz, hxz⟩ := (QuotientGroup.mk'_eq_mk' (N := Msub)).mp hxy
    have hz1 : z = 1 := by
      apply Subtype.ext
      have hz' := Subgroup.mem_subgroupOf.mp hz
      rw [show (FFModel.nat (StatedSU m (2 ^ a) E)).ker = ⊥ from rfl,
        Subgroup.mem_bot] at hz'
      exact hz'
    rw [hz1, mul_one] at hxz
    exact hxz
  let βe : ↥(⊤ : Subgroup W) ≃* Q := MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩
  let mkE : ↥(⊤ : Subgroup (Multiplicative (Fin m → E))) ≃* Q :=
    MulEquiv.ofBijective (QuotientGroup.mk' Msub)
      ⟨hmk_inj, QuotientGroup.mk'_surjective Msub⟩
  let e : W ≃* Multiplicative (Fin m → E) :=
    (Subgroup.topEquiv.symm.trans (βe.trans mkE.symm)).trans Subgroup.topEquiv
  have e_act : ∀ (γ : ↥(StatedSU m (2 ^ a) E)) (u : W),
      e ((π γ : MulAut W) u) = natAct (StatedSU m (2 ^ a) E) γ (e u) := by
    intro γ u
    set xM : ↥(⊤ : Subgroup (Multiplicative (Fin m → E))) :=
      mkE.symm (β (Subgroup.topEquiv.symm u)) with hxM
    have hbeta_u : β (Subgroup.topEquiv.symm u) = QuotientGroup.mk' Msub xM := by
      rw [hxM]
      exact (MulEquiv.apply_symm_apply mkE (β (Subgroup.topEquiv.symm u))).symm
    have hstep := hβequiv γ (Subgroup.topEquiv.symm u) xM (by trivial) (by trivial) hbeta_u
    have h1 : e ((π γ : MulAut W) u) =
        (mkE.symm (β ⟨(π γ : MulAut W) (Subgroup.topEquiv.symm u), by trivial⟩) :
          Multiplicative (Fin m → E)) := rfl
    rw [h1, hstep]
    have h2 : mkE.symm (QuotientGroup.mk
        ⟨(FFModel.nat (StatedSU m (2 ^ a) E)).act γ (xM :
          Multiplicative (Fin m → E)), by trivial⟩) =
        ⟨(FFModel.nat (StatedSU m (2 ^ a) E)).act γ (xM :
          Multiplicative (Fin m → E)), by trivial⟩ := by
      change mkE.symm (mkE ⟨(FFModel.nat (StatedSU m (2 ^ a) E)).act γ (xM :
          Multiplicative (Fin m → E)), by trivial⟩) = _
      exact MulEquiv.symm_apply_apply mkE _
    rw [h2]
    rfl
  let B : W →* W →* Multiplicative (ZMod 2) :=
    { toFun := fun u => (w1369_mB (E := E) (m := m) a (e u)).comp e
      map_one' := by
        apply MonoidHom.ext
        intro v
        apply Multiplicative.ext
        change (w1369_trForm (E := E) (m := m) a) (toAdd (e 1)) (toAdd (e v)) = toAdd 1
        rw [map_one, toAdd_one, map_zero, toAdd_one]
        rfl
      map_mul' := by
        intro u u'
        apply MonoidHom.ext
        intro v
        apply Multiplicative.ext
        change (w1369_trForm (E := E) (m := m) a) (toAdd (e (u * u'))) (toAdd (e v)) =
          (w1369_trForm (E := E) (m := m) a) (toAdd (e u)) (toAdd (e v)) +
            (w1369_trForm (E := E) (m := m) a) (toAdd (e u')) (toAdd (e v))
        rw [map_mul, toAdd_mul, map_add]
        rfl }
  refine ⟨B, ?_, ?_, ?_⟩
  · intro u hu
    have h1 : e u = 1 := by
      apply w1369_mB_sep (E := E) (a := a) hcard (e u)
      intro v
      obtain ⟨y, rfl⟩ := e.surjective v
      exact hu y
    exact e.injective (by rw [h1, map_one])
  · intro u
    exact w1369_mB_alt (E := E) (a := a) hcard (e u)
  · intro k hk x y
    obtain ⟨γ, hγ⟩ := hπsurj ⟨k, hk⟩
    have hk_coe : (k : MulAut W) = (π γ : MulAut W) := congrArg Subtype.val hγ.symm
    rw [hk_coe]
    change w1369_mB (E := E) (m := m) a (e ((π γ : MulAut W) x))
        (e ((π γ : MulAut W) y)) = w1369_mB a (e x) (e y)
    rw [e_act γ x, e_act γ y, w1369_mB_inv (E := E) (a := a) hcard γ (e x) (e y)]

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
