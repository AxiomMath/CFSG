module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.N588

open Subgroup

theorem exists_mulAut_injective_GL_aux {q : ℕ} [hq : Fact q.Prime] {W : Type*} [CommGroup W]
    [Finite W] [Module (ZMod q) (Additive W)] {d : ℕ} (hW : Nat.card W = q ^ d) :
    ∃ f : MulAut W →* GL (Fin d) (ZMod q), Function.Injective f := by
  classical
  let f : MulAut W → (Additive W →ₗ[ZMod q] Additive W) := fun k =>
    AddMonoidHom.toZModLinearMap q (MonoidHom.toAdditive k.toMonoidHom)
  have hf : ∀ (k : MulAut W) (x : Additive W), (f k x).toMul = k x.toMul := fun k x => rfl
  let ρ : MulAut W →* Module.End (ZMod q) (Additive W) :=
    { toFun := f
      map_one' := LinearMap.ext fun x => Additive.toMul.injective (by
        rw [hf]; rfl)
      map_mul' := fun g h => LinearMap.ext fun x => Additive.toMul.injective (by
        rw [hf, Module.End.mul_apply, hf, hf]; rfl) }
  have : Fintype (Additive W) := Fintype.ofFinite _
  have hcard : Fintype.card (Additive W) = q ^ d := by
    rw [← Nat.card_eq_fintype_card, ← hW]
    exact Nat.card_congr Additive.toMul
  have hfin : Module.finrank (ZMod q) (Additive W) = d := by
    have h := Module.card_eq_pow_finrank (K := ZMod q) (V := Additive W)
    rw [hcard, ZMod.card] at h
    exact (Nat.pow_right_injective hq.out.two_le h).symm
  let b := Module.finBasisOfFinrankEq (ZMod q) (Additive W) hfin
  let μ : MulAut W →* Matrix (Fin d) (Fin d) (ZMod q) :=
    (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp ρ
  refine ⟨μ.toHomUnits, fun g h hgh => ?_⟩
  have h1 : μ g = μ h := by
    have := congrArg Units.val hgh
    simpa using this
  have h2 : ρ g = ρ h := (LinearMap.toMatrixAlgEquiv b).injective h1
  ext x
  exact congrArg (fun L : Module.End (ZMod q) (Additive W) => (L (Additive.ofMul x)).toMul) h2

theorem exists_mulAut_injective_GL {q : ℕ} [Fact q.Prime] {V : Type*} [Group V] [Finite V]
    (hcomm : ∀ a b : V, a * b = b * a) (hexp : ∀ a : V, a ^ q = 1) {d : ℕ}
    (hcard : Nat.card V = q ^ d) :
    ∃ f : MulAut V →* GL (Fin d) (ZMod q), Function.Injective f := by
  letI : CommGroup V := { (inferInstance : Group V) with mul_comm := hcomm }
  letI : Module (ZMod q) (Additive V) := AddCommGroup.zmodModule (n := q) fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hexp _
  exact exists_mulAut_injective_GL_aux hcard

theorem card_mulAut_dvd_card_GL {q : ℕ} [Fact q.Prime] {V : Type*} [Group V] [Finite V]
    (hcomm : ∀ a b : V, a * b = b * a) (hexp : ∀ a : V, a ^ q = 1) {d : ℕ}
    (hcard : Nat.card V = q ^ d) :
    Nat.card (MulAut V) ∣ Nat.card (GL (Fin d) (ZMod q)) := by
  obtain ⟨f, hf⟩ := exists_mulAut_injective_GL hcomm hexp hcard
  exact Subgroup.card_dvd_of_injective f hf

theorem coprime_pow_sub_one {q m : ℕ} (hq : q.Prime) (hm : 1 ≤ m) : Nat.Coprime q (q ^ m - 1) := by
  rw [hq.coprime_iff_not_dvd]
  intro h
  have h1 : q ∣ q ^ m := dvd_pow_self q (by omega)
  have h2 : 1 ≤ q ^ m := Nat.one_le_pow _ _ hq.pos
  have h3 : q ∣ q ^ m - (q ^ m - 1) := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2] at h3
  exact hq.one_lt.ne' (Nat.dvd_one.1 h3)

theorem le_sum_of_pow_dvd_card_GL {q : ℕ} [hq : Fact q.Prime] {a k : ℕ}
    (h : q ^ k ∣ Nat.card (GL (Fin a) (ZMod q))) : k ≤ ∑ i : Fin a, (i : ℕ) := by
  classical
  rw [Matrix.card_GL_field, ZMod.card] at h
  have hfac : ∀ i : Fin a, q ^ a - q ^ (i : ℕ) = q ^ (i : ℕ) * (q ^ (a - i) - 1) := by
    intro i
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' i.2.le]
  rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum] at h
  have hcop : Nat.Coprime (q ^ k) (∏ i : Fin a, (q ^ (a - (i : ℕ)) - 1)) := by
    apply Nat.Coprime.pow_left
    exact Nat.Coprime.prod_right fun i _ => coprime_pow_sub_one hq.out (by omega)
  have h2 := hcop.dvd_of_dvd_mul_right h
  exact (Nat.pow_dvd_pow_iff_le_right hq.out.one_lt).1 h2

theorem le_three_of_pow_dvd_card_GL {q : ℕ} [Fact q.Prime] {a k : ℕ} (ha : a ≤ 3)
    (h : q ^ k ∣ Nat.card (GL (Fin a) (ZMod q))) : k ≤ 3 := by
  have h1 := le_sum_of_pow_dvd_card_GL h
  interval_cases a <;> simp [Fin.sum_univ_succ] at h1 <;> omega

theorem eq_one_of_forall_PGL {L : Type*} [Group L] (hL : commutator L = ⊤) {d q : ℕ}
    (h : ∀ f : L →* GL (Fin d) (ZMod q) ⧸ center (GL (Fin d) (ZMod q)), f = 1)
    (f : L →* GL (Fin d) (ZMod q)) : f = 1 := by
  have hc : ∀ x, f x ∈ center (GL (Fin d) (ZMod q)) := by
    intro x
    have h1 := congrArg (fun φ : L →* GL (Fin d) (ZMod q) ⧸ center (GL (Fin d) (ZMod q)) => φ x)
      (h ((QuotientGroup.mk' _).comp f))
    simp only [MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
      MonoidHom.one_apply] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hker : commutator L ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
      (Subgroup.mem_center_iff.1 (hc a) (f b)).symm]
    group
  refine MonoidHom.ext fun x => ?_
  have hx : x ∈ f.ker := hker (hL ▸ Subgroup.mem_top x)
  simpa using hx

@[expose] noncomputable def autQuot {K : Type*} [Group K] (N : Subgroup K) [N.Characteristic] :
    MulAut K →* MulAut (K ⧸ N) where
  toFun e := QuotientGroup.congr N N e (Subgroup.characteristic_iff_map_eq.1 inferInstance e)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' e f := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem autQuot_mk {K : Type*} [Group K] (N : Subgroup K) [N.Characteristic] (e : MulAut K)
    (x : K) : autQuot N e (x : K ⧸ N) = ((e x : K) : K ⧸ N) :=
  rfl

end CFSG.LocalAnalysis.UniquenessCase.UC6.N588
