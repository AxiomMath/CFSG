module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

private theorem exists_apply_ne_zero_and_apply_apply_eq_zero
    {A : Type*} [AddCommGroup A] (f : AddMonoid.End A)
    (hf : IsNilpotent f) (hne : f ≠ 0) :
    ∃ v : A, f v ≠ 0 ∧ f (f v) = 0 := by
  classical
  have : Nontrivial (AddMonoid.End A) := ⟨0, f, Ne.symm hne⟩
  let c : ℕ := nilpotencyClass f
  have hc : f ^ c = 0 := pow_nilpotencyClass hf
  have hcpos : 0 < c := pos_nilpotencyClass_iff.mpr hf
  have hcne1 : c ≠ 1 := by
    intro h
    exact hne (nilpotencyClass_eq_one.mp (show nilpotencyClass f = 1 from h))
  have hc2 : 2 ≤ c := by omega
  have hpred : f ^ (c - 1) ≠ 0 := pow_pred_nilpotencyClass hf
  have hex : ∃ x, (f ^ (c - 1)) x ≠ 0 := by
    by_contra h
    apply hpred
    ext x
    by_contra hx
    exact h ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hex
  have hmul : f * f ^ (c - 2) = f ^ (c - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hmul2 : f * f ^ (c - 1) = f ^ c := by
    rw [← pow_succ']
    congr 1
    omega
  have hstep : f ((f ^ (c - 2)) x) = (f ^ (c - 1)) x := by
    rw [← hmul]
    rfl
  have hstep2 : f ((f ^ (c - 1)) x) = 0 := by
    have h' : f ((f ^ (c - 1)) x) = (f ^ c) x := by
      rw [← hmul2]
      rfl
    rw [h', hc]
    rfl
  exact ⟨(f ^ (c - 2)) x, by rw [hstep]; exact hx, by rw [hstep, hstep2]⟩

theorem exists_quadratic_vector
    {A : Type*} [AddCommGroup A] (e : ℕ) (α : AddMonoid.End A)
    (hkill : ∀ x : A, (3 ^ e) • x = 0) (hα3 : α ^ 3 = 1) (hαne : α ≠ 1) :
    ∃ v : A, α v ≠ v ∧ α (α v - v) = α v - v := by
  classical
  have h3nil : IsNilpotent (3 : AddMonoid.End A) := by
    have hcast : IsNilpotent (((3 : ℕ) : AddMonoid.End A)) := by
      refine ⟨e, ?_⟩
      rw [← Nat.cast_pow]
      ext x
      rw [AddMonoid.End.natCast_apply]
      exact hkill x
    simpa using hcast
  let δ : AddMonoid.End A := α - 1
  have hδ3 : δ ^ 3 = (-3 : AddMonoid.End A) * (δ * α) := by
    have haux : δ ^ 3 + 3 * δ * α = α ^ 3 - 1 := by
      rw [show δ = α - 1 from rfl]
      noncomm_ring
    rw [hα3, sub_self] at haux
    have hneg : δ ^ 3 = -(3 * δ * α) := add_eq_zero_iff_eq_neg.mp haux
    rw [hneg]
    noncomm_ring
  have hneg3nil : IsNilpotent (-3 : AddMonoid.End A) := h3nil.neg
  have hcomm : Commute (-3 : AddMonoid.End A) (δ * α) := by
    have h1 : Commute (δ * α) (3 : AddMonoid.End A) := by
      simpa using Nat.commute_cast (δ * α) 3
    exact h1.symm.neg_left
  have hδ3nil : IsNilpotent (δ ^ 3) := by
    rw [hδ3]
    exact hcomm.isNilpotent_mul_right hneg3nil
  have hδnil : IsNilpotent δ := IsNilpotent.of_pow hδ3nil
  have hδne : δ ≠ 0 := by
    intro h
    apply hαne
    ext x
    have hx : δ x = 0 := by rw [h]; rfl
    rw [show δ = α - 1 from rfl] at hx
    have hx' : α x - x = 0 := hx
    exact sub_eq_zero.mp hx'
  obtain ⟨v, hv1, hv2⟩ :=
    exists_apply_ne_zero_and_apply_apply_eq_zero δ hδnil hδne
  have hδv : δ v = α v - v := by
    rw [show δ = α - 1 from rfl]
    rfl
  have hδδ : δ (δ v) = α (α v - v) - (α v - v) := by
    rw [hδv]
    rw [show δ = α - 1 from rfl]
    rfl
  refine ⟨v, ?_, ?_⟩
  · intro hαv
    apply hv1
    rw [hδv, hαv, sub_self]
  · have hzero : α (α v - v) - (α v - v) = 0 := by
      rw [← hδδ]
      exact hv2
    exact sub_eq_zero.mp hzero

theorem exists_quadratic_element {H : Type*} [Group H] {T : Subgroup H} (e : ℕ)
    (hT : IsMulCommutative ↥T) (hkill : ∀ t ∈ T, t ^ (3 ^ e) = 1) {α : MulAut H}
    (hαT : ∀ t ∈ T, α t ∈ T) (hα3 : α ^ 3 = 1) (hmov : ∃ t ∈ T, α t ≠ t) :
    ∃ v ∈ T, α v ≠ v ∧ α (α v * v⁻¹) = α v * v⁻¹ := by
  let _ : CommGroup ↥T :=
    { (inferInstance : Group ↥T) with mul_comm := fun a b => hT.is_comm.comm a b }
  let f : ↥T →* ↥T :=
    { toFun := fun t => ⟨α (t : H), hαT t t.2⟩
      map_one' := Subtype.ext (map_one α)
      map_mul' := fun a b => Subtype.ext (map_mul α (a : H) (b : H)) }
  let a : AddMonoid.End (Additive ↥T) := MonoidHom.toAdditive f
  have happ : ∀ x : Additive ↥T, (a x).toMul = f x.toMul := fun x => rfl
  have hkill' : ∀ x : Additive ↥T, (3 ^ e) • x = 0 := by
    intro x
    have h := hkill (x.toMul : H) x.toMul.2
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by simpa using h)
  have hα3' : ∀ t : H, α (α (α t)) = t := by
    intro t
    have h : (α ^ 3) t = (1 : MulAut H) t := by rw [hα3]
    simpa [pow_succ, MulAut.mul_apply] using h
  have ha3' : ∀ y : Additive ↥T, a (a (a y)) = y := by
    intro y
    apply Additive.toMul.injective
    rw [happ, happ, happ]
    exact Subtype.ext (hα3' (y.toMul : H))
  have ha3 : a ^ 3 = 1 := by
    refine AddMonoidHom.ext (fun x => ?_)
    calc (a ^ 3) x = a (a (a x)) := by rw [AddMonoid.End.coe_pow]; rfl
      _ = x := ha3' x
      _ = (1 : AddMonoid.End (Additive ↥T)) x := rfl
  have hane : a ≠ 1 := by
    obtain ⟨t, htT, htne⟩ := hmov
    intro h
    have h1 := congrArg (fun g : AddMonoid.End (Additive ↥T) =>
      (g (Additive.ofMul (⟨t, htT⟩ : ↥T))).toMul) h
    exact htne (congrArg Subtype.val h1)
  obtain ⟨v, hv1, hv2⟩ := exists_quadratic_vector e a hkill' ha3 hane
  refine ⟨(v.toMul : H), v.toMul.2, fun h => hv1 ?_, ?_⟩
  · apply Additive.toMul.injective
    rw [happ]
    exact Subtype.ext h
  · have h2 := congrArg Additive.toMul hv2
    rw [happ, toMul_sub, happ] at h2
    have h3 := congrArg Subtype.val h2
    simpa [f, div_eq_mul_inv] using h3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
