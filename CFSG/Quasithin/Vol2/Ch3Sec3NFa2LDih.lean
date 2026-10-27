module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.H13.NFa2

section Aux

variable {Γ : Type} [Group Γ]

private def pw (t : Γ) (a : ZMod 6) : Γ := t ^ a.val

private lemma pw_add {t : Γ} (ht6 : orderOf t = 6) (a b : ZMod 6) :
    pw t (a + b) = pw t a * pw t b := by
  unfold pw
  rw [← pow_add, ZMod.val_add]
  have h := pow_mod_orderOf t (a.val + b.val)
  rw [ht6] at h
  exact h

private lemma pw_zero (t : Γ) : pw t 0 = 1 := by
  simp [pw]

private lemma pw_mul_neg {t : Γ} (ht6 : orderOf t = 6) (a : ZMod 6) :
    pw t a * pw t (-a) = 1 := by
  rw [← pw_add ht6, add_neg_cancel, pw_zero]

private lemma pw_inv {t : Γ} (ht6 : orderOf t = 6) (a : ZMod 6) :
    (pw t a)⁻¹ = pw t (-a) :=
  inv_eq_of_mul_eq_one_right (pw_mul_neg ht6 a)

private lemma s_mul_pw {s t : Γ} (ht6 : orderOf t = 6) (hst : s * t * s⁻¹ = t⁻¹) (a : ZMod 6) :
    s * pw t a = pw t (-a) * s := by
  have h : s * pw t a * s⁻¹ = (pw t a)⁻¹ := by
    unfold pw
    rw [← conj_pow, hst, inv_pow]
  rw [mul_inv_eq_iff_eq_mul, pw_inv ht6] at h
  exact h

private lemma mul_self_of_orderOf_two {s : Γ} (hs2 : orderOf s = 2) : s * s = 1 := by
  have h := pow_orderOf_eq_one s
  rw [hs2, pow_two] at h
  exact h

private lemma not_pw {s t : Γ} (ht6 : orderOf t = 6) (hst : s * t * s⁻¹ = t⁻¹) (a : ZMod 6) :
    s ≠ pw t a := by
  intro hs
  have hc : pw t a * t = t * pw t a := by
    unfold pw
    rw [← pow_succ, pow_succ']
  rw [hs, hc, mul_inv_cancel_right] at hst
  have h2 : t * t = 1 := mul_eq_one_iff_eq_inv.mpr hst
  have h3 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rw [ht6] at h3
  omega

private def phi (t s : Γ) : DihedralGroup 6 → Γ
  | .r i => pw t i
  | .sr j => pw t (-j) * s

private lemma phi_mul {s t : Γ} (ht6 : orderOf t = 6) (hst : s * t * s⁻¹ = t⁻¹)
    (hss : s * s = 1) (x y : DihedralGroup 6) :
    phi t s (x * y) = phi t s x * phi t s y := by
  rcases x with i | i <;> rcases y with k | k
  · change pw t (i + k) = pw t i * pw t k
    exact pw_add ht6 i k
  · change pw t (-(k - i)) * s = pw t i * (pw t (-k) * s)
    rw [← mul_assoc, ← pw_add ht6, show -(k - i) = i + -k by ring]
  · change pw t (-(i + k)) * s = pw t (-i) * s * pw t k
    rw [mul_assoc, s_mul_pw ht6 hst, ← mul_assoc, ← pw_add ht6,
      show -(i + k) = -i + -k by ring]
  · change pw t (k - i) = pw t (-i) * s * (pw t (-k) * s)
    rw [mul_assoc (pw t (-i)) s, ← mul_assoc s, s_mul_pw ht6 hst, neg_neg, mul_assoc, hss,
      mul_one, ← pw_add ht6, show -i + k = k - i by ring]

end Aux

theorem nfa2_closure_dihedral6 {Γ : Type} [Group Γ] (t s : Γ) (ht6 : orderOf t = 6)
    (hs2 : orderOf s = 2) (hst : s * t * s⁻¹ = t⁻¹) :
    Nat.card ↥(Subgroup.closure ({t, s} : Set Γ)) = 12 ∧
      Nonempty (↥(Subgroup.closure ({t, s} : Set Γ)) ≃* DihedralGroup 6) := by
  have hss : s * s = 1 := mul_self_of_orderOf_two hs2
  let F : DihedralGroup 6 →* Γ := MonoidHom.mk' (phi t s) (phi_mul ht6 hst hss)
  set E := Subgroup.closure ({t, s} : Set Γ) with hE
  have ht_mem : t ∈ E := Subgroup.subset_closure (Set.mem_insert t {s})
  have hs_mem : s ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem t (Set.mem_singleton s))
  have hmem : ∀ x, F x ∈ E := by
    intro x
    cases x with
    | r i =>
      change t ^ i.val ∈ E
      exact pow_mem ht_mem _
    | sr j =>
      change pw t (-j) * s ∈ E
      exact mul_mem (pow_mem ht_mem _) hs_mem
  have hsub : ({t, s} : Set Γ) ⊆ F.range := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy, SetLike.mem_coe, MonoidHom.mem_range]
      refine ⟨DihedralGroup.r 1, ?_⟩
      change t ^ (1 : ZMod 6).val = t
      rw [show (1 : ZMod 6).val = 1 from rfl, pow_one]
    · rw [hy, SetLike.mem_coe, MonoidHom.mem_range]
      refine ⟨DihedralGroup.sr 0, ?_⟩
      change pw t (-0) * s = s
      rw [neg_zero, pw_zero, one_mul]
  have hE_le : E ≤ F.range := (Subgroup.closure_le F.range).2 hsub
  have hsurj : ∀ y ∈ E, ∃ x, F x = y := fun y hy => MonoidHom.mem_range.1 (hE_le hy)
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_one F]
    intro x hx
    cases x with
    | r i =>
      change t ^ i.val = 1 at hx
      have h1 : orderOf t ∣ i.val := orderOf_dvd_of_pow_eq_one hx
      rw [ht6] at h1
      have h2 : i.val = 0 := by
        have := ZMod.val_lt i
        omega
      rw [(ZMod.val_eq_zero i).1 h2]
      exact DihedralGroup.one_def.symm
    | sr j =>
      exfalso
      change pw t (-j) * s = 1 at hx
      exact not_pw ht6 hst (-(-j)) (mul_left_cancel (hx.trans (pw_mul_neg ht6 (-j)).symm))
  let F' : DihedralGroup 6 →* E :=
    { toFun := fun x => ⟨F x, hmem x⟩
      map_one' := Subtype.ext (map_one F)
      map_mul' := fun x y => Subtype.ext (map_mul F x y) }
  have hbij : Function.Bijective F' := by
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hsurj y.1 y.2
    exact ⟨x, Subtype.ext hx⟩
  have e : DihedralGroup 6 ≃* E := MulEquiv.ofBijective F' hbij
  refine ⟨?_, ⟨e.symm⟩⟩
  have h1 := Nat.card_congr e.toEquiv
  rw [DihedralGroup.nat_card] at h1
  omega

end CFSG.Quasithin.H13.NFa2
