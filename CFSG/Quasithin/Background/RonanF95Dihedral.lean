module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.RonanF95

private theorem conj_zpow_aux {Γ : Type*} [Group Γ] {a b : Γ} (ha : a * a = 1) (hb : b * b = 1)
    (k : ℤ) : a * (a * b) ^ k = (a * b) ^ (-k) * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, ha', hb', ← mul_assoc a a b, ha, one_mul]
  have h3 := conj_zpow (a := a) (b := a * b) (i := k)
  rw [h1, inv_zpow', ha'] at h3
  calc a * (a * b) ^ k = a * (a * b) ^ k * (a * a) := by rw [ha, mul_one]
    _ = (a * (a * b) ^ k * a) * a := (mul_assoc _ _ _).symm
    _ = (a * b) ^ (-k) * a := by rw [← h3]

private def zpowZMod {Γ : Type*} [Group Γ] {m : ℕ} (ρ : Γ) (i : ZMod m) : Γ :=
  ρ ^ (i.val : ℤ)

private def dihedralImage {Γ : Type*} [Group Γ] {m : ℕ} (ρ a : Γ) :
    DihedralGroup m → Γ
  | .r i => zpowZMod ρ i
  | .sr i => zpowZMod ρ (-i) * a

theorem nonempty_mulEquiv_dihedral {Γ : Type*} [Group Γ] {a b : Γ} {m : ℕ} (hm : 3 ≤ m)
    (ha : a * a = 1) (hb : b * b = 1) (hab : orderOf (a * b) = m) :
    Nonempty (↥(Subgroup.closure ({a, b} : Set Γ)) ≃* DihedralGroup m) := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Γ, a * b = ρ := ⟨_, rfl⟩
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hord : orderOf ρ = m := by rw [← hρ]; exact hab
  have hconj : ∀ k : ℤ, a * ρ ^ k = ρ ^ (-k) * a := by
    intro k
    rw [← hρ]
    exact conj_zpow_aux ha hb k
  have hzm : ∀ y : ℤ, ρ ^ y = ρ ^ (y % (m : ℤ)) := by
    intro y
    have h := zpow_mod_orderOf ρ y
    rw [hord] at h
    exact h.symm
  have hcastval : ∀ i : ZMod m, ((i.val : ℤ) : ZMod m) = i := fun i => by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hpow : ∀ (x : ℤ) (i : ZMod m), (x : ZMod m) = i → ρ ^ x = zpowZMod ρ i := by
    intro x i hx
    have hcast : (x : ZMod m) = ((i.val : ℤ) : ZMod m) := by
      rw [hx, hcastval]
    have hmod : x % (m : ℤ) = (i.val : ℤ) % (m : ℤ) :=
      (ZMod.intCast_eq_intCast_iff' x (i.val : ℤ) m).mp hcast
    unfold zpowZMod
    rw [hzm x, hmod]
    exact (hzm _).symm
  have zadd : ∀ i j : ZMod m, zpowZMod ρ (i + j) = zpowZMod ρ i * zpowZMod ρ j := by
    intro i j
    have h := hpow ((i.val : ℤ) + (j.val : ℤ)) (i + j)
      (by rw [Int.cast_add, hcastval, hcastval])
    rw [← h]
    unfold zpowZMod
    rw [zpow_add]
  have hz_one : zpowZMod ρ (1 : ZMod m) = ρ := by
    have h := hpow 1 1 (by simp)
    rw [zpow_one] at h
    exact h.symm
  have hz_neg_one : zpowZMod ρ (-1 : ZMod m) = ρ⁻¹ := by
    have h := hpow (-1) (-1) (by simp)
    rw [zpow_neg_one] at h
    exact h.symm
  have neg_conj : ∀ j : ZMod m, a * zpowZMod ρ j = zpowZMod ρ (-j) * a := by
    intro j
    have hc : ((-(j.val : ℤ) : ℤ) : ZMod m) = -j := by
      rw [Int.cast_neg, hcastval]
    have h := hconj (j.val : ℤ)
    rw [hpow _ _ hc] at h
    exact h
  have hmul : ∀ x y : DihedralGroup m,
      dihedralImage ρ a (x * y) = dihedralImage ρ a x * dihedralImage ρ a y := by
    rintro (i | i) (j | j)
    · rw [DihedralGroup.r_mul_r]
      exact zadd i j
    · rw [DihedralGroup.r_mul_sr]
      show zpowZMod ρ (-(j - i)) * a = zpowZMod ρ i * (zpowZMod ρ (-j) * a)
      rw [← mul_assoc, ← zadd, show -(j - i) = i + -j by ring]
    · rw [DihedralGroup.sr_mul_r]
      show zpowZMod ρ (-(i + j)) * a = zpowZMod ρ (-i) * a * zpowZMod ρ j
      rw [mul_assoc, neg_conj j, ← mul_assoc, ← zadd, neg_add]
    · rw [DihedralGroup.sr_mul_sr]
      show zpowZMod ρ (j - i) = zpowZMod ρ (-i) * a * (zpowZMod ρ (-j) * a)
      have hkey : a * (zpowZMod ρ (-j) * a) = zpowZMod ρ j := by
        rw [← mul_assoc, neg_conj (-j), neg_neg, mul_assoc, ha, mul_one]
      rw [mul_assoc, hkey, ← zadd, show j - i = -i + j by ring]
  let φ : DihedralGroup m →* Γ := MonoidHom.mk' (dihedralImage ρ a) hmul
  have hφr : ∀ i : ZMod m, φ (DihedralGroup.r i) = zpowZMod ρ i := fun i => rfl
  have hφsr : ∀ i : ZMod m, φ (DihedralGroup.sr i) = zpowZMod ρ (-i) * a := fun i => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    cases x with
    | r i =>
      rw [hφr] at hx
      have hx' : ρ ^ (i.val : ℤ) = 1 := hx
      have hdvd : (orderOf ρ : ℤ) ∣ (i.val : ℤ) := orderOf_dvd_iff_zpow_eq_one.mpr hx'
      rw [hord] at hdvd
      have hdvd' : m ∣ i.val := Int.natCast_dvd_natCast.mp hdvd
      have hi : i = 0 :=
        (ZMod.val_eq_zero i).mp (Nat.eq_zero_of_dvd_of_lt hdvd' (ZMod.val_lt i))
      rw [hi, DihedralGroup.r_zero]
    | sr i =>
      exfalso
      rw [hφsr] at hx
      have hx' : ρ ^ (((-i).val : ℕ) : ℤ) * a = 1 := hx
      have ha_eq : a = ρ ^ (-(((-i).val : ℕ) : ℤ)) := by
        rw [zpow_neg]
        exact eq_inv_of_mul_eq_one_right hx'
      have hcomm : a * ρ = ρ * a := by
        rw [ha_eq]
        exact ((Commute.refl ρ).zpow_left _).eq
      have h2 : ρ * a = ρ⁻¹ * a := by
        rw [← hcomm]
        have h := neg_conj 1
        rw [hz_one, hz_neg_one] at h
        exact h
      have hρρ : ρ = ρ⁻¹ := mul_right_cancel h2
      have hsq : ρ * ρ = 1 := by
        calc ρ * ρ = ρ⁻¹ * ρ := congrArg (· * ρ) hρρ
          _ = 1 := inv_mul_cancel ρ
      have hdvd : orderOf ρ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
      rw [hord] at hdvd
      have hle : m ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
  have hamem : a ∈ Subgroup.closure ({a, b} : Set Γ) := Subgroup.subset_closure (by simp)
  have hbmem : b ∈ Subgroup.closure ({a, b} : Set Γ) := Subgroup.subset_closure (by simp)
  have hρmem : ρ ∈ Subgroup.closure ({a, b} : Set Γ) := by
    rw [← hρ]
    exact Subgroup.mul_mem _ hamem hbmem
  have hzmem : ∀ i : ZMod m, zpowZMod ρ i ∈ Subgroup.closure ({a, b} : Set Γ) := by
    intro i
    unfold zpowZMod
    exact Subgroup.zpow_mem _ hρmem _
  have hrange : φ.range = Subgroup.closure ({a, b} : Set Γ) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
      cases x with
      | r i =>
        rw [hφr]
        exact hzmem i
      | sr i =>
        rw [hφsr]
        exact Subgroup.mul_mem _ (hzmem (-i)) hamem
    · rw [Subgroup.closure_le]
      intro y hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy
      · rw [hy]
        refine MonoidHom.mem_range.mpr ⟨DihedralGroup.sr 0, ?_⟩
        rw [hφsr]
        simp [zpowZMod]
      · rw [hy]
        refine MonoidHom.mem_range.mpr ⟨DihedralGroup.sr 1, ?_⟩
        rw [hφsr, hz_neg_one, ← hρ, mul_inv_rev, ha', hb', mul_assoc, ha, mul_one]
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hinj).symm⟩

end CFSG.Quasithin.RonanF95
