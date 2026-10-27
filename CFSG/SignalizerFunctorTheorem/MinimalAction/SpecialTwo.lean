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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped commutatorElement Pointwise

namespace CFSG.SignalizerFunctorTheorem.MinimalAction

section SpecialTwoAux

structure SpecialTwo.IsSpecial (P : Type*) [Group P] : Prop where
  card_center : Nat.card (Subgroup.center P) = 4
  comm_mem : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.center P
  sq_mem : ∀ g : P, g ^ 2 ∈ Subgroup.center P
  sq_eq_one : ∀ z ∈ Subgroup.center P, z ^ 2 = 1
  mem_center : ∀ g : P, g ^ 2 = 1 → g ∈ Subgroup.center P

variable {P : Type*} [Group P]

theorem SpecialTwo.IsSpecial.mul_self_eq_one (h : IsSpecial P) {z : P}
    (hz : z ∈ Subgroup.center P) : z * z = 1 := by
  rw [← sq]
  exact h.sq_eq_one z hz

@[expose] def SpecialTwo.commHom (h : IsSpecial P) (a : P) : P →* Subgroup.center P where
  toFun y := ⟨⁅y, a⁆, h.comm_mem y a⟩
  map_one' := Subtype.ext (by simp)
  map_mul' y z := by
    apply Subtype.ext
    show ⁅y * z, a⁆ = ⁅y, a⁆ * ⁅z, a⁆
    have hz : y * ⁅z, a⁆ = ⁅z, a⁆ * y := Subgroup.mem_center_iff.1 (h.comm_mem z a) y
    have hyz : ⁅z, a⁆ * ⁅y, a⁆ = ⁅y, a⁆ * ⁅z, a⁆ :=
      Subgroup.mem_center_iff.1 (h.comm_mem y a) _
    calc ⁅y * z, a⁆ = y * ⁅z, a⁆ * y⁻¹ * ⁅y, a⁆ := by
          simp only [commutatorElement_def]
          group
      _ = ⁅z, a⁆ * ⁅y, a⁆ := by
          rw [hz]
          group
      _ = ⁅y, a⁆ * ⁅z, a⁆ := hyz

@[simp] theorem SpecialTwo.coe_commHom (h : IsSpecial P) (a y : P) :
    ((commHom h a y : Subgroup.center P) : P) = ⁅y, a⁆ := rfl

theorem SpecialTwo.mem_ker_commHom (h : IsSpecial P) {a y : P} :
    y ∈ (commHom h a).ker ↔ y * a = a * y := by
  rw [MonoidHom.mem_ker, Subtype.ext_iff, coe_commHom, Subgroup.coe_one,
    commutatorElement_eq_one_iff_mul_comm]

theorem SpecialTwo.index_ker_commHom_le [Finite P] (h : IsSpecial P) (a : P) :
    (commHom h a).ker.index ≤ 4 := by
  rw [Subgroup.index_ker, ← h.card_center]
  exact Subgroup.card_le_card_group _

@[expose] def SpecialTwo.pairSubgroup {G : Type*} [Group G] (s : G) (hs : s * s = 1) :
    Subgroup G where
  carrier := {1, s}
  one_mem' := Set.mem_insert _ _
  mul_mem' := by
    rintro _ _ (rfl | rfl) (rfl | rfl) <;> simp [hs]
  inv_mem' := by
    rintro _ (rfl | rfl)
    · simp
    · simp [inv_eq_of_mul_eq_one_right hs]

theorem SpecialTwo.mem_pairSubgroup {G : Type*} [Group G] (s : G) (hs : s * s = 1) (x : G) :
    x ∈ pairSubgroup s hs ↔ x = 1 ∨ x = s := Iff.rfl

theorem SpecialTwo.card_pairSubgroup {G : Type*} [Group G] {s : G} (hs : s * s = 1)
    (hne : s ≠ 1) : Nat.card (pairSubgroup s hs) = 2 := by
  have : Nat.card (pairSubgroup s hs) = Set.ncard ({1, s} : Set G) :=
    Nat.card_coe_set_eq ({1, s} : Set G)
  rw [this, Set.ncard_pair hne.symm]

@[expose] def SpecialTwo.twoSub (h : IsSpecial P) (a : P) : Subgroup (Subgroup.center P) :=
  pairSubgroup (⟨a ^ 2, h.sq_mem a⟩ : Subgroup.center P)
    (Subtype.ext (h.mul_self_eq_one (h.sq_mem a)))

theorem SpecialTwo.mem_twoSub (h : IsSpecial P) (a : P) (z : Subgroup.center P) :
    z ∈ twoSub h a ↔ (z : P) = 1 ∨ (z : P) = a ^ 2 := by
  rw [twoSub, mem_pairSubgroup, Subtype.ext_iff, Subtype.ext_iff]
  rfl

theorem SpecialTwo.index_twoSub (h : IsSpecial P) {a : P} (ha : a ∉ Subgroup.center P) :
    (twoSub h a).index = 2 := by
  have hne : (⟨a ^ 2, h.sq_mem a⟩ : Subgroup.center P) ≠ 1 := fun h1 =>
    ha (h.mem_center a (congrArg Subtype.val h1))
  have hcard := (twoSub h a).card_mul_index
  have h2 : Nat.card (twoSub h a) = 2 := card_pairSubgroup _ hne
  rw [h2, h.card_center] at hcard
  omega

instance SpecialTwo.normal_twoSub (h : SpecialTwo.IsSpecial P) (a : P) :
    (SpecialTwo.twoSub h a).Normal where
  conj_mem n hn g := by
    have hc : g * n = n * g := Subtype.ext (Subgroup.mem_center_iff.1 g.2 n.1).symm
    rw [hc, mul_inv_cancel_right]
    exact hn

theorem SpecialTwo.index_comap_twoSub_le (h : IsSpecial P) {a : P}
    (ha : a ∉ Subgroup.center P) (x : P) :
    ((twoSub h a).comap (commHom h x)).index ≤ 2 := by
  rw [Subgroup.index_comap]
  have hd := Subgroup.relIndex_dvd_index_of_normal (twoSub h a) (commHom h x).range
  rw [index_twoSub h ha] at hd
  exact Nat.le_of_dvd (by norm_num) hd

@[expose] def SpecialTwo.centerCosets (a : P) : Set P :=
  (Subgroup.center P : Set P) ∪ a • (Subgroup.center P : Set P)

theorem SpecialTwo.mem_centerCosets {a c : P} :
    c ∈ centerCosets a ↔ c ∈ Subgroup.center P ∨ a⁻¹ * c ∈ Subgroup.center P := by
  simp [centerCosets, mem_leftCoset_iff]

theorem SpecialTwo.ncard_centerCosets_le (h : IsSpecial P) (a : P) :
    (centerCosets a).ncard ≤ 8 := by
  have hZ : (Subgroup.center P : Set P).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_center
  calc (centerCosets a).ncard
      ≤ (Subgroup.center P : Set P).ncard + (a • (Subgroup.center P : Set P)).ncard :=
        Set.ncard_union_le _ _
    _ = 8 := by rw [Set.ncard_smul_set, hZ]

theorem SpecialTwo.sq_ne_one_and_ne_sq (h : IsSpecial P) {a c : P} (hca : c * a = a * c)
    (hc : c ∉ centerCosets a) : c ^ 2 ≠ 1 ∧ c ^ 2 ≠ a ^ 2 := by
  rw [mem_centerCosets, not_or] at hc
  refine ⟨fun h1 => hc.1 (h.mem_center c h1), fun h2 => hc.2 ?_⟩
  have hca2 : (c * a) ^ 2 = 1 := by
    rw [Commute.mul_pow (show Commute c a from hca), h2]
    exact h.mul_self_eq_one (h.sq_mem a)
  have hw : c * a ∈ Subgroup.center P := h.mem_center _ hca2
  have hw' : a⁻¹ * (c * a) = c * a * a⁻¹ := Subgroup.mem_center_iff.1 hw a⁻¹
  have hform : a⁻¹ * c = c * a * (a ^ 2)⁻¹ := by
    calc a⁻¹ * c = a⁻¹ * (c * a) * a⁻¹ := by group
      _ = c * a * a⁻¹ * a⁻¹ := by rw [hw']
      _ = c * a * (a ^ 2)⁻¹ := by group
  rw [hform]
  exact Subgroup.mul_mem _ hw (Subgroup.inv_mem _ (h.sq_mem a))

theorem SpecialTwo.mul_mul_notMem_of_index_two {G : Type*} [Group G] {S : Subgroup G}
    (hS : S.index = 2) {u v w : G} (hu : u ∉ S) (hv : v ∉ S) (hw : w ∉ S) : u * v * w ∉ S := by
  have huv : u * v ∈ S := (Subgroup.mul_mem_iff_of_index_two hS).2 (iff_of_false hu hv)
  exact fun huvw => hw (((Subgroup.mul_mem_iff_of_index_two hS).1 huvw).1 huv)

theorem SpecialTwo.mul_sq_eq {G : Type*} [Group G] {x y k : G} (hyx : y * x = k * x * y)
    (hk : x * k = k * x) : (x * y) ^ 2 = k * x ^ 2 * y ^ 2 := by
  calc (x * y) ^ 2 = x * (y * x) * y := by rw [sq]; group
    _ = x * (k * x * y) * y := by rw [hyx]
    _ = (x * k) * x * y * y := by group
    _ = k * x * x * y * y := by rw [hk]
    _ = k * x ^ 2 * y ^ 2 := by simp only [sq, mul_assoc]

theorem SpecialTwo.comm_eq_sq_mul_sq_mul_sq {G : Type*} [Group G] {x y : G}
    (hk : x * ⁅y, x⁆ = ⁅y, x⁆ * x) (hX : ∀ g : G, g * x ^ 2 = x ^ 2 * g)
    (hXX : x ^ 2 * x ^ 2 = 1) (hYY : y ^ 2 * y ^ 2 = 1) :
    ⁅y, x⁆ = (x * y) ^ 2 * x ^ 2 * y ^ 2 := by
  have hyx : y * x = ⁅y, x⁆ * x * y := by
    simp [commutatorElement_def, mul_assoc]
  generalize ⁅y, x⁆ = k at hk hyx ⊢
  rw [mul_sq_eq hyx hk]
  calc k = k * (x ^ 2 * x ^ 2) * (y ^ 2 * y ^ 2) := by
        rw [hXX, hYY, mul_one, mul_one]
    _ = k * x ^ 2 * (x ^ 2 * y ^ 2) * y ^ 2 := by group
    _ = k * x ^ 2 * (y ^ 2 * x ^ 2) * y ^ 2 := by rw [hX (y ^ 2)]
    _ = k * x ^ 2 * y ^ 2 * x ^ 2 * y ^ 2 := by group

theorem SpecialTwo.commHom_notMem_twoSub (h : IsSpecial P) {a x y : P}
    (ha : a ∉ Subgroup.center P) (hxa : x * a = a * x) (hya : y * a = a * y)
    (hx : x ∉ centerCosets a) (hy : y ∉ centerCosets a) (hxy : x * y ∉ centerCosets a) :
    commHom h x y ∉ twoSub h a := by
  have hnot : ∀ c : P, c * a = a * c → c ∉ centerCosets a →
      (⟨c ^ 2, h.sq_mem c⟩ : Subgroup.center P) ∉ twoSub h a := by
    intro c hca hc hmem
    obtain ⟨h1, h2⟩ := sq_ne_one_and_ne_sq h hca hc
    rcases (mem_twoSub h a _).1 hmem with h3 | h3
    · exact h1 h3
    · exact h2 h3
  have hxya : x * y * a = a * (x * y) :=
    Commute.mul_left (show Commute x a from hxa) (show Commute y a from hya)
  have key : commHom h x y = ⟨(x * y) ^ 2, h.sq_mem _⟩ * ⟨x ^ 2, h.sq_mem x⟩ *
      ⟨y ^ 2, h.sq_mem y⟩ := by
    apply Subtype.ext
    show ⁅y, x⁆ = (x * y) ^ 2 * x ^ 2 * y ^ 2
    exact comm_eq_sq_mul_sq_mul_sq (Subgroup.mem_center_iff.1 (h.comm_mem y x) x)
      (Subgroup.mem_center_iff.1 (h.sq_mem x)) (h.mul_self_eq_one (h.sq_mem x))
      (h.mul_self_eq_one (h.sq_mem y))
  rw [key]
  exact mul_mul_notMem_of_index_two (index_twoSub h ha) (hnot _ hxya hxy) (hnot _ hxa hx)
    (hnot _ hya hy)

theorem SpecialTwo.exists_cover (h : IsSpecial P) {a : P} (ha : a ∉ Subgroup.center P) :
    ∃ x : P, x * a = a * x ∧ ∀ y : P, y * a = a * y → commHom h x y ∈ twoSub h a →
      y ∈ centerCosets a ∨ x * y ∈ centerCosets a := by
  by_cases hC : ∃ x : P, x * a = a * x ∧ x ∉ centerCosets a
  · obtain ⟨x, hxa, hxN⟩ := hC
    refine ⟨x, hxa, fun y hya hy => ?_⟩
    by_contra hcon
    rw [not_or] at hcon
    exact commHom_notMem_twoSub h ha hxa hya hxN hcon.1 hcon.2 hy
  · exact ⟨1, by simp, fun y hya _ =>
      Or.inl (by_contra fun hy => hC ⟨y, hya, hy⟩)⟩

theorem SpecialTwo.card_le_of_not_mem_center [Finite P] (h : IsSpecial P) {a : P}
    (ha : a ∉ Subgroup.center P) : Nat.card P ≤ 128 := by
  obtain ⟨x, hxa, hcover⟩ := exists_cover h ha
  let K : Subgroup P := (commHom h a).ker ⊓ (twoSub h a).comap (commHom h x)
  have hindex : K.index ≤ 8 := by
    calc K.index ≤ (commHom h a).ker.index * ((twoSub h a).comap (commHom h x)).index :=
          Subgroup.index_inf_le
      _ ≤ 4 * 2 := Nat.mul_le_mul (index_ker_commHom_le h a) (index_comap_twoSub_le h ha x)
  have hcard : Nat.card K ≤ 16 := by
    have hsub : (K : Set P) ⊆ centerCosets a ∪ x⁻¹ • centerCosets a := by
      intro y hy
      have hy1 : y ∈ K := hy
      obtain ⟨hy2, hy3⟩ := Subgroup.mem_inf.1 hy1
      rcases hcover y ((mem_ker_commHom h).1 hy2) hy3 with hyN | hxyN
      · exact Or.inl hyN
      · exact Or.inr ((mem_leftCoset_iff x⁻¹).2 (by simpa using hxyN))
    have hN := ncard_centerCosets_le h a
    calc Nat.card K = (K : Set P).ncard := Nat.card_coe_set_eq (K : Set P)
      _ ≤ (centerCosets a ∪ x⁻¹ • centerCosets a).ncard := Set.ncard_le_ncard hsub
      _ ≤ (centerCosets a).ncard + (x⁻¹ • centerCosets a).ncard := Set.ncard_union_le _ _
      _ = 2 * (centerCosets a).ncard := by rw [Set.ncard_smul_set]; ring
      _ ≤ 16 := by omega
  calc Nat.card P = Nat.card K * K.index := K.card_mul_index.symm
    _ ≤ 16 * 8 := Nat.mul_le_mul hcard hindex

end SpecialTwoAux

theorem card_le_of_special_two {P : Type*} [Group P] [Finite P]
    (hZ : Nat.card (Subgroup.center P) = 4)
    (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ Subgroup.center P)
    (hsq : ∀ g : P, g ^ 2 ∈ Subgroup.center P)
    (hZexp : ∀ z ∈ Subgroup.center P, z ^ 2 = 1)
    (hinv : ∀ g : P, g ^ 2 = 1 → g ∈ Subgroup.center P) :
    Nat.card P ≤ 128 := by
  have h : SpecialTwo.IsSpecial P := ⟨hZ, hcomm, hsq, hZexp, hinv⟩
  by_cases hPZ : ∀ g : P, g ∈ Subgroup.center P
  · have htop : Subgroup.center P = ⊤ := (Subgroup.eq_top_iff' _).2 hPZ
    have hcard : Nat.card P = Nat.card (Subgroup.center P) := by
      rw [htop, Subgroup.card_top]
    omega
  · obtain ⟨a, ha⟩ := not_forall.1 hPZ
    exact SpecialTwo.card_le_of_not_mem_center h ha

end CFSG.SignalizerFunctorTheorem.MinimalAction
