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
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Transfer
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.Walter.WardLocal

theorem card_dvd_card_sub_one_of_fpf {G : Type*} [Group G] [Finite G] (A H : Subgroup G)
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ h ∈ H, a * h * a⁻¹ = h → h = 1) :
    Nat.card A ∣ Nat.card H - 1 := by
  classical
  let X := {h : G // h ∈ H ∧ h ≠ 1}
  have hmem : ∀ (a : A) (h : X), (a : G) * h.1 * (a : G)⁻¹ ∈ H ∧
      (a : G) * h.1 * (a : G)⁻¹ ≠ 1 := by
    intro a h
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hAH a.2) h.1).mp h.2.1, ?_⟩
    intro h1
    apply h.2.2
    have := congrArg (fun x => (a : G)⁻¹ * x * a) h1
    simpa [mul_assoc] using this
  let : MulAction A X :=
    { smul := fun a h => ⟨(a : G) * h.1 * (a : G)⁻¹, hmem a h⟩
      one_smul := by
        intro h; apply Subtype.ext
        change ((1 : A) : G) * h.1 * ((1 : A) : G)⁻¹ = h.1
        simp
      mul_smul := by
        intro a b h; apply Subtype.ext
        change ((a * b : A) : G) * h.1 * ((a * b : A) : G)⁻¹ =
          (a : G) * ((b : G) * h.1 * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc] }
  have hstab : ∀ e : X, MulAction.stabilizer A e = ⊥ := by
    intro e
    rw [eq_bot_iff]
    intro a ha
    have hae : a • e = e := by simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha1
    have hfix : (a : G) * e.1 * (a : G)⁻¹ = e.1 := congrArg Subtype.val hae
    exact e.2.2 (hfree a a.2 (fun h => ha1 (Subtype.ext h)) e.1 e.2.1 hfix)
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hXcard : Nat.card X = Nat.card H - 1 := by
    have : Fintype G := Fintype.ofFinite G
    have e1 : Nat.card X = Nat.card {h : H // h ≠ 1} := by
      apply Nat.card_congr
      exact { toFun := fun h => ⟨⟨h.1, h.2.1⟩, fun e => h.2.2 (congrArg Subtype.val e)⟩
              invFun := fun h => ⟨h.1.1, h.1.2, fun e => h.2 (Subtype.ext e)⟩
              left_inv := fun h => rfl
              right_inv := fun h => rfl }
    rw [e1]
    have : Fintype H := Fintype.ofFinite H
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    simp
  rw [hXcard, Nat.card_prod] at hcard
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A X)), by rw [mul_comm]; exact hcard⟩

theorem dvd_of_pow_three_modEq {n i : ℕ} (h : (3 ^ n - 1) / 2 ∣ 3 ^ i - 1) : n ∣ i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : 3 ^ i - 1 = 0 := by simpa using h
    have hi : i = 0 := by
      by_contra hi
      have : 3 ≤ 3 ^ i := Nat.le_self_pow hi 3
      omega
    simp [hi]
  set N := (3 ^ n - 1) / 2 with hN
  have h3n : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hN2 : 2 * N = 3 ^ n - 1 := by
    have : 2 ∣ 3 ^ n - 1 := by
      have : Odd (3 ^ n) := Odd.pow (by decide)
      obtain ⟨t, ht⟩ := this
      omega
    omega
  have hmod : 3 ^ n ≡ 1 [MOD N] :=
    ((Nat.modEq_iff_dvd' h3n).mpr ⟨2, by omega⟩).symm
  have hi : 3 ^ i ≡ 1 [MOD N] :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr h).symm
  have hr : 3 ^ (i % n) ≡ 1 [MOD N] := by
    have h1 : 3 ^ i = (3 ^ n) ^ (i / n) * 3 ^ (i % n) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have h2 : (3 ^ n) ^ (i / n) * 3 ^ (i % n) ≡ 1 ^ (i / n) * 3 ^ (i % n) [MOD N] :=
      (hmod.pow _).mul_right _
    rw [one_pow, one_mul, ← h1] at h2
    exact h2.symm.trans hi
  by_contra hndvd
  have hrpos : 0 < i % n := Nat.pos_of_ne_zero (fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0))
  have hrlt : i % n < n := Nat.mod_lt _ hn
  have hdvd : N ∣ 3 ^ (i % n) - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp hr.symm
  have hlt : 3 ^ (i % n) - 1 < N := by
    have : 3 ^ (i % n) ≤ 3 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 3 ^ n = 3 * 3 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have hpos : 0 < 3 ^ (i % n) - 1 := by
    have : 3 ≤ 3 ^ (i % n) := Nat.le_self_pow (by omega) 3
    omega
  exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

theorem odd_mem_of_card_eq_two_mul {G : Type*} [Group G] [Finite G] {H M : Subgroup G}
    (hHM : H ≤ M) (hcard : Nat.card M = 2 * Nat.card H) {x : G} (hx : x ∈ M)
    (hodd : Odd (orderOf x)) : x ∈ H := by
  set H' := H.subgroupOf M with hH'
  have hcH' : Nat.card H' = Nat.card H := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv
  have hidx : H'.index = 2 := by
    have h1 := Subgroup.card_mul_index H'
    rw [hcH', hcard] at h1
    have hpos : 0 < Nat.card H := Nat.card_pos
    nlinarith
  have hsq := Subgroup.sq_mem_of_index_two hidx ⟨x, hx⟩
  have hsq' : x ^ 2 ∈ H := by
    rw [hH', Subgroup.mem_subgroupOf] at hsq
    simpa using hsq
  obtain ⟨t, ht⟩ := hodd
  have hx1 : x = (x ^ 2) ^ (t + 1) := by
    rw [← pow_mul, show 2 * (t + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hx1]
  exact Subgroup.pow_mem _ hsq' _

@[expose, instance_reducible] def conjAct {G : Type*} [Group G] (A : Subgroup G) (X : Finset G)
    (hX : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X) : MulAction A X where
  smul a x := ⟨(a : G) * x.1 * (a : G)⁻¹, hX a a.2 x.1 x.2⟩
  one_smul x := by
    apply Subtype.ext
    change ((1 : A) : G) * x.1 * ((1 : A) : G)⁻¹ = x.1
    simp
  mul_smul a b x := by
    apply Subtype.ext
    change ((a * b : A) : G) * x.1 * ((a * b : A) : G)⁻¹ =
      (a : G) * ((b : G) * x.1 * (b : G)⁻¹) * (a : G)⁻¹
    simp [mul_assoc]

theorem card_dvd_card_of_free {G : Type*} [Group G] [Finite G] (A : Subgroup G) (X : Finset G)
    (hX : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ x ∈ X, a * x * a⁻¹ = x → False) :
    Nat.card A ∣ X.card := by
  classical
  let : MulAction A X := conjAct A X hX
  have hstab : ∀ e : X, MulAction.stabilizer A e = ⊥ := by
    intro e
    rw [eq_bot_iff]
    intro a ha
    have hae : a • e = e := by simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha1
    have hfix : (a : G) * e.1 * (a : G)⁻¹ = e.1 := congrArg Subtype.val hae
    exact hfree a a.2 (fun h => ha1 (Subtype.ext h)) e.1 e.2 hfix
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  rw [Nat.card_prod] at hcard
  have hX' : Nat.card X = X.card := by simp
  rw [hX'] at hcard
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A X)), by rw [mul_comm]; exact hcard⟩

theorem card_eq_card_mul_centralizer {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    (X : Finset G) (hX : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X)
    (htrans : ∀ x ∈ X, ∀ y ∈ X, ∃ a ∈ A, a * x * a⁻¹ = y) {x : G} (hx : x ∈ X) :
    Nat.card A = X.card * Nat.card (A ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
  classical
  let : MulAction A X := conjAct A X hX
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer A (⟨x, hx⟩ : X))
  rw [MulAction.index_stabilizer] at h1
  have horb : MulAction.orbit A (⟨x, hx⟩ : X) = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true]
    obtain ⟨a, ha, hay⟩ := htrans x hx y.1 y.2
    exact ⟨⟨a, ha⟩, Subtype.ext hay⟩
  have hmem : ∀ a : A, a ∈ MulAction.stabilizer A (⟨x, hx⟩ : X) ↔
      (a : G) ∈ Subgroup.centralizer ({x} : Set G) := by
    intro a
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : (a : G) * x * (a : G)⁻¹ = x := congrArg Subtype.val h
      calc (a : G) * x = (a : G) * x * (a : G)⁻¹ * a := by group
        _ = x * a := by rw [h']
    · intro h
      apply Subtype.ext
      change (a : G) * x * (a : G)⁻¹ = x
      rw [h]; group
  have hstab : Nat.card (MulAction.stabilizer A (⟨x, hx⟩ : X)) =
      Nat.card (A ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
    apply Nat.card_congr
    exact { toFun := fun a => ⟨a.1.1, a.1.2, (hmem a.1).mp a.2⟩
            invFun := fun a => ⟨⟨a.1, a.2.1⟩, (hmem ⟨a.1, a.2.1⟩).mpr a.2.2⟩
            left_inv := fun a => rfl
            right_inv := fun a => rfl }
  rw [horb, hstab, Set.ncard_univ] at h1
  have hXc : Nat.card X = X.card := by simp
  rw [hXc] at h1
  rw [← h1, mul_comm]

theorem transferSylow_eq_one {H : Type*} [Group H] [Finite H] {r p : ℕ} [Fact r.Prime]
    [hp : Fact p.Prime] (hrp : r ≠ p) (R : Sylow r H)
    (hR : Subgroup.normalizer (R : Subgroup H) ≤ Subgroup.centralizer (R : Set H)) {x : H}
    {i : ℕ} (hx : orderOf x = p ^ i) : MonoidHom.transferSylow R hR x = 1 := by
  set y := MonoidHom.transferSylow R hR x
  have h1 : orderOf y ∣ p ^ i := hx ▸ orderOf_map_dvd _ x
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp R.2) y
  have h2 : r ^ j ∣ p ^ i := hj ▸ h1
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0, pow_zero, orderOf_eq_one_iff] at hj; exact hj
  · exfalso
    have : r ∣ p ^ i := (dvd_pow_self r hpos.ne').trans h2
    have := (Nat.prime_dvd_prime_iff_eq Fact.out hp.out).mp
      ((Nat.Prime.dvd_of_dvd_pow Fact.out) this)
    exact hrp this

theorem isPGroup_mul_of_burnside {H : Type*} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]
    {a m : ℕ} (hcard : Nat.card H = p ^ a * m) (hpm : ¬ p ∣ m)
    (hBurn : ∀ r : ℕ, r.Prime → r ∣ m → ∃ R : Sylow r H,
      Subgroup.normalizer (R : Subgroup H) ≤ Subgroup.centralizer (R : Set H))
    {x y : H} (hx : ∃ i, orderOf x = p ^ i) (hy : ∃ j, orderOf y = p ^ j) :
    ∃ l, orderOf (x * y) = p ^ l := by
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  have hcop : Nat.Coprime (orderOf (x * y)) m := by
    apply Nat.coprime_of_dvd
    intro r hr hrz hrm
    have : Fact r.Prime := ⟨hr⟩
    have hrp : r ≠ p := fun h => hpm (h ▸ hrm)
    obtain ⟨R, hR⟩ := hBurn r hr hrm
    have hker : x * y ∈ (MonoidHom.transferSylow R hR).ker := by
      rw [MonoidHom.mem_ker, map_mul, transferSylow_eq_one hrp R hR hi,
        transferSylow_eq_one hrp R hR hj, one_mul]
    have h1 := Subgroup.orderOf_dvd_natCard _ hker
    exact MonoidHom.not_dvd_card_ker_transferSylow R hR (hrz.trans h1)
  have hdvd : orderOf (x * y) ∣ p ^ a :=
    hcop.dvd_of_dvd_mul_right (hcard ▸ orderOf_dvd_natCard (x * y))
  obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  exact ⟨l, hl⟩

theorem exists_normal_sylow_of_burnside {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    {p : ℕ} [hp : Fact p.Prime] {a m : ℕ} (hcard : Nat.card N = p ^ a * m) (hpm : ¬ p ∣ m)
    (hBurn : ∀ r : ℕ, r.Prime → r ∣ m → ∃ R : Subgroup G, R ≤ N ∧ IsPGroup r R ∧
      Nat.card R = r ^ (Nat.card N).factorization r ∧
      ∀ n ∈ N, (∀ x ∈ R, n * x * n⁻¹ ∈ R) → ∀ x ∈ R, n * x = x * n) :
    ∃ P : Subgroup G, P ≤ N ∧ (∀ x ∈ N, x ∈ P ↔ ∃ i, orderOf x = p ^ i) ∧
      Nat.card P = p ^ a ∧ ∀ n ∈ N, ∀ x ∈ P, n * x * n⁻¹ ∈ P := by
  classical
  have hB : ∀ r : ℕ, r.Prime → r ∣ m → ∃ R : Sylow r N,
      Subgroup.normalizer (R : Subgroup N) ≤ Subgroup.centralizer (R : Set N) := by
    intro r hr hrm
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨R, hRN, hRp, hRc, hRcomm⟩ := hBurn r hr hrm
    have hRc' : Nat.card (R.subgroupOf N) = r ^ (Nat.card N).factorization r := by
      rw [← hRc]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv
    refine ⟨Sylow.ofCard (R.subgroupOf N) hRc', ?_⟩
    intro n hn
    rw [Sylow.coe_ofCard] at hn
    show n ∈ Subgroup.centralizer ((R.subgroupOf N : Subgroup N) : Set N)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hconj : ∀ y ∈ R, (n : G) * y * (n : G)⁻¹ ∈ R := by
      intro y hy
      have h1 : (⟨y, hRN hy⟩ : N) ∈ R.subgroupOf N := hy
      have h2 := (Subgroup.mem_normalizer_iff.mp hn _).mp h1
      exact h2
    have := hRcomm n n.2 hconj x hx
    exact Subtype.ext this.symm
  let P : Subgroup G :=
    { carrier := {x | x ∈ N ∧ ∃ i, orderOf x = p ^ i}
      mul_mem' := by
        rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
        refine ⟨Subgroup.mul_mem _ hxN hyN, ?_⟩
        have hcardN : Nat.card N = p ^ a * m := hcard
        obtain ⟨l, hl⟩ := isPGroup_mul_of_burnside (H := N) hcardN hpm hB
          (x := ⟨x, hxN⟩) (y := ⟨y, hyN⟩) (by simpa [Subgroup.orderOf_mk] using hx)
          (by simpa [Subgroup.orderOf_mk] using hy)
        exact ⟨l, by rw [← hl, ← Subgroup.orderOf_mk]; rfl⟩
      one_mem' := ⟨Subgroup.one_mem _, 0, by simp⟩
      inv_mem' := by
        rintro x ⟨hxN, hx⟩
        exact ⟨Subgroup.inv_mem _ hxN, by simpa using hx⟩ }
  have hPN : P ≤ N := fun x hx => hx.1
  have hPp : IsPGroup p P := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨x, hxN, i, hi⟩
    exact ⟨i, (Subgroup.orderOf_coe _).symm.trans hi⟩
  refine ⟨P, hPN, fun x hxN => ⟨fun hx => hx.2, fun hx => ⟨hxN, hx⟩⟩, ?_, ?_⟩
  ·
    obtain ⟨Q⟩ : Nonempty (Sylow p N) := inferInstance
    have hQ : ((Q : Subgroup N).map N.subtype) ≤ P := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp Q.2) ⟨y, hy⟩
      refine ⟨i, ?_⟩
      rw [Subgroup.coe_subtype, Subgroup.orderOf_coe, ← Subgroup.orderOf_mk y hy]
      exact hi
    have hQc : Nat.card ((Q : Subgroup N).map N.subtype) = p ^ a := by
      rw [Subgroup.card_map_of_injective N.subtype_injective, Q.card_eq_multiplicity, hcard,
        Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) (by
          rintro rfl; exact hpm (dvd_zero p)), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpm, add_zero,
        Nat.Prime.factorization_pow hp.out, Finsupp.single_eq_same]
    have h1 : p ^ a ≤ Nat.card P := hQc ▸ Subgroup.card_le_of_le hQ
    have h2 : Nat.card P ∣ p ^ a * m := hcard ▸ Subgroup.card_dvd_of_le hPN
    obtain ⟨b, hb⟩ := hPp.exists_card_eq
    rw [hb] at h1 h2 ⊢
    have h3 : p ^ b ∣ p ^ a := (Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr
      hpm)).dvd_of_dvd_mul_right h2
    have h4 := Nat.le_of_dvd (pow_pos hp.out.pos a) h3
    omega
  · rintro n hn x ⟨hxN, hx⟩
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hxN) (Subgroup.inv_mem _ hn), ?_⟩
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx

end CFSG.Walter.WardLocal
