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
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup

section Constrained

variable {Y : Type*} [Group Y]

@[expose] def ConstrainedAt (t : Y) : Prop :=
  ∃ Q : Subgroup Y, IsPGroup 2 Q ∧ Q ≤ centralizer ({t} : Set Y) ∧
    (∀ c ∈ centralizer ({t} : Set Y), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) ∧
    (∀ c ∈ centralizer ({t} : Set Y), (∀ q ∈ Q, c * q = q * c) → c ∈ Q)

@[expose] def TwoCentralConstrained (Y : Type*) [Group Y] : Prop :=
  ∀ (T : Subgroup Y) (t : Y), IsPGroup 2 T → ¬ 2 ∣ T.index → t ∈ T →
    (∀ x ∈ T, x * t = t * x) → orderOf t = 2 → ConstrainedAt t

@[expose] def InvolutionConstrained (Y : Type*) [Group Y] : Prop :=
  ∀ t : Y, orderOf t = 2 → ConstrainedAt t

theorem InvolutionConstrained.twoCentral (h : InvolutionConstrained Y) :
    TwoCentralConstrained Y :=
  fun _ t _ _ _ _ ht => h t ht

variable {Y' : Type*} [Group Y']

theorem ConstrainedAt.map (e : Y ≃* Y') {t : Y} (h : ConstrainedAt t) : ConstrainedAt (e t) := by
  obtain ⟨Q, hQ, hQC, hnorm, hcen⟩ := h
  have hC : ∀ c : Y', c ∈ centralizer ({e t} : Set Y') →
      e.symm c ∈ centralizer ({t} : Set Y) := by
    intro c hc
    rw [mem_centralizer_singleton_iff] at hc ⊢
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hc
  refine ⟨Q.map e.toMonoidHom, hQ.map _, ?_, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    have h1 := hQC hq
    rw [mem_centralizer_singleton_iff] at h1 ⊢
    change e q * e t = e t * e q
    rw [← map_mul, ← map_mul, h1]
  · rintro c hc _ ⟨q, hq, rfl⟩
    refine ⟨e.symm c * q * (e.symm c)⁻¹, hnorm _ (hC c hc) q hq, ?_⟩
    change e (e.symm c * q * (e.symm c)⁻¹) = c * e q * c⁻¹
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  · intro c hc hcQ
    refine ⟨e.symm c, hcen _ (hC c hc) fun q hq => ?_, by simp⟩
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hcQ (e q) ⟨q, hq, rfl⟩

end Constrained

section Core

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem conj_eq_or_eq_inv {z x : Y} (hz : orderOf z = 3)
    (hx : x ∈ normalizer ((zpowers z : Subgroup Y) : Set Y)) :
    x * z * x⁻¹ = z ∨ x * z * x⁻¹ = z⁻¹ := by
  have hmem : x * z * x⁻¹ ∈ zpowers z := (mem_normalizer_iff.mp hx z).mp (mem_zpowers z)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  have h3 : z ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat, ← hz, pow_orderOf_eq_one]
  have hk' : z ^ (k % 3) = x * z * x⁻¹ := by
    rw [show (3 : ℤ) = ((orderOf z : ℕ) : ℤ) by rw [hz]; rfl, zpow_mod_orderOf, hk]
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with h | h | h
  · exfalso
    rw [h, zpow_zero] at hk'
    have hz1 : z = 1 := by
      have h1 : x⁻¹ * (x * z * x⁻¹) * x = x⁻¹ * 1 * x := by rw [← hk']
      simpa [mul_assoc] using h1
    rw [hz1, orderOf_one] at hz
    norm_num at hz
  · left
    rw [h, zpow_one] at hk'
    exact hk'.symm
  · right
    rw [h] at hk'
    rw [← hk']
    have h2 : z ^ (2 : ℤ) * z = 1 := by
      rw [← zpow_add_one]
      exact h3
    exact eq_inv_of_mul_eq_one_left h2

theorem exists_central_involution {T : Subgroup Y} (hT : IsPGroup 2 T) (hT3 : 2 < Nat.card T)
    {z : Y} (hz : orderOf z = 3)
    (hTz : T ≤ normalizer ((zpowers z : Subgroup Y) : Set Y)) :
    ∃ t ∈ T, (∀ x ∈ T, x * t = t * x) ∧ t * z = z * t ∧ orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T₀ : Subgroup Y := T ⊓ centralizer ({z} : Set Y) with hT₀def
  have hT₀ : ∃ w ∈ T₀, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hinv : ∀ x ∈ T, x ≠ 1 → x * z * x⁻¹ = z⁻¹ := by
      intro x hx hx1
      rcases conj_eq_or_eq_inv hz (hTz hx) with h | h
      · exfalso
        refine hx1 (hcon x (mem_inf.mpr ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩))
        calc x * z = x * z * x⁻¹ * x := by group
          _ = z * x := by rw [h]
      · exact h
    have hle : Nat.card T ≤ 2 := by
      by_contra hgt
      push Not at hgt
      obtain ⟨a, b, hab, ha1, hb1⟩ : ∃ a b : T, a ≠ b ∧ a ≠ 1 ∧ b ≠ 1 := by
        classical
        have : Fintype T := Fintype.ofFinite T
        have hc : 2 < Fintype.card T := by rwa [← Nat.card_eq_fintype_card]
        have h1 : 1 < (Finset.univ.erase (1 : T)).card := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
          omega
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
        exact ⟨a, b, hab, Finset.ne_of_mem_erase ha, Finset.ne_of_mem_erase hb⟩
      have ha := hinv a a.2 (fun h => ha1 (Subtype.ext h))
      have hb := hinv b b.2 (fun h => hb1 (Subtype.ext h))
      have hab' : (a : Y)⁻¹ * b ∈ T₀ := by
        refine mem_inf.mpr ⟨T.mul_mem (T.inv_mem a.2) b.2,
          mem_centralizer_singleton_iff.mpr ?_⟩
        symm
        calc z * ((a : Y)⁻¹ * b) = (a : Y)⁻¹ * ((a : Y) * z * (a : Y)⁻¹) * b := by group
          _ = (a : Y)⁻¹ * (b * z * (b : Y)⁻¹) * b := by rw [ha, hb]
          _ = (a : Y)⁻¹ * b * z := by group
      have h1 := hcon _ hab'
      apply hab
      apply Subtype.ext
      calc (a : Y) = a * ((a : Y)⁻¹ * b) := by rw [h1, mul_one]
        _ = b := by group
    omega
  obtain ⟨w, hwT₀, hw1⟩ := hT₀
  have hN : (T₀.subgroupOf T).Normal := by
    refine ⟨fun c hc x => ?_⟩
    rw [mem_subgroupOf] at hc ⊢
    have hc' := mem_inf.mp hc
    have hcz : Commute (c : Y) z := mem_centralizer_singleton_iff.mp hc'.2
    refine mem_inf.mpr ⟨T.mul_mem (T.mul_mem x.2 hc'.1) (T.inv_mem x.2),
      mem_centralizer_singleton_iff.mpr ?_⟩
    have hw : Commute (c : Y) ((x : Y)⁻¹ * z * x) := by
      rcases conj_eq_or_eq_inv hz (inv_mem (hTz x.2)) with h | h
      · rw [inv_inv] at h
        rw [h]
        exact hcz
      · rw [inv_inv] at h
        rw [h]
        exact hcz.inv_right
    simp only [coe_mul, coe_inv]
    calc (x : Y) * c * (x : Y)⁻¹ * z = (x : Y) * (c * ((x : Y)⁻¹ * z * x)) * (x : Y)⁻¹ := by
          group
      _ = (x : Y) * (((x : Y)⁻¹ * z * x) * c) * (x : Y)⁻¹ := by rw [hw.eq]
      _ = z * ((x : Y) * c * (x : Y)⁻¹) := by group
  have : Group.IsNilpotent T := hT.isNilpotent
  have hne : T₀.subgroupOf T ≠ ⊥ := by
    intro hbot
    apply hw1
    have : (⟨w, hwT₀.1⟩ : T) ∈ T₀.subgroupOf T := by rw [mem_subgroupOf]; exact hwT₀
    rw [hbot, mem_bot] at this
    exact congrArg Subtype.val this
  have hW := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  set W : Subgroup T := T₀.subgroupOf T ⊓ center T with hWdef
  have hWp : IsPGroup 2 W := hT.to_subgroup W
  have hW2 : 2 ∣ Nat.card W := by
    rcases hWp.card_eq_or_dvd with h | h
    · exact absurd ((Subgroup.card_eq_one).mp h) hW
    · exact h
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hW2
  have htW := mem_inf.mp t.2
  set t₁ : T := t.1 with ht₁
  refine ⟨(t₁ : Y), t₁.2, fun x hx => ?_, ?_, ?_⟩
  · have hc := mem_center_iff.mp htW.2 ⟨x, hx⟩
    exact congrArg Subtype.val hc
  · have h1 := htW.1
    rw [mem_subgroupOf] at h1
    exact mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2
  · rw [Subgroup.orderOf_coe, ht₁, Subgroup.orderOf_coe]
    exact ht

theorem false_of_le_normalizer_zpowers (hY : TwoCentralConstrained Y) {T : Subgroup Y}
    (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) (hT3 : 2 < Nat.card T) {z : Y}
    (hz : orderOf z = 3) (hTz : T ≤ normalizer ((zpowers z : Subgroup Y) : Set Y)) : False := by
  obtain ⟨t, htT, htc, htz, ht2⟩ := exists_central_involution hT hT3 hz hTz
  obtain ⟨Q, hQ, -, hnorm, hcen⟩ := hY T t hT hTi htT htc ht2
  have hzC : z ∈ centralizer ({t} : Set Y) := mem_centralizer_singleton_iff.mpr htz.symm
  have hTC : ∀ x ∈ T, x ∈ centralizer ({t} : Set Y) :=
    fun x hx => mem_centralizer_singleton_iff.mpr (htc x hx)
  have hQT : Q ≤ T := by
    have hTN : T ≤ normalizer (Q : Set Y) := by
      intro x hx
      rw [mem_normalizer_iff]
      intro q
      refine ⟨fun hq => hnorm x (hTC x hx) q hq, fun hq => ?_⟩
      have h1 := hnorm x⁻¹ (inv_mem (hTC x hx)) _ hq
      rwa [show x⁻¹ * (x * q * x⁻¹) * x⁻¹⁻¹ = q by group] at h1
    have hsup : IsPGroup 2 ↥(Q ⊔ T) := hQ.to_sup_of_normal_left' hT hTN
    have h1 : T.relIndex (Q ⊔ T) ∣ T.index := relIndex_dvd_index_of_le le_sup_right
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hsup
    have h2 : T.relIndex (Q ⊔ T) ∣ 2 ^ k := by
      rw [← hk]
      exact (T.subgroupOf (Q ⊔ T)).index_dvd_card
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    have hj0 : j = 0 := by
      by_contra hj0
      apply hTi
      rw [hj] at h1
      exact (dvd_pow_self 2 hj0).trans h1
    rw [hj0, pow_zero, relIndex_eq_one] at hj
    exact le_sup_left.trans hj
  have hzQ : ∀ q ∈ Q, z * q = q * z := by
    intro q hq
    have hcQ : z * q * z⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hnorm z hzC q hq) (Q.inv_mem hq)
    have hcZ : z * q * z⁻¹ * q⁻¹ ∈ zpowers z := by
      have h1 : q * z⁻¹ * q⁻¹ ∈ zpowers z :=
        (mem_normalizer_iff.mp (hTz (hQT hq)) z⁻¹).mp (inv_mem (mem_zpowers z))
      rw [show z * q * z⁻¹ * q⁻¹ = z * (q * z⁻¹ * q⁻¹) by group]
      exact mul_mem (mem_zpowers z) h1
    have hc1 : z * q * z⁻¹ * q⁻¹ = 1 := by
      obtain ⟨k, hk⟩ := hQ ⟨_, hcQ⟩
      have h2 : orderOf (z * q * z⁻¹ * q⁻¹) ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      have h3 : orderOf (z * q * z⁻¹ * q⁻¹) ∣ 3 := hz ▸ orderOf_dvd_of_mem_zpowers hcZ
      have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h3 h2)
    calc z * q = z * q * z⁻¹ * q⁻¹ * (q * z) := by group
      _ = q * z := by rw [hc1, one_mul]
  obtain ⟨k, hk⟩ := hQ ⟨z, hcen z hzC hzQ⟩
  have h2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  rw [hz] at h2
  have h32 : (3 : ℕ) ∣ 2 := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h2)
  omega

end Core

section Inner

variable {X : Type*} [Group X]

theorem ker_conj_eq_center : (MulAut.conj : X →* MulAut X).ker = center X := by
  ext x
  rw [MonoidHom.mem_ker, mem_center_iff]
  constructor
  · intro h g
    have := congrArg (fun φ : MulAut X => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul, h g]

theorem inn_normal : ((MulAut.conj : X →* MulAut X).range).Normal := by
  refine ⟨fun n ⟨x, hx⟩ φ => ⟨φ x, ?_⟩⟩
  rw [← hx]
  ext g
  simp only [MulAut.conj_apply, MulAut.mul_apply]
  simp

@[expose] noncomputable def quotientCenterEquivInn :
    X ⧸ center X ≃* ↥(MulAut.conj : X →* MulAut X).range :=
  (QuotientGroup.quotientMulEquivOfEq ker_conj_eq_center.symm).trans
    (QuotientGroup.quotientKerEquivRange _)

end Inner

section Orders

variable {X : Type*} [Group X]

@[expose] noncomputable def autQuotCenter : MulAut X →* MulAut (X ⧸ center X) where
  toFun α := QuotientGroup.congr (center X) (center X) α
    (Subgroup.characteristic_iff_map_eq.mp inferInstance α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem autQuotCenter_mk (α : MulAut X) (x : X) :
    autQuotCenter α (x : X ⧸ center X) = ((α x : X) : X ⧸ center X) :=
  rfl

theorem autQuotCenter_injective [Group.IsPerfect X] :
    Function.Injective (autQuotCenter (X := X)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro α hα
  rw [MonoidHom.mem_ker] at hα
  have hc : ∀ x : X, x⁻¹ * α x ∈ center X := by
    intro x
    have h1 := congrArg (fun φ : MulAut (X ⧸ center X) => φ (x : X ⧸ center X)) hα
    simp only [autQuotCenter_mk, MulAut.one_apply] at h1
    rw [QuotientGroup.eq] at h1
    have h2 := (center X).inv_mem h1
    rw [mul_inv_rev, inv_inv] at h2
    exact h2
  let d : X →* center X :=
    { toFun := fun x => ⟨x⁻¹ * α x, hc x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        simp only [map_mul, mul_inv_rev, coe_mul]
        have hz := mem_center_iff.mp (hc x)
        calc y⁻¹ * x⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [← hz y⁻¹]
          _ = x⁻¹ * α x * (y⁻¹ * α y) := by group }
  have hker : d.ker = ⊤ := by
    rw [eq_top_iff, ← (Group.IsPerfect.commutator_eq_top (G := X))]
    exact Abelianization.commutator_subset_ker d
  rw [mem_bot]
  ext x
  have hx : x ∈ d.ker := hker ▸ mem_top x
  rw [MonoidHom.mem_ker] at hx
  have h2 : x⁻¹ * α x = 1 := congrArg Subtype.val hx
  rw [MulAut.one_apply]
  calc α x = x * (x⁻¹ * α x) := by group
    _ = x := by rw [h2, mul_one]

theorem card_mulAut_dvd_of_perfect [Group.IsPerfect X] :
    Nat.card (MulAut X) ∣ Nat.card (MulAut (X ⧸ center X)) :=
  Subgroup.card_dvd_of_injective _ autQuotCenter_injective

theorem false_of_card_mulAut_dvd {n : ℕ} (hn : Nat.card (MulAut X) ∣ n) (h27 : ¬ 27 ∣ n)
    {B : Subgroup (MulAut X)} (hB : ∃ a : ℕ, Nat.card B = 2 ^ a * 27) : False := by
  obtain ⟨a, ha⟩ := hB
  have h1 : 27 ∣ Nat.card B := ⟨2 ^ a, by rw [ha, mul_comm]⟩
  exact h27 (h1.trans ((card_subgroup_dvd_card B).trans hn))

theorem card_mulAut_congr {X' : Type*} [Group X'] (e : X ≃* X') :
    Nat.card (MulAut X) = Nat.card (MulAut X') :=
  Nat.card_congr (MulAut.congr e).toEquiv

end Orders

end CFSG.Quasithin.H13.KG14726

end
