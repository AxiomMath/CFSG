module

public import CFSG.CharacterTheory.Semidihedral.Local.QuaternionNormalForm
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
public import Mathlib.GroupTheory.SemidirectProduct
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

public section

namespace CFSG.Quasithin

namespace S143

namespace SL23

open Subgroup QuaternionGroup CFSG.Semidihedral.Local

section Semi

variable {G G' : Type*} [Group G] [Group G']

abbrev conjHom (Q K : Subgroup G) (hK : K ≤ Subgroup.normalizer (Q : Set G)) : ↥K →* MulAut ↥Q :=
  (Q.normalizerMonoidHom).comp (Subgroup.inclusion hK)

theorem conjHom_apply {Q K : Subgroup G} (hK : K ≤ Subgroup.normalizer (Q : Set G)) (k : ↥K) (q : ↥Q) :
    ((conjHom Q K hK k q : ↥Q) : G) = (k : G) * (q : G) * (k : G)⁻¹ := rfl

theorem monoidHomSubgroup_eq {Q K : Subgroup G} (hK : K ≤ Subgroup.normalizer (Q : Set G))
    (p : (↥Q ⋊[conjHom Q K hK] ↥K)) :
    SemidirectProduct.monoidHomSubgroup hK p = (p.left : G) * (p.right : G) := rfl

theorem monoidHomSubgroup_injective {Q K : Subgroup G} (hK : K ≤ Subgroup.normalizer (Q : Set G))
    (hd : Disjoint Q K) : Function.Injective (SemidirectProduct.monoidHomSubgroup hK) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  rw [monoidHomSubgroup_eq] at hp
  have h1 : (p.left : G) = ((p.right : G))⁻¹ := eq_inv_of_mul_eq_one_left hp
  have hl : (p.left : G) ∈ Q ⊓ K := ⟨p.left.2, by rw [h1]; exact K.inv_mem p.right.2⟩
  rw [disjoint_iff.mp hd] at hl
  have hl1 : p.left = 1 := Subtype.ext (by simpa using hl)
  have hr1 : p.right = 1 := by
    apply Subtype.ext
    have : (p.right : G) = 1 := by
      have := hp
      rw [hl1] at this
      simpa using this
    simpa using this
  refine SemidirectProduct.ext ?_ ?_
  · simpa using hl1
  · simpa using hr1

theorem monoidHomSubgroup_range {Q K : Subgroup G} (hK : K ≤ Subgroup.normalizer (Q : Set G)) :
    (SemidirectProduct.monoidHomSubgroup hK).range = Q ⊔ K := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    rw [monoidHomSubgroup_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left p.left.2) (Subgroup.mem_sup_right p.right.2)
  · intro x hx
    have := Subgroup.coe_mul_of_right_le_normalizer_left Q K hK
    rw [← SetLike.mem_coe, this] at hx
    obtain ⟨n, hn, k, hk, rfl⟩ := hx
    exact ⟨⟨⟨n, hn⟩, ⟨k, hk⟩⟩, rfl⟩

noncomputable def semiEquivSup {Q K : Subgroup G} (hK : K ≤ Subgroup.normalizer (Q : Set G))
    (hd : Disjoint Q K) : (↥Q ⋊[conjHom Q K hK] ↥K) ≃* ↥(Q ⊔ K) :=
  (MonoidHom.ofInjective (monoidHomSubgroup_injective hK hd)).trans
    (MulEquiv.subgroupCongr (monoidHomSubgroup_range hK))

theorem nonempty_mulEquiv_sup {Q K : Subgroup G} {Q' K' : Subgroup G'}
    (hK : K ≤ Subgroup.normalizer (Q : Set G)) (hd : Disjoint Q K)
    (hK' : K' ≤ Subgroup.normalizer (Q' : Set G')) (hd' : Disjoint Q' K')
    (Θ : ↥Q ≃* ↥Q') (Λ : ↥K ≃* ↥K')
    (h : ∀ (k : ↥K) (q : ↥Q), ((Θ (conjHom Q K hK k q) : ↥Q') : G') =
      (Λ k : G') * (Θ q : G') * (Λ k : G')⁻¹) :
    Nonempty (↥(Q ⊔ K) ≃* ↥(Q' ⊔ K')) := by
  have hcongr : ∀ k : ↥K, (conjHom Q K hK k).trans Θ = Θ.trans (conjHom Q' K' hK' (Λ k)) := by
    intro k
    ext q
    exact h k q
  exact ⟨(semiEquivSup hK hd).symm.trans ((SemidirectProduct.congr Θ Λ hcongr).trans
    (semiEquivSup hK' hd'))⟩

end Semi

abbrev SL3 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

def slMk (a b c d : ZMod 3) (h : a * d - b * c = 1 := by decide) : SL3 :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩

def iL : SL3 := slMk 0 2 1 0
def jL : SL3 := slMk 1 1 1 2

theorem iL_pow_four : iL ^ 4 = 1 := by decide
theorem iL_sq_ne : iL ^ 2 ≠ 1 := by decide
theorem jL_sq : jL ^ 2 = iL ^ 2 := by decide
theorem jL_conj : jL * iL * jL⁻¹ = iL⁻¹ := by decide
theorem iL_order : orderOf iL = 4 := by
  refine orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using iL_sq_ne) (by simpa using iL_pow_four)
theorem jL_not_mem : jL ∉ Subgroup.zpowers iL := by
  intro h
  rw [mem_zpowers_iff_mem_range_orderOf, iL_order] at h
  revert h
  decide

section NF

variable {H : Type*} [Group H] {x y : H}

theorem normalFormHom_injective (hx : orderOf x = 4) (hy : y ∉ Subgroup.zpowers x)
    (hx4 : x ^ (2 * 2) = 1) (hy2 : y ^ 2 = x ^ 2) (hyx : y * x * y⁻¹ = x⁻¹) :
    Function.Injective (normalFormHom (m := 2) hx4 hy2 hyx) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rcases g with i | i
  · have h1 : x ^ i.val = 1 := hg
    have h2 : 4 ∣ i.val := by rw [← hx]; exact orderOf_dvd_of_pow_eq_one h1
    have h3 : i.val < 4 := ZMod.val_lt i
    have h4 : i.val = 0 := by omega
    have : i = 0 := (ZMod.val_eq_zero i).mp h4
    rw [this]; rfl
  · exfalso
    apply hy
    have h1 : y * x ^ i.val = 1 := hg
    have : y = (x ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)

end NF

section Q8Facts

theorem q8_rel : ∀ p q : QuaternionGroup 2, p ^ 2 ≠ 1 → p ^ 4 = 1 → q ^ 2 ≠ 1 → q ^ 4 = 1 →
    q ≠ p → q ≠ p⁻¹ → q ^ 2 = p ^ 2 ∧ q * p * q⁻¹ = p⁻¹ := by decide +kernel

theorem q8_third : ∀ p q r : QuaternionGroup 2, p ^ 2 ≠ 1 → p ^ 4 = 1 → q ^ 2 ≠ 1 → q ^ 4 = 1 →
    r ^ 2 ≠ 1 → r ^ 4 = 1 → q ≠ p → q ≠ p⁻¹ → r ≠ p → r ≠ p⁻¹ → r ≠ q → r ≠ q⁻¹ →
    (r = p * q ∨ r = (p * q)⁻¹) := by decide +kernel

end Q8Facts

section Triple

variable {Bg : Type*} [Group Bg]

theorem q8_order_a : orderOf (a 1 : QuaternionGroup 2) = 4 := by
  rw [QuaternionGroup.orderOf_a_one]

theorem q8_order_xa : orderOf (xa 0 : QuaternionGroup 2) = 4 := QuaternionGroup.orderOf_xa 0

theorem sq_ne_pow_four_of_orderOf {H : Type*} [Group H] {p : H} (h : orderOf p = 4) :
    p ^ 2 ≠ 1 ∧ p ^ 4 = 1 := by
  refine ⟨fun h2 => ?_, by rw [← h]; exact pow_orderOf_eq_one p⟩
  have := orderOf_dvd_of_pow_eq_one h2
  rw [h] at this
  omega

theorem exists_triple (e : Bg ≃* QuaternionGroup 2) (α : Bg ≃* Bg)
    (h3 : ∀ b, α (α (α b)) = b) (hne : ∃ b, α b ≠ b) :
    ∃ i : Bg, orderOf i = 4 ∧ α i ∉ Subgroup.zpowers i ∧ α i ^ 2 = i ^ 2 ∧
      α i * i * (α i)⁻¹ = i⁻¹ ∧ (α (α i) = i * α i ∨ α (α i) = (i * α i)⁻¹) := by
  classical
  have : Finite Bg := Finite.of_equiv _ e.symm.toEquiv
  have step_a : ∃ i : Bg, orderOf i = 4 ∧ α i ≠ i := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b, hb⟩ := hne
    have hp : α (e.symm (a 1)) = e.symm (a 1) := by
      by_contra hh
      have := hcon (e.symm (a 1)) (by rw [MulEquiv.orderOf_eq]; exact q8_order_a)
      exact hh this
    have hq : α (e.symm (xa 0)) = e.symm (xa 0) := by
      by_contra hh
      have := hcon (e.symm (xa 0)) (by rw [MulEquiv.orderOf_eq]; exact q8_order_xa)
      exact hh this
    have hhom : α.toMonoidHom.comp e.symm.toMonoidHom = e.symm.toMonoidHom :=
      quaternion_eq_of_generators (by simpa using hp) (by simpa using hq)
    apply hb
    have := congrArg (fun f : QuaternionGroup 2 →* Bg => f (e b)) hhom
    simpa using this
  obtain ⟨i, hi4, hi⟩ := step_a
  have hα_order : ∀ b, orderOf (α b) = orderOf b := fun b => MulEquiv.orderOf_eq α b
  have hinv : α i ≠ i⁻¹ := by
    intro h
    have h1 : α (α i) = i := by rw [h, map_inv, h, inv_inv]
    have h2 : α (α (α i)) = α i := by rw [h1]
    rw [h3] at h2
    exact hi h2.symm
  have hnot : α i ∉ Subgroup.zpowers i := by
    intro hmem
    rw [mem_zpowers_iff_mem_range_orderOf, hi4] at hmem
    simp only [Finset.mem_image, Finset.mem_range] at hmem
    obtain ⟨n, hn, hn'⟩ := hmem
    have hio := sq_ne_pow_four_of_orderOf hi4
    have hjo : orderOf (α i) = 4 := by rw [hα_order, hi4]
    have hjo' := sq_ne_pow_four_of_orderOf hjo
    interval_cases n
    · apply hjo'.1; rw [← hn']; simp
    · exact hi (by simpa using hn'.symm)
    · apply hjo'.1; rw [← hn', ← pow_mul]
      have : i ^ (2 * 2) = 1 := by simpa using hio.2
      exact this
    · apply hinv; rw [← hn']
      have : i ^ 4 = 1 := hio.2
      calc i ^ 3 = i ^ 3 * (i ^ 1 * (i ^ 1)⁻¹) := by group
        _ = (i ^ 3 * i ^ 1) * (i ^ 1)⁻¹ := by group
        _ = i⁻¹ := by
          rw [← pow_add, this]; group
  have hio := sq_ne_pow_four_of_orderOf hi4
  have hjo : orderOf (α i) = 4 := by rw [hα_order, hi4]
  have hjo' := sq_ne_pow_four_of_orderOf hjo
  have hko : orderOf (α (α i)) = 4 := by rw [hα_order, hα_order, hi4]
  have hko' := sq_ne_pow_four_of_orderOf hko
  have hpo : orderOf (e i) = 4 := by rw [MulEquiv.orderOf_eq]; exact hi4
  have hqo : orderOf (e (α i)) = 4 := by rw [MulEquiv.orderOf_eq]; exact hjo
  have hro : orderOf (e (α (α i))) = 4 := by rw [MulEquiv.orderOf_eq]; exact hko
  have hpo' := sq_ne_pow_four_of_orderOf hpo
  have hqo' := sq_ne_pow_four_of_orderOf hqo
  have hro' := sq_ne_pow_four_of_orderOf hro
  have hqp : e (α i) ≠ e i := fun h => hi (e.injective h)
  have hqp' : e (α i) ≠ (e i)⁻¹ := fun h => hinv (e.injective (by rw [h, map_inv]))
  obtain ⟨hrel1, hrel2⟩ := q8_rel (e i) (e (α i)) hpo'.1 hpo'.2 hqo'.1 hqo'.2 hqp hqp'
  have hrel1' : α i ^ 2 = i ^ 2 := e.injective (by rw [map_pow, map_pow]; exact hrel1)
  have hrel2' : α i * i * (α i)⁻¹ = i⁻¹ := e.injective (by
    rw [map_mul, map_mul, map_inv, map_inv]; exact hrel2)
  have hk1 : α (α i) ≠ i := by
    intro h
    have h2 : α (α (α i)) = α i := by rw [h]
    rw [h3] at h2
    exact hi h2.symm
  have hk2 : α (α i) ≠ i⁻¹ := by
    intro h
    have h2 : α (α (α i)) = α i⁻¹ := by rw [h]
    rw [h3, map_inv] at h2
    exact hinv (inv_eq_iff_eq_inv.mp h2.symm)
  have hk3 : α (α i) ≠ α i := by
    intro h
    have h2 : α (α (α i)) = α (α i) := congrArg α h
    rw [h3] at h2
    exact hi (h.symm.trans h2.symm)
  have hk4 : α (α i) ≠ (α i)⁻¹ := by
    intro h
    have h2 : α (α (α i)) = α ((α i)⁻¹) := congrArg α h
    rw [h3, map_inv, h, inv_inv] at h2
    exact hi h2.symm
  have hr1 : e (α (α i)) ≠ e i := fun h => hk1 (e.injective h)
  have hr2 : e (α (α i)) ≠ (e i)⁻¹ := fun h => hk2 (e.injective (by rw [h, map_inv]))
  have hr3 : e (α (α i)) ≠ e (α i) := fun h => hk3 (e.injective h)
  have hr4 : e (α (α i)) ≠ (e (α i))⁻¹ := fun h => hk4 (e.injective (by rw [h, map_inv]))
  have hthird := q8_third (e i) (e (α i)) (e (α (α i))) hpo'.1 hpo'.2 hqo'.1 hqo'.2 hro'.1 hro'.2
    hqp hqp' hr1 hr2 hr3 hr4
  refine ⟨i, hi4, hnot, hrel1', hrel2', ?_⟩
  rcases hthird with h | h
  · left
    exact e.injective (by rw [h, map_mul])
  · right
    exact e.injective (by rw [h, map_inv, map_mul])

end Triple

section Concrete

@[expose] noncomputable def phiL : QuaternionGroup 2 →* SL3 :=
  normalFormHom (m := 2) (x := iL) (y := jL) (by simpa using iL_pow_four) jL_sq jL_conj

theorem phiL_a (n : ZMod 4) : phiL (a n) = iL ^ n.val := rfl

theorem phiL_xa (n : ZMod 4) : phiL (xa n) = jL * iL ^ n.val := rfl

theorem phiL_a_one : phiL (a 1) = iL := by
  rw [phiL_a]
  have : (1 : ZMod 4).val = 1 := by decide
  rw [this, pow_one]

theorem phiL_xa_zero : phiL (xa 0) = jL := by
  rw [phiL_xa, ZMod.val_zero, pow_zero, mul_one]

theorem phiL_injective : Function.Injective phiL :=
  normalFormHom_injective iL_order jL_not_mem _ jL_sq jL_conj

theorem iL_ne_jL : iL ≠ jL := by decide

theorem card_sl3 : Nat.card SL3 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem exists_omegaL (κ : QuaternionGroup 2) (hκ : κ = a 1 * xa 0 ∨ κ = (a 1 * xa 0)⁻¹) :
    ∃ ω : SL3, ω ^ 3 = 1 ∧ ω * iL * ω⁻¹ = jL ∧ ω * jL * ω⁻¹ = phiL κ := by
  rcases hκ with rfl | rfl
  · rw [map_mul, phiL_a_one, phiL_xa_zero]
    have : ∃ ω : SL3, ω ^ 3 = 1 ∧ ω * iL * ω⁻¹ = jL ∧ ω * jL * ω⁻¹ = iL * jL := by decide
    exact this
  · rw [map_inv, map_mul, phiL_a_one, phiL_xa_zero]
    have : ∃ ω : SL3, ω ^ 3 = 1 ∧ ω * iL * ω⁻¹ = jL ∧ ω * jL * ω⁻¹ = (iL * jL)⁻¹ := by decide
    exact this

end Concrete

section Cyclic

variable {G G' : Type*} [Group G] [Group G']

noncomputable def cycEquiv {x : G} {y : G'} (hx : IsOfFinOrder x) (hy : IsOfFinOrder y)
    (h : orderOf x = orderOf y) : ↥(Subgroup.zpowers x) ≃ ↥(Subgroup.zpowers y) :=
  (finEquivZPowers hx).symm.trans ((finCongr h).trans (finEquivZPowers hy))

theorem cycEquiv_apply {x : G} {y : G'} (hx : IsOfFinOrder x) (hy : IsOfFinOrder y)
    (h : orderOf x = orderOf y) (n : ℕ) :
    cycEquiv hx hy h ⟨x ^ n, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) n⟩ =
      ⟨y ^ n, Subgroup.pow_mem _ (Subgroup.mem_zpowers y) n⟩ := by
  have e1 : (⟨x ^ n, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) n⟩ : ↥(Subgroup.zpowers x)) =
      ⟨x ^ n, ⟨n, by simp⟩⟩ := rfl
  rw [cycEquiv, Equiv.trans_apply, Equiv.trans_apply, e1, finEquivZPowers_symm_apply]
  apply Subtype.ext
  show y ^ (n % orderOf x) = y ^ n
  rw [h]
  exact pow_mod_orderOf y n

noncomputable def cycMulEquiv {x : G} {y : G'} (hx : IsOfFinOrder x) (hy : IsOfFinOrder y)
    (h : orderOf x = orderOf y) : ↥(Subgroup.zpowers x) ≃* ↥(Subgroup.zpowers y) :=
  MulEquiv.mk' (cycEquiv hx hy h) (by
    intro a b
    obtain ⟨m, hm⟩ := (hx.mem_powers_iff_mem_zpowers).mpr a.2
    obtain ⟨n, hn⟩ := (hx.mem_powers_iff_mem_zpowers).mpr b.2
    have ha : a = ⟨x ^ m, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) m⟩ := Subtype.ext hm.symm
    have hb : b = ⟨x ^ n, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) n⟩ := Subtype.ext hn.symm
    have hab : a * b = ⟨x ^ (m + n), Subgroup.pow_mem _ (Subgroup.mem_zpowers x) (m + n)⟩ := by
      rw [ha, hb]
      exact Subtype.ext (by simp [pow_add])
    rw [hab, ha, hb, cycEquiv_apply, cycEquiv_apply, cycEquiv_apply]
    exact Subtype.ext (by simp [pow_add]))

theorem cycMulEquiv_apply {x : G} {y : G'} (hx : IsOfFinOrder x) (hy : IsOfFinOrder y)
    (h : orderOf x = orderOf y) (n : ℕ) :
    cycMulEquiv hx hy h ⟨x ^ n, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) n⟩ =
      ⟨y ^ n, Subgroup.pow_mem _ (Subgroup.mem_zpowers y) n⟩ :=
  cycEquiv_apply hx hy h n

end Cyclic

section Recognition

variable {G : Type*} [Group G]

theorem nonempty_mulEquiv_sl23 {B : Subgroup G} {ω : G}
    (hB : Nonempty (↥B ≃* QuaternionGroup 2)) (hω3 : orderOf ω = 3)
    (hn : ∀ b ∈ B, ω * b * ω⁻¹ ∈ B) (hnt : ∃ b ∈ B, ω * b * ω⁻¹ ≠ b) :
    Nonempty (↥(B ⊔ Subgroup.zpowers ω) ≃* SL3) := by
  classical
  obtain ⟨eB⟩ := hB
  have hωpow : ω ^ 3 = 1 := by rw [← hω3]; exact pow_orderOf_eq_one ω
  have hωωω : ω * ω * ω = 1 := by rw [← pow_three']; exact hωpow
  have hn' : ∀ b ∈ B, ω⁻¹ * b * ω ∈ B := fun b hb => by
    have e : ω⁻¹ * b * ω = ω * (ω * b * ω⁻¹) * ω⁻¹ := by
      calc ω⁻¹ * b * ω = (ω * ω * ω) * (ω⁻¹ * b * ω) * (ω * ω * ω)⁻¹ := by rw [hωωω]; group
        _ = ω * (ω * b * ω⁻¹) * ω⁻¹ := by group
    rw [e]
    exact hn _ (hn b hb)
  let α : ↥B ≃* ↥B :=
    { toFun := fun b => ⟨ω * b * ω⁻¹, hn b b.2⟩
      invFun := fun b => ⟨ω⁻¹ * b * ω, hn' b b.2⟩
      left_inv := fun b => Subtype.ext (by
        show ω⁻¹ * (ω * (b : G) * ω⁻¹) * ω = b
        group)
      right_inv := fun b => Subtype.ext (by
        show ω * (ω⁻¹ * (b : G) * ω) * ω⁻¹ = b
        group)
      map_mul' := fun a b => Subtype.ext (by
        show ω * ((a : G) * (b : G)) * ω⁻¹ = ω * (a : G) * ω⁻¹ * (ω * (b : G) * ω⁻¹)
        group) }
  have hα : ∀ b : ↥B, ((α b : ↥B) : G) = ω * (b : G) * ω⁻¹ := fun b => rfl
  have h3 : ∀ b, α (α (α b)) = b := fun b => Subtype.ext (by
    rw [hα, hα, hα]
    calc ω * (ω * (ω * (b : G) * ω⁻¹) * ω⁻¹) * ω⁻¹ = (ω * ω * ω) * (b : G) * (ω * ω * ω)⁻¹ := by
          group
      _ = b := by rw [hωωω]; group)
  have hne : ∃ b, α b ≠ b := by
    obtain ⟨b, hb, hbne⟩ := hnt
    exact ⟨⟨b, hb⟩, fun h => hbne (congrArg Subtype.val h)⟩
  obtain ⟨i, hi4, hnot, hj2, hji, hk⟩ := exists_triple eB α h3 hne
  have hx4 : i ^ (2 * 2) = 1 := by
    have := (sq_ne_pow_four_of_orderOf hi4).2
    simpa using this
  let φB : QuaternionGroup 2 →* ↥B := normalFormHom (m := 2) (x := i) (y := α i) hx4 hj2 hji
  have hφB_a : φB (a 1) = i := by
    show i ^ (1 : ZMod 4).val = i
    have : (1 : ZMod 4).val = 1 := by decide
    rw [this, pow_one]
  have hφB_xa : φB (xa 0) = α i := by
    show α i * i ^ (0 : ZMod 4).val = α i
    rw [ZMod.val_zero, pow_zero, mul_one]
  have hφB_inj : Function.Injective φB := normalFormHom_injective hi4 hnot hx4 hj2 hji
  have hfinB : Finite ↥B := Finite.of_equiv _ eB.symm.toEquiv
  have hcardQ8 : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcardB : Nat.card ↥B = 8 := by rw [Nat.card_congr eB.toEquiv, hcardQ8]
  have hbij : Function.Bijective φB :=
    Function.Injective.bijective_of_nat_card_le hφB_inj (by rw [hcardB, hcardQ8])
  let φBe : QuaternionGroup 2 ≃* ↥B := MulEquiv.ofBijective φB hbij
  let Θ : ↥B ≃* ↥(phiL.range) := φBe.symm.trans (MonoidHom.ofInjective phiL_injective)
  have hΘ : ∀ g, ((Θ (φB g) : ↥(phiL.range)) : SL3) = phiL g := fun g => by
    show ((MonoidHom.ofInjective phiL_injective (φBe.symm (φB g))) : SL3) = phiL g
    have : φBe.symm (φB g) = g := φBe.symm_apply_apply g
    rw [this]
    rfl
  obtain ⟨κ, hκ, hκB⟩ : ∃ κ : QuaternionGroup 2, (κ = a 1 * xa 0 ∨ κ = (a 1 * xa 0)⁻¹) ∧
      α (α i) = φB κ := by
    rcases hk with h | h
    · exact ⟨a 1 * xa 0, Or.inl rfl, by rw [map_mul, hφB_a, hφB_xa, h]⟩
    · exact ⟨(a 1 * xa 0)⁻¹, Or.inr rfl, by rw [map_inv, map_mul, hφB_a, hφB_xa, h]⟩
  obtain ⟨ωL, hωL3, hωLi, hωLj⟩ := exists_omegaL κ hκ
  have E1 : ∀ q : ↥B, ((Θ (α q) : ↥(phiL.range)) : SL3) =
      ωL * ((Θ q : ↥(phiL.range)) : SL3) * ωL⁻¹ := by
    intro q
    obtain ⟨g, rfl⟩ := hbij.2 q
    rw [hΘ]
    let ψ₁ : QuaternionGroup 2 →* SL3 :=
      (phiL.range).subtype.comp (Θ.toMonoidHom.comp (α.toMonoidHom.comp φB))
    let ψ₂ : QuaternionGroup 2 →* SL3 := (MulAut.conj ωL).toMonoidHom.comp phiL
    have hψ : ψ₁ = ψ₂ := by
      refine quaternion_eq_of_generators ?_ ?_
      · show ((Θ (α (φB (a 1))) : ↥(phiL.range)) : SL3) = ωL * phiL (a 1) * ωL⁻¹
        rw [hφB_a, ← hφB_xa, hΘ, phiL_xa_zero, phiL_a_one, hωLi]
      · show ((Θ (α (φB (xa 0))) : ↥(phiL.range)) : SL3) = ωL * phiL (xa 0) * ωL⁻¹
        rw [hφB_xa, hκB, hΘ, phiL_xa_zero, hωLj]
    have := congrArg (fun f : QuaternionGroup 2 →* SL3 => f g) hψ
    simpa [ψ₁, ψ₂] using this
  have E2 : ∀ (m : ℕ) (q : ↥B), ((Θ ((⇑α)^[m] q) : ↥(phiL.range)) : SL3) =
      ωL ^ m * ((Θ q : ↥(phiL.range)) : SL3) * (ωL ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro q; simp
    | succ m ih =>
      intro q
      rw [Function.iterate_succ_apply', E1, ih]
      group
  have E3 : ∀ (m : ℕ) (q : ↥B), (((⇑α)^[m] q : ↥B) : G) = ω ^ m * (q : G) * (ω ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro q; simp
    | succ m ih =>
      intro q
      rw [Function.iterate_succ_apply', hα, ih]
      group
  have hωN : ω ∈ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hn h hh, fun hh => ?_⟩
    have := hn' _ hh
    have e : ω⁻¹ * (ω * h * ω⁻¹) * ω = h := by group
    rwa [e] at this
  have hK : Subgroup.zpowers ω ≤ Subgroup.normalizer (B : Set G) := Subgroup.zpowers_le.mpr hωN
  have hKcard : Nat.card ↥(Subgroup.zpowers ω) = 3 := by rw [Nat.card_zpowers, hω3]
  have hd : Disjoint B (Subgroup.zpowers ω) :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hcardB, hKcard]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hωL1 : ωL ≠ 1 := by
    intro h
    rw [h] at hωLi
    simp only [one_mul, inv_one, mul_one] at hωLi
    exact iL_ne_jL hωLi
  have hωLord : orderOf ωL = 3 := orderOf_eq_prime hωL3 hωL1
  have hKLcard : Nat.card ↥(Subgroup.zpowers ωL) = 3 := by rw [Nat.card_zpowers, hωLord]
  have hQLcard : Nat.card ↥(phiL.range) = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective phiL_injective).toEquiv, hcardQ8]
  have hωLconj : ∀ y ∈ phiL.range, ωL * y * ωL⁻¹ ∈ phiL.range := by
    rintro _ ⟨g, rfl⟩
    have hpowj : ∀ k : ℕ, ωL * iL ^ k * ωL⁻¹ = jL ^ k := fun k => by rw [← conj_pow, hωLi]
    rcases g with n | n
    · have : ωL * phiL (a n) * ωL⁻¹ = phiL ((xa 0 : QuaternionGroup 2) ^ n.val) := by
        rw [phiL_a, map_pow, phiL_xa_zero, hpowj]
      exact ⟨_, this.symm⟩
    · have : ωL * phiL (xa n) * ωL⁻¹ = phiL (κ * (xa 0 : QuaternionGroup 2) ^ n.val) := by
        rw [phiL_xa, map_mul, map_pow, phiL_xa_zero]
        calc ωL * (jL * iL ^ n.val) * ωL⁻¹ = (ωL * jL * ωL⁻¹) * (ωL * iL ^ n.val * ωL⁻¹) := by
              group
          _ = phiL κ * jL ^ n.val := by rw [hωLj, hpowj]
      exact ⟨_, this.symm⟩
  have hωLN : ωL ∈ Subgroup.normalizer ((phiL.range : Subgroup SL3) : Set SL3) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hωLconj h hh, fun hh => ?_⟩
    have hωωω' : ωL * ωL * ωL = 1 := by rw [← pow_three']; exact hωL3
    have e : h = ωL * (ωL * (ωL * h * ωL⁻¹) * ωL⁻¹) * ωL⁻¹ := by
      calc h = (ωL * ωL * ωL) * h * (ωL * ωL * ωL)⁻¹ := by rw [hωωω']; group
        _ = ωL * (ωL * (ωL * h * ωL⁻¹) * ωL⁻¹) * ωL⁻¹ := by group
    rw [e]
    exact hωLconj _ (hωLconj _ hh)
  have hK' : Subgroup.zpowers ωL ≤ Subgroup.normalizer ((phiL.range : Subgroup SL3) : Set SL3) :=
    Subgroup.zpowers_le.mpr hωLN
  have hd' : Disjoint phiL.range (Subgroup.zpowers ωL) :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hQLcard, hKLcard]; norm_num)
  have hsup : phiL.range ⊔ Subgroup.zpowers ωL = ⊤ := by
    have h8 : 8 ∣ Nat.card ↥(phiL.range ⊔ Subgroup.zpowers ωL) := by
      have := Subgroup.card_dvd_of_le (le_sup_left : phiL.range ≤ phiL.range ⊔ Subgroup.zpowers ωL)
      rwa [hQLcard] at this
    have h3' : 3 ∣ Nat.card ↥(phiL.range ⊔ Subgroup.zpowers ωL) := by
      have := Subgroup.card_dvd_of_le
        (le_sup_right : Subgroup.zpowers ωL ≤ phiL.range ⊔ Subgroup.zpowers ωL)
      rwa [hKLcard] at this
    have hle : Nat.card ↥(phiL.range ⊔ Subgroup.zpowers ωL) ∣ 24 := by
      have := Subgroup.card_subgroup_dvd_card (phiL.range ⊔ Subgroup.zpowers ωL)
      rwa [card_sl3] at this
    have hpos : 0 < Nat.card ↥(phiL.range ⊔ Subgroup.zpowers ωL) := Nat.card_pos
    apply Subgroup.eq_top_of_card_eq
    have := Nat.le_of_dvd (by norm_num) hle
    rw [card_sl3]
    omega
  let Λ : ↥(Subgroup.zpowers ω) ≃* ↥(Subgroup.zpowers ωL) :=
    cycMulEquiv (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hωpow⟩)
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hωL3⟩) (by rw [hω3, hωLord])
  have hΛ : ∀ m : ℕ, ((Λ ⟨ω ^ m, Subgroup.pow_mem _ (Subgroup.mem_zpowers ω) m⟩ :
      ↥(Subgroup.zpowers ωL)) : SL3) = ωL ^ m := fun m => by
    have := cycMulEquiv_apply (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hωpow⟩)
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hωL3⟩) (by rw [hω3, hωLord]) m
    exact congrArg Subtype.val this
  have hequi : ∀ (k : ↥(Subgroup.zpowers ω)) (q : ↥B),
      ((Θ (conjHom B (Subgroup.zpowers ω) hK k q) : ↥(phiL.range)) : SL3) =
        (Λ k : SL3) * ((Θ q : ↥(phiL.range)) : SL3) * (Λ k : SL3)⁻¹ := by
    intro k q
    obtain ⟨m, hm⟩ := (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hωpow⟩ :
      IsOfFinOrder ω).mem_powers_iff_mem_zpowers.mpr k.2
    have hk : k = ⟨ω ^ m, Subgroup.pow_mem _ (Subgroup.mem_zpowers ω) m⟩ := Subtype.ext hm.symm
    have hcj : conjHom B (Subgroup.zpowers ω) hK k q = (⇑α)^[m] q := by
      apply Subtype.ext
      rw [conjHom_apply, E3, hk]
    rw [hcj, E2, hk, hΛ]
  obtain ⟨e⟩ := nonempty_mulEquiv_sup hK hd hK' hd' Θ Λ hequi
  exact ⟨e.trans ((MulEquiv.subgroupCongr hsup).trans Subgroup.topEquiv)⟩

end Recognition

end SL23

end S143

end CFSG.Quasithin
