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

namespace CFSG.Quasithin.EmptyFaithfulMultiple

section ElemSq

variable {E : Type*} [Group E] {p : ℕ}

structure IsElemSq (p : ℕ) (E : Type*) [Group E] : Prop where
  comm : ∀ a b : E, a * b = b * a
  pow : ∀ a : E, a ^ p = 1
  card : Nat.card E = p ^ 2

theorem mulAut_comm_of_isCyclic {C : Type*} [Group C] [IsCyclic C] (a b : MulAut C) :
    a * b = b * a := by
  apply (IsCyclic.mulAutMulEquiv C).injective
  rw [map_mul, map_mul, mul_comm]

variable [hp : Fact p.Prime]

theorem IsElemSq.finite (hE : IsElemSq p E) : Finite E :=
  Nat.finite_of_card_ne_zero (by rw [hE.card]; exact pow_ne_zero 2 hp.out.ne_zero)

omit hp in
theorem IsElemSq.normal (hE : IsElemSq p E) (L : Subgroup E) : L.Normal :=
  ⟨fun n hn g => by rw [hE.comm g n, mul_inv_cancel_right]; exact hn⟩

theorem eq_zpowers_of_card_eq_prime {L : Subgroup E} (hL : Nat.card L = p) {l : E}
    (hlL : l ∈ L) (hl1 : l ≠ 1) : L = Subgroup.zpowers l := by
  have : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; exact hp.out.ne_zero)
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hlL) ?_
  rw [hL, Nat.card_zpowers]
  have h1 : orderOf l ∣ p := hL ▸ Subgroup.orderOf_dvd_natCard L hlL
  have h2 : orderOf l ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  rcases (Nat.dvd_prime hp.out).mp h1 with h | h
  · exact absurd h h2
  · rw [h]

theorem exists_ne_one_of_card_eq_prime {L : Subgroup E} (hL : Nat.card L = p) :
    ∃ l ∈ L, l ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : L = ⊥ := (Subgroup.eq_bot_iff_forall L).mpr hcon
  rw [this, Subgroup.card_bot] at hL
  exact hp.out.one_lt.ne hL

theorem inf_eq_bot_of_card_eq_prime {L L' : Subgroup E} (hL : Nat.card L = p)
    (hL' : Nat.card L' = p) (hne : L ≠ L') : L ⊓ L' = ⊥ := by
  rw [eq_bot_iff]
  rintro l ⟨h1, h2⟩
  by_contra hl
  exact hne ((eq_zpowers_of_card_eq_prime hL h1 hl).trans
    (eq_zpowers_of_card_eq_prime hL' h2 hl).symm)

theorem IsElemSq.eq_top_of_lt (hE : IsElemSq p E) {L M' : Subgroup E} (hL : Nat.card L = p)
    (hLM : L ≤ M') (hne : ¬ M' ≤ L) : M' = ⊤ := by
  have := hE.finite
  have hdvd : Nat.card M' ∣ p ^ 2 := hE.card ▸ Subgroup.card_subgroup_dvd_card M'
  obtain ⟨k, hk, hkM⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  have hge : p ≤ Nat.card M' := hL ▸ Subgroup.card_le_of_le hLM
  interval_cases k
  · rw [pow_zero] at hkM
    have := hp.out.one_lt
    omega
  · rw [pow_one] at hkM
    exact absurd (Subgroup.eq_of_le_of_card_ge hLM (by rw [hkM, hL])).symm.le hne
  · exact Subgroup.eq_top_of_card_eq M' (hkM.trans hE.card.symm)

theorem IsElemSq.exists_mul_of_ne (hE : IsElemSq p E) {L₁ L₂ : Subgroup E}
    (h₁ : Nat.card L₁ = p) (h₂ : Nat.card L₂ = p) (hne : L₁ ≠ L₂) (y : E) :
    ∃ m₁ ∈ L₁, ∃ m₂ ∈ L₂, y = m₁ * m₂ := by
  have := hE.normal L₂
  have := hE.finite
  have htop : L₁ ⊔ L₂ = ⊤ := by
    refine hE.eq_top_of_lt h₂ le_sup_right fun h => hne ?_
    exact Subgroup.eq_of_le_of_card_ge (le_sup_left.trans h) (by rw [h₁, h₂])
  have hy : y ∈ ((L₁ ⊔ L₂ : Subgroup E) : Set E) := by
    rw [htop]
    exact Subgroup.mem_top y
  rw [Subgroup.mul_normal] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hy
  exact ⟨a, ha, b, hb, rfl⟩

theorem map_eq_of_mapsTo {L : Subgroup E} [Finite L] {α : MulAut E} (h : ∀ l ∈ L, α l ∈ L) :
    L.map (α : E →* E) = L := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨l, hl, rfl⟩
    exact h l hl
  · rw [Subgroup.card_map_of_injective α.injective]

theorem inv_mapsTo {L : Subgroup E} [Finite L] {α : MulAut E} (h : ∀ l ∈ L, α l ∈ L) :
    ∀ l ∈ L, α⁻¹ l ∈ L := by
  intro l hl
  rw [← map_eq_of_mapsTo h] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  simpa using hl'

theorem exists_zpow_on_line {L : Subgroup E} (hL : Nat.card L = p) {α : MulAut E}
    (h : ∀ l ∈ L, α l ∈ L) : ∃ a : ℤ, ∀ l ∈ L, α l = l ^ a := by
  obtain ⟨l₀, hl₀, hl₀1⟩ := exists_ne_one_of_card_eq_prime hL
  have hLz := eq_zpowers_of_card_eq_prime hL hl₀ hl₀1
  have hα₀ := h l₀ hl₀
  rw [hLz] at hα₀
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hα₀
  refine ⟨a, fun l hl => ?_⟩
  rw [hLz] at hl
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
  rw [map_zpow, ← ha, ← zpow_mul, ← zpow_mul, mul_comm]

theorem IsElemSq.commutator_trivial (hE : IsElemSq p E) {L : Subgroup E} (hL : Nat.card L = p)
    {α β : MulAut E} (hα : ∀ l ∈ L, α l ∈ L) (hβ : ∀ l ∈ L, β l ∈ L) :
    (∀ l ∈ L, (α * β * α⁻¹ * β⁻¹) l = l) ∧ ∀ y, (α * β * α⁻¹ * β⁻¹) y * y⁻¹ ∈ L := by
  have : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; exact hp.out.ne_zero)
  have := hE.finite
  have := hE.normal L
  have hαm := map_eq_of_mapsTo hα
  have hβm := map_eq_of_mapsTo hβ
  have hα'm := map_eq_of_mapsTo (inv_mapsTo hα)
  have hβ'm := map_eq_of_mapsTo (inv_mapsTo hβ)
  constructor
  ·
    have : IsCyclic L := isCyclic_of_prime_card hL
    let res : ∀ γ : MulAut E, L.map (γ : E →* E) = L → MulAut L := fun γ hγ =>
      (γ.subgroupMap L).trans (MulEquiv.subgroupCongr hγ)
    have hres : ∀ γ hγ (l : L), ((res γ hγ l : L) : E) = γ l := fun _ _ _ => rfl
    have hinv : ∀ γ hγ hγ', res γ⁻¹ hγ' = (res γ hγ)⁻¹ := by
      intro γ hγ hγ'
      rw [eq_inv_iff_mul_eq_one]
      ext l
      simp [hres]
    intro l hl
    have key : res α hαm * res β hβm * res α⁻¹ hα'm * res β⁻¹ hβ'm = 1 := by
      rw [hinv α hαm hα'm, hinv β hβm hβ'm, mulAut_comm_of_isCyclic (res α hαm)]
      group
    have := congrArg (fun γ : MulAut L => ((γ ⟨l, hl⟩ : L) : E)) key
    simpa [hres] using this
  ·
    have hcard : Nat.card (E ⧸ L) = p := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup L
      rw [hE.card, hL, pow_two] at h1
      exact (Nat.eq_of_mul_eq_mul_right hp.out.pos h1).symm
    have : IsCyclic (E ⧸ L) := isCyclic_of_prime_card hcard
    let ind : ∀ γ : MulAut E, L.map (γ : E →* E) = L → MulAut (E ⧸ L) := fun γ hγ =>
      QuotientGroup.congr L L γ hγ
    have hind : ∀ γ hγ (y : E), ind γ hγ (y : E ⧸ L) = ((γ y : E) : E ⧸ L) :=
      fun γ hγ y => QuotientGroup.congr_mk L L γ hγ y
    have hinv : ∀ γ hγ hγ', ind γ⁻¹ hγ' = (ind γ hγ)⁻¹ := by
      intro γ hγ hγ'
      rw [eq_inv_iff_mul_eq_one]
      ext q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      simp [hind]
    intro y
    have key : ind α hαm * ind β hβm * ind α⁻¹ hα'm * ind β⁻¹ hβ'm = 1 := by
      rw [hinv α hαm hα'm, hinv β hβm hβ'm, mulAut_comm_of_isCyclic (ind α hαm)]
      group
    have h1 := congrArg (fun γ : MulAut (E ⧸ L) => γ (y : E ⧸ L)) key
    simp only [MulAut.mul_apply, hind, MulAut.one_apply] at h1
    have h2 := QuotientGroup.eq.mp h1
    have h3 := L.inv_mem h2
    rwa [mul_inv_rev, inv_inv, hE.comm] at h3

omit hp in
theorem IsElemSq.pow_eq_one_of_trivial (hE : IsElemSq p E) {L : Subgroup E} {c : MulAut E}
    (h1 : ∀ l ∈ L, c l = l) (h2 : ∀ y, c y * y⁻¹ ∈ L) : c ^ p = 1 := by
  ext y
  set ℓ := c y * y⁻¹ with hℓ
  have hcℓ : c ℓ = ℓ := h1 ℓ (h2 y)
  have hcy : c y = ℓ * y := by rw [hℓ]; group
  have key : ∀ n : ℕ, (c ^ n) y = ℓ ^ n * y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hcℓ, hcy, pow_succ]
      group
  rw [key, hE.pow, one_mul, MulAut.one_apply]

theorem IsElemSq.eq_zpow_of_three_lines (hE : IsElemSq p E) {α : MulAut E}
    {L₁ L₂ L₃ : Subgroup E} (h₁ : Nat.card L₁ = p) (h₂ : Nat.card L₂ = p) (h₃ : Nat.card L₃ = p)
    (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) (hα₁ : ∀ l ∈ L₁, α l ∈ L₁)
    (hα₂ : ∀ l ∈ L₂, α l ∈ L₂) (hα₃ : ∀ l ∈ L₃, α l ∈ L₃) : ∃ k : ℤ, ∀ y, α y = y ^ k := by
  obtain ⟨a₁, ha₁⟩ := exists_zpow_on_line h₁ hα₁
  obtain ⟨a₂, ha₂⟩ := exists_zpow_on_line h₂ hα₂
  obtain ⟨a₃, ha₃⟩ := exists_zpow_on_line h₃ hα₃
  obtain ⟨l₃, hl₃, hl₃1⟩ := exists_ne_one_of_card_eq_prime h₃
  obtain ⟨m₁, hm₁, m₂, hm₂, hl₃eq⟩ := hE.exists_mul_of_ne h₁ h₂ h12 l₃
  have hm₁1 : m₁ ≠ 1 := by
    rintro rfl
    rw [one_mul] at hl₃eq
    subst hl₃eq
    exact h23 ((eq_zpowers_of_card_eq_prime h₂ hm₂ hl₃1).trans
      (eq_zpowers_of_card_eq_prime h₃ hl₃ hl₃1).symm)
  have hm₂1 : m₂ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hl₃eq
    subst hl₃eq
    exact h13 ((eq_zpowers_of_card_eq_prime h₁ hm₁ hl₃1).trans
      (eq_zpowers_of_card_eq_prime h₃ hl₃ hl₃1).symm)
  have hcomm : ∀ (a b : E) (k : ℤ), (a * b) ^ k = a ^ k * b ^ k := fun a b k =>
    (Commute.mul_zpow (hE.comm a b) k)
  have heq : m₁ ^ a₁ * m₂ ^ a₂ = m₁ ^ a₃ * m₂ ^ a₃ := by
    rw [← ha₁ m₁ hm₁, ← ha₂ m₂ hm₂, ← map_mul, ← hl₃eq, ha₃ l₃ hl₃, hl₃eq, hcomm]
  have hrel : (m₁ ^ a₃)⁻¹ * m₁ ^ a₁ = m₂ ^ a₃ * (m₂ ^ a₂)⁻¹ := by
    calc (m₁ ^ a₃)⁻¹ * m₁ ^ a₁ = (m₁ ^ a₃)⁻¹ * (m₁ ^ a₁ * m₂ ^ a₂) * (m₂ ^ a₂)⁻¹ := by group
      _ = (m₁ ^ a₃)⁻¹ * (m₁ ^ a₃ * m₂ ^ a₃) * (m₂ ^ a₂)⁻¹ := by rw [heq]
      _ = m₂ ^ a₃ * (m₂ ^ a₂)⁻¹ := by group
  have hint' : (m₁ ^ a₃)⁻¹ * m₁ ^ a₁ ∈ L₁ ⊓ L₂ := by
    refine ⟨L₁.mul_mem (L₁.inv_mem (L₁.zpow_mem hm₁ _)) (L₁.zpow_mem hm₁ _), ?_⟩
    rw [hrel]
    exact L₂.mul_mem (L₂.zpow_mem hm₂ _) (L₂.inv_mem (L₂.zpow_mem hm₂ _))
  rw [inf_eq_bot_of_card_eq_prime h₁ h₂ h12, Subgroup.mem_bot] at hint'
  have hint : m₁ ^ a₁ = m₁ ^ a₃ := (inv_mul_eq_one.mp hint').symm
  have hint₂ : m₂ ^ a₂ = m₂ ^ a₃ := by
    rw [hint'] at hrel
    exact (mul_inv_eq_one.mp hrel.symm).symm
  have hL₁ : ∀ l ∈ L₁, α l = l ^ a₃ := by
    intro l hl
    rw [eq_zpowers_of_card_eq_prime h₁ hm₁ hm₁1] at hl
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
    rw [ha₁ _ (L₁.zpow_mem hm₁ j), ← zpow_mul, ← zpow_mul, mul_comm, zpow_mul, hint,
      ← zpow_mul, mul_comm]
  have hL₂ : ∀ l ∈ L₂, α l = l ^ a₃ := by
    intro l hl
    rw [eq_zpowers_of_card_eq_prime h₂ hm₂ hm₂1] at hl
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
    rw [ha₂ _ (L₂.zpow_mem hm₂ j), ← zpow_mul, ← zpow_mul, mul_comm, zpow_mul, hint₂,
      ← zpow_mul, mul_comm]
  refine ⟨a₃, fun y => ?_⟩
  obtain ⟨n₁, hn₁, n₂, hn₂, rfl⟩ := hE.exists_mul_of_ne h₁ h₂ h12 y
  rw [map_mul, hL₁ n₁ hn₁, hL₂ n₂ hn₂, hcomm]

theorem IsElemSq.exists_not_mapsTo (hE : IsElemSq p E) (hp2 : p ≠ 2)
    {Q : Subgroup (MulAut E)} (hQ : IsPGroup 2 Q) {x : MulAut E} (hx3 : x ^ 3 = 1)
    (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hxq : ∃ q ∈ Q, x * q ≠ q * x) {L : Subgroup E}
    (hL : Nat.card L = p) : ∃ q ∈ Q, ∃ l ∈ L, q l ∉ L := by
  by_contra h
  push Not at h
  obtain ⟨q₀, hq₀, hne⟩ := hxq
  have := hE.finite
  have hxinv : x⁻¹ = x * x := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three]
    exact hx3
  have hxQ' : ∀ q ∈ Q, x⁻¹ * q * x ∈ Q := by
    intro q hq
    have h1 : (x * x)⁻¹ = x := by rw [← hxinv, inv_inv]
    have : x⁻¹ * q * x = x * (x * q * x⁻¹) * x⁻¹ := by
      calc x⁻¹ * q * x = (x * x) * q * (x * x)⁻¹ := by rw [h1, ← hxinv]
        _ = x * (x * q * x⁻¹) * x⁻¹ := by group
    rw [this]
    exact hxQ _ (hxQ q hq)
  by_cases hxL : ∀ l ∈ L, x l ∈ L
  ·
    set c := q₀ * x * q₀⁻¹ * x⁻¹ with hc
    have hcQ : c ∈ Q := by
      have : c = q₀ * (x * q₀⁻¹ * x⁻¹) := by rw [hc]; group
      rw [this]
      exact Q.mul_mem hq₀ (hxQ _ (Q.inv_mem hq₀))
    obtain ⟨hc1, hc2⟩ := hE.commutator_trivial hL (h q₀ hq₀) hxL
    have hcp : c ^ p = 1 := hE.pow_eq_one_of_trivial hc1 hc2
    obtain ⟨k, hk⟩ := hQ ⟨c, hcQ⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
    have h2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
    have hc1' : c = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    apply hne
    have : q₀ * x * q₀⁻¹ * x⁻¹ = 1 := hc1'
    calc x * q₀ = (q₀ * x * q₀⁻¹ * x⁻¹)⁻¹ * (q₀ * x) := by group
      _ = q₀ * x := by rw [this, inv_one, one_mul]
  ·
    push Not at hxL
    obtain ⟨l₁, hl₁, hxl₁⟩ := hxL
    have hcardmap : ∀ γ : MulAut E, Nat.card (L.map (γ : E →* E)) = p := fun γ => by
      rw [Subgroup.card_map_of_injective γ.injective, hL]
    have hQmap : ∀ γ : MulAut E, (∀ q ∈ Q, γ⁻¹ * q * γ ∈ Q) →
        ∀ q ∈ Q, ∀ l ∈ L.map (γ : E →* E), q l ∈ L.map (γ : E →* E) := by
      rintro γ hγ q hq _ ⟨l, hl, rfl⟩
      refine ⟨(γ⁻¹ * q * γ) l, h _ (hγ q hq) l hl, ?_⟩
      simp [MulAut.mul_apply]
    have hγ2 : ∀ q ∈ Q, (x * x)⁻¹ * q * (x * x) ∈ Q := by
      intro q hq
      have : (x * x)⁻¹ * q * (x * x) = x⁻¹ * (x⁻¹ * q * x) * x := by group
      rw [this]
      exact hxQ' _ (hxQ' q hq)
    set L₂ := L.map (x : E →* E)
    set L₃ := L.map ((x * x : MulAut E) : E →* E)
    have h12 : L ≠ L₂ := fun heq => hxl₁ (by rw [heq]; exact ⟨l₁, hl₁, rfl⟩)
    have h23 : L₂ ≠ L₃ := by
      intro heq
      apply hxl₁
      have : x (x l₁) ∈ L₃ := ⟨l₁, hl₁, rfl⟩
      rw [← heq] at this
      obtain ⟨l', hl', hl'eq⟩ := this
      have : l' = x l₁ := x.injective hl'eq
      rw [← this]
      exact hl'
    have h13 : L ≠ L₃ := by
      intro heq
      apply h12
      ext y
      constructor
      · intro hy
        have : x⁻¹ y ∈ L₃ := by
          rw [← heq]
          rw [hxinv]
          have h1 : (x * x) y ∈ L₃ := ⟨y, hy, rfl⟩
          rw [← heq] at h1
          exact h1
        rw [← heq] at this
        exact ⟨x⁻¹ y, this, by simp⟩
      · rintro ⟨l, hl, rfl⟩
        have h1 : (x * x) l ∈ L₃ := ⟨l, hl, rfl⟩
        rw [← heq] at h1
        have h2 : (x * x) ((x * x) l) ∈ L₃ := ⟨_, h1, rfl⟩
        rw [← heq] at h2
        have h3 : (x * x) ((x * x) l) = x l := by
          rw [← MulAut.mul_apply]
          congr 1
          rw [show x * x * (x * x) = x ^ 3 * x by rw [pow_three']; simp only [mul_assoc], hx3,
            one_mul]
        rw [h3] at h2
        exact h2
    have hpow : ∀ q ∈ Q, ∃ k : ℤ, ∀ y, q y = y ^ k := fun q hq =>
      hE.eq_zpow_of_three_lines hL (hcardmap x) (hcardmap (x * x)) h12 h13 h23 (h q hq)
        (hQmap x hxQ' q hq) (hQmap (x * x) hγ2 q hq)
    obtain ⟨k, hk⟩ := hpow q₀ hq₀
    apply hne
    ext y
    rw [MulAut.mul_apply, MulAut.mul_apply, hk, hk, map_zpow]

theorem IsElemSq.exists_inv_mem (hE : IsElemSq p E) {Q : Subgroup (MulAut E)}
    (hQ : IsPGroup 2 Q) (hirr : ∀ L : Subgroup E, Nat.card L = p → ∃ q ∈ Q, ∃ l ∈ L, q l ∉ L) :
    ∃ t ∈ Q, ∀ y, t y = y⁻¹ := by
  have := hE.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE1 : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hE.card]
    exact Nat.one_lt_pow two_ne_zero hp.out.one_lt
  obtain ⟨y₀, hy₀⟩ := exists_ne (1 : E)
  have hy₀p : orderOf y₀ = p := orderOf_eq_prime (hE.pow y₀) hy₀
  have hlineex : Nat.card (Subgroup.zpowers y₀) = p := by rw [Nat.card_zpowers, hy₀p]
  have hQnt : Nontrivial Q := by
    obtain ⟨q, hq, l, hl, hql⟩ := hirr _ hlineex
    refine ⟨⟨⟨q, hq⟩, 1, fun h => hql ?_⟩⟩
    have : q = 1 := congrArg Subtype.val h
    rw [this]
    exact hl
  have : Finite Q := inferInstance
  have hZ := hQ.center_nontrivial
  have h2 : 2 ∣ Nat.card (Subgroup.center Q) := by
    obtain ⟨n, hn⟩ := (hQ.to_subgroup (Subgroup.center Q)).exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hn
    rw [hn]
    exact dvd_pow_self 2 hn0
  have : Fintype (Subgroup.center Q) := Fintype.ofFinite _
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card (G := Subgroup.center Q) 2
    (by rw [← Nat.card_eq_fintype_card]; exact h2)
  set t' : MulAut E := ((t : Q) : MulAut E) with ht'
  have ht'Q : t' ∈ Q := (t : Q).2
  have ht2 : t' ^ 2 = 1 := by
    have h1 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    have h3 := congrArg (fun z : Subgroup.center Q => ((z : Q) : MulAut E)) h1
    simpa using h3
  have ht1 : t' ≠ 1 := by
    intro h1
    have h3 : t = 1 := Subtype.ext (Subtype.ext h1)
    rw [h3, orderOf_one] at ht
    omega
  have htc : ∀ q ∈ Q, q * t' = t' * q := by
    intro q hq
    have h3 := (Subgroup.mem_center_iff.mp t.2) ⟨q, hq⟩
    exact congrArg Subtype.val h3
  refine ⟨t', ht'Q, ?_⟩
  by_contra hnot
  push Not at hnot
  obtain ⟨y₁, hy₁⟩ := hnot
  let C : Subgroup E := (t' : E →* E).eqLocus (MonoidHom.id E)
  have hmemC : ∀ y, y ∈ C ↔ t' y = y := fun y => Iff.rfl
  have htt : ∀ y, t' (t' y) = y := fun y => by
    rw [← MulAut.mul_apply, ← pow_two, ht2]
    rfl
  have hC1 : C ≠ ⊥ := by
    intro hC
    have hmem : y₁ * t' y₁ ∈ C := by
      rw [hmemC, map_mul, htt, hE.comm]
    rw [hC, Subgroup.mem_bot] at hmem
    exact hy₁ (eq_inv_of_mul_eq_one_right hmem)
  have hCtop : C ≠ ⊤ := by
    intro hC
    apply ht1
    ext y
    have : y ∈ C := by rw [hC]; exact Subgroup.mem_top y
    exact this
  have hCp : Nat.card C = p := by
    have hdvd : Nat.card C ∣ p ^ 2 := hE.card ▸ Subgroup.card_subgroup_dvd_card C
    obtain ⟨k, hk, hkC⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    interval_cases k
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hkC, pow_zero])) hC1
    · rw [hkC, pow_one]
    · exact absurd (Subgroup.eq_top_of_card_eq C (hkC.trans hE.card.symm)) hCtop
  obtain ⟨q, hq, l, hl, hql⟩ := hirr C hCp
  apply hql
  rw [hmemC] at hl ⊢
  rw [← MulAut.mul_apply, ← htc q hq, MulAut.mul_apply, hl]

end ElemSq

end CFSG.Quasithin.EmptyFaithfulMultiple
