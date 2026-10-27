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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

namespace CFSG.Quasithin.H13.NFa2

variable {G : Type} [Group G] [Finite G]

structure IsChiefPair (X N₀ N₁ : Subgroup G) : Prop where
  lt : N₀ < N₁
  norm₀ : X ≤ Subgroup.normalizer (N₀ : Set G)
  norm₁ : X ≤ Subgroup.normalizer (N₁ : Set G)
  normal : N₁ ≤ Subgroup.normalizer (N₀ : Set G)
  min : ∀ N : Subgroup G, N₀ ≤ N → N ≤ N₁ → X ≤ Subgroup.normalizer (N : Set G) →
    N = N₀ ∨ N = N₁

private instance finite_subgroup {H : Type} [Group H] [Finite H] : Finite (Subgroup H) :=
  Finite.of_injective (fun K : Subgroup H => (K : Set H)) SetLike.coe_injective

private lemma isPGroup_two_of_le {A B : Subgroup G} (hA : IsPGroup 2 ↥A) (hBA : B ≤ A) :
    IsPGroup 2 ↥B := by
  intro g
  obtain ⟨s, hs⟩ := hA ⟨g, hBA g.2⟩
  refine ⟨s, Subtype.ext ?_⟩
  simpa using congrArg Subtype.val hs

private lemma index_two_props {P : Type} [Group P] (M : Subgroup P) [M.Normal]
    (hM : M.index = 2) : (∀ p : P, p * p ∈ M) ∧ ∀ p q : P, p * q * p⁻¹ * q⁻¹ ∈ M := by
  have hQ : ∀ x : P ⧸ M, x * x = 1 := by
    intro x
    have h2 : x ^ 2 = 1 := by
      have h := pow_card_eq_one' (G := P ⧸ M) (x := x)
      rwa [← Subgroup.index_eq_card, hM] at h
    rwa [pow_two] at h2
  refine ⟨fun p => ?_, fun p q => ?_⟩
  · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    exact hQ _
  · rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [inv_eq_of_mul_eq_one_right (hQ (p : P ⧸ M)), inv_eq_of_mul_eq_one_right (hQ (q : P ⧸ M))]
    simpa [mul_assoc] using hQ ((p : P ⧸ M) * (q : P ⧸ M))

private lemma exists_sub_of_two_group {N₀ N₁ : Subgroup G} (hlt : N₀ < N₁)
    (hp : IsPGroup 2 ↥N₁) :
    ∃ M : Subgroup G, N₀ ≤ M ∧ M < N₁ ∧ (∀ a ∈ N₁, ∀ b ∈ N₁, a * b * a⁻¹ * b⁻¹ ∈ M) ∧
      ∀ a ∈ N₁, a * a ∈ M := by
  haveI : Group.IsNilpotent N₁ := IsPGroup.isNilpotent hp
  have hH₀ : N₀.subgroupOf N₁ ≠ ⊤ := by
    intro htop
    obtain ⟨g, hg1, hg2⟩ := SetLike.exists_of_lt hlt
    have hmem : (⟨g, hg1⟩ : ↥N₁) ∈ N₀.subgroupOf N₁ := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hg2 (Subgroup.mem_subgroupOf.mp hmem)
  obtain ⟨M, hMc, hH₀M⟩ : ∃ M : Subgroup ↥N₁, IsCoatom M ∧ N₀.subgroupOf N₁ ≤ M := by
    rcases eq_top_or_exists_le_coatom (N₀.subgroupOf N₁) with h | ⟨M, hM, hle⟩
    · exact absurd h hH₀
    · exact ⟨M, hM, hle⟩
  have hidx : M.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hp).mp hMc
  haveI : M.Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨hsq, hcm⟩ := index_two_props M hidx
  refine ⟨M.map N₁.subtype, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have hgM : (⟨g, hlt.le hg⟩ : ↥N₁) ∈ M := hH₀M (Subgroup.mem_subgroupOf.mpr hg)
    exact Subgroup.mem_map.mpr ⟨_, hgM, rfl⟩
  · refine lt_of_le_of_ne ?_ ?_
    · rintro _ hg
      obtain ⟨p, _, rfl⟩ := Subgroup.mem_map.mp hg
      exact p.2
    · intro heq
      obtain ⟨p, hpM⟩ : ∃ p : ↥N₁, p ∉ M := by
        by_contra hcon
        push Not at hcon
        exact hMc.1 ((Subgroup.eq_top_iff' M).mpr hcon)
      have hpmem : (p : G) ∈ M.map N₁.subtype := by
        rw [heq]
        exact p.2
      obtain ⟨q, hq, hqp⟩ := Subgroup.mem_map.mp hpmem
      have hqp' : q = p := Subtype.ext hqp
      rw [hqp'] at hq
      exact hpM hq
  · intro a ha b hb
    exact Subgroup.mem_map.mpr
      ⟨(⟨a, ha⟩ : ↥N₁) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥N₁)⁻¹ * (⟨b, hb⟩ : ↥N₁)⁻¹,
        hcm ⟨a, ha⟩ ⟨b, hb⟩, rfl⟩
  · intro a ha
    exact Subgroup.mem_map.mpr ⟨(⟨a, ha⟩ : ↥N₁) * ⟨a, ha⟩, hsq ⟨a, ha⟩, rfl⟩

private def commSq (N₁ : Subgroup G) : Set G :=
  {g | ∃ a ∈ N₁, ∃ b ∈ N₁, g = a * b * a⁻¹ * b⁻¹ ∨ g = a * a}

private lemma commSq_subset (N₁ : Subgroup G) : commSq N₁ ⊆ (N₁ : Set G) := by
  rintro g ⟨a, ha, b, hb, rfl | rfl⟩
  · exact N₁.mul_mem (N₁.mul_mem (N₁.mul_mem ha hb) (N₁.inv_mem ha)) (N₁.inv_mem hb)
  · exact N₁.mul_mem ha ha

private lemma commSq_conj {N₁ : Subgroup G} {y : G} (hy : y ∈ Subgroup.normalizer (N₁ : Set G)) :
    ∀ g ∈ commSq N₁, y * g * y⁻¹ ∈ commSq N₁ := by
  rintro g ⟨a, ha, b, hb, rfl | rfl⟩
  · refine ⟨y * a * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy a).mp ha,
      y * b * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy b).mp hb, Or.inl ?_⟩
    group
  · refine ⟨y * a * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy a).mp ha,
      y * a * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy a).mp ha, Or.inr ?_⟩
    group

private lemma normalizer_sup_closure {X N₀ N₁ : Subgroup G} (h : IsChiefPair X N₀ N₁) :
    X ≤ Subgroup.normalizer ((N₀ ⊔ Subgroup.closure (commSq N₁) : Subgroup G) : Set G) := by
  have fwd : ∀ y ∈ X, ∀ g ∈ N₀ ⊔ Subgroup.closure (commSq N₁),
      y * g * y⁻¹ ∈ N₀ ⊔ Subgroup.closure (commSq N₁) := by
    intro y hy
    let K : Subgroup G :=
      (N₀ ⊔ Subgroup.closure (commSq N₁)).comap (MulEquiv.toMonoidHom (MulAut.conj y))
    have hle : N₀ ⊔ Subgroup.closure (commSq N₁) ≤ K := by
      refine sup_le (fun g hg => ?_) ((Subgroup.closure_le _).mpr fun g hg => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (h.norm₀ hy) g).mp hg)
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure (commSq_conj (h.norm₁ hy) g hg))
    exact fun g hg => hle hg
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fwd y hy g, fun hg => ?_⟩
  have := fwd y⁻¹ (X.inv_mem hy) _ hg
  simpa [mul_assoc] using this

private lemma sup_commSq_eq {X N₀ N₁ : Subgroup G} (h : IsChiefPair X N₀ N₁)
    (hp : IsPGroup 2 ↥N₁) : N₀ ⊔ Subgroup.closure (commSq N₁) = N₀ := by
  have hN₂N₁ : N₀ ⊔ Subgroup.closure (commSq N₁) ≤ N₁ :=
    sup_le h.lt.le ((Subgroup.closure_le _).mpr (commSq_subset N₁))
  rcases h.min (N₀ ⊔ Subgroup.closure (commSq N₁)) le_sup_left hN₂N₁
    (normalizer_sup_closure h) with heq | heq
  · exact heq
  · exfalso
    obtain ⟨M, hN₀M, hMlt, hcm, hsq⟩ := exists_sub_of_two_group h.lt hp
    have hgen : commSq N₁ ⊆ (M : Set G) := by
      rintro g ⟨a, ha, b, hb, rfl | rfl⟩
      · exact hcm a ha b hb
      · exact hsq a ha
    have hN₂M : N₀ ⊔ Subgroup.closure (commSq N₁) ≤ M :=
      sup_le hN₀M ((Subgroup.closure_le _).mpr hgen)
    have hN₁M : N₁ ≤ M := (le_of_eq heq.symm).trans hN₂M
    exact lt_irrefl _ (lt_of_le_of_lt hN₁M hMlt)

theorem odd_centralizes_of_stable {k : G} (hk : Odd (orderOf k)) {Z₀ N₀ N₁ : Subgroup G}
    (hZN : Z₀ ≤ N₀) (hNN : N₀ ≤ N₁) (hN₀2 : IsPGroup 2 ↥N₀)
    (hZn : N₁ ≤ Subgroup.normalizer (Z₀ : Set G)) (hN₀n : N₁ ≤ Subgroup.normalizer (N₀ : Set G))
    (hkZ : k ∈ Subgroup.normalizer (Z₀ : Set G)) (hkN₀ : k ∈ Subgroup.normalizer (N₀ : Set G))
    (hkN₁ : k ∈ Subgroup.normalizer (N₁ : Set G))
    (h0 : ∀ a ∈ N₀, k * a * k⁻¹ * a⁻¹ ∈ Z₀) (h1 : ∀ n ∈ N₁, k * n * k⁻¹ * n⁻¹ ∈ N₀) :
    ∀ n ∈ N₁, k * n * k⁻¹ * n⁻¹ ∈ Z₀ := by
  intro n hn
  obtain ⟨a, ha_def⟩ : ∃ a : G, a = k * n * k⁻¹ * n⁻¹ := ⟨_, rfl⟩
  have ha : a ∈ N₀ := by
    rw [ha_def]
    exact h1 n hn
  have hkn : k * n * k⁻¹ = a * n := by
    rw [ha_def]
    group
  have key : ∀ j : ℕ, ∃ z ∈ Z₀, k ^ j * n * (k ^ j)⁻¹ = z * a ^ j * n := by
    intro j
    induction j with
    | zero => exact ⟨1, Z₀.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨z, hz, hzj⟩ := ih
      have hb : z * a ^ j ∈ N₀ := N₀.mul_mem (hZN hz) (N₀.pow_mem ha j)
      refine ⟨k * (z * a ^ j) * k⁻¹ * (z * a ^ j)⁻¹ * z, Z₀.mul_mem (h0 _ hb) hz, ?_⟩
      have hW : k * (z * a ^ j) * k⁻¹ * (z * a ^ j)⁻¹ * z * a ^ (j + 1)
          = k * (z * a ^ j) * k⁻¹ * a := by
        group
      calc k ^ (j + 1) * n * (k ^ (j + 1))⁻¹ = k * (k ^ j * n * (k ^ j)⁻¹) * k⁻¹ := by group
        _ = k * (z * a ^ j * n) * k⁻¹ := by rw [hzj]
        _ = k * (z * a ^ j) * k⁻¹ * (k * n * k⁻¹) := by group
        _ = k * (z * a ^ j) * k⁻¹ * (a * n) := by rw [hkn]
        _ = k * (z * a ^ j) * k⁻¹ * a * n := by group
        _ = k * (z * a ^ j) * k⁻¹ * (z * a ^ j)⁻¹ * z * a ^ (j + 1) * n := by rw [hW]
  obtain ⟨z, hz, hzm⟩ := key (orderOf k)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hzm
  have h2 : z * a ^ orderOf k = 1 := mul_right_cancel (b := n) (by rw [one_mul]; exact hzm.symm)
  have ham : a ^ orderOf k ∈ Z₀ := by
    rw [eq_inv_of_mul_eq_one_right h2]
    exact Z₀.inv_mem hz
  obtain ⟨s, hs⟩ := hN₀2 ⟨a, ha⟩
  have hs' : a ^ 2 ^ s = 1 := by
    simpa using congrArg Subtype.val hs
  have hcop2 : Nat.Coprime (orderOf k) 2 := Nat.coprime_two_right.mpr hk
  have hcop : Nat.Coprime (orderOf k) (orderOf a) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hs') (Nat.Coprime.pow_right s hcop2)
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  have haZ : a ∈ Z₀ := by
    have h3 := Z₀.pow_mem ham t
    rwa [ht] at h3
  rw [ha_def] at haZ
  exact haZ

theorem exists_chiefPair {X A Z₀ : Subgroup G} (hA : IsPGroup 2 ↥A)
    (hXA : X ≤ Subgroup.normalizer (A : Set G)) (hXZ : X ≤ Subgroup.normalizer (Z₀ : Set G))
    (hAZ : A ≤ Subgroup.normalizer (Z₀ : Set G)) (hZA : Z₀ ≤ A)
    (hAX : ∀ N : Subgroup G, N ≤ A → X ≤ Subgroup.normalizer (N : Set G) →
      A ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hxX : x ∈ X) (hxodd : Odd (orderOf x)) (hx : ∃ a ∈ A, x * a * x⁻¹ * a⁻¹ ∉ Z₀) :
    ∃ N₀ N₁ : Subgroup G, IsChiefPair X N₀ N₁ ∧ Z₀ ≤ N₀ ∧ N₁ ≤ A ∧
      ∃ n ∈ N₁, x * n * x⁻¹ * n⁻¹ ∉ N₀ := by
  classical
  obtain ⟨N₁, ⟨hZN₁, hN₁A, hXN₁, n₀, hn₀N₁, hn₀⟩, hN₁min⟩ :=
    (wellFounded_lt (α := Subgroup G)).has_min
      {N : Subgroup G | Z₀ ≤ N ∧ N ≤ A ∧ X ≤ Subgroup.normalizer (N : Set G) ∧
        ∃ a ∈ N, x * a * x⁻¹ * a⁻¹ ∉ Z₀}
      ⟨A, hZA, le_rfl, hXA, hx⟩
  have hZlt : Z₀ < N₁ := by
    refine lt_of_le_of_ne hZN₁ fun heq => hn₀ ?_
    have hn₀Z : n₀ ∈ Z₀ := by
      rw [heq]
      exact hn₀N₁
    exact Z₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXZ hxX) n₀).mp hn₀Z) (Z₀.inv_mem hn₀Z)
  obtain ⟨N₀, ⟨hZN₀, hN₀lt, hXN₀⟩, hN₀max⟩ :=
    (wellFounded_gt (α := Subgroup G)).has_min
      {N : Subgroup G | Z₀ ≤ N ∧ N < N₁ ∧ X ≤ Subgroup.normalizer (N : Set G)}
      ⟨Z₀, le_rfl, hZlt, hXZ⟩
  have hN₀A : N₀ ≤ A := hN₀lt.le.trans hN₁A
  have hchief : IsChiefPair X N₀ N₁ := by
    refine ⟨hN₀lt, hXN₀, hXN₁, hN₁A.trans (hAX N₀ hN₀A hXN₀), fun N hN₀N hNN₁ hXN => ?_⟩
    by_cases hEq : N = N₁
    · exact Or.inr hEq
    · refine Or.inl ?_
      have hNlt : N < N₁ := lt_of_le_of_ne hNN₁ hEq
      exact ((le_iff_eq_or_lt.mp hN₀N).resolve_right
        (hN₀max N ⟨hZN₀.trans hN₀N, hNlt, hXN⟩)).symm
  have h0 : ∀ a ∈ N₀, x * a * x⁻¹ * a⁻¹ ∈ Z₀ := by
    intro a ha
    by_contra hc
    exact hN₁min N₀ ⟨hZN₀, hN₀A, hXN₀, a, ha, hc⟩ hN₀lt
  have hfinal : ∃ n ∈ N₁, x * n * x⁻¹ * n⁻¹ ∉ N₀ := by
    by_contra hcon
    push Not at hcon
    have hall := odd_centralizes_of_stable hxodd hZN₀ hN₀lt.le (isPGroup_two_of_le hA hN₀A)
      (hN₁A.trans hAZ) hchief.normal (hXZ hxX) (hXN₀ hxX) (hXN₁ hxX) h0 hcon
    exact hn₀ (hall n₀ hn₀N₁)
  exact ⟨N₀, N₁, hchief, hZN₀, hN₁A, hfinal⟩

theorem IsChiefPair.comm_mem {X N₀ N₁ : Subgroup G} (h : IsChiefPair X N₀ N₁)
    (hp : IsPGroup 2 ↥N₁) : ∀ a ∈ N₁, ∀ b ∈ N₁, a * b * a⁻¹ * b⁻¹ ∈ N₀ := by
  intro a ha b hb
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ N₀ ⊔ Subgroup.closure (commSq N₁) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure
      (show a * b * a⁻¹ * b⁻¹ ∈ commSq N₁ from ⟨a, ha, b, hb, Or.inl rfl⟩))
  rwa [sup_commSq_eq h hp] at hmem

theorem IsChiefPair.sq_mem {X N₀ N₁ : Subgroup G} (h : IsChiefPair X N₀ N₁)
    (hp : IsPGroup 2 ↥N₁) : ∀ a ∈ N₁, a * a ∈ N₀ := by
  intro a ha
  have hmem : a * a ∈ N₀ ⊔ Subgroup.closure (commSq N₁) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure
      (show a * a ∈ commSq N₁ from ⟨a, ha, a, ha, Or.inr rfl⟩))
  rwa [sup_commSq_eq h hp] at hmem

end CFSG.Quasithin.H13.NFa2
