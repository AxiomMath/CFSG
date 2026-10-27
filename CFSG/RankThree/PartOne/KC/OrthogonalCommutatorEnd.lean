module

public import CFSG.RankThree.PartOne.KC.OddCommutatorSkeleton
public import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators

public section

namespace CFSG.RankThree.PartOne.KCOrthComm

open Subgroup
open scoped commutatorElement

theorem commutator_mem_oddPart_of_invariant {C : Type*} [Group C] [Finite C] {Z : Subgroup C}
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) {α : C} (hαZ : ∀ z ∈ Z, α * z * α⁻¹ ∈ Z)
    (hfix : ∀ z ∈ Z, (∃ k : ℕ, z ^ 2 ^ k = 1) → α * z * α⁻¹ = z) {c : C} (hc : c ∈ Z) :
    ⁅α, c⁆ ∈ KCOddCommutator.oddPart Z hZ := by
  obtain ⟨k, b, hb, hord⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf c)
    (orderOf_pos c).ne'
  have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) (b : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hb))
  obtain ⟨u, v, huv⟩ := hcop
  have huv' : ((2 ^ k : ℕ) : ℤ) * u + (b : ℤ) * v = 1 := by linarith
  have hdec : c = (c ^ 2 ^ k) ^ u * (c ^ b) ^ v := by
    calc c = c ^ (((2 ^ k : ℕ) : ℤ) * u + (b : ℤ) * v) := by rw [huv', zpow_one]
      _ = (c ^ 2 ^ k) ^ u * (c ^ b) ^ v := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  set x : C := (c ^ 2 ^ k) ^ u with hx
  set y : C := (c ^ b) ^ v with hy
  have hxZ : x ∈ Z := Z.zpow_mem (Z.pow_mem hc _) u
  have hyZ : y ∈ Z := Z.zpow_mem (Z.pow_mem hc _) v
  have hxodd : Odd (orderOf x) := by
    have h1 : orderOf (c ^ 2 ^ k) = b := by
      rw [orderOf_pow' c (by positivity), hord, Nat.gcd_eq_right (dvd_mul_right _ _),
        Nat.mul_div_cancel_left _ (by positivity)]
    have h2 : orderOf x ∣ orderOf (c ^ 2 ^ k) := orderOf_dvd_of_pow_eq_one (by
      rw [hx, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
        one_zpow])
    rw [h1] at h2
    exact Odd.of_dvd_nat hb h2
  have hy2 : y ^ 2 ^ k = 1 := by
    rw [hy, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul, mul_comm,
      ← hord, pow_orderOf_eq_one, one_zpow]
  have hαy : α * y * α⁻¹ = y := hfix y hyZ ⟨k, hy2⟩
  have hcomm : ⁅α, c⁆ = (α * x * α⁻¹) * x⁻¹ := by
    rw [commutatorElement_def]
    calc α * c * α⁻¹ * c⁻¹ = α * (x * y) * α⁻¹ * (x * y)⁻¹ := by rw [← hdec]
      _ = (α * x * α⁻¹) * (α * y * α⁻¹) * y⁻¹ * x⁻¹ := by group
      _ = (α * x * α⁻¹) * x⁻¹ := by rw [hαy]; group
  rw [hcomm]
  refine (KCOddCommutator.oddPart Z hZ).mul_mem ?_
    ((KCOddCommutator.oddPart Z hZ).inv_mem ⟨hxZ, hxodd⟩)
  refine ⟨hαZ x hxZ, ?_⟩
  have : orderOf (α * x * α⁻¹) = orderOf x :=
    orderOf_injective (MulAut.conj α).toMonoidHom (MulAut.conj α).injective x
  rwa [this]

theorem odd_card_commutator_of_index_two {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {S A Γ P : Subgroup G} (hA : IsPGroup p A) (hS : ¬ p ∣ Nat.card S)
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) (hSAΓ : ⁅S, A⁆ ≤ Γ)
    (hidx : ∀ g ∈ Γ, ∀ g' ∈ Γ, g ∉ P → g' ∉ P → g⁻¹ * g' ∈ P)
    (hAΓ : ∀ α ∈ A, ∀ g ∈ Γ, α * g * α⁻¹ ∈ Γ) (hAP : ∀ α ∈ A, ∀ g ∈ P, α * g * α⁻¹ ∈ P)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hfix : ∀ α ∈ A, ∀ z ∈ P, (∃ k : ℕ, z ^ 2 ^ k = 1) → α * z * α⁻¹ = z) :
    Odd (Nat.card (⁅S, A⁆ : Subgroup G)) := by
  classical
  have hidem := CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent hp A S
    hA hS hAS
  have hRΓ : ⁅S, A⁆ ≤ Γ := hSAΓ
  have hRAP : ⁅(⁅S, A⁆ : Subgroup G), A⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro r hr α hα
    have hrΓ : r ∈ Γ := hRΓ hr
    have hg' : α * r⁻¹ * α⁻¹ ∈ Γ := hAΓ α hα r⁻¹ (Γ.inv_mem hrΓ)
    by_cases hrP : r ∈ P
    · have h1 : α * r⁻¹ * α⁻¹ ∈ P := hAP α hα r⁻¹ (P.inv_mem hrP)
      have h2 : r * (α * r⁻¹ * α⁻¹) ∈ P := P.mul_mem hrP h1
      have h3 : ⁅r, α⁆ = r * (α * r⁻¹ * α⁻¹) := by
        rw [commutatorElement_def]; group
      rw [h3]
      exact h2
    · have hninvP : r⁻¹ ∉ P := fun h => hrP (by simpa using P.inv_mem h)
      have hg'P : α * r⁻¹ * α⁻¹ ∉ P := by
        intro h
        have h1 := hAP α⁻¹ (A.inv_mem hα) _ h
        apply hninvP
        have h2 : α⁻¹ * (α * r⁻¹ * α⁻¹) * α⁻¹⁻¹ = r⁻¹ := by group
        rwa [h2] at h1
      have h1 := hidx r⁻¹ (Γ.inv_mem hrΓ) _ hg' hninvP hg'P
      have h3 : ⁅r, α⁆ = (r⁻¹)⁻¹ * (α * r⁻¹ * α⁻¹) := by
        rw [commutatorElement_def]; group
      rw [h3]
      exact h1
  have hRP : (⁅S, A⁆ : Subgroup G) ≤ P := by
    have := hRAP
    rwa [hidem] at this
  have hRodd : ⁅(⁅S, A⁆ : Subgroup G), A⁆ ≤ KCOddCommutator.oddPart P hcomm := by
    rw [Subgroup.commutator_le]
    intro r hr α hα
    have hrP : r ∈ P := hRP hr
    have h1 := commutator_mem_oddPart_of_invariant hcomm (fun z hz => hAP α hα z hz)
      (hfix α hα) hrP
    have h2 : ⁅r, α⁆ = (⁅α, r⁆)⁻¹ := (commutatorElement_inv α r).symm
    rw [h2]
    exact (KCOddCommutator.oddPart P hcomm).inv_mem h1
  have hle : (⁅S, A⁆ : Subgroup G) ≤ KCOddCommutator.oddPart P hcomm := by
    rwa [hidem] at hRodd
  exact Odd.of_dvd_nat (KCOddCommutator.odd_card_oddPart hcomm) (Subgroup.card_dvd_of_le hle)


section SmallIndex

theorem perm_eq_one_of_card_lt {X : Type*} [Fintype X] [DecidableEq X] {p n : ℕ} [Fact p.Prime]
    {σ : Equiv.Perm X} (hσ : σ ^ p ^ n = 1) (hX : Fintype.card X < p) : σ = 1 := by
  have h := Equiv.Perm.card_compl_support_modEq hσ
  have h1 : σ.supportᶜ.card = Fintype.card X :=
    Nat.ModEq.eq_of_lt_of_lt h (lt_of_le_of_lt (Finset.card_le_univ _) hX) hX
  have h2 : σ.supportᶜ = Finset.univ := Finset.eq_univ_of_card _ h1
  have h3 : σ.support = ∅ := (Finset.compl_eq_univ_iff _).mp h2
  exact Equiv.Perm.support_eq_empty_iff.mp h3

theorem commutator_mem_of_small_index {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {A Γ P : Subgroup G} (hA : IsPGroup p A) (hidx : (P.subgroupOf Γ).index < p)
    (hAΓ : ∀ α ∈ A, ∀ g ∈ Γ, α * g * α⁻¹ ∈ Γ)
    (hAP : ∀ α ∈ A, ∀ g ∈ P, α * g * α⁻¹ ∈ P) {α : G} (hα : α ∈ A) {r : G} (hr : r ∈ Γ) :
    ⁅r, α⁆ ∈ P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set P' : Subgroup ↥Γ := P.subgroupOf Γ with hP'
  have hαinv : α⁻¹ ∈ A := A.inv_mem hα
  let cα : ∀ {a : G}, a ∈ A → ↥Γ → ↥Γ := fun {a} ha g => ⟨a * g * a⁻¹, hAΓ a ha g g.2⟩
  have hresp : ∀ {a : G} (ha : a ∈ A) (g₁ g₂ : ↥Γ), (QuotientGroup.leftRel P').r g₁ g₂ →
      (QuotientGroup.leftRel P').r (cα ha g₁) (cα ha g₂) := by
    intro a ha g₁ g₂ h
    rw [QuotientGroup.leftRel_apply] at h ⊢
    have h1 : (g₁⁻¹ * g₂ : ↥Γ) ∈ P' := h
    rw [hP', Subgroup.mem_subgroupOf] at h1 ⊢
    have h2 := hAP a ha _ h1
    have h3 : (a * ((g₁⁻¹ * g₂ : ↥Γ) : G) * a⁻¹) = (((cα ha g₁)⁻¹ * cα ha g₂ : ↥Γ) : G) := by
      change a * (((g₁ : G))⁻¹ * (g₂ : G)) * a⁻¹ =
        (a * (g₁ : G) * a⁻¹)⁻¹ * (a * (g₂ : G) * a⁻¹)
      group
    rwa [h3] at h2
  let fwd : ↥Γ ⧸ P' → ↥Γ ⧸ P' := Quotient.map' (cα hα) (hresp hα)
  let bwd : ↥Γ ⧸ P' → ↥Γ ⧸ P' := Quotient.map' (cα hαinv) (hresp hαinv)
  have hfb : ∀ c, bwd (fwd c) = c := by
    intro c
    induction c using Quotient.inductionOn' with
    | h g =>
      change (QuotientGroup.mk (cα hαinv (cα hα g)) : ↥Γ ⧸ P') = QuotientGroup.mk g
      congr 1
      refine Subtype.ext ?_
      change α⁻¹ * (α * (g : G) * α⁻¹) * α⁻¹⁻¹ = g
      group
  have hbf : ∀ c, fwd (bwd c) = c := by
    intro c
    induction c using Quotient.inductionOn' with
    | h g =>
      change (QuotientGroup.mk (cα hα (cα hαinv g)) : ↥Γ ⧸ P') = QuotientGroup.mk g
      congr 1
      refine Subtype.ext ?_
      change α * (α⁻¹ * (g : G) * α⁻¹⁻¹) * α⁻¹ = g
      group
  let π : Equiv.Perm (↥Γ ⧸ P') := ⟨fwd, bwd, hfb, hbf⟩
  have hfinite : Fintype (↥Γ ⧸ P') := Fintype.ofFinite _
  obtain ⟨j, hj⟩ := hA ⟨α, hα⟩
  have hαj : α ^ p ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hiter : ∀ (n : ℕ) (g : ↥Γ), ∃ g' : ↥Γ, (π ^ n) (QuotientGroup.mk g) = QuotientGroup.mk g' ∧
      (g' : G) = α ^ n * (g : G) * (α ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => exact fun g => ⟨g, by simp, by simp⟩
    | succ n ih =>
      intro g
      obtain ⟨g', h1, h2⟩ := ih g
      refine ⟨cα hα g', ?_, ?_⟩
      · rw [pow_succ', Equiv.Perm.mul_apply, h1]
        rfl
      · change α * (g' : G) * α⁻¹ = α ^ (n + 1) * (g : G) * (α ^ (n + 1))⁻¹
        rw [h2, pow_succ', mul_inv_rev]
        group
  have hπ : π ^ p ^ j = 1 := by
    refine Equiv.ext fun c => ?_
    induction c using Quotient.inductionOn' with
    | h g =>
      obtain ⟨g', h1, h2⟩ := hiter (p ^ j) g
      have hg' : g' = g := Subtype.ext (by rw [h2, hαj]; simp)
      change (π ^ p ^ j) (QuotientGroup.mk g) = QuotientGroup.mk g
      rw [h1, hg']
  have hcard : Fintype.card (↥Γ ⧸ P') < p := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact hidx
  have hπ1 : π = 1 := perm_eq_one_of_card_lt hπ hcard
  have hr' : r⁻¹ ∈ Γ := Γ.inv_mem hr
  have hfix := congrArg (fun σ : Equiv.Perm (↥Γ ⧸ P') => σ (QuotientGroup.mk (⟨r⁻¹, hr'⟩ : ↥Γ)))
    hπ1
  have hfix' : (QuotientGroup.mk (cα hα ⟨r⁻¹, hr'⟩) : ↥Γ ⧸ P') = QuotientGroup.mk ⟨r⁻¹, hr'⟩ :=
    hfix
  have := QuotientGroup.eq.mp hfix'
  rw [hP', Subgroup.mem_subgroupOf] at this
  have h3 : ((((cα hα ⟨r⁻¹, hr'⟩)⁻¹ * ⟨r⁻¹, hr'⟩ : ↥Γ)) : G) = α * r * α⁻¹ * r⁻¹ := by
    change (α * r⁻¹ * α⁻¹)⁻¹ * r⁻¹ = α * r * α⁻¹ * r⁻¹
    group
  have h4 : ⁅r, α⁆ = (α * r * α⁻¹ * r⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h4]
  exact P.inv_mem (by rw [← h3]; exact this)

theorem odd_card_commutator_of_small_index {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {S A Γ P : Subgroup G} (hA : IsPGroup p A) (hS : ¬ p ∣ Nat.card S)
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) (hSAΓ : ⁅S, A⁆ ≤ Γ)
    (hidx : (P.subgroupOf Γ).index < p) (hAΓ : ∀ α ∈ A, ∀ g ∈ Γ, α * g * α⁻¹ ∈ Γ)
    (hAP : ∀ α ∈ A, ∀ g ∈ P, α * g * α⁻¹ ∈ P) (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hfix : ∀ α ∈ A, ∀ z ∈ P, (∃ k : ℕ, z ^ 2 ^ k = 1) → α * z * α⁻¹ = z) :
    Odd (Nat.card (⁅S, A⁆ : Subgroup G)) := by
  classical
  have hidem := CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent hp A S
    hA hS hAS
  have hRAP : ⁅(⁅S, A⁆ : Subgroup G), A⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro r hr α hα
    exact commutator_mem_of_small_index hp hA hidx hAΓ hAP hα (hSAΓ hr)
  have hRP : (⁅S, A⁆ : Subgroup G) ≤ P := by
    have := hRAP
    rwa [hidem] at this
  have hRodd : ⁅(⁅S, A⁆ : Subgroup G), A⁆ ≤ KCOddCommutator.oddPart P hcomm := by
    rw [Subgroup.commutator_le]
    intro r hr α hα
    have hrP : r ∈ P := hRP hr
    have h1 := commutator_mem_oddPart_of_invariant hcomm (fun z hz => hAP α hα z hz)
      (hfix α hα) hrP
    have h2 : ⁅r, α⁆ = (⁅α, r⁆)⁻¹ := (commutatorElement_inv α r).symm
    rw [h2]
    exact (KCOddCommutator.oddPart P hcomm).inv_mem h1
  have hle : (⁅S, A⁆ : Subgroup G) ≤ KCOddCommutator.oddPart P hcomm := by
    rwa [hidem] at hRodd
  exact Odd.of_dvd_nat (KCOddCommutator.odd_card_oddPart hcomm) (Subgroup.card_dvd_of_le hle)

end SmallIndex

end CFSG.RankThree.PartOne.KCOrthComm
