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

namespace CFSG.Quasithin.A10

open Subgroup

theorem inf_eq_bot_of_fixed_point_free {Γ : Type*} [Group Γ] [Finite Γ] {W Q : Subgroup Γ}
    {c : Γ} (hc : c ^ 3 = 1) (hW : Nat.card W = 4) (hWc : ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    (hQc : ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) (hfix : ∀ w ∈ W, c * w * c⁻¹ = w → w = 1)
    (hWQ : ¬ W ≤ Q) : W ⊓ Q = ⊥ := by
  classical
  by_contra hne
  have hne' : W ⊓ Q ≠ ⊥ := hne
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hne'
  obtain ⟨⟨x, hx⟩, hx1⟩ := hne'
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨hxW, hxQ⟩ := hx
  have hx1W : c * x * c⁻¹ ∈ W := hWc x hxW
  have hx1Q : c * x * c⁻¹ ∈ Q := hQc x hxQ
  have hx2W : c * (c * x * c⁻¹) * c⁻¹ ∈ W := hWc _ hx1W
  have hx2Q : c * (c * x * c⁻¹) * c⁻¹ ∈ Q := hQc _ hx1Q
  have hc3' : c * c * c = 1 := by rw [← pow_three']; exact hc
  have hc3 : ∀ y : Γ, c * (c * (c * y * c⁻¹) * c⁻¹) * c⁻¹ = y := fun y => by
    calc c * (c * (c * y * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * y * (c * c * c)⁻¹ := by group
      _ = y := by rw [hc3']; group
  have hne1 : c * x * c⁻¹ ≠ 1 := fun h => hx1' (by
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group)
  have hne2 : c * (c * x * c⁻¹) * c⁻¹ ≠ 1 := fun h => hne1 (by
    calc c * x * c⁻¹ = c⁻¹ * (c * (c * x * c⁻¹) * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group)
  have hxx1 : x ≠ c * x * c⁻¹ := fun h => hx1' (hfix x hxW h.symm)
  have hx1x2 : c * x * c⁻¹ ≠ c * (c * x * c⁻¹) * c⁻¹ := fun h =>
    hne1 (hfix _ hx1W h.symm)
  have hxx2 : x ≠ c * (c * x * c⁻¹) * c⁻¹ := fun h => hxx1 (by
    have h3 := hc3 x
    calc x = c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹ := h3.symm
      _ = c * x * c⁻¹ := by rw [← h])
  have hsub : ({1, x, c * x * c⁻¹, c * (c * x * c⁻¹) * c⁻¹} : Set Γ) ⊆
      ((W ⊓ Q : Subgroup Γ) : Set Γ) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact ⟨hxW, hxQ⟩
    · exact ⟨hx1W, hx1Q⟩
    · exact ⟨hx2W, hx2Q⟩
  have hcard : ({1, x, c * x * c⁻¹, c * (c * x * c⁻¹) * c⁻¹} : Set Γ).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hx1x2]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hxx1, hxx2⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm hx1', Ne.symm hne1, Ne.symm hne2⟩
  have h4 : 4 ≤ Nat.card ↥(W ⊓ Q) := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hcard] at this
    rw [← Nat.card_coe_set_eq] at this
    exact this
  have hle : W ⊓ Q ≤ W := inf_le_left
  have heq : W ⊓ Q = W := Subgroup.eq_of_le_of_card_ge hle (by rw [hW]; exact h4)
  exact hWQ (heq ▸ inf_le_right)

theorem W_le_Q {Γ : Type*} [Group Γ] [Finite Γ] {Q B W : Subgroup Γ} [Q.Normal] [B.Normal]
    (hΓ : Nat.card Γ = 12 * Nat.card Q)
    (hB : Nat.card B = 2 * Nat.card ↥(B ⊓ Q)) {c : Γ} (hc : c ^ 3 = 1)
    (hW : Nat.card W = 4) (hWc : ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    (hfix : ∀ w ∈ W, c * w * c⁻¹ = w → w = 1) : W ≤ Q := by
  classical
  by_contra hWQ
  have hQc : ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := fun q hq => Normal.conj_mem ‹Q.Normal› q hq c
  have hWQ' : W ⊓ Q = ⊥ := inf_eq_bot_of_fixed_point_free hc hW hWc hQc hfix hWQ
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hquot : Nat.card (Γ ⧸ Q) = 12 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Q
    rw [hΓ] at h
    exact (Nat.eq_of_mul_eq_mul_right hQpos h).symm
  obtain ⟨b, hbB, hbQ⟩ : ∃ b ∈ B, b ∉ Q := by
    by_contra h
    push Not at h
    have hle : B ≤ Q := h
    have h1 : B ⊓ Q = B := inf_eq_left.2 hle
    rw [h1] at hB
    have hBpos : 0 < Nat.card B := Nat.card_pos
    omega
  have hidx2 : ∀ x ∈ B, x ∉ Q → ∀ y ∈ B, y ∉ Q → x⁻¹ * y ∈ Q := by
    intro x hx hxQ y hy hyQ
    have hle : B ⊓ Q ≤ B := inf_le_left
    have hcard : Nat.card ((B ⊓ Q).subgroupOf B) = Nat.card ↥(B ⊓ Q) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hind : ((B ⊓ Q).subgroupOf B).index = 2 := by
      have h := Subgroup.card_mul_index ((B ⊓ Q).subgroupOf B)
      rw [hcard, hB] at h
      have hpos : 0 < Nat.card ↥(B ⊓ Q) := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h]; ring)
    have hX : (⟨x, hx⟩ : B) ∉ (B ⊓ Q).subgroupOf B := fun h => hxQ (Subgroup.mem_inf.1 h).2
    have hY : (⟨y, hy⟩ : B) ∉ (B ⊓ Q).subgroupOf B := fun h => hyQ (Subgroup.mem_inf.1 h).2
    have hXY : (⟨x, hx⟩ : B)⁻¹ * ⟨y, hy⟩ ∈ (B ⊓ Q).subgroupOf B :=
      (Subgroup.mul_mem_iff_of_index_two hind).2
        (iff_of_false (fun h => hX (by simpa using h)) hY)
    exact (Subgroup.mem_inf.1 hXY).2
  let π : Γ →* Γ ⧸ Q := QuotientGroup.mk' Q
  have hπeq : ∀ x y : Γ, π x = π y ↔ x⁻¹ * y ∈ Q := fun x y => QuotientGroup.eq
  have hπone : ∀ x : Γ, π x = 1 ↔ x ∈ Q := fun x => QuotientGroup.eq_one_iff x
  have hbne : π b ≠ 1 := fun h => hbQ ((hπone b).1 h)
  have hbsq : π b * π b = 1 := by
    have hbinvB : b⁻¹ ∈ B := B.inv_mem hbB
    have hbinvQ : b⁻¹ ∉ Q := fun h => hbQ (by simpa using Q.inv_mem h)
    have := hidx2 b⁻¹ hbinvB hbinvQ b hbB hbQ
    rw [inv_inv] at this
    rw [← map_mul]
    exact (hπone _).2 this
  have hcentral : ∀ g : Γ, π g * π b = π b * π g := by
    intro g
    have hgb : g * b * g⁻¹ ∈ B := Normal.conj_mem ‹B.Normal› b hbB g
    have hgbQ : g * b * g⁻¹ ∉ Q := fun h => hbQ (by
      have := Normal.conj_mem ‹Q.Normal› _ h g⁻¹
      simpa [mul_assoc] using this)
    have h := hidx2 b hbB hbQ (g * b * g⁻¹) hgb hgbQ
    have h2 : π b = π (g * b * g⁻¹) := (hπeq _ _).2 h
    rw [map_mul, map_mul, map_inv] at h2
    calc π g * π b = (π g * π b * (π g)⁻¹) * π g := by group
      _ = π b * π g := by rw [← h2]
  have hcentral' : ∀ gb : Γ ⧸ Q, gb * π b = π b * gb := by
    intro gb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    exact hcentral g
  let φ : W →* Γ ⧸ Q := π.comp W.subtype
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have hxQ : (x : Γ) ∈ Q := (hπone _).1 hx
      have : (x : Γ) ∈ W ⊓ Q := ⟨x.2, hxQ⟩
      rw [hWQ'] at this
      exact Subtype.ext (Subgroup.mem_bot.1 this)
    · intro hx
      rw [hx, map_one]
  let V : Subgroup (Γ ⧸ Q) := φ.range
  have hVcard : Nat.card V = 4 := by
    rw [← hW]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hVcard]; norm_num)
  have hVidx : ¬ 2 ∣ V.index := by
    have h := Subgroup.card_mul_index V
    rw [hVcard, hquot] at h
    have : V.index = 3 := by omega
    rw [this]
    decide
  let PV : Sylow 2 (Γ ⧸ Q) := hVp.toSylow hVidx
  have hZp : IsPGroup 2 (Subgroup.zpowers (π b)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : orderOf (π b) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hbsq) hbne
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, this]
    norm_num
  obtain ⟨P', hZP'⟩ := hZp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Γ ⧸ Q) P' PV
  have hbP' : π b ∈ (P' : Subgroup (Γ ⧸ Q)) := hZP' (Subgroup.mem_zpowers _)
  have hconj : g * π b * g⁻¹ ∈ ((g • P' : Sylow 2 (Γ ⧸ Q)) : Subgroup (Γ ⧸ Q)) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨π b, hbP', by simp [MulAut.conj_apply]⟩
  rw [hg] at hconj
  have hPV : (PV : Subgroup (Γ ⧸ Q)) = V := rfl
  rw [hPV, hcentral' g, mul_assoc, mul_inv_cancel, mul_one] at hconj
  obtain ⟨w, hw⟩ := hconj
  have hw1 : (w : Γ) ≠ 1 := fun h => hbne (by
    rw [← hw]
    show π (w : Γ) = 1
    rw [h, map_one])
  have hcw : c * (w : Γ) * c⁻¹ ∈ W := hWc w w.2
  have himg : φ ⟨c * (w : Γ) * c⁻¹, hcw⟩ = φ w := by
    show π (c * (w : Γ) * c⁻¹) = π (w : Γ)
    have hw' : π (w : Γ) = π b := hw
    rw [map_mul, map_mul, map_inv, hw']
    calc π c * π b * (π c)⁻¹ = (π b * π c) * (π c)⁻¹ := by rw [hcentral c]
      _ = π b := by group
  have := hφinj himg
  exact hw1 (hfix w w.2 (congrArg Subtype.val this))

theorem W_le_Q_of_le {G : Type*} [Group G] [Finite G] {Γ Q B W : Subgroup G}
    (hQΓ : Q ≤ Γ) (hBΓ : B ≤ Γ) (hWΓ : W ≤ Γ)
    (hQn : ∀ g ∈ Γ, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hBn : ∀ g ∈ Γ, ∀ b ∈ B, g * b * g⁻¹ ∈ B)
    (hΓ : Nat.card Γ = 12 * Nat.card Q)
    (hB : Nat.card B = 2 * Nat.card ↥(B ⊓ Q)) {c : G} (hcΓ : c ∈ Γ) (hc : c ^ 3 = 1)
    (hW : Nat.card W = 4) (hWc : ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    (hfix : ∀ w ∈ W, c * w * c⁻¹ = w → w = 1) : W ≤ Q := by
  classical
  have : (Q.subgroupOf Γ).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hQn g g.2 n hn⟩
  have : (B.subgroupOf Γ).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hBn g g.2 n hn⟩
  have hQcard : Nat.card (Q.subgroupOf Γ) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQΓ).toEquiv
  have hBcard : Nat.card (B.subgroupOf Γ) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBΓ).toEquiv
  have hWcard : Nat.card (W.subgroupOf Γ) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWΓ).toEquiv
  have hBQcard : Nat.card ((B.subgroupOf Γ) ⊓ (Q.subgroupOf Γ) : Subgroup Γ) =
      Nat.card (B ⊓ Q : Subgroup G) := by
    have h : (B.subgroupOf Γ) ⊓ (Q.subgroupOf Γ) = (B ⊓ Q).subgroupOf Γ :=
      (Subgroup.comap_inf B Q Γ.subtype).symm
    rw [h]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hBΓ)).toEquiv
  have hmain := W_le_Q (Γ := Γ) (Q := Q.subgroupOf Γ) (B := B.subgroupOf Γ)
    (W := W.subgroupOf Γ)
    (by rw [hQcard]; exact hΓ) (by rw [hBcard, hBQcard]; exact hB)
    (c := ⟨c, hcΓ⟩) (Subtype.ext (by simpa using hc)) (by rw [hWcard]; exact hW)
    (fun w hw => by
      rw [Subgroup.mem_subgroupOf] at hw ⊢
      exact hWc _ hw)
    (fun w hw hcw => by
      rw [Subgroup.mem_subgroupOf] at hw
      apply Subtype.ext
      exact hfix _ hw (by simpa using congrArg Subtype.val hcw))
  intro w hw
  have := hmain (Subgroup.mem_subgroupOf.2 (by simpa using hw) : (⟨w, hWΓ hw⟩ : Γ) ∈ W.subgroupOf Γ)
  exact Subgroup.mem_subgroupOf.1 this

end CFSG.Quasithin.A10
