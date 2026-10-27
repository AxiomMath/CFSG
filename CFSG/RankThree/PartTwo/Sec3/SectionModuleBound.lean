module

public import CFSG.RankThree.PartTwo.Sec3.ElemTwoModuleBound
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_lt_self [Finite G] {p : ℕ} [Fact p.Prime] {Q W : Subgroup G}
    (hQ : IsPGroup p Q) [W.Normal] (hWQ : W ≤ Q) (hW : W ≠ ⊥) : ⁅W, Q⁆ < W := by
  refine lt_of_le_of_ne (commutator_le_left W Q) fun h => hW ?_
  have hnil : Group.IsNilpotent Q := hQ.isNilpotent
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries Q).mp hnil
  have key : ∀ k, W ≤ Q.lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact hWQ
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ, ← h]
      exact commutator_mono ih le_rfl
  rw [eq_bot_iff, ← hn]
  exact key n

theorem commute_of_odd_of_stabilizes {P W' : Subgroup G} (hP : IsPGroup 2 P) (hW'P : W' ≤ P)
    {k : G} (hk : Odd (orderOf k)) (hkP : ∀ p ∈ P, k * p * k⁻¹ * p⁻¹ ∈ W')
    (hkW' : ∀ w ∈ W', k * w * k⁻¹ = w) {p : G} (hp : p ∈ P) : k * p * k⁻¹ = p := by
  obtain ⟨w, hwdef⟩ : ∃ w, w = k * p * k⁻¹ * p⁻¹ := ⟨_, rfl⟩
  have hw : w ∈ W' := hwdef ▸ hkP p hp
  have hkp : k * p * k⁻¹ = w * p := by rw [hwdef]; group
  have hpow : ∀ m : ℕ, k ^ m * p * (k ^ m)⁻¹ = w ^ m * p := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hkw : k * w ^ m * k⁻¹ = w ^ m := by
        rw [← conj_pow, hkW' w hw]
      calc k ^ (m + 1) * p * (k ^ (m + 1))⁻¹ = k * (k ^ m * p * (k ^ m)⁻¹) * k⁻¹ := by group
        _ = k * w ^ m * k⁻¹ * (k * p * k⁻¹) := by rw [ih]; group
        _ = w ^ (m + 1) * p := by rw [hkw, hkp, pow_succ, mul_assoc]
  have h1 := hpow (orderOf k)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have hwm : w ^ orderOf k = 1 := by
    have := mul_right_cancel (h1.symm.trans (one_mul p).symm)
    exact this
  obtain ⟨j, hj⟩ := hP ⟨w, hW'P hw⟩
  have hwj : w ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have hdvd : orderOf w ∣ Nat.gcd (orderOf k) (2 ^ j) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hwm) (orderOf_dvd_of_pow_eq_one hwj)
  have hcop : Nat.Coprime (orderOf k) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hk)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  rw [hkp, hdvd, one_mul]

section Section

variable (W W' : Subgroup G) [W.Normal] [W'.Normal]

theorem map_conjNormal_subgroupOf (g : G) :
    (W'.subgroupOf W).map ((MulAut.conjNormal (H := W) g : MulAut W) : W →* W) =
      W'.subgroupOf W := by
  ext ⟨w, hw⟩
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨⟨x, hxW⟩, hx, hxw⟩
    have h1 : g * x * g⁻¹ = w := congrArg Subtype.val hxw
    rw [← h1]
    exact Subgroup.Normal.conj_mem inferInstance x hx g
  · intro hw'
    refine ⟨⟨g⁻¹ * w * g⁻¹⁻¹, Subgroup.Normal.conj_mem inferInstance w hw g⁻¹⟩, ?_, ?_⟩
    · exact Subgroup.Normal.conj_mem inferInstance w hw' g⁻¹
    · apply Subtype.ext
      change g * (g⁻¹ * w * g⁻¹⁻¹) * g⁻¹ = w
      group

noncomputable def sectionAction : G →* MulAut (↥W ⧸ W'.subgroupOf W) where
  toFun g := QuotientGroup.congr (W'.subgroupOf W) (W'.subgroupOf W)
    (MulAut.conjNormal (H := W) g) (map_conjNormal_subgroupOf W W' g)
  map_one' := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H w =>
      rw [QuotientGroup.congr_mk, MulAut.one_apply, map_one, MulAut.one_apply]
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H w =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk, map_mul, MulAut.mul_apply]

theorem sectionAction_mk (g : G) (w : W) :
    sectionAction W W' g (QuotientGroup.mk w) =
      QuotientGroup.mk (MulAut.conjNormal (H := W) g w) := by
  change QuotientGroup.congr _ _ (MulAut.conjNormal (H := W) g)
    (map_conjNormal_subgroupOf W W' g) (QuotientGroup.mk w) = _
  exact QuotientGroup.congr_mk _ _ _ _ w

theorem sectionAction_eq_one {g : G} (hg : ∀ w ∈ W, g * w * g⁻¹ * w⁻¹ ∈ W') :
    sectionAction W W' g = 1 := by
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H w =>
    rw [sectionAction_mk, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := hg w w.2
    change (g * w * g⁻¹)⁻¹ * w ∈ W'
    have h2 : (g * w * g⁻¹)⁻¹ * w =
        (w : G)⁻¹ * (g * w * g⁻¹ * (w : G)⁻¹)⁻¹ * (w : G)⁻¹⁻¹ := by group
    rw [h2]
    exact Subgroup.Normal.conj_mem inferInstance _ (W'.inv_mem this) _

end Section

@[expose] def conjCommHom {W : Subgroup G} [W.Normal] (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (t : G) : W →* W where
  toFun w := w⁻¹ * MulAut.conjNormal (H := W) t w
  map_one' := by rw [inv_one, map_one, one_mul]
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    have ha' : t * (a : G) * t⁻¹ ∈ W := Subgroup.Normal.conj_mem inferInstance _ a.2 t
    have hcomm : (b : G)⁻¹ * ((a : G)⁻¹ * (t * a * t⁻¹)) = (a : G)⁻¹ * (t * a * t⁻¹) * (b : G)⁻¹ :=
      hWc _ (W.inv_mem b.2) _ (W.mul_mem (W.inv_mem a.2) ha')
    calc ((a : G) * b)⁻¹ * (t * (a * b) * t⁻¹)
        = (b : G)⁻¹ * ((a : G)⁻¹ * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
      _ = (a : G)⁻¹ * (t * a * t⁻¹) * ((b : G)⁻¹ * (t * b * t⁻¹)) := by rw [hcomm]; group

theorem conjCommHom_apply {W : Subgroup G} [W.Normal] (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (t : G) (w : W) : ((conjCommHom hWc t w : W) : G) = (w : G)⁻¹ * (t * w * t⁻¹) := rfl

theorem relIndex_centralizer_eq_card_range {W : Subgroup G} [W.Normal]
    (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (t : G) :
    (centralizer ({t} : Set G)).relIndex W = Nat.card (conjCommHom hWc t).range := by
  rw [Subgroup.relIndex, ← Subgroup.index_ker]
  congr 1
  ext w
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply Subtype.ext
    rw [conjCommHom_apply, ← h]
    change (w : G)⁻¹ * (w * t * t⁻¹) = 1
    group
  · intro h
    have h' := congrArg Subtype.val h
    rw [conjCommHom_apply] at h'
    change (w : G)⁻¹ * (t * w * t⁻¹) = 1 at h'
    have h'' : t * (w : G) * t⁻¹ = w := by
      calc t * (w : G) * t⁻¹ = w * ((w : G)⁻¹ * (t * w * t⁻¹)) := by group
        _ = w := by rw [h', mul_one]
    calc (w : G) * t = t * w * t⁻¹ * t := by rw [h'']
      _ = t * w := by group

theorem relIndex_ne_zero_of_finite [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  intro h
  have := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [h, zero_mul] at this
  exact (Nat.card_pos (α := K)).ne' this.symm

section Bounds

variable [Finite G] {Q B : Subgroup G} [Q.Normal] (hQ : IsPGroup 2 Q)
  (hB3 : ∀ b ∈ B, b ^ 3 = 1)

include hQ hB3 in
theorem le_relIndex_of_section (k : ℕ) (t : G)
    (hsec : ∀ W : Subgroup G, W.Normal → W ≤ Q → (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) →
      (∀ w ∈ W, w * w = 1) → (∃ b ∈ B, ∃ w ∈ W, b * w * b⁻¹ * w⁻¹ ∉ ⁅W, Q⁆) →
      k ≤ (centralizer ({t} : Set G)).relIndex W)
    (W : Subgroup G) (hWn : W.Normal) (hWQ : W ≤ Q) (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hW2 : ∀ w ∈ W, w * w = 1) (hBW : ∃ b ∈ B, ∃ w ∈ W, b * w * b⁻¹ ≠ w) :
    k ≤ (centralizer ({t} : Set G)).relIndex W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction hn : Nat.card W using Nat.strong_induction_on generalizing W with
  | _ n ih =>
  by_cases hA : ∃ b ∈ B, ∃ w ∈ W, b * w * b⁻¹ * w⁻¹ ∉ ⁅W, Q⁆
  · exact hsec W hWn hWQ hWc hW2 hA
  push Not at hA
  have hW'n : (⁅W, Q⁆).Normal := Subgroup.commutator_normal W Q
  have hW'W : ⁅W, Q⁆ ≤ W := Subgroup.commutator_le_left W Q
  have hBW' : ∃ b ∈ B, ∃ w ∈ ⁅W, Q⁆, b * w * b⁻¹ ≠ w := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b, hb, w, hw, hbw⟩ := hBW
    have hodd : Odd (orderOf b) := by
      have hdvd : orderOf b ∣ 3 := orderOf_dvd_of_pow_eq_one (hB3 b hb)
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h <;> rw [h] <;> decide
    exact hbw (commute_of_odd_of_stabilizes (hQ.to_le hWQ) hW'W hodd (fun p hp => hA b hb p hp)
      (fun w hw => hcon b hb w hw) hw)
  have hW1 : W ≠ ⊥ := by
    intro h
    obtain ⟨b, -, w, hw, hbw⟩ := hBW
    rw [h, Subgroup.mem_bot] at hw
    rw [hw, mul_one, mul_inv_cancel] at hbw
    exact hbw rfl
  have hlt : ⁅W, Q⁆ < W := commutator_lt_self hQ hWQ hW1
  have hcard : Nat.card ↥⁅W, Q⁆ < n := hn ▸ Subgroup.card_lt_of_lt hlt
  have := ih _ hcard ⁅W, Q⁆ hW'n (hW'W.trans hWQ)
    (fun a ha b hb => hWc a (hW'W ha) b (hW'W hb)) (fun w hw => hW2 w (hW'W hw)) hBW' rfl
  exact this.trans (Subgroup.relIndex_le_of_le_right hW'W (relIndex_ne_zero_of_finite _ _))

end Bounds

section SectionCase

variable [Finite G] {Q B : Subgroup G} [Q.Normal]
  (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB3 : ∀ b ∈ B, b ^ 3 = 1) (hB9 : Nat.card B = 9)
  (htr : ∀ d ∈ B, ∀ d' ∈ B, d ≠ 1 → d' ≠ 1 → ∃ n ∈ normalizer (B : Set G), n * d * n⁻¹ = d')
include hBc hB3 hB9 htr

omit [Finite G] [Q.Normal] hBc hB3 hB9 htr in
theorem card_map_le_card [Finite G] {H : Type*} [Group H] (f : G →* H) (K : Subgroup G) :
    Nat.card (K.map f) ≤ Nat.card K := by
  refine Nat.card_le_card_of_surjective (fun x : K => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ :
    K.map f)) ?_
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem bounds_of_section {W : Subgroup G} [W.Normal] (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hW2 : ∀ w ∈ W, w * w = 1) (hBW : ∃ b ∈ B, ∃ w ∈ W, b * w * b⁻¹ * w⁻¹ ∉ ⁅W, Q⁆) (t : G) :
    ((∃ d ∈ B, d ≠ 1 ∧ t * d * t⁻¹ * d ∈ Q) → 8 ≤ (centralizer ({t} : Set G)).relIndex W) ∧
      ((∀ b ∈ B, t * b * t⁻¹ * b ∈ Q) → 16 ≤ (centralizer ({t} : Set G)).relIndex W) := by
  classical
  have : (⁅W, Q⁆).Normal := Subgroup.commutator_normal W Q
  let _ : CommGroup B := { (inferInstance : Group B) with
    mul_comm := fun a b => Subtype.ext (hBc a a.2 b b.2) }
  let _ : Fintype B := Fintype.ofFinite B
  set N := (⁅W, Q⁆).subgroupOf W with hN
  let _ : CommGroup (W ⧸ N) := { (inferInstance : Group (W ⧸ N)) with
    mul_comm := by
      intro a b
      induction a using QuotientGroup.induction_on with
      | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hWc a a.2 b b.2) }
  set ρ := sectionAction W ⁅W, Q⁆ with hρ
  let β : B →* MulAut (W ⧸ N) :=
    { toFun := fun b => ρ (b : G)
      map_one' := map_one ρ
      map_mul' := fun a b => map_mul ρ (a : G) (b : G) }
  have hβapp : ∀ b : B, β b = ρ (b : G) := fun b => rfl
  have hV2 : ∀ v : W ⧸ N, v * v = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H w =>
    rw [← QuotientGroup.mk_mul, show w * w = 1 from Subtype.ext (hW2 w w.2),
      QuotientGroup.mk_one]
  have h3B : ∀ b : B, b ^ 3 = 1 := fun b =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hB3 b b.2)
  have hQtriv : ∀ q ∈ Q, ρ q = 1 := fun q hq => sectionAction_eq_one W ⁅W, Q⁆ (fun w hw => by
    have hc := Subgroup.commutator_mem_commutator hw hq
    have h2 : q * w * q⁻¹ * w⁻¹ = (⁅w, q⁆)⁻¹ := by rw [commutatorElement_def]; group
    rw [h2]
    exact Subgroup.inv_mem _ hc)
  have hβ : ∃ b v, β b v ≠ v := by
    obtain ⟨b₀, hb₀, w₀, hw₀, hbw₀⟩ := hBW
    refine ⟨⟨b₀, hb₀⟩, QuotientGroup.mk ⟨w₀, hw₀⟩, fun h => hbw₀ ?_⟩
    rw [hβapp, sectionAction_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    change (b₀ * w₀ * b₀⁻¹)⁻¹ * w₀ ∈ ⁅W, Q⁆ at h
    have h2 : b₀ * w₀ * b₀⁻¹ * w₀⁻¹ =
        (b₀ * w₀ * b₀⁻¹) * ((b₀ * w₀ * b₀⁻¹)⁻¹ * w₀)⁻¹ * (b₀ * w₀ * b₀⁻¹)⁻¹ := by group
    rw [h2]
    exact Subgroup.Normal.conj_mem inferInstance _ (Subgroup.inv_mem _ h) _
  have htr' : ∀ d d' : B, d ≠ 1 → d' ≠ 1 → ∃ (ν : MulAut (W ⧸ N)) (σ : MulAut B),
      σ d = d' ∧ ∀ b, ν * β b * ν⁻¹ = β (σ b) := by
    intro d d' hd hd'
    obtain ⟨n, hn, hnd⟩ := htr d d.2 d' d'.2 (fun h => hd (Subtype.ext h))
      (fun h => hd' (Subtype.ext h))
    refine ⟨ρ n, B.normalizerMonoidHom ⟨n, hn⟩, Subtype.ext ?_, fun b => ?_⟩
    · rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact hnd
    · rw [hβapp, hβapp, ← map_inv, ← map_mul, ← map_mul]
      congr 1
  have hrange : Nat.card (commHom (ρ t)).range ≤
      (centralizer ({t} : Set G)).relIndex W := by
    rw [relIndex_centralizer_eq_card_range hWc t]
    have hle : (commHom (ρ t)).range ≤
        ((conjCommHom hWc t).range).map (QuotientGroup.mk' N) := by
      rintro _ ⟨v, rfl⟩
      induction v using QuotientGroup.induction_on with
      | H w =>
      refine ⟨conjCommHom hWc t w, ⟨w, rfl⟩, ?_⟩
      rw [QuotientGroup.mk'_apply, commHom_apply, sectionAction_mk, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul]
      rfl
    exact (Subgroup.card_le_of_le hle).trans (card_map_le_card _ _)
  have hinv : ∀ b : B, t * b * t⁻¹ * b ∈ Q → ∀ v, ρ t (β b v) = β b⁻¹ (ρ t v) := by
    intro b htb v
    have hmul : ρ (t * b) = ρ ((b : G)⁻¹ * t) := by
      have hc : t * (b : G) = (t * b * t⁻¹ * b) * ((b : G)⁻¹ * t) := by group
      rw [hc, map_mul, hQtriv _ htb, one_mul]
    rw [hβapp, hβapp, Subgroup.coe_inv, ← MulAut.mul_apply, ← map_mul, hmul, map_mul,
      MulAut.mul_apply]
  refine ⟨fun ⟨d, hdB, hd1, htd⟩ => ?_, fun hta => ?_⟩
  · exact (eight_le_card_range_commHom hV2 h3B hB9 β hβ htr' (τ := ρ t) (d := ⟨d, hdB⟩)
      (fun h => hd1 (congrArg Subtype.val h)) (hinv ⟨d, hdB⟩ htd)).trans hrange
  · exact (sixteen_le_card_range_commHom hV2 h3B hB9 β hβ htr' (τ := ρ t)
      (fun b => hinv b (hta b b.2))).trans hrange

end SectionCase

section KeyBounds

variable [Finite G] {Q B : Subgroup G} [Q.Normal] (hQ : IsPGroup 2 Q)
  (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB3 : ∀ b ∈ B, b ^ 3 = 1) (hB9 : Nat.card B = 9)
  (htr : ∀ d ∈ B, ∀ d' ∈ B, d ≠ 1 → d' ≠ 1 → ∃ n ∈ normalizer (B : Set G), n * d * n⁻¹ = d')
include hQ hBc hB3 hB9 htr

theorem eight_le_relIndex_centralizer {t d : G} (hdB : d ∈ B) (hd1 : d ≠ 1)
    (htd : t * d * t⁻¹ * d ∈ Q) (W : Subgroup G) (hWn : W.Normal) (hWQ : W ≤ Q)
    (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ w ∈ W, w * w = 1)
    (hBW : ∃ b ∈ B, ∃ w ∈ W, b * w * b⁻¹ ≠ w) :
    8 ≤ (centralizer ({t} : Set G)).relIndex W :=
  le_relIndex_of_section hQ hB3 8 t (fun W' hW'n _ hW'c hW'2 hB' => by
    have := hW'n
    exact (bounds_of_section hBc hB3 hB9 htr hW'c hW'2 hB' t).1 ⟨d, hdB, hd1, htd⟩)
    W hWn hWQ hWc hW2 hBW

theorem sixteen_le_relIndex_centralizer {t : G} (hta : ∀ b ∈ B, t * b * t⁻¹ * b ∈ Q)
    (W : Subgroup G) (hWn : W.Normal) (hWQ : W ≤ Q)
    (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ w ∈ W, w * w = 1)
    (hBW : ∃ b ∈ B, ∃ w ∈ W, b * w * b⁻¹ ≠ w) :
    16 ≤ (centralizer ({t} : Set G)).relIndex W :=
  le_relIndex_of_section hQ hB3 16 t (fun W' hW'n _ hW'c hW'2 hB' => by
    have := hW'n
    exact (bounds_of_section hBc hB3 hB9 htr hW'c hW'2 hB' t).2 hta)
    W hWn hWQ hWc hW2 hBW

end KeyBounds

end CFSG.RankThree.PartTwo.Sec3
