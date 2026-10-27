module

public import CFSG.Quasithin.EmptyFaithful.S146F19
public import CFSG.Quasithin.EmptyFaithful.S146F14

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section Dihedral

theorem dihedral_eq_one_or_eq_of_conj {n : ℕ} [NeZero n] (hn : Odd n) {a s : DihedralGroup n}
    (hs : s * s = 1) (hs1 : s ≠ 1) (h : a * s * a⁻¹ = s) : a = 1 ∨ a = s := by
  have h2 : ∀ x : ZMod n, x + x = 0 → x = 0 := by
    intro x hx
    have hu : IsUnit ((2 : ℕ) : ZMod n) :=
      (ZMod.isUnit_iff_coprime 2 n).mpr (Nat.coprime_two_left.mpr hn)
    have : ((2 : ℕ) : ZMod n) * x = 0 := by
      push_cast
      rw [two_mul]
      exact hx
    exact (hu.mul_right_eq_zero).mp this
  rcases a with i | i <;> rcases s with j | j
  · exfalso
    apply hs1
    have hj : j + j = 0 := by
      have := hs
      rw [DihedralGroup.r_mul_r, ← DihedralGroup.r_zero, DihedralGroup.r.injEq] at this
      exact this
    rw [h2 j hj, DihedralGroup.r_zero]
  · left
    have h' : j - i + -i = j := by
      have := h
      rw [DihedralGroup.r_mul_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r,
        DihedralGroup.sr.injEq] at this
      exact this
    have hi : i + i = 0 := by linear_combination -h'
    rw [h2 i hi, DihedralGroup.r_zero]
  · exfalso
    apply hs1
    have hj : j + j = 0 := by
      have := hs
      rw [DihedralGroup.r_mul_r, ← DihedralGroup.r_zero, DihedralGroup.r.injEq] at this
      exact this
    rw [h2 j hj, DihedralGroup.r_zero]
  · right
    have h' : i - (j - i) = j := by
      have := h
      rw [DihedralGroup.sr_mul_sr, DihedralGroup.inv_sr, DihedralGroup.r_mul_sr,
        DihedralGroup.sr.injEq] at this
      exact this
    have hij : (i - j) + (i - j) = 0 := by linear_combination h'
    rw [sub_eq_zero.mp (h2 _ hij)]

end Dihedral

theorem exists_mem_not_mem_of_relIndex_two {G : Type} [Group G] {Q S : Subgroup G}
    (h : Q.relIndex S = 2) : ∃ s ∈ S, s ∉ Q := by
  by_contra hcon
  have hle : S ≤ Q := fun s hs => by_contra fun hn => hcon ⟨s, hs, hn⟩
  have h1 : Q.relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hle
  omega

section Norm

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem IsDec12.card_H₁_gen (hp0 : p ≠ 0) (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    Nat.card H₁ = 2 * p * Nat.card (pCoreOf 2 H) := by
  have : NeZero p := ⟨hp0⟩
  obtain ⟨hQn, ⟨e⟩⟩ := h.dihedral₁
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((pCoreOf 2 H).subgroupOf H₁)
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Q₁).toEquiv] at h1
  have h6 : Nat.card (DihedralGroup p) = 2 * p := by
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]
  rw [h1, h6]

theorem IsDec12.isSylowTwoOf_inf_H₁ (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDec12 T M H p H₀ H₁ H₂ t) :
    IsSylowTwoOf ((T ⊓ H₀) ⊓ H₁) H₁ ∧ pCoreOf 2 H ≤ (T ⊓ H₀) ⊓ H₁ ∧
      (pCoreOf 2 H).relIndex ((T ⊓ H₀) ⊓ H₁) = 2 := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hT₀ : IsSylowTwoOf (T ⊓ H₀) H₀ := B6.isSylowTwoOf_inf_normal hTsyl h.le h.le_normalizer_H₀
  have hH₀N₁ : H₀ ≤ Subgroup.normalizer (H₁ : Set G) := by
    rw [h.sup]
    exact sup_le Subgroup.le_normalizer h.swap.le_normalizer_H₂
  have hS₁ : IsSylowTwoOf ((T ⊓ H₀) ⊓ H₁) H₁ := B6.isSylowTwoOf_inf_normal hT₀ h.le₁ hH₀N₁
  have hQT : pCoreOf 2 H ≤ T := S.pCoreOf_le_T hH
  have hQS : pCoreOf 2 H ≤ (T ⊓ H₀) ⊓ H₁ := le_inf (le_inf hQT (h.Q₁.trans h.le₁)) h.Q₁
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := hTsyl.isPGroup.to_le hQT
  have hodd : Odd p := hred.prime.odd_of_ne_two hred.odd
  have hp2 : ¬ 2 ∣ p := by
    rcases hodd with ⟨k, hk⟩
    omega
  have htw : twoPart H₁ = 2 ^ 1 * Nat.card (pCoreOf 2 H) :=
    twoPart_eq_of_card_eq_odd_mul hQ2 hp2 (by rw [h.card_H₁_gen hred.prime.ne_zero]; ring)
  have hcard : Nat.card ↥((T ⊓ H₀) ⊓ H₁) = 2 * Nat.card (pCoreOf 2 H) := by
    rw [hS₁.card_eq, htw]
    ring
  refine ⟨hS₁, hQS, ?_⟩
  have hmul := Subgroup.relIndex_mul_card (pCoreOf 2 H) ((T ⊓ H₀) ⊓ H₁)
  rw [inf_eq_left.mpr hQS, hcard] at hmul
  have hQpos : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hQpos hmul

theorem IsDec12.mem_of_conj_mem (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) {s a : G} (hs : s ∈ (T ⊓ H₀) ⊓ H₁) (hsQ : s ∉ pCoreOf 2 H)
    (haH : a ∈ H₁) (ha : a * s * a⁻¹ ∈ (T ⊓ H₀) ⊓ H₁) : a ∈ (T ⊓ H₀) ⊓ H₁ := by
  obtain ⟨-, hQS, hidx⟩ := h.isSylowTwoOf_inf_H₁ S hred
  have hodd : Odd p := hred.prime.odd_of_ne_two hred.odd
  have : NeZero p := ⟨hred.prime.ne_zero⟩
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hnormQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hsH₁ : s ∈ H₁ := hs.2
  have hcQ : a * s * a⁻¹ ∉ pCoreOf 2 H := by
    intro hc
    apply hsQ
    have := (Subgroup.mem_normalizer_iff.mp (hnormQ (H.inv_mem (hH₁H haH))) (a * s * a⁻¹)).mp hc
    simpa [mul_assoc] using this
  have hcs : a * s * a⁻¹ * s⁻¹ ∈ pCoreOf 2 H := mul_inv_mem_of_relIndex_two hidx ha hs hcQ hsQ
  have hss : s * s ∈ pCoreOf 2 H := by
    have hs'Q : s⁻¹ ∉ pCoreOf 2 H := fun hh => hsQ (by simpa using (pCoreOf 2 H).inv_mem hh)
    have := mul_inv_mem_of_relIndex_two hidx hs (((T ⊓ H₀) ⊓ H₁).inv_mem hs) hsQ hs'Q
    simpa using this
  obtain ⟨hQn, ⟨e⟩⟩ := h.dihedral₁
  let φ : ↥H₁ →* DihedralGroup p :=
    e.toMonoidHom.comp (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf H₁))
  have hker : ∀ x : ↥H₁, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    show e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have h1 : φ ⟨s, hsH₁⟩ ≠ 1 := fun hh => hsQ ((hker _).mp hh)
  have h2 : φ ⟨s, hsH₁⟩ * φ ⟨s, hsH₁⟩ = 1 := by
    rw [← map_mul]
    exact (hker _).mpr hss
  have h3 : φ ⟨a, haH⟩ * φ ⟨s, hsH₁⟩ * (φ ⟨a, haH⟩)⁻¹ = φ ⟨s, hsH₁⟩ := by
    have hcs' : φ (⟨a, haH⟩ * ⟨s, hsH₁⟩ * ⟨a, haH⟩⁻¹ * ⟨s, hsH₁⟩⁻¹) = 1 := (hker _).mpr hcs
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hcs'
    exact mul_inv_eq_one.mp hcs'
  rcases dihedral_eq_one_or_eq_of_conj hodd h2 h1 h3 with h4 | h4
  · exact hQS ((hker _).mp h4)
  · have hh : φ (⟨a, haH⟩ * ⟨s, hsH₁⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h4, mul_inv_cancel]
    have h5 : a * s⁻¹ ∈ pCoreOf 2 H := (hker _).mp hh
    have h6 : a * s⁻¹ ∈ (T ⊓ H₀) ⊓ H₁ := hQS h5
    have e : a = (a * s⁻¹) * s := by group
    rw [e]
    exact ((T ⊓ H₀) ⊓ H₁).mul_mem h6 hs

theorem IsDec12.mem_inf_of_mem_normalizer (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDec12 T M H p H₀ H₁ H₂ t) {x : G} (hx : x ∈ H₀)
    (hxn : x ∈ Subgroup.normalizer ((T ⊓ H₀ : Subgroup G) : Set G)) : x ∈ T ⊓ H₀ := by
  have hN₂ : H₁ ≤ Subgroup.normalizer (H₂ : Set G) := h.le_normalizer_H₂
  have hmul : (↑(H₁ ⊔ H₂) : Set G) = ↑H₁ * ↑H₂ :=
    Subgroup.coe_mul_of_left_le_normalizer_right H₁ H₂ hN₂
  have hx' : x ∈ (↑(H₁ ⊔ H₂) : Set G) := by
    rw [← h.sup]
    exact hx
  rw [hmul] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  obtain ⟨hS₁, hQS₁, hidx₁⟩ := h.isSylowTwoOf_inf_H₁ S hred
  obtain ⟨hS₂, hQS₂, hidx₂⟩ := h.swap.isSylowTwoOf_inf_H₁ S hred
  have hcomm : ∀ {u v : G}, u ∈ H₁ → v ∈ H₂ → u * v * u⁻¹ * v⁻¹ ∈ pCoreOf 2 H := fun {u v} hu hv =>
    h.comm (Subgroup.commutator_mem_commutator hu hv)
  have hcomm' : ∀ {u v : G}, u ∈ H₂ → v ∈ H₁ → u * v * u⁻¹ * v⁻¹ ∈ pCoreOf 2 H := fun {u v} hu hv => by
    refine h.comm ?_
    rw [← Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hu hv
  have hxnorm : ∀ y ∈ T ⊓ H₀, (a * b) * y * (a * b)⁻¹ ∈ T ⊓ H₀ := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hxn y).mp hy
  have hT₀H₁ : (T ⊓ H₀) ⊓ H₁ ≤ T ⊓ H₀ := inf_le_left
  have hT₀H₂ : (T ⊓ H₀) ⊓ H₂ ≤ T ⊓ H₀ := inf_le_left
  obtain ⟨s₁, hs₁, hs₁Q⟩ := exists_mem_not_mem_of_relIndex_two hidx₁
  have haS : a ∈ (T ⊓ H₀) ⊓ H₁ := by
    have hc : b * s₁ * b⁻¹ * s₁⁻¹ ∈ pCoreOf 2 H := hcomm' hb hs₁.2
    have e : b * s₁ * b⁻¹ = (b * s₁ * b⁻¹ * s₁⁻¹) * s₁ := by group
    have hbs : b * s₁ * b⁻¹ ∈ (T ⊓ H₀) ⊓ H₁ := by
      rw [e]
      exact ((T ⊓ H₀) ⊓ H₁).mul_mem (hQS₁ hc) hs₁
    have hbsQ : b * s₁ * b⁻¹ ∉ pCoreOf 2 H := by
      intro hh
      apply hs₁Q
      have := (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem hc) hh
      rw [e] at this
      simpa [mul_assoc] using this
    refine h.mem_of_conj_mem S hred hbs hbsQ ha ?_
    have h1 : (a * b) * s₁ * (a * b)⁻¹ ∈ T ⊓ H₀ := hxnorm s₁ (hT₀H₁ hs₁)
    have h2 : (a * b) * s₁ * (a * b)⁻¹ = a * (b * s₁ * b⁻¹) * a⁻¹ := by group
    refine ⟨?_, ?_⟩
    · rw [← h2]
      exact h1
    · have hbs' : b * s₁ * b⁻¹ ∈ H₁ := hbs.2
      exact H₁.mul_mem (H₁.mul_mem ha hbs') (H₁.inv_mem ha)
  obtain ⟨s₂, hs₂, hs₂Q⟩ := exists_mem_not_mem_of_relIndex_two hidx₂
  have hbS : b ∈ (T ⊓ H₀) ⊓ H₂ := by
    refine h.swap.mem_of_conj_mem S hred hs₂ hs₂Q hb ?_
    have hw : b * s₂ * b⁻¹ ∈ H₂ := H₂.mul_mem (H₂.mul_mem hb hs₂.2) (H₂.inv_mem hb)
    have hc : a * (b * s₂ * b⁻¹) * a⁻¹ * (b * s₂ * b⁻¹)⁻¹ ∈ pCoreOf 2 H := hcomm ha hw
    have h1 : (a * b) * s₂ * (a * b)⁻¹ ∈ T ⊓ H₀ := hxnorm s₂ (hT₀H₂ hs₂)
    have h2 : (a * b) * s₂ * (a * b)⁻¹ =
        (a * (b * s₂ * b⁻¹) * a⁻¹ * (b * s₂ * b⁻¹)⁻¹) * (b * s₂ * b⁻¹) := by group
    have hS₂mem : (a * b) * s₂ * (a * b)⁻¹ ∈ (T ⊓ H₀) ⊓ H₂ := by
      refine ⟨h1, ?_⟩
      rw [h2]
      exact H₂.mul_mem (h.Q₂ hc) hw
    rw [h2] at hS₂mem
    have := ((T ⊓ H₀) ⊓ H₂).mul_mem (((T ⊓ H₀) ⊓ H₂).inv_mem (hQS₂ hc)) hS₂mem
    simpa [mul_assoc] using this
  exact (T ⊓ H₀).mul_mem (hT₀H₁ haS) (hT₀H₂ hbS)

end Norm

theorem input14616Norm_proved : Input14616Norm := by
  intro G _ _ T M S H PQ p hred H₀ H₁ H₂ t h
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  rw [h.inf_normalizer_eq hTH]
  apply le_antisymm
  · rintro x ⟨hxn, hxH⟩
    by_cases hx0 : x ∈ H₀
    · exact (h.mem_inf_of_mem_normalizer S hred hx0 hxn).1
    · have ht0 : t ∉ H₀ := fun ht0 => h.t_not (h.H₀_le_normalizer_H₁ ht0)
      have hxt : x * t⁻¹ ∈ H₀ := mul_inv_mem_of_relIndex_two h.index hxH (hTH h.t_mem) hx0 ht0
      have htn : t ∈ Subgroup.normalizer ((T ⊓ H₀ : Subgroup G) : Set G) := by
        have := h.le_normalizer_inf hred h.t_mem
        rwa [h.inf_normalizer_eq hTH] at this
      have hxtn : x * t⁻¹ ∈ Subgroup.normalizer ((T ⊓ H₀ : Subgroup G) : Set G) :=
        (Subgroup.normalizer _).mul_mem hxn ((Subgroup.normalizer _).inv_mem htn)
      have hT := (h.mem_inf_of_mem_normalizer S hred hxt hxtn).1
      have e : x = (x * t⁻¹) * t := by group
      rw [e]
      exact T.mul_mem hT h.t_mem
  · intro x hx
    refine ⟨?_, hTH hx⟩
    have := h.le_normalizer_inf hred hx
    rwa [h.inf_normalizer_eq hTH] at this

theorem stage14616_of_named_inputs_v2 (h14 : Stage14614) (h15 : Stage14615)
    (iWeak : Input14616Weak) (iOne : Input14616One) : Stage14616 :=
  stage14616_of_named_inputs h14 h15 input14616Norm_proved iWeak iOne

end CFSG.Quasithin
