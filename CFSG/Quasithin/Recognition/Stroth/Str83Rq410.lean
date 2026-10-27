module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqArc
import CFSG.Quasithin.Recognition.Stroth.Str83RqArcRoot
import CFSG.Quasithin.Recognition.Stroth.Str83RqArcRadius
import CFSG.Quasithin.Recognition.Stroth.Str83Rq410a
import CFSG.Quasithin.Recognition.Stroth.Str83RqO8

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem r40_comm_le_iff (g : G) {A B A' B' : Subgroup G}
    (hA : A.map (MulAut.conj g).toMonoidHom = A') (hB : B.map (MulAut.conj g).toMonoidHom = B') :
    ⁅A', B'⁆ ≤ A' ⊓ B' ↔ ⁅A, B⁆ ≤ A ⊓ B := by
  subst hA hB
  rw [← Subgroup.map_commutator, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective,
    Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective]

private theorem r40_comm_eq_bot_iff (g : G) {A B A' B' : Subgroup G}
    (hA : A.map (MulAut.conj g).toMonoidHom = A') (hB : B.map (MulAut.conj g).toMonoidHom = B') :
    ⁅A', B'⁆ = ⊥ ↔ ⁅A, B⁆ = ⊥ := by
  subst hA hB
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective

private theorem r40_map_Zv_tau {i j : ℤ} (k : ℤ) (h : i + 2 * k = j) :
    (t.Zv i).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Zv j := by
  subst h
  exact map_qv_tau_pow i k

private theorem r40_map_Gv {c : ℤ} {y : G}
    (hGw : ∀ u w : ℤ, (t.Gw u w).map (MulAut.conj y).toMonoidHom = t.Gw (2 * c - w) (2 * c - u))
    (i : ℤ) : (t.Gv i).map (MulAut.conj y).toMonoidHom = t.Gv (2 * c - i) := by
  have h := hGw i i
  rwa [show t.Gw i i = t.Gv i from win_self i,
    show t.Gw (2 * c - i) (2 * c - i) = t.Gv (2 * c - i) from win_self _] at h

private theorem r40_isMaxArc_idx {u u' : ℤ} {n : ℕ} (h : t.IsMaxArc u n) (hu : u = u') :
    t.IsMaxArc u' n := by
  subst hu
  exact h

private theorem r40_isFixRadius_idx {v v' : ℤ} {b : ℕ} (h : t.IsFixRadius v b) (hv : v = v') :
    t.IsFixRadius v' b := by
  subst hv
  exact h

private theorem r40_Zv_le_Gw {i u w u' w' : ℤ} (h : t.Zv i ≤ t.Gw u w) (hu : u = u')
    (hw : w = w') : t.Zv i ≤ t.Gw u' w' := by
  subst hu hw
  exact h

private theorem r40_not_le_Gv {i j j' : ℤ} (h : ¬ t.Zv i ≤ t.Gv j) (hj : j = j') :
    ¬ t.Zv i ≤ t.Gv j' := by
  subst hj
  exact h

private theorem r40_pCore_eq_bot {u w u' w' : ℤ} (h : pCoreOf 2 (t.Gw u w) = ⊥) (hu : u = u')
    (hw : w = w') : pCoreOf 2 (t.Gw u' w') = ⊥ := by
  subst hu hw
  exact h

private theorem r40_isFixRadius_reflect {c : ℤ} {y : G}
    (hGw : ∀ u w : ℤ, (t.Gw u w).map (MulAut.conj y).toMonoidHom = t.Gw (2 * c - w) (2 * c - u))
    (hZ : ∀ i : ℤ, (t.Zv i).map (MulAut.conj y).toMonoidHom = t.Zv (2 * c - i))
    {v : ℤ} {b : ℕ} (h : t.IsFixRadius v b) : t.IsFixRadius (2 * c - v) b := by
  refine ⟨?_, ?_⟩
  · have h1 := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) h.le_Gw
    rw [hZ, hGw] at h1
    exact t.r40_Zv_le_Gw h1 (by ring) (by ring)
  · intro hle
    apply Track.IsFixRadius.not_le_Gv_sub t h
    have h1 := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hle
    rw [hZ, t.r40_map_Gv hGw] at h1
    have e1 : 2 * c - (2 * c - v) = v := by ring
    have e2 : 2 * c - (2 * c - v + b + 1) = v - b - 1 := by ring
    rwa [e1, e2] at h1

private theorem r40_card_pCoreOf {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {u w : ℤ} {n : ℕ} (h : t.IsMaxArc u n) (hw : w = u + n) (hu : ¬ Even u) :
    Nat.card (pCoreOf 2 (t.Gw u w)) = 2 ^ f ∧
      ∀ X : Subgroup G, X ≤ pCoreOf 2 (t.Gw u w) → X ≠ ⊥ → t.K ≤ normalizer (X : Set G) →
        X = pCoreOf 2 (t.Gw u w) := by
  subst hw
  have h1 := Track.IsMaxArc.card_omegaOneCenterOf t hfr h (e := u) (Or.inl rfl)
  have h2 := Track.IsMaxArc.card_pCoreOf_le t hfr h (e := u) (Or.inl rfl)
  rw [if_neg hu] at h1 h2
  have heq : omegaOneCenterOf (pCoreOf 2 (t.Gw u (u + n))) = pCoreOf 2 (t.Gw u (u + n)) :=
    Subgroup.eq_of_le_of_card_ge (A4.omegaOneCenterOf_le _) (by rw [h1]; exact h2)
  refine ⟨heq ▸ h1, fun X hXQ hX hXK => le_antisymm hXQ ?_⟩
  exact heq.symm.le.trans (Track.IsMaxArc.omegaOneCenterOf_le t hfr h hXQ hX hXK)

private theorem r40_numbers {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {m b₀ b₁ : ℕ} (h : t.IsMaxArc ε (2 * m))
    (h₀ : t.IsFixRadius ε b₀) (h₁ : t.IsFixRadius (ε + 1) b₁) (hb₀ : Even b₀) (hb₁ : Odd b₁)
    (hlt : b₀ < b₁) : b₁ = b₀ + 1 ∧ b₀ < m ∧ m ≤ b₀ + 2 := by
  have h1 := Track.IsMaxArc.fixRadius_add_one t hfr h h₁
  have h2 := Track.IsMaxArc.fixRadius_self t hfr h h₀
  obtain ⟨u, hu⟩ := hb₀
  obtain ⟨v, hv⟩ := hb₁
  omega

private theorem r40_hwlog {ε c : ℤ} {m : ℕ} (hc : ε + 1 = 2 * c) (h : t.IsMaxArc ε (2 * m))
    (hb : ¬ t.IsMaxArc (ε + 1) (2 * m)) :
    ∀ k : ℤ, pCoreOf 2 (t.Gw (2 * k - 2 * m) (2 * k)) = ⊥ := by
  intro k
  by_contra hne
  apply hb
  have hk : t.IsMaxArc (2 * k - 2 * m) (2 * m) := by
    refine ⟨?_, h.pCoreOf_eq_bot⟩
    have e : 2 * k - 2 * (m : ℤ) + ((2 * m : ℕ) : ℤ) = 2 * k := by push_cast; ring
    rw [e]
    exact hne
  exact t.r40_isMaxArc_idx (Track.IsMaxArc.shift t hk (c - k + m)) (by omega)

private theorem r40_m3 {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hrq : f ≠ 2 * a + 1) {m b₀ : ℕ} (hb2 : b₀ = 2) (hm : m = 3)
    (hwlog : ∀ k : ℤ, pCoreOf 2 (t.Gw (2 * k - 2 * m) (2 * k)) = ⊥)
    (r0 : t.IsFixRadius 1 b₀) (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀))
    (hcard0 : Nat.card (t.Zv 1) = 2 ^ f * 2 ^ f) (hcard : Nat.card (t.Zv 0) = 2 ^ f)
    (hZ10 : t.Zv 0 ≤ t.Zv 1)
    (hN1 : ∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 0) : False := by
  subst hb2 hm
  have hr0 : t.IsFixRadius (-1) 2 :=
    t.r40_isFixRadius_idx (Track.IsFixRadius.shift t r0 (-1)) (by norm_num)
  have hZ2' : ¬ t.Zv (-1) ≤ t.Gv 2 := t.r40_not_le_Gv hr0.not_le_Gv (by norm_num)
  exact t.false_of_t_eq_six hfr hrq (t.r40_pCore_eq_bot (hwlog 2) (by norm_num) (by norm_num))
    (t.r40_Zv_le_Gw hZ0 (by norm_num) (by norm_num)) hZ2' hcard0 hcard hZ10 hN1

private theorem r40_m4 {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {m b₀ : ℕ} (hb2 : b₀ = 2) (hm : m = 4) (hγ : t.IsMaxArc (1 - 2 * m) (2 * m))
    (hwlog : ∀ k : ℤ, pCoreOf 2 (t.Gw (2 * k - 2 * m) (2 * k)) = ⊥)
    (hmax : ∀ u w : ℤ, ((2 * m : ℕ) : ℤ) < w - u → pCoreOf 2 (t.Gw u w) = ⊥)
    (r0 : t.IsFixRadius 1 b₀) (r1 : t.IsFixRadius 0 (b₀ + 1))
    (hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀))
    (hcard : Nat.card (t.Zv 0) = 2 ^ f) (hZ10 : t.Zv 0 ≤ t.Zv 1)
    (hN1 : ∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 0)
    (hN2 : ∀ s ∈ S, s ∉ t.Qv 1 → ∀ z ∈ t.Zv 1, s * z * s⁻¹ = z → z ∈ t.Zv 0)
    (hN3 : ∀ z ∈ t.Zv 0, z ≠ 1 → ∀ z' ∈ t.Zv 0, z' ≠ 1 → ∃ d ∈ t.D2, d * z * d⁻¹ = z') :
    False := by
  subst hb2 hm
  have hr0 : t.IsFixRadius (-1) 2 :=
    t.r40_isFixRadius_idx (Track.IsFixRadius.shift t r0 (-1)) (by norm_num)
  have hγ₁ : t.IsMaxArc (-5) (2 * 4) :=
    t.r40_isMaxArc_idx (Track.IsMaxArc.shift t hγ 1) (by norm_num)
  have hγ₂ : t.IsMaxArc (-3) (2 * 4) :=
    t.r40_isMaxArc_idx (Track.IsMaxArc.shift t hγ 2) (by norm_num)
  have hW := (t.r40_card_pCoreOf hfr hγ₂ (w := 5) (by norm_num) (by decide)).1
  have hW' := (t.r40_card_pCoreOf hfr hγ₁ (w := 3) (by norm_num) (by decide)).1
  exact t.false_of_t_eq_eight hfr hW hW' (hmax (-5) 5 (by norm_num))
    (t.r40_pCore_eq_bot (hwlog 2) (by norm_num) (by norm_num))
    (t.r40_Zv_le_Gw hZ0 (by norm_num) (by norm_num))
    (t.r40_Zv_le_Gw hr0.le_Gw (by norm_num) (by norm_num))
    (t.r40_not_le_Gv hr0.not_le_Gv (by norm_num))
    (t.r40_Zv_le_Gw r1.le_Gw (by norm_num) (by norm_num))
    (t.r40_not_le_Gv (Track.IsFixRadius.not_le_Gv_sub t r1) (by norm_num))
    (t.r40_not_le_Gv r1.not_le_Gv (by norm_num)) hcard hZ10 hN1 hN2 hN3

private theorem r40_core {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1) (hO4 : t.GT = t.K) {m b₀ : ℕ}
    (hγ : t.IsMaxArc (1 - 2 * m) (2 * m)) (hb₀ : Even b₀)
    (hwlog : ∀ k : ℤ, pCoreOf 2 (t.Gw (2 * k - 2 * m) (2 * k)) = ⊥)
    (r0 : t.IsFixRadius 1 b₀) (r1 : t.IsFixRadius 0 (b₀ + 1))
    (hm1 : m ≤ b₀ + 2) (hm2 : b₀ < m) (hX : ⁅t.Zv 1, t.Zv (1 - b₀)⁆ ≠ ⊥) : False := by
  have hb₀1 : 1 ≤ b₀ := Track.IsFixRadius.one_le t hfr r0
  have hmax := hγ.pCoreOf_eq_bot
  obtain ⟨hQ, hKQ⟩ := t.r40_card_pCoreOf hfr hγ (w := 1) (by push_cast; ring)
    (by rintro ⟨r, hr⟩; omega)
  have hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀) := r0.le_Gw
  have hZ0' : ¬ t.Zv 1 ≤ t.Gv (2 + b₀) := t.r40_not_le_Gv r0.not_le_Gv (by ring)
  have hZ1 : t.Zv 0 ≤ t.Gw (-((b₀ + 1 : ℕ) : ℤ)) (b₀ + 1) :=
    t.r40_Zv_le_Gw r1.le_Gw (by ring) (by push_cast; ring)
  have h3 : 3 * b₀ ≤ 2 * m := t.three_mul_le_of_commutator_ne_bot hfr hb₀ hmax hZ0 hX
  have hC0 := t.Zv_one_inf_centralizer_L2_eq_bot hfr hO4 hb₀ hm1 hmax hQ hKQ hwlog
    hZ0 hZ1
  obtain ⟨hcard0, hcardA, hN1, hN2, hN3⟩ := t.natural_Zv_one hfr hb₀ hZ0 hZ0' hC0
  have hA := (t.Zv_zero_eq_and_le_centralizer hfr hb₀ hb₀1 hm1 hm2 h3 hQ hwlog hZ1 hcardA).1
  have hb2 := t.eq_two_of_Zv_zero_eq hfr hO4 hb₀ hZ0 hZ0' hZ1 hA hcard0 hcardA hN1 hN2
  rw [← hA] at hcardA hN1 hN2 hN3
  have hZ10 : t.Zv 0 ≤ t.Zv 1 := hA ▸ inf_le_left
  rcases (show m = 3 ∨ m = 4 by omega) with hm | hm
  · exact t.r40_m3 hfr hrq hb2 hm hwlog r0 hZ0 hcard0 hcardA hZ10 hN1
  · exact t.r40_m4 hfr hb2 hm hγ hwlog hmax r0 r1 hZ0 hcardA hZ10 hN1 hN2 hN3

private theorem r40_false {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1) (hO4 : t.GT = t.K) {ε c : ℤ}
    {n b₀ b₁ : ℕ} (h : t.IsMaxArc ε n) (h₀ : t.IsFixRadius ε b₀)
    (h₁ : t.IsFixRadius (ε + 1) b₁) (hb₀ : Even b₀) (hb₁ : Odd b₁) (hlt : b₀ < b₁)
    (hb : ¬ t.IsMaxArc (ε + 1) n) (hγ : t.IsMaxArc (1 - n) n) (r0 : t.IsFixRadius 1 b₀)
    (r1 : t.IsFixRadius 0 b₁) (hX : ⁅t.Zv 1, t.Zv (1 - b₀)⁆ ≠ ⊥) (hc : ε + 1 = 2 * c) : False := by
  obtain ⟨m, hm⟩ := Track.IsMaxArc.even t hfr h hrq
  obtain rfl : n = 2 * m := by omega
  obtain ⟨hb₁', hm2, hm1⟩ := t.r40_numbers hfr h h₀ h₁ hb₀ hb₁ hlt
  subst hb₁'
  exact t.r40_core hfr hrq hO4 (t.r40_isMaxArc_idx hγ (by push_cast; ring)) hb₀
    (t.r40_hwlog hc h hb) r0 r1 hm1 hm2 hX

private theorem r40_odd {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1) (hO4 : t.GT = t.K) {ε : ℤ} {n b₀ b₁ : ℕ}
    (h : t.IsMaxArc ε n) (h₀ : t.IsFixRadius ε b₀) (h₁ : t.IsFixRadius (ε + 1) b₁)
    (hb₀ : Even b₀) (hb₁ : Odd b₁) (hlt : b₀ < b₁) (ho : Odd ε)
    (ha : ¬ ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≤ t.Zv (ε + 1) ⊓ t.Zv (ε + 1 + b₁)) :
    ⁅t.Zv ε, t.Zv (ε + b₀)⁆ ≠ ⊥ ∧ ⁅t.Zv ε, t.Zv (ε + b₀)⁆ ≤ t.Zv ε ⊓ t.Zv (ε + b₀) ∧
      t.IsMaxArc (ε + 1) n := by
  obtain ⟨k, hk⟩ := ho
  obtain ⟨y, -, -, hGw, -, hZ⟩ := t.exists_reflection (k + 1)
  have hZ' : ∀ i j : ℤ, 2 * (k + 1) - i = j →
      (t.Zv i).map (MulAut.conj y).toMonoidHom = t.Zv j := fun i j hij => by rw [hZ i, hij]
  have r0 : t.IsFixRadius 1 b₀ :=
    t.r40_isFixRadius_idx (t.r40_isFixRadius_reflect hGw hZ h₀) (by omega)
  have r1 : t.IsFixRadius 0 b₁ :=
    t.r40_isFixRadius_idx (t.r40_isFixRadius_reflect hGw hZ h₁) (by omega)
  have hna : ¬ ⁅t.Zv 0, t.Zv (-(b₁ : ℤ))⁆ ≤ t.Zv 0 ⊓ t.Zv (-(b₁ : ℤ)) := fun H =>
    ha ((r40_comm_le_iff y (hZ' (ε + 1) 0 (by omega))
      (hZ' (ε + 1 + b₁) (-(b₁ : ℤ)) (by omega))).mp H)
  have hZ1 : t.Zv 0 ≤ t.Gv (-(b₁ : ℤ)) := r1.le_Gw.trans (win_le_qv (by omega) (by omega))
  have hC := t.not_le_centralizer_Zv_one hfr hb₁ hZ1 hna
  have hZ0 : t.Zv 1 ≤ t.Gw (1 - b₀) (1 + b₀) := r0.le_Gw
  have hZ0' : ¬ t.Zv 1 ≤ t.Gv (2 + b₀) := t.r40_not_le_Gv r0.not_le_Gv (by omega)
  have hX : ⁅t.Zv 1, t.Zv (1 - b₀)⁆ ≠ ⊥ := fun e =>
    hC (t.le_centralizer_of_commutator_eq_bot hfr hb₀ hZ0 hZ0' e)
  have hA := hZ' ε 1 (by omega)
  have hB := hZ' (ε + b₀) (1 - b₀) (by omega)
  by_cases hb : t.IsMaxArc (ε + 1) n
  · exact ⟨fun e => hX ((r40_comm_eq_bot_iff y hA hB).mpr e),
      (r40_comm_le_iff y hA hB).mp (t.commutator_Zv_one_le_inf hb₀ hZ0), hb⟩
  · have hγ : t.IsMaxArc (1 - n) n :=
      t.r40_isMaxArc_idx (Track.IsMaxArc.reflect t h (k + 1)) (by omega)
    exact (t.r40_false (c := k + 1) hfr hrq hO4 h h₀ h₁ hb₀ hb₁ hlt hb hγ r0 r1 hX
      (by omega)).elim

private theorem r40_even {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {ε : ℤ} {b₀ b₁ : ℕ} (h₀ : t.IsFixRadius ε b₀) (h₁ : t.IsFixRadius (ε + 1) b₁)
    (hb₀ : Even b₀) (hb₁ : Odd b₁) (he : Even ε) :
    ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≤ t.Zv (ε + 1) ⊓ t.Zv (ε + 1 + b₁) := by
  obtain ⟨k, hk⟩ := he
  have h₀' : t.IsFixRadius 0 b₀ :=
    t.r40_isFixRadius_idx (Track.IsFixRadius.shift t h₀ (-k)) (by omega)
  have h₁' : t.IsFixRadius 1 b₁ :=
    t.r40_isFixRadius_idx (Track.IsFixRadius.shift t h₁ (-k)) (by omega)
  have hZ0 : t.Zv 0 ≤ t.Gw (-(b₀ : ℤ)) b₀ := t.r40_Zv_le_Gw h₀'.le_Gw (by omega) (by omega)
  have hZ0' : ¬ t.Zv 0 ≤ t.Gv (b₀ + 1) := t.r40_not_le_Gv h₀'.not_le_Gv (by omega)
  have hZ1 : t.Zv 1 ≤ t.Gv (1 + b₁) := h₁'.le_Gw.trans (win_le_qv (by omega) (by omega))
  have hA : (t.Zv 1).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Zv (ε + 1) :=
    t.r40_map_Zv_tau k (by omega)
  have hB : (t.Zv (1 + b₁)).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
      t.Zv (ε + 1 + b₁) := t.r40_map_Zv_tau k (by omega)
  exact (r40_comm_le_iff _ hA hB).mpr
    (t.commutator_le_inf_of_even_of_sz hfr hb₀ hZ0 hZ0' hb₁ hZ1)

theorem IsMaxArc.commutator_le_inf_or_of_even
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1)
    (hO4 : t.GT = t.K) {ε : ℤ} {n b₀ b₁ : ℕ} (h : t.IsMaxArc ε n) (h₀ : t.IsFixRadius ε b₀)
    (h₁ : t.IsFixRadius (ε + 1) b₁) (hb₀ : Even b₀) :
    ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≤ t.Zv (ε + 1) ⊓ t.Zv (ε + 1 + b₁) ∨
      (⁅t.Zv ε, t.Zv (ε + b₀)⁆ ≠ ⊥ ∧ ⁅t.Zv ε, t.Zv (ε + b₀)⁆ ≤ t.Zv ε ⊓ t.Zv (ε + b₀) ∧
        t.IsMaxArc (ε + 1) n) := by
  by_cases ha : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≤ t.Zv (ε + 1) ⊓ t.Zv (ε + 1 + b₁)
  · exact Or.inl ha
  obtain ⟨-, hb₁, hlt⟩ := (Track.IsFixRadius.commutator_le_inf_or t h₀ h₁).resolve_left ha
  rcases Int.even_or_odd ε with he | ho
  · exact (ha (t.r40_even hfr h₀ h₁ hb₀ hb₁ he)).elim
  · exact Or.inr (t.r40_odd hfr hrq hO4 h h₀ h₁ hb₀ hb₁ hlt ho ha)

end Track

end CFSG.Quasithin.Stroth.Rq
