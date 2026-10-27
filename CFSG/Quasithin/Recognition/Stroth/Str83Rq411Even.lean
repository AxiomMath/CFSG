module

public import CFSG.Quasithin.Recognition.Stroth.Str83Rq411
public import CFSG.Quasithin.Recognition.Stroth.Str83RqArcRoot
import CFSG.Quasithin.Recognition.Stroth.Str83Rq410a
import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem r6g_card_le {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {ε : ℤ} (h : t.IsMaxArc ε 4) (h₀ : t.IsFixRadius ε 2) :
    Nat.card (t.Zv (ε + 2)) ≤ if Even ε then 2 ^ (2 * a + 1) else 2 ^ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : t.IsFixRadius (ε + 2) 2 := by simpa using Track.IsFixRadius.shift t h₀ 1
  have hZw : t.Zv (ε + 2) ≤ t.Gw ε (ε + ((4 : ℕ) : ℤ)) := fun z hz =>
    mem_win_iff.mpr fun i h1 h2' =>
      mem_win_iff.mp (h2.le_Gw hz) i (by push_cast at h1 ⊢; omega) (by push_cast at h2' ⊢; omega)
  have hZQ : t.Zv (ε + 2) ≤ pCoreOf 2 (t.Gw ε (ε + ((4 : ℕ) : ℤ))) :=
    t.le_pCoreOf_Gw hfr (by push_cast; omega) (t.isPGroup_Zv _) hZw
  have hZΩ : t.Zv (ε + 2) ≤ omegaOneCenterOf (pCoreOf 2 (t.Gw ε (ε + ((4 : ℕ) : ℤ)))) := by
    intro z hz
    refine IsMaxArc.mem_omegaOneCenterOf t hfr h (hZQ hz) ?_
    rw [t.Zv_eq] at hz
    exact A4.sq_eq_one_of_mem_omegaOneCenterOf hz
  have hc := Subgroup.card_le_of_le hZΩ
  rwa [IsMaxArc.card_omegaOneCenterOf t hfr h (e := ε) (Or.inl rfl)] at hc

private theorem r6g_comm_sz {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hcard : Nat.card (t.Zv 0) ≤ 2 ^ (2 * a + 1)) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXG : X ≤ t.Gv 0) : ⁅X, t.Zv 0⁆ = ⊥ := by
  have hq : 2 ^ (2 * a + 1) < 2 ^ (4 * (2 * a + 1)) :=
    Nat.pow_lt_pow_right (by norm_num) (by have := hfr.ha; omega)
  have hrel : (t.Zv 0 ⊓ centralizer (L1 : Set G)).relIndex (t.Zv 0) < 2 ^ (4 * (2 * a + 1)) :=
    lt_of_le_of_lt
      ((Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _)).trans hcard) hq
  have hL := t.L1_le_centralizer_Zv_zero_of_relIndex_lt hfr hrel
  have hQ : Q1 L1 L2 S ≤ centralizer (t.Zv 0 : Set G) := by
    rw [← t.Qv_zero]
    exact Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 0)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  obtain ⟨j, hj⟩ := hX ⟨x, hx⟩
  have hxj : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hxP : x ∈ P1 L1 L2 S := by
    rw [← t.Gv_zero]
    exact hXG hx
  exact sup_le hL hQ (t.mem_L1_sup_Q1_of_pow_eq_one hfr hxP hxj)

private theorem r6g_comm_l2 {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hcard : Nat.card (t.Zv 1) ≤ 2 ^ f) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXG : X ≤ t.Gv 1) : ⁅X, t.Zv 1⁆ = ⊥ := by
  have hr : 2 ^ f < 2 ^ f * 2 ^ f := by
    have : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := hfr.hf; omega)
    nlinarith
  have hrel : (t.Zv 1 ⊓ centralizer (L2 : Set G)).relIndex (t.Zv 1) < 2 ^ f * 2 ^ f :=
    lt_of_le_of_lt
      ((Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _)).trans hcard) hr
  have hL := t.L2_le_centralizer_Zv_one_of_relIndex_lt hfr hrel
  have hQ : Q2 L1 L2 S ≤ centralizer (t.Zv 1 : Set G) := by
    rw [← t.Qv_one]
    exact Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 1)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  obtain ⟨j, hj⟩ := hX ⟨x, hx⟩
  have hxj : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hxP : x ∈ P2 L1 L2 S := by
    rw [← t.Gv_one]
    exact hXG hx
  exact sup_le hL hQ (t.mem_L2_sup_Q2_of_pow_eq_one hfr hxP hxj)

private theorem r6g_core_even {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (h : t.IsMaxArc (-2) 4) (h₀ : t.IsFixRadius (-2) 2) (h₁ : t.IsFixRadius (-1) 1) :
    ⁅t.Zv (-1), t.Zv 0⁆ = ⊥ := by
  have hc := r6g_card_le t hfr h h₀
  rw [if_pos ⟨-1, by norm_num⟩, show (-2 : ℤ) + 2 = 0 by norm_num] at hc
  have hXG : t.Zv (-1) ≤ t.Gv 0 := h₁.le_Gw.trans (win_le_qv (by omega) (by omega))
  exact r6g_comm_sz t hfr hc (t.isPGroup_Zv _) hXG

private theorem r6g_core_odd {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (h : t.IsMaxArc (-1) 4) (h₀ : t.IsFixRadius (-1) 2) (h₁ : t.IsFixRadius 0 1) :
    ⁅t.Zv 0, t.Zv 1⁆ = ⊥ := by
  have hc := r6g_card_le t hfr h h₀
  rw [if_neg (by decide), show (-1 : ℤ) + 2 = 1 by norm_num] at hc
  have hXG : t.Zv 0 ≤ t.Gv 1 := h₁.le_Gw.trans (win_le_qv (by omega) (by omega))
  exact r6g_comm_l2 t hfr hc (t.isPGroup_Zv _) hXG

omit [Finite G] in
private theorem r6g_comm_shift (i j k : ℤ) (h : ⁅t.Zv i, t.Zv j⁆ = ⊥) :
    ⁅t.Zv (i + 2 * k), t.Zv (j + 2 * k)⁆ = ⊥ := by
  have h2 := congrArg (Subgroup.map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom) h
  rw [Subgroup.map_commutator, Subgroup.map_bot] at h2
  rwa [map_qv_tau_pow, map_qv_tau_pow] at h2

theorem IsMaxArc.commutator_eq_bot_of_eq_four {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} (h : t.IsMaxArc ε 4) (h₀ : t.IsFixRadius ε 2)
    (h₁ : t.IsFixRadius (ε + 1) 1) :
    ⁅t.Zv (ε + 1), t.Zv (ε + 2)⁆ = ⊥ := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' ε
  · have h' := Track.IsMaxArc.shift t h (-(k + 1))
    have h₀' := Track.IsFixRadius.shift t h₀ (-(k + 1))
    have h₁' := Track.IsFixRadius.shift t h₁ (-(k + 1))
    rw [show ε + 2 * -(k + 1) = -2 by omega] at h' h₀'
    rw [show ε + 1 + 2 * -(k + 1) = -1 by omega] at h₁'
    have := r6g_comm_shift t (-1) 0 (k + 1) (r6g_core_even t hfr h' h₀' h₁')
    rwa [show -1 + 2 * (k + 1) = ε + 1 by omega, show 0 + 2 * (k + 1) = ε + 2 by omega] at this
  · have h' := Track.IsMaxArc.shift t h (-(k + 1))
    have h₀' := Track.IsFixRadius.shift t h₀ (-(k + 1))
    have h₁' := Track.IsFixRadius.shift t h₁ (-(k + 1))
    rw [show ε + 2 * -(k + 1) = -1 by omega] at h' h₀'
    rw [show ε + 1 + 2 * -(k + 1) = 0 by omega] at h₁'
    have := r6g_comm_shift t 0 1 (k + 1) (r6g_core_odd t hfr h' h₀' h₁')
    rwa [show 0 + 2 * (k + 1) = ε + 1 by omega, show 1 + 2 * (k + 1) = ε + 2 by omega] at this

private theorem r6h_relIndex_ne_zero (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite (G := ↥K) (H := H.subgroupOf K)

private theorem r6h_sq_eq_one (i : ℤ) {e : G} (he : e ∈ t.Zv i) : e ^ 2 = 1 := by
  rw [t.Zv_eq i] at he
  exact A4.sq_eq_one_of_mem_omegaOneCenterOf he

private theorem r6h_map_Zv_tau (i k : ℤ) :
    (t.Zv i).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Zv (i + 2 * k) :=
  map_qv_tau_pow i k

private theorem r6h_map_Zv_x₁ (i : ℤ) :
    (t.Zv i).map (MulAut.conj t.x₁).toMonoidHom = t.Zv (-i) :=
  t.track.map_qv_x₁
    ((le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _))
    ((le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)) i

private theorem r6h_map_Zv_x₂ (i : ℤ) :
    (t.Zv i).map (MulAut.conj t.x₂).toMonoidHom = t.Zv (2 - i) :=
  t.track.map_qv_x₂
    ((le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _))
    ((le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)) i

private theorem r6h_map_Qv_x₂ (i : ℤ) :
    (t.Qv i).map (MulAut.conj t.x₂).toMonoidHom = t.Qv (2 - i) :=
  t.track.map_qv_x₂ (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _) i

private theorem r6h_shift_commutator {u w : ℤ} (h : ⁅t.Zv u, t.Zv w⁆ = ⊥) (k : ℤ) :
    ⁅t.Zv (u + 2 * k), t.Zv (w + 2 * k)⁆ = ⊥ := by
  have h2 := congrArg (Subgroup.map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom) h
  rwa [Subgroup.map_commutator, Subgroup.map_bot, t.r6h_map_Zv_tau, t.r6h_map_Zv_tau] at h2

private theorem r6h_all {v : ℤ} (h₀ : t.IsFixRadius v 1) (h₁ : t.IsFixRadius (v + 1) 1) (w : ℤ) :
    t.IsFixRadius w 1 := by
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' (w - v)
  · have := Track.IsFixRadius.shift t h₀ j
    rwa [show v + 2 * j = w by omega] at this
  · have := Track.IsFixRadius.shift t h₁ j
    rwa [show v + 1 + 2 * j = w by omega] at this

private theorem r6h_Zv_zero_le (h₀ : t.IsFixRadius 0 1) : t.Zv 0 ≤ t.Gw (-1) 1 := by
  simpa using h₀.le_Gw

private theorem r6h_Zv_one_le (h₁ : t.IsFixRadius 1 1) : t.Zv 1 ≤ t.Gw 0 2 := by
  simpa using h₁.le_Gw

private theorem r6h_not_Zv_zero_le_Gv_two (h₀ : t.IsFixRadius 0 1) : ¬ t.Zv 0 ≤ t.Gv 2 := by
  simpa using h₀.not_le_Gv

private theorem r6h_not_Zv_one_le_Gv_neg_one (h₁ : t.IsFixRadius 1 1) : ¬ t.Zv 1 ≤ t.Gv (-1) := by
  simpa using h₁.not_le_Gv_sub t

private theorem r6h_Zv_le_S {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {w : ℤ} (h : t.Zv w ≤ t.Gw 0 1) : t.Zv w ≤ S := by
  have h2 := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) (t.isPGroup_Zv w) h
  rwa [t.pCoreOf_Gw_zero_one hfr] at h2

private theorem r6h_relIndex_Qv_zero_Zv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₁ : t.IsFixRadius 1 1) :
    (t.Qv 0).relIndex (t.Zv 1) ≤ 2 ^ (2 * a + 1) := by
  have hZS : t.Zv 1 ≤ S :=
    t.r6h_Zv_le_S hfr ((t.r6h_Zv_one_le h₁).trans (win_mono le_rfl (by norm_num)))
  have hle : t.Zv 1 ≤ t.rootOmega 0 := by
    intro x hx
    rw [t.mem_rootOmega_iff hfr 0, zero_add, t.pCoreOf_Gw_zero_one hfr]
    exact ⟨hZS hx, by rw [t.r6h_sq_eq_one 1 hx]; exact one_mem _⟩
  have h := t.relIndex_rootOmega hfr 0
  rw [if_pos (by decide : Even (0 : ℤ))] at h
  exact (Subgroup.relIndex_le_of_le_right hle (r6h_relIndex_ne_zero _ _)).trans h.le

private theorem r6h_relIndex_Qv_two_Zv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₁ : t.IsFixRadius 1 1) :
    (t.Qv 2).relIndex (t.Zv 1) ≤ 2 ^ (2 * a + 1) := by
  have h := t.r6h_relIndex_Qv_zero_Zv_one hfr h₁
  rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj t.x₂).toMonoidHom) (t.Qv 0)
    (t.Zv 1) (MulAut.conj _).injective, t.r6h_map_Qv_x₂, t.r6h_map_Zv_x₂] at h
  simpa using h

private theorem r6h_x₂_mem_normalizer_C :
    t.x₂ ∈ normalizer ((t.Zv 1 ⊓ (t.Qv 0 ⊓ t.Qv 2) : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  show (t.Zv 1 ⊓ (t.Qv 0 ⊓ t.Qv 2)).map (MulAut.conj t.x₂).toMonoidHom = _
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective, t.r6h_map_Zv_x₂, t.r6h_map_Qv_x₂,
    t.r6h_map_Qv_x₂, show (2 : ℤ) - 1 = 1 by norm_num, show (2 : ℤ) - 0 = 2 by norm_num,
    show (2 : ℤ) - 2 = 0 by norm_num, inf_comm (t.Qv 2) (t.Qv 0)]

private theorem r6h_C_le_centralizer_L2 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₀ : t.IsFixRadius 0 1) :
    t.Zv 1 ⊓ (t.Qv 0 ⊓ t.Qv 2) ≤ centralizer (L2 : Set G) := by
  have hYS : t.Zv 0 ≤ S :=
    t.r6h_Zv_le_S hfr ((t.r6h_Zv_zero_le h₀).trans (win_mono (by norm_num) le_rfl))
  have hYD : t.D2 ≤ normalizer (t.Zv 0 : Set G) :=
    (le_sup_right : t.D2 ≤ t.K).trans ((t.K_le_Gv 0).trans (t.Gv_le_normalizer_Zv 0))
  have hYQ : ¬ t.Zv 0 ≤ t.Qv 1 := fun hle =>
    t.r6h_not_Zv_zero_le_Gv_two h₀ (hle.trans (by simpa using (t.Qv_le_Gv hfr 1).2))
  have hYC : t.Zv 0 ≤ centralizer ((t.Zv 1 ⊓ (t.Qv 0 ⊓ t.Qv 2) : Subgroup G) : Set G) :=
    (t.Zv_le_centralizer 0).trans (Subgroup.centralizer_le fun x hx =>
      (mem_inf.mp (mem_inf.mp hx).2).1)
  exact Subgroup.le_centralizer_iff.mp (t.L2_le_centralizer_of_l2 hfr hYS hYD hYQ inf_le_left hYC
    t.r6h_x₂_mem_normalizer_C)

private theorem r6h_relIndex_L2_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₀ : t.IsFixRadius 0 1) (h₁ : t.IsFixRadius 1 1) :
    (t.Zv 1 ⊓ centralizer (L2 : Set G)).relIndex (t.Zv 1) ≤
      2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := by
  have hle : t.Zv 1 ⊓ (t.Qv 0 ⊓ t.Qv 2) ≤ t.Zv 1 ⊓ centralizer (L2 : Set G) :=
    le_inf inf_le_left (t.r6h_C_le_centralizer_L2 hfr h₀)
  calc (t.Zv 1 ⊓ centralizer (L2 : Set G)).relIndex (t.Zv 1)
      ≤ (t.Zv 1 ⊓ (t.Qv 0 ⊓ t.Qv 2)).relIndex (t.Zv 1) :=
        Subgroup.relIndex_le_of_le_left hle (r6h_relIndex_ne_zero _ _)
    _ = (t.Qv 0 ⊓ t.Qv 2).relIndex (t.Zv 1) := by rw [inf_comm, Subgroup.inf_relIndex_right]
    _ ≤ (t.Qv 0).relIndex (t.Zv 1) * (t.Qv 2).relIndex (t.Zv 1) := Subgroup.relIndex_inf_le
    _ ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) :=
        Nat.mul_le_mul (t.r6h_relIndex_Qv_zero_Zv_one hfr h₁)
          (t.r6h_relIndex_Qv_two_Zv_one hfr h₁)

private theorem r6h_relIndex_Qv_one_Zv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₀ : t.IsFixRadius 0 1) :
    (t.Qv 1).relIndex (t.Zv 0) ≤ 2 ^ f := by
  have hw : t.Zv 0 ≤ t.Gw (1 - 1) 1 := by
    rw [sub_self]
    exact (t.r6h_Zv_zero_le h₀).trans (win_mono (by norm_num) le_rfl)
  have h := t.relIndex_Qv_le hfr 1 (t.isPGroup_Zv 0) (Or.inl hw)
  rwa [if_neg Int.not_even_one] at h

private theorem r6h_relIndex_Qv_neg_one_Zv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₀ : t.IsFixRadius 0 1) :
    (t.Qv (-1)).relIndex (t.Zv 0) ≤ 2 ^ f := by
  have hw : t.Zv 0 ≤ t.Gw (-1) (-1 + 1) := by
    rw [neg_add_cancel]
    exact (t.r6h_Zv_zero_le h₀).trans (win_mono le_rfl (by norm_num))
  have h := t.relIndex_Qv_le hfr (-1) (t.isPGroup_Zv 0) (Or.inr hw)
  rwa [if_neg (by decide : ¬ Even (-1 : ℤ))] at h

private theorem r6h_C_le_centralizer_L1 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₁ : t.IsFixRadius 1 1) :
    t.Zv 0 ⊓ (t.Qv 1 ⊓ t.Qv (-1)) ≤ centralizer (L1 : Set G) := by
  have hYS : t.Zv 1 ≤ S :=
    t.r6h_Zv_le_S hfr ((t.r6h_Zv_one_le h₁).trans (win_mono le_rfl (by norm_num)))
  have hYD : t.D1 ≤ normalizer (t.Zv 1 : Set G) :=
    (le_sup_left : t.D1 ≤ t.K).trans ((t.K_le_Gv 1).trans (t.Gv_le_normalizer_Zv 1))
  have hYQ : ¬ t.Zv 1 ≤ t.Qv 0 := fun hle =>
    t.r6h_not_Zv_one_le_Gv_neg_one h₁ (hle.trans (by simpa using (t.Qv_le_Gv hfr 0).1))
  have hY : t.Zv 1 ≤ centralizer ((t.Zv 0 ⊓ (t.Qv 1 ⊓ t.Qv (-1)) : Subgroup G) : Set G) :=
    (t.Zv_le_centralizer 1).trans (Subgroup.centralizer_le fun x hx =>
      (mem_inf.mp (mem_inf.mp hx).2).1)
  have hY' : (t.Zv 1).map (MulAut.conj t.x₁).toMonoidHom ≤
      centralizer ((t.Zv 0 ⊓ (t.Qv 1 ⊓ t.Qv (-1)) : Subgroup G) : Set G) := by
    rw [t.r6h_map_Zv_x₁]
    exact (t.Zv_le_centralizer (-1)).trans (Subgroup.centralizer_le fun x hx =>
      (mem_inf.mp (mem_inf.mp hx).2).2)
  exact Subgroup.le_centralizer_iff.mp
    (t.L1_le_centralizer_of_sz hfr hYS hYD hYQ inf_le_left hY hY')

private theorem r6h_relIndex_L1_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₀ : t.IsFixRadius 0 1) (h₁ : t.IsFixRadius 1 1) :
    (t.Zv 0 ⊓ centralizer (L1 : Set G)).relIndex (t.Zv 0) ≤ 2 ^ f * 2 ^ f := by
  have hle : t.Zv 0 ⊓ (t.Qv 1 ⊓ t.Qv (-1)) ≤ t.Zv 0 ⊓ centralizer (L1 : Set G) :=
    le_inf inf_le_left (t.r6h_C_le_centralizer_L1 hfr h₁)
  calc (t.Zv 0 ⊓ centralizer (L1 : Set G)).relIndex (t.Zv 0)
      ≤ (t.Zv 0 ⊓ (t.Qv 1 ⊓ t.Qv (-1))).relIndex (t.Zv 0) :=
        Subgroup.relIndex_le_of_le_left hle (r6h_relIndex_ne_zero _ _)
    _ = (t.Qv 1 ⊓ t.Qv (-1)).relIndex (t.Zv 0) := by rw [inf_comm, Subgroup.inf_relIndex_right]
    _ ≤ (t.Qv 1).relIndex (t.Zv 0) * (t.Qv (-1)).relIndex (t.Zv 0) := Subgroup.relIndex_inf_le
    _ ≤ 2 ^ f * 2 ^ f :=
        Nat.mul_le_mul (t.r6h_relIndex_Qv_one_Zv_zero hfr h₀)
          (t.r6h_relIndex_Qv_neg_one_Zv_zero hfr h₀)

private theorem r6h_le_centralizer_Zv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hL : L2 ≤ centralizer (t.Zv 1 : Set G)) {w : ℤ}
    (hw : t.Zv w ≤ t.Gv 1) : t.Zv w ≤ centralizer (t.Zv 1 : Set G) := by
  have hQ : Q2 L1 L2 S ≤ centralizer (t.Zv 1 : Set G) := by
    rw [← t.Qv_one]
    exact Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 1)
  intro z hz
  obtain ⟨j, hj⟩ := t.isPGroup_Zv w ⟨z, hz⟩
  have hz1 : z ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hzP : z ∈ P2 L1 L2 S := by
    rw [← t.Gv_one]
    exact hw hz
  exact sup_le hL hQ (t.mem_L2_sup_Q2_of_pow_eq_one hfr hzP hz1)

private theorem r6h_le_centralizer_Zv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hL : L1 ≤ centralizer (t.Zv 0 : Set G)) {w : ℤ}
    (hw : t.Zv w ≤ t.Gv 0) : t.Zv w ≤ centralizer (t.Zv 0 : Set G) := by
  have hQ : Q1 L1 L2 S ≤ centralizer (t.Zv 0 : Set G) := by
    rw [← t.Qv_zero]
    exact Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 0)
  intro z hz
  obtain ⟨j, hj⟩ := t.isPGroup_Zv w ⟨z, hz⟩
  have hz1 : z ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hzP : z ∈ P1 L1 L2 S := by
    rw [← t.Gv_zero]
    exact hw hz
  exact sup_le hL hQ (t.mem_L1_sup_Q1_of_pow_eq_one hfr hzP hz1)

private theorem r6h_base_of_lt {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hlt : f < 2 * a + 1) (h₀ : t.IsFixRadius 0 1) (h₁ : t.IsFixRadius 1 1) :
    ⁅t.Zv 0, t.Zv 1⁆ = ⊥ ∧ ⁅t.Zv 1, t.Zv 2⁆ = ⊥ := by
  have hrel : (t.Zv 0 ⊓ centralizer (L1 : Set G)).relIndex (t.Zv 0) < 2 ^ (4 * (2 * a + 1)) := by
    refine lt_of_le_of_lt (t.r6h_relIndex_L1_le hfr h₀ h₁) ?_
    rw [← pow_add]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hL := t.L1_le_centralizer_Zv_zero_of_relIndex_lt hfr hrel
  have hm1 : t.IsFixRadius (-1) 1 := by simpa using Track.IsFixRadius.shift t h₁ (-1)
  have hZ1 : t.Zv 1 ≤ t.Gv 0 := (t.r6h_Zv_one_le h₁).trans (win_le_qv le_rfl (by norm_num))
  have hZm : t.Zv (-1) ≤ t.Gv 0 := by
    have := hm1.le_Gw
    exact (by simpa using this : t.Zv (-1) ≤ t.Gw (-2) 0).trans (win_le_qv (by norm_num) le_rfl)
  refine ⟨?_, ?_⟩
  · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact t.r6h_le_centralizer_Zv_zero hfr hL hZ1
  · have h1 : ⁅t.Zv (-1), t.Zv 0⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (t.r6h_le_centralizer_Zv_zero hfr hL hZm)
    simpa using t.r6h_shift_commutator h1 1

private theorem r6h_base_of_gt {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hlt : 2 * a + 1 < f) (h₀ : t.IsFixRadius 0 1) (h₁ : t.IsFixRadius 1 1) :
    ⁅t.Zv 0, t.Zv 1⁆ = ⊥ ∧ ⁅t.Zv 1, t.Zv 2⁆ = ⊥ := by
  have hrel : (t.Zv 1 ⊓ centralizer (L2 : Set G)).relIndex (t.Zv 1) < 2 ^ f * 2 ^ f := by
    refine lt_of_le_of_lt (t.r6h_relIndex_L2_le hfr h₀ h₁) ?_
    exact Nat.mul_self_lt_mul_self (Nat.pow_lt_pow_right (by norm_num) hlt)
  have hL := t.L2_le_centralizer_Zv_one_of_relIndex_lt hfr hrel
  have h₂ : t.IsFixRadius 2 1 := by simpa using Track.IsFixRadius.shift t h₀ 1
  have hZ0 : t.Zv 0 ≤ t.Gv 1 := (t.r6h_Zv_zero_le h₀).trans (win_le_qv (by norm_num) le_rfl)
  have hZ2 : t.Zv 2 ≤ t.Gv 1 := by
    have := h₂.le_Gw
    exact (by simpa using this : t.Zv 2 ≤ t.Gw 1 3).trans (win_le_qv le_rfl (by norm_num))
  refine ⟨?_, ?_⟩
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (t.r6h_le_centralizer_Zv_one hfr hL hZ0)
  · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact t.r6h_le_centralizer_Zv_one hfr hL hZ2

private theorem r6h_base {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hrq : f ≠ 2 * a + 1) (h₀ : t.IsFixRadius 0 1) (h₁ : t.IsFixRadius 1 1) :
    ⁅t.Zv 0, t.Zv 1⁆ = ⊥ ∧ ⁅t.Zv 1, t.Zv 2⁆ = ⊥ := by
  rcases lt_or_gt_of_ne hrq with hlt | hlt
  · exact t.r6h_base_of_lt hfr hlt h₀ h₁
  · exact t.r6h_base_of_gt hfr hlt h₀ h₁

theorem IsFixRadius.commutator_eq_bot_of_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1)
    {v : ℤ} (h₀ : t.IsFixRadius v 1) (h₁ : t.IsFixRadius (v + 1) 1) :
    ⁅t.Zv v, t.Zv (v + 1)⁆ = ⊥ := by
  obtain ⟨hA, hB⟩ := t.r6h_base hfr hrq (t.r6h_all h₀ h₁ 0) (t.r6h_all h₀ h₁ 1)
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' v
  · have := t.r6h_shift_commutator hA k
    rwa [show (0 : ℤ) + 2 * k = 2 * k by ring, show (1 : ℤ) + 2 * k = 2 * k + 1 by ring] at this
  · have := t.r6h_shift_commutator hB k
    rwa [show (1 : ℤ) + 2 * k = 2 * k + 1 by ring,
      show (2 : ℤ) + 2 * k = 2 * k + 1 + 1 by ring] at this

private theorem r6f_map_Gw_x₂ (a b : ℤ) :
    (t.Gw a b).map (MulAut.conj t.x₂).toMonoidHom = t.Gw (2 - b) (2 - a) :=
  t.track.map_win_x₂ Subgroup.le_normalizer Subgroup.le_normalizer a b

private theorem r6f_Zv_comm (i : ℤ) {x y : G} (hx : x ∈ t.Zv i) (hy : y ∈ t.Zv i) :
    x * y = y * x :=
  (mem_centralizer_iff.mp (t.Zv_le_centralizer i hx) y (t.Zv_le_Qv i hy)).symm

private theorem r6f_pCoreOf_le_Qv_one (hF : Hyp111 L1 L2 S) : pCoreOf 2 L2 ≤ t.Qv 1 := by
  have h := Hyp111.pCoreOf_le_pCoreOf_vertex hF.symm
  rw [bigB_comm] at h
  rw [t.Qv_one]
  exact h

private theorem r6f_Zv_le_Gv {v : ℤ} {b : ℕ} (h : t.IsFixRadius v b) {i : ℤ}
    (h1 : v - b ≤ i) (h2 : i ≤ v + b) : t.Zv v ≤ t.Gv i :=
  h.le_Gw.trans (win_le_qv h1 h2)

private theorem r6f_Zv_le_Gw {v : ℤ} {b : ℕ} (h : t.IsFixRadius v b) {u w : ℤ}
    (h1 : v - b ≤ u) (h2 : w ≤ v + b) : t.Zv v ≤ t.Gw u w :=
  h.le_Gw.trans (win_mono h1 h2)

private theorem r6f_le_normalizer_commutator {H A B : Subgroup G}
    (hA : H ≤ normalizer (A : Set G)) (hB : H ≤ normalizer (B : Set G)) :
    H ≤ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro h hh
  have hA' : A.map (MulAut.conj h).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hh)
  have hB' : B.map (MulAut.conj h).toMonoidHom = B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hh)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (⁅A, B⁆ : Subgroup G).map (MulAut.conj h).toMonoidHom = ⁅A, B⁆
  rw [Subgroup.map_commutator, hA', hB']

private theorem r6f_commutator_sup {A Q Z : Subgroup G} (hA : A ≤ normalizer (Q : Set G))
    (hQ : Q ≤ centralizer (Z : Set G)) : ⁅A ⊔ Q, Z⁆ = ⁅A, Z⁆ := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun g hg z hz => ?_)
    (Subgroup.commutator_mono le_sup_left le_rfl)
  have hg' : g ∈ ((A ⊔ Q : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A Q hA] at hg'
  obtain ⟨a, ha, q, hq, rfl⟩ := hg'
  have hzq : z * q = q * z := mem_centralizer_iff.mp (hQ hq) z hz
  have hqz : q * z * q⁻¹ = z := by rw [← hzq, mul_inv_cancel_right]
  have e : ⁅a * q, z⁆ = ⁅a, z⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * q * z * (a * q)⁻¹ * z⁻¹ = a * (q * z * q⁻¹) * a⁻¹ * z⁻¹ := by group
      _ = a * z * a⁻¹ * z⁻¹ := by rw [hqz]
  rw [e]
  exact Subgroup.commutator_mem_commutator ha hz

private theorem r6f_root_eq {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (w i : ℤ) (hi : t.Zv i ≤ t.Gw w (w + 1)) (hn : ¬ t.Zv i ≤ t.Gv (w - 1)) :
    t.Zv i ⊔ t.Qv w = t.rootOmega w := by
  have hp : t.Zv i ≤ pCoreOf 2 (t.Gw w (w + 1)) :=
    t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv i) hi
  have hK : t.K ≤ normalizer (t.Zv i : Set G) := (t.K_le_Gv i).trans (t.Gv_le_normalizer_Zv i)
  have hQ : ¬ t.Zv i ≤ t.Qv w := fun hle => hn (hle.trans (t.Qv_le_Gv hfr w).1)
  refine le_antisymm (sup_le ?_ (t.Qv_le_rootOmega hfr w)) (t.rootOmega_le_sup hfr w hp hK hQ)
  intro x hx
  rw [t.mem_rootOmega_iff hfr w]
  exact ⟨hp hx, by rw [t.r6h_sq_eq_one i hx]; exact (t.Qv w).one_mem⟩

private theorem r6f_partA {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {ε : ℤ} (h₀ : t.IsFixRadius ε 2) (h₁ : t.IsFixRadius (ε + 1) 3) :
    ⁅t.Zv (ε + 1), t.Zv (ε + 4)⁆ = ⁅t.Zv (ε + 2), t.Zv (ε + 4)⁆ := by
  have h2 : t.IsFixRadius (ε + 2) 2 := by
    have := Track.IsFixRadius.shift t h₀ 1
    rwa [show ε + 2 * (1 : ℤ) = ε + 2 by ring] at this
  have h6 : t.IsFixRadius (ε + 6) 2 := by
    have := Track.IsFixRadius.shift t h₀ 3
    rwa [show ε + 2 * (3 : ℤ) = ε + 6 by ring] at this
  have h7 : t.IsFixRadius (ε + 7) 3 := by
    have := Track.IsFixRadius.shift t h₁ 3
    rwa [show ε + 1 + 2 * (3 : ℤ) = ε + 7 by ring] at this
  have hn7 : ¬ t.Zv (ε + 7) ≤ t.Gv (ε + 4 - 1) := by
    have := Track.IsFixRadius.not_le_Gv_sub t h7
    rwa [show ε + 7 - ((3 : ℕ) : ℤ) - 1 = ε + 4 - 1 by push_cast; ring] at this
  have hn6 : ¬ t.Zv (ε + 6) ≤ t.Gv (ε + 4 - 1) := by
    have := Track.IsFixRadius.not_le_Gv_sub t h6
    rwa [show ε + 6 - ((2 : ℕ) : ℤ) - 1 = ε + 4 - 1 by push_cast; ring] at this
  have hX7 := t.r6f_root_eq hfr (ε + 4) (ε + 7)
    (t.r6f_Zv_le_Gw h7 (by push_cast; omega) (by push_cast; omega)) hn7
  have hX6 := t.r6f_root_eq hfr (ε + 4) (ε + 6)
    (t.r6f_Zv_le_Gw h6 (by push_cast; omega) (by push_cast; omega)) hn6
  obtain ⟨y, -, -, -, hQy, hZy⟩ := t.exists_reflection (ε + 4)
  have hsup := congrArg (Subgroup.map (MulAut.conj y).toMonoidHom) (hX7.trans hX6.symm)
  rw [Subgroup.map_sup, Subgroup.map_sup, hZy, hZy, hQy,
    show 2 * (ε + 4) - (ε + 7) = ε + 1 by ring, show 2 * (ε + 4) - (ε + 6) = ε + 2 by ring,
    show 2 * (ε + 4) - (ε + 4) = ε + 4 by ring] at hsup
  have hN1 : t.Zv (ε + 1) ≤ normalizer (t.Qv (ε + 4) : Set G) :=
    (t.r6f_Zv_le_Gv h₁ (by push_cast; omega) (by push_cast; omega)).trans
      (t.Gv_le_normalizer_Qv _)
  have hN2 : t.Zv (ε + 2) ≤ normalizer (t.Qv (ε + 4) : Set G) :=
    (t.r6f_Zv_le_Gv h2 (by push_cast; omega) (by push_cast; omega)).trans
      (t.Gv_le_normalizer_Qv _)
  have hQC : t.Qv (ε + 4) ≤ centralizer (t.Zv (ε + 4) : Set G) :=
    Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer (ε + 4))
  calc ⁅t.Zv (ε + 1), t.Zv (ε + 4)⁆
      = ⁅t.Zv (ε + 1) ⊔ t.Qv (ε + 4), t.Zv (ε + 4)⁆ := (r6f_commutator_sup hN1 hQC).symm
    _ = ⁅t.Zv (ε + 2) ⊔ t.Qv (ε + 4), t.Zv (ε + 4)⁆ := by rw [hsup]
    _ = ⁅t.Zv (ε + 2), t.Zv (ε + 4)⁆ := r6f_commutator_sup hN2 hQC

private theorem r6f_R_le (hm1 : t.IsFixRadius (-1) 2) :
    ⁅t.Zv 1, t.Zv (-1)⁆ ≤ t.Zv 1 ∧ ⁅t.Zv 1, t.Zv (-1)⁆ ≤ t.Zv (-1) := by
  have h1 : t.IsFixRadius 1 2 := by
    have := Track.IsFixRadius.shift t hm1 1
    rwa [show (-1 : ℤ) + 2 * 1 = 1 by norm_num] at this
  have hZ1 : t.Zv 1 ≤ t.Gv (-1) := t.r6f_Zv_le_Gv h1 (by norm_num) (by norm_num)
  have hZm : t.Zv (-1) ≤ t.Gv 1 := t.r6f_Zv_le_Gv hm1 (by norm_num) (by norm_num)
  exact ⟨Subgroup.le_normalizer_iff_commutator_le_left.mp (hZm.trans (t.Gv_le_normalizer_Zv 1)),
    Subgroup.le_normalizer_iff_commutator_le_right.mp (hZ1.trans (t.Gv_le_normalizer_Zv (-1)))⟩

private theorem r6f_Y_facts {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hm1 : t.IsFixRadius (-1) 2) :
    t.Zv (-1) ≤ S ∧ t.D2 ≤ normalizer (t.Zv (-1) : Set G) ∧ ¬ t.Zv (-1) ≤ t.Qv 1 := by
  refine ⟨?_, ?_, ?_⟩
  · have hYG : t.Zv (-1) ≤ t.Gw 0 1 :=
      t.r6f_Zv_le_Gw hm1 (by norm_num) (by norm_num)
    have := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) (t.isPGroup_Zv _) hYG
    rwa [t.pCoreOf_Gw_zero_one hfr] at this
  · exact ((le_sup_right : t.D2 ≤ t.K).trans (t.K_le_Gv (-1))).trans (t.Gv_le_normalizer_Zv (-1))
  · intro hle
    have h2 : t.Qv 1 ≤ t.Gv (1 + 1) := (t.Qv_le_Gv hfr 1).2
    exact hm1.not_le_Gv (hle.trans h2)

private theorem r6f_stable {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (h : t.IsMaxArc (-1) 8) (hm1 : t.IsFixRadius (-1) 2) (h0 : t.IsFixRadius 0 3)
    (hle : ⁅t.Zv 1, t.Zv 3⁆ ≤ t.Zv 0 ⊓ t.Zv 3) (hne : ⁅t.Zv 1, t.Zv 3⁆ ≠ ⊥) :
    ⁅t.Zv 1, t.Zv (-1)⁆ = ⁅t.Zv 1, t.Zv 3⁆ := by
  have h3 : t.IsFixRadius 3 2 := by
    have := Track.IsFixRadius.shift t hm1 2
    rwa [show (-1 : ℤ) + 2 * 2 = 3 by norm_num] at this
  have h' : t.IsMaxArc (-3) 8 := by
    have := Track.IsMaxArc.shift t h (-1)
    rwa [show (-1 : ℤ) + 2 * (-1) = -3 by norm_num] at this
  set R : Subgroup G := ⁅t.Zv 1, t.Zv 3⁆ with hR
  have hR0 : R ≤ t.Zv 0 := hle.trans inf_le_left
  have hR3 : R ≤ t.Zv 3 := hle.trans inf_le_right
  have hRw : R ≤ t.Gw (-3) 5 := by
    intro x hx
    have hx0 : x ∈ t.Gw (-3) 3 :=
      t.r6f_Zv_le_Gw h0 (by norm_num) (by norm_num) (hR0 hx)
    have hx3 : x ∈ t.Gw 1 5 :=
      t.r6f_Zv_le_Gw h3 (by norm_num) (by norm_num) (hR3 hx)
    refine mem_win_iff.mpr fun i hi1 hi2 => ?_
    rcases le_total i 3 with hi | hi
    · exact mem_win_iff.mp hx0 i hi1 hi
    · exact mem_win_iff.mp hx3 i (by omega) hi2
  have hRQ : R ≤ pCoreOf 2 (t.Gw (-3) 5) :=
    t.le_pCoreOf_Gw hfr (by norm_num) ((t.isPGroup_Zv 3).to_le hR3) hRw
  set f₂ : G →* G := (MulAut.conj t.x₂).toMonoidHom with hf₂
  have hR' : R.map f₂ = ⁅t.Zv 1, t.Zv (-1)⁆ := by
    rw [hR, Subgroup.map_commutator, hf₂, t.r6h_map_Zv_x₂, t.r6h_map_Zv_x₂,
      show (2 : ℤ) - 1 = 1 by norm_num, show (2 : ℤ) - 3 = -1 by norm_num]
  have hR'Gw : R.map f₂ ≤ t.Gw (-3) 5 := by
    have h1 := Subgroup.map_mono (f := f₂) hRw
    rwa [hf₂, t.r6f_map_Gw_x₂, show (2 : ℤ) - 5 = -3 by norm_num,
      show (2 : ℤ) - -3 = 5 by norm_num] at h1
  have hR'Z : R.map f₂ ≤ t.Zv (-1) := by
    have h1 := Subgroup.map_mono (f := f₂) hR3
    rwa [hf₂, t.r6h_map_Zv_x₂, show (2 : ℤ) - 3 = -1 by norm_num] at h1
  have hR'Q : R.map f₂ ≤ pCoreOf 2 (t.Gw (-3) 5) :=
    t.le_pCoreOf_Gw hfr (by norm_num) ((t.isPGroup_Zv (-1)).to_le hR'Z) hR'Gw
  have hR'ne : R.map f₂ ≠ ⊥ := fun hb =>
    hne ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj t.x₂).injective).mp hb)
  have hKR' : t.K ≤ normalizer ((R.map f₂ : Subgroup G) : Set G) := by
    rw [hR']
    exact r6f_le_normalizer_commutator ((t.K_le_Gv 1).trans (t.Gv_le_normalizer_Zv 1))
      ((t.K_le_Gv (-1)).trans (t.Gv_le_normalizer_Zv (-1)))
  have hΩ := Track.IsMaxArc.omegaOneCenterOf_le t hfr h' hR'Q hR'ne hKR'
  have hRΩ : R ≤ omegaOneCenterOf (pCoreOf 2 (t.Gw (-3) 5)) := fun x hx =>
    Track.IsMaxArc.mem_omegaOneCenterOf t hfr h' (hRQ hx) (t.r6h_sq_eq_one 3 (hR3 hx))
  have hcard : Nat.card (R.map f₂) ≤ Nat.card R :=
    (Subgroup.card_map_of_injective (MulAut.conj t.x₂).injective).le
  have heq : R = R.map f₂ := Subgroup.eq_of_le_of_card_ge (hRΩ.trans hΩ) hcard
  exact hR'.symm.trans heq.symm

private theorem r6f_commL2_le {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hm1 : t.IsFixRadius (-1) 2)
    (hx₂ : t.x₂ ∈ normalizer ((⁅t.Zv 1, t.Zv (-1)⁆ : Subgroup G) : Set G)) :
    ⁅L2, t.Zv 1⁆ ≤ ⁅t.Zv 1, t.Zv (-1)⁆ := by
  obtain ⟨hYS, hYD, hYQ⟩ := t.r6f_Y_facts hfr hm1
  obtain ⟨hRZ1, hRZm⟩ := t.r6f_R_le hm1
  set R : Subgroup G := ⁅t.Zv 1, t.Zv (-1)⁆ with hR
  set X : Subgroup G := centralizerMod R (normalizer (t.Zv 1 : Set G)) (t.Zv 1) with hX
  have hY1 : t.Zv (-1) ≤ t.Gv 1 := t.r6f_Zv_le_Gv hm1 (by norm_num) (by norm_num)
  have hYcent : t.Zv (-1) ≤ centralizer (R : Set G) := fun y hy => by
    rw [mem_centralizer_iff]
    exact fun r hr => t.r6f_Zv_comm (-1) (hRZm hr) hy
  have hQC : t.Qv 1 ≤ centralizer (t.Zv 1 : Set G) :=
    Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 1)
  have hQR : t.Qv 1 ≤ centralizer (R : Set G) := hQC.trans (Subgroup.centralizer_le hRZ1)
  have hZX : t.Zv (-1) ≤ X := fun y hy => by
    refine mem_centralizerMod.mpr ⟨t.Gv_le_normalizer_Zv 1 (hY1 hy),
      Subgroup.centralizer_le_normalizer _ (hYcent hy), fun u hu => ?_⟩
    have := Subgroup.commutator_mem_commutator hy hu
    rwa [Subgroup.commutator_comm (t.Zv (-1)) (t.Zv 1)] at this
  have hQX : t.Qv 1 ≤ X := fun y hy => by
    refine mem_centralizerMod.mpr ⟨t.Gv_le_normalizer_Zv 1 (t.Qv_le_Gv_self 1 hy),
      Subgroup.centralizer_le_normalizer _ (hQR hy), fun u hu => ?_⟩
    have hc : u * y = y * u := mem_centralizer_iff.mp (hQC hy) u hu
    have : y * u * y⁻¹ * u⁻¹ = 1 := by rw [← hc]; group
    rw [this]
    exact R.one_mem
  have hx₂Z : t.x₂ ∈ normalizer (t.Zv 1 : Set G) :=
    t.Gv_le_normalizer_Zv 1 (by rw [t.Gv_one]; exact t.track.x₂_mem)
  have hzp : Subgroup.zpowers t.x₂ ≤ normalizer (X : Set G) :=
    le_normalizer_centralizerMod (Subgroup.zpowers_le.mpr hx₂)
      (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hx₂Z)) (Subgroup.zpowers_le.mpr hx₂Z)
  have hS : S ≤ t.Zv (-1) ⊔ t.Qv 1 := t.S_le_sup_Qv_one_of_torus hfr hYS hYD hYQ
  have hT : S ⊓ L2 ≤ X ⊔ t.Qv 1 := inf_le_left.trans (hS.trans (sup_le_sup hZX le_rfl))
  have hL := t.L2_le_sup_Qv_one_of_sylow hfr hT (hzp (Subgroup.mem_zpowers t.x₂))
  rw [sup_eq_left.mpr hQX] at hL
  exact Subgroup.commutator_le.mpr fun l hl u hu => (mem_centralizerMod.mp (hL hl)).2.2 u hu

private theorem r6f_L2_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hm1 : t.IsFixRadius (-1) 2)
    (hx₂ : t.x₂ ∈ normalizer ((⁅t.Zv 1, t.Zv (-1)⁆ : Subgroup G) : Set G)) :
    L2 ≤ centralizer (t.Zv 1 : Set G) := by
  obtain ⟨hYS, hYD, hYQ⟩ := t.r6f_Y_facts hfr hm1
  obtain ⟨hRZ1, hRZm⟩ := t.r6f_R_le hm1
  have hYcent : t.Zv (-1) ≤ centralizer ((⁅t.Zv 1, t.Zv (-1)⁆ : Subgroup G) : Set G) :=
    fun y hy => by
      rw [mem_centralizer_iff]
      exact fun r hr => t.r6f_Zv_comm (-1) (hRZm hr) hy
  have hL2R : L2 ≤ centralizer ((⁅t.Zv 1, t.Zv (-1)⁆ : Subgroup G) : Set G) :=
    t.L2_le_centralizer_of_l2 hfr hYS hYD hYQ hRZ1 hYcent hx₂
  have h1 : ⁅⁅L2, t.Zv 1⁆, L2⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    ((t.r6f_commL2_le hfr hm1 hx₂).trans (Subgroup.le_centralizer_iff.mp hL2R))
  have h2 : ⁅⁅t.Zv 1, L2⁆, L2⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (t.Zv 1) L2]
    exact h1
  have h3 : ⁅L2, L2⁆ ≤ centralizer (t.Zv 1 : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2)
  have hQ : pCoreOf 2 L2 ≤ centralizer (t.Zv 1 : Set G) :=
    (t.r6f_pCoreOf_le_Qv_one hfr.hF.1).trans
      (Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 1))
  exact (CFSG.Quasithin.F112R.le_commutator_sup_pCoreOf_of_isL2Quot hfr.hf hfr.hL2).trans
    (sup_le h3 hQ)

private theorem r6f_comm_eq_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h3 : t.IsFixRadius 3 2)
    (hL : L2 ≤ centralizer (t.Zv 1 : Set G)) : ⁅t.Zv 1, t.Zv 3⁆ = ⊥ := by
  have hZ3 : t.Zv 3 ≤ t.Gv 1 := t.r6f_Zv_le_Gv h3 (by norm_num) (by norm_num)
  have hQ2 : Q2 L1 L2 S ≤ centralizer (t.Zv 1 : Set G) := by
    rw [← t.Qv_one]
    exact Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 1)
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  have hxP : x ∈ P2 L1 L2 S := by
    rw [← t.Gv_one]
    exact hZ3 hx
  exact (sup_le hL hQ2) (t.mem_L2_sup_Q2_of_pow_eq_one hfr hxP (j := 1)
    (by simpa using t.r6h_sq_eq_one 3 hx))

private theorem r6f_base {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (h : t.IsMaxArc (-1) 8) (hm1 : t.IsFixRadius (-1) 2) (h0 : t.IsFixRadius 0 3)
    (hle : ⁅t.Zv 0, t.Zv 3⁆ ≤ t.Zv 0 ⊓ t.Zv 3) : ⁅t.Zv 0, t.Zv 3⁆ = ⊥ := by
  have h3 : t.IsFixRadius 3 2 := by
    have := Track.IsFixRadius.shift t hm1 2
    rwa [show (-1 : ℤ) + 2 * 2 = 3 by norm_num] at this
  have hA := t.r6f_partA hfr hm1 h0
  rw [show (-1 : ℤ) + 1 = 0 by norm_num, show (-1 : ℤ) + 4 = 3 by norm_num,
    show (-1 : ℤ) + 2 = 1 by norm_num] at hA
  rw [hA] at hle ⊢
  by_contra hne
  have hst := t.r6f_stable hfr h hm1 h0 hle hne
  have hx₂ : t.x₂ ∈ normalizer ((⁅t.Zv 1, t.Zv (-1)⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (⁅t.Zv 1, t.Zv (-1)⁆ : Subgroup G).map (MulAut.conj t.x₂).toMonoidHom = _
    rw [Subgroup.map_commutator, t.r6h_map_Zv_x₂, t.r6h_map_Zv_x₂,
      show (2 : ℤ) - 1 = 1 by norm_num, show (2 : ℤ) - -1 = 3 by norm_num]
    exact hst.symm
  exact hne (t.r6f_comm_eq_bot hfr h3 (t.r6f_L2_le_centralizer hfr hm1 hx₂))

private theorem r6f_map_commutator (k u v : ℤ) :
    (⁅t.Zv u, t.Zv v⁆ : Subgroup G).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
      ⁅t.Zv (u + 2 * k), t.Zv (v + 2 * k)⁆ := by
  rw [Subgroup.map_commutator, t.r6h_map_Zv_tau, t.r6h_map_Zv_tau]

private theorem r6f_map_inf (k u v : ℤ) :
    (t.Zv u ⊓ t.Zv v).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
      t.Zv (u + 2 * k) ⊓ t.Zv (v + 2 * k) := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective, t.r6h_map_Zv_tau, t.r6h_map_Zv_tau]

theorem IsMaxArc.commutator_eq_bot_of_eq_eight {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    {ε : ℤ} (h : t.IsMaxArc ε 8) (h₀ : t.IsFixRadius ε 2) (h₁ : t.IsFixRadius (ε + 1) 3)
    (hle : ⁅t.Zv (ε + 1), t.Zv (ε + 4)⁆ ≤ t.Zv (ε + 1) ⊓ t.Zv (ε + 4)) :
    ⁅t.Zv (ε + 1), t.Zv (ε + 4)⁆ = ⊥ := by
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' ε
  · have h2 : t.IsFixRadius (ε + 2) 2 := by
      have := Track.IsFixRadius.shift t h₀ 1
      rwa [show ε + 2 * (1 : ℤ) = ε + 2 by ring] at this
    have hB := Track.IsFixRadius.commutator_eq_bot_of_even t hfr h2
      ⟨m + 1, by omega⟩ (⟨1, rfl⟩ : Even 2)
    rw [show ε + 2 + ((2 : ℕ) : ℤ) = ε + 4 by push_cast; ring] at hB
    rw [t.r6f_partA hfr h₀ h₁]
    exact hB
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, ε + 2 * k = -1 := ⟨-(m + 1), by omega⟩
    have hmax := Track.IsMaxArc.shift t h k
    have h₀' := Track.IsFixRadius.shift t h₀ k
    have h₁' := Track.IsFixRadius.shift t h₁ k
    rw [hk] at hmax h₀'
    rw [show ε + 1 + 2 * k = 0 by omega] at h₁'
    have hle' : ⁅t.Zv 0, t.Zv 3⁆ ≤ t.Zv 0 ⊓ t.Zv 3 := by
      have := Subgroup.map_mono (f := (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom) hle
      rwa [t.r6f_map_commutator, t.r6f_map_inf, show ε + 1 + 2 * k = 0 by omega,
        show ε + 4 + 2 * k = 3 by omega] at this
    have hz : (⁅t.Zv (ε + 1), t.Zv (ε + 4)⁆ : Subgroup G).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = ⊥ := by
      rw [t.r6f_map_commutator, show ε + 1 + 2 * k = 0 by omega,
        show ε + 4 + 2 * k = 3 by omega]
      exact t.r6f_base hfr hmax h₀' h₁' hle'
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).mp hz

end Track

end CFSG.Quasithin.Stroth.Rq
