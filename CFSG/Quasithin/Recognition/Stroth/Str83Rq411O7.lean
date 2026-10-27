module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqArcRoot
public import CFSG.Quasithin.Recognition.Stroth.Str83RqT6
public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackVertex
import CFSG.Quasithin.Recognition.Stroth.Str83G4Reduction
import CFSG.Quasithin.Recognition.Stroth.Str83Rq410a
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4SzSub
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4SzSylow
import CFSG.Quasithin.Recognition.Stroth.Str83RqTools

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem r65a_sq_eq_one (i : ℤ) {e : G} (he : e ∈ t.Zv i) : e ^ 2 = 1 := by
  rw [t.Zv_eq i] at he
  exact A4.sq_eq_one_of_mem_omegaOneCenterOf he

private theorem r65a_map_Zv_x₁ (i : ℤ) :
    (t.Zv i).map (MulAut.conj t.x₁).toMonoidHom = t.Zv (-i) :=
  t.track.map_qv_x₁
    ((le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _))
    ((le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)) i

private theorem r65a_Zv_le_S {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {w : ℤ} (h : t.Zv w ≤ t.Gw 0 1) : t.Zv w ≤ S := by
  have h2 := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) (t.isPGroup_Zv w) h
  rwa [t.pCoreOf_Gw_zero_one hfr] at h2

private theorem r65a_Qv_zero_le_S {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 0 ≤ S := by
  have h1 : t.Qv 0 ≤ t.Gv 1 := by simpa using (t.Qv_le_Gv hfr 0).2
  have hw : t.Qv 0 ≤ t.Gw 0 1 := fun y hy => mem_win_iff.mpr fun i hi0 hi1 => by
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact t.Qv_le_Gv_self 0 hy
    · exact h1 hy
  have h2 := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) (t.isPGroup_Qv 0) hw
  rwa [t.pCoreOf_Gw_zero_one hfr] at h2

private theorem r65a_radius_neg_one (h₁ : t.IsFixRadius 1 2) : t.IsFixRadius (-1) 2 := by
  simpa using Track.IsFixRadius.shift t h₁ (-1)

private theorem r65a_Zv_neg_one_le (h₁ : t.IsFixRadius 1 2) : t.Zv (-1) ≤ t.Gw (-3) 1 := by
  simpa using (t.r65a_radius_neg_one h₁).le_Gw

private theorem r65a_not_Zv_neg_one_le_Gv_two (h₁ : t.IsFixRadius 1 2) :
    ¬ t.Zv (-1) ≤ t.Gv 2 := by
  simpa using (t.r65a_radius_neg_one h₁).not_le_Gv

private theorem r65a_S_le_sup {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (h₁ : t.IsFixRadius 1 2) : S ≤ t.Zv (-1) ⊔ t.Qv 1 := by
  have hYS : t.Zv (-1) ≤ S :=
    t.r65a_Zv_le_S hfr ((t.r65a_Zv_neg_one_le h₁).trans (win_mono (by norm_num) le_rfl))
  have hYD : t.D2 ≤ normalizer (t.Zv (-1) : Set G) :=
    (le_sup_right : t.D2 ≤ t.K).trans ((t.K_le_Gv (-1)).trans (t.Gv_le_normalizer_Zv (-1)))
  have hYQ : ¬ t.Zv (-1) ≤ t.Qv 1 := fun hle =>
    t.r65a_not_Zv_neg_one_le_Gv_two h₁ (hle.trans (by simpa using (t.Qv_le_Gv hfr 1).2))
  exact t.S_le_sup_Qv_one_of_torus hfr hYS hYD hYQ

private theorem r65a_S_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₁ : t.IsFixRadius 1 2)
    (hle : ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Zv (-1) ⊓ t.Zv 1) :
    S ≤ centralizer ((⁅t.Zv (-1), t.Zv 1⁆ : Subgroup G) : Set G) := by
  refine (t.r65a_S_le_sup hfr h₁).trans (sup_le ?_ ?_)
  · intro y hy
    rw [mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_iff.mp (t.Zv_le_centralizer (-1) hy) x
      (t.Zv_le_Qv (-1) (mem_inf.mp (hle hx)).1)
  · intro y hy
    rw [mem_centralizer_iff]
    intro x hx
    exact (mem_centralizer_iff.mp (t.Zv_le_centralizer 1 (mem_inf.mp (hle hx)).2) y hy).symm

private theorem r65a_R_le_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₁ : t.IsFixRadius 1 2)
    (hle : ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Zv (-1) ⊓ t.Zv 1) :
    ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Qv 0 := by
  have hR : ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Zv (-1) := hle.trans inf_le_left
  exact t.le_Qv_of_le_Gw hfr (u := -3) (w := 1) (j := 0) (by norm_num) (by norm_num)
    ((t.isPGroup_Zv (-1)).to_le hR) (hR.trans (t.r65a_Zv_neg_one_le h₁))

private theorem r65a_R_le_Zv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₁ : t.IsFixRadius 1 2)
    (hle : ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Zv (-1) ⊓ t.Zv 1) :
    ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Zv 0 := by
  have hQ := t.r65a_R_le_Qv_zero hfr h₁ hle
  have hC : ⁅t.Zv (-1), t.Zv 1⁆ ≤ centralizer (t.Qv 0 : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    have h := mem_centralizer_iff.mp (t.r65a_S_le_centralizer hfr h₁ hle
      (t.r65a_Qv_zero_le_S hfr hy)) x hx
    exact h.symm
  intro x hx
  rw [t.Zv_eq 0]
  exact Subgroup.subset_closure ⟨⟨hQ hx, hC hx⟩, t.r65a_sq_eq_one (-1) (mem_inf.mp (hle hx)).1⟩

private theorem r65a_map_R :
    (⁅t.Zv (-1), t.Zv 1⁆ : Subgroup G).map (MulAut.conj t.x₁).toMonoidHom =
      ⁅t.Zv (-1), t.Zv 1⁆ := by
  rw [Subgroup.map_commutator, t.r65a_map_Zv_x₁, t.r65a_map_Zv_x₁, neg_neg,
    Subgroup.commutator_comm]

private theorem r65a_map_S_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₁ : t.IsFixRadius 1 2)
    (hle : ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Zv (-1) ⊓ t.Zv 1) :
    S.map (MulAut.conj t.x₁).toMonoidHom ≤
      centralizer ((⁅t.Zv (-1), t.Zv 1⁆ : Subgroup G) : Set G) := by
  have h : ⁅S, ⁅t.Zv (-1), t.Zv 1⁆⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (t.r65a_S_le_centralizer hfr h₁ hle)
  have h2 := congrArg (Subgroup.map (MulAut.conj t.x₁).toMonoidHom) h
  rw [Subgroup.map_commutator, Subgroup.map_bot, t.r65a_map_R] at h2
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2

private theorem r65a_D1_le_normalizer_S {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.D1 ≤ normalizer (S : Set G) :=
  ((le_sup_left : t.D1 ≤ t.K).trans t.hHall.1).trans hfr.hN

private theorem r65a_not_S_le_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : ¬ S ≤ t.Qv 0 := by
  intro hSle
  have hQS : (t.Qv 0).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hSle
  have h9 := (t.relIndex_Qv_pCoreOf hfr 0).2
  rw [zero_add, t.pCoreOf_Gw_zero_one hfr, if_pos (by decide), hQS] at h9
  have h4 : 4 ≤ (2 ^ (2 * a + 1)) ^ 2 :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * (2 * a + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (2 ^ (2 * a + 1)) ^ 2 := by rw [← pow_mul, mul_comm]
  omega

theorem commutator_le_Zv_zero_and_Lv_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₁ : t.IsFixRadius 1 2)
    (hle : ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Zv (-1) ⊓ t.Zv 1) :
    ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Zv 0 ∧
      t.Lv 0 ≤ centralizer ((⁅t.Zv (-1), t.Zv 1⁆ : Subgroup G) : Set G) := by
  have hZ0 := t.r65a_R_le_Zv_zero hfr h₁ hle
  have hSC := t.r65a_S_le_centralizer hfr h₁ hle
  refine ⟨hZ0, ?_⟩
  rw [t.Lv_zero]
  refine sup_le ?_ ((?_ : Q1 L1 L2 S ≤ S).trans hSC)
  · exact t.L1_le_centralizer_of_sz hfr (Y := S) le_rfl (t.r65a_D1_le_normalizer_S hfr)
      (t.r65a_not_S_le_Qv_zero hfr) hZ0 hSC (t.r65a_map_S_le_centralizer hfr h₁ hle)
  · rw [← t.Qv_zero]
    exact t.r65a_Qv_zero_le_S hfr

private theorem r65b_Zv_one_le_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₁ : t.IsFixRadius 1 2) : t.Zv 1 ≤ t.Qv 0 := by
  have hw : t.Zv 1 ≤ t.Gw (-1) 3 := by simpa using h₁.le_Gw
  exact t.le_Qv_of_le_Gw hfr (by norm_num) (by norm_num) (t.isPGroup_Zv 1) hw

private theorem r65b_Zv_zero_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₁ : t.IsFixRadius 1 2) :
    t.Zv 0 ≤ centralizer (t.Zv 1 : Set G) := by
  have h : t.Zv 1 ≤ centralizer (t.Zv 0 : Set G) :=
    (r65b_Zv_one_le_Qv_zero t hfr h₁).trans
      (Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 0))
  exact Subgroup.le_centralizer_iff.mp h

private theorem r65b_Zv_zero_le_S {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b : ℕ} (h₀ : t.IsFixRadius 0 b) : t.Zv 0 ≤ S := by
  have hb := IsFixRadius.one_le t hfr h₀
  have hw : t.Zv 0 ≤ t.Gw 0 1 := fun z hz =>
    mem_win_iff.mpr fun i hi1 hi2 =>
      mem_win_iff.mp (h₀.le_Gw hz) i (by omega) (by omega)
  have h := t.le_pCoreOf_Gw hfr (show (0 : ℤ) < 1 by norm_num) (t.isPGroup_Zv 0) hw
  rwa [t.pCoreOf_Gw_zero_one hfr] at h

private theorem r65b_D2_le_normalizer_Zv_zero :
    t.D2 ≤ normalizer (t.Zv 0 : Set G) :=
  (le_sup_right : t.D2 ≤ t.K).trans ((t.K_le_Gv 0).trans (t.Gv_le_normalizer_Zv 0))

private theorem r65b_x₂_mem_normalizer_Zv_one :
    t.x₂ ∈ normalizer (t.Zv 1 : Set G) := by
  have hx : t.x₂ ∈ t.Gv 1 := by
    rw [t.Gv_one]
    exact t.track.x₂_mem
  exact t.Gv_le_normalizer_Zv 1 hx

private theorem r65b_commutator_eq_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₁ : t.IsFixRadius 1 2)
    (hL : L2 ≤ centralizer (t.Zv 1 : Set G)) : ⁅t.Zv (-1), t.Zv 1⁆ = ⊥ := by
  have h₁' : t.IsFixRadius (-1) 2 := by simpa using Track.IsFixRadius.shift t h₁ (-1)
  have hXG : t.Zv (-1) ≤ t.Gv 1 := h₁'.le_Gw.trans (win_le_qv (by omega) (by omega))
  have hQ : Q2 L1 L2 S ≤ centralizer (t.Zv 1 : Set G) := by
    rw [← t.Qv_one]
    exact Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 1)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  obtain ⟨j, hj⟩ := t.isPGroup_Zv (-1) ⟨x, hx⟩
  have hxj : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hxP : x ∈ P2 L1 L2 S := by
    rw [← t.Gv_one]
    exact hXG hx
  exact sup_le hL hQ (t.mem_L2_sup_Q2_of_pow_eq_one hfr hxP hxj)

theorem Zv_zero_le_Qv_one_of_commutator_ne_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b : ℕ} (h₀ : t.IsFixRadius 0 b) (h₁ : t.IsFixRadius 1 2)
    (hne : ⁅t.Zv (-1), t.Zv 1⁆ ≠ ⊥) : t.Zv 0 ≤ t.Qv 1 := by
  by_contra hY
  have hL : L2 ≤ centralizer (t.Zv 1 : Set G) :=
    t.L2_le_centralizer_of_l2 hfr (Y := t.Zv 0) (C := t.Zv 1) (r65b_Zv_zero_le_S t hfr h₀)
      (r65b_D2_le_normalizer_Zv_zero t) hY le_rfl (r65b_Zv_zero_le_centralizer t hfr h₁)
      (r65b_x₂_mem_normalizer_Zv_one t)
  exact hne (r65b_commutator_eq_bot t hfr h₁ hL)

private theorem r65c_Zv_one_le (h₁ : t.IsFixRadius 1 2) : t.Zv 1 ≤ t.Gw (-1) 3 := by
  simpa using h₁.le_Gw

private theorem r65c_inf_le_Gw : t.Gw (-3) 1 ⊓ t.Gw (-1) 3 ≤ t.Gw (-3) 3 := by
  intro y hy
  refine mem_win_iff.mpr fun i h1 h2 => ?_
  by_cases hi : i ≤ 1
  · exact mem_win_iff.mp hy.1 i h1 hi
  · exact mem_win_iff.mp hy.2 i (by omega) h2

private theorem r65c_commutator_le_Gw (h₁ : t.IsFixRadius 1 2)
    (hle : ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Zv (-1) ⊓ t.Zv 1) :
    ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Gw (-3) 3 :=
  hle.trans ((inf_le_inf (t.r65a_Zv_neg_one_le h₁) (t.r65c_Zv_one_le h₁)).trans
    t.r65c_inf_le_Gw)

private theorem r65c_mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

private theorem r65c_K_le_normalizer_commutator :
    t.K ≤ normalizer ((⁅t.Zv (-1), t.Zv 1⁆ : Subgroup G) : Set G) := fun _ hg =>
  r65c_mem_normalizer_commutator (t.Gv_le_normalizer_Zv (-1) (t.K_le_Gv (-1) hg))
    (t.Gv_le_normalizer_Zv 1 (t.K_le_Gv 1 hg))

theorem pCoreOf_Gw_eq_commutator {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} (h : t.IsMaxArc ε 6) (h₁ : t.IsFixRadius 1 2)
    (hle : ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Zv (-1) ⊓ t.Zv 1) (hne : ⁅t.Zv (-1), t.Zv 1⁆ ≠ ⊥) :
    pCoreOf 2 (t.Gw (-3) 3) = ⁅t.Zv (-1), t.Zv 1⁆ ∧ Nat.card ↥⁅t.Zv (-1), t.Zv 1⁆ = 2 ^ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h36 : (-3 : ℤ) + ((6 : ℕ) : ℤ) = 3 := by norm_num
  have hRp : IsPGroup 2 (⁅t.Zv (-1), t.Zv 1⁆ : Subgroup G) :=
    (t.isPGroup_Zv (-1)).to_le (hle.trans inf_le_left)
  have hRP : ⁅t.Zv (-1), t.Zv 1⁆ ≤ pCoreOf 2 (t.Gw (-3) 3) :=
    t.le_pCoreOf_Gw hfr (by norm_num) hRp (t.r65c_commutator_le_Gw h₁ hle)
  have hγ : t.IsMaxArc (-3) 6 := by
    refine ⟨?_, h.pCoreOf_eq_bot⟩
    rw [h36]
    intro hbot
    exact hne (le_bot_iff.mp (hbot ▸ hRP))
  have hRP' : ⁅t.Zv (-1), t.Zv 1⁆ ≤ pCoreOf 2 (t.Gw (-3) (-3 + ((6 : ℕ) : ℤ))) := by
    rw [h36]
    exact hRP
  have hΩR : omegaOneCenterOf (pCoreOf 2 (t.Gw (-3) (-3 + ((6 : ℕ) : ℤ)))) ≤
      ⁅t.Zv (-1), t.Zv 1⁆ :=
    IsMaxArc.omegaOneCenterOf_le t hfr hγ hRP' hne t.r65c_K_le_normalizer_commutator
  have hΩcard := IsMaxArc.card_omegaOneCenterOf t hfr hγ (e := -3) (Or.inl rfl)
  have hPcard := IsMaxArc.card_pCoreOf_le t hfr hγ (e := -3) (Or.inl rfl)
  have hodd : ¬ Even (-3 : ℤ) := by decide
  rw [if_neg hodd] at hΩcard hPcard
  rw [h36] at hΩR hΩcard hPcard
  have h1 := Subgroup.card_le_of_le hΩR
  have h2 := Subgroup.card_le_of_le hRP
  have hRcard : Nat.card ↥(⁅t.Zv (-1), t.Zv 1⁆ : Subgroup G) = 2 ^ f := by omega
  refine ⟨(Subgroup.eq_of_le_of_card_ge hRP (by omega)).symm, hRcard⟩

private theorem r65d_relIndex_ne_zero (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite (G := ↥K) (H := H.subgroupOf K)

private theorem r65d_map_Zv_x₂ (i : ℤ) :
    (t.Zv i).map (MulAut.conj t.x₂).toMonoidHom = t.Zv (2 - i) :=
  t.track.map_qv_x₂
    ((le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _))
    ((le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)) i

private theorem r65d_map_Qv_x₂ (i : ℤ) :
    (t.Qv i).map (MulAut.conj t.x₂).toMonoidHom = t.Qv (2 - i) :=
  t.track.map_qv_x₂ (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _) i

private theorem r65d_map_Gw_x₂ (a b : ℤ) :
    (t.Gw a b).map (MulAut.conj t.x₂).toMonoidHom = t.Gw (2 - b) (2 - a) :=
  t.track.map_win_x₂ Subgroup.le_normalizer Subgroup.le_normalizer a b

private theorem r65d_relIndex_Qv_two :
    (t.Qv 2).relIndex (t.Zv 0) = (t.Qv 0).relIndex (t.Zv 2) := by
  rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj t.x₂).toMonoidHom) (t.Qv 2)
    (t.Zv 0) (MulAut.conj _).injective, t.r65d_map_Qv_x₂, t.r65d_map_Zv_x₂]
  norm_num

private theorem r65d_Zv_le_rootOmega {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {i v : ℤ} (h : t.Zv i ≤ t.Gw v (v + 1)) :
    t.Zv i ≤ t.rootOmega v := by
  intro x hx
  rw [t.mem_rootOmega_iff hfr v]
  refine ⟨t.le_pCoreOf_Gw hfr (u := v) (w := v + 1) (by omega) (t.isPGroup_Zv i) h hx, ?_⟩
  rw [t.r65a_sq_eq_one i hx]
  exact one_mem _

private theorem r65d_relIndex_Zv_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {i v : ℤ} (hv : Even v) (h : t.Zv i ≤ t.Gw v (v + 1)) :
    (t.Qv v).relIndex (t.Zv i) ≤ 2 ^ (2 * a + 1) := by
  have h1 := Subgroup.relIndex_le_of_le_right (H := t.Qv v) (t.r65d_Zv_le_rootOmega hfr h)
    (r65d_relIndex_ne_zero _ _)
  rwa [t.relIndex_rootOmega hfr v, if_pos hv] at h1

private theorem r65d_card_Zv_zero_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZ : t.Zv 0 ≤ t.Gw (-2) 2)
    (hP : Nat.card ↥(pCoreOf 2 (t.Gw (-3) 3)) ≤ 2 ^ f) :
    Nat.card ↥(t.Zv 0) ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) * 2 ^ f := by
  have ha : (t.Qv 2).relIndex (t.Zv 0) ≤ 2 ^ (2 * a + 1) := by
    rw [t.r65d_relIndex_Qv_two]
    refine t.r65d_relIndex_Zv_le hfr (v := 0) (by decide) ?_
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hZ
    rw [t.r65d_map_Zv_x₂, t.r65d_map_Gw_x₂] at h
    refine (by simpa using h : t.Zv 2 ≤ t.Gw 0 4).trans (win_mono le_rfl (by norm_num))
  have hb : (t.Qv (-2)).relIndex (t.Zv 0) ≤ 2 ^ (2 * a + 1) :=
    t.r65d_relIndex_Zv_le hfr (v := -2) (by decide) (hZ.trans (win_mono le_rfl (by norm_num)))
  have hCle : t.Zv 0 ⊓ (t.Qv 2 ⊓ t.Qv (-2)) ≤ t.Zv 0 := inf_le_left
  have hCw : t.Zv 0 ⊓ (t.Qv 2 ⊓ t.Qv (-2)) ≤ t.Gw (-3) 3 := by
    intro y hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i = -3 ∨ (-2 ≤ i ∧ i ≤ 2) ∨ i = 3 by omega) with rfl | ⟨h3, h4⟩ | rfl
    · have := (t.Qv_le_Gv hfr (-2)).1 hy.2.2
      simpa using this
    · exact mem_win_iff.mp (hZ hy.1) i h3 h4
    · have := (t.Qv_le_Gv hfr 2).2 hy.2.1
      simpa using this
  have hCP : Nat.card ↥(t.Zv 0 ⊓ (t.Qv 2 ⊓ t.Qv (-2))) ≤ 2 ^ f :=
    (Subgroup.card_le_of_le (t.le_pCoreOf_Gw hfr (by norm_num)
      ((t.isPGroup_Zv 0).to_le hCle) hCw)).trans hP
  have hmul : (t.Zv 0 ⊓ (t.Qv 2 ⊓ t.Qv (-2))).relIndex (t.Zv 0) *
      Nat.card ↥(t.Zv 0 ⊓ (t.Qv 2 ⊓ t.Qv (-2))) = Nat.card ↥(t.Zv 0) := by
    have := Subgroup.relIndex_mul_card (H := t.Zv 0 ⊓ (t.Qv 2 ⊓ t.Qv (-2))) (K := t.Zv 0)
    rwa [inf_eq_left.mpr hCle] at this
  have hrel : (t.Zv 0 ⊓ (t.Qv 2 ⊓ t.Qv (-2))).relIndex (t.Zv 0) ≤
      2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) :=
    calc (t.Zv 0 ⊓ (t.Qv 2 ⊓ t.Qv (-2))).relIndex (t.Zv 0)
        = (t.Qv 2 ⊓ t.Qv (-2)).relIndex (t.Zv 0) := Subgroup.inf_relIndex_left _ _
      _ ≤ (t.Qv 2).relIndex (t.Zv 0) * (t.Qv (-2)).relIndex (t.Zv 0) := Subgroup.relIndex_inf_le
      _ ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := Nat.mul_le_mul ha hb
  rw [← hmul]
  exact Nat.mul_le_mul hrel hCP

private theorem r65d_L1_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hcard : Nat.card ↥(t.Zv 0) ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) * 2 ^ f)
    {R : Subgroup G} (hRZ : R ≤ t.Zv 0) (hRL : L1 ≤ centralizer (R : Set G))
    (hRcard : Nat.card ↥R = 2 ^ f) : L1 ≤ centralizer (t.Zv 0 : Set G) := by
  refine t.L1_le_centralizer_Zv_zero_of_relIndex_lt hfr ?_
  have hR : R ≤ t.Zv 0 ⊓ centralizer (L1 : Set G) :=
    le_inf hRZ (Subgroup.le_centralizer_iff.mp hRL)
  have h1 : (t.Zv 0 ⊓ centralizer (L1 : Set G)).relIndex (t.Zv 0) ≤ R.relIndex (t.Zv 0) :=
    Subgroup.relIndex_le_of_le_left hR (r65d_relIndex_ne_zero _ _)
  have h2 : R.relIndex (t.Zv 0) * 2 ^ f = Nat.card ↥(t.Zv 0) := by
    have := Subgroup.relIndex_mul_card (H := R) (K := t.Zv 0)
    rwa [inf_eq_left.mpr hRZ, hRcard] at this
  have h3 : R.relIndex (t.Zv 0) ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := by
    have : R.relIndex (t.Zv 0) * 2 ^ f ≤ (2 ^ (2 * a + 1) * 2 ^ (2 * a + 1)) * 2 ^ f := by
      rw [h2]
      exact hcard
    exact Nat.le_of_mul_le_mul_right this (by positivity)
  refine lt_of_le_of_lt (h1.trans h3) ?_
  have hq : 2 ≤ 2 ^ (2 * a + 1) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : 2 ^ (4 * (2 * a + 1)) = (2 ^ (2 * a + 1)) ^ 4 := by
    rw [← pow_mul, mul_comm]
  rw [e]
  nlinarith [Nat.mul_le_mul hq hq, Nat.pos_of_ne_zero (show 2 ^ (2 * a + 1) ≠ 0 by positivity)]

private theorem r65d_Lv_zero_le_centralizer (hL1 : L1 ≤ centralizer (t.Zv 0 : Set G)) :
    t.Lv 0 ≤ centralizer (t.Zv 0 : Set G) := by
  rw [t.Lv_zero]
  refine sup_le hL1 ?_
  rw [← t.Qv_zero]
  exact Subgroup.le_centralizer_iff.mp (t.Zv_le_centralizer 0)

private theorem r65d_Zv_zero_le_Zv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hL : t.Lv 0 ≤ centralizer (t.Zv 0 : Set G))
    (h2 : t.Zv 0 ≤ t.Qv 1) : t.Zv 0 ≤ t.Zv 1 := by
  have hQ1G : t.Qv 1 ≤ t.Gv 0 := by simpa using (t.Qv_le_Gv hfr 1).1
  have hQL : t.Qv 1 ≤ t.Lv 0 := t.le_Lv hfr (t.isPGroup_Qv 1) hQ1G
  intro z hz
  have hC : z ∈ centralizer (t.Qv 1 : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact (mem_centralizer_iff.mp (hL (hQL hy)) z hz).symm
  rw [t.Zv_eq 1]
  exact Subgroup.subset_closure ⟨⟨h2 hz, hC⟩, t.r65a_sq_eq_one 0 hz⟩

private theorem r65d_Zv_zero_le_Zv_neg_one (h : t.Zv 0 ≤ t.Zv 1) : t.Zv 0 ≤ t.Zv (-1) := by
  have h' := Subgroup.map_mono (f := (MulAut.conj t.x₁).toMonoidHom) h
  rw [t.r65a_map_Zv_x₁, t.r65a_map_Zv_x₁, neg_zero] at h'
  exact h'

private theorem r65d_core {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h : t.IsMaxArc 0 6) {b : ℕ} (h₀ : t.IsFixRadius 0 b)
    (h₁ : t.IsFixRadius 1 2)
    (h1 : ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Zv 0 ∧
      t.Lv 0 ≤ centralizer ((⁅t.Zv (-1), t.Zv 1⁆ : Subgroup G) : Set G))
    (h2 : t.Zv 0 ≤ t.Qv 1)
    (h3 : pCoreOf 2 (t.Gw (-3) 3) = ⁅t.Zv (-1), t.Zv 1⁆ ∧
      Nat.card ↥⁅t.Zv (-1), t.Zv 1⁆ = 2 ^ f) :
    t.Zv 0 = ⁅t.Zv (-1), t.Zv 1⁆ ∧ t.Lv 0 ≤ centralizer (t.Zv 0 : Set G) ∧ b = 3 := by
  have hb1 : 1 ≤ b := Track.IsFixRadius.one_le t hfr h₀
  have hb2 : 2 ≤ b := by
    by_contra hlt
    obtain rfl : b = 1 := by omega
    apply h₀.not_le_Gv
    have h4 : t.Zv 0 ≤ t.Gv 2 := h2.trans (t.Qv_le_Gv hfr 1).2
    simpa using h4
  have hb6 : 2 * b ≤ 6 := Track.IsFixRadius.two_mul_le t hfr h h₀
  have hZ2 : t.Zv 0 ≤ t.Gw (-2) 2 := h₀.le_Gw.trans (win_mono (by omega) (by omega))
  have hP : Nat.card ↥(pCoreOf 2 (t.Gw (-3) 3)) ≤ 2 ^ f := by
    rw [h3.1]
    exact h3.2.le
  have hcard := t.r65d_card_Zv_zero_le hfr hZ2 hP
  have hL1Lv : L1 ≤ t.Lv 0 := by
    rw [t.Lv_zero]
    exact le_sup_left
  have hL1 : L1 ≤ centralizer (t.Zv 0 : Set G) :=
    t.r65d_L1_le_centralizer hfr hcard h1.1 (hL1Lv.trans h1.2) h3.2
  have hL := t.r65d_Lv_zero_le_centralizer hL1
  have hZ1 := t.r65d_Zv_zero_le_Zv_one hfr hL h2
  have hZ1' := t.r65d_Zv_zero_le_Zv_neg_one hZ1
  have hZw : t.Zv 0 ≤ t.Gw (-3) 3 :=
    (le_inf (hZ1'.trans (t.r65a_Zv_neg_one_le h₁)) (hZ1.trans (t.r65c_Zv_one_le h₁))).trans
      t.r65c_inf_le_Gw
  have hZR : t.Zv 0 ≤ ⁅t.Zv (-1), t.Zv 1⁆ := by
    rw [← h3.1]
    exact t.le_pCoreOf_Gw hfr (by norm_num) (t.isPGroup_Zv 0) hZw
  refine ⟨le_antisymm hZR h1.1, hL, ?_⟩
  by_contra hne3
  obtain rfl : b = 2 := by omega
  apply h₀.not_le_Gv
  have h4 : t.Zv 0 ≤ t.Gv 3 := (hZw.trans (win_le_qv (by norm_num) le_rfl))
  simpa using h4

private theorem r65e_le_centralizer_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.Zv 1 ⊓ centralizer (L2 : Set G) ≤ centralizer (t.Qv 0 : Set G) := by
  have hQ0G : t.Qv 0 ≤ t.Gv 1 := by
    have h := (t.Qv_le_Gv hfr 0).2
    rwa [zero_add] at h
  have hQ0L : t.Qv 0 ≤ t.Lv 1 := t.le_Lv hfr (t.isPGroup_Qv 0) hQ0G
  have hL2 : L2 ≤ centralizer ((t.Zv 1 ⊓ centralizer (L2 : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp inf_le_right
  have hQ2 : t.Qv 1 ≤ centralizer ((t.Zv 1 ⊓ centralizer (L2 : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp (inf_le_left.trans (t.Zv_le_centralizer 1))
  have hL : t.Lv 1 ≤ centralizer ((t.Zv 1 ⊓ centralizer (L2 : Set G) : Subgroup G) : Set G) := by
    rw [t.Lv_one]
    exact sup_le hL2 (by rwa [← t.Qv_one])
  exact Subgroup.le_centralizer_iff.mp (hQ0L.trans hL)

private theorem r65e_le_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.Zv 1 ⊓ centralizer (L2 : Set G) ≤ t.Qv 0 := by
  have hQ1G : t.Qv 1 ≤ t.Gv 0 := by
    have h := (t.Qv_le_Gv hfr 1).1
    rwa [sub_self] at h
  have hchar : CharTwo (t.Gv 0) := by
    rw [t.Gv_zero]
    exact F1.parabolic_charTwo (Hyp111R.of_hyp111 rankOneListedFacts hfr.hF.1)
  intro x hx
  have hxG : x ∈ t.Gv 0 := hQ1G (t.Zv_le_Qv 1 (Subgroup.mem_inf.mp hx).1)
  have hxC : x ∈ centralizer (t.Qv 0 : Set G) := r65e_le_centralizer_Qv_zero t hfr hx
  rw [t.Qv_eq 0]
  exact hchar ⟨hxG, by rwa [← t.Qv_eq 0]⟩

private theorem r65e_le_Zv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.Zv 1 ⊓ centralizer (L2 : Set G) ≤ t.Zv 0 := by
  intro x hx
  have hxZ : x ∈ t.Zv 1 := (Subgroup.mem_inf.mp hx).1
  have hx2 : x ^ 2 = 1 := by
    rw [t.Zv_eq 1] at hxZ
    exact CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf hxZ
  have hxQ : x ∈ t.Qv 0 := r65e_le_Qv_zero t hfr hx
  have hxC : x ∈ centralizer (t.Qv 0 : Set G) := r65e_le_centralizer_Qv_zero t hfr hx
  rw [t.Zv_eq 0]
  exact CFSG.Quasithin.mem_omegaOneCenterOf hxQ
    (fun y hy => Subgroup.mem_centralizer_iff.mp hxC y hy) hx2

private theorem r65e_le_bigB {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.Zv 1 ⊓ centralizer (L2 : Set G) ≤ bigB L1 L2 S := by
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le
    (F112W.isSylowTwoOf_parabolic' (Hyp111R.of_hyp111 rankOneListedFacts hfr.hF.1))
  have hQ1 : t.Zv 1 ≤ Q2 L1 L2 S := by
    rw [← t.Qv_one]
    exact t.Zv_le_Qv 1
  exact (inf_le_left.trans hQ1).trans (hQ2S.trans (le_sup_right : S ≤ bigB L1 L2 S))

theorem Zv_one_inf_centralizer_eq_bot_of_Lv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZ0 : t.Lv 0 ≤ centralizer (t.Zv 0 : Set G)) :
    t.Zv 1 ⊓ centralizer (L2 : Set G) = ⊥ := by
  have hCZ0 : t.Zv 1 ⊓ centralizer (L2 : Set G) ≤ t.Zv 0 := r65e_le_Zv_zero t hfr
  have hL1 : L1 ≤ centralizer ((t.Zv 1 ⊓ centralizer (L2 : Set G) : Subgroup G) : Set G) := by
    have h : L1 ≤ t.Lv 0 := by
      rw [t.Lv_zero]
      exact le_sup_left
    exact h.trans (hZ0.trans (Subgroup.centralizer_le hCZ0))
  have hL2 : L2 ≤ centralizer ((t.Zv 1 ⊓ centralizer (L2 : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp inf_le_right
  refine eq_bot_of_le_bigB hfr.hF.1 (r65e_le_bigB t hfr) ?_ ?_
  · exact le_sup_of_le_left (le_inf (le_sup_left : L1 ≤ P1 L1 L2 S)
      (hL1.trans (Subgroup.centralizer_le_normalizer _)))
  · exact le_sup_of_le_left (le_inf (le_sup_left : L2 ≤ P2 L1 L2 S)
      (hL2.trans (Subgroup.centralizer_le_normalizer _)))

private theorem r65f_S_le_Gv_zero : S ≤ t.Gv 0 := by
  rw [t.Gv_zero]
  exact (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right

private theorem r65f_x₁_mem_Gv_zero : t.x₁ ∈ t.Gv 0 := by
  rw [t.Gv_zero]
  exact t.track.x₁_mem

private theorem r65f_conj_mem_Qv_zero {q : G} (hq : q ∈ t.Qv 0) :
    t.x₁⁻¹ * q * t.x₁ ∈ t.Qv 0 :=
  (mem_normalizer_iff''.mp (t.Gv_le_normalizer_Qv 0 t.r65f_x₁_mem_Gv_zero) q).mp hq

private theorem r65f_conj_mem_Zv_one {z : G} (hz : z ∈ t.Zv (-1)) :
    t.x₁⁻¹ * z * t.x₁ ∈ t.Zv 1 := by
  have h1 : P1 L1 L2 S ≤ normalizer (Z1 L1 L2 S : Set G) := by
    have h := t.Gv_le_normalizer_Zv 0
    rwa [t.Gv_zero, t.Zv_zero] at h
  have h2 : P2 L1 L2 S ≤ normalizer (Z2 L1 L2 S : Set G) := by
    have h := t.Gv_le_normalizer_Zv 1
    rwa [t.Gv_one, t.Zv_one] at h
  have h := (t.track.mem_qv_neg_iff h1 h2 (-1)).mp hz
  rwa [neg_neg] at h

private theorem r65f_Zv_zero_eq {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hZ0 : t.Zv 0 ≤ t.Zv (-1) ⊓ t.Zv 1) (hZ0L : t.Lv 0 ≤ centralizer (t.Zv 0 : Set G))
    (hcard0 : Nat.card (t.Zv 0) = 2 ^ f)
    (hcardA : Nat.card (t.Zv 1 ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ f) :
    t.Zv 0 = t.Zv 1 ⊓ centralizer (S : Set G) := by
  have hSL : S ≤ t.Lv 0 := t.le_Lv hfr hfr.hF.1.h1.pgroup t.r65f_S_le_Gv_zero
  have hZS : t.Zv 0 ≤ centralizer (S : Set G) := Subgroup.le_centralizer_iff.mp (hSL.trans hZ0L)
  exact Subgroup.eq_of_le_of_card_ge (le_inf (fun z hz => (hZ0 hz).2) hZS)
    (by rw [hcard0, hcardA])

theorem commutator_Qv_zero_Zv_neg_one_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hZ0 : t.Zv 0 ≤ t.Zv (-1) ⊓ t.Zv 1) (hZ0L : t.Lv 0 ≤ centralizer (t.Zv 0 : Set G))
    (hcard0 : Nat.card (t.Zv 0) = 2 ^ f)
    (hN1 : ∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 1 ⊓ centralizer (S : Set G))
    (hcardA : Nat.card (t.Zv 1 ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ f) :
    ∀ q ∈ t.Qv 0, ∀ z ∈ t.Zv (-1), ⁅q, z⁆ ∈ t.Zv 0 := by
  intro q hq z hz
  have hA : t.Zv 0 = t.Zv 1 ⊓ centralizer (S : Set G) :=
    t.r65f_Zv_zero_eq hfr hZ0 hZ0L hcard0 hcardA
  have h := hN1 _ ((t.r65a_Qv_zero_le_S hfr) (t.r65f_conj_mem_Qv_zero hq)) _
    (t.r65f_conj_mem_Zv_one hz)
  rw [← hA] at h
  have key : ⁅q, z⁆ = t.x₁ * ((t.x₁⁻¹ * q * t.x₁) * (t.x₁⁻¹ * z * t.x₁) * (t.x₁⁻¹ * q * t.x₁)⁻¹ *
      (t.x₁⁻¹ * z * t.x₁)⁻¹) * t.x₁⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [key]
  exact (mem_normalizer_iff.mp (t.Gv_le_normalizer_Zv 0 t.r65f_x₁_mem_Gv_zero) _).mp h

private theorem r65g_mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [mem_inf, mem_inf, hA x, hB x]

private theorem r65g_mem_normalizer_of_map_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  have h1 : g * y * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * (g * y * g⁻¹) * g ∈ H :=
    mem_map_conj_iff
  rw [h, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1
  exact h1.symm

private theorem r65g_Zv_map_tau (i k : ℤ) :
    (t.Zv i).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Zv (i + 2 * k) :=
  map_qv_tau_pow i k

private theorem r65g_Zv_neg_two_le_Zv_neg_one (hZ0 : t.Zv 0 ≤ t.Zv (-1) ⊓ t.Zv 1) :
    t.Zv (-2) ≤ t.Zv (-1) := by
  have h := Subgroup.map_mono (f := (MulAut.conj ((t.x₂ * t.x₁) ^ (-1 : ℤ))).toMonoidHom)
    (hZ0.trans inf_le_right)
  rw [r65g_Zv_map_tau, r65g_Zv_map_tau] at h
  norm_num at h
  exact h

private theorem r65g_Zv_one_le_E {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₁ : t.IsFixRadius 1 2) : t.Zv 1 ≤ t.Qv 0 ⊓ t.Qv 2 := by
  have hw : t.Zv 1 ≤ t.Gw (-1) 3 := by simpa using h₁.le_Gw
  exact le_inf (t.le_Qv_of_le_Gw hfr (by norm_num) (by norm_num) (t.isPGroup_Zv 1) hw)
    (t.le_Qv_of_le_Gw hfr (by norm_num) (by norm_num) (t.isPGroup_Zv 1) hw)

private theorem r65g_conj_mem_E {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₁ : t.IsFixRadius 1 2)
    (hZ0 : t.Zv 0 ≤ t.Zv (-1) ⊓ t.Zv 1)
    (hQZ : ∀ q ∈ t.Qv 0, ∀ z ∈ t.Zv (-1), ⁅q, z⁆ ∈ t.Zv 0)
    {y e : G} (hy : y ∈ t.Zv (-2)) (he : e ∈ t.Qv 0 ⊓ t.Qv 2) :
    y * e * y⁻¹ ∈ t.Qv 0 ⊓ t.Qv 2 := by
  have hy1 : y ∈ t.Zv (-1) := t.r65g_Zv_neg_two_le_Zv_neg_one hZ0 hy
  have hc : ⁅e, y⁆ ∈ t.Zv 0 := hQZ e (mem_inf.mp he).1 y hy1
  have hcE : ⁅e, y⁆ ∈ t.Qv 0 ⊓ t.Qv 2 :=
    t.r65g_Zv_one_le_E hfr h₁ ((hZ0.trans inf_le_right) hc)
  have key : y * e * y⁻¹ = ⁅e, y⁆⁻¹ * e := by
    rw [commutatorElement_def]
    group
  rw [key]
  exact mul_mem (inv_mem hcE) he

private theorem r65g_Zv_neg_two_le_normalizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₁ : t.IsFixRadius 1 2)
    (hZ0 : t.Zv 0 ≤ t.Zv (-1) ⊓ t.Zv 1)
    (hQZ : ∀ q ∈ t.Qv 0, ∀ z ∈ t.Zv (-1), ⁅q, z⁆ ∈ t.Zv 0) :
    t.Zv (-2) ≤ normalizer ((t.Qv 0 ⊓ t.Qv 2 : Subgroup G) : Set G) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro e
  refine ⟨fun he => t.r65g_conj_mem_E hfr h₁ hZ0 hQZ hy he, fun he => ?_⟩
  have h := t.r65g_conj_mem_E hfr h₁ hZ0 hQZ (inv_mem hy) he
  rwa [show y⁻¹ * (y * e * y⁻¹) * y⁻¹⁻¹ = e by group] at h

private theorem r65g_Qv_one_le_normalizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.Qv 1 ≤ normalizer ((t.Qv 0 ⊓ t.Qv 2 : Subgroup G) : Set G) := by
  have h := t.Qv_le_Gv hfr 1
  rw [show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num] at h
  intro q hq
  exact r65g_mem_normalizer_inf (t.Gv_le_normalizer_Qv 0 (h.1 hq))
    (t.Gv_le_normalizer_Qv 2 (h.2 hq))

private theorem r65g_x₂_mem_normalizer_E :
    t.x₂ ∈ normalizer ((t.Qv 0 ⊓ t.Qv 2 : Subgroup G) : Set G) := by
  have hmap : ∀ i : ℤ, (t.Qv i).map (MulAut.conj t.x₂).toMonoidHom = t.Qv (2 - i) := fun i =>
    t.track.map_qv_x₂ (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _) i
  have h0 := hmap 0
  have h2 := hmap 2
  rw [show (2 : ℤ) - 0 = 2 by norm_num] at h0
  rw [show (2 : ℤ) - 2 = 0 by norm_num] at h2
  apply r65g_mem_normalizer_of_map_eq
  rw [Subgroup.map_inf _ _ (MulAut.conj t.x₂).toMonoidHom (MulAut.conj t.x₂).injective, h0, h2,
    inf_comm]

private theorem r65g_Zv_neg_two_le_S {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₀ : t.IsFixRadius 0 3) : t.Zv (-2) ≤ S := by
  have h₀' : t.IsFixRadius (-2) 3 := by simpa using Track.IsFixRadius.shift t h₀ (-1)
  have hw : t.Zv (-2) ≤ t.Gw (-5) 1 := by simpa using h₀'.le_Gw
  have hw' : t.Zv (-2) ≤ t.Gw 0 1 := hw.trans (win_mono (by norm_num) le_rfl)
  have h := t.le_pCoreOf_Gw hfr (show (0 : ℤ) < 1 by norm_num) (t.isPGroup_Zv (-2)) hw'
  rwa [t.pCoreOf_Gw_zero_one hfr] at h

private theorem r65g_not_Zv_neg_two_le_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₀ : t.IsFixRadius 0 3) : ¬ t.Zv (-2) ≤ t.Qv 1 := by
  have h₀' : t.IsFixRadius (-2) 3 := by simpa using Track.IsFixRadius.shift t h₀ (-1)
  have hG : ¬ t.Zv (-2) ≤ t.Gv 2 := by
    have h := h₀'.not_le_Gv
    rwa [show (-2 : ℤ) + ((3 : ℕ) : ℤ) + 1 = 2 by norm_num] at h
  have h1 := (t.Qv_le_Gv hfr 1).2
  rw [show (1 : ℤ) + 1 = 2 by norm_num] at h1
  exact fun h => hG (h.trans h1)

theorem Lv_one_le_normalizer_Qv_zero_inf_Qv_two {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₀ : t.IsFixRadius 0 3) (h₁ : t.IsFixRadius 1 2)
    (hZ0 : t.Zv 0 ≤ t.Zv (-1) ⊓ t.Zv 1)
    (hQZ : ∀ q ∈ t.Qv 0, ∀ z ∈ t.Zv (-1), ⁅q, z⁆ ∈ t.Zv 0) :
    t.Lv 1 ≤ normalizer ((t.Qv 0 ⊓ t.Qv 2 : Subgroup G) : Set G) := by
  set X : Subgroup G := normalizer ((t.Qv 0 ⊓ t.Qv 2 : Subgroup G) : Set G)
  have hQ1X : t.Qv 1 ≤ X := t.r65g_Qv_one_le_normalizer hfr
  have hYX : t.Zv (-2) ≤ X := t.r65g_Zv_neg_two_le_normalizer hfr h₁ hZ0 hQZ
  have hYD : t.D2 ≤ normalizer (t.Zv (-2) : Set G) :=
    ((le_sup_right : t.D2 ≤ t.K).trans (t.K_le_Gv (-2))).trans (t.Gv_le_normalizer_Zv (-2))
  have hSY : S ≤ t.Zv (-2) ⊔ t.Qv 1 :=
    t.S_le_sup_Qv_one_of_torus hfr (t.r65g_Zv_neg_two_le_S hfr h₀) hYD
      (t.r65g_not_Zv_neg_two_le_Qv_one hfr h₀)
  have hSX : S ≤ X := hSY.trans (sup_le hYX hQ1X)
  have hx₂ : t.x₂ ∈ normalizer (X : Set G) := Subgroup.le_normalizer (t.r65g_x₂_mem_normalizer_E)
  have hL2 : L2 ≤ X ⊔ t.Qv 1 :=
    t.L2_le_sup_Qv_one_of_sylow hfr (inf_le_left.trans (hSX.trans le_sup_left)) hx₂
  rw [sup_eq_left.mpr hQ1X] at hL2
  rw [t.Lv_one, ← t.Qv_one]
  exact sup_le hL2 hQ1X

private theorem r65j_map_conj_eq_of_mem {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  rw [mem_map_conj_iff]
  have h := mem_normalizer_iff.mp (inv_mem hg) y
  rw [inv_inv] at h
  exact h.symm

private theorem r65j_map_conj_dc {Q : Subgroup G} {b₁ g b₂ : G}
    (h₂ : b₂ ∈ normalizer (Q : Set G)) :
    Q.map (MulAut.conj (b₁ * g * b₂)).toMonoidHom =
      (Q.map (MulAut.conj g).toMonoidHom).map (MulAut.conj b₁).toMonoidHom := by
  rw [Subgroup.map_conj_map_conj Q g b₁, ← Subgroup.map_conj_map_conj Q b₂ (b₁ * g),
    r65j_map_conj_eq_of_mem h₂]

private theorem r65j_map_conj_dc_eq {Q : Subgroup G} {y x b₁ g b₂ b₃ b₄ : G}
    (hy : y = b₁ * g * b₂) (hx : x = b₃ * g * b₄) (h₂ : b₂ ∈ normalizer (Q : Set G))
    (h₄ : b₄ ∈ normalizer (Q : Set G)) :
    Q.map (MulAut.conj y).toMonoidHom =
      (Q.map (MulAut.conj x).toMonoidHom).map (MulAut.conj (b₁ * b₃⁻¹)).toMonoidHom := by
  rw [hy, hx, r65j_map_conj_dc h₂, r65j_map_conj_dc h₄,
    Subgroup.map_conj_map_conj _ b₃ (b₁ * b₃⁻¹), inv_mul_cancel_right]

open scoped Pointwise in
private theorem r65j_exists_of_mem_doubleCoset {B : Subgroup G} {g p : G}
    (hp : p ∈ (B : Set G) * ({g} : Set G) * (B : Set G)) :
    ∃ b₁ ∈ B, ∃ b₂ ∈ B, p = b₁ * g * b₂ := by
  obtain ⟨u, hu, b₂, hb₂, rfl⟩ := Set.mem_mul.mp hp
  obtain ⟨b₁, hb₁, g', hg', rfl⟩ := Set.mem_mul.mp hu
  rw [Set.mem_singleton_iff] at hg'
  subst hg'
  exact ⟨b₁, hb₁, b₂, hb₂, rfl⟩

private theorem r65j_exists_not_mem_bigB
    (hF : F112HypW L1 L2 S) : ∃ g ∈ L2, g ∉ bigB L1 L2 S := by
  have hR' : Hyp111R L2 L1 S := Hyp111R.symm (Hyp111R.of_hyp111 rankOneListedFacts hF.1)
  have hlt : L2 ⊓ bigB L2 L1 S < L2 := by
    rw [CFSG.Quasithin.F1.inf_bigB_eq_borelOf hR']
    exact CFSG.Quasithin.F1.lt_borelOf hR'
  obtain ⟨g, hgL2, hgB⟩ := SetLike.exists_of_lt hlt
  exact ⟨g, hgL2, fun h => hgB ⟨hgL2, by rwa [bigB_comm]⟩⟩

private theorem r65j_Gv_one_le_normalizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hE : t.Lv 1 ≤ normalizer ((t.Qv 0 ⊓ t.Qv 2 : Subgroup G) : Set G)) :
    t.Gv 1 ≤ normalizer ((t.Qv 0 ⊓ t.Qv 2 : Subgroup G) : Set G) := by
  have hS1 : S ≤ t.Gv 1 := by
    rw [t.Gv_one]
    exact (le_sup_right : S ≤ bigB L1 L2 S).trans (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)
  have hS : S ≤ t.Lv 1 := t.le_Lv hfr hfr.hF.1.h1.pgroup hS1
  have hL2 : L2 ≤ t.Lv 1 := by
    rw [t.Lv_one]
    exact le_sup_left
  have hK : t.K ≤ normalizer ((t.Qv 0 ⊓ t.Qv 2 : Subgroup G) : Set G) := fun k hk =>
    r65g_mem_normalizer_inf (t.Gv_le_normalizer_Qv 0 (t.K_le_Gv 0 hk))
      (t.Gv_le_normalizer_Qv 2 (t.K_le_Gv 2 hk))
  rw [t.Gv_one]
  change L2 ⊔ bigB L1 L2 S ≤ _
  rw [← t.sup_K_eq_bigB]
  exact sup_le (hL2.trans hE) (sup_le (hS.trans hE) hK)

private theorem r65j_inf_le_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hG : t.Gv 1 ≤ normalizer ((t.Qv 0 ⊓ t.Qv 2 : Subgroup G) : Set G)) :
    t.Qv 0 ⊓ t.Qv 2 ≤ t.Qv 1 := by
  have hEG : t.Qv 0 ⊓ t.Qv 2 ≤ t.Gv 1 := by
    have h := (t.Qv_le_Gv hfr 0).2
    rw [zero_add] at h
    exact inf_le_left.trans h
  rw [t.Qv_eq 1]
  exact le_pCoreOf_of_le_normalizer 2 hEG hG ((t.isPGroup_Qv 0).to_le inf_le_left)

private theorem r65j_inf_map_eq {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hG : t.Gv 1 ≤ normalizer ((t.Qv 0 ⊓ t.Qv 2 : Subgroup G) : Set G))
    {y : G} (hy1 : y ∈ t.Gv 1) (hy0 : y ∉ t.Gv 0) :
    t.Qv 0 ⊓ (t.Qv 0).map (MulAut.conj y).toMonoidHom = t.Qv 0 ⊓ t.Qv 2 := by
  obtain ⟨g, hgL2, hgB⟩ := r65j_exists_not_mem_bigB (L1 := L1) (L2 := L2) (S := S) hfr.hF
  have hBP1 : bigB L1 L2 S ≤ t.Gv 0 := by
    rw [t.Gv_zero]
    exact le_sup_right
  have hBP2 : bigB L1 L2 S ≤ t.Gv 1 := by
    rw [t.Gv_one]
    exact le_sup_right
  have hyB : y ∉ bigB L1 L2 S := fun h => hy0 (hBP1 h)
  have hxB : t.x₂ ∉ bigB L1 L2 S := fun h => t.track.x₂_not_mem (by
    have := hBP1 h
    rwa [t.Gv_zero] at this)
  have hyP2 : y ∈ P2 L1 L2 S := by
    rwa [t.Gv_one] at hy1
  have hxP2 : t.x₂ ∈ P2 L1 L2 S := t.track.x₂_mem
  obtain ⟨b₁, hb₁, b₂, hb₂, hy_eq⟩ := r65j_exists_of_mem_doubleCoset
    ((mem_bigB_or_mem_doubleCoset_p2 (n := f) hfr.hf hfr.hF hfr.hL2 hgL2 hgB hyP2).resolve_left
      hyB)
  obtain ⟨b₃, hb₃, b₄, hb₄, hx_eq⟩ := r65j_exists_of_mem_doubleCoset
    ((mem_bigB_or_mem_doubleCoset_p2 (n := f) hfr.hf hfr.hF hfr.hL2 hgL2 hgB hxP2).resolve_left
      hxB)
  have hN0 : ∀ b ∈ bigB L1 L2 S, b ∈ normalizer (t.Qv 0 : Set G) := fun b hb =>
    t.Gv_le_normalizer_Qv 0 (hBP1 hb)
  have hc : b₁ * b₃⁻¹ ∈ bigB L1 L2 S := mul_mem hb₁ (inv_mem hb₃)
  have h02 : (t.Qv 0).map (MulAut.conj t.x₂).toMonoidHom = t.Qv 2 := by
    have h := t.track.map_qv_x₂ (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S)) 0
    rw [sub_zero] at h
    exact h
  rw [r65j_map_conj_dc_eq hy_eq hx_eq (hN0 b₂ hb₂) (hN0 b₄ hb₄), h02]
  have hc0 := r65j_map_conj_eq_of_mem (hN0 _ hc)
  have hcE := r65j_map_conj_eq_of_mem (hG (hBP2 hc))
  calc t.Qv 0 ⊓ (t.Qv 2).map (MulAut.conj (b₁ * b₃⁻¹)).toMonoidHom
      = (t.Qv 0).map (MulAut.conj (b₁ * b₃⁻¹)).toMonoidHom ⊓
          (t.Qv 2).map (MulAut.conj (b₁ * b₃⁻¹)).toMonoidHom := by rw [hc0]
    _ = (t.Qv 0 ⊓ t.Qv 2).map (MulAut.conj (b₁ * b₃⁻¹)).toMonoidHom :=
        (Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective).symm
    _ = t.Qv 0 ⊓ t.Qv 2 := hcE

theorem Qv_zero_inf_map_eq {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hE : t.Lv 1 ≤ normalizer ((t.Qv 0 ⊓ t.Qv 2 : Subgroup G) : Set G)) :
    t.Qv 0 ⊓ t.Qv 2 ≤ t.Qv 1 ∧ ∀ y ∈ t.Gv 1, y ∉ t.Gv 0 →
      t.Qv 0 ⊓ (t.Qv 0).map (MulAut.conj y).toMonoidHom = t.Qv 0 ⊓ t.Qv 2 := by
  have hG := t.r65j_Gv_one_le_normalizer hfr hE
  exact ⟨t.r65j_inf_le_Qv_one hfr hG, fun y hy1 hy0 => t.r65j_inf_map_eq hfr hG hy1 hy0⟩

private theorem r65h_le_Qv_one_inf_Qv_two {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    pCoreOf 2 (t.Gw 0 6) ≤ t.Qv 1 ⊓ t.Qv 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_inf
    (t.le_Qv_of_le_Gw hfr (by norm_num) (by norm_num) (pCoreOf_isPGroup 2 _) (pCoreOf_le 2 _))
    (t.le_Qv_of_le_Gw hfr (by norm_num) (by norm_num) (pCoreOf_isPGroup 2 _) (pCoreOf_le 2 _))

private theorem r65h_le_Gw_neg_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : pCoreOf 2 (t.Gw 0 6) ≤ t.Qv 0) :
    pCoreOf 2 (t.Gw 0 6) ≤ t.Gw (-1) 6 := by
  have h1 : pCoreOf 2 (t.Gw 0 6) ≤ t.Gv (-1) := by
    have := (t.Qv_le_Gv hfr 0).1
    rw [zero_sub] at this
    exact hQ.trans this
  change pCoreOf 2 (t.Gw 0 6) ≤ win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (-1) 6
  rw [show (-1 : ℤ) = 0 - 1 by norm_num, win_sub_one_left (by norm_num)]
  exact le_inf h1 (pCoreOf_le 2 _)

theorem not_Qv_one_inf_Qv_two_le_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h : t.IsMaxArc 0 6) : ¬ t.Qv 1 ⊓ t.Qv 2 ≤ t.Qv 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hle
  have hne : pCoreOf 2 (t.Gw 0 6) ≠ ⊥ := by simpa using h.pCoreOf_ne_bot
  have hbot : pCoreOf 2 (t.Gw (-1) 6) = ⊥ := h.pCoreOf_eq_bot (-1) 6 (by norm_num)
  have hQ0 : pCoreOf 2 (t.Gw 0 6) ≤ t.Qv 0 := (r65h_le_Qv_one_inf_Qv_two t hfr).trans hle
  have hle2 : pCoreOf 2 (t.Gw 0 6) ≤ pCoreOf 2 (t.Gw (-1) 6) :=
    t.le_pCoreOf_Gw hfr (by norm_num) (pCoreOf_isPGroup 2 _) (r65h_le_Gw_neg_one t hfr hQ0)
  rw [hbot] at hle2
  exact hne (le_bot_iff.mp hle2)

private theorem r65i_commutator_mem {s s' : G} (hs : s ∈ S) (hs' : s' ∈ S) : ⁅s, s'⁆ ∈ S :=
  Subgroup.commutator_le_of_le le_rfl le_rfl (Subgroup.commutator_mem_commutator hs hs')

theorem commutator_mem_rootOmega_zero_and_exists_not_mem {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    (∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ t.rootOmega 0) ∧ ∃ s ∈ S, ∃ s' ∈ S, ⁅s, s'⁆ ∉ t.Qv 0 := by
  refine ⟨fun s hs s' hs' => ?_, ?_⟩
  ·
    rw [t.mem_rootOmega_iff hfr 0, zero_add, t.pCoreOf_Gw_zero_one hfr, t.Qv_zero, pow_two]
    exact ⟨r65i_commutator_mem hs hs', commutator_mul_self_mem_Q1 hfr hs hs'⟩
  ·
    rw [t.Qv_zero]
    exact exists_commutator_not_mem_Q1 hfr

private theorem r65k_comm_mem {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

private theorem r65k_comm_mul_mul_mem {N H : Subgroup G} (hHN : H ≤ normalizer (N : Set G))
    {a b c d : G} (hb : b ∈ H) (hc : c ∈ H) (hd : d ∈ H)
    (ha' : ∀ u ∈ H, ⁅u, a⁆ ∈ N) (hc' : ∀ u ∈ H, ⁅u, c⁆ ∈ N) :
    ⁅a * b, c * d⁆ * ⁅b, d⁆⁻¹ ∈ N := by
  have key : ⁅a * b, c * d⁆ * ⁅b, d⁆⁻¹ =
      ⁅b * (c * d) * b⁻¹, a⁆⁻¹ * (⁅b, d⁆ * ⁅d * b * d⁻¹, c⁆ * ⁅b, d⁆⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [key]
  refine mul_mem (inv_mem (ha' _ ?_))
    ((mem_normalizer_iff.mp (hHN (r65k_comm_mem hb hd)) _).mp (hc' _ ?_))
  · exact mul_mem (mul_mem hb (mul_mem hc hd)) (inv_mem hb)
  · exact mul_mem (mul_mem hd hb) (inv_mem hd)

private theorem r65k_conj_qv {Q₁ Q₂ : Subgroup G} (hQ₁ : P1 L1 L2 S ≤ normalizer (Q₁ : Set G))
    (hQ₂ : P2 L1 L2 S ≤ normalizer (Q₂ : Set G)) {i j : ℤ} (hij : i + j = 2) {y : G}
    (hy : y ∈ qv Q₁ Q₂ t.x₁ t.x₂ i) :
    t.x₂⁻¹ * y * t.x₂ ∈ qv Q₁ Q₂ t.x₁ t.x₂ j ∧ t.x₂ * y * t.x₂⁻¹ ∈ qv Q₁ Q₂ t.x₁ t.x₂ j := by
  obtain rfl : j = 2 - i := by omega
  refine ⟨(t.track.mem_qv_two_sub_iff hQ₁ hQ₂ i).mp hy, ?_⟩
  rw [t.track.mem_qv_two_sub_iff hQ₁ hQ₂ (2 - i), sub_sub_cancel]
  convert hy using 1
  group

private theorem r65k_conj_Qv {i j : ℤ} (hij : i + j = 2) {y : G} (hy : y ∈ t.Qv i) :
    t.x₂⁻¹ * y * t.x₂ ∈ t.Qv j ∧ t.x₂ * y * t.x₂⁻¹ ∈ t.Qv j :=
  t.r65k_conj_qv (Q₁ := Q1 L1 L2 S) (Q₂ := Q2 L1 L2 S) (le_normalizer_pCoreOf 2 _)
    (le_normalizer_pCoreOf 2 _) hij hy

private theorem r65k_conj_Zv {i j : ℤ} (hij : i + j = 2) {y : G} (hy : y ∈ t.Zv i) :
    t.x₂⁻¹ * y * t.x₂ ∈ t.Zv j ∧ t.x₂ * y * t.x₂⁻¹ ∈ t.Zv j := by
  have h1 : P1 L1 L2 S ≤ normalizer (Z1 L1 L2 S : Set G) := by
    have h := t.Gv_le_normalizer_Zv 0
    rwa [t.Gv_zero, t.Zv_zero] at h
  have h2 : P2 L1 L2 S ≤ normalizer (Z2 L1 L2 S : Set G) := by
    have h := t.Gv_le_normalizer_Zv 1
    rwa [t.Gv_one, t.Zv_one] at h
  exact t.r65k_conj_qv h1 h2 hij hy

private theorem r65k_map_Qv {i j : ℤ} (hij : i + j = 2) :
    (t.Qv i).map (MulAut.conj t.x₂).toMonoidHom = t.Qv j := by
  obtain rfl : j = 2 - i := by omega
  exact t.track.map_qv_x₂ (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _) i

private theorem r65k_x₂_mem_Gv_one : t.x₂ ∈ t.Gv 1 := by
  rw [t.Gv_one]
  exact t.track.x₂_mem

private theorem r65k_P2_le_normalizer_L2 (hF : Hyp111 L1 L2 S) :
    P2 L1 L2 S ≤ normalizer (L2 : Set G) := by
  have h := bigB_le_normalizer_of_hyp111 hF.symm
  rw [bigB_comm] at h
  exact sup_le le_normalizer h

private theorem r65k_x₂_mem_normalizer_L2 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.x₂ ∈ normalizer (L2 : Set G) :=
  r65k_P2_le_normalizer_L2 hfr.hF.1 t.track.x₂_mem

private theorem r65k_L2_le_normalizer_Qv_one : L2 ≤ normalizer (t.Qv 1 : Set G) := by
  have h : L2 ≤ t.Lv 1 := by
    rw [t.Lv_one]
    exact le_sup_left
  exact h.trans ((t.Lv_le_Gv 1).trans (t.Gv_le_normalizer_Qv 1))

private theorem r65k_S_le_Gv_one : S ≤ t.Gv 1 := by
  rw [t.Gv_one]
  exact (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right

private theorem r65k_Qv_one_le_Gv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 1 ≤ t.Gv 0 := by
  simpa using (t.Qv_le_Gv hfr 1).1

private theorem r65k_Qv_one_le_Gv_two {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 1 ≤ t.Gv 2 := by
  simpa using (t.Qv_le_Gv hfr 1).2

private theorem r65k_Qv_one_le_S {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 1 ≤ S := by
  have hw : t.Qv 1 ≤ t.Gw 0 1 := fun y hy => mem_win_iff.mpr fun i hi0 hi1 => by
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact t.r65k_Qv_one_le_Gv_zero hfr hy
    · exact t.Qv_le_Gv_self 1 hy
  have h2 := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) (t.isPGroup_Qv 1) hw
  rwa [t.pCoreOf_Gw_zero_one hfr] at h2

private theorem r65k_commutator_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : ⁅t.rootOmega 0, S⁆ ≤ t.Qv 0 := by
  have h := t.commutator_rootOmega_le hfr 0
  rwa [zero_add, t.pCoreOf_Gw_zero_one hfr] at h

private theorem r65k_Zv_four_le (h₀ : t.IsFixRadius 0 3) : t.Zv 4 ≤ t.Gw 1 7 := by
  have h₄ : t.IsFixRadius 4 3 := by simpa using Track.IsFixRadius.shift t h₀ 2
  simpa using h₄.le_Gw

private theorem r65k_Zv_four_le_Gv_one (h₀ : t.IsFixRadius 0 3) : t.Zv 4 ≤ t.Gv 1 :=
  (t.r65k_Zv_four_le h₀).trans (win_le_qv (by norm_num) (by norm_num))

private theorem r65k_Zv_four_inf_Gv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h : t.IsMaxArc 0 6) (h₀ : t.IsFixRadius 0 3) :
    t.Zv 4 ⊓ t.Gv 0 = ⊥ := by
  have hw : t.Zv 4 ⊓ t.Gv 0 ≤ t.Gw 0 7 := fun y hy => mem_win_iff.mpr fun i hi0 hi7 => by
    rcases (show i = 0 ∨ 1 ≤ i by omega) with rfl | hi1
    · exact hy.2
    · exact mem_win_iff.mp (t.r65k_Zv_four_le h₀ hy.1) i hi1 hi7
  have hpc := t.le_pCoreOf_Gw hfr (show (0 : ℤ) < 7 by norm_num)
    ((t.isPGroup_Zv 4).to_le inf_le_left) hw
  rw [h.pCoreOf_eq_bot 0 7 (by norm_num)] at hpc
  exact le_bot_iff.mp hpc

private theorem r65k_Zv_two_le_E {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₀ : t.IsFixRadius 0 3) : t.Zv 2 ≤ t.Qv 0 ⊓ t.Qv 2 := by
  have h₂ : t.IsFixRadius 2 3 := by simpa using Track.IsFixRadius.shift t h₀ 1
  have hw : t.Zv 2 ≤ t.Gw (-1) 5 := by simpa using h₂.le_Gw
  exact le_inf (t.le_Qv_of_le_Gw hfr (by norm_num) (by norm_num) (t.isPGroup_Zv 2) hw)
    (t.Zv_le_Qv 2)

private theorem r65k_Zv_four_le_Zv_three (hZ0 : t.Zv 0 ≤ t.Zv (-1) ⊓ t.Zv 1) :
    t.Zv 4 ≤ t.Zv 3 := by
  have h := Subgroup.map_mono (f := (MulAut.conj ((t.x₂ * t.x₁) ^ (2 : ℤ))).toMonoidHom)
    (hZ0.trans inf_le_left)
  rw [show (t.Zv 0).map (MulAut.conj ((t.x₂ * t.x₁) ^ (2 : ℤ))).toMonoidHom = t.Zv (0 + 2 * 2)
      from map_qv_tau_pow 0 2,
    show (t.Zv (-1)).map (MulAut.conj ((t.x₂ * t.x₁) ^ (2 : ℤ))).toMonoidHom =
      t.Zv (-1 + 2 * 2) from map_qv_tau_pow (-1) 2] at h
  norm_num at h
  exact h

private theorem r65k_comm_Qv_two_Zv_three
    (hQZ : ∀ q ∈ t.Qv 0, ∀ z ∈ t.Zv (-1), ⁅q, z⁆ ∈ t.Zv 0) {q w : G}
    (hq : q ∈ t.Qv 2) (hw : w ∈ t.Zv 3) : ⁅q, w⁆ ∈ t.Zv 2 := by
  have hq' := (t.r65k_conj_Qv (i := 2) (j := 0) (by norm_num) hq).1
  have hw' := (t.r65k_conj_Zv (i := 3) (j := -1) (by norm_num) hw).1
  have key : ⁅q, w⁆ = t.x₂ * ⁅t.x₂⁻¹ * q * t.x₂, t.x₂⁻¹ * w * t.x₂⁆ * t.x₂⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [key]
  exact (t.r65k_conj_Zv (i := 0) (j := 2) (by norm_num) (hQZ _ hq' _ hw')).2

private theorem r65k_comm_Qv_two_z {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₀ : t.IsFixRadius 0 3) (hZ0 : t.Zv 0 ≤ t.Zv (-1) ⊓ t.Zv 1)
    (hQZ : ∀ q ∈ t.Qv 0, ∀ z ∈ t.Zv (-1), ⁅q, z⁆ ∈ t.Zv 0) {z q : G} (hz : z ∈ t.Zv 4)
    (hq : q ∈ t.Qv 2) : ⁅q, z⁆ ∈ t.Qv 0 ⊓ t.Qv 2 :=
  t.r65k_Zv_two_le_E hfr h₀
    (t.r65k_comm_Qv_two_Zv_three hQZ hq (t.r65k_Zv_four_le_Zv_three hZ0 hz))

private theorem r65k_mem_E_of_comm
    (h22 : ∀ y ∈ t.Gv 1, y ∉ t.Gv 0 →
      t.Qv 0 ⊓ (t.Qv 0).map (MulAut.conj y).toMonoidHom = t.Qv 0 ⊓ t.Qv 2)
    {z : G} (hz1 : z⁻¹ ∈ t.Gv 1) (hz0 : z⁻¹ ∉ t.Gv 0) {y : G} (hy : y ∈ t.Qv 0)
    (hc : ⁅y, z⁆ ∈ t.Qv 0) : y ∈ t.Qv 0 ⊓ t.Qv 2 := by
  rw [← h22 z⁻¹ hz1 hz0]
  refine mem_inf.mpr ⟨hy, ?_⟩
  rw [mem_map_conj_iff, inv_inv]
  have key : z * y * z⁻¹ = ⁅y, z⁆⁻¹ * y := by
    rw [commutatorElement_def]
    group
  rw [key]
  exact mul_mem (inv_mem hc) hy

private theorem r65k_exists_mul {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hD : (t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0 = t.rootOmega 0) {y : G}
    (hy : y ∈ t.Qv 1 ⊓ t.rootOmega 0) :
    ∃ d₀ ∈ t.Qv 0 ⊓ t.Qv 1, ∃ d₂ ∈ t.Qv 1 ⊓ t.Qv 2, y = d₀ * d₂ := by
  have hN : t.Qv 1 ⊓ t.Qv 2 ≤ normalizer (t.Qv 0 : Set G) :=
    inf_le_left.trans ((t.r65k_Qv_one_le_Gv_zero hfr).trans (t.Gv_le_normalizer_Qv 0))
  have hy' : y ∈ t.Qv 0 ⊔ (t.Qv 1 ⊓ t.Qv 2) := by
    rw [sup_comm, hD]
    exact (mem_inf.mp hy).2
  obtain ⟨d₀, hd₀, d₂, hd₂, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hN).mp hy'
  refine ⟨d₀, mem_inf.mpr ⟨hd₀, ?_⟩, d₂, hd₂, rfl⟩
  have e : d₀ = d₀ * d₂ * d₂⁻¹ := by group
  rw [e]
  exact mul_mem (mem_inf.mp hy).1 (inv_mem (mem_inf.mp hd₂).1)

private theorem r65k_Y_eq {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hD : (t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0 = t.rootOmega 0) :
    t.Qv 1 ⊓ t.rootOmega 0 = (t.Qv 0 ⊓ t.Qv 1) ⊔ (t.Qv 1 ⊓ t.Qv 2) := by
  refine le_antisymm (fun y hy => ?_) (sup_le ?_ ?_)
  · obtain ⟨d₀, hd₀, d₂, hd₂, rfl⟩ := t.r65k_exists_mul hfr hD hy
    exact mul_mem (mem_sup_left hd₀) (mem_sup_right hd₂)
  · exact le_inf inf_le_right (inf_le_left.trans (t.Qv_le_rootOmega hfr 0))
  · exact le_inf inf_le_left (le_sup_left.trans hD.le)

private theorem r65k_x₂_mem_normalizer_Y {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hD : (t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0 = t.rootOmega 0) :
    t.x₂ ∈ normalizer ((t.Qv 1 ⊓ t.rootOmega 0 : Subgroup G) : Set G) := by
  rw [t.r65k_Y_eq hfr hD]
  apply r65g_mem_normalizer_of_map_eq
  rw [Subgroup.map_sup, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective, t.r65k_map_Qv (i := 0) (j := 2) rfl,
    t.r65k_map_Qv (i := 1) (j := 1) rfl, t.r65k_map_Qv (i := 2) (j := 0) rfl,
    inf_comm (t.Qv 2), inf_comm (t.Qv 1) (t.Qv 0), sup_comm]

private theorem r65k_comm_Qv_one_D₂ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hD : (t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0 = t.rootOmega 0) {q d : G}
    (hq : q ∈ t.Qv 1) (hd : d ∈ t.Qv 1 ⊓ t.Qv 2) : ⁅q, d⁆ ∈ t.Qv 0 ⊓ t.Qv 2 := by
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [← commutatorElement_inv]
    exact inv_mem (t.r65k_commutator_le hfr
      (commutator_mem_commutator (hD.le (mem_sup_left hd)) (t.r65k_Qv_one_le_S hfr hq)))
  · rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp (t.Gv_le_normalizer_Qv 2
      (t.r65k_Qv_one_le_Gv_two hfr hq)) d).mp (mem_inf.mp hd).2) (inv_mem (mem_inf.mp hd).2)

private theorem r65k_comm_Qv_one_D₀ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hD : (t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0 = t.rootOmega 0) {q d : G}
    (hq : q ∈ t.Qv 1) (hd : d ∈ t.Qv 0 ⊓ t.Qv 1) : ⁅q, d⁆ ∈ t.Qv 0 ⊓ t.Qv 2 := by
  have hq' := (t.r65k_conj_Qv (i := 1) (j := 1) (by norm_num) hq).1
  have hd0 := (t.r65k_conj_Qv (i := 0) (j := 2) (by norm_num) (mem_inf.mp hd).1).1
  have hd1 := (t.r65k_conj_Qv (i := 1) (j := 1) (by norm_num) (mem_inf.mp hd).2).1
  have h := t.r65k_comm_Qv_one_D₂ hfr hD hq' (mem_inf.mpr ⟨hd1, hd0⟩)
  have key : ⁅q, d⁆ = t.x₂ * ⁅t.x₂⁻¹ * q * t.x₂, t.x₂⁻¹ * d * t.x₂⁆ * t.x₂⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [key]
  exact (mem_normalizer_iff.mp t.r65g_x₂_mem_normalizer_E _).mp h

private theorem r65k_comm_Qv_one_Y {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hD : (t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0 = t.rootOmega 0) {q y : G}
    (hq : q ∈ t.Qv 1) (hy : y ∈ t.Qv 1 ⊓ t.rootOmega 0) : ⁅q, y⁆ ∈ t.Qv 0 ⊓ t.Qv 2 := by
  obtain ⟨d₀, hd₀, d₂, hd₂, rfl⟩ := t.r65k_exists_mul hfr hD hy
  have key : ⁅q, d₀ * d₂⁆ = ⁅q, d₀⁆ * (d₀ * ⁅q, d₂⁆ * d₀⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [key]
  exact mul_mem (t.r65k_comm_Qv_one_D₀ hfr hD hq hd₀)
    ((mem_normalizer_iff.mp (t.r65g_Qv_one_le_normalizer hfr (mem_inf.mp hd₀).2) _).mp
      (t.r65k_comm_Qv_one_D₂ hfr hD hq hd₂))

private theorem r65k_comm_mem_Y {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hSz : ∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ t.rootOmega 0) {q q' : G}
    (hq : q ∈ t.Qv 1) (hq' : q' ∈ t.Qv 1) : ⁅q, q'⁆ ∈ t.Qv 1 ⊓ t.rootOmega 0 :=
  mem_inf.mpr ⟨r65k_comm_mem hq hq',
    hSz q (t.r65k_Qv_one_le_S hfr hq) q' (t.r65k_Qv_one_le_S hfr hq')⟩

private theorem r65k_conj_mem_rootOmega {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {s h : G} (hs : s ∈ S) (hh : h ∈ t.rootOmega 0) :
    s * h * s⁻¹ ∈ t.rootOmega 0 := by
  have h1 := t.r65k_commutator_le hfr (commutator_mem_commutator hh hs)
  have key : s * h * s⁻¹ = ⁅h, s⁆⁻¹ * h := by
    rw [commutatorElement_def]
    group
  rw [key]
  exact mul_mem (inv_mem (t.Qv_le_rootOmega hfr 0 h1)) hh

private theorem r65k_S_le_normalizer_rootOmega {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : S ≤ normalizer (t.rootOmega 0 : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro h
  refine ⟨t.r65k_conj_mem_rootOmega hfr hs, fun hh => ?_⟩
  have h' := t.r65k_conj_mem_rootOmega hfr (inv_mem hs) hh
  rwa [show s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ = h by group] at h'

private theorem r65k_L2_comm_mem_Y {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hSz : ∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ t.rootOmega 0)
    (hD : (t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0 = t.rootOmega 0) {l q : G} (hl : l ∈ L2)
    (hq : q ∈ t.Qv 1) : ⁅l, q⁆ ∈ t.Qv 1 ⊓ t.rootOmega 0 := by
  have hSX : S ≤ centralizerMod (t.Qv 1 ⊓ t.rootOmega 0) ⊤ (t.Qv 1) := by
    intro s hs
    refine ⟨mem_top s, r65g_mem_normalizer_inf
      (t.Gv_le_normalizer_Qv 1 (t.r65k_S_le_Gv_one hs)) (t.r65k_S_le_normalizer_rootOmega hfr hs),
      fun u hu => ?_⟩
    refine mem_inf.mpr ⟨?_, ?_⟩
    · exact mul_mem ((mem_normalizer_iff.mp (t.Gv_le_normalizer_Qv 1 (t.r65k_S_le_Gv_one hs))
        u).mp hu) (inv_mem hu)
    · have h := hSz s hs u (t.r65k_Qv_one_le_S hfr hu)
      rwa [commutatorElement_def] at h
  have hQX : t.Qv 1 ≤ centralizerMod (t.Qv 1 ⊓ t.rootOmega 0) ⊤ (t.Qv 1) :=
    (t.r65k_Qv_one_le_S hfr).trans hSX
  have hx₂ : t.x₂ ∈ normalizer
      ((centralizerMod (t.Qv 1 ⊓ t.rootOmega 0) ⊤ (t.Qv 1) : Subgroup G) : Set G) := by
    refine le_normalizer_centralizerMod (H := zpowers t.x₂) ?_ ?_ ?_ (mem_zpowers t.x₂)
    · exact zpowers_le.mpr (t.r65k_x₂_mem_normalizer_Y hfr hD)
    · exact zpowers_le.mpr (mem_normalizer_iff.mpr fun h => by simp)
    · exact zpowers_le.mpr (t.Gv_le_normalizer_Qv 1 t.r65k_x₂_mem_Gv_one)
  have hL2 := t.L2_le_sup_Qv_one_of_sylow hfr (inf_le_left.trans (hSX.trans le_sup_left)) hx₂
  rw [sup_eq_left.mpr hQX] at hL2
  rw [commutatorElement_def]
  exact (hL2 hl).2.2 q hq

private theorem r65k_L2_comm_comm {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hSz : ∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ t.rootOmega 0)
    (hD : (t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0 = t.rootOmega 0) {l q q' : G} (hl : l ∈ L2)
    (hq : q ∈ t.Qv 1) (hq' : q' ∈ t.Qv 1) : ⁅l, ⁅q, q'⁆⁆ ∈ t.Qv 0 ⊓ t.Qv 2 := by
  have key : ⁅l, ⁅q, q'⁆⁆ = ⁅⁅l, q⁆ * q, ⁅l, q'⁆ * q'⁆ * ⁅q, q'⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [key]
  have hy := t.r65k_L2_comm_mem_Y hfr hSz hD hl hq
  have hy' := t.r65k_L2_comm_mem_Y hfr hSz hD hl hq'
  exact r65k_comm_mul_mul_mem (t.r65g_Qv_one_le_normalizer hfr) hq (mem_inf.mp hy').1 hq'
    (fun u hu => t.r65k_comm_Qv_one_Y hfr hD hu hy) (fun u hu => t.r65k_comm_Qv_one_Y hfr hD hu hy')

private theorem r65k_mem_D₂ {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (h : t.IsMaxArc 0 6) (h₀ : t.IsFixRadius 0 3)
    (h22 : ∀ y ∈ t.Gv 1, y ∉ t.Gv 0 →
      t.Qv 0 ⊓ (t.Qv 0).map (MulAut.conj y).toMonoidHom = t.Qv 0 ⊓ t.Qv 2)
    (hZ0 : t.Zv 0 ≤ t.Zv (-1) ⊓ t.Zv 1)
    (hQZ : ∀ q ∈ t.Qv 0, ∀ z ∈ t.Zv (-1), ⁅q, z⁆ ∈ t.Zv 0)
    (hD : (t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0 = t.rootOmega 0) {y : G}
    (hy : y ∈ t.Qv 1 ⊓ t.rootOmega 0) (hyL : ∀ l ∈ L2, ⁅l, y⁆ ∈ t.Qv 0 ⊓ t.Qv 2) :
    y ∈ t.Qv 1 ⊓ t.Qv 2 := by
  obtain ⟨z, hz, hz1⟩ :=
    (Subgroup.bot_or_exists_ne_one (t.Zv 4)).resolve_left (t.Zv_ne_bot hfr.hF 4)
  have hzG1 : z ∈ t.Gv 1 := t.r65k_Zv_four_le_Gv_one h₀ hz
  have hzG0 : z⁻¹ ∉ t.Gv 0 := fun h' => hz1 (by
    have hz' : z ∈ t.Zv 4 ⊓ t.Gv 0 := mem_inf.mpr ⟨hz, inv_mem_iff.mp h'⟩
    rw [t.r65k_Zv_four_inf_Gv_zero hfr h h₀] at hz'
    exact mem_bot.mp hz')
  have hzL : z ∈ t.Qv 1 ⊔ L2 := by
    rw [t.Qv_one, sup_comm, ← t.Lv_one]
    exact t.le_Lv hfr (t.isPGroup_Zv 4) (t.r65k_Zv_four_le_Gv_one h₀) hz
  obtain ⟨q, hq, l, hl, hzql⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes t.r65k_L2_le_normalizer_Qv_one).mp hzL
  have hzy : ⁅z, y⁆ ∈ t.Qv 0 ⊓ t.Qv 2 := by
    have key : ⁅q * l, y⁆ = q * ⁅l, y⁆ * q⁻¹ * ⁅q, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hzql, key]
    exact mul_mem ((mem_normalizer_iff.mp (t.r65g_Qv_one_le_normalizer hfr hq) _).mp
      (hyL l hl)) (t.r65k_comm_Qv_one_Y hfr hD hq hy)
  obtain ⟨d₀, hd₀, d₂, hd₂, rfl⟩ := t.r65k_exists_mul hfr hD hy
  have hz2 : ⁅z, d₂⁆ ∈ t.Qv 0 ⊓ t.Qv 2 := by
    rw [← commutatorElement_inv]
    exact inv_mem (t.r65k_comm_Qv_two_z hfr h₀ hZ0 hQZ hz (mem_inf.mp hd₂).2)
  have hz0 : ⁅z, d₀⁆ ∈ t.Qv 0 ⊓ t.Qv 2 := by
    have key : ⁅z, d₀⁆ = ⁅z, d₀ * d₂⁆ * (d₀ * ⁅z, d₂⁆ * d₀⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [key]
    exact mul_mem hzy (inv_mem ((mem_normalizer_iff.mp
      (t.r65g_Qv_one_le_normalizer hfr (mem_inf.mp hd₀).2) _).mp hz2))
  have hd₀E : d₀ ∈ t.Qv 0 ⊓ t.Qv 2 :=
    t.r65k_mem_E_of_comm h22 (inv_mem hzG1) hzG0 (mem_inf.mp hd₀).1 (by
      rw [← commutatorElement_inv]
      exact inv_mem (mem_inf.mp hz0).1)
  exact mul_mem (mem_inf.mpr ⟨(mem_inf.mp hd₀).2, (mem_inf.mp hd₀E).2⟩) hd₂

private theorem r65k_mem_E {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (h : t.IsMaxArc 0 6) (h₀ : t.IsFixRadius 0 3)
    (h22 : ∀ y ∈ t.Gv 1, y ∉ t.Gv 0 →
      t.Qv 0 ⊓ (t.Qv 0).map (MulAut.conj y).toMonoidHom = t.Qv 0 ⊓ t.Qv 2)
    (hZ0 : t.Zv 0 ≤ t.Zv (-1) ⊓ t.Zv 1)
    (hQZ : ∀ q ∈ t.Qv 0, ∀ z ∈ t.Zv (-1), ⁅q, z⁆ ∈ t.Zv 0)
    (hD : (t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0 = t.rootOmega 0) {y : G}
    (hy : y ∈ t.Qv 1 ⊓ t.rootOmega 0) (hyL : ∀ l ∈ L2, ⁅l, y⁆ ∈ t.Qv 0 ⊓ t.Qv 2) :
    y ∈ t.Qv 0 ⊓ t.Qv 2 := by
  have h2 := t.r65k_mem_D₂ hfr h h₀ h22 hZ0 hQZ hD hy hyL
  have hy' : t.x₂⁻¹ * y * t.x₂ ∈ t.Qv 1 ⊓ t.rootOmega 0 :=
    (mem_normalizer_iff''.mp (t.r65k_x₂_mem_normalizer_Y hfr hD) y).mp hy
  have hyL' : ∀ l ∈ L2, ⁅l, t.x₂⁻¹ * y * t.x₂⁆ ∈ t.Qv 0 ⊓ t.Qv 2 := by
    intro l hl
    have hl' : t.x₂ * l * t.x₂⁻¹ ∈ L2 :=
      (mem_normalizer_iff.mp (t.r65k_x₂_mem_normalizer_L2 hfr) l).mp hl
    have key : ⁅l, t.x₂⁻¹ * y * t.x₂⁆ = t.x₂⁻¹ * ⁅t.x₂ * l * t.x₂⁻¹, y⁆ * t.x₂ := by
      simp only [commutatorElement_def]
      group
    rw [key]
    exact (mem_normalizer_iff''.mp t.r65g_x₂_mem_normalizer_E _).mp (hyL _ hl')
  have h2' := t.r65k_mem_D₂ hfr h h₀ h22 hZ0 hQZ hD hy' hyL'
  have h0 : y ∈ t.Qv 0 := by
    have e : y = t.x₂ * (t.x₂⁻¹ * y * t.x₂) * t.x₂⁻¹ := by group
    rw [e]
    exact (t.r65k_conj_Qv (i := 2) (j := 0) (by norm_num) (mem_inf.mp h2').2).2
  exact mem_inf.mpr ⟨h0, (mem_inf.mp h2).2⟩

private theorem r65k_S_le_sup {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (h₁ : t.IsFixRadius 1 2) : S ≤ t.Qv 0 ⊔ t.Qv 1 := by
  have h₁' : t.IsFixRadius (-1) 2 := by simpa using Track.IsFixRadius.shift t h₁ (-1)
  have hw : t.Zv (-1) ≤ t.Gw (-3) 1 := by simpa using h₁'.le_Gw
  have hG : ¬ t.Zv (-1) ≤ t.Gv 2 := by simpa using h₁'.not_le_Gv
  have hYS : t.Zv (-1) ≤ S := by
    have h2 := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) (t.isPGroup_Zv (-1))
      (hw.trans (win_mono (by norm_num) le_rfl))
    rwa [t.pCoreOf_Gw_zero_one hfr] at h2
  have hYD : t.D2 ≤ normalizer (t.Zv (-1) : Set G) :=
    (le_sup_right : t.D2 ≤ t.K).trans ((t.K_le_Gv (-1)).trans (t.Gv_le_normalizer_Zv (-1)))
  have hYQ : ¬ t.Zv (-1) ≤ t.Qv 1 := fun hle => hG (hle.trans (t.r65k_Qv_one_le_Gv_two hfr))
  have hZQ : t.Zv (-1) ≤ t.Qv 0 := t.le_Qv_of_le_Gw hfr (u := -3) (w := 1) (j := 0)
    (by norm_num) (by norm_num) (t.isPGroup_Zv (-1)) hw
  exact (t.S_le_sup_Qv_one_of_torus hfr hYS hYD hYQ).trans (sup_le_sup_right hZQ _)

private theorem r65k_comm_Qv_zero {u q : G} (hu : u ∈ S) (hq : q ∈ t.Qv 0) : ⁅u, q⁆ ∈ t.Qv 0 := by
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.mp (t.Gv_le_normalizer_Qv 0 (t.r65f_S_le_Gv_zero hu)) q).mp hq)
    (inv_mem hq)

theorem false_of_sup_eq_rootOmega {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (h : t.IsMaxArc 0 6) (h₀ : t.IsFixRadius 0 3) (h₁ : t.IsFixRadius 1 2)
    (h22 : ∀ y ∈ t.Gv 1, y ∉ t.Gv 0 →
      t.Qv 0 ⊓ (t.Qv 0).map (MulAut.conj y).toMonoidHom = t.Qv 0 ⊓ t.Qv 2)
    (hSz : ∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ t.rootOmega 0) (hSz' : ∃ s ∈ S, ∃ s' ∈ S, ⁅s, s'⁆ ∉ t.Qv 0)
    (hZ0 : t.Zv 0 ≤ t.Zv (-1) ⊓ t.Zv 1)
    (hQZ : ∀ q ∈ t.Qv 0, ∀ z ∈ t.Zv (-1), ⁅q, z⁆ ∈ t.Zv 0)
    (hD : (t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0 = t.rootOmega 0) : False := by
  have hQQ : ∀ q ∈ t.Qv 1, ∀ q' ∈ t.Qv 1, ⁅q, q'⁆ ∈ t.Qv 0 ⊓ t.Qv 2 := fun q hq q' hq' =>
    t.r65k_mem_E hfr h h₀ h22 hZ0 hQZ hD (t.r65k_comm_mem_Y hfr hSz hq hq')
      (fun l hl => t.r65k_L2_comm_comm hfr hSz hD hl hq hq')
  have hN : t.Qv 1 ≤ normalizer (t.Qv 0 : Set G) :=
    (t.r65k_Qv_one_le_Gv_zero hfr).trans (t.Gv_le_normalizer_Qv 0)
  obtain ⟨s, hs, s', hs', hns⟩ := hSz'
  obtain ⟨q₀, hq₀, q₁, hq₁, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hN).mp (t.r65k_S_le_sup hfr h₁ hs)
  obtain ⟨q₀', hq₀', q₁', hq₁', rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hN).mp (t.r65k_S_le_sup hfr h₁ hs')
  apply hns
  have hc := r65k_comm_mul_mul_mem (N := t.Qv 0) (H := S)
    (t.r65f_S_le_Gv_zero.trans (t.Gv_le_normalizer_Qv 0)) (t.r65k_Qv_one_le_S hfr hq₁)
    (t.r65a_Qv_zero_le_S hfr hq₀') (t.r65k_Qv_one_le_S hfr hq₁')
    (fun u hu => t.r65k_comm_Qv_zero hu hq₀) (fun u hu => t.r65k_comm_Qv_zero hu hq₀')
  have e : ⁅q₀ * q₁, q₀' * q₁'⁆ = ⁅q₀ * q₁, q₀' * q₁'⁆ * ⁅q₁, q₁'⁆⁻¹ * ⁅q₁, q₁'⁆ := by group
  rw [e]
  exact mul_mem hc (mem_inf.mp (hQQ q₁ hq₁ q₁' hq₁')).1

private theorem r65l_commutator_mem_left {A : Subgroup G} {a b : G} (ha : a ∈ A)
    (hb : b ∈ normalizer (A : Set G)) : ⁅a, b⁆ ∈ A := by
  have h : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
  rw [h]
  exact mul_mem ha ((mem_normalizer_iff.mp hb _).mp (inv_mem ha))

private theorem r65l_commutator_mem_right {A : Subgroup G} {a b : G}
    (ha : a ∈ normalizer (A : Set G)) (hb : b ∈ A) : ⁅a, b⁆ ∈ A := by
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.mp ha _).mp hb) (inv_mem hb)

private theorem r65l_commutator_mem_sup {A B : Subgroup G} (hA : A ≤ normalizer (B : Set G))
    (hAA : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ B) {s s' : G} (hs : s ∈ A ⊔ B) (hs' : s' ∈ A ⊔ B) :
    ⁅s, s'⁆ ∈ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hA).mp hs
  obtain ⟨a', ha', b', hb', rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hA).mp hs'
  have nB : ∀ g ∈ A, ∀ x ∈ B, g * x * g⁻¹ ∈ B := fun g hg x hx =>
    (mem_normalizer_iff.mp (hA hg) x).mp hx
  have key : ⁅a * b, a' * b'⁆ = a * (b * (a' * (b' * b⁻¹) * a'⁻¹) *
      (a' * a⁻¹ * b'⁻¹ * (a' * a⁻¹)⁻¹)) * a⁻¹ * ⁅a, a'⁆ := by
    simp only [commutatorElement_def]; group
  rw [key]
  exact mul_mem (nB a ha _ (mul_mem (mul_mem hb (nB a' ha' _ (mul_mem hb' (inv_mem hb))))
    (nB _ (mul_mem ha' (inv_mem ha)) _ (inv_mem hb')))) (hAA a ha a' ha')

private theorem r65l_eq_one_of_sq {M : Type*} [Group M] {a b x : M} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b * (a * b) = 1) (h : b * a = a * b * x) : x = 1 :=
  calc x = (a * b)⁻¹ * (b * a) := by rw [h]; group
    _ = a * b * (b * a) := by rw [inv_eq_of_mul_eq_one_right hab]
    _ = a * (b * b) * a := by group
    _ = 1 := by rw [hb, mul_one, ha]

open Classical in
private noncomputable def r65l_bar (E : Subgroup G) (x : G) :
    ↥(normalizer (E : Set G)) ⧸ E.subgroupOf (normalizer (E : Set G)) :=
  if h : x ∈ normalizer (E : Set G) then QuotientGroup.mk ⟨x, h⟩ else 1

private theorem r65l_bar_of_mem {E : Subgroup G} {x : G} (hx : x ∈ normalizer (E : Set G)) :
    r65l_bar E x = QuotientGroup.mk ⟨x, hx⟩ := by
  rw [r65l_bar, dif_pos hx]

private theorem r65l_bar_mul {E : Subgroup G} {x y : G} (hx : x ∈ normalizer (E : Set G))
    (hy : y ∈ normalizer (E : Set G)) : r65l_bar E (x * y) = r65l_bar E x * r65l_bar E y := by
  rw [r65l_bar_of_mem hx, r65l_bar_of_mem hy, r65l_bar_of_mem (mul_mem hx hy)]
  rfl

private theorem r65l_bar_eq_one {E : Subgroup G} {x : G} (hx : x ∈ normalizer (E : Set G)) :
    r65l_bar E x = 1 ↔ x ∈ E := by
  rw [r65l_bar_of_mem hx, QuotientGroup.eq_one_iff, mem_subgroupOf]

private theorem r65l_Qv_one_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 1 ≤ t.Gv 0 ∧ t.Qv 1 ≤ t.Gv 2 := by
  have h := t.Qv_le_Gv hfr 1
  rw [show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num] at h
  exact h

private theorem r65l_mem_Qv_iff (i : ℤ) {y : G} :
    y ∈ t.Qv i ↔ t.x₂⁻¹ * y * t.x₂ ∈ t.Qv (2 - i) :=
  t.track.mem_qv_two_sub_iff (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _) i

private theorem r65l_Zv_four_le_Qv_two {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h₀ : t.IsFixRadius 0 3) : t.Zv 4 ≤ t.Qv 2 :=
  t.le_Qv_of_le_Gw hfr (u := 1) (w := 7) (by norm_num) (by norm_num) (t.isPGroup_Zv 4)
    (t.r65k_Zv_four_le h₀)

private theorem r65l_commutator_D_D {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {d d' : G} (hd : d ∈ t.Qv 0 ⊓ t.Qv 1)
    (hd' : d' ∈ t.Qv 1 ⊓ t.Qv 2) : ⁅d, d'⁆ ∈ t.Qv 0 ⊓ t.Qv 2 :=
  mem_inf.mpr ⟨r65l_commutator_mem_left (mem_inf.mp hd).1
      (t.Gv_le_normalizer_Qv 0 ((t.r65l_Qv_one_le hfr).1 (mem_inf.mp hd').1)),
    r65l_commutator_mem_right
      (t.Gv_le_normalizer_Qv 2 ((t.r65l_Qv_one_le hfr).2 (mem_inf.mp hd).2)) (mem_inf.mp hd').2⟩

private theorem r65l_commutator_D_z {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {y z : G} (hy : y ∈ t.Qv 0 ⊓ t.Qv 1) (hz1 : z ∈ t.Gv 1)
    (hz2 : z ∈ t.Qv 2) : ⁅y, z⁆ ∈ t.Qv 1 ⊓ t.Qv 2 :=
  mem_inf.mpr ⟨r65l_commutator_mem_left (mem_inf.mp hy).2 (t.Gv_le_normalizer_Qv 1 hz1),
    r65l_commutator_mem_right
      (t.Gv_le_normalizer_Qv 2 ((t.r65l_Qv_one_le hfr).2 (mem_inf.mp hy).2)) hz2⟩

private theorem r65l_mem_E_of_commutator_mem
    (h22 : ∀ y ∈ t.Gv 1, y ∉ t.Gv 0 →
      t.Qv 0 ⊓ (t.Qv 0).map (MulAut.conj y).toMonoidHom = t.Qv 0 ⊓ t.Qv 2)
    {z y : G} (hz1 : z ∈ t.Gv 1) (hz0 : z ∉ t.Gv 0) (hy : y ∈ t.Qv 0)
    (hc : ⁅y, z⁆ ∈ t.Qv 0) : y ∈ t.Qv 0 ⊓ t.Qv 2 := by
  have hz0' : z⁻¹ ∉ t.Gv 0 := fun h => hz0 (by simpa using inv_mem h)
  rw [← h22 z⁻¹ (inv_mem hz1) hz0', mem_inf, mem_map_conj_iff, inv_inv]
  have e : z * y * z⁻¹ = (y⁻¹ * ⁅y, z⁆)⁻¹ := by rw [commutatorElement_def]; group
  rw [e]
  exact ⟨hy, inv_mem (mul_mem (inv_mem hy) hc)⟩

private theorem r65l_bar_mul_commutator {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {z y₁ y₂ : G} (hz1 : z ∈ t.Gv 1) (hz2 : z ∈ t.Qv 2)
    (hy₁ : y₁ ∈ t.Qv 0 ⊓ t.Qv 1) (hy₂ : y₂ ∈ t.Qv 0 ⊓ t.Qv 1) :
    r65l_bar (t.Qv 0 ⊓ t.Qv 2) ⁅y₁ * y₂, z⁆ =
      r65l_bar (t.Qv 0 ⊓ t.Qv 2) ⁅y₂, z⁆ * r65l_bar (t.Qv 0 ⊓ t.Qv 2) ⁅y₁, z⁆ := by
  have hN := t.r65g_Qv_one_le_normalizer hfr
  have hc₁ := hN (mem_inf.mp (t.r65l_commutator_D_z hfr hy₁ hz1 hz2)).1
  have hc₂' := t.r65l_commutator_D_z hfr hy₂ hz1 hz2
  have hc₂ := hN (mem_inf.mp hc₂').1
  have hd := t.r65l_commutator_D_D hfr hy₁ hc₂'
  have key : ⁅y₁ * y₂, z⁆ = ⁅y₁, ⁅y₂, z⁆⁆ * (⁅y₂, z⁆ * ⁅y₁, z⁆) := by
    simp only [commutatorElement_def]; group
  rw [key, r65l_bar_mul (le_normalizer hd) (mul_mem hc₂ hc₁),
    (r65l_bar_eq_one (le_normalizer hd)).mpr hd, one_mul, r65l_bar_mul hc₂ hc₁]

private theorem r65l_bar_sq {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {z y : G} (hz1 : z ∈ t.Gv 1) (hz2 : z ∈ t.Qv 2)
    (hzz : z * z = 1) (hzc : ∀ q ∈ t.Qv 2, ⁅q, z⁆ ∈ t.Qv 0 ⊓ t.Qv 2)
    (hy : y ∈ t.Qv 0 ⊓ t.Qv 1) :
    r65l_bar (t.Qv 0 ⊓ t.Qv 2) ⁅y, z⁆ * r65l_bar (t.Qv 0 ⊓ t.Qv 2) ⁅y, z⁆ = 1 := by
  have hc := t.r65l_commutator_D_z hfr hy hz1 hz2
  have hcN := t.r65g_Qv_one_le_normalizer hfr (mem_inf.mp hc).1
  have he : ⁅z, ⁅y, z⁆⁆ ∈ t.Qv 0 ⊓ t.Qv 2 := by
    have h := inv_mem (hzc _ (mem_inf.mp hc).2)
    rwa [commutatorElement_inv] at h
  have heN := le_normalizer he
  have key : ⁅y, z⁆ * ⁅z, ⁅y, z⁆⁆ * ⁅y, z⁆ = 1 :=
    calc ⁅y, z⁆ * ⁅z, ⁅y, z⁆⁆ * ⁅y, z⁆ = y * (z * z) * y⁻¹ * (z * z)⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = 1 := by rw [hzz]; group
  calc r65l_bar (t.Qv 0 ⊓ t.Qv 2) ⁅y, z⁆ * r65l_bar (t.Qv 0 ⊓ t.Qv 2) ⁅y, z⁆
      = r65l_bar (t.Qv 0 ⊓ t.Qv 2) ⁅y, z⁆ * r65l_bar (t.Qv 0 ⊓ t.Qv 2) ⁅z, ⁅y, z⁆⁆ *
          r65l_bar (t.Qv 0 ⊓ t.Qv 2) ⁅y, z⁆ := by
        rw [(r65l_bar_eq_one heN).mpr he, mul_one]
    _ = r65l_bar (t.Qv 0 ⊓ t.Qv 2) (⁅y, z⁆ * ⁅z, ⁅y, z⁆⁆ * ⁅y, z⁆) := by
        rw [r65l_bar_mul (mul_mem hcN heN) hcN, r65l_bar_mul hcN heN]
    _ = 1 := by
        rw [key, r65l_bar_eq_one (one_mem _)]
        exact one_mem _

private theorem r65l_mem_E_of_bar_eq_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (h22 : ∀ y ∈ t.Gv 1, y ∉ t.Gv 0 →
      t.Qv 0 ⊓ (t.Qv 0).map (MulAut.conj y).toMonoidHom = t.Qv 0 ⊓ t.Qv 2)
    {z y : G} (hz1 : z ∈ t.Gv 1) (hz2 : z ∈ t.Qv 2) (hz0 : z ∉ t.Gv 0)
    (hy : y ∈ t.Qv 0 ⊓ t.Qv 1) (h1 : r65l_bar (t.Qv 0 ⊓ t.Qv 2) ⁅y, z⁆ = 1) :
    y ∈ t.Qv 0 ⊓ t.Qv 2 := by
  have hc := t.r65l_commutator_D_z hfr hy hz1 hz2
  have hcE := (r65l_bar_eq_one (t.r65g_Qv_one_le_normalizer hfr (mem_inf.mp hc).1)).mp h1
  exact t.r65l_mem_E_of_commutator_mem h22 hz1 hz0 (mem_inf.mp hy).1 (mem_inf.mp hcE).1

private theorem r65l_commutator_D_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (h22 : ∀ y ∈ t.Gv 1, y ∉ t.Gv 0 →
      t.Qv 0 ⊓ (t.Qv 0).map (MulAut.conj y).toMonoidHom = t.Qv 0 ⊓ t.Qv 2)
    {z : G} (hz1 : z ∈ t.Gv 1) (hz2 : z ∈ t.Qv 2) (hz0 : z ∉ t.Gv 0) (hzz : z * z = 1)
    (hzc : ∀ q ∈ t.Qv 2, ⁅q, z⁆ ∈ t.Qv 0 ⊓ t.Qv 2)
    {y₁ y₂ : G} (hy₁ : y₁ ∈ t.Qv 0 ⊓ t.Qv 1) (hy₂ : y₂ ∈ t.Qv 0 ⊓ t.Qv 1) :
    ⁅y₁, y₂⁆ ∈ t.Qv 0 ⊓ t.Qv 2 := by
  have hw : ⁅y₁, y₂⁆ ∈ t.Qv 0 ⊓ t.Qv 1 := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hy₁ hy₂) (inv_mem hy₁)) (inv_mem hy₂)
  have h21 : y₂ * y₁ ∈ t.Qv 0 ⊓ t.Qv 1 := mul_mem hy₂ hy₁
  have e : y₁ * y₂ = ⁅y₁, y₂⁆ * (y₂ * y₁) := by rw [commutatorElement_def]; group
  refine t.r65l_mem_E_of_bar_eq_one hfr h22 hz1 hz2 hz0 hw (r65l_eq_one_of_sq
    (t.r65l_bar_sq hfr hz1 hz2 hzz hzc hy₁) (t.r65l_bar_sq hfr hz1 hz2 hzz hzc hy₂) ?_ ?_)
  · rw [← t.r65l_bar_mul_commutator hfr hz1 hz2 hy₂ hy₁]
    exact t.r65l_bar_sq hfr hz1 hz2 hzz hzc h21
  · rw [← t.r65l_bar_mul_commutator hfr hz1 hz2 hy₁ hy₂,
      ← t.r65l_bar_mul_commutator hfr hz1 hz2 hy₂ hy₁,
      ← t.r65l_bar_mul_commutator hfr hz1 hz2 hw h21, ← e]

private theorem r65l_map_S_le (hD : S ≤ (t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0) :
    S.map (MulAut.conj t.x₂).toMonoidHom ≤ (t.Qv 0 ⊓ t.Qv 1) ⊔ t.Qv 2 := by
  have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hD
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj t.x₂).injective, t.r65d_map_Qv_x₂,
    t.r65d_map_Qv_x₂, t.r65d_map_Qv_x₂, show (2 : ℤ) - 1 = 1 by norm_num,
    show (2 : ℤ) - 2 = 0 by norm_num, show (2 : ℤ) - 0 = 2 by norm_num, inf_comm] at h
  exact h

theorem false_of_le_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (h : t.IsMaxArc 0 6) (h₀ : t.IsFixRadius 0 3)
    (h22 : ∀ y ∈ t.Gv 1, y ∉ t.Gv 0 →
      t.Qv 0 ⊓ (t.Qv 0).map (MulAut.conj y).toMonoidHom = t.Qv 0 ⊓ t.Qv 2)
    (hSz' : ∃ s ∈ S, ∃ s' ∈ S, ⁅s, s'⁆ ∉ t.Qv 0)
    (hZ0 : t.Zv 0 ≤ t.Zv (-1) ⊓ t.Zv 1)
    (hQZ : ∀ q ∈ t.Qv 0, ∀ z ∈ t.Zv (-1), ⁅q, z⁆ ∈ t.Zv 0)
    (hD : S ≤ (t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0) : False := by
  obtain ⟨z, hz, hz1'⟩ := (t.Zv 4).bot_or_exists_ne_one.resolve_left (t.Zv_ne_bot hfr.hF 4)
  have hz1 : z ∈ t.Gv 1 := (t.r65k_Zv_four_le h₀).trans (win_le_qv (by norm_num) (by norm_num)) hz
  have hz2 : z ∈ t.Qv 2 := t.r65l_Zv_four_le_Qv_two hfr h₀ hz
  have hz0 : z ∉ t.Gv 0 := fun h0 => hz1' (mem_bot.mp
    ((t.r65k_Zv_four_inf_Gv_zero hfr h h₀).le (mem_inf.mpr ⟨hz, h0⟩)))
  have hzz : z * z = 1 := by
    rw [t.Zv_eq 4] at hz
    rw [← sq]
    exact A4.sq_eq_one_of_mem_omegaOneCenterOf hz
  have hzc : ∀ q ∈ t.Qv 2, ⁅q, z⁆ ∈ t.Qv 0 ⊓ t.Qv 2 := fun q hq =>
    t.r65k_Zv_two_le_E hfr h₀
      (t.r65k_comm_Qv_two_Zv_three hQZ hq (t.r65k_Zv_four_le_Zv_three hZ0 hz))
  have hA : t.Qv 0 ⊓ t.Qv 1 ≤ normalizer (t.Qv 2 : Set G) := fun y hy =>
    t.Gv_le_normalizer_Qv 2 ((t.r65l_Qv_one_le hfr).2 (mem_inf.mp hy).2)
  have hAA : ∀ y₁ ∈ t.Qv 0 ⊓ t.Qv 1, ∀ y₂ ∈ t.Qv 0 ⊓ t.Qv 1, ⁅y₁, y₂⁆ ∈ t.Qv 2 :=
    fun y₁ hy₁ y₂ hy₂ =>
      (mem_inf.mp (t.r65l_commutator_D_zero hfr h22 hz1 hz2 hz0 hzz hzc hy₁ hy₂)).2
  obtain ⟨s, hs, s', hs', hss⟩ := hSz'
  have hmem : ∀ u ∈ S, t.x₂ * u * t.x₂⁻¹ ∈ (t.Qv 0 ⊓ t.Qv 1) ⊔ t.Qv 2 := fun u hu =>
    t.r65l_map_S_le hD (by rw [mem_map_conj_iff]; convert hu using 1; group)
  have hc := (t.r65l_mem_Qv_iff 2).mp
    (r65l_commutator_mem_sup hA hAA (hmem s hs) (hmem s' hs'))
  have e : t.x₂⁻¹ * ⁅t.x₂ * s * t.x₂⁻¹, t.x₂ * s' * t.x₂⁻¹⁆ * t.x₂ = ⁅s, s'⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, show (2 : ℤ) - 2 = 0 by norm_num] at hc
  exact hss hc

theorem Zv_zero_eq_commutator {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h : t.IsMaxArc 0 6) {b : ℕ} (h₀ : t.IsFixRadius 0 b)
    (h₁ : t.IsFixRadius 1 2) (hle : ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Zv (-1) ⊓ t.Zv 1)
    (hne : ⁅t.Zv (-1), t.Zv 1⁆ ≠ ⊥) :
    t.Zv 0 = ⁅t.Zv (-1), t.Zv 1⁆ ∧ t.Lv 0 ≤ centralizer (t.Zv 0 : Set G) ∧ b = 3 :=
  t.r65d_core hfr h h₀ h₁ (t.commutator_le_Zv_zero_and_Lv_le_centralizer hfr h₁ hle)
    (t.Zv_zero_le_Qv_one_of_commutator_ne_bot hfr h₀ h₁ hne)
    (t.pCoreOf_Gw_eq_commutator hfr h h₁ hle hne)

private theorem r65m_Qv_le_S {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {i : ℤ} (hi : i = 0 ∨ i = 1) : t.Qv i ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw : t.Qv i ≤ t.Gw 0 1 := by
    intro x hx
    refine mem_win_iff.mpr fun j h1 h2 => ?_
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rcases hi with rfl | rfl
      · exact t.Qv_le_Gv_self 0 hx
      · have := (t.Qv_le_Gv hfr 1).1 hx
        simpa using this
    · rcases hi with rfl | rfl
      · have := (t.Qv_le_Gv hfr 0).2 hx
        simpa using this
      · exact t.Qv_le_Gv_self 1 hx
  have := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) (t.isPGroup_Qv i) hw
  rwa [t.pCoreOf_Gw_zero_one hfr] at this

private theorem r65m_mem_normalizer_X {g : G} (h0 : g ∈ normalizer (t.Qv 0 : Set G))
    (h1 : g ∈ normalizer (t.Qv 1 : Set G)) (h2 : g ∈ normalizer (t.Qv 2 : Set G)) :
    g ∈ normalizer (((t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0 : Subgroup G) : Set G) := by
  have h12 := A4.mem_normalizer_inf h1 h2
  have hle : Subgroup.zpowers g ≤ normalizer (((t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0 : Subgroup G) : Set G) :=
    F1.le_normalizer_sup ((Subgroup.zpowers_le).mpr h12) ((Subgroup.zpowers_le).mpr h0)
  exact hle (Subgroup.mem_zpowers g)

private theorem r65m_base {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (h : t.IsMaxArc 0 6) {b : ℕ} (h₀ : t.IsFixRadius 0 b) (h₁ : t.IsFixRadius 1 2)
    (hle : ⁅t.Zv (-1), t.Zv 1⁆ ≤ t.Zv (-1) ⊓ t.Zv 1) (hne : ⁅t.Zv (-1), t.Zv 1⁆ ≠ ⊥) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZ0eq, hZ0L, rfl⟩ := t.Zv_zero_eq_commutator hfr h h₀ h₁ hle hne
  have hcard0 : Nat.card (t.Zv 0) = 2 ^ f := by
    rw [hZ0eq]
    exact (t.pCoreOf_Gw_eq_commutator hfr h h₁ hle hne).2
  have hZ0 : t.Zv 0 ≤ t.Zv (-1) ⊓ t.Zv 1 := hZ0eq ▸ hle
  have hC0 := t.Zv_one_inf_centralizer_eq_bot_of_Lv_zero hfr hZ0L
  have hZ1w : t.Zv 1 ≤ t.Gw (1 - ((2 : ℕ) : ℤ)) (1 + ((2 : ℕ) : ℤ)) := by
    have := h₁.le_Gw
    simpa using this
  have hZ1n : ¬ t.Zv 1 ≤ t.Gv (2 + ((2 : ℕ) : ℤ)) := by
    have := h₁.not_le_Gv
    rwa [show (1 : ℤ) + ((2 : ℕ) : ℤ) + 1 = 2 + ((2 : ℕ) : ℤ) by norm_num] at this
  obtain ⟨-, hcardA, hN1, -, -⟩ := t.natural_Zv_one hfr (b₀ := 2) even_two hZ1w hZ1n hC0
  have hQZ := t.commutator_Qv_zero_Zv_neg_one_le hfr hZ0 hZ0L hcard0 hN1 hcardA
  have hE := t.Lv_one_le_normalizer_Qv_zero_inf_Qv_two hfr h₀ h₁ hZ0 hQZ
  obtain ⟨-, h22⟩ := t.Qv_zero_inf_map_eq hfr hE
  obtain ⟨hSz, hSz'⟩ := t.commutator_mem_rootOmega_zero_and_exists_not_mem hfr
  have hL1 := t.not_Qv_one_inf_Qv_two_le_Qv_zero hfr h
  set X : Subgroup G := (t.Qv 1 ⊓ t.Qv 2) ⊔ t.Qv 0 with hX
  have hQ0S := t.r65m_Qv_le_S hfr (Or.inl rfl)
  have hQ1S := t.r65m_Qv_le_S hfr (Or.inr rfl)
  have hXS : X ≤ S := sup_le (inf_le_left.trans hQ1S) hQ0S
  have hKX : t.K ≤ normalizer (X : Set G) := fun k hk =>
    t.r65m_mem_normalizer_X (t.Gv_le_normalizer_Qv 0 (t.K_le_Gv 0 hk))
      (t.Gv_le_normalizer_Qv 1 (t.K_le_Gv 1 hk)) (t.Gv_le_normalizer_Qv 2 (t.K_le_Gv 2 hk))
  have hSX : S ≤ normalizer (X : Set G) := by
    have hr : t.IsFixRadius (-1) 2 := by
      have := Track.IsFixRadius.shift t h₁ (-1)
      simpa using this
    have hYw : t.Zv (-1) ≤ t.Gw (-3) 1 := by
      have := hr.le_Gw
      simpa using this
    have hYS : t.Zv (-1) ≤ S := by
      have h01 : t.Zv (-1) ≤ t.Gw 0 1 := hYw.trans (win_mono (by norm_num) le_rfl)
      have := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) (t.isPGroup_Zv (-1)) h01
      rwa [t.pCoreOf_Gw_zero_one hfr] at this
    have hYD : t.D2 ≤ normalizer (t.Zv (-1) : Set G) :=
      ((le_sup_right : t.D2 ≤ t.K).trans (t.K_le_Gv (-1))).trans (t.Gv_le_normalizer_Zv (-1))
    have hYQ : ¬ t.Zv (-1) ≤ t.Qv 1 := fun hle' => by
      have h2 := (t.Qv_le_Gv hfr 1).2
      have h3 := hr.not_le_Gv
      rw [show (-1 : ℤ) + ((2 : ℕ) : ℤ) + 1 = 1 + 1 by norm_num] at h3
      exact h3 (hle'.trans h2)
    have hS := t.S_le_sup_Qv_one_of_torus hfr hYS hYD hYQ
    have hYQ0 : t.Zv (-1) ≤ t.Qv 0 :=
      t.le_Qv_of_le_Gw hfr (u := -3) (w := 1) (j := 0) (by norm_num) (by norm_num)
        (t.isPGroup_Zv (-1)) hYw
    refine hS.trans (sup_le (hYQ0.trans ?_) ?_)
    · exact (le_sup_right : t.Qv 0 ≤ X).trans (Subgroup.le_normalizer)
    · intro q hq
      exact t.r65m_mem_normalizer_X
        ((t.Gv_le_normalizer_Qv 0) ((t.Qv_le_Gv hfr 1).1 (by simpa using hq)))
        (t.Gv_le_normalizer_Qv 1 (t.Qv_le_Gv_self 1 hq))
        ((t.Gv_le_normalizer_Qv 2) (by simpa using (t.Qv_le_Gv hfr 1).2 hq))
  rcases t.trichotomy_Qv_zero hfr hXS hSX hKX with h1 | ⟨h2a, h2b⟩ | h3
  · exact hL1 (le_sup_left.trans h1)
  · have hD : X = t.rootOmega 0 := by
      apply le_antisymm
      · intro x hx
        refine (t.mem_rootOmega_iff hfr 0).mpr ⟨?_, ?_⟩
        · rw [zero_add, t.pCoreOf_Gw_zero_one hfr]
          exact hXS hx
        · rw [pow_two]
          exact h2a x hx
      · intro x hx
        obtain ⟨hxS, hx2⟩ := (t.mem_rootOmega_iff hfr 0).mp hx
        rw [zero_add, t.pCoreOf_Gw_zero_one hfr] at hxS
        have := h2b x hxS (by rwa [pow_two] at hx2)
        rwa [sup_eq_left.mpr (le_sup_right : t.Qv 0 ≤ X)] at this
    exact t.false_of_sup_eq_rootOmega hfr h h₀ h₁ h22 hSz hSz' hZ0 hQZ hD
  · rw [sup_eq_left.mpr (le_sup_right : t.Qv 0 ≤ X)] at h3
    exact t.false_of_le_sup hfr h h₀ h22 hSz' hZ0 hQZ h3

theorem IsMaxArc.false_of_eq_six {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {b₀ : ℕ} (hε : Even ε) (h : t.IsMaxArc ε 6)
    (h₀ : t.IsFixRadius ε b₀) (h₁ : t.IsFixRadius (ε + 1) 2)
    (hle : ⁅t.Zv (ε + 1), t.Zv (ε + 3)⁆ ≤ t.Zv (ε + 1) ⊓ t.Zv (ε + 3))
    (hne : ⁅t.Zv (ε + 1), t.Zv (ε + 3)⁆ ≠ ⊥) : False := by
  obtain ⟨j, rfl⟩ := hε
  have h' : t.IsMaxArc 0 6 := by
    have := Track.IsMaxArc.shift t h (-j)
    rwa [show j + j + 2 * -j = 0 by ring] at this
  have h₀' : t.IsFixRadius 0 b₀ := by
    have := Track.IsFixRadius.shift t h₀ (-j)
    rwa [show j + j + 2 * -j = 0 by ring] at this
  have h₁' : t.IsFixRadius 1 2 := by
    have := Track.IsFixRadius.shift t h₁ (-j)
    rwa [show j + j + 1 + 2 * -j = 1 by ring] at this
  have hm1 : (t.Zv (j + j + 1)).map (MulAut.conj ((t.x₂ * t.x₁) ^ (-(j + 1)))).toMonoidHom =
      t.Zv (-1) := by
    rw [map_qv_tau_pow]
    congr 1
    ring
  have hm3 : (t.Zv (j + j + 3)).map (MulAut.conj ((t.x₂ * t.x₁) ^ (-(j + 1)))).toMonoidHom =
      t.Zv 1 := by
    rw [map_qv_tau_pow]
    congr 1
    ring
  have hinj := (MulAut.conj ((t.x₂ * t.x₁) ^ (-(j + 1)))).injective
  refine t.r65m_base hfr h' h₀' h₁' ?_ ?_
  · rw [← hm1, ← hm3, ← Subgroup.map_commutator, ← Subgroup.map_inf_eq _ _ _ hinj]
    exact Subgroup.map_mono hle
  · rw [← hm1, ← hm3, ← Subgroup.map_commutator]
    intro h0
    exact hne ((Subgroup.map_eq_bot_iff_of_injective _ hinj).mp h0)

end Track

end CFSG.Quasithin.Stroth.Rq
