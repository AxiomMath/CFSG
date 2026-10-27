module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackBasic
import CFSG.Quasithin.Recognition.Stroth.Str83RqTorus
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexL2
import CFSG.Quasithin.Recognition.Stroth.Str83RqTools
import CFSG.Quasithin.Recognition.Stroth.Str83RqSzModule
import CFSG.Quasithin.Recognition.Stroth.Str83RqRoot
import CFSG.Quasithin.Recognition.St84.Gen.L2SecFaithful
import CFSG.Quasithin.Recognition.Stroth.BenderSylow
import CFSG.Quasithin.Recognition.Stroth.F112Tree

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem t6r_conj_mem {N : Subgroup G} {g n : G} (hg : g ∈ normalizer (N : Set G))
    (hn : n ∈ N) : g * n * g⁻¹ ∈ N :=
  (mem_normalizer_iff.mp hg n).mp hn

private theorem t6r_relIndex_ne_zero (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem D2_le_K : t.D2 ≤ t.K := le_sup_right

private theorem D2_le_Gv (i : ℤ) : t.D2 ≤ t.Gv i := t.D2_le_K.trans (t.K_le_Gv i)

private theorem Q2_le_S (hF : F112HypW L1 L2 S) : Q2 L1 L2 S ≤ S :=
  F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF)

private theorem Q1_le_S (hF : F112HypW L1 L2 S) : Q1 L1 L2 S ≤ S :=
  F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)

private theorem S_le_Gw_zero_one (hF : F112HypW L1 L2 S) :
    S ≤ t.Gw 0 1 := by
  rw [t.Gw_zero_one hF]
  exact le_sup_right

private theorem Qv_one_le_Gv_two {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.Qv 1 ≤ t.Gv 2 := by
  have hX : t.Qv 1 ≤ t.Gw (1 - 1) 1 := by
    rw [show (1 : ℤ) - 1 = 0 by norm_num, t.Qv_one]
    exact (Q2_le_S hfr.hF).trans (t.S_le_Gw_zero_one hfr.hF)
  have h := (t.inf_Gv_eq_inf_Qv hfr 1 (t.isPGroup_Qv 1)).1 hX
  rw [inf_idem] at h
  have h2 := inf_eq_left.mp h
  rwa [show (1 : ℤ) + 1 = 2 by norm_num] at h2

theorem card_le_mul_card_inf_Gv_add_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXw : X ≤ t.Gw (v - 1) v) :
    Nat.card X ≤ (if Even v then (2 ^ (2 * a + 1)) ^ 2 else 2 ^ f) *
      Nat.card ↥(X ⊓ t.Gv (v + 1)) := by
  have h1 := (t.inf_Gv_eq_inf_Qv hfr v hX).1 hXw
  have h2 := t.relIndex_Qv_le hfr v hX (Or.inl hXw)
  have h3 := Subgroup.relIndex_mul_card (t.Qv v) X
  rw [inf_comm, ← h1] at h3
  rw [← h3]
  exact Nat.mul_le_mul_right _ h2

theorem card_le_mul_card_inf_Gv_sub_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXw : X ≤ t.Gw v (v + 1)) :
    Nat.card X ≤ (if Even v then (2 ^ (2 * a + 1)) ^ 2 else 2 ^ f) *
      Nat.card ↥(X ⊓ t.Gv (v - 1)) := by
  have h1 := (t.inf_Gv_eq_inf_Qv hfr v hX).2 hXw
  have h2 := t.relIndex_Qv_le hfr v hX (Or.inr hXw)
  have h3 := Subgroup.relIndex_mul_card (t.Qv v) X
  rw [inf_comm, ← h1] at h3
  rw [← h3]
  exact Nat.mul_le_mul_right _ h2

private theorem tl_map_conj_eq_of_mem {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  rw [mem_map_conj_iff]
  have := mem_normalizer_iff.mp (inv_mem hg) y
  rw [inv_inv] at this
  exact this.symm

private theorem tl_mem_normalizer_sup {H K : Subgroup G} {g : G}
    (hH : g ∈ normalizer (H : Set G)) (hK : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  F1.le_normalizer_sup (X := Subgroup.zpowers g) (zpowers_le.mpr hH) (zpowers_le.mpr hK)
    (mem_zpowers g)

private theorem tl_pCoreOf_le_Qv_one (hF : Hyp111 L1 L2 S) : pCoreOf 2 L2 ≤ t.Qv 1 := by
  have h := Hyp111.pCoreOf_le_pCoreOf_vertex hF.symm
  rw [bigB_comm] at h
  rw [t.Qv_one]
  exact h

private theorem tl_P2_le_normalizer_L2 (hF : Hyp111 L1 L2 S) :
    P2 L1 L2 S ≤ normalizer (L2 : Set G) := by
  have h := bigB_le_normalizer_of_hyp111 hF.symm
  rw [bigB_comm] at h
  exact sup_le le_normalizer h

private theorem tl_D2_le_normalizer_T : t.D2 ≤ normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
  t.hD2hall.1.trans inf_le_right

private theorem tl_T_le_normalizer_Qv_one : S ⊓ L2 ≤ normalizer (t.Qv 1 : Set G) := by
  have h : P2 L1 L2 S ≤ normalizer (t.Qv 1 : Set G) := by
    rw [← t.Gv_one]
    exact t.Gv_le_normalizer_Qv 1
  exact inf_le_right.trans (le_sup_left.trans h)

private theorem tl_S_eq_sup_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : S = t.Qv 1 ⊔ (S ⊓ L2) := by
  have h := eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN
    (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))
  rw [sup_comm] at h
  rw [t.Qv_one]
  exact h

private theorem tl_ne_conj_x₂ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    S ⊓ L2 ≠ (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf (S ⊓ L2) L2 := hfr.hF.1.h2.sylow
  have hSQ : S = t.Qv 1 ⊔ (S ⊓ L2) := t.tl_S_eq_sup_Qv_one hfr
  intro heq
  have hTG01 : S ⊓ L2 ≤ t.Gw 0 1 := inf_le_left.trans (t.S_le_Gw_zero_one hfr.hF)
  have hT'G12 : (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom ≤ t.Gw 1 2 := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hTG01
    have e := t.track.map_win_x₂ (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      Subgroup.le_normalizer Subgroup.le_normalizer 0 1
    rw [show (2 : ℤ) - 1 = 1 by norm_num, show (2 : ℤ) - 0 = 2 by norm_num] at e
    exact h.trans e.le
  have hTG02 : S ⊓ L2 ≤ t.Gw 0 2 := by
    intro y hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i ≤ 1 ∨ i = 2 by omega) with h3 | rfl
    · exact mem_win_iff.mp (hTG01 hy) i h1 h3
    · have hy' : y ∈ (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom := heq ▸ hy
      exact mem_win_iff.mp (hT'G12 hy') 2 (by norm_num) le_rfl
  have hTQ : S ⊓ L2 ≤ t.Qv 1 :=
    t.le_Qv_of_le_Gw hfr (u := 0) (w := 2) (j := 1) (by norm_num) (by norm_num)
      hTsyl.2.1 hTG02
  have hSle : S ≤ t.Qv 1 := hSQ.le.trans (sup_le le_rfl hTQ)
  have hQS : (t.Qv 1).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hSle
  have h9 := (t.relIndex_Qv_pCoreOf hfr 1).1
  rw [sub_self, t.pCoreOf_Gw_zero_one hfr, if_neg Int.not_even_one, hQS] at h9
  have h4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
  omega

theorem S_le_sup_Qv_one_of_torus {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {Y : Subgroup G} (hYS : Y ≤ S)
    (hYD : t.D2 ≤ normalizer (Y : Set G)) (hYQ : ¬ Y ≤ t.Qv 1) :
    S ≤ Y ⊔ t.Qv 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf (S ⊓ L2) L2 := hfr.hF.1.h2.sylow
  have hQ2le : pCoreOf 2 L2 ≤ t.Qv 1 := t.tl_pCoreOf_le_Qv_one hfr.hF.1
  have hTQ' : S ⊓ L2 ≤ normalizer (t.Qv 1 : Set G) := t.tl_T_le_normalizer_Qv_one
  have hSQ : S = t.Qv 1 ⊔ (S ⊓ L2) := t.tl_S_eq_sup_Qv_one hfr
  have hXN : t.D2 ≤ normalizer (((Y ⊔ t.Qv 1) ⊓ (S ⊓ L2) : Subgroup G) : Set G) := by
    intro d hd
    refine A4.mem_normalizer_inf ?_ (t.tl_D2_le_normalizer_T hd)
    exact tl_mem_normalizer_sup (hYD hd)
      ((t.D2_le_Gv 1).trans (t.Gv_le_normalizer_Qv 1) hd)
  have hXnot : ¬ ((Y ⊔ t.Qv 1) ⊓ (S ⊓ L2) ≤ pCoreOf 2 L2) := by
    intro hX
    apply hYQ
    intro y hy
    have hyS : y ∈ t.Qv 1 ⊔ (S ⊓ L2) := hSQ.le (hYS hy)
    obtain ⟨q, hq, τ, hτ, hyqτ⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTQ').mp hyS
    have hτy : τ = q⁻¹ * y := by rw [hyqτ]; group
    have hτX : τ ∈ (Y ⊔ t.Qv 1) ⊓ (S ⊓ L2) := by
      refine ⟨?_, hτ⟩
      rw [hτy]
      exact mul_mem (mem_sup_right (inv_mem hq)) (mem_sup_left hy)
    rw [hyqτ]
    exact mul_mem hq (hQ2le (hX hτX))
  have hKI : S ⊓ L2 ≤ (Y ⊔ t.Qv 1) ⊓ (S ⊓ L2) ⊔ pCoreOf 2 L2 :=
    le_sup_pCoreOf_of_torus_of_l2 hfr.hf hfr.hL2 hTsyl t.hD2hall inf_le_right hXN hXnot
  have hTYQ : S ⊓ L2 ≤ Y ⊔ t.Qv 1 :=
    hKI.trans (sup_le inf_le_left (hQ2le.trans le_sup_right))
  exact hSQ.le.trans (sup_le le_sup_right hTYQ)

theorem L2_le_sup_Qv_one_of_sylow {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {X : Subgroup G} (hT : S ⊓ L2 ≤ X ⊔ t.Qv 1)
    (hx : t.x₂ ∈ normalizer (X : Set G)) :
    L2 ≤ X ⊔ t.Qv 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf (S ⊓ L2) L2 := hfr.hF.1.h2.sylow
  have hQ2le : pCoreOf 2 L2 ≤ t.Qv 1 := t.tl_pCoreOf_le_Qv_one hfr.hF.1
  have hx₂L2 : t.x₂ ∈ normalizer (L2 : Set G) :=
    tl_P2_le_normalizer_L2 hfr.hF.1 t.track.x₂_mem
  have hx₂Q : t.x₂ ∈ normalizer (t.Qv 1 : Set G) := by
    have hx₂ : t.x₂ ∈ t.Gv 1 := by
      rw [t.Gv_one]
      exact t.track.x₂_mem
    exact t.Gv_le_normalizer_Qv 1 hx₂
  have hT'syl : IsSylowTwoOf ((S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom) L2 := by
    have h := IsSylowTwoOf.map_equiv (MulAut.conj t.x₂) hTsyl
    rwa [tl_map_conj_eq_of_mem hx₂L2] at h
  have hT'CQ : (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom ≤ X ⊔ t.Qv 1 := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hT
    rwa [tl_map_conj_eq_of_mem (tl_mem_normalizer_sup hx hx₂Q)] at h
  have h := le_sup_pCoreOf_of_sylow_ne_of_l2 (X := X ⊔ t.Qv 1) hfr.hf hfr.hL2 hTsyl hT'syl
    (t.tl_ne_conj_x₂ hfr) (hT.trans le_sup_left) (hT'CQ.trans le_sup_left)
  exact h.trans (sup_le le_rfl (hQ2le.trans le_sup_right))

private def VZ : Subgroup G := ⨆ g ∈ P1 L1 L2 S, (t.Zv 1).map (MulAut.conj g).toMonoidHom

private theorem le_VZ {g : G} (hg : g ∈ P1 L1 L2 S) :
    (t.Zv 1).map (MulAut.conj g).toMonoidHom ≤ t.VZ :=
  le_iSup₂ (f := fun g (_ : g ∈ P1 L1 L2 S) => (t.Zv 1).map (MulAut.conj g).toMonoidHom) g hg

private theorem t6v_conj_mem {g z : G} (hg : g ∈ P1 L1 L2 S) (hz : z ∈ t.Zv 1) :
    g * z * g⁻¹ ∈ t.VZ :=
  t.le_VZ hg (mem_map_conj_iff.mpr (by simpa [mul_assoc] using hz))

private theorem t6v_VZ_le {K : Subgroup G}
    (h : ∀ g ∈ P1 L1 L2 S, ∀ z ∈ t.Zv 1, g * z * g⁻¹ ∈ K) : t.VZ ≤ K := by
  refine iSup₂_le fun g hg y hy => ?_
  have h1 := h g hg _ (mem_map_conj_iff.mp hy)
  simpa [mul_assoc] using h1

private theorem Zv_one_le_VZ : t.Zv 1 ≤ t.VZ := fun z hz => by
  simpa using t.t6v_conj_mem (one_mem _) hz

private theorem P1_le_normalizer_VZ : P1 L1 L2 S ≤ normalizer (t.VZ : Set G) := by
  have key : ∀ h ∈ P1 L1 L2 S, ∀ y ∈ t.VZ, h * y * h⁻¹ ∈ t.VZ := by
    intro h hh
    have hle : t.VZ ≤ t.VZ.comap (MulAut.conj h).toMonoidHom := by
      refine t.t6v_VZ_le fun g hg z hz => ?_
      have := t.t6v_conj_mem (mul_mem hh hg) hz
      simpa [mul_assoc] using this
    exact fun y hy => hle hy
  intro h hh
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key h hh y, fun hy => ?_⟩
  have := key h⁻¹ (inv_mem hh) _ hy
  simpa [mul_assoc] using this

private theorem VZ_le_Qv_zero {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) : t.VZ ≤ t.Qv 0 := by
  have hZQ : t.Zv 1 ≤ t.Qv 0 :=
    t.le_Qv_of_le_Gw hfr (u := -1) (w := 3) (j := 0) (by norm_num) (by norm_num)
      (t.isPGroup_Zv 1) hZ0
  refine t.t6v_VZ_le fun g hg z hz => ?_
  have hgN : g ∈ normalizer (t.Qv 0 : Set G) :=
    t.Gv_le_normalizer_Qv 0 (by rw [t.Gv_zero]; exact hg)
  exact (mem_normalizer_iff.mp hgN z).mp (hZQ hz)

private theorem t6v_P1_le_normalizer_Zv_zero :
    P1 L1 L2 S ≤ normalizer (t.Zv 0 : Set G) := by
  rw [t.Zv_zero]
  exact (le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)

private theorem t6v_VZ_le_normalizer_Zv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) :
    t.VZ ≤ normalizer (t.Zv 0 : Set G) :=
  ((t.VZ_le_Qv_zero hfr hZ0).trans (by rw [t.Qv_zero]; exact pCoreOf_le 2 _)).trans
    t.t6v_P1_le_normalizer_Zv_zero

private def t6v_commSub (N Z : Subgroup G) (hN : N ≤ normalizer (Z : Set G)) (p : G) :
    Subgroup G where
  carrier := {v | v ∈ N ∧ ⁅p, v⁆ ∈ Z}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro v w ⟨hv, hvZ⟩ ⟨hw, hwZ⟩
    refine ⟨mul_mem hv hw, ?_⟩
    have e : ⁅p, v * w⁆ = ⁅p, v⁆ * (v * ⁅p, w⁆ * v⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem hvZ ((mem_normalizer_iff.mp (hN hv) _).mp hwZ)
  inv_mem' := by
    rintro v ⟨hv, hvZ⟩
    refine ⟨inv_mem hv, ?_⟩
    have e : ⁅p, v⁻¹⁆ = v⁻¹ * ⁅p, v⁆⁻¹ * v := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := (mem_normalizer_iff.mp (hN (inv_mem hv)) _).mp (inv_mem hvZ)
    simpa using this

private theorem commutator_mem_Zv_zero_of_mem_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3)
    (hN1 : ∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 0) :
    ∀ p ∈ t.Qv 0, ∀ v ∈ t.VZ, ⁅p, v⁆ ∈ t.Zv 0 := by
  intro p hp
  have hle : t.VZ ≤ t6v_commSub t.VZ (t.Zv 0) (t.t6v_VZ_le_normalizer_Zv_zero hfr hZ0) p := by
    refine t.t6v_VZ_le fun g hg z hz => ⟨t.t6v_conj_mem hg hz, ?_⟩
    have hgN : g⁻¹ ∈ normalizer (t.Qv 0 : Set G) :=
      t.Gv_le_normalizer_Qv 0 (by rw [t.Gv_zero]; exact inv_mem hg)
    have hpS : g⁻¹ * p * g ∈ S := by
      have h := (mem_normalizer_iff.mp hgN p).mp hp
      rw [inv_inv] at h
      have h' : g⁻¹ * p * g ∈ Q1 L1 L2 S := by rw [← t.Qv_zero]; exact h
      exact Q1_le_S hfr.hF h'
    have key := hN1 _ hpS z hz
    have e : ⁅p, g * z * g⁻¹⁆ = g * (g⁻¹ * p * g * z * (g⁻¹ * p * g)⁻¹ * z⁻¹) * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (mem_normalizer_iff.mp (t.t6v_P1_le_normalizer_Zv_zero hg) _).mp key
  intro v hv
  exact (hle hv).2

private theorem t6v_sq_conj_eq_one {g z : G} (hz : z ∈ t.Zv 1) : (g * z * g⁻¹) ^ 2 = 1 := by
  rw [t.Zv_eq 1] at hz
  rw [conj_pow, A4.sq_eq_one_of_mem_omegaOneCenterOf hz]
  simp

private theorem isElemSec_VZ {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) (hZ10 : t.Zv 0 ≤ t.Zv 1)
    (hN1 : ∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 0) :
    CFSG.GH74.QTGen4.DSGen4.IsElemSec (t.Zv 0) t.VZ := by
  have hcomm : ∀ v ∈ t.VZ, ∀ w ∈ t.VZ, ⁅v, w⁆ ∈ t.Zv 0 := fun v hv w hw =>
    t.commutator_mem_Zv_zero_of_mem_Qv_zero hfr hZ0 hN1 v (t.VZ_le_Qv_zero hfr hZ0 hv) w hw
  unfold CFSG.GH74.QTGen4.DSGen4.IsElemSec
  refine ⟨hZ10.trans t.Zv_one_le_VZ, Subgroup.commutator_le.mpr hcomm, ?_⟩
  let K : Subgroup G :=
    { carrier := {v | v ∈ t.VZ ∧ v ^ 2 ∈ t.Zv 0}
      one_mem' := ⟨one_mem _, by simpa using one_mem (t.Zv 0)⟩
      mul_mem' := by
        rintro v w ⟨hv, hv2⟩ ⟨hw, hw2⟩
        refine ⟨mul_mem hv hw, ?_⟩
        have e : (v * w) ^ 2 = v ^ 2 * ⁅v⁻¹, w⁆ * w ^ 2 := by
          simp only [commutatorElement_def, pow_two]; group
        rw [e]
        exact mul_mem (mul_mem hv2 (hcomm _ (inv_mem hv) _ hw)) hw2
      inv_mem' := by
        rintro v ⟨hv, hv2⟩
        refine ⟨inv_mem hv, ?_⟩
        rw [inv_pow]
        exact inv_mem hv2 }
  have hle : t.VZ ≤ K := t.t6v_VZ_le fun g hg z hz =>
    ⟨t.t6v_conj_mem hg hz, by rw [t.t6v_sq_conj_eq_one hz]; exact one_mem _⟩
  exact fun e he => (hle he).2

private theorem t6v_P2_le_normalizer_Z2 : P2 L1 L2 S ≤ normalizer (Z2 L1 L2 S : Set G) :=
  (le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)

private theorem exists_not_commutator_mem_VZ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZ10 : t.Zv 0 ≤ t.Zv 1)
    (hcard0 : Nat.card (t.Zv 1) = 2 ^ f * 2 ^ f) :
    ∃ l ∈ L1, ∃ v ∈ t.VZ, ⁅l, v⁆ ∉ t.Zv 0 := by
  by_contra hcon
  push Not at hcon
  have hL1 : ∀ l ∈ L1, ∀ z ∈ t.Zv 1, l * z * l⁻¹ ∈ t.Zv 1 := by
    intro l hl z hz
    have h1 := hcon l hl z (t.Zv_one_le_VZ hz)
    have h2 : l * z * l⁻¹ = ⁅l, z⁆ * z := by
      simp only [commutatorElement_def]; group
    rw [h2]
    exact mul_mem (hZ10 h1) hz
  have hL1N : L1 ≤ normalizer (Z2 L1 L2 S : Set G) := by
    rw [← t.Zv_one]
    intro l hl
    rw [mem_normalizer_iff]
    intro z
    refine ⟨hL1 l hl z, fun hz => ?_⟩
    have := hL1 l⁻¹ (inv_mem hl) _ hz
    simpa [mul_assoc] using this
  have hbot : Z2 L1 L2 S = ⊥ := by
    refine eq_bot_of_le_bigB hfr.hF.1 (X := Z2 L1 L2 S) ?_ ?_ ?_
    · exact (A4.omegaOneCenterOf_le _).trans ((Q2_le_S hfr.hF).trans le_sup_right)
    · exact le_sup_of_le_left (le_inf le_sup_left hL1N)
    · exact le_sup_of_le_left (le_inf le_sup_left (le_sup_left.trans t6v_P2_le_normalizer_Z2))
  have h1 : Nat.card (t.Zv 1) = 1 := by
    rw [t.Zv_one, hbot]
    exact Subgroup.card_bot
  have h4 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
  have := Nat.mul_le_mul h4 h4
  omega

private theorem two_pow_le_relIndex_VZ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) (hZ10 : t.Zv 0 ≤ t.Zv 1)
    (hcard0 : Nat.card (t.Zv 1) = 2 ^ f * 2 ^ f)
    (hN1 : ∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 0) :
    2 ^ (4 * (2 * a + 1)) ≤ (t.Zv 0).relIndex t.VZ := by
  have hL : L1 ≤ normalizer (t.VZ : Set G) ⊓ normalizer (t.Zv 0 : Set G) :=
    le_inf (le_sup_left.trans t.P1_le_normalizer_VZ)
      (le_sup_left.trans t.t6v_P1_le_normalizer_Zv_zero)
  have hQ : ∀ p ∈ pCoreOf 2 L1, ∀ v ∈ t.VZ, ⁅p, v⁆ ∈ t.Zv 0 := fun p hp v hv =>
    t.commutator_mem_Zv_zero_of_mem_Qv_zero hfr hZ0 hN1 p
      (by rw [t.Qv_zero]; exact Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1 hp) v hv
  exact CFSG.Quasithin.Stroth.two_pow_le_relIndex_of_nontrivial_of_sz hfr.ha hfr.hSz
    (t.isElemSec_VZ hfr hZ0 hZ10 hN1) hL hQ (t.exists_not_commutator_mem_VZ hfr hZ10 hcard0)

private theorem t6o_ext_right {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {u v v' : ℤ} (huv : u < v) (hv' : v' = v + 1)
    {X : Subgroup G} (hX : IsPGroup 2 X) (hXw : X ≤ t.Gw u v) :
    Nat.card X ≤ (if Even v then (2 ^ (2 * a + 1)) ^ 2 else 2 ^ f) * Nat.card ↥(X ⊓ t.Gv v') ∧
      X ⊓ t.Gv v' ≤ t.Gw u v' := by
  subst hv'
  refine ⟨t.card_le_mul_card_inf_Gv_add_one hfr v hX
    (hXw.trans (win_mono (by omega) le_rfl)), ?_⟩
  rw [show t.Gw u (v + 1) = t.Gw u v ⊓ t.Gv (v + 1) from win_add_one_right (by omega)]
  exact inf_le_inf_right _ hXw

private theorem t6o_ext_left {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {u u' w : ℤ} (huw : u < w) (hu' : u' = u - 1)
    {X : Subgroup G} (hX : IsPGroup 2 X) (hXw : X ≤ t.Gw u w) :
    Nat.card X ≤ (if Even u then (2 ^ (2 * a + 1)) ^ 2 else 2 ^ f) * Nat.card ↥(X ⊓ t.Gv u') ∧
      X ⊓ t.Gv u' ≤ t.Gw u' w := by
  subst hu'
  refine ⟨t.card_le_mul_card_inf_Gv_sub_one hfr u hX
    (hXw.trans (win_mono le_rfl (by omega))), ?_⟩
  rw [show t.Gw (u - 1) w = t.Gv (u - 1) ⊓ t.Gw u w from win_sub_one_left (by omega), inf_comm]
  exact inf_le_inf_left _ hXw

private theorem t6o_Qv_le_Gw {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) {u w : ℤ} (hu : u = v - 1) (hw : w = v + 1) :
    t.Qv v ≤ t.Gw u w := by
  subst hu hw
  intro y hy
  refine mem_win_iff.mpr fun i h1 h2 => ?_
  rcases (show i = v - 1 ∨ i = v ∨ i = v + 1 by omega) with rfl | rfl | rfl
  · exact (t.Qv_le_Gv hfr v).1 hy
  · exact t.Qv_le_Gv_self _ hy
  · exact (t.Qv_le_Gv hfr v).2 hy

private theorem t6o_mem_Gw_union {u m w : ℤ} {y : G} (h1 : y ∈ t.Gw u m) (h2 : y ∈ t.Gw m w) :
    y ∈ t.Gw u w := by
  refine mem_win_iff.mpr fun i hi1 hi2 => ?_
  rcases le_total i m with h | h
  · exact mem_win_iff.mp h1 i hi1 h
  · exact mem_win_iff.mp h2 i h hi2

private theorem card_S_le_of_t6 {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hwlog : pCoreOf 2 (t.Gw (-2) 4) = ⊥) :
    Nat.card S ≤ (2 ^ f) ^ 3 * ((2 ^ (2 * a + 1)) ^ 2) ^ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 S := by
    have h := pCoreOf_isPGroup 2 (t.Gw 0 1)
    rwa [t.pCoreOf_Gw_zero_one hfr] at h
  have hS01 : S ≤ t.Gw 0 1 := t.S_le_Gw_zero_one hfr.hF
  obtain ⟨c1, w1⟩ := t.t6o_ext_left hfr (u := 0) (u' := -1) (w := 1) (by norm_num)
    (by norm_num) hSp hS01
  have hp1 : IsPGroup 2 ↥(S ⊓ t.Gv (-1)) := hSp.to_le inf_le_left
  obtain ⟨c2, w2⟩ := t.t6o_ext_right hfr (u := -1) (v := 1) (v' := 2) (by norm_num)
    (by norm_num) hp1 w1
  have hp2 : IsPGroup 2 ↥(S ⊓ t.Gv (-1) ⊓ t.Gv 2) := hp1.to_le inf_le_left
  obtain ⟨c3, w3⟩ := t.t6o_ext_left hfr (u := -1) (u' := -2) (w := 2) (by norm_num)
    (by norm_num) hp2 w2
  have hp3 : IsPGroup 2 ↥(S ⊓ t.Gv (-1) ⊓ t.Gv 2 ⊓ t.Gv (-2)) := hp2.to_le inf_le_left
  obtain ⟨c4, w4⟩ := t.t6o_ext_right hfr (u := -2) (v := 2) (v' := 3) (by norm_num)
    (by norm_num) hp3 w3
  have hp4 : IsPGroup 2 ↥(S ⊓ t.Gv (-1) ⊓ t.Gv 2 ⊓ t.Gv (-2) ⊓ t.Gv 3) :=
    hp3.to_le inf_le_left
  obtain ⟨c5, w5⟩ := t.t6o_ext_right hfr (u := -2) (v := 3) (v' := 4) (by norm_num)
    (by norm_num) hp4 w4
  have hp5 : IsPGroup 2 ↥(S ⊓ t.Gv (-1) ⊓ t.Gv 2 ⊓ t.Gv (-2) ⊓ t.Gv 3 ⊓ t.Gv 4) :=
    hp4.to_le inf_le_left
  have hbot : S ⊓ t.Gv (-1) ⊓ t.Gv 2 ⊓ t.Gv (-2) ⊓ t.Gv 3 ⊓ t.Gv 4 = ⊥ := by
    have h := t.le_pCoreOf_Gw hfr (show (-2 : ℤ) < 4 by norm_num) hp5 w5
    rw [hwlog] at h
    exact le_bot_iff.mp h
  rw [hbot, Subgroup.card_bot] at c5
  rw [if_pos (show Even (0 : ℤ) by decide)] at c1
  rw [if_neg (show ¬ Even (1 : ℤ) by decide)] at c2
  rw [if_neg (show ¬ Even (-1 : ℤ) by decide)] at c3
  rw [if_pos (show Even (2 : ℤ) by decide)] at c4
  rw [if_neg (show ¬ Even (3 : ℤ) by decide)] at c5
  have key : Nat.card S ≤ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ f * (2 ^ f * ((2 ^ (2 * a + 1)) ^ 2 *
      (2 ^ f * 1)))) := by
    refine c1.trans (Nat.mul_le_mul_left _ ?_)
    refine c2.trans (Nat.mul_le_mul_left _ ?_)
    refine c3.trans (Nat.mul_le_mul_left _ ?_)
    refine c4.trans (Nat.mul_le_mul_left _ ?_)
    exact c5
  calc Nat.card S ≤ _ := key
    _ = (2 ^ f) ^ 3 * ((2 ^ (2 * a + 1)) ^ 2) ^ 2 := by ring

private theorem card_Qv_zero_le_of_t6 {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hwlog : pCoreOf 2 (t.Gw (-2) 4) = ⊥) :
    Nat.card (t.Qv 0) ≤ (2 ^ f) ^ 3 * (2 ^ (2 * a + 1)) ^ 2 := by
  have hS := t.card_S_le_of_t6 hfr hwlog
  have h1 := (t.relIndex_Qv_pCoreOf hfr 0).2
  rw [show (0 : ℤ) + 1 = 1 by norm_num, t.pCoreOf_Gw_zero_one hfr,
    if_pos (show Even (0 : ℤ) by decide)] at h1
  have hQS : t.Qv 0 ≤ S := by
    rw [t.Qv_zero]
    exact Q1_le_S hfr.hF
  have h3 := Subgroup.relIndex_mul_card (t.Qv 0) S
  rw [inf_eq_left.mpr hQS, h1] at h3
  have hpos : 0 < (2 ^ (2 * a + 1)) ^ 2 := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc (2 ^ (2 * a + 1)) ^ 2 * Nat.card (t.Qv 0) = Nat.card S := h3
    _ ≤ (2 ^ f) ^ 3 * ((2 ^ (2 * a + 1)) ^ 2) ^ 2 := hS
    _ = (2 ^ (2 * a + 1)) ^ 2 * ((2 ^ f) ^ 3 * (2 ^ (2 * a + 1)) ^ 2) := by ring

private theorem Qv_zero_inf_Qv_two_eq_of_t6 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hwlog : pCoreOf 2 (t.Gw (-2) 4) = ⊥)
    (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) (hcard0 : Nat.card (t.Zv 1) = 2 ^ f * 2 ^ f) :
    t.Qv 0 ⊓ t.Qv 2 = t.Zv 1 := by
  have hXp : IsPGroup 2 ↥(t.Qv 0 ⊓ t.Qv 2) := (t.isPGroup_Qv 0).to_le inf_le_left
  have hXw : t.Qv 0 ⊓ t.Qv 2 ≤ t.Gw (-1) 3 := by
    intro y hy
    exact t.t6o_mem_Gw_union
      (t.t6o_Qv_le_Gw hfr 0 (u := -1) (w := 1) (by norm_num) (by norm_num) hy.1)
      (t.t6o_Qv_le_Gw hfr 2 (u := 1) (w := 3) (by norm_num) (by norm_num) hy.2)
  obtain ⟨c1, w1⟩ := t.t6o_ext_right hfr (u := -1) (v := 3) (v' := 4) (by norm_num)
    (by norm_num) hXp hXw
  have hp1 : IsPGroup 2 ↥(t.Qv 0 ⊓ t.Qv 2 ⊓ t.Gv 4) := hXp.to_le inf_le_left
  obtain ⟨c2, w2⟩ := t.t6o_ext_left hfr (u := -1) (u' := -2) (w := 4) (by norm_num)
    (by norm_num) hp1 w1
  have hp2 : IsPGroup 2 ↥(t.Qv 0 ⊓ t.Qv 2 ⊓ t.Gv 4 ⊓ t.Gv (-2)) := hp1.to_le inf_le_left
  have hbot : t.Qv 0 ⊓ t.Qv 2 ⊓ t.Gv 4 ⊓ t.Gv (-2) = ⊥ := by
    have h := t.le_pCoreOf_Gw hfr (show (-2 : ℤ) < 4 by norm_num) hp2 w2
    rw [hwlog] at h
    exact le_bot_iff.mp h
  rw [hbot, Subgroup.card_bot] at c2
  rw [if_neg (show ¬ Even (3 : ℤ) by decide)] at c1
  rw [if_neg (show ¬ Even (-1 : ℤ) by decide)] at c2
  have hle0 : t.Zv 1 ≤ t.Qv 0 :=
    t.le_Qv_of_le_Gw hfr (u := -1) (w := 3) (j := 0) (by norm_num) (by norm_num)
      (t.isPGroup_Zv 1) hZ0
  have hle2 : t.Zv 1 ≤ t.Qv 2 :=
    t.le_Qv_of_le_Gw hfr (u := -1) (w := 3) (j := 2) (by norm_num) (by norm_num)
      (t.isPGroup_Zv 1) hZ0
  have hcard : Nat.card ↥(t.Qv 0 ⊓ t.Qv 2) ≤ Nat.card (t.Zv 1) := by
    rw [hcard0]
    calc Nat.card ↥(t.Qv 0 ⊓ t.Qv 2) ≤ 2 ^ f * Nat.card ↥(t.Qv 0 ⊓ t.Qv 2 ⊓ t.Gv 4) := c1
      _ ≤ 2 ^ f * (2 ^ f * 1) := Nat.mul_le_mul_left _ c2
      _ = 2 ^ f * 2 ^ f := by rw [mul_one]
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hle0 hle2) hcard).symm

private theorem t6p_P1_le_normalizer_Z1 : P1 L1 L2 S ≤ normalizer (Z1 L1 L2 S : Set G) :=
  (le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)

private theorem t6p_mem_normalizer_of_map_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  have h1 : g * y * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * (g * y * g⁻¹) * g ∈ H :=
    mem_map_conj_iff
  rw [h, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1
  exact h1.symm

private theorem t6p_mem_normalizer_of_map_le {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ normalizer (H : Set G) := by
  apply t6p_mem_normalizer_of_map_eq
  refine Subgroup.eq_of_le_of_card_ge h ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem t6p_conj_mem {H : Subgroup G} {g y : G} (hg : g ∈ normalizer (H : Set G))
    (hy : y ∈ H) : g * y * g⁻¹ ∈ H :=
  (mem_normalizer_iff.mp hg y).mp hy

private theorem t6p_mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [mem_inf, mem_inf, hA x, hB x]

private theorem t6p_mem_normalizer_sup {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

private theorem t6p_Qv_one_le_Gv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 1 ≤ t.Gv 0 := by
  have h := (t.Qv_le_Gv hfr 1).1
  rwa [show (1 : ℤ) - 1 = 0 by norm_num] at h

private theorem t6p_S_le_Gv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : S ≤ t.Gv 1 :=
  (t.S_le_Gw_zero_one hfr.hF).trans (win_le_qv (by norm_num) le_rfl)

private theorem Zv_neg_one_le_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) : t.Zv (-1) ≤ t.Qv 0 := by
  have h1 : t.Zv 1 ≤ t.Qv 0 :=
    t.le_Qv_of_le_Gw hfr (u := -1) (w := 3) (j := 0) (by norm_num) (by norm_num)
      (t.isPGroup_Zv 1) hZ0
  have hZ : (t.Zv 1).map (MulAut.conj t.x₁).toMonoidHom = t.Zv (-1) :=
    t.track.map_qv_x₁ t6p_P1_le_normalizer_Z1 t6v_P2_le_normalizer_Z2 1
  have hQ : (t.Qv 0).map (MulAut.conj t.x₁).toMonoidHom = t.Qv 0 := by
    have := t.track.map_qv_x₁ (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _) 0
    rwa [neg_zero] at this
  exact hZ.symm.le.trans ((Subgroup.map_mono h1).trans hQ.le)

private theorem S_le_Zv_neg_one_sup_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) (hZ2' : ¬ t.Zv (-1) ≤ t.Gv 2) :
    S ≤ t.Zv (-1) ⊔ t.Qv 1 := by
  refine t.S_le_sup_Qv_one_of_torus hfr (Y := t.Zv (-1)) ?_ ?_ ?_
  · have h := t.Zv_neg_one_le_Qv_zero hfr hZ0
    rw [t.Qv_zero] at h
    exact h.trans (Q1_le_S hfr.hF)
  · exact (t.D2_le_Gv (-1)).trans (t.Gv_le_normalizer_Zv (-1))
  · intro h
    exact hZ2' (h.trans (t.Qv_one_le_Gv_two hfr))

private theorem x₂_mem_normalizer_A {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.x₂ ∈ normalizer (((t.Qv 1 ⊓ t.Qv 0) ⊔ (t.Qv 1 ⊓ t.Qv 2) : Subgroup G) : Set G) := by
  clear hfr
  have hmap : ∀ i : ℤ, (t.Qv i).map (MulAut.conj t.x₂).toMonoidHom = t.Qv (2 - i) := fun i =>
    t.track.map_qv_x₂ (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _) i
  have h0 := hmap 0
  have h1 := hmap 1
  have h2 := hmap 2
  rw [show (2 : ℤ) - 0 = 2 by norm_num] at h0
  rw [show (2 : ℤ) - 1 = 1 by norm_num] at h1
  rw [show (2 : ℤ) - 2 = 0 by norm_num] at h2
  apply t6p_mem_normalizer_of_map_eq
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj t.x₂).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj t.x₂).injective, h0, h1, h2, sup_comm]

private theorem L2_le_normalizer_A {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) (hZ2' : ¬ t.Zv (-1) ≤ t.Gv 2) :
    L2 ≤ normalizer (((t.Qv 1 ⊓ t.Qv 0) ⊔ (t.Qv 1 ⊓ t.Qv 2) : Subgroup G) : Set G) := by
  have hQ1G0 : t.Qv 1 ≤ t.Gv 0 := t.t6p_Qv_one_le_Gv_zero hfr
  have hQ1G2 : t.Qv 1 ≤ t.Gv 2 := t.Qv_one_le_Gv_two hfr
  have hN0 : ∀ g ∈ t.Gv 0, g ∈ normalizer (t.Qv 0 : Set G) := fun g hg =>
    t.Gv_le_normalizer_Qv 0 hg
  have hN1 : ∀ g ∈ t.Gv 1, g ∈ normalizer (t.Qv 1 : Set G) := fun g hg =>
    t.Gv_le_normalizer_Qv 1 hg
  have hN2 : ∀ g ∈ t.Gv 2, g ∈ normalizer (t.Qv 2 : Set G) := fun g hg =>
    t.Gv_le_normalizer_Qv 2 hg
  have hQ1N : t.Qv 1 ≤ normalizer
      (((t.Qv 1 ⊓ t.Qv 0) ⊔ (t.Qv 1 ⊓ t.Qv 2) : Subgroup G) : Set G) := by
    intro q hq
    exact t6p_mem_normalizer_sup
      (t6p_mem_normalizer_inf (hN1 q (t.Qv_le_Gv_self 1 hq)) (hN0 q (hQ1G0 hq)))
      (t6p_mem_normalizer_inf (hN1 q (t.Qv_le_Gv_self 1 hq)) (hN2 q (hQ1G2 hq)))
  have hZN : t.Zv (-1) ≤ normalizer
      (((t.Qv 1 ⊓ t.Qv 0) ⊔ (t.Qv 1 ⊓ t.Qv 2) : Subgroup G) : Set G) := by
    intro z hz
    have hz0 : z ∈ t.Qv 0 := t.Zv_neg_one_le_Qv_zero hfr hZ0 hz
    have hzS : z ∈ S := by
      rw [t.Qv_zero] at hz0
      exact Q1_le_S hfr.hF hz0
    have hzN0 : z ∈ normalizer (t.Qv 0 : Set G) := hN0 z (t.Qv_le_Gv_self 0 hz0)
    have hzN1 : z ∈ normalizer (t.Qv 1 : Set G) := hN1 z (t.t6p_S_le_Gv_one hfr hzS)
    apply t6p_mem_normalizer_of_map_le
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact mem_sup_left (t6p_conj_mem (t6p_mem_normalizer_inf hzN1 hzN0) hy)
    · rintro _ ⟨y, hy, rfl⟩
      have hyN0 : y ∈ normalizer (t.Qv 0 : Set G) := hN0 y (hQ1G0 (mem_inf.mp hy).1)
      have hc0 : z * y * z⁻¹ * y⁻¹ ∈ t.Qv 0 := by
        rw [mul_assoc, mul_assoc]
        refine mul_mem hz0 ?_
        have := t6p_conj_mem hyN0 (inv_mem hz0)
        rwa [mul_assoc] at this
      have hc1 : z * y * z⁻¹ * y⁻¹ ∈ t.Qv 1 :=
        mul_mem (t6p_conj_mem hzN1 (mem_inf.mp hy).1) (inv_mem (mem_inf.mp hy).1)
      have e : (MulAut.conj z).toMonoidHom y = (z * y * z⁻¹ * y⁻¹) * y := by
        simp [MulAut.conj_apply]
      rw [e]
      exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hc1, hc0⟩)) (mem_sup_right hy)
  have hSN : S ≤ normalizer
      (((t.Qv 1 ⊓ t.Qv 0) ⊔ (t.Qv 1 ⊓ t.Qv 2) : Subgroup G) : Set G) :=
    (t.S_le_Zv_neg_one_sup_Qv_one hfr hZ0 hZ2').trans (sup_le hZN hQ1N)
  have hx := Subgroup.le_normalizer (t.x₂_mem_normalizer_A hfr)
  have h := t.L2_le_sup_Qv_one_of_sylow hfr
    (X := normalizer
      (((t.Qv 1 ⊓ t.Qv 0) ⊔ (t.Qv 1 ⊓ t.Qv 2) : Subgroup G) : Set G))
    ((inf_le_left.trans hSN).trans le_sup_left) hx
  rwa [sup_eq_left.mpr hQ1N] at h

open scoped commutatorElement in
private theorem commutator_mem_of_mem_A {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hD : t.Qv 0 ⊓ t.Qv 2 = t.Zv 1) :
    ∀ x ∈ t.Qv 1 ⊓ t.Qv 0, ∀ y ∈ t.Qv 1 ⊓ t.Qv 2, ⁅x, y⁆ ∈ t.Zv 1 := by
  intro x hx y hy
  rw [← hD]
  have hQ1G0 : t.Qv 1 ≤ t.Gv 0 := t.t6p_Qv_one_le_Gv_zero hfr
  have hQ1G2 : t.Qv 1 ≤ t.Gv 2 := t.Qv_one_le_Gv_two hfr
  obtain ⟨hx1, hx0⟩ := mem_inf.mp hx
  obtain ⟨hy1, hy2⟩ := mem_inf.mp hy
  have hyN0 : y ∈ normalizer (t.Qv 0 : Set G) := t.Gv_le_normalizer_Qv 0 (hQ1G0 hy1)
  have hxN2 : x ∈ normalizer (t.Qv 2 : Set G) := t.Gv_le_normalizer_Qv 2 (hQ1G2 hx1)
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine mul_mem hx0 ?_
    have := t6p_conj_mem hyN0 (inv_mem hx0)
    rwa [mul_assoc] at this
  · exact mul_mem (t6p_conj_mem hxN2 hy2) (inv_mem hy2)

private def t6q_commSub (N V Z : Subgroup G) (hN : N ≤ normalizer (Z : Set G)) : Subgroup G where
  carrier := {s | s ∈ N ∧ ∀ v ∈ V, ⁅s, v⁆ ∈ Z}
  one_mem' := ⟨one_mem _, fun v _ => by simp⟩
  mul_mem' := by
    rintro s₁ s₂ ⟨hs₁, h₁⟩ ⟨hs₂, h₂⟩
    refine ⟨mul_mem hs₁ hs₂, fun v hv => ?_⟩
    have e : ⁅s₁ * s₂, v⁆ = (s₁ * ⁅s₂, v⁆ * s₁⁻¹) * ⁅s₁, v⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.mp (hN hs₁) _).mp (h₂ v hv)) (h₁ v hv)
  inv_mem' := by
    rintro s ⟨hs, h⟩
    refine ⟨inv_mem hs, fun v hv => ?_⟩
    have e : ⁅s⁻¹, v⁆ = s⁻¹ * ⁅s, v⁆⁻¹ * s := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := (mem_normalizer_iff.mp (hN (inv_mem hs)) _).mp (inv_mem (h v hv))
    simpa using this

private theorem t6q_commutator_mem_Zv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) (hZ2' : ¬ t.Zv (-1) ≤ t.Gv 2)
    (hZ10 : t.Zv 0 ≤ t.Zv 1) (hN1 : ∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 0)
    (hA : t.Qv 1 ⊓ t.Qv 0 = t.Zv 1) : ∀ s ∈ S, ∀ v ∈ t.VZ, ⁅s, v⁆ ∈ t.Zv 1 := by
  have hZH : t.Zv (-1) ≤ t6q_commSub (t.Gv 1) t.VZ (t.Zv 1) (t.Gv_le_normalizer_Zv 1) := by
    intro z hz
    have hz0 : z ∈ t.Qv 0 := t.Zv_neg_one_le_Qv_zero hfr hZ0 hz
    refine ⟨?_, fun v hv => ?_⟩
    · rw [t.Qv_zero] at hz0
      exact t.t6p_S_le_Gv_one hfr (Q1_le_S hfr.hF hz0)
    · exact hZ10 (t.commutator_mem_Zv_zero_of_mem_Qv_zero hfr hZ0 hN1 z hz0 v hv)
  have hQH : t.Qv 1 ≤ t6q_commSub (t.Gv 1) t.VZ (t.Zv 1) (t.Gv_le_normalizer_Zv 1) := by
    intro q hq
    refine ⟨t.Qv_le_Gv_self 1 hq, fun v hv => ?_⟩
    have hv0 : v ∈ t.Qv 0 := t.VZ_le_Qv_zero hfr hZ0 hv
    have hvS : v ∈ S := by
      rw [t.Qv_zero] at hv0
      exact Q1_le_S hfr.hF hv0
    have hqN0 : q ∈ normalizer (t.Qv 0 : Set G) :=
      t.Gv_le_normalizer_Qv 0 (t.t6p_Qv_one_le_Gv_zero hfr hq)
    have hvN1 : v ∈ normalizer (t.Qv 1 : Set G) :=
      t.Gv_le_normalizer_Qv 1 (t.t6p_S_le_Gv_one hfr hvS)
    rw [← hA]
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : v * q⁻¹ * v⁻¹ ∈ t.Qv 1 := t6r_conj_mem hvN1 (inv_mem hq)
      have e : ⁅q, v⁆ = q * (v * q⁻¹ * v⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem hq h1
    · rw [commutatorElement_def]
      exact mul_mem (t6r_conj_mem hqN0 hv0) (inv_mem hv0)
  have hS : S ≤ t6q_commSub (t.Gv 1) t.VZ (t.Zv 1) (t.Gv_le_normalizer_Zv 1) :=
    (t.S_le_Zv_neg_one_sup_Qv_one hfr hZ0 hZ2').trans (sup_le hZH hQH)
  exact fun s hs v hv => (hS hs).2 v hv

private theorem Qv_one_inf_Qv_zero_ne_of_t6 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) (hZ2' : ¬ t.Zv (-1) ≤ t.Gv 2)
    (hZ10 : t.Zv 0 ≤ t.Zv 1) (hcard0 : Nat.card (t.Zv 1) = 2 ^ f * 2 ^ f)
    (hN1 : ∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 0) :
    t.Qv 1 ⊓ t.Qv 0 ≠ t.Zv 1 := by
  intro hA
  have hS := t.t6q_commutator_mem_Zv_one hfr hZ0 hZ2' hZ10 hN1 hA
  have hquad : ∀ s ∈ S ⊓ L1, ∀ v ∈ t.VZ, ⁅s, ⁅s, v⁆⁆ ∈ t.Zv 0 := by
    intro s hs v hv
    exact hN1 s (mem_inf.mp hs).1 ⁅s, v⁆ (hS s (mem_inf.mp hs).1 v hv)
  have hL : L1 ≤ normalizer (t.VZ : Set G) ⊓ normalizer (t.Zv 0 : Set G) :=
    le_inf (le_sup_left.trans t.P1_le_normalizer_VZ)
      (le_sup_left.trans t.t6v_P1_le_normalizer_Zv_zero)
  have hQ : ∀ p ∈ pCoreOf 2 L1, ∀ v ∈ t.VZ, ⁅p, v⁆ ∈ t.Zv 0 := fun p hp v hv =>
    t.commutator_mem_Zv_zero_of_mem_Qv_zero hfr hZ0 hN1 p
      (by rw [t.Qv_zero]; exact Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1 hp) v hv
  obtain ⟨l, hl, v, hv, hnot⟩ := t.exists_not_commutator_mem_VZ hfr hZ10 hcard0
  exact hnot (CFSG.Quasithin.Stroth.commutator_mem_of_quadratic_of_sz hfr.ha hfr.hSz
    hfr.hF.1.h1.sylow (t.isElemSec_VZ hfr hZ0 hZ10 hN1) hL hQ hquad l hl v hv)

private theorem Qv_one_inf_Qv_two_ne_of_t6 {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) (hZ2' : ¬ t.Zv (-1) ≤ t.Gv 2)
    (hZ10 : t.Zv 0 ≤ t.Zv 1) (hcard0 : Nat.card (t.Zv 1) = 2 ^ f * 2 ^ f)
    (hN1 : ∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 0) :
    t.Qv 1 ⊓ t.Qv 2 ≠ t.Zv 1 := by
  intro h
  refine t.Qv_one_inf_Qv_zero_ne_of_t6 hfr hZ0 hZ2' hZ10 hcard0 hN1 ?_
  have hmapQ : ∀ i : ℤ, (t.Qv i).map (MulAut.conj t.x₂).toMonoidHom = t.Qv (2 - i) := fun i =>
    t.track.map_qv_x₂ (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _) i
  have hmapZ : ∀ i : ℤ, (t.Zv i).map (MulAut.conj t.x₂).toMonoidHom = t.Zv (2 - i) := fun i =>
    t.track.map_qv_x₂ t6p_P1_le_normalizer_Z1 t6v_P2_le_normalizer_Z2 i
  have h1 := congrArg (Subgroup.map (MulAut.conj t.x₂).toMonoidHom) h
  rw [Subgroup.map_inf _ _ _ (MulAut.conj t.x₂).injective, hmapQ 1, hmapQ 2, hmapZ 1,
    show (2 : ℤ) - 1 = 1 by norm_num, show (2 : ℤ) - 2 = 0 by norm_num] at h1
  exact h1

theorem exists_omega_of_sz {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    ∃ Ω : Subgroup G, (∀ s, s ∈ Ω ↔ s ∈ S ∧ s ^ 2 ∈ t.Qv 0) ∧
      (∀ ω ∈ Ω, ∀ s ∈ S, ⁅ω, s⁆ ∈ t.Qv 0) ∧ (t.Qv 0).relIndex Ω ≤ 2 ^ (2 * a + 1) := by
  have hR : pCoreOf 2 (t.Gw 0 (0 + 1)) = S := by
    rw [zero_add]
    exact t.pCoreOf_Gw_zero_one hfr
  refine ⟨t.rootOmega 0, fun s => ?_, fun ω hω s hs => ?_, ?_⟩
  · rw [t.mem_rootOmega_iff hfr 0, hR]
  · exact t.commutator_rootOmega_le hfr 0
      (Subgroup.commutator_mem_commutator hω (by rw [hR]; exact hs))
  · rw [t.relIndex_rootOmega hfr 0, if_pos (by decide)]

private theorem exists_R_of_t6 {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hD : t.Qv 0 ⊓ t.Qv 2 = t.Zv 1) (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3)
    (hA : t.Qv 1 ⊓ t.Qv 2 ≠ t.Zv 1) :
    ∃ R : Subgroup G, t.Zv 1 ≤ R ∧ R ≤ t.Qv 1 ⊓ t.Qv 2 ∧ R ≠ t.Zv 1 ∧
      (∀ y, y ∈ R ↔ y ∈ t.Qv 1 ⊓ t.Qv 2 ∧ y ^ 2 ∈ t.Qv 0) ∧
      (∀ q ∈ t.Qv 1, ∀ y ∈ R, ⁅q, y⁆ ∈ t.Zv 1) ∧
      (∀ y ∈ R, ∀ y' ∈ R, ⁅y, y'⁆ ∈ t.Zv 1) ∧
      (t.Zv 1).relIndex R ≤ 2 ^ (2 * a + 1) := by
  classical
  obtain ⟨Ω, hΩmem, hΩcomm, hΩidx⟩ := t.exists_omega_of_sz hfr
  have hQ1S : t.Qv 1 ≤ S := by
    rw [t.Qv_one]
    exact Q2_le_S hfr.hF
  have hZQ1 : t.Zv 1 ≤ t.Qv 1 := t.Zv_le_Qv 1
  have hZQ2 : t.Zv 1 ≤ t.Qv 2 :=
    t.le_Qv_of_le_Gw hfr (u := -1) (w := 3) (j := 2) (by norm_num) (by norm_num)
      (t.isPGroup_Zv 1) hZ0
  have hZQ0 : t.Zv 1 ≤ t.Qv 0 := hD.symm.le.trans inf_le_left
  have hZsq : ∀ z ∈ t.Zv 1, z ^ 2 = 1 := fun z hz =>
    A4.sq_eq_one_of_mem_omegaOneCenterOf (by rwa [t.Zv_eq 1] at hz)
  have hΩ : ∀ y ∈ t.Qv 1 ⊓ t.Qv 2, (y ∈ Ω ↔ y ^ 2 ∈ t.Qv 0) := fun y hy =>
    (hΩmem y).trans ⟨fun h => h.2, fun h => ⟨hQ1S hy.1, h⟩⟩
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup G, R = (t.Qv 1 ⊓ t.Qv 2) ⊓ Ω := ⟨_, rfl⟩
  have hRQ : R ≤ t.Qv 1 ⊓ t.Qv 2 := hRdef ▸ inf_le_left
  have hRΩ : R ≤ Ω := hRdef ▸ inf_le_right
  have hRmem : ∀ y, y ∈ R ↔ y ∈ t.Qv 1 ⊓ t.Qv 2 ∧ y ^ 2 ∈ t.Qv 0 := by
    intro y
    rw [hRdef]
    constructor
    · rintro ⟨hy, hyΩ⟩
      exact ⟨hy, (hΩ y hy).mp hyΩ⟩
    · rintro ⟨hy, hy2⟩
      exact ⟨hy, (hΩ y hy).mpr hy2⟩
  have hZR : t.Zv 1 ≤ R := by
    intro z hz
    refine (hRmem z).mpr ⟨⟨hZQ1 hz, hZQ2 hz⟩, ?_⟩
    rw [hZsq z hz]
    exact one_mem _
  have hcomm : ∀ q ∈ t.Qv 1, ∀ y ∈ R, ⁅q, y⁆ ∈ t.Zv 1 := by
    intro q hq y hy
    rw [← hD]
    refine ⟨?_, ?_⟩
    · have h := inv_mem (hΩcomm y (hRΩ hy) q (hQ1S hq))
      rwa [commutatorElement_inv] at h
    · have hqN : q ∈ normalizer (t.Qv 2 : Set G) :=
        t.Gv_le_normalizer_Qv 2 (t.Qv_one_le_Gv_two hfr hq)
      have hy2 : y ∈ t.Qv 2 := (hRQ hy).2
      have h2 : ⁅q, y⁆ ∈ t.Qv 2 := mul_mem (t6r_conj_mem hqN hy2) (inv_mem hy2)
      exact h2
  have hRQ0 : t.Qv 0 ⊓ R = t.Zv 1 := by
    refine le_antisymm ?_ (le_inf hZQ0 hZR)
    rintro y ⟨hy0, hyR⟩
    rw [← hD]
    exact ⟨hy0, (hRQ hyR).2⟩
  have hne : R ≠ t.Zv 1 := by
    intro hR
    obtain ⟨y, hy, hyZ⟩ : ∃ y ∈ t.Qv 1 ⊓ t.Qv 2, y ∉ t.Zv 1 := by
      by_contra hcon
      apply hA
      refine le_antisymm (fun y hy => ?_) (le_inf hZQ1 hZQ2)
      by_contra hyZ
      exact hcon ⟨y, hy, hyZ⟩
    have hex : ∃ j : ℕ, y ^ (2 ^ j) ∈ t.Zv 1 := by
      obtain ⟨n, hn⟩ := (t.isPGroup_Qv 1) ⟨y, hy.1⟩
      refine ⟨n, ?_⟩
      have h1 : y ^ (2 ^ n) = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      rw [h1]
      exact one_mem _
    obtain ⟨j, hj, hjmin⟩ : ∃ j : ℕ, y ^ (2 ^ j) ∈ t.Zv 1 ∧ ∀ i < j, y ^ (2 ^ i) ∉ t.Zv 1 :=
      ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := by
      rcases j with _ | j'
      · exact absurd (by simpa using hj) hyZ
      · exact ⟨j', rfl⟩
    have hy'sq : (y ^ (2 ^ j')) ^ 2 ∈ t.Qv 0 := by
      rw [← pow_mul, ← pow_succ]
      exact hZQ0 hj
    have hy'R : y ^ (2 ^ j') ∈ R := (hRmem _).mpr ⟨pow_mem hy _, hy'sq⟩
    rw [hR] at hy'R
    exact hjmin j' (Nat.lt_succ_self j') hy'R
  refine ⟨R, hZR, hRQ, hne, hRmem, hcomm, fun y hy y' hy' => hcomm y (hRQ hy).1 y' hy', ?_⟩
  calc (t.Zv 1).relIndex R = (t.Qv 0).relIndex R := by
        rw [← hRQ0, Subgroup.inf_relIndex_right]
    _ ≤ (t.Qv 0).relIndex Ω := Subgroup.relIndex_le_of_le_right hRΩ (t6r_relIndex_ne_zero _ _)
    _ ≤ 2 ^ (2 * a + 1) := hΩidx

private theorem t6f_sq_mul {Z : Subgroup G} {x y : G} (hx : x ∈ normalizer (Z : Set G))
    (hc : ⁅y, x⁆ ∈ Z) : ∃ z ∈ Z, (x * y) ^ 2 = z * (x ^ 2 * y ^ 2) := by
  refine ⟨x * ⁅y, x⁆ * x⁻¹, (mem_normalizer_iff.mp hx _).mp hc, ?_⟩
  simp only [commutatorElement_def, pow_two]
  group

private theorem t6f_mem_normalizer_of_comm {Z R : Subgroup G} {g : G} (hZR : Z ≤ R)
    (h : ∀ y ∈ R, ⁅g, y⁆ ∈ Z) (h' : ∀ y ∈ R, ⁅g⁻¹, y⁆ ∈ Z) :
    g ∈ normalizer (R : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have e : ⁅g, y⁆ * y = g * y * g⁻¹ := by simp only [commutatorElement_def]; group
    rw [← e]
    exact mul_mem (hZR (h y hy)) hy
  · intro hy
    have e : ⁅g⁻¹, g * y * g⁻¹⁆ * (g * y * g⁻¹) = y := by
      simp only [commutatorElement_def]; group
    have := mul_mem (hZR (h' _ hy)) hy
    rwa [e] at this

private theorem t6f_mem_normalizer_R {Q0 Q1 Q2 R : Subgroup G} {g : G}
    (hQ0 : g ∈ normalizer (Q0 : Set G)) (hQ1 : g ∈ normalizer (Q1 : Set G))
    (hQ2 : g ∈ normalizer (Q2 : Set G)) (hRmem : ∀ y, y ∈ R ↔ y ∈ Q1 ⊓ Q2 ∧ y ^ 2 ∈ Q0) :
    g ∈ normalizer (R : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  have e : (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ := by simp only [pow_two]; group
  have h12 := A4.mem_normalizer_inf hQ1 hQ2
  show y ∈ R ↔ g * y * g⁻¹ ∈ R
  rw [hRmem, hRmem, e]
  exact and_congr (mem_normalizer_iff.mp h12 y) (mem_normalizer_iff.mp hQ0 (y ^ 2))

private theorem t6f_conj_data {Q0 Q1 Q2 Z R R' : Subgroup G} {c : G}
    (hcQ1 : c ∈ normalizer (Q1 : Set G)) (hcZ : c ∈ normalizer (Z : Set G))
    (h02 : ∀ w, w ∈ Q0 ↔ c⁻¹ * w * c ∈ Q2) (h20 : ∀ w, w ∈ Q2 ↔ c⁻¹ * w * c ∈ Q0)
    (hR' : ∀ y, y ∈ R' ↔ c⁻¹ * y * c ∈ R) (hZR : Z ≤ R) (hRA : R ≤ Q1 ⊓ Q2)
    (hRmem : ∀ y, y ∈ R ↔ y ∈ Q1 ⊓ Q2 ∧ y ^ 2 ∈ Q0)
    (hRQ : ∀ q ∈ Q1, ∀ y ∈ R, ⁅q, y⁆ ∈ Z) :
    Z ≤ R' ∧ R' ≤ Q1 ⊓ Q0 ∧ (∀ y, y ∈ R' ↔ y ∈ Q1 ⊓ Q0 ∧ y ^ 2 ∈ Q2) ∧
      ∀ q ∈ Q1, ∀ y ∈ R', ⁅q, y⁆ ∈ Z := by
  have hQ1c : ∀ w, w ∈ Q1 ↔ c⁻¹ * w * c ∈ Q1 := fun w => by
    have := mem_normalizer_iff.mp (inv_mem hcQ1) w
    rwa [inv_inv] at this
  have hZc : ∀ w, w ∈ Z ↔ c⁻¹ * w * c ∈ Z := fun w => by
    have := mem_normalizer_iff.mp (inv_mem hcZ) w
    rwa [inv_inv] at this
  have hsq : ∀ y : G, (c⁻¹ * y * c) ^ 2 = c⁻¹ * y ^ 2 * c := fun y => by
    simp only [pow_two]; group
  have hRA' : R' ≤ Q1 ⊓ Q0 := fun y hy => by
    have h1 := hRA ((hR' y).mp hy)
    exact mem_inf.mpr ⟨(hQ1c y).mpr (mem_inf.mp h1).1, (h02 y).mpr (mem_inf.mp h1).2⟩
  refine ⟨fun z hz => (hR' z).mpr (hZR ((hZc z).mp hz)), hRA',
    fun y => ⟨fun hy => ⟨hRA' hy, ?_⟩, fun hy => ?_⟩, ?_⟩
  · have h1 := ((hRmem _).mp ((hR' y).mp hy)).2
    rw [hsq] at h1
    exact (h20 _).mpr h1
  · have h1 := mem_inf.mp hy.1
    refine (hR' y).mpr ((hRmem _).mpr ⟨mem_inf.mpr ⟨(hQ1c y).mp h1.1, (h02 y).mp h1.2⟩, ?_⟩)
    rw [hsq]
    exact (h20 _).mp hy.2
  · intro q hq y hy
    have h1 := hRQ (c⁻¹ * q * c) ((hQ1c q).mp hq) (c⁻¹ * y * c) ((hR' y).mp hy)
    have e : ⁅c⁻¹ * q * c, c⁻¹ * y * c⁆ = c⁻¹ * ⁅q, y⁆ * c := by
      simp only [commutatorElement_def]; group
    rw [e] at h1
    exact (hZc _).mpr h1

private structure t6f_Data (Q0 Q1 Q2 Z R R' : Subgroup G) : Prop where
  hD : Q0 ⊓ Q2 = Z
  hZQ : Z ≤ Q1
  hQN : Q1 ≤ normalizer (Z : Set G)
  hAA : ∀ x ∈ Q1 ⊓ Q0, ∀ y ∈ Q1 ⊓ Q2, ⁅x, y⁆ ∈ Z
  hZR : Z ≤ R
  hRA : R ≤ Q1 ⊓ Q2
  hRmem : ∀ y, y ∈ R ↔ y ∈ Q1 ⊓ Q2 ∧ y ^ 2 ∈ Q0
  hRQ : ∀ q ∈ Q1, ∀ y ∈ R, ⁅q, y⁆ ∈ Z
  hZR' : Z ≤ R'
  hRA' : R' ≤ Q1 ⊓ Q0
  hRmem' : ∀ y, y ∈ R' ↔ y ∈ Q1 ⊓ Q0 ∧ y ^ 2 ∈ Q2
  hRQ' : ∀ q ∈ Q1, ∀ y ∈ R', ⁅q, y⁆ ∈ Z

private theorem t6f_Z_le_Q0 {Q0 Q1 Q2 Z R R' : Subgroup G} (h : t6f_Data Q0 Q1 Q2 Z R R') :
    Z ≤ Q0 := by
  rw [← h.hD]; exact inf_le_left

private theorem t6f_Z_le_Q2 {Q0 Q1 Q2 Z R R' : Subgroup G} (h : t6f_Data Q0 Q1 Q2 Z R R') :
    Z ≤ Q2 := by
  rw [← h.hD]; exact inf_le_right

private theorem t6f_AB {Q0 Q1 Q2 Z R R' : Subgroup G} (h : t6f_Data Q0 Q1 Q2 Z R R') :
    (Q1 ⊓ Q0) ⊓ (Q1 ⊓ Q2) = Z := by
  refine le_antisymm ?_ (le_inf (le_inf h.hZQ (t6f_Z_le_Q0 h)) (le_inf h.hZQ (t6f_Z_le_Q2 h)))
  intro y hy
  have h0 : y ∈ Q0 := (mem_inf.mp (mem_inf.mp hy).1).2
  have h2 : y ∈ Q2 := (mem_inf.mp (mem_inf.mp hy).2).2
  rw [← h.hD]
  exact mem_inf.mpr ⟨h0, h2⟩

private theorem t6f_A_le_normalizer_B {Q0 Q1 Q2 Z R R' : Subgroup G}
    (h : t6f_Data Q0 Q1 Q2 Z R R') :
    (Q1 ⊓ Q0) ≤ normalizer ((Q1 ⊓ Q2 : Subgroup G) : Set G) := fun x hx =>
  t6f_mem_normalizer_of_comm (le_inf h.hZQ (t6f_Z_le_Q2 h)) (fun y hy => h.hAA x hx y hy)
    (fun y hy => h.hAA x⁻¹ (inv_mem hx) y hy)

private theorem t6f_R'_le_normalizer_R {Q0 Q1 Q2 Z R R' : Subgroup G}
    (h : t6f_Data Q0 Q1 Q2 Z R R') : R' ≤ normalizer (R : Set G) := fun x hx =>
  t6f_mem_normalizer_of_comm h.hZR (fun y hy => h.hAA x (h.hRA' hx) y (h.hRA hy))
    (fun y hy => h.hAA x⁻¹ (h.hRA' (inv_mem hx)) y (h.hRA hy))

private theorem t6f_sup_decomp {Q0 Q1 Q2 Z R R' : Subgroup G} (h : t6f_Data Q0 Q1 Q2 Z R R')
    {p : G} (hp : p ∈ R' ⊔ R) : ∃ r ∈ R, ∃ r' ∈ R', p = r * r' := by
  rw [sup_comm] at hp
  exact (F1.mem_sup_iff_exists_mul_of_normalizes (t6f_R'_le_normalizer_R h)).mp hp

private theorem t6f_sup_le_Q1 {Q0 Q1 Q2 Z R R' : Subgroup G} (h : t6f_Data Q0 Q1 Q2 Z R R') :
    R' ⊔ R ≤ Q1 :=
  sup_le (h.hRA'.trans inf_le_left) (h.hRA.trans inf_le_left)

private theorem t6f_sq_R {Q0 Q1 Q2 Z R R' : Subgroup G} (h : t6f_Data Q0 Q1 Q2 Z R R')
    {r : G} (hr : r ∈ R) : r ^ 2 ∈ Z := by
  have h1 := (h.hRmem r).mp hr
  rw [← h.hD]
  exact mem_inf.mpr ⟨h1.2, (mem_inf.mp (pow_mem h1.1 2)).2⟩

private theorem t6f_sq_R' {Q0 Q1 Q2 Z R R' : Subgroup G} (h : t6f_Data Q0 Q1 Q2 Z R R')
    {r : G} (hr : r ∈ R') : r ^ 2 ∈ Z := by
  have h1 := (h.hRmem' r).mp hr
  rw [← h.hD]
  exact mem_inf.mpr ⟨(mem_inf.mp (pow_mem h1.1 2)).2, h1.2⟩

private theorem t6f_comm_P0 {Q0 Q1 Q2 Z R R' : Subgroup G} (h : t6f_Data Q0 Q1 Q2 Z R R') :
    ∀ q ∈ Q1, ∀ v ∈ R' ⊔ R, ⁅q, v⁆ ∈ Z := by
  intro q hq v hv
  obtain ⟨r, hr, r', hr', rfl⟩ := t6f_sup_decomp h hv
  have e : ⁅q, r * r'⁆ = ⁅q, r⁆ * (r * ⁅q, r'⁆ * r⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  have hrQ : r ∈ Q1 := (mem_inf.mp (h.hRA hr)).1
  exact mul_mem (h.hRQ q hq r hr)
    ((mem_normalizer_iff.mp (h.hQN hrQ) _).mp (h.hRQ' q hq r' hr'))

private theorem t6f_sq_P0 {Q0 Q1 Q2 Z R R' : Subgroup G} (h : t6f_Data Q0 Q1 Q2 Z R R')
    {p : G} (hp : p ∈ R' ⊔ R) : p ^ 2 ∈ Z := by
  obtain ⟨r, hr, r', hr', rfl⟩ := t6f_sup_decomp h hp
  obtain ⟨z, hz, hzeq⟩ := t6f_sq_mul (Z := Z) (x := r) (y := r')
    (h.hQN (mem_inf.mp (h.hRA hr)).1) (h.hAA r' (h.hRA' hr') r (h.hRA hr))
  rw [hzeq]
  exact mul_mem hz (mul_mem (t6f_sq_R h hr) (t6f_sq_R' h hr'))

private theorem t6f_isElemSec {Q0 Q1 Q2 Z R R' : Subgroup G} (h : t6f_Data Q0 Q1 Q2 Z R R') :
    CFSG.GH74.QTGen4.DSGen4.IsElemSec Z (R' ⊔ R) := by
  unfold CFSG.GH74.QTGen4.DSGen4.IsElemSec
  refine ⟨h.hZR.trans le_sup_right, ?_, fun p hp => t6f_sq_P0 h hp⟩
  rw [Subgroup.commutator_le]
  intro p hp v hv
  exact t6f_comm_P0 h p (t6f_sup_le_Q1 h hp) v hv

private theorem t6f_mem_sup_iff {Q0 Q1 Q2 Z R R' : Subgroup G} (h : t6f_Data Q0 Q1 Q2 Z R R')
    (p : G) : p ∈ R' ⊔ R ↔ p ∈ (Q1 ⊓ Q0) ⊔ (Q1 ⊓ Q2) ∧ p ^ 2 ∈ Z := by
  constructor
  · intro hp
    exact ⟨sup_le_sup h.hRA' h.hRA hp, t6f_sq_P0 h hp⟩
  · rintro ⟨hp, hp2⟩
    rw [sup_comm] at hp
    obtain ⟨b, hb, a, ha, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes (t6f_A_le_normalizer_B h)).mp hp
    obtain ⟨z, hz, hzeq⟩ := t6f_sq_mul (Z := Z) (x := b) (y := a)
      (h.hQN (mem_inf.mp hb).1) (h.hAA a ha b hb)
    rw [hzeq] at hp2
    have hZB : Z ≤ Q1 ⊓ Q2 := le_inf h.hZQ (t6f_Z_le_Q2 h)
    have h3 : b ^ 2 * a ^ 2 ∈ Z := by
      have := mul_mem (inv_mem hz) hp2
      rwa [inv_mul_cancel_left] at this
    have h4 : a ^ 2 ∈ Q1 ⊓ Q2 := by
      have e : a ^ 2 = (b ^ 2)⁻¹ * (b ^ 2 * a ^ 2) := by group
      rw [e]
      exact mul_mem (inv_mem (pow_mem hb 2)) (hZB h3)
    have h5 : a ^ 2 ∈ Z := by
      rw [← t6f_AB h]
      exact mem_inf.mpr ⟨pow_mem ha 2, h4⟩
    have h6 : b ^ 2 ∈ Z := by
      have e : b ^ 2 = (b ^ 2 * a ^ 2) * (a ^ 2)⁻¹ := by group
      rw [e]
      exact mul_mem h3 (inv_mem h5)
    have hbR : b ∈ R := (h.hRmem b).mpr ⟨hb, t6f_Z_le_Q0 h h6⟩
    have haR' : a ∈ R' := (h.hRmem' a).mpr ⟨ha, t6f_Z_le_Q2 h h5⟩
    exact mul_mem (mem_sup_right hbR) (mem_sup_left haR')

private theorem t6f_mem_normalizer_P0 {Q0 Q1 Q2 Z R R' : Subgroup G}
    (h : t6f_Data Q0 Q1 Q2 Z R R') {g : G}
    (hgP : g ∈ normalizer (((Q1 ⊓ Q0) ⊔ (Q1 ⊓ Q2) : Subgroup G) : Set G))
    (hgZ : g ∈ normalizer (Z : Set G)) : g ∈ normalizer ((R' ⊔ R : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro p
  have e : (g * p * g⁻¹) ^ 2 = g * p ^ 2 * g⁻¹ := by simp only [pow_two]; group
  show p ∈ R' ⊔ R ↔ g * p * g⁻¹ ∈ R' ⊔ R
  rw [t6f_mem_sup_iff h, t6f_mem_sup_iff h, e]
  exact and_congr (mem_normalizer_iff.mp hgP p) (mem_normalizer_iff.mp hgZ (p ^ 2))

private theorem t6f_inf_RR' {Q0 Q1 Q2 Z R R' : Subgroup G} (h : t6f_Data Q0 Q1 Q2 Z R R') :
    R ⊓ R' = Z := by
  refine le_antisymm ?_ (le_inf h.hZR h.hZR')
  intro y hy
  rw [← t6f_AB h]
  exact mem_inf.mpr ⟨h.hRA' (mem_inf.mp hy).2, h.hRA (mem_inf.mp hy).1⟩

private theorem t6f_relIndex_sup {Q0 Q1 Q2 Z R R' : Subgroup G} (h : t6f_Data Q0 Q1 Q2 Z R R') :
    Z.relIndex (R' ⊔ R) = Z.relIndex R' * Z.relIndex R := by
  have h1 := Subgroup.relIndex_mul_relIndex Z R (R' ⊔ R) h.hZR le_sup_right
  have h2 := C5.relIndex_sup_eq_of_le_normalizer (t6f_R'_le_normalizer_R h)
  have h3 : R.relIndex R' = Z.relIndex R' := by
    have h4 := Subgroup.inf_relIndex_right R R'
    rw [t6f_inf_RR' h] at h4
    exact h4.symm
  rw [← h1, h2, h3]
  exact mul_comm _ _

private theorem false_of_R {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hqr : 2 * a + 1 < f)
    (hD : t.Qv 0 ⊓ t.Qv 2 = t.Zv 1)
    (hL2P : L2 ≤ normalizer (((t.Qv 1 ⊓ t.Qv 0) ⊔ (t.Qv 1 ⊓ t.Qv 2) : Subgroup G) : Set G))
    (hAA : ∀ x ∈ t.Qv 1 ⊓ t.Qv 0, ∀ y ∈ t.Qv 1 ⊓ t.Qv 2, ⁅x, y⁆ ∈ t.Zv 1)
    {R : Subgroup G} (hZR : t.Zv 1 ≤ R) (hRA : R ≤ t.Qv 1 ⊓ t.Qv 2) (hRne : R ≠ t.Zv 1)
    (hRmem : ∀ y, y ∈ R ↔ y ∈ t.Qv 1 ⊓ t.Qv 2 ∧ y ^ 2 ∈ t.Qv 0)
    (hRQ : ∀ q ∈ t.Qv 1, ∀ y ∈ R, ⁅q, y⁆ ∈ t.Zv 1)
    (hRidx : (t.Zv 1).relIndex R ≤ 2 ^ (2 * a + 1)) : False := by
  have hx₂G : t.x₂ ∈ t.Gv 1 := by rw [t.Gv_one]; exact t.track.x₂_mem
  have hx₂Q : t.x₂ ∈ normalizer (t.Qv 1 : Set G) := t.Gv_le_normalizer_Qv 1 hx₂G
  have hx₂Z : t.x₂ ∈ normalizer (t.Zv 1 : Set G) := t.Gv_le_normalizer_Zv 1 hx₂G
  have hQx : ∀ (i : ℤ) (w : G), w ∈ t.Qv i ↔ t.x₂⁻¹ * w * t.x₂ ∈ t.Qv (2 - i) := fun i w =>
    t.track.mem_qv_two_sub_iff (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _) i
  have h02 : ∀ w, w ∈ t.Qv 0 ↔ t.x₂⁻¹ * w * t.x₂ ∈ t.Qv 2 := by
    intro w; have := hQx 0 w; rwa [sub_zero] at this
  have h20 : ∀ w, w ∈ t.Qv 2 ↔ t.x₂⁻¹ * w * t.x₂ ∈ t.Qv 0 := by
    intro w; have := hQx 2 w; rwa [sub_self] at this
  obtain ⟨R', hR', hrel⟩ : ∃ R' : Subgroup G, (∀ y, y ∈ R' ↔ t.x₂⁻¹ * y * t.x₂ ∈ R) ∧
      (t.Zv 1).relIndex R' = (t.Zv 1).relIndex R := by
    refine ⟨R.map (MulAut.conj t.x₂).toMonoidHom, fun y => mem_map_conj_iff, ?_⟩
    have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj t.x₂).toMonoidHom)
      (t.Zv 1) R (MulAut.conj t.x₂).injective
    have hZmap : (t.Zv 1).map (MulAut.conj t.x₂).toMonoidHom = t.Zv 1 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hx₂Z
    rwa [hZmap] at h
  obtain ⟨hZR', hRA', hRmem', hRQ'⟩ := t6f_conj_data hx₂Q hx₂Z h02 h20 hR' hZR hRA hRmem hRQ
  have hZQ : t.Zv 1 ≤ t.Qv 1 := t.Zv_le_Qv 1
  have hQN : t.Qv 1 ≤ normalizer (t.Zv 1 : Set G) :=
    (t.Qv_le_Gv_self 1).trans (t.Gv_le_normalizer_Zv 1)
  have hdata : t6f_Data (t.Qv 0) (t.Qv 1) (t.Qv 2) (t.Zv 1) R R' :=
    ⟨hD, hZQ, hQN, hAA, hZR, hRA, hRmem, hRQ, hZR', hRA', hRmem', hRQ'⟩
  have hL2Z : L2 ≤ normalizer (t.Zv 1 : Set G) := by
    have h1 : L2 ≤ t.Gv 1 := by rw [t.Gv_one]; exact le_sup_left
    exact h1.trans (t.Gv_le_normalizer_Zv 1)
  have hP0N : L2 ≤ normalizer ((R' ⊔ R : Subgroup G) : Set G) := fun l hl =>
    t6f_mem_normalizer_P0 hdata (hL2P hl) (hL2Z hl)
  have hQ2 : ∀ p ∈ pCoreOf 2 L2, ∀ v ∈ R' ⊔ R, ⁅p, v⁆ ∈ t.Zv 1 := fun p hp v hv =>
    t6f_comm_P0 hdata p (t.tl_pCoreOf_le_Qv_one hfr.hF.1 hp) v hv
  have hbound : (t.Zv 1).relIndex (R' ⊔ R) ≤ (2 ^ (2 * a + 1)) ^ 2 := by
    rw [t6f_relIndex_sup hdata, hrel, sq]
    exact Nat.mul_le_mul hRidx hRidx
  have htriv : ∀ l ∈ L2, ∀ v ∈ R' ⊔ R, ⁅l, v⁆ ∈ t.Zv 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨l, hl, v, hv, hne⟩ := hcon
    have h1 := St84.two_pow_le_relIndex_of_nontrivial (by omega : 1 ≤ f) hfr.hL2
      (t6f_isElemSec hdata) (le_inf hP0N hL2Z) hQ2 ⟨l, hl, v, hv, hne⟩
    have h2 : (2 ^ (2 * a + 1)) ^ 2 < 2 ^ (2 * f) := by
      rw [← pow_mul]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact absurd (h1.trans hbound) (not_le.mpr h2)
  have hL2R : L2 ≤ normalizer (R : Set G) := fun l hl =>
    t6f_mem_normalizer_of_comm hZR (fun y hy => htriv l hl y (mem_sup_right hy))
      (fun y hy => htriv l⁻¹ (inv_mem hl) y (mem_sup_right hy))
  have hQR : t.Qv 1 ≤ normalizer (R : Set G) := fun q hq =>
    t6f_mem_normalizer_of_comm hZR (fun y hy => hRQ q hq y hy)
      (fun y hy => hRQ q⁻¹ (inv_mem hq) y hy)
  have hKR : t.K ≤ normalizer (R : Set G) := fun k hk =>
    t6f_mem_normalizer_R (t.Gv_le_normalizer_Qv 0 (t.K_le_Gv 0 hk))
      (t.Gv_le_normalizer_Qv 1 (t.K_le_Gv 1 hk)) (t.Gv_le_normalizer_Qv 2 (t.K_le_Gv 2 hk)) hRmem
  have hSR : S ≤ normalizer (R : Set G) :=
    (t.tl_S_eq_sup_Qv_one hfr).le.trans (sup_le hQR (inf_le_right.trans hL2R))
  have hBR : bigB L1 L2 S ≤ normalizer (R : Set G) :=
    t.hBsplit.le.trans (sup_le (sup_le hSR (le_sup_left.trans hKR)) (le_sup_right.trans hKR))
  have hP2R : P2 L1 L2 S ≤ normalizer (R : Set G) := sup_le hL2R hBR
  have hx₂R : t.x₂ ∈ normalizer (R : Set G) := hP2R t.track.x₂_mem
  have hRZ : R ≤ t.Zv 1 := by
    intro y hy
    have h1 := (mem_normalizer_iff.mp (inv_mem hx₂R) y).mp hy
    rw [inv_inv] at h1
    have hy' : y ∈ R' := (hR' y).mpr h1
    rw [← hD]
    exact mem_inf.mpr ⟨(mem_inf.mp (hRA' hy')).2, (mem_inf.mp (hRA hy)).2⟩
  exact hRne (le_antisymm hRZ hZR)

theorem false_of_t_eq_six {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1)
    (hwlog : pCoreOf 2 (t.Gw (-2) 4) = ⊥)
    (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) (hZ2' : ¬ t.Zv (-1) ≤ t.Gv 2)
    (hcard0 : Nat.card (t.Zv 1) = 2 ^ f * 2 ^ f)
    (hcard : Nat.card (t.Zv 0) = 2 ^ f) (hZ10 : t.Zv 0 ≤ t.Zv 1)
    (hN1 : ∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 0) :
    False := by
  have hV := t.two_pow_le_relIndex_VZ hfr hZ0 hZ10 hcard0 hN1
  have hVQ := t.VZ_le_Qv_zero hfr hZ0
  have hQ0 := t.card_Qv_zero_le_of_t6 hfr hwlog
  have hD := t.Qv_zero_inf_Qv_two_eq_of_t6 hfr hwlog hZ0 hcard0
  have hqr : 2 * a + 1 < f := by
    have hZV : t.Zv 0 ≤ t.VZ := hZ10.trans t.Zv_one_le_VZ
    have hcardV : Nat.card t.VZ = (t.Zv 0).relIndex t.VZ * 2 ^ f := by
      rw [← hcard, ← Subgroup.relIndex_mul_card (t.Zv 0) t.VZ, inf_eq_left.mpr hZV]
    have hle : (t.Zv 0).relIndex t.VZ * 2 ^ f ≤ (2 ^ f) ^ 3 * (2 ^ (2 * a + 1)) ^ 2 := by
      rw [← hcardV]
      exact (Subgroup.card_le_of_le hVQ).trans hQ0
    have h1 : 2 ^ (4 * (2 * a + 1) + f) ≤ 2 ^ (3 * f + 2 * (2 * a + 1)) := by
      calc 2 ^ (4 * (2 * a + 1) + f) = 2 ^ (4 * (2 * a + 1)) * 2 ^ f := pow_add _ _ _
        _ ≤ (t.Zv 0).relIndex t.VZ * 2 ^ f := Nat.mul_le_mul_right _ hV
        _ ≤ (2 ^ f) ^ 3 * (2 ^ (2 * a + 1)) ^ 2 := hle
        _ = 2 ^ (3 * f + 2 * (2 * a + 1)) := by rw [← pow_mul, ← pow_mul, ← pow_add]; ring_nf
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    omega
  have hL2P := t.L2_le_normalizer_A hfr hZ0 hZ2'
  have hAA := t.commutator_mem_of_mem_A hfr hD
  have hA := t.Qv_one_inf_Qv_two_ne_of_t6 hfr hZ0 hZ2' hZ10 hcard0 hN1
  obtain ⟨R, hZR, hRA, hRne, hRmem, hRQ, -, hRidx⟩ := t.exists_R_of_t6 hfr hD hZ0 hA
  exact t.false_of_R hfr hqr hD hL2P hAA hZR hRA hRne hRmem hRQ hRidx

end Track

end CFSG.Quasithin.Stroth.Rq
