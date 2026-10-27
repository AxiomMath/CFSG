module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrack
import CFSG.Quasithin.Recognition.Stroth.Str83RqTools
import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackMove
import CFSG.Quasithin.Recognition.Stroth.Str83RqArc
import CFSG.Quasithin.Recognition.Stroth.BenderSylow
import CFSG.Quasithin.Recognition.Stroth.F112Tree

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits
open CFSG.ComponentClassification.Asc76X CFSG.ComponentClassification.AschbacherToolkit.Bender

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem le_normalizer_inf' {H A B : Subgroup G} (hA : H ≤ normalizer (A : Set G))
    (hB : H ≤ normalizer (B : Set G)) : H ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  fun _ hh => inf_normalizer_le_normalizer_inf (mem_inf.mpr ⟨hA hh, hB hh⟩)

private theorem eq_bot_of_le_Gw {b : ℤ} (hmax : ∀ u : ℤ, pCoreOf 2 (t.Gw u (u + 2 * b + 1)) = ⊥)
    {u : ℤ} {X : Subgroup G} (hX : IsPGroup 2 X) (hXw : X ≤ t.Gw u (u + 2 * b + 1))
    (hN : t.Gw u (u + 2 * b + 1) ≤ normalizer (X : Set G)) : X = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_bot_iff.mp ((le_pCoreOf_of_le_normalizer 2 hXw hN hX).trans (hmax u).le)

private theorem Zv_le_Gw_of_even {b : ℤ} (hZ0 : t.Zv 0 ≤ t.Gw (-b) b) {v c d : ℤ} (hv : Even v)
    (hc : c = v - b) (hd : d = v + b) : t.Zv v ≤ t.Gw c d := by
  have h := Subgroup.map_mono (f := (MulAut.conj (t.edgeElt v)).toMonoidHom) hZ0
  rw [t.map_Zv_edgeElt, t.map_Gw_edgeElt, if_pos hv, if_pos hv, add_zero, ← sub_eq_add_neg] at h
  rwa [hc, hd]

private theorem Qv_one_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZL : L1 ≤ centralizer (t.Zv 0 : Set G)) :
    t.Qv 1 ≤ centralizer (t.Zv 0 : Set G) := by
  have hQ0 : t.Qv 0 ≤ centralizer (t.Zv 0 : Set G) := le_centralizer_iff.mp (t.Zv_le_centralizer 0)
  have hS : S ≤ t.Qv 0 ⊔ (S ⊓ L1) := by
    have h := eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
    rw [t.Qv_zero, sup_comm]
    exact h.le
  have hQ1 : t.Qv 1 ≤ S := by
    rw [t.Qv_one]
    exact F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hfr.hF)
  exact hQ1.trans (hS.trans (sup_le hQ0 (inf_le_right.trans hZL)))

private theorem Zv_le_Zv_of_comm {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {v w : ℤ} (hw : t.Zv v ≤ t.Gw (w - 1) (w + 1))
    (hc : ⁅t.Qv w, t.Zv v⁆ = ⊥) : t.Zv v ≤ t.Zv w := by
  have hQ : t.Zv v ≤ t.Qv w := t.le_Qv_of_le_Gw hfr (u := w - 1) (w := w + 1) (j := w)
    (by omega) (by omega) (t.isPGroup_Zv v) hw
  have hC : t.Qv w ≤ centralizer (t.Zv v : Set G) := commutator_eq_bot_iff_le_centralizer.mp hc
  intro z hz
  rw [t.Zv_eq w]
  refine mem_omegaOneCenterOf (hQ hz) (fun y hy => (mem_centralizer_iff.mp (hC hy) z hz).symm) ?_
  rw [t.Zv_eq v] at hz
  exact A4.sq_eq_one_of_mem_omegaOneCenterOf hz

theorem false_of_five_le_b {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {b : ℤ} (hb : 5 ≤ b) (hbo : Odd b) (hZ0 : t.Zv 0 ≤ t.Gw (-b) b)
    (hmax : ∀ u : ℤ, pCoreOf 2 (t.Gw u (u + 2 * b + 1)) = ⊥)
    (hZL : L1 ≤ centralizer (t.Zv 0 : Set G)) (hcard : 2 ^ f ≤ Nat.card (t.Zv 0))
    (hR : ⁅⁅t.Zv 0, t.Zv (-b)⁆, t.Zv 0⁆ = ⊥) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hbo
  have hev2 : Even (-b - 1) := ⟨-m - 1, by omega⟩
  have hev1 : Even (-b + 1) := ⟨-m, by omega⟩
  have hodd : ¬ Even (-b) := by
    rw [Int.not_even_iff_odd]
    exact ⟨-m - 1, by omega⟩
  have hQb := t.Qv_le_Gv hfr (-b)
  have hA : t.Zv 0 ⊓ t.Qv (-b) = ⊥ := by
    refine t.eq_bot_of_le_Gw hmax (u := -b - 1) ((t.isPGroup_Zv 0).to_le inf_le_left) ?_ ?_
    · intro y hy
      refine mem_win_iff.mpr fun i h1 h2 => ?_
      rcases (show i = -b - 1 ∨ -b ≤ i by omega) with rfl | h3
      · exact hQb.1 hy.2
      · exact mem_win_iff.mp (hZ0 hy.1) i h3 (by omega)
    · exact le_normalizer_inf' ((win_le_qv (by omega) (by omega)).trans (t.Gv_le_normalizer_Zv 0))
        ((win_le_qv (by omega) (by omega)).trans (t.Gv_le_normalizer_Qv (-b)))
  set E := pCoreOf 2 (t.Gw (-b) (-b + 1)) with hE
  have hZw : t.Zv 0 ≤ t.Gw (-b) (-b + 1) := hZ0.trans (win_mono le_rfl (by omega))
  have hQw : t.Qv (-b) ≤ t.Gw (-b) (-b + 1) := by
    intro y hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i = -b ∨ i = -b + 1 by omega) with rfl | rfl
    · exact t.Qv_le_Gv_self _ hy
    · exact hQb.2 hy
  have hZE : t.Zv 0 ≤ E := t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv 0) hZw
  have hQE : t.Qv (-b) ≤ E := t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Qv (-b)) hQw
  have hZN : t.Zv 0 ≤ normalizer (t.Qv (-b) : Set G) :=
    (hZ0.trans (win_le_qv (by omega) (by omega))).trans (t.Gv_le_normalizer_Qv (-b))
  have hEle : E ≤ t.Zv 0 ⊔ t.Qv (-b) := by
    have hidx := (t.relIndex_Qv_pCoreOf hfr (-b)).2
    rw [if_neg hodd] at hidx
    have hcE : Nat.card E = 2 ^ f * Nat.card (t.Qv (-b)) := by
      have h := Subgroup.relIndex_mul_card (t.Qv (-b)) E
      rw [inf_eq_left.mpr hQE, hidx] at h
      exact h.symm
    have hcZQ : Nat.card ↥(t.Zv 0 ⊔ t.Qv (-b)) = Nat.card (t.Zv 0) * Nat.card (t.Qv (-b)) := by
      have h := C5.card_sup_mul_card_inf_of_le_normalizer hZN
      rwa [hA, Subgroup.card_bot, mul_one] at h
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hZE hQE) ?_).symm.le
    rw [hcE, hcZQ]
    exact Nat.mul_le_mul_right _ hcard
  have hGL : t.Zv (-b) ⊓ centralizer (E : Set G) ≤ t.Zv (-b + 1) := by
    rintro y ⟨hyZ, hyC⟩
    set g := t.edgeElt (-b) with hg
    have h1 := t.map_Zv_edgeElt (-b) 1
    have h0 := t.map_Zv_edgeElt (-b) 0
    have hw := t.map_Gw_zero_one_edgeElt (-b)
    rw [if_neg hodd, show -b + 1 - 1 = -b by ring] at h1
    rw [if_neg hodd, sub_zero] at h0
    have hy1 : g⁻¹ * y * g ∈ t.Zv 1 := by
      rw [← h1] at hyZ
      exact mem_map_conj_iff.mp hyZ
    have hyC' : g⁻¹ * y * g ∈ centralizer (pCoreOf 2 (t.Gw 0 1) : Set G) := by
      rw [mem_centralizer_iff]
      intro p hp
      have hp' : g * p * g⁻¹ ∈ E := by
        rw [hE, ← hw, pCoreOf_map_mulEquiv 2 (MulAut.conj g) _]
        exact mem_map_conj_iff.mpr (by simpa [mul_assoc] using hp)
      have hc := mem_centralizer_iff.mp hyC _ hp'
      calc p * (g⁻¹ * y * g) = g⁻¹ * ((g * p * g⁻¹) * y) * g := by group
        _ = g⁻¹ * (y * (g * p * g⁻¹)) * g := by rw [hc]
        _ = g⁻¹ * y * g * p := by group
    rw [t.Zv_one] at hy1
    rw [t.Gw_zero_one hfr.hF] at hyC'
    have hbase := z2_inf_centralizer_le_z1 hfr.hF.1 ⟨hy1, hyC'⟩
    rw [← t.Zv_zero] at hbase
    rw [← h0, mem_map_conj_iff]
    exact hbase
  have hCZ : t.Zv (-b) ⊓ centralizer (t.Zv 0 : Set G) ≤ t.Zv (-b + 1) := by
    rintro y ⟨hyY, hyZ⟩
    refine hGL ⟨hyY, ?_⟩
    have hyQ : y ∈ centralizer (t.Qv (-b) : Set G) := t.Zv_le_centralizer (-b) hyY
    have h1 : zpowers y ≤ centralizer (t.Zv 0 : Set G) := zpowers_le.mpr hyZ
    have h2 : zpowers y ≤ centralizer (t.Qv (-b) : Set G) := zpowers_le.mpr hyQ
    have h3 : t.Zv 0 ⊔ t.Qv (-b) ≤ centralizer (zpowers y : Set G) :=
      sup_le (le_centralizer_iff.mp h1) (le_centralizer_iff.mp h2)
    exact zpowers_le.mp (le_centralizer_iff.mp (hEle.trans h3))
  have hRY : ⁅t.Zv 0, t.Zv (-b)⁆ ≤ t.Zv (-b) := by
    rw [commutator_le]
    intro z hz y hy
    have hzN : z ∈ normalizer (t.Zv (-b) : Set G) :=
      t.Gv_le_normalizer_Zv (-b) (win_le_qv (by omega) (by omega) (hZ0 hz))
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp hzN y).mp hy) (inv_mem hy)
  have hRm : ⁅t.Zv 0, t.Zv (-b)⁆ ≤ t.Zv (-b + 1) := fun x hx =>
    hCZ ⟨hRY hx, commutator_eq_bot_iff_le_centralizer.mp hR hx⟩
  have hmir : ⁅t.Zv (-b - 1), t.Zv (-1)⁆ ≤ t.Zv (-2) := by
    obtain ⟨y₀, -, -, -, -, hZmap⟩ := t.exists_reflection (-m - 1)
    have h := Subgroup.map_mono (f := (MulAut.conj y₀).toMonoidHom) hRm
    rw [Subgroup.map_commutator, hZmap, hZmap, hZmap,
      show 2 * (-m - 1) - 0 = -b - 1 by omega, show 2 * (-m - 1) - -b = -1 by omega,
      show 2 * (-m - 1) - (-b + 1) = -2 by omega] at h
    exact h
  have hc1 : ⁅t.Qv 1, t.Zv 0⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (t.Qv_one_le_centralizer hfr hZL)
  have hc2 : ⁅t.Qv (-1), t.Zv 0⁆ = ⊥ := by
    obtain ⟨y, -, -, -, hQm, hZm⟩ := t.exists_reflection 0
    have h := congrArg (Subgroup.map (MulAut.conj y).toMonoidHom) hc1
    rw [Subgroup.map_commutator, Subgroup.map_bot, hQm, hZm] at h
    simpa using h
  have hc3 : ⁅t.Qv (-b), t.Zv (-b - 1)⁆ = ⊥ := by
    have h := congrArg (Subgroup.map (MulAut.conj (t.edgeElt (-b - 1))).toMonoidHom) hc1
    rw [Subgroup.map_commutator, Subgroup.map_bot, t.map_Qv_edgeElt, t.map_Zv_edgeElt,
      if_pos hev2, if_pos hev2, show -b - 1 + 1 = -b by ring, add_zero] at h
    exact h
  have hYp : t.Zv (-b - 1) ≤ t.Gw (-2 * b - 1) (-1) :=
    t.Zv_le_Gw_of_even hZ0 hev2 (by ring) (by ring)
  have hYpY : t.Zv (-b - 1) ≤ t.Zv (-b) :=
    t.Zv_le_Zv_of_comm hfr (hYp.trans (win_mono (by omega) (by omega))) hc3
  have hZZ2 : t.Zv 0 ≤ t.Zv (-1) :=
    t.Zv_le_Zv_of_comm hfr (hZ0.trans (win_mono (by omega) (by omega))) hc2
  have hW1 : ⁅t.Zv 0, t.Zv (-b - 1)⁆ ≤ t.Zv (-b + 1) := (commutator_mono le_rfl hYpY).trans hRm
  have hW2 : ⁅t.Zv 0, t.Zv (-b - 1)⁆ ≤ t.Zv (-2) := by
    calc ⁅t.Zv 0, t.Zv (-b - 1)⁆ ≤ ⁅t.Zv (-1), t.Zv (-b - 1)⁆ := commutator_mono hZZ2 le_rfl
      _ = ⁅t.Zv (-b - 1), t.Zv (-1)⁆ := commutator_comm _ _
      _ ≤ t.Zv (-2) := hmir
  have hYm : t.Zv (-b + 1) ≤ t.Gw (1 - 2 * b) 1 := t.Zv_le_Gw_of_even hZ0 hev1 (by ring) (by ring)
  have hZ3 : t.Zv (-2) ≤ t.Gw (-2 - b) (-2 + b) := t.Zv_le_Gw_of_even hZ0 ⟨-1, by norm_num⟩ rfl rfl
  have hB1 : t.Zv (-b + 1) ⊓ t.Zv (-2) = ⊥ := by
    refine t.eq_bot_of_le_Gw hmax (u := 1 - 2 * b) ((t.isPGroup_Zv _).to_le inf_le_left) ?_ ?_
    · intro y hy
      refine mem_win_iff.mpr fun i h1 h2 => ?_
      rcases (show i ≤ 1 ∨ 2 ≤ i by omega) with h3 | h3
      · exact mem_win_iff.mp (hYm hy.1) i (by omega) h3
      · exact mem_win_iff.mp (hZ3 hy.2) i (by omega) (by omega)
    · exact le_normalizer_inf' ((win_le_qv (by omega) (by omega)).trans (t.Gv_le_normalizer_Zv _))
        ((win_le_qv (by omega) (by omega)).trans (t.Gv_le_normalizer_Zv _))
  have hB2 : t.Zv (-b + 1) ⊓ t.Zv (-b - 1) = ⊥ := by
    refine t.eq_bot_of_le_Gw hmax (u := -2 * b - 1) ((t.isPGroup_Zv _).to_le inf_le_left) ?_ ?_
    · intro y hy
      refine mem_win_iff.mpr fun i h1 h2 => ?_
      rcases (show 1 - 2 * b ≤ i ∨ i ≤ -1 by omega) with h3 | h3
      · exact mem_win_iff.mp (hYm hy.1) i h3 (by omega)
      · exact mem_win_iff.mp (hYp hy.2) i (by omega) h3
    · exact le_normalizer_inf' ((win_le_qv (by omega) (by omega)).trans (t.Gv_le_normalizer_Zv _))
        ((win_le_qv (by omega) (by omega)).trans (t.Gv_le_normalizer_Zv _))
  have hWne : ⁅t.Zv 0, t.Zv (-b - 1)⁆ ≠ ⊥ := by
    intro hW0
    have hYpC : t.Zv (-b - 1) ≤ centralizer (t.Zv 0 : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hW0)
    have hYpm : t.Zv (-b - 1) ≤ t.Zv (-b + 1) := fun y hy => hCZ ⟨hYpY hy, hYpC hy⟩
    exact t.Zv_ne_bot hfr.hF (-b - 1) (le_bot_iff.mp (hB2 ▸ le_inf hYpm le_rfl))
  exact hWne (le_bot_iff.mp (hB1 ▸ le_inf hW1 hW2))

end Track

end CFSG.Quasithin.Stroth.Rq
