module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackBasic
import CFSG.Quasithin.Recognition.Stroth.Str83RqTorus
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexL2
import CFSG.Quasithin.Recognition.Stroth.BenderSylow
import CFSG.Quasithin.Recognition.Stroth.F112Tree
public import CFSG.Quasithin.Background.B1MoreTwelveA

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

private theorem conj_eq_of_mem_centralizerMod {L D Z W : Subgroup G} {k : G}
    (hk : k ∈ centralizerMod Z L D) (hWD : W ≤ D) (hkW : k ∈ normalizer (W : Set G))
    (hWZ : W ⊓ Z = ⊥) {w : G} (hw : w ∈ W) : k * w * k⁻¹ = w := by
  have h1 : k * w * k⁻¹ * w⁻¹ ∈ Z := hk.2.2 w (hWD hw)
  have h2 : k * w * k⁻¹ * w⁻¹ ∈ W :=
    W.mul_mem ((mem_normalizer_iff.mp hkW w).mp hw) (W.inv_mem hw)
  have h3 : k * w * k⁻¹ * w⁻¹ = 1 := by
    have : k * w * k⁻¹ * w⁻¹ ∈ W ⊓ Z := ⟨h2, h1⟩
    rw [hWZ] at this
    exact this
  calc k * w * k⁻¹ = k * w * k⁻¹ * w⁻¹ * w := by group
    _ = w := by rw [h3, one_mul]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem D2_le_K : t.D2 ≤ t.K := le_sup_right

private theorem D2_le_Gv (i : ℤ) : t.D2 ≤ t.Gv i := t.D2_le_K.trans (t.K_le_Gv i)

private theorem K_le_normalizer_pCoreOf_Gw (a b : ℤ) :
    t.K ≤ normalizer (pCoreOf 2 (t.Gw a b) : Set G) :=
  (t.K_le_Gw a b).trans (le_normalizer_pCoreOf 2 _)

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

private theorem exists_D2_conj_ne {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card (t.Zv 0) = 2 ^ f)
    (hN3 : ∀ z ∈ t.Zv 0, z ≠ 1 → ∀ z' ∈ t.Zv 0, z' ≠ 1 → ∃ d ∈ t.D2, d * z * d⁻¹ = z') :
    ∃ d ∈ t.D2, ∃ z ∈ t.Zv 0, d * z * d⁻¹ ≠ z := by
  by_contra hcon
  push Not at hcon
  have h4 : 4 ≤ Nat.card (t.Zv 0) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have key : ∀ z ∈ t.Zv 0, z ≠ 1 → ∀ z' ∈ t.Zv 0, z' ≠ 1 → z' = z := by
    intro z hz hz1 z' hz' hz'1
    obtain ⟨d, hd, hdz⟩ := hN3 z hz hz1 z' hz' hz'1
    rw [← hdz]
    exact hcon d hd z hz
  have hcard' : Nat.card (t.Zv 0) = Set.ncard ((t.Zv 0 : Subgroup G) : Set G) :=
    Nat.card_coe_set_eq _
  by_cases hbot : ∃ z ∈ t.Zv 0, z ≠ 1
  · obtain ⟨z, hz, hz1⟩ := hbot
    have hsub : ((t.Zv 0 : Subgroup G) : Set G) ⊆ {1, z} := by
      intro y hy
      by_cases hy1 : y = 1
      · simp [hy1]
      · right
        exact key z hz hz1 y hy hy1
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, z} : Set G).ncard ≤ 2 := by
      calc ({1, z} : Set G).ncard ≤ ({z} : Set G).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  · push Not at hbot
    have hsub : ((t.Zv 0 : Subgroup G) : Set G) ⊆ {1} := by
      intro y hy
      exact hbot y hy
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at h1
    omega

private theorem Zv_zero_inf_Gv_eq_bot {j : ℤ} (hj : ¬ t.Zv 0 ≤ t.Gv j)
    (hN3 : ∀ z ∈ t.Zv 0, z ≠ 1 → ∀ z' ∈ t.Zv 0, z' ≠ 1 → ∃ d ∈ t.D2, d * z * d⁻¹ = z') :
    t.Zv 0 ⊓ t.Gv j = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨hz0, hzj⟩ := Subgroup.mem_inf.mp hz
  by_contra hz1
  apply hj
  intro z' hz'
  by_cases hz'1 : z' = 1
  · rw [hz'1]
    exact one_mem _
  · obtain ⟨d, hd, hdz⟩ := hN3 z hz0 hz1 z' hz' hz'1
    rw [← hdz]
    exact mul_mem (mul_mem (t.D2_le_Gv j hd) hzj) (inv_mem (t.D2_le_Gv j hd))

private theorem Zv_one_inf_Gv_neg_two_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) (hZ2 : t.Zv (-1) ≤ t.Gw (-3) 1) (hZ2' : ¬ t.Zv (-1) ≤ t.Gv 2)
    (hN2 : ∀ s ∈ S, s ∉ t.Qv 1 → ∀ z ∈ t.Zv 1, s * z * s⁻¹ = z → z ∈ t.Zv 0) :
    t.Zv 1 ⊓ t.Gv (-2) ≤ t.Zv 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : IsPGroup 2 ↥(t.Zv 1 ⊓ t.Gv (-2)) := (t.isPGroup_Zv 1).to_le inf_le_left
  have hXw : t.Zv 1 ⊓ t.Gv (-2) ≤ t.Gw (-2) 3 := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i = -2 ∨ -1 ≤ i by omega) with rfl | h3
    · exact hy2
    · exact mem_win_iff.mp (hZ0 hy1) i h3 h2
  have hXQ : t.Zv 1 ⊓ t.Gv (-2) ≤ t.Qv (-1) :=
    t.le_Qv_of_le_Gw hfr (u := -2) (w := 3) (j := -1) (by norm_num) (by norm_num) hX hXw
  have hnot : ¬ t.Zv (-1) ≤ t.Qv 1 := fun h =>
    hZ2' (h.trans (t.Qv_one_le_Gv_two hfr))
  obtain ⟨y, hy, hyQ⟩ := Set.not_subset.mp hnot
  have hyS : y ∈ S := by
    have h1 : t.Zv (-1) ≤ t.Gw 0 1 := hZ2.trans (win_mono (by norm_num) le_rfl)
    have h2 := t.le_pCoreOf_Gw hfr (u := 0) (w := 1) (by norm_num) (t.isPGroup_Zv (-1)) h1
    rw [t.pCoreOf_Gw_zero_one hfr] at h2
    exact h2 hy
  intro z hz
  obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
  have hzQ : z ∈ t.Qv (-1) := hXQ hz
  have hcomm : z * y = y * z :=
    Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer (-1) hy) z hzQ
  have hconj : y * z * y⁻¹ = z := by
    rw [← hcomm, mul_inv_cancel_right]
  exact hN2 y hyS hyQ z hz1 hconj

private theorem pCoreOf_Gw_neg_three_five_inf_Zv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) (hZ2 : t.Zv (-1) ≤ t.Gw (-3) 1) (hZ2' : ¬ t.Zv (-1) ≤ t.Gv 2)
    (hN2 : ∀ s ∈ S, s ∉ t.Qv 1 → ∀ z ∈ t.Zv 1, s * z * s⁻¹ = z → z ∈ t.Zv 0)
    (hZ1r : ¬ t.Zv 0 ≤ t.Gv 4)
    (hN3 : ∀ z ∈ t.Zv 0, z ≠ 1 → ∀ z' ∈ t.Zv 0, z' ≠ 1 → ∃ d ∈ t.D2, d * z * d⁻¹ = z') :
    pCoreOf 2 (t.Gw (-3) 5) ⊓ t.Zv 1 = ⊥ := by
  have hW2 : pCoreOf 2 (t.Gw (-3) 5) ≤ t.Gv (-2) :=
    (pCoreOf_le 2 _).trans (win_le_qv (by norm_num) (by norm_num))
  have hW4 : pCoreOf 2 (t.Gw (-3) 5) ≤ t.Gv 4 :=
    (pCoreOf_le 2 _).trans (win_le_qv (by norm_num) (by norm_num))
  have h1 : pCoreOf 2 (t.Gw (-3) 5) ⊓ t.Zv 1 ≤ t.Zv 0 := by
    refine (inf_le_inf_right _ hW2).trans ?_
    rw [inf_comm]
    exact t.Zv_one_inf_Gv_neg_two_le hfr hZ0 hZ2 hZ2' hN2
  have h2 : pCoreOf 2 (t.Gw (-3) 5) ⊓ t.Zv 1 ≤ t.Gv 4 := inf_le_left.trans hW4
  have h3 := t.Zv_zero_inf_Gv_eq_bot hZ1r hN3
  exact le_bot_iff.mp (h3 ▸ le_inf h1 h2)

private theorem pCoreOf_Gw_neg_five_three_inf_Zv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) (hZ2 : t.Zv (-1) ≤ t.Gw (-3) 1) (hZ2' : ¬ t.Zv (-1) ≤ t.Gv 2)
    (hN2 : ∀ s ∈ S, s ∉ t.Qv 1 → ∀ z ∈ t.Zv 1, s * z * s⁻¹ = z → z ∈ t.Zv 0)
    (hZ1l : ¬ t.Zv 0 ≤ t.Gv (-4))
    (hN3 : ∀ z ∈ t.Zv 0, z ≠ 1 → ∀ z' ∈ t.Zv 0, z' ≠ 1 → ∃ d ∈ t.D2, d * z * d⁻¹ = z') :
    pCoreOf 2 (t.Gw (-5) 3) ⊓ t.Zv 1 = ⊥ := by
  have hW2 : pCoreOf 2 (t.Gw (-5) 3) ≤ t.Gv (-2) :=
    (pCoreOf_le 2 _).trans (win_le_qv (by norm_num) (by norm_num))
  have hW4 : pCoreOf 2 (t.Gw (-5) 3) ≤ t.Gv (-4) :=
    (pCoreOf_le 2 _).trans (win_le_qv (by norm_num) (by norm_num))
  have h1 : pCoreOf 2 (t.Gw (-5) 3) ⊓ t.Zv 1 ≤ t.Zv 0 := by
    refine (inf_le_inf_right _ hW2).trans ?_
    rw [inf_comm]
    exact t.Zv_one_inf_Gv_neg_two_le hfr hZ0 hZ2 hZ2' hN2
  have h2 : pCoreOf 2 (t.Gw (-5) 3) ⊓ t.Zv 1 ≤ t.Gv (-4) := inf_le_left.trans hW4
  have h3 := t.Zv_zero_inf_Gv_eq_bot hZ1l hN3
  exact le_bot_iff.mp (h3 ▸ le_inf h1 h2)

private theorem card_mul_card_le_card_sup_of_inf_eq_bot {V D : Subgroup G} (h : V ⊓ D = ⊥) :
    Nat.card V * Nat.card D ≤ Nat.card ↥(V ⊔ D) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p : ↥V × ↥D => (⟨(p.1 : G) * p.2,
    mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩ : ↥(V ⊔ D))) ?_
  rintro ⟨v, d⟩ ⟨v', d'⟩ hvd
  have h1 : (v : G) * d = v' * d' := congrArg Subtype.val hvd
  have h2 : (v' : G)⁻¹ * v = d' * (d : G)⁻¹ := by
    calc (v' : G)⁻¹ * v = (v' : G)⁻¹ * (v * d) * (d : G)⁻¹ := by group
      _ = (v' : G)⁻¹ * (v' * d') * (d : G)⁻¹ := by rw [h1]
      _ = d' * (d : G)⁻¹ := by group
  have h3 : (v' : G)⁻¹ * v ∈ V ⊓ D :=
    Subgroup.mem_inf.mpr ⟨V.mul_mem (V.inv_mem v'.2) v.2, h2 ▸ D.mul_mem d'.2 (D.inv_mem d.2)⟩
  rw [h, mem_bot] at h3
  have hv : (v : G) = v' := (inv_mul_eq_one.mp h3).symm
  have hd : (d : G) = d' := by
    rw [hv] at h1
    exact (mul_left_cancel h1)
  exact Prod.ext (Subtype.ext hv) (Subtype.ext hd)

private theorem card_le_of_le_Gw_left {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) (hv : ¬ Even v) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXw : X ≤ t.Gw (v - 1) v) :
    Nat.card X ≤ 2 ^ f * Nat.card ↥(X ⊓ t.Gv (v + 1)) := by
  have h1 := (t.inf_Gv_eq_inf_Qv hfr v hX).1 hXw
  have h2 := t.relIndex_Qv_le hfr v hX (Or.inl hXw)
  rw [if_neg hv] at h2
  have h3 := Subgroup.relIndex_mul_card (t.Qv v) X
  rw [inf_comm, ← h1] at h3
  rw [← h3]
  exact Nat.mul_le_mul_right _ h2

private theorem card_le_of_le_Gw_right {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) (hv : ¬ Even v) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXw : X ≤ t.Gw v (v + 1)) :
    Nat.card X ≤ 2 ^ f * Nat.card ↥(X ⊓ t.Gv (v - 1)) := by
  have h1 := (t.inf_Gv_eq_inf_Qv hfr v hX).2 hXw
  have h2 := t.relIndex_Qv_le hfr v hX (Or.inr hXw)
  rw [if_neg hv] at h2
  have h3 := Subgroup.relIndex_mul_card (t.Qv v) X
  rw [inf_comm, ← h1] at h3
  rw [← h3]
  exact Nat.mul_le_mul_right _ h2

private theorem card_pCoreOf_Gw_neg_three_three_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hwlog : pCoreOf 2 (t.Gw (-4) 4) = ⊥) :
    Nat.card (pCoreOf 2 (t.Gw (-3) 3)) ≤ 2 ^ f * 2 ^ f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPp : IsPGroup 2 (pCoreOf 2 (t.Gw (-3) 3)) := pCoreOf_isPGroup 2 _
  have hPle : pCoreOf 2 (t.Gw (-3) 3) ≤ t.Gw (-3) 3 := pCoreOf_le 2 _
  have hodd3 : ¬ Even (3 : ℤ) := by decide
  have hoddm3 : ¬ Even (-3 : ℤ) := by decide
  have hP23 : pCoreOf 2 (t.Gw (-3) 3) ≤ t.Gw (3 - 1) 3 :=
    hPle.trans (win_mono (by norm_num) le_rfl)
  have c1 := t.card_le_of_le_Gw_left hfr 3 hodd3 hPp hP23
  rw [show (3 : ℤ) + 1 = 4 by norm_num] at c1
  have hP₁p : IsPGroup 2 ↥(pCoreOf 2 (t.Gw (-3) 3) ⊓ t.Gv 4) := hPp.to_le inf_le_left
  have hP₁w : pCoreOf 2 (t.Gw (-3) 3) ⊓ t.Gv 4 ≤ t.Gw (-3) (-3 + 1) :=
    (inf_le_left.trans hPle).trans (win_mono le_rfl (by norm_num))
  have c2 := t.card_le_of_le_Gw_right hfr (-3) hoddm3 hP₁p hP₁w
  rw [show (-3 : ℤ) - 1 = -4 by norm_num] at c2
  have hle : (pCoreOf 2 (t.Gw (-3) 3) ⊓ t.Gv 4) ⊓ t.Gv (-4) ≤ t.Gw (-4) 4 := by
    intro y hy
    obtain ⟨⟨hyP, hy4⟩, hy4'⟩ := hy
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    by_cases hi : i = -4
    · subst hi
      exact hy4'
    by_cases hi' : i = 4
    · subst hi'
      exact hy4
    · exact mem_win_iff.mp (hPle hyP) i (by omega) (by omega)
  have hbot : (pCoreOf 2 (t.Gw (-3) 3) ⊓ t.Gv 4) ⊓ t.Gv (-4) = ⊥ := by
    have h := t.le_pCoreOf_Gw hfr (show (-4 : ℤ) < 4 by norm_num) (hP₁p.to_le inf_le_left) hle
    rw [hwlog] at h
    exact le_bot_iff.mp h
  rw [hbot, Subgroup.card_bot] at c2
  calc Nat.card (pCoreOf 2 (t.Gw (-3) 3))
      ≤ 2 ^ f * Nat.card ↥(pCoreOf 2 (t.Gw (-3) 3) ⊓ t.Gv 4) := c1
    _ ≤ 2 ^ f * (2 ^ f * 1) := Nat.mul_le_mul_left _ c2
    _ = 2 ^ f * 2 ^ f := by rw [mul_one]

private theorem Zv_zero_le_sup_pCoreOf {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hW : Nat.card (pCoreOf 2 (t.Gw (-3) 5)) = 2 ^ f)
    (hW' : Nat.card (pCoreOf 2 (t.Gw (-5) 3)) = 2 ^ f)
    (hmax : pCoreOf 2 (t.Gw (-5) 5) = ⊥) (hwlog : pCoreOf 2 (t.Gw (-4) 4) = ⊥)
    (hZ1 : t.Zv 0 ≤ t.Gw (-3) 3) :
    t.Zv 0 ≤ pCoreOf 2 (t.Gw (-3) 5) ⊔ pCoreOf 2 (t.Gw (-5) 3) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWp : IsPGroup 2 (pCoreOf 2 (t.Gw (-3) 5)) := pCoreOf_isPGroup 2 _
  have hW'p : IsPGroup 2 (pCoreOf 2 (t.Gw (-5) 3)) := pCoreOf_isPGroup 2 _
  have hWP : pCoreOf 2 (t.Gw (-3) 5) ≤ pCoreOf 2 (t.Gw (-3) 3) :=
    t.le_pCoreOf_Gw hfr (by norm_num) hWp
      ((pCoreOf_le 2 _).trans (win_mono le_rfl (by norm_num)))
  have hW'P : pCoreOf 2 (t.Gw (-5) 3) ≤ pCoreOf 2 (t.Gw (-3) 3) :=
    t.le_pCoreOf_Gw hfr (by norm_num) hW'p
      ((pCoreOf_le 2 _).trans (win_mono (by norm_num) le_rfl))
  have hZP : t.Zv 0 ≤ pCoreOf 2 (t.Gw (-3) 3) :=
    t.le_pCoreOf_Gw hfr (by norm_num) (t.isPGroup_Zv 0) hZ1
  have hdisj : pCoreOf 2 (t.Gw (-3) 5) ⊓ pCoreOf 2 (t.Gw (-5) 3) = ⊥ := by
    have hle : pCoreOf 2 (t.Gw (-3) 5) ⊓ pCoreOf 2 (t.Gw (-5) 3) ≤ t.Gw (-5) 5 := by
      intro y hy
      refine mem_win_iff.mpr fun i h1 h2 => ?_
      by_cases hi : -3 ≤ i
      · exact mem_win_iff.mp (pCoreOf_le 2 _ hy.1) i hi h2
      · exact mem_win_iff.mp (pCoreOf_le 2 _ hy.2) i h1 (by omega)
    have h := t.le_pCoreOf_Gw hfr (show (-5 : ℤ) < 5 by norm_num) (hWp.to_le inf_le_left) hle
    rw [hmax] at h
    exact le_bot_iff.mp h
  have hprod := card_mul_card_le_card_sup_of_inf_eq_bot hdisj
  have hP := t.card_pCoreOf_Gw_neg_three_three_le hfr hwlog
  have hsup : pCoreOf 2 (t.Gw (-3) 5) ⊔ pCoreOf 2 (t.Gw (-5) 3) = pCoreOf 2 (t.Gw (-3) 3) :=
    Subgroup.eq_of_le_of_card_ge (sup_le hWP hW'P) (by
      rw [hW, hW'] at hprod
      exact hP.trans hprod)
  rw [hsup]
  exact hZP

private theorem P1_le_normalizer_Z1 : P1 L1 L2 S ≤ normalizer (Z1 L1 L2 S : Set G) :=
  (le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)

private theorem P2_le_normalizer_Z2 : P2 L1 L2 S ≤ normalizer (Z2 L1 L2 S : Set G) :=
  (le_normalizer_pCoreOf 2 _).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)

private theorem Zv_neg_one_le_centralizerMod {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hZ2 : t.Zv (-1) ≤ t.Gw (-3) 1) (hZ10 : t.Zv 0 ≤ t.Zv 1)
    (hN1 : ∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 0) :
    t.Zv (-1) ≤ centralizerMod (t.Zv 1) (t.Gv 1) (t.Qv 0 ⊓ t.Qv 2) := by
  intro y hy
  have hyG : y ∈ t.Gv 1 := win_le_qv (by norm_num) le_rfl (hZ2 hy)
  refine mem_centralizerMod.mpr ⟨hyG, t.Gv_le_normalizer_Zv 1 hyG, fun u hu => ?_⟩
  have hZx : ∀ (i : ℤ) {w : G}, w ∈ t.Zv i ↔ t.x₁⁻¹ * w * t.x₁ ∈ t.Zv (-i) :=
    fun i _ => t.track.mem_qv_neg_iff P1_le_normalizer_Z1 P2_le_normalizer_Z2 i
  have hQx : ∀ (i : ℤ) {w : G}, w ∈ t.Qv i ↔ t.x₁⁻¹ * w * t.x₁ ∈ t.Qv (-i) :=
    fun i _ => t.track.mem_qv_neg_iff (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _) i
  have hz : t.x₁⁻¹ * y * t.x₁ ∈ t.Zv 1 := by
    have := (hZx (-1)).mp hy
    rwa [neg_neg] at this
  have hs : t.x₁⁻¹ * u * t.x₁ ∈ S := by
    have := (hQx 0).mp (mem_inf.mp hu).1
    rw [neg_zero, t.Qv_zero] at this
    exact Q1_le_S hfr.hF this
  have key := hN1 _ hs _ hz
  have e : (t.x₁⁻¹ * u * t.x₁) * (t.x₁⁻¹ * y * t.x₁) * (t.x₁⁻¹ * u * t.x₁)⁻¹ *
      (t.x₁⁻¹ * y * t.x₁)⁻¹ = t.x₁⁻¹ * (u * y * u⁻¹ * y⁻¹) * t.x₁ := by group
  rw [e] at key
  have key2 : u * y * u⁻¹ * y⁻¹ ∈ t.Zv 0 := (hZx 0).mpr (by rw [neg_zero]; exact key)
  have key3 := inv_mem key2
  rw [show (u * y * u⁻¹ * y⁻¹)⁻¹ = y * u * y⁻¹ * u⁻¹ by group] at key3
  exact hZ10 key3

private theorem Qv_one_le_normalizer_centralizerMod {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.Qv 1 ≤ normalizer (centralizerMod (t.Zv 1) (t.Gv 1) (t.Qv 0 ⊓ t.Qv 2) : Set G) := by
  have h1 : t.Qv 1 ≤ t.Gv 0 := by
    rw [t.Qv_one]
    exact ((Q2_le_S hfr.hF).trans (t.S_le_Gw_zero_one hfr.hF)).trans
      (win_le_qv le_rfl (by norm_num))
  have h2 : t.Qv 1 ≤ t.Gv 2 := t.Qv_one_le_Gv_two hfr
  refine le_normalizer_centralizerMod ((t.Qv_le_Gv_self 1).trans (t.Gv_le_normalizer_Zv 1))
    ((t.Qv_le_Gv_self 1).trans Subgroup.le_normalizer) fun x hx => ?_
  exact A4.mem_normalizer_inf (t.Gv_le_normalizer_Qv 0 (h1 hx))
    (t.Gv_le_normalizer_Qv 2 (h2 hx))

private theorem x₂_mem_normalizer_centralizerMod {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    t.x₂ ∈ normalizer (centralizerMod (t.Zv 1) (t.Gv 1) (t.Qv 0 ⊓ t.Qv 2) : Set G) := by
  have hx₂G : t.x₂ ∈ t.Gv 1 := by rw [t.Gv_one]; exact t.track.x₂_mem
  have hQx : ∀ (i : ℤ) (n : G), n ∈ t.Qv i ↔ t.x₂ * n * t.x₂⁻¹ ∈ t.Qv (2 - i) := by
    intro i n
    rw [t.track.mem_qv_two_sub_iff (le_normalizer_pCoreOf 2 _) (le_normalizer_pCoreOf 2 _) (2 - i),
      sub_sub_cancel, show t.x₂⁻¹ * (t.x₂ * n * t.x₂⁻¹) * t.x₂ = n by group]
  have hU : t.x₂ ∈ normalizer ((t.Qv 0 ⊓ t.Qv 2 : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro n
    simp only [SetLike.mem_coe, mem_inf]
    have h0 := hQx 0 n
    have h2 := hQx 2 n
    rw [sub_zero] at h0
    rw [sub_self] at h2
    rw [h0, h2]
    exact and_comm
  have := le_normalizer_centralizerMod (H := zpowers t.x₂)
    (zpowers_le.mpr (t.Gv_le_normalizer_Zv 1 hx₂G))
    (zpowers_le.mpr (Subgroup.le_normalizer hx₂G)) (zpowers_le.mpr hU)
  exact this (mem_zpowers _)

private theorem map_conj_eq_of_mem {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  rw [mem_map_conj_iff]
  have := mem_normalizer_iff.mp (inv_mem hg) y
  rw [inv_inv] at this
  exact this.symm

private theorem mem_normalizer_sup {H K : Subgroup G} {g : G}
    (hH : g ∈ normalizer (H : Set G)) (hK : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  F1.le_normalizer_sup (X := Subgroup.zpowers g) (zpowers_le.mpr hH) (zpowers_le.mpr hK)
    (mem_zpowers g)

private theorem pCoreOf_le_Qv_one (hF : Hyp111 L1 L2 S) : pCoreOf 2 L2 ≤ t.Qv 1 := by
  have h := Hyp111.pCoreOf_le_pCoreOf_vertex hF.symm
  rw [bigB_comm] at h
  rw [t.Qv_one]
  exact h

private theorem P2_le_normalizer_L2 (hF : Hyp111 L1 L2 S) :
    P2 L1 L2 S ≤ normalizer (L2 : Set G) := by
  have h := bigB_le_normalizer_of_hyp111 hF.symm
  rw [bigB_comm] at h
  exact sup_le le_normalizer h

private theorem odd_orderOf_of_mem_D2 {d : G} (hd : d ∈ t.D2) : Odd (orderOf d) :=
  Odd.of_dvd_nat t.hD2hall.2.1 (Subgroup.orderOf_dvd_natCard t.D2 hd)

private theorem D2_le_normalizer_Zv (i : ℤ) : t.D2 ≤ normalizer (t.Zv i : Set G) := by
  rw [t.Zv_eq i]
  exact (t.D2_le_Gv i).trans ((t.Gv_le_normalizer_Qv i).trans
    (A4.normalizer_le_normalizer_omegaOneCenterOf _))

private theorem D2_le_normalizer_T : t.D2 ≤ normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
  t.hD2hall.1.trans inf_le_right

private theorem Zv_le_S {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hZ2 : t.Zv (-1) ≤ t.Gw (-3) 1) : t.Zv (-1) ≤ S := by
  have h1 : t.Zv (-1) ≤ t.Gw 0 1 := hZ2.trans (win_mono (by norm_num) le_rfl)
  have h2 := t.le_pCoreOf_Gw hfr (show (0 : ℤ) < 1 by norm_num) (t.isPGroup_Zv (-1)) h1
  rwa [t.pCoreOf_Gw_zero_one hfr] at h2

private theorem D2_le_of_le_normalizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {C : Subgroup G} (hYC : t.Zv (-1) ≤ C)
    (hQC : t.Qv 1 ≤ normalizer (C : Set G)) (hxC : t.x₂ ∈ normalizer (C : Set G))
    (hZ2 : t.Zv (-1) ≤ t.Gw (-3) 1) (hZ2' : ¬ t.Zv (-1) ≤ t.Gv 2) :
    t.D2 ≤ C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf (S ⊓ L2) L2 := hfr.hF.1.h2.sylow
  have hQ2le : pCoreOf 2 L2 ≤ t.Qv 1 := t.pCoreOf_le_Qv_one hfr.hF.1
  have hx₂L2 : t.x₂ ∈ normalizer (L2 : Set G) :=
    P2_le_normalizer_L2 hfr.hF.1 t.track.x₂_mem
  have hx₂Q : t.x₂ ∈ normalizer (t.Qv 1 : Set G) := by
    have hx : t.x₂ ∈ t.Gv 1 := by
      rw [t.Gv_one]
      exact t.track.x₂_mem
    exact t.Gv_le_normalizer_Qv 1 hx
  have hTQ' : S ⊓ L2 ≤ normalizer (t.Qv 1 : Set G) := by
    have h : P2 L1 L2 S ≤ normalizer (t.Qv 1 : Set G) := by
      rw [← t.Gv_one]
      exact t.Gv_le_normalizer_Qv 1
    exact inf_le_right.trans (le_sup_left.trans h)
  have hYS : t.Zv (-1) ≤ S := t.Zv_le_S hfr hZ2
  have hYQ : ¬ t.Zv (-1) ≤ t.Qv 1 := fun h => hZ2' (h.trans (t.Qv_one_le_Gv_two hfr))
  have hSQ : S = t.Qv 1 ⊔ (S ⊓ L2) := by
    have h := eq_sup_pCoreOf_of_bender_right hfr.hF.1 hfr.hN
      (Or.inr (Or.inr ⟨f, hfr.hf, hfr.hL2⟩))
    rw [sup_comm] at h
    rw [t.Qv_one]
    exact h
  have hXN : t.D2 ≤ normalizer (((t.Zv (-1) ⊔ t.Qv 1) ⊓ (S ⊓ L2) : Subgroup G) : Set G) := by
    intro d hd
    refine A4.mem_normalizer_inf ?_ (t.D2_le_normalizer_T hd)
    exact mem_normalizer_sup (t.D2_le_normalizer_Zv (-1) hd)
      ((t.D2_le_Gv 1).trans (t.Gv_le_normalizer_Qv 1) hd)
  have hXnot : ¬ ((t.Zv (-1) ⊔ t.Qv 1) ⊓ (S ⊓ L2) ≤ pCoreOf 2 L2) := by
    intro hX
    apply hYQ
    intro y hy
    have hyS : y ∈ t.Qv 1 ⊔ (S ⊓ L2) := hSQ.le (hYS hy)
    obtain ⟨q, hq, τ, hτ, hyqτ⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hTQ').mp hyS
    have hτy : τ = q⁻¹ * y := by rw [hyqτ]; group
    have hτX : τ ∈ (t.Zv (-1) ⊔ t.Qv 1) ⊓ (S ⊓ L2) := by
      refine ⟨?_, hτ⟩
      rw [hτy]
      exact mul_mem (mem_sup_right (inv_mem hq)) (mem_sup_left hy)
    rw [hyqτ]
    exact mul_mem hq (hQ2le (hX hτX))
  have hKI : S ⊓ L2 ≤ (t.Zv (-1) ⊔ t.Qv 1) ⊓ (S ⊓ L2) ⊔ pCoreOf 2 L2 :=
    le_sup_pCoreOf_of_torus_of_l2 hfr.hf hfr.hL2 hTsyl t.hD2hall inf_le_right hXN hXnot
  have hTCQ : S ⊓ L2 ≤ C ⊔ t.Qv 1 := by
    refine hKI.trans (sup_le ?_ (hQ2le.trans le_sup_right))
    exact inf_le_left.trans (sup_le_sup_right hYC _)
  have hT'syl : IsSylowTwoOf ((S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom) L2 := by
    have h := IsSylowTwoOf.map_equiv (MulAut.conj t.x₂) hTsyl
    rwa [map_conj_eq_of_mem hx₂L2] at h
  have hT'CQ : (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom ≤ C ⊔ t.Qv 1 := by
    have h := Subgroup.map_mono (f := (MulAut.conj t.x₂).toMonoidHom) hTCQ
    rwa [map_conj_eq_of_mem (mem_normalizer_sup hxC hx₂Q)] at h
  have hne : S ⊓ L2 ≠ (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom := by
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
  have hL2CQ : L2 ≤ C ⊔ t.Qv 1 := by
    have h := le_sup_pCoreOf_of_sylow_ne_of_l2 (X := C ⊔ t.Qv 1) hfr.hf hfr.hL2 hTsyl hT'syl hne
      (hTCQ.trans le_sup_left) (hT'CQ.trans le_sup_left)
    exact h.trans (sup_le le_rfl (hQ2le.trans le_sup_right))
  intro d hd
  exact B1Red.mem_of_odd_orderOf_of_mem_sup (t.isPGroup_Qv 1) hQC
    (hL2CQ (F1.borelOf_le L2 S (t.hD2hall.1 hd))) (t.odd_orderOf_of_mem_D2 hd)

theorem false_of_t_eq_eight {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hW : Nat.card (pCoreOf 2 (t.Gw (-3) 5)) = 2 ^ f)
    (hW' : Nat.card (pCoreOf 2 (t.Gw (-5) 3)) = 2 ^ f)
    (hmax : pCoreOf 2 (t.Gw (-5) 5) = ⊥) (hwlog : pCoreOf 2 (t.Gw (-4) 4) = ⊥)
    (hZ0 : t.Zv 1 ≤ t.Gw (-1) 3) (hZ2 : t.Zv (-1) ≤ t.Gw (-3) 1)
    (hZ2' : ¬ t.Zv (-1) ≤ t.Gv 2)
    (hZ1 : t.Zv 0 ≤ t.Gw (-3) 3) (hZ1l : ¬ t.Zv 0 ≤ t.Gv (-4)) (hZ1r : ¬ t.Zv 0 ≤ t.Gv 4)
    (hcard : Nat.card (t.Zv 0) = 2 ^ f) (hZ10 : t.Zv 0 ≤ t.Zv 1)
    (hN1 : ∀ s ∈ S, ∀ z ∈ t.Zv 1, s * z * s⁻¹ * z⁻¹ ∈ t.Zv 0)
    (hN2 : ∀ s ∈ S, s ∉ t.Qv 1 → ∀ z ∈ t.Zv 1, s * z * s⁻¹ = z → z ∈ t.Zv 0)
    (hN3 : ∀ z ∈ t.Zv 0, z ≠ 1 → ∀ z' ∈ t.Zv 0, z' ≠ 1 → ∃ d ∈ t.D2, d * z * d⁻¹ = z') :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd, z, hz, hdz⟩ := t.exists_D2_conj_ne hfr.hf hcard hN3
  have hdC : d ∈ centralizerMod (t.Zv 1) (t.Gv 1) (t.Qv 0 ⊓ t.Qv 2) :=
    t.D2_le_of_le_normalizer hfr (t.Zv_neg_one_le_centralizerMod hfr hZ2 hZ10 hN1)
      (t.Qv_one_le_normalizer_centralizerMod hfr) (t.x₂_mem_normalizer_centralizerMod hfr)
      hZ2 hZ2' hd
  have hD0 : ∀ {u w : ℤ}, u < 0 → 2 < w → pCoreOf 2 (t.Gw u w) ≤ t.Qv 0 ⊓ t.Qv 2 :=
    fun hu hw => le_inf
      (t.le_Qv_of_le_Gw hfr hu (by omega) (pCoreOf_isPGroup 2 _) (pCoreOf_le 2 _))
      (t.le_Qv_of_le_Gw hfr (by omega) hw (pCoreOf_isPGroup 2 _) (pCoreOf_le 2 _))
  have hcomm : ∀ {u w : ℤ}, u < 0 → 2 < w → pCoreOf 2 (t.Gw u w) ⊓ t.Zv 1 = ⊥ →
      ∀ x ∈ pCoreOf 2 (t.Gw u w), d * x * d⁻¹ = x :=
    fun hu hw hbot x hx => conj_eq_of_mem_centralizerMod hdC (hD0 hu hw)
      (t.K_le_normalizer_pCoreOf_Gw _ _ (t.D2_le_K hd)) hbot hx
  have hsub : pCoreOf 2 (t.Gw (-3) 5) ⊔ pCoreOf 2 (t.Gw (-5) 3) ≤
      centralizer ({d} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_centralizer_iff]
      rintro h rfl
      have := hcomm (by norm_num) (by norm_num)
        (t.pCoreOf_Gw_neg_three_five_inf_Zv_one hfr hZ0 hZ2 hZ2' hN2 hZ1r hN3) x hx
      calc h * x = h * x * h⁻¹ * h := by group
        _ = x * h := by rw [this]
    · rw [mem_centralizer_iff]
      rintro h rfl
      have := hcomm (by norm_num) (by norm_num)
        (t.pCoreOf_Gw_neg_five_three_inf_Zv_one hfr hZ0 hZ2 hZ2' hN2 hZ1l hN3) x hx
      calc h * x = h * x * h⁻¹ * h := by group
        _ = x * h := by rw [this]
  have hzd := mem_centralizer_iff.mp
    (hsub (t.Zv_zero_le_sup_pCoreOf hfr hW hW' hmax hwlog hZ1 hz)) d rfl
  exact hdz (by rw [hzd]; group)

end Track

end CFSG.Quasithin.Stroth.Rq
