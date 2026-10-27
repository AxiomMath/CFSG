module

public import CFSG.RankThree.PartOne.K133C.LinearPlane
public import CFSG.RankThree.PartOne.K133C.MatrixModel
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.KC.LinearNoninnerPlaneInner

public section

namespace CFSG.RankThree.PartOne.K133C

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.K133
  CFSG.RankThree.PartOne.OutStructure CFSG.RankThree.PartOne.S13K
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem center_bot_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (h : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have ha : a ∈ Subgroup.center X := h1 ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem det_eq_one_of_mem_statedSL {n : ℕ} {K : Type} [Field K] {A : GL (Fin n) K}
    (hA : A ∈ StatedSL n K) : (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hA

theorem good_of_model_PSL {X : Type} [Group X] [Finite X] {n m p : ℕ} (hn3 : 3 ≤ n) (hn4 : n ≤ 4)
    (hZ : Subgroup.center X = ⊥) (h : StatedClassicalModel X .PSL n 2 m) (hp : p.Prime)
    (h5 : 5 ≤ p) : Good p X := by
  have hdiag : ¬ p ∣ Nat.gcd n (2 ^ m - 1) := fun hd => by
    have := Nat.le_of_dvd (by omega) (hd.trans (Nat.gcd_dvd_left _ _))
    omega
  have hO := (outPNice_PSL_ge_three hp (by omega) hn3 h hdiag).toChain
  refine good_of_movingPlanes hp hZ hO fun P hP hc => ?_
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine movingPlane_of_matrix_model (StatedSL n K) e hp (d := n) ?_ (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) ?_ hP hc
  · intro c hcM
    have h1 := det_eq_one_of_mem_statedSL hcM
    have h2 := KCLinPlane.det_scalar_gl_units (n := n) (K := K) c
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    rw [← Matrix.GeneralLinearGroup.val_det_apply, h2] at h1
    simpa using h1
  · intro F hFM hFe hFc
    have : Finite F := Nat.finite_of_card_ne_zero (by rw [hFc]; positivity)
    obtain ⟨W, hstab, g, hg, x, hxF, hne⟩ :=
      exists_moving_radSub hp (by omega) (by omega) F hFe hFc
    exact ⟨radSub W, radSub_le_statedSL W, radSub_isPGroup W,
      fun y hy s hs => radSub_normalized (hstab y hy) (fun w hw => hstab y⁻¹ (F.inv_mem hy) w hw) hs,
      x, hxF, g, hg, hne⟩

theorem kf133ResMaxAt_leaf7_three (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf7 3) := by
  refine KF133ResMaxAt.of_goodRes hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hmod := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e0
  rw [hq2] at hmod
  exact (good_of_model_PSL (by norm_num) (by norm_num) (center_bot_of_simple hne) hmod hp h5).goodRes

theorem kf133ResMaxAt_leaf8_zero (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf8 0) := by
  refine KF133ResMaxAt.of_goodRes hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hmod := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e0
  rw [hq2] at hmod
  exact (good_of_model_PSL (by norm_num) (by norm_num) (center_bot_of_simple hne) hmod hp h5).goodRes

end CFSG.RankThree.PartOne.K133C
