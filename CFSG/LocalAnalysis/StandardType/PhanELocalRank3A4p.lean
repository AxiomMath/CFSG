module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A4pFrame
public import CFSG.ClassicalInvolution.Phan.SimplyConnected

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.ClassicalGroups.Unitary CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

private theorem plh_hermLin_apply (n : ℕ) (u v : Fin n → K) :
    hermLin K f n 0 n u v = herm (sg K f) u v := by
  unfold hermLin herm
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [if_pos ⟨Nat.zero_le _, i.isLt⟩, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

private theorem plh_perpB_eq_perp (hK : Nat.card K = (2 ^ f) ^ 2)
    (U : Submodule K (Fin 4 → K)) : perpB K f 4 0 4 U = perp (sg K f) U := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  ext v
  simp only [perpB, perp, Submodule.mem_iInf, LinearMap.mem_ker, Set.mem_setOf_eq]
  constructor
  · intro h u hu
    have h1 : herm (sg K f) u v = 0 := by
      have := h u hu
      rwa [plh_hermLin_apply K f] at this
    rw [herm_conj (sg K f) hσ.invol u v, h1, map_zero]
  · intro h u hu
    have h1 : herm (sg K f) v u = 0 := h u hu
    rw [plh_hermLin_apply K f, herm_conj (sg K f) hσ.invol v u, h1, map_zero]

theorem mem_genSet_a3_4p_iff (hK : Nat.card K = (2 ^ f) ^ 2) (x : FlagK K 4) :
    x ∈ genSet K f 4 [0, 4] [true] ↔ NondegFlag (sg K f) x := by
  have hfar : x ∈ farSet 4 [0, 4] := by
    intro i hi j hj
    have hi' : i < 2 := by simpa using hi
    interval_cases i
    · rw [show [0, 4].getD 0 0 = 0 from rfl, Vsub_zero, inf_bot_eq, finrank_bot]
      omega
    · rw [show [0, 4].getD 1 0 = 4 from rfl, Vsub_self, inf_top_eq, x.dim j hj]
      omega
  have hbu : ∀ r : ℕ, blockU K 4 [0, 4] x.E 0 r = x.E r := by
    intro r
    simp only [blockU, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, Nat.sub_self,
      Nat.zero_add, Vsub_self, Vsub_zero, inf_top_eq, sup_bot_eq]
  have hblock0 : blockOK K f 4 [0, 4] [true] x.E 0 ↔ NondegFlag (sg K f) x := by
    constructor
    · intro h r hr
      have hb := h r (by simpa only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
        Nat.sub_self, Nat.zero_add] using hr)
      rw [if_pos (show [true].getD 0 false = true from rfl), hbu r,
        show [0, 4].getD (0 + 1) 0 = 4 from rfl,
        show [0, 4].getD 0 0 = 0 from rfl, Vsub_zero] at hb
      rw [plh_perpB_eq_perp K f hK] at hb
      rw [nondeg_iff_rad_eq_bot]
      simpa only [rad] using hb
    · intro h r hr
      rw [if_pos (show [true].getD 0 false = true from rfl), hbu r,
        show [0, 4].getD (0 + 1) 0 = 4 from rfl,
        show [0, 4].getD 0 0 = 0 from rfl, Vsub_zero]
      have hb := h r (by simpa only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
        Nat.sub_self, Nat.zero_add] using hr)
      rw [nondeg_iff_rad_eq_bot] at hb
      simp only [rad] at hb
      rw [plh_perpB_eq_perp K f hK]
      exact hb
  have hiff : (∀ i, i + 1 < [0, 4].length → blockOK K f 4 [0, 4] [true] x.E i) ↔
      blockOK K f 4 [0, 4] [true] x.E 0 := by
    constructor
    · intro h; exact h 0 (by decide)
    · intro h i hi
      have hi0 : i = 0 := by
        have : i + 1 < 2 := by simpa using hi
        omega
      rw [hi0]; exact h
  simp only [genSet, Set.mem_setOf_eq]
  rw [hiff]
  exact ⟨fun h => hblock0.mp h.2, fun h => ⟨hfar, hblock0.mpr h⟩⟩

private theorem plh_flag_E_eq_spanAt (hσ : IsUnitaryInvolution (sg K f)) (x : FlagK K 4)
    (hx : NondegFlag (sg K f) x) (j : ℕ) :
    x.E j = (frameOfFlag hσ x hx).spanAt (Finset.univ.filter fun k : Fin 4 => k.val < j) := by
  have h := congrArg (fun y : FlagK K 4 => y.E j) (flagOfFrame_frameOfFlag hσ x hx)
  rw [← h]
  rfl

private noncomputable def plh_toFrame (hK : Nat.card K = (2 ^ f) ^ 2)
    (x : ↥(genSet K f 4 [0, 4] [true])) : Frame (sg K f) 4 :=
  frameOfFlag (isUnitaryInvolution_unitaryInvolution hK) x.1
    ((mem_genSet_a3_4p_iff K f hK x.1).mp x.2)

private noncomputable def plh_ofFrame (hK : Nat.card K = (2 ^ f) ^ 2)
    (c : Frame (sg K f) 4) : ↥(genSet K f 4 [0, 4] [true]) :=
  ⟨flagOfFrame (isUnitaryInvolution_unitaryInvolution hK) c,
    (mem_genSet_a3_4p_iff K f hK _).mpr
      (nondegFlag_flagOfFrame (isUnitaryInvolution_unitaryInvolution hK) c)⟩

private theorem plh_left_inv (hK : Nat.card K = (2 ^ f) ^ 2)
    (x : ↥(genSet K f 4 [0, 4] [true])) :
    plh_ofFrame K f hK (plh_toFrame K f hK x) = x := by
  apply Subtype.ext
  exact flagOfFrame_frameOfFlag (isUnitaryInvolution_unitaryInvolution hK) x.1 _

private theorem plh_right_inv (hK : Nat.card K = (2 ^ f) ^ 2) (c : Frame (sg K f) 4) :
    plh_toFrame K f hK (plh_ofFrame K f hK c) = c := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  exact (congrArg (frameOfFlag hσ (flagOfFrame hσ c)) (Subsingleton.elim _ _)).trans
    (frameOfFlag_flagOfFrame hσ c)

private theorem plh_adj_iff (hK : Nat.card K = (2 ^ f) ^ 2) (i : Fin 3)
    (x y : ↥(genSet K f 4 [0, 4] [true])) :
    ((flagSys K 3).restrict (genSet K f 4 [0, 4] [true])).adj i x y ↔
      (CFSG.ClassicalInvolution.Phan.frameSystem (sg K f) 3).adj i
        (plh_toFrame K f hK x) (plh_toFrame K f hK y) := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  rw [CFSG.ClassicalInvolution.Phan.frameSystem_adj]
  show (∀ j, j ≠ i.val + 1 → x.1.E j = y.1.E j) ↔
    ∀ k : Fin 4, k ≠ i.castSucc → k ≠ i.succ →
      (plh_toFrame K f hK x).line k = (plh_toFrame K f hK y).line k
  constructor
  · intro h k hk1 hk2
    have hk1' : k.val ≠ i.val := fun h' => hk1 (Fin.ext (by simpa using h'))
    have hk2' : k.val ≠ i.val + 1 := fun h' => hk2 (Fin.ext (by simpa using h'))
    show x.1.E (k.val + 1) ⊓ perp (sg K f) (x.1.E k.val) =
      y.1.E (k.val + 1) ⊓ perp (sg K f) (y.1.E k.val)
    rw [h (k.val + 1) (by omega), h k.val (by omega)]
  · intro h j hj
    have hx := (mem_genSet_a3_4p_iff K f hK x.1).mp x.2
    have hy := (mem_genSet_a3_4p_iff K f hK y.1).mp y.2
    rw [plh_flag_E_eq_spanAt K f hσ x.1 hx j,
      plh_flag_E_eq_spanAt K f hσ y.1 hy j]
    by_cases hjle : j ≤ i.val
    · refine Frame.spanAt_congr ?_
      intro k hk
      have hkv : k.val < j := by simpa using hk
      have hk1 : k ≠ i.castSucc := by
        intro h'; have h2 := congrArg Fin.val h'
        simp only [Fin.val_castSucc] at h2; omega
      have hk2 : k ≠ i.succ := by
        intro h'; have h2 := congrArg Fin.val h'
        simp only [Fin.val_succ] at h2; omega
      exact h k hk1 hk2
    · have hjge : i.val + 2 ≤ j := by omega
      refine Frame.spanAt_eq_of_agree hσ ?_
      intro k hk
      have hkv : j ≤ k.val := by
        by_contra hlt
        exact hk (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega)
      have hk1 : k ≠ i.castSucc := by
        intro h'; have h2 := congrArg Fin.val h'
        simp only [Fin.val_castSucc] at h2; omega
      have hk2 : k ≠ i.succ := by
        intro h'; have h2 := congrArg Fin.val h'
        simp only [Fin.val_succ] at h2; omega
      exact h k hk1 hk2

noncomputable def flagFrameIso (hK : Nat.card K = (2 ^ f) ^ 2) :
    ChamberIso ((flagSys K 3).restrict (genSet K f 4 [0, 4] [true]))
      (CFSG.ClassicalInvolution.Phan.frameSystem (sg K f) 3) where
  e := Equiv.refl (Fin 3)
  Φ :=
    { toFun := plh_toFrame K f hK
      invFun := plh_ofFrame K f hK
      left_inv := plh_left_inv K f hK
      right_inv := plh_right_inv K f hK }
  adj_iff := plh_adj_iff K f hK

theorem a3_4p_models (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((flagSys K 3).restrict (genSet K f 4 [0, 4] [true])).Connected ∧
      ((flagSys K 3).restrict (genSet K f 4 [0, 4] [true])).SimplyTwoConnected := by
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  constructor
  · exact (flagFrameIso K f hK).connected_iff.mpr
      (frameSystem_connected hσ hK (q := 2 ^ f) (by omega))
  · exact (flagFrameIso K f hK).simplyTwoConnected_iff.mpr
      (frameSystem_simplyTwoConnected hσ (q := 2 ^ f) hK hq 3)

end CFSG.ClassicalInvolution.Phan.PhanE

end
