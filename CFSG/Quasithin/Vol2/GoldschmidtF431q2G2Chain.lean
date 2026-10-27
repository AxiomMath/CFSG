module

public import CFSG.Quasithin.Vol2.GoldschmidtF431q2G2Model
public import CFSG.Quasithin.Vol2.GoldschmidtF431q2Syl

public section

namespace CFSG.Quasithin.H13.F431.G2Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F6 CFSG.Quasithin.F6.G22Perm
  CFSG.Quasithin.F6.G22Shape CFSG.Sporadic.Bridge

namespace Model

variable {k : Type} [Field k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1)

include hk2

theorem eq_z_of_central {p : G2Group k} (hp : p ∈ (lat h2 hk2).P₂) (hp1 : p ≠ 1)
    (hp2 : p * p = 1) (hc : ∀ q ∈ (lat h2 hk2).P₂, q * p = p * q) : p = sEl h2 26 := by
  have hpS := mem_of_isSylowTwoOf_of_central hp2 hp hc (isSylowTwoOf_S h2 hk2)
  rcases zs_lift h2 hk2 hpS (fun t ht => hc t ((lat h2 hk2).S_le_P₂ ht)) with h | h
  · exact absurd h hp1
  · exact h

theorem y_conj : g2HomC h2 (u33GenPG 4) * sEl h2 5 * (g2HomC h2 (u33GenPG 4))⁻¹ = sEl h2 8 :=
  conjG h2 hk2 (by norm_num) (by norm_num) (by norm_num) Tab.conjY_chk

theorem x_conj : g2HomC h2 (u33GenPG 3) * sEl h2 8 * (g2HomC h2 (u33GenPG 3))⁻¹ = sEl h2 26 :=
  conjG h2 hk2 (by norm_num) (by norm_num) (by norm_num) Tab.conjX_chk

theorem chain {w : G2Group k} (hw : w ∈ TpSub h2 hk2) (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    ∃ a ∈ (lat h2 hk2).P₂, ∃ b ∈ (lat h2 hk2).P₁, ∃ u ∈ (lat h2 hk2).S,
      a * w * a⁻¹ = u ∧ b * u * b⁻¹ = sEl h2 26 := by
  obtain ⟨i, hi, rfl⟩ := (mem_TpSub h2 hk2).1 hw
  have hii := (sEl_sq h2 hk2 (by omega : i < 64)).1 hw2
  have hi0 : i ≠ 0 := fun h => hw1 (h ▸ sEl_zero h2 hk2)
  have hS8 : sEl h2 8 ∈ (lat h2 hk2).S := sEl_mem_S h2 hk2 (by norm_num)
  have hyP := y_mem h2 hk2
  have hxP := x_mem h2 hk2
  have hSP : ∀ {j : ℕ}, j < 64 → sEl h2 j ∈ (lat h2 hk2).P₂ := fun hj =>
    (lat h2 hk2).S_le_P₂ (sEl_mem_S h2 hk2 hj)
  rcases Tab.inv_chk i hi hii hi0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hyP, _, hxP, _, hS8, y_conj h2 hk2, x_conj h2 hk2⟩
  · exact ⟨1, one_mem _, _, hxP, _, hS8, by simp, x_conj h2 hk2⟩
  · refine ⟨sEl h2 5, hSP (by norm_num), _, hxP, _, hS8, ?_, x_conj h2 hk2⟩
    rw [sEl_conj h2 hk2 (a := 5) (j := 12) (by norm_num) (by norm_num), Tab.conjS_chk.2.2.2]
  · refine ⟨g2HomC h2 (u33GenPG 4) * sEl h2 1, Subgroup.mul_mem _ hyP (hSP (by norm_num)), _, hxP,
      _, hS8, ?_, x_conj h2 hk2⟩
    calc g2HomC h2 (u33GenPG 4) * sEl h2 1 * sEl h2 21 *
          (g2HomC h2 (u33GenPG 4) * sEl h2 1)⁻¹ =
        g2HomC h2 (u33GenPG 4) * (sEl h2 1 * sEl h2 21 * (sEl h2 1)⁻¹) *
          (g2HomC h2 (u33GenPG 4))⁻¹ := by group
      _ = g2HomC h2 (u33GenPG 4) * sEl h2 5 * (g2HomC h2 (u33GenPG 4))⁻¹ := by
        rw [sEl_conj h2 hk2 (a := 1) (j := 21) (by norm_num) (by norm_num), Tab.conjS_chk.1]
      _ = sEl h2 8 := y_conj h2 hk2
  · refine ⟨g2HomC h2 (u33GenPG 4) * sEl h2 2, Subgroup.mul_mem _ hyP (hSP (by norm_num)), _, hxP,
      _, hS8, ?_, x_conj h2 hk2⟩
    calc g2HomC h2 (u33GenPG 4) * sEl h2 2 * sEl h2 24 *
          (g2HomC h2 (u33GenPG 4) * sEl h2 2)⁻¹ =
        g2HomC h2 (u33GenPG 4) * (sEl h2 2 * sEl h2 24 * (sEl h2 2)⁻¹) *
          (g2HomC h2 (u33GenPG 4))⁻¹ := by group
      _ = g2HomC h2 (u33GenPG 4) * sEl h2 5 * (g2HomC h2 (u33GenPG 4))⁻¹ := by
        rw [sEl_conj h2 hk2 (a := 2) (j := 24) (by norm_num) (by norm_num), Tab.conjS_chk.2.1]
      _ = sEl h2 8 := y_conj h2 hk2
  · exact ⟨1, one_mem _, 1, one_mem _, _, sEl_mem_S h2 hk2 (i := 26) (by norm_num), by simp,
      by simp⟩
  · refine ⟨g2HomC h2 (u33GenPG 4) * sEl h2 7, Subgroup.mul_mem _ hyP (hSP (by norm_num)), _, hxP,
      _, hS8, ?_, x_conj h2 hk2⟩
    calc g2HomC h2 (u33GenPG 4) * sEl h2 7 * sEl h2 31 *
          (g2HomC h2 (u33GenPG 4) * sEl h2 7)⁻¹ =
        g2HomC h2 (u33GenPG 4) * (sEl h2 7 * sEl h2 31 * (sEl h2 7)⁻¹) *
          (g2HomC h2 (u33GenPG 4))⁻¹ := by group
      _ = g2HomC h2 (u33GenPG 4) * sEl h2 5 * (g2HomC h2 (u33GenPG 4))⁻¹ := by
        rw [sEl_conj h2 hk2 (a := 7) (j := 31) (by norm_num) (by norm_num), Tab.conjS_chk.2.2.1]
      _ = sEl h2 8 := y_conj h2 hk2

end Model

end CFSG.Quasithin.H13.F431.G2Two
