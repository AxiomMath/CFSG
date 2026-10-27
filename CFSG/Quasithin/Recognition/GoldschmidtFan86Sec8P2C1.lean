module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Cal
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Fix

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem fix_ball_two (F : FanTree Γ G) (h : Fan71c F L) {a b k : Fin 5} (hak : a ≠ k)
    (hbk : b ≠ k) {w : V} (hw : Γ.dist (D.beta k) w ≤ 2) :
    (L.z (D.alpha a) * L.z (D.alpha b)) • w = w := by
  have hw' : Γ.dist w (D.beta k) ≤ 2 := by rw [SimpleGraph.dist_comm]; exact hw
  rw [mul_smul]
  rcases IsTree.dist_adj_cases F.isTree (r := w) (D.adj_start_beta k) with h1 | h1
  · rw [D.fix_alpha_side F h b (m := k) (by omega) (by omega),
      D.fix_alpha_side F h a (m := k) (by omega) (by omega)]
  · have hb : Γ.dist w (D.beta k) + 1 = Γ.dist w α := h1.symm
    have hcases : Γ.dist w (D.beta k) = 0 ∨ Γ.dist w (D.beta k) = 1 ∨
        Γ.dist w (D.beta k) = 2 := by omega
    rcases hcases with h0 | h0 | h0
    · rw [D.fix_below_one F h hbk hb (by omega), D.fix_below_one F h hak hb (by omega)]
    · rw [D.fix_below_one F h hbk hb (by omega), D.fix_below_one F h hak hb (by omega)]
    · have := D.fix_depth_two F h hak hbk h0 (by omega)
      rwa [mul_smul] at this

open Fin.NatCast in
theorem calpha_mem_zpowers (F : FanTree Γ G) (h7 : Fan7 F L) {c : G} (hc : c ∈ D.calpha)
    {i : Fin 5} (hfix : ∀ w, Γ.dist (D.beta i) w ≤ 2 → c • w = w) :
    c ∈ Subgroup.zpowers (L.z α) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hcm : Commute c D.x :=
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 D.x (by simp)).symm
  have hspread : ∀ (k : Fin 5) (w : V), Γ.dist (D.beta k) w ≤ 2 → c • w = w := by
    intro k w hw
    have hy : (D.x ^ (k - i).val)⁻¹ • D.beta i = D.beta k := by
      have := D.x_pow_inv_smul_vert F h71c (k - i).val i (m := 1) (by norm_num)
      rw [Fin.cast_val_eq_self, show i + (k - i) = k by abel] at this
      exact this
    have hcy : c * (D.x ^ (k - i).val)⁻¹ = (D.x ^ (k - i).val)⁻¹ * c :=
      ((hcm.pow_right _).inv_right).eq
    have hY : D.x ^ (k - i).val • D.beta k = D.beta i := by
      rw [← hy, smul_inv_smul]
    have hw' : Γ.dist (D.beta i) (D.x ^ (k - i).val • w) ≤ 2 := by
      have h1 := dist_smul F (D.x ^ (k - i).val) (D.beta k) w
      rw [hY] at h1
      omega
    have h1 := hfix _ hw'
    calc c • w = c • (D.x ^ (k - i).val)⁻¹ • (D.x ^ (k - i).val • w) := by
          rw [inv_smul_smul]
      _ = (c * (D.x ^ (k - i).val)⁻¹) • (D.x ^ (k - i).val • w) := (mul_smul _ _ _).symm
      _ = ((D.x ^ (k - i).val)⁻¹ * c) • (D.x ^ (k - i).val • w) := by rw [hcy]
      _ = (D.x ^ (k - i).val)⁻¹ • c • (D.x ^ (k - i).val • w) := mul_smul _ _ _
      _ = (D.x ^ (k - i).val)⁻¹ • (D.x ^ (k - i).val • w) := by rw [h1]
      _ = w := inv_smul_smul _ w
  have hK : c ∈ nbrStab Γ G α := (Subgroup.mem_inf.1 hc).1
  have hfixα : c • α = α := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer α hK)
  have h3 : c ∈ ballStab Γ G 3 α := by
    refine mem_ballStab.2 fun w hw => ?_
    by_cases hw0 : w = α
    · rw [hw0]
      exact hfixα
    · obtain ⟨P, hP0, hPn⟩ := IsTree.exists_arc_between F.isTree α w
      have hd : 1 ≤ Γ.dist α w := by
        have := F.isTree.connected.pos_dist_of_ne (Ne.symm hw0)
        omega
      have hβ : Γ.Adj α (P.vert 1) := by
        have := P.adj 0 hd
        rwa [hP0] at this
      obtain ⟨k, hk⟩ := D.exists_beta_eq F h71c hβ
      refine hspread k w ?_
      rw [hk]
      have := Arc.dist_vert F.isTree P (i := 1) (j := Γ.dist α w) hd le_rfl
      rw [hPn] at this
      omega
  obtain ⟨P8, -, h4, -, -, -⟩ := D.exists_arc8 F h71c (i := 0) (j := 1) (by decide)
  have h75 := (h7.2.2.2.2.2.2.2.2 P8 (by rw [h4]; exact D.val)).1
  rw [h4] at h75
  rwa [h75] at h3

end D10Set

end CFSG.Quasithin.Fan86
