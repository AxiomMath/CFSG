module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Arc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Rot
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Sq

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem exists_third_nbr_five (F : FanTree Γ G) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5) :
    ∃ y : V, Γ.Adj (P.vert 5) y ∧ y ≠ P.vert 4 ∧ y ≠ P.vert 6 ∧
      ∀ u, Γ.Adj (P.vert 5) u → u = P.vert 4 ∨ u = P.vert 6 ∨ u = y := by
  have h53 : valence Γ (P.vert 5) = 3 :=
    (P71.valence_arc F P (by norm_num) h5 5 (by norm_num)).2 (by norm_num)
  have hS : (Γ.neighborSet (P.vert 5)).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact h53
  have hfin : (Γ.neighborSet (P.vert 5)).Finite := Set.finite_of_ncard_pos (by omega)
  have h46 : P.vert 4 ≠ P.vert 6 := P.nb 4 (by norm_num)
  have hlt : ({P.vert 4, P.vert 6} : Set V).ncard < (Γ.neighborSet (P.vert 5)).ncard := by
    rw [Set.ncard_pair h46, hS]
    norm_num
  obtain ⟨y, hyS, hy⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  have hy4 : y ≠ P.vert 4 := fun h => hy (Or.inl h)
  have hy6 : y ≠ P.vert 6 := fun h => hy (Or.inr h)
  have hsub : ({P.vert 4, P.vert 6, y} : Set V) ⊆ Γ.neighborSet (P.vert 5) := by
    rintro _ (rfl | rfl | rfl)
    · exact (P.adj 4 (by norm_num)).symm
    · exact P.adj 5 (by norm_num)
    · exact hyS
  have hc3 : ({P.vert 4, P.vert 6, y} : Set V).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨_, _, _, h46, hy4.symm, hy6.symm, rfl⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hc3, hS]) hfin
  refine ⟨y, hyS, hy4, hy6, fun u hu => ?_⟩
  have : u ∈ ({P.vert 4, P.vert 6, y} : Set V) := by
    rw [heq]
    exact hu
  simpa using this

theorem calpha_mem_nbrStab_five_six (h71a : Fan71a F L) (h71c : Fan71c F L) {P : Arc Γ 8}
    (h5 : valence Γ (P.vert 4) = 5) {c : G} (hc : c ∈ L.calpha P) :
    c ∈ nbrStab Γ G (P.vert 5) ∧ c ∈ nbrStab Γ G (P.vert 6) := by
  have hcP := hc
  rw [calpha_eq_stab h71a h71c h5, Arc.mem_stab] at hcP
  refine ⟨mem_nbrStab_of_fix_two F (MulAction.mem_stabilizer_iff.2 (hcP 5 (by norm_num)))
      (P.adj 4 (by norm_num)).symm (P.adj 5 (by norm_num)) (P.nb 4 (by norm_num))
      (hcP 4 (by norm_num)) (hcP 6 (by norm_num)),
    mem_nbrStab_of_fix_two F (MulAction.mem_stabilizer_iff.2 (hcP 6 (by norm_num)))
      (P.adj 5 (by norm_num)).symm (P.adj 6 (by norm_num)) (P.nb 5 (by norm_num))
      (hcP 5 (by norm_num)) (hcP 7 (by norm_num))⟩

theorem xe_mul_comm {c : G} {P : Arc Γ 8} (hc : c ∈ L.calpha P) : xe L P * c = c * xe L P :=
  Subgroup.mem_centralizer_iff.1 (show c ∈ nbrStab Γ G (P.vert 4) ⊓
    Subgroup.centralizer ({xe L P} : Set G) from hc).2 _ (Set.mem_singleton _)

theorem mem_nbrStab_of_dist_two (h65 : Fan65 F) (h71a : Fan71a F L) (h71c : Fan71c F L)
    {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5) {y : V}
    (hall : ∀ u, Γ.Adj (P.vert 5) u → u = P.vert 4 ∨ u = P.vert 6 ∨ u = y) {c : G}
    (hc : c ∈ L.calpha P) (hcy : c ∈ nbrStab Γ G y) {w : V} (hw : Γ.dist (P.vert 4) w = 2) :
    c ∈ nbrStab Γ G w := by
  have hxs := xe_mem_stabilizer h71c h5
  have hx5 := orderOf_xe h71a h71c h5
  obtain ⟨Q, hQ4, hQ6⟩ := exists_arc8_between F hw (i := 4) (by norm_num)
  have hu : Γ.Adj (P.vert 4) (Q.vert 5) := by
    have := Q.adj 4 (by norm_num)
    rwa [hQ4] at this
  have huw : Γ.Adj (Q.vert 5) w := by
    have := Q.adj 5 (by norm_num)
    rwa [show (5 + 1 : ℕ) = 4 + 2 from rfl, hQ6] at this
  obtain ⟨j, hj⟩ := exists_zpow_smul_eq F h65 h5 hxs hx5 (P.adj 4 (by norm_num)) hu
  have hadj : Γ.Adj (P.vert 5) ((xe L P ^ j)⁻¹ • w) := by
    have := (F.adj_smul ((xe L P ^ j)⁻¹) (Q.vert 5) w).2 huw
    rwa [← hj, inv_smul_smul] at this
  have hne : (xe L P ^ j)⁻¹ • w ≠ P.vert 4 := by
    intro h
    have hfix : (xe L P ^ j) • P.vert 4 = P.vert 4 :=
      zpow_smul_of_smul_eq (MulAction.mem_stabilizer_iff.1 hxs) j
    rw [inv_smul_eq_iff, hfix] at h
    rw [h, SimpleGraph.dist_self] at hw
    omega
  have hc6 := (calpha_mem_nbrStab_five_six h71a h71c h5 hc).2
  have hcw' : c ∈ nbrStab Γ G ((xe L P ^ j)⁻¹ • w) := by
    rcases hall _ hadj with h | h | h
    · exact absurd h hne
    · rw [h]
      exact hc6
    · rw [h]
      exact hcy
  have hxc : Commute (xe L P ^ j) c :=
    Commute.zpow_left (show Commute (xe L P) c from xe_mul_comm hc) j
  have hconj : (xe L P ^ j)⁻¹ * c * xe L P ^ j = c := by
    calc (xe L P ^ j)⁻¹ * c * xe L P ^ j = (xe L P ^ j)⁻¹ * (c * xe L P ^ j) := by
          rw [mul_assoc]
      _ = (xe L P ^ j)⁻¹ * (xe L P ^ j * c) := by rw [← hxc.eq]
      _ = c := inv_mul_cancel_left _ _
  have := (F.mem_nbrStab_smul_iff (xe L P ^ j) ((xe L P ^ j)⁻¹ • w) (h := c)).2
    (by rw [hconj]; exact hcw')
  rwa [smul_inv_smul] at this

theorem mem_ballStab_three_of_nbrStab (h73b : Fan73b F L) {P : Arc Γ 8}
    (h5 : valence Γ (P.vert 4) = 5) {c : G} (hc : c ∈ L.calpha P)
    (hK : ∀ w, Γ.dist (P.vert 4) w = 2 → c ∈ nbrStab Γ G w) :
    c ∈ ballStab Γ G 3 (P.vert 4) := by
  have hb2 : c ∈ ballStab Γ G 2 (P.vert 4) := by
    rw [(h73b P h5).1]
    exact Subgroup.mem_sup_right hc
  refine mem_ballStab.2 fun v hv => ?_
  by_cases hv2 : Γ.dist (P.vert 4) v ≤ 2
  · exact mem_ballStab.1 hb2 v hv2
  · have hd : Γ.dist (P.vert 4) v = 3 := by omega
    obtain ⟨Q, hQ4, hQ7⟩ := exists_arc8_between F hd (i := 4) (by norm_num)
    have hd2 : Γ.dist (P.vert 4) (Q.vert 6) = 2 := by
      have := Arc.dist_vert F.isTree Q (i := 4) (j := 6) (by norm_num) (by norm_num)
      rw [hQ4] at this
      omega
    have hadj : Γ.Adj (Q.vert 6) v := by
      have := Q.adj 6 (by norm_num)
      rwa [show (6 + 1 : ℕ) = 4 + 3 from rfl, hQ7] at this
    exact mem_nbrStab.1 (hK _ hd2) v hadj

end P74

end CFSG.Quasithin.Fan86
