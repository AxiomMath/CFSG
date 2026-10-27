module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Tr
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Cen2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Tr
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCore
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Co
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Rot
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Sq2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Geo

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem nbrStab_conj_stab (F : FanTree Γ G) {g : G} {a : V} (hg : g • a = a) {k : G}
    (hk : k ∈ nbrStab Γ G a) : g * k * g⁻¹ ∈ nbrStab Γ G a := by
  have := (mem_nbrStab_smul_iff F g (g * k * g⁻¹) a).2 (by
    have e : g⁻¹ * (g * k * g⁻¹) * g = k := by group
    rw [e]; exact hk)
  rwa [hg] at this

theorem xe_comm_ballStab_three (h40 : Fan40 F) (h64 : Fan64 F) (h71a : Fan71a F L)
    (h71c : Fan71c F L) (h72b : Fan72b F L) (h73b : Fan73b F L) {P : Arc Γ 8}
    (h5 : valence Γ (P.vert 4) = 5) {n : G} (hn : n ∈ ballStab Γ G 3 (P.vert 4)) :
    xe L P * n = n * xe L P := by
  have := ballStab_three_le_calpha h40 h64 h71a h71c h72b h73b h5 hn
  exact Subgroup.mem_centralizer_iff.1
    (show n ∈ nbrStab Γ G (P.vert 4) ⊓ Subgroup.centralizer ({xe L P} : Set G) from this).2
    _ (Set.mem_singleton _)

theorem nbrStab_const (h40 : Fan40 F) (h64 : Fan64 F) (h65 : Fan65 F) (h71a : Fan71a F L)
    (h71c : Fan71c F L) (h72b : Fan72b F L) (h73b : Fan73b F L) {P : Arc Γ 8}
    (h5 : valence Γ (P.vert 4) = 5) {n : G} (hn : n ∈ ballStab Γ G 3 (P.vert 4)) {w : V}
    (hw : Γ.dist (P.vert 4) w = 4) : n ∈ nbrStab Γ G w ↔ n ∈ nbrStab Γ G (P.vert 8) := by
  have hx5 : xe L P ^ 5 = 1 := xe_pow_five h71a h5
  have hxo : orderOf (xe L P) = 5 := orderOf_xe h71a h71c h5
  have hxmem : xe L P ∈ MulAction.stabilizer G (P.vert 4) := xe_mem_stabilizer h71c h5
  have hxα : xe L P • P.vert 4 = P.vert 4 := MulAction.mem_stabilizer_iff.1 hxmem
  obtain ⟨A, hA0, hA4⟩ := exists_arc8_between F hw (i := 0) (by norm_num)
  have hA4' : A.vert 4 = w := hA4
  have hadj1 : Γ.Adj (P.vert 4) (A.vert 1) := by
    have := A.adj 0 (by norm_num)
    rwa [hA0] at this
  have hd1 : Γ.dist (A.vert 1) w = 3 := by
    have := Arc.dist_vert F.isTree A (i := 1) (j := 4) (by norm_num) (by norm_num)
    rw [hA4'] at this
    omega
  obtain ⟨j, hj⟩ := exists_zpow_smul_eq F h65 h5 hxmem hxo (P.adj 4 (by norm_num)) hadj1
  obtain ⟨w', hw'⟩ : ∃ w', w' = (xe L P ^ (-j)) • w := ⟨_, rfl⟩
  have hxw' : (xe L P ^ j) • w' = w := by
    rw [hw', ← mul_smul, ← zpow_add, add_neg_cancel, zpow_zero, one_smul]
  have hd5 : Γ.dist (P.vert 5) w' = 3 := by
    have := dist_smul F (xe L P ^ j) (P.vert 5) w'
    rw [hj, hxw', hd1] at this
    exact this.symm
  have hd4 : Γ.dist (P.vert 4) w' = 4 := by
    have := dist_smul F (xe L P ^ j) (P.vert 4) w'
    rw [zpow_smul_of_smul_eq hxα j, hxw', hw] at this
    exact this.symm
  obtain ⟨k, hk, hkw⟩ := exists_nbrStab_smul h65 h71a h71c h5 hd5 hd4
  have := P71.finite_nbrStab F (P.vert 4)
  obtain ⟨d, hd, c, hcK, hxc, hkdc⟩ := exists_mul_of_comm hx5 (F.nbrStab_isPGroup _)
    (fun k hk => nbrStab_conj_stab F hxα hk) hk
  have hcc : c ∈ L.calpha P := by
    rw [ZLab.calpha, Subgroup.mem_inf]
    exact ⟨hcK, Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]; exact hxc)⟩
  rw [calpha_eq_stab h71a h71c h5, Arc.mem_stab] at hcc
  have hd8 : d • P.vert 8 = w' := by
    rw [← hkw, hkdc, mul_smul, hcc 8 le_rfl]
  have hg8 : (xe L P ^ j * d) • P.vert 8 = w := by rw [mul_smul, hd8, hxw']
  have hxn := xe_comm_ballStab_three h40 h64 h71a h71c h72b h73b h5 hn
  have hcomm : Commute (xe L P ^ j * d) n :=
    (Commute.zpow_left (show Commute (xe L P) n from hxn) j).mul_left
      (show Commute d n from ballStab_three_comm_commDG h40 h64 h71a h71c h72b h73b h5 hn hd)
  have hgn : (xe L P ^ j * d)⁻¹ * n * (xe L P ^ j * d) = n := by
    have h1 : n * (xe L P ^ j * d) = (xe L P ^ j * d) * n := hcomm.symm
    calc (xe L P ^ j * d)⁻¹ * n * (xe L P ^ j * d)
        = (xe L P ^ j * d)⁻¹ * ((xe L P ^ j * d) * n) := by rw [← h1]; group
      _ = n := by group
  rw [← hg8, mem_nbrStab_smul_iff F, hgn]

theorem eq_one_of_mem_nbrStab (h40 : Fan40 F) (hΞ : ∃ T : Track Γ G, InXi T) (h62 : Fan62 F)
    (h64 : Fan64 F) (h65 : Fan65 F) (h71a : Fan71a F L) (h71c : Fan71c F L)
    (h72b : Fan72b F L) (h73b : Fan73b F L) {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5)
    {n : G} (hn : n ∈ ballStab Γ G 3 (P.vert 4)) (hn8 : n ∈ nbrStab Γ G (P.vert 8)) :
    n = 1 := by
  have hn4 := ballStab_three_le_four h40 h64 h71a h71c h72b h73b h5 hn
  have hM : n ∈ ballStab Γ G 5 (P.vert 4) := by
    refine mem_ballStab.2 fun u hu => ?_
    by_cases hu4 : Γ.dist (P.vert 4) u ≤ 4
    · exact mem_ballStab.1 hn4 u hu4
    · have hd : Γ.dist (P.vert 4) u = 5 := by omega
      obtain ⟨A, hA0, hA5⟩ := exists_arc8_between F hd (i := 0) (by norm_num)
      have hA5' : A.vert 5 = u := hA5
      have hd4 : Γ.dist (P.vert 4) (A.vert 4) = 4 := by
        have := Arc.dist_vert F.isTree A (i := 0) (j := 4) (by norm_num) (by norm_num)
        rw [hA0] at this
        omega
      have hmem := (nbrStab_const h40 h64 h65 h71a h71c h72b h73b h5 hn hd4).2 hn8
      have hadj : Γ.Adj (A.vert 4) u := by
        have := A.adj 4 (by norm_num)
        rwa [hA5'] at this
      exact mem_nbrStab.1 hmem u hadj
  have := ballStab_five_eq_bot F h40 hΞ h62 h65 h5
  rw [this] at hM
  exact hM

end P74

end CFSG.Quasithin.Fan86
