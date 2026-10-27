module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Tight
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Arc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Ind
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Sq
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem arcTrans (h65 : Fan65 F) (h71a : Fan71a F L) (h71c : Fan71c F L) {P : Arc Γ 8}
    (h5 : valence Γ (P.vert 4) = 5) : P71.ArcTrans Γ G := by
  have hcal := calpha_eq_stab h71a h71c h5
  have hcent : ∀ g ∈ P.stab G, g * xe L P = xe L P * g := by
    intro g hg
    rw [← hcal] at hg
    exact (Subgroup.mem_centralizer_iff.1
      (show g ∈ nbrStab Γ G (P.vert 4) ⊓ Subgroup.centralizer ({xe L P} : Set G) from hg).2
      _ (Set.mem_singleton _)).symm
  have hK := h65.1 (P.vert 4) h5 (xe L P) (xe_mem_stabilizer h71c h5) (orderOf_xe h71a h71c h5)
  exact P71.arcTrans_of_tight F P h5 (P71.R_tight F P h5 hcent hK)

theorem exists_nbrStab_smul (h65 : Fan65 F) (h71a : Fan71a F L) (h71c : Fan71c F L)
    {P : Arc Γ 8} (h5 : valence Γ (P.vert 4) = 5) {w : V} (hd5 : Γ.dist (P.vert 5) w = 3)
    (hd4 : Γ.dist (P.vert 4) w = 4) : ∃ k ∈ nbrStab Γ G (P.vert 4), k • P.vert 8 = w := by
  have hA := arcTrans h65 h71a h71c h5
  have key : ∀ n : ℕ, Γ.dist (P.vert 5) w = n →
      ∃ A : Arc Γ n, A.vert 0 = P.vert 5 ∧ A.vert n = w := by
    rintro n rfl
    exact IsTree.exists_arc_between F.isTree (P.vert 5) w
  obtain ⟨G3, hG0, hG3⟩ := key 3 hd5
  have hjunc : (Arc.take P 5 (by norm_num)).vert 5 = G3.vert 0 := by
    rw [hG0]; rfl
  have hnb : 1 ≤ 5 → 1 ≤ 3 → (Arc.take P 5 (by norm_num)).vert (5 - 1) ≠ G3.vert 1 := by
    intro _ _ h
    have hd := Arc.dist_vert F.isTree G3 (i := 1) (j := 3) (by norm_num) (by norm_num)
    have h4 : (Arc.take P 5 (by norm_num)).vert 4 = P.vert 4 := rfl
    rw [show 5 - 1 = 4 from rfl, h4] at h
    rw [← h, hG3] at hd
    omega
  let B : Arc Γ 8 := Arc.append (Arc.take P 5 (by norm_num)) G3 hjunc hnb
  have hB0 : B.vert 0 = P.vert 0 := Arc.append_vert_le _ _ hjunc hnb (by norm_num)
  have h0 : valence Γ (P.vert 0) = 5 := valence_vert F P h5 (by norm_num) (by norm_num)
  obtain ⟨g, hg⟩ := hA P B h0 (by rw [hB0]; exact h0)
  have hgi : ∀ i, i ≤ 5 → g • P.vert i = P.vert i := fun i hi => by
    rw [hg i (by omega)]
    exact Arc.append_vert_le _ _ hjunc hnb hi
  have hg8 : g • P.vert 8 = w := by
    rw [hg 8 le_rfl, Arc.append_vert_ge _ _ hjunc hnb (by norm_num)]
    exact hG3
  refine ⟨g, ?_, hg8⟩
  exact mem_nbrStab_of_fix_two F (MulAction.mem_stabilizer_iff.2 (hgi 4 (by norm_num)))
    (P.adj 3 (by norm_num)).symm (P.adj 4 (by norm_num)) (P.nb 3 (by norm_num))
    (hgi 3 (by norm_num)) (hgi 5 (by norm_num))

end P74

end CFSG.Quasithin.Fan86
