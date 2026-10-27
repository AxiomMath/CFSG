module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Far

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem not_rightSingular_of_trans (F : FanTree Γ G) {k : ℕ} (P : Arc Γ k)
    (hP : RightTransitive Γ G P.vert 0 k) : ¬ RightSingular Γ G P.vert 0 k := by
  rintro ⟨w, hw, hwne, hfixw⟩
  obtain ⟨u, hu, hu1, hu2⟩ := exists_adj_ne₂ F (P.vert k) (P.vert (k - 1)) w
  obtain ⟨g, hg, hgw⟩ := hP w u hw hwne hu hu1
  exact hu2 (hgw.symm.trans (hfixw g hg))

theorem not_rightSingular_seven_three (F : FanTree Γ G) (hA : ArcTrans Γ G) (P : Arc Γ 7)
    (h3 : Fan86.valence Γ (P.vert 7) = 3) : ¬ RightSingular Γ G P.vert 0 7 := by
  rintro ⟨w, hw, hwne, hfixw⟩
  have h6 : Fan86.valence Γ (P.vert 6) = 5 :=
    valence_adj_five F h3 (P.adj 6 (by norm_num)).symm
  have h0 : Fan86.valence Γ (P.vert 0) = 5 := by
    refine valence_of_dist_even F h6 ?_
    rw [SimpleGraph.dist_comm, Arc.dist_vert F.isTree P (Nat.zero_le 6) (by norm_num)]
  obtain ⟨u, hu, hu1, hu2⟩ := exists_adj_ne₂ F (P.vert 7) (P.vert 6) w
  have hA0 : Fan86.valence Γ ((snoc P w hw (fun _ => hwne)).vert 0) = 5 := by
    rw [snoc_vert_le P w hw _ (Nat.zero_le 7)]
    exact h0
  have hB0 : Fan86.valence Γ ((snoc P u hu (fun _ => hu1)).vert 0) = 5 := by
    rw [snoc_vert_le P u hu _ (Nat.zero_le 7)]
    exact h0
  obtain ⟨g, hg⟩ := hA _ _ hA0 hB0
  have hgs : g ∈ stabRange G P.vert 0 7 := by
    refine mem_stabRange.2 fun m _ hm => ?_
    have := hg m (by omega)
    rwa [snoc_vert_le P w hw _ hm, snoc_vert_le P u hu _ hm] at this
  have h8 := hg 8 le_rfl
  rw [snoc_vert_last P w hw _, snoc_vert_last P u hu _, hfixw g hgs] at h8
  exact hu2 h8.symm

theorem not_rightSingular_seven_five (F : FanTree Γ G) (L : ZLab Γ G)
    (hb : ∀ l, Fan86.valence Γ l = 5 → L.z l ∈ ballStab Γ G 4 l)
    (hfix : ∀ l, Fan86.valence Γ l = 5 → fixedPts (V := V) (L.z l) = {v | Γ.dist l v ≤ 4})
    (P : Arc Γ 7) (h5 : Fan86.valence Γ (P.vert 7) = 5) : ¬ RightSingular Γ G P.vert 0 7 := by
  rintro ⟨w, hw, hwne, hfixw⟩
  have d73 : Γ.dist (P.vert 3) (P.vert 7) = 4 :=
    Arc.dist_vert F.isTree P (by norm_num) le_rfl
  have h3 : Fan86.valence Γ (P.vert 3) = 5 := by
    refine valence_of_dist_even F h5 ?_
    rw [SimpleGraph.dist_comm, d73]
  have hzs : L.z (P.vert 3) ∈ stabRange G P.vert 0 7 := by
    refine mem_stabRange.2 fun m _ hm => ?_
    refine mem_ballStab.1 (hb _ h3) (P.vert m) ?_
    rcases le_total m 3 with h | h
    · rw [SimpleGraph.dist_comm, Arc.dist_vert F.isTree P h (by norm_num)]
      omega
    · rw [Arc.dist_vert F.isTree P h hm]
      omega
  have hw' : L.z (P.vert 3) • w = w := hfixw _ hzs
  have hmem : w ∈ fixedPts (V := V) (L.z (P.vert 3)) := hw'
  rw [hfix _ h3] at hmem
  have d83 : Γ.dist (P.vert 3) w = 5 := by
    have := Arc.dist_vert F.isTree (snoc P w hw (fun _ => hwne)) (i := 3) (j := 8)
      (by norm_num) le_rfl
    rwa [snoc_vert_le P w hw _ (by norm_num), snoc_vert_last P w hw _] at this
  have : Γ.dist (P.vert 3) w ≤ 4 := hmem
  omega

theorem singGe_eight (F : FanTree Γ G) (L : ZLab Γ G) (hA : ArcTrans Γ G)
    (hb : ∀ l, Fan86.valence Γ l = 5 → L.z l ∈ ballStab Γ G 4 l)
    (hfix : ∀ l, Fan86.valence Γ l = 5 → fixedPts (V := V) (L.z l) = {v | Γ.dist l v ≤ 4}) :
    SingGe Γ G 8 := by
  rintro k hk1 hk8 ⟨P, hP⟩
  by_cases hk : k ≤ 6
  · exact not_rightSingular_of_trans F P (rightTransitive_of_arcTrans F hA P hk) hP
  · have hk7 : k = 7 := by omega
    subst hk7
    have hv := F.valence (P.vert 7)
    rcases hv with h | h
    · exact not_rightSingular_seven_three F hA P h hP
    · exact not_rightSingular_seven_five F L hb hfix P h hP

end P71

end CFSG.Quasithin.Fan86
