module

public import CFSG.Quasithin.Vol2.Ch10SecB4Main
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem normalizer_T1_le_of_thompsonJ (h3210 : TmpL6_3_2_10_eight) (h1012 : Stmt10_1_2)
    (hyp : Hyp10 G T L I) (hJ : thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) :
    Subgroup.normalizer (T1 T L : Set G) ≤ fsuM T L := by
  have hJT1 : thompsonJ T ≤ T1 T L := (h1012 G T L I hyp).2.1
  have hT1 : IsPGroup 2 (T1 T L) := hyp.fsu.sylow.1.to_le inf_le_left
  by_cases hiii : Sub326iii T L I
  · exact (h3210 G T L I (fsuVM T L I) hyp.fsu (Or.inl ⟨hiii, rfl⟩) hJ (T1 T L) hT1 hJT1).2
  · have hV : fsuV T I ≤ fsuVM T L I := le_conjClosure _ _
    exact (h3210 G T L I (fsuV T I) hyp.fsu (Or.inr ⟨hiii, rfl⟩)
      (hJ.trans (Subgroup.centralizer_le hV)) (T1 T L) hT1 hJT1).2

omit [Finite G] in
theorem not_case3_of_case12 {T L I : Subgroup G}
    (hc : (∃ n, Case10_1_1One T L I n) ∨ Case10_1_1Two T L I) : ¬ Case10_1_1Three T L I := by
  intro h3
  have hcard := card_lbar h3.1
  rcases hc with ⟨n, hn, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ | ⟨⟨e⟩, -⟩
  · rw [Nat.card_congr e.toEquiv] at hcard
    exact card_sl_two_ne hn hK hcard
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hcard
    exact absurd hcard (by decide)

theorem normalizer_T1_le_of_case12 (h1012 : Stmt10_1_2) (h1021 : Stmt10_2_1)
    (hyp : Hyp10 G T L I) (hc : (∃ n, Case10_1_1One T L I n) ∨ Case10_1_1Two T L I)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) :
    Subgroup.normalizer (T1 T L : Set G) ≤ fsuM T L := by
  have hS : baum T ≤ T1 T L := ((h1012 G T L I hyp).2.2.2.2.2.2.2.2 hc).2 hJ
  have hS' : baum T = baum (T1 T L) := baum_eq_of_le hS inf_le_left
  intro g hg
  have h1 := normalizer_le_normalizer_baum (T1 T L) hg
  rw [← hS'] at h1
  exact h1021 G T L I hyp (not_case3_of_case12 hc) h1

theorem cases123_of_not_thompsonJ (h1012 : Stmt10_1_2) (hyp : Hyp10 G T L I)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) :
    (∃ n, Case10_1_1One T L I n) ∨ Case10_1_1Two T L I ∨ Case10_1_1Three T L I := by
  by_contra h
  exact hJ ((h1012 G T L I hyp).1 h).2

end CFSG.Quasithin.Vol2.Ch10.SecB
