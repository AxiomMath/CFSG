module

public import CFSG.Quasithin.Vol2.Ch10SecC9C12
public import CFSG.Quasithin.Vol2.Ch10SecC9C3b
public import CFSG.Quasithin.Vol2.Ch10SecC9C3c
public import CFSG.Quasithin.Vol2.Ch10SecC9CA
public import CFSG.Quasithin.Vol2.Ch10SecA1012Four

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_claimOut
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1013 : Stmt10_1_3) (h1021 : Stmt10_2_1) (h1025 : Stmt10_2_5)
    (h1026 : Stmt10_2_6) (h1028 : Stmt10_2_8) (h484 : ASInputs.AS_B_4_8_four)
    (h3210e : TmpL6_3_2_10_eight) (h3210n : TmpL6_3_2_10_nine) (he23 : E2.E23Statement)
    (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape) (h3228 : TmpL6_3_2_2_eight)
    (hGap : Gap10_2_9V1capV2) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {v : G} (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hv1 : v ≠ 1)
    (hvM : ¬ Subgroup.centralizer ({v} : Set G) ≤ fsuM T L) : ∃ w, ClaimOut T L I t w := by
  by_cases h3 : Case10_1_1Three T L I
  · by_cases hc : cV1 T L I = ⊥
    · exact claim_case3_eq h37 h38 hyp h1011 h1012 h1025 h3
        (SecA.fsuCVM_eq_bot_of_cV1 h37 h38 hyp hc) ht htn hv hv1 hvM
    · have hne' : fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
        obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hc
        intro h
        have hxC : (x : G) ∈ fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) :=
          ⟨x.2, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (SecA.le_fsuL0 T L))
            (Subgroup.mem_subgroupOf.mp hx)⟩
        rw [h, Subgroup.mem_bot] at hxC
        exact hx1 (Subtype.ext (Subtype.ext hxC))
      exact claim_case3_ne h37 h38 hyp h1011 h1012 h1013 h1026 h1028 h484 h3210n h3 hc hne' ht
        htn hv hv1 hvM
  · by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)
    · exact claim_thompsonJ h37 h38 hyp h1011 h3210e h3210n hJ h3 ht htn hv hv1 hvM
    · by_cases h1 : ∃ n, Case10_1_1One T L I n
      · obtain ⟨n, h1⟩ := h1
        exact claim_case1 h37 h38 hyp h1011 h1021 h1026 he23 h322 hshape h3228 hGap h1 hJ ht htn
          hv hv1 hvM
      · have h2 : Case10_1_1Two T L I := by
          by_contra h2
          exact hJ ((h1012 G T L I hyp).1 (by tauto)).2
        exact claim_case2 h37 h38 hyp h1011 h1012 h1021 he23 h322 hshape h3228 h1 h2 hJ ht htn
          hv hv1 hvM

end CFSG.Quasithin.Vol2.Ch10.SecC
