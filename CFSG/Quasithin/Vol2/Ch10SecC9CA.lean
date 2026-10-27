module

public import CFSG.Quasithin.Vol2.Ch10SecC9Out
public import CFSG.Quasithin.Vol2.Ch10SecC8Main4c
public import CFSG.Quasithin.Vol2.Ch10SecC9B

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem claim_thompsonJ (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h3210e : TmpL6_3_2_10_eight) (h3210n : TmpL6_3_2_10_nine)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G))
    (hn3 : ¬ Case10_1_1Three T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {v : G}
    (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hv1 : v ≠ 1)
    (hvM : ¬ Subgroup.centralizer ({v} : Set G) ≤ fsuM T L) : ∃ w, ClaimOut T L I t w := by
  have hcv := fsuCVM_eq_bot_of_thompsonJ h3210n hyp hJ
  have hvV1 : v ∉ fsuUL T L I := fun h => by
    have := inf_V2_le_fsuCVM hyp h1011 ht htn ⟨h, hv⟩
    rw [hcv, Subgroup.mem_bot] at this
    exact hv1 this
  obtain ⟨m, hm, hwW, hwV1, hSyl, -⟩ := exists_conj_in_V2 h37 h38 hyp ht htn hv hvV1
  have hV2V : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I := commutator_le_left_of_le_normalizer
    ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hJw : thompsonJ T ≤ Subgroup.centralizer ({m * v * m⁻¹} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hJ hx) _ (hV2V hwW)).symm
  have hN := normalizer_le_of_thompsonJ h3210e hyp hJ hyp.fsu.sylow.1.to_inf_left
    (le_inf (B6.thompsonJ_le T) hJw)
  refine ⟨m * v * m⁻¹, hwW, hwV1, ?_, isSylowTwoOf_of_normalizer_le hSyl (inf_le_right.trans hN),
    hJw, fun h3 => absurd h3 hn3⟩
  rw [centralizer_conj_le_iff hm]
  exact hvM

end CFSG.Quasithin.Vol2.Ch10.SecC
