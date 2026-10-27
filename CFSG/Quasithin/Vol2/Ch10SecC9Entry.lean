module

public import CFSG.Quasithin.Vol2.Ch10SecC9Claim
public import CFSG.Quasithin.Vol2.Ch10SecC9S49f

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem inf_centralizer_le_T1 (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {w : G}
    (hwW : w ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hwV1 : w ∉ fsuUL T L I) :
    T ⊓ Subgroup.centralizer ({w} : Set G) ≤ T1 T L := by
  rintro s ⟨hs, hsw⟩
  refine ⟨hs, ?_⟩
  rcases SecA.conjugate_eq_or h37 h38 hyp ht htn (SecA.le_fsuM T L hs) with h | h
  · exact SecA.conjugate_eq_self_iff.mp h
  · exfalso
    have hsw' : s * w * s⁻¹ = w := mul_conj_eq_of_mem_centralizer hsw
    have key : w ∈ ⁅fsuVM T L I, CFSG.conjugate L s⁆ := by
      rw [h]
      exact hwW
    rw [← SecA.conjugate_commutator_fsuVM (I := I) (SecA.le_fsuM T L hs), SecA.mem_conjugate_iff,
      hsw'] at key
    exact hwV1 key

theorem exists_conf_isQuasisimple_autI
    (h36 : Vol2Native.A36CoreForSQTKCat)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1013 : Stmt10_1_3) (h1021 : Stmt10_2_1) (h1025 : Stmt10_2_5)
    (h1026 : Stmt10_2_6) (h1027 : Stmt10_2_7) (h1028 : Stmt10_2_8)
    (h484 : ASInputs.AS_B_4_8_four) (h3210e : TmpL6_3_2_10_eight) (h3210n : TmpL6_3_2_10_nine)
    (he23 : E2.E23Statement) (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h3228 : TmpL6_3_2_2_eight) (hGap : Gap10_2_9V1capV2) (hK1 : FactK1) (hK3 : FactK3Sp4)
    (hSp4 : ASInputs.AS_I_1_3_Sp4) (hK8a : FactK8a) (hK8b : FactK8b) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {v : G}
    (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hv1 : v ≠ 1)
    (hvM : ¬ Subgroup.centralizer ({v} : Set G) ≤ fsuM T L) :
    ∃ w J, Conf T L I t w J ∧ ¬ CFSG.Open.IsQuasisimple ↥J ∧
      CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) ∧
      ∃ hVe : IsElemAbelian 2 (VI T L I J w), CFSG.Open.IsQuasisimple ↥(autI hVe J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_claimOut h37 h38 hyp h1011 h1012 h1013 h1021 h1025 h1026 h1028 h484
    h3210e h3210n he23 h322 hshape h3228 hGap ht htn hv hv1 hvM
  have hw1 : w ≠ 1 := fun h => hw.2.1 (h ▸ Subgroup.one_mem _)
  have hTwL : T ⊓ Subgroup.centralizer ({w} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    (inf_centralizer_le_T1 h37 h38 hyp ht htn hw.1 hw.2.1).trans inf_le_right
  obtain ⟨J, hJmem, hLJ, hLne, hJn, hJM⟩ :=
    exists_cComp_gt h37 h38 h39 hyp h1011 h1026 ht htn hw.1 hw1 hw.2.2.2.1 hTwL hw.2.2.1
  have c : Conf T L I t w J := ⟨hyp, ht, htn, hw, hJmem, hLJ, hLne, hJn, hJM⟩
  have hq : ¬ CFSG.Open.IsQuasisimple ↥J := fun hq =>
    c.false_of_isQuasisimple h37 h38 h1011 h1013 h1026 h1027 hK1 hK3 hSp4 hq
  have hO := oddCoreIn_eq_bot h37 h38 hyp h1011 h1026 ht hw.1 hw.2.1 hJmem hLJ hJn
  have hJ2 := charTwo_of_not_isQuasisimple hJmem hq hO
  have hF : CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) :=
    charTwo_sup hJ2 hyp.fsu.sylow.1.to_inf_left c.Tw_le_normalizer
  have hVe := (VI_props hyp c.w_mem_V c.isSylowTwoOf_sup hF).2.1
  exact ⟨w, J, c, hq, hF, hVe,
    c.isQuasisimple_autI h36 h37 h38 h1011 h1026 h1027 hK8a hK8b hF hVe⟩

end CFSG.Quasithin.Vol2.Ch10.SecC
