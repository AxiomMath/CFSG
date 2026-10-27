module

public import CFSG.Quasithin.Vol2.Ch10SecQ2Nor
public import CFSG.Quasithin.Vol2.Ch10SecEBlockA5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem normalizer_baum_le_case2_eq
    (he23 : E2.E23Statement) (he234 : E2.E23FourStatement)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (h331 : Stmt3_3_1) (h113 : ASInputs.AS_C_1_13)
    (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G))
    (hCZ : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥) :
    Subgroup.normalizer (baum T : Set G) ≤ fsuM T L := by
  by_contra hNS
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hb := isA5Block_case2 he234 h37 h38 hshape h3228 h331 hyp h2 hJ hNS
  have hC0 := inf_centralizer_fsuL0_eq_bot hyp hCZ
  have hCV := centralizer_le_fsuVM_case2 h113 h37 h38 h322 h3228 hyp h2 hb hCZ
  obtain ⟨D⟩ := exists_case2Data he23 h37 h38 h322 hshape h3228 hyp h2 ht htn hJ
  obtain ⟨q, hqT, hq2, hqc, hqτ⟩ := D.exists_Q h113 h37 h38 ht htn h2 hb hC0 hCV
  obtain ⟨ρ, hρL, hρ⟩ := D.exists_rho h37 h38 h322 h2
  obtain ⟨j₀, hj₀, hs₀⟩ := C10P02.t_conj_tau D h37 h38 ht htn (Or.inl rfl)
  obtain ⟨j₁, hj₁, hs₁⟩ := C10P02.t_conj_tau D h37 h38 ht htn (Or.inr rfl)
  have hj : j₀ ≠ j₁ := by
    rintro rfl
    have h01 : D.tau 0 = D.tau 1 := mul_left_cancel (mul_right_cancel (hs₀.trans hs₁.symm))
    exact sA_ne_sB (D.θ₁.symm.injective (Subtype.ext h01))
  have hNV := C10P02.normalizer_baum_le_normalizer D hyp.fsu.sylow.2 hC0 hCV hqT hq2 hqc hqτ
    hρL.1 (C10P02.rho_conj_tau D hρ) (s := ⟨t, SecA.le_normalizer_fsuVM T L I ht⟩) ht hj₀ hj₁
    hj hs₀ hs₁
  exact hNS (hNV.trans (SecB.normalizer_le_fsuM_of_L0T h331 hyp (SecA.isPGroup_fsuVM hyp)
    (SecA.fsuVM_ne_bot hyp.fsu)
    (sup_le (SecA.fsuL0_le_normalizer_fsuVM T L I) (SecA.le_normalizer_fsuVM T L I))))

end CFSG.Quasithin.Vol2.Ch10.SecE
