module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Nu
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s1614e3_false_of_row (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV) {U : Subgroup G} (hU : Min1614 D V U)
    (hUΓ : U ∉ gammaEleven D.M V) (hk : D.k < mBar D.M ⊥ V hV)
    (hrk : D.k + 2 < rk (Vtil ⊥ V hV))
    (hrow : ∀ t ∈ Mbar D.M ⊥ V hV, orderOf t = 2 → D.k < rkIdx (fixV (Subgroup.zpowers t)) →
      ∀ W : Subgroup (Vtil ⊥ V hV), W ≤ fixV (Subgroup.zpowers t) → rkIdx W ≤ D.k + 2 →
        (∃ z ∈ W, z ≠ 1 ∧ ∃ p ∈ D.sig, ∃ B : Subgroup (MulAut (Vtil ⊥ V hV)),
          B ≤ Mbar D.M ⊥ V hV ∧ IsPGroup p ↥B ∧ ¬ IsCyclic ↥B ∧ z ∈ fixV B) ∨
        (∃ p ∈ D.sig, CFSG.Open.pRank p (Mbar D.M ⊥ V hV) ≤ 2 ∧
          ∀ E : Subgroup (MulAut (Vtil ⊥ V hV)), E ≤ Mbar D.M ⊥ V hV →
            IsElemAbelianOfRank p 2 ↥E → ∃ e ∈ E, e ≠ 1 ∧
              ∃ Z : Subgroup (Vtil ⊥ V hV), Z ≠ ⊥ ∧ Z ≤ W ∧ Z.map e.toMonoidHom = Z)) :
    False := by
  have hP : PairFacts D.M ⊥ V := hc.setting.hyp16.hyp125.pairFacts
  by_cases hU0 : U = ⊥
  · subst hU0
    have h1 := s1614_rkIdx_le D hV hU
    have h2 : imgTil ⊥ V hV (⊥ : Subgroup G) = ⊥ := by
      unfold imgTil intSub
      rw [Subgroup.bot_subgroupOf]
      exact Subgroup.map_bot _
    rw [h2] at h1
    have h3 := rk_add_rkIdx (⊥ : Subgroup (Vtil ⊥ V hV))
    rw [rk_bot] at h3
    omega
  · obtain ⟨t, htM, ht2, htU⟩ :=
      s1614_exists_involution D hV hP.le_normalizer hU.1 hU0 hU.2.1 hUΓ
    have hmt : D.k < rkIdx (fixV (Subgroup.zpowers t)) :=
      lt_of_lt_of_le hk (CFSG.Quasithin.Asc81c.Pf.mParam_le_of_orderOf_two htM ht2)
    rcases hrow t htM ht2 hmt (imgTil ⊥ V hV U) htU (s1614_rkIdx_le D hV hU) with
      ⟨z, hzW, hz1, p, hp, B, hB, hBp, hBc, hzB⟩ | ⟨p, hp, hpr, hnorm⟩
    · exact s1614_nu_prime D h61 hV hP hU.2.1 hp hB hBp hBc hzW hz1 hzB
    · exact s1614e3_false_of_lemmaP D hx h61 h127 hV hc hU hp hpr hnorm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
