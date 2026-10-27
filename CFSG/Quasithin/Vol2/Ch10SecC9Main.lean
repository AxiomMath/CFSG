module

public import CFSG.Quasithin.Vol2.Ch10SecC9S5h
public import CFSG.Quasithin.Vol2.Ch10SecC9A
public import CFSG.Quasithin.Vol2.Ch10SecC9Entry

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem centralizer_le_of_mem_V2
    (h36 : Vol2Native.A36CoreForSQTKCat)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2)
    (h1013 : Stmt10_1_3) (h1021 : Stmt10_2_1) (h1025 : Stmt10_2_5) (h1026 : Stmt10_2_6)
    (h1027 : Stmt10_2_7) (h1028 : Stmt10_2_8) (h484 : ASInputs.AS_B_4_8_four)
    (h3210e : TmpL6_3_2_10_eight) (h3210n : TmpL6_3_2_10_nine) (he23 : E2.E23Statement)
    (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape) (h3228 : TmpL6_3_2_2_eight)
    (hSp4 : ASInputs.AS_I_1_3_Sp4) (h124 : C124StatementSQTK (G := G)) (h318 : A318Facts)
    (h36' : A36ForSQTK) (hE : Ch11.SecA.FactA318ExclTwo) (hK1 : FactK1) (hK3 : FactK3Sp4)
    (hK8a : FactK8a) (hK8b : FactK8b) (hK2 : FactK2) (hK4 : FactK4) (hK7 : FactK7)
    (hGap : Gap10_2_9V1capV2) (hObl : Obl10_2_9L32Branch) (hyp : Hyp10 G T L I) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {v : G}
    (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hv1 : v ≠ 1) :
    Subgroup.centralizer ({v} : Set G) ≤ fsuM T L := by
  by_contra hvM
  obtain ⟨w, J, c, hq, hF, hVe, hI⟩ := exists_conf_isQuasisimple_autI h36 h37 h38 h39 hyp h1011
    h1012 h1013 h1021 h1025 h1026 h1027 h1028 h484 h3210e h3210n he23 h322 hshape h3228 hGap hK1
    hK3 hSp4 hK8a hK8b ht htn hv hv1 hvM
  exact c.false_of_S5 h124 h37 h38 h1011 h1012 h1013 h1026 h1027 h322 hK8a hK8b h318 h36' hK2 hK4
    hK7 hE hObl hq hF hVe hI

theorem stmt10_2_9_of
    (h36 : Vol2Native.A36CoreForSQTKCat)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2)
    (h1013 : Stmt10_1_3) (h1021 : Stmt10_2_1) (h1025 : Stmt10_2_5) (h1026 : Stmt10_2_6)
    (h1027 : Stmt10_2_7) (h1028 : Stmt10_2_8) (h484 : ASInputs.AS_B_4_8_four)
    (h3210e : TmpL6_3_2_10_eight) (h3210n : TmpL6_3_2_10_nine) (he23 : E2.E23Statement)
    (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape) (h3228 : TmpL6_3_2_2_eight)
    (hSp4 : ASInputs.AS_I_1_3_Sp4)
    (h124 : ∀ (Γ : Type) [Group Γ] [Finite Γ], C124StatementSQTK (G := Γ)) (h318 : A318Facts)
    (h36' : A36ForSQTK) (hE : Ch11.SecA.FactA318ExclTwo) (hK1 : FactK1) (hK3 : FactK3Sp4)
    (hK8a : FactK8a) (hK8b : FactK8b) (hK2 : FactK2) (hK4 : FactK4) (hK7 : FactK7)
    (hGap : Gap10_2_9V1capV2) (hObl : Obl10_2_9L32Branch) : Stmt10_2_9 := by
  intro G _ _ T L I hyp K hK
  have h2 : ∀ {t : G}, t ∈ T → t ∉ Subgroup.normalizer (L : Set G) →
      ∀ v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆, v ≠ 1 →
        Subgroup.centralizer ({v} : Set G) ≤ fsuM T L := fun ht htn v hv hv1 =>
    centralizer_le_of_mem_V2 h36 h37 h38 h39 h1011 h1012 h1013 h1021 h1025 h1026 h1027 h1028 h484
      h3210e h3210n he23 h322 hshape h3228 hSp4 (h124 G) h318 h36' hE hK1 hK3 hK8a hK8b hK2 hK4 hK7
      hGap hObl hyp ht htn hv hv1
  have h1 : ∀ v ∈ ⁅fsuVM T L I, K⁆, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ fsuM T L := by
    rcases hK with hKL | ⟨t, ht, htn, hKt⟩
    · intro v hv hv1
      rw [hKL] at hv
      obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
      have hx : t⁻¹ * v * t ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
        rw [← SecA.conjugate_commutator_fsuVM (I := I) (SecA.le_fsuM T L ht),
          SecA.mem_conjugate_iff]
        simpa [mul_assoc] using hv
      have e : t * (t⁻¹ * v * t) * t⁻¹ = v := by group
      have hx1 : t⁻¹ * v * t ≠ 1 := fun h => hv1 (by rw [← e, h]; group)
      rw [← e, centralizer_conj_le_iff (SecA.le_fsuM T L ht)]
      exact h2 ht htn _ hx hx1
    · rw [hKt]
      exact h2 ht htn
  have hKL0 : K ≤ fsuL0 T L := by
    rcases hK with hKL | ⟨t, ht, -, hKt⟩
    · exact hKL ▸ SecA.le_fsuL0 T L
    · exact hKt ▸ SecA.conjugate_le_fsuL0 ht
  have hKV : ⁅fsuVM T L I, K⁆ ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer (hKL0.trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  exact ⟨h1, le_rParam_of_part_one hyp hKV h1, le_normalizer_of_part_one hyp h37 h38 h1011 hK h1⟩

end CFSG.Quasithin.Vol2.Ch10.SecC
