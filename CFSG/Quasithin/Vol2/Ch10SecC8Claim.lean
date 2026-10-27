module

public import CFSG.Quasithin.Vol2.Ch10SecC8H1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem mem_sup_centralizer_conjugate (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1027 : Stmt10_2_7) (h484 : ASInputs.AS_B_4_8_four)
    (h3210 : TmpL6_3_2_10_nine) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) {t : G}
    (ht : t ∈ T) {z : G}
    (hz : z ∈ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G))) :
    z ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ⊔
      (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ⊓
        Subgroup.centralizer (CFSG.conjugate L t : Set G)) := by
  have hTX := le_normalizer_omegaOne_Q T L I
  have hXc : ∀ a ∈ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)),
      ∀ b ∈ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)), a * b = b * a :=
    fun a ha b hb => A4.mul_comm_of_mem_omegaOneCenterOf ha hb
  have hV1V : fsuUL T L I ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hV1X := hV1V.trans (fsuVM_le_omegaOneCenterOf hyp)
  have hz' : t * z * t⁻¹ ∈ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) :=
    (Subgroup.mem_normalizer_iff.mp (hTX ht) z).mp hz
  have h1 : t * z * t⁻¹ ∈ (↑(fsuUL T L I ⊔
      (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ⊓
        Subgroup.centralizer (L : Set G))) : Set G) :=
    mem_sup_centralizer_fsuUL h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne hz'
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (le_normalizer_of_comm hXc hV1X inf_le_left)] at h1
  obtain ⟨v, hv, c, hc, hvc⟩ := h1
  have hvc' : v * c = t * z * t⁻¹ := hvc
  have e : z = (t⁻¹ * v * t) * (t⁻¹ * c * t) := by
    have e1 : z = t⁻¹ * (t * z * t⁻¹) * t := by group
    rw [e1, ← hvc']
    group
  rw [e]
  refine Subgroup.mul_mem_sup ?_ (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · rw [← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht), SecA.mem_conjugate_iff]
    have e2 : t * (t⁻¹ * v * t) * t⁻¹ = v := by group
    rw [e2]
    exact hv
  · have h2 := (Subgroup.mem_normalizer_iff.mp (hTX (T.inv_mem ht)) c).mp hc.1
    rwa [inv_inv] at h2
  · rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hm' : t * m * t⁻¹ ∈ L := SecA.mem_conjugate_iff.mp hm
    have hc' := Subgroup.mem_centralizer_iff.mp hc.2 _ hm'
    calc m * (t⁻¹ * c * t) = t⁻¹ * ((t * m * t⁻¹) * c) * t := by group
      _ = t⁻¹ * (c * (t * m * t⁻¹)) * t := by rw [hc']
      _ = (t⁻¹ * c * t) * m := by group

theorem le_sup_centralizer_fsuL0 (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1027 : Stmt10_2_7) (h484 : ASInputs.AS_B_4_8_four)
    (h3210 : TmpL6_3_2_10_nine) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) :
    omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ≤
      fsuVM T L I ⊔ (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ⊓
        Subgroup.centralizer (fsuL0 T L : Set G)) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, -, hV2, -⟩ := hdec t ht htn
  have hXc : ∀ a ∈ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)),
      ∀ b ∈ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)), a * b = b * a :=
    fun a ha b hb => A4.mul_comm_of_mem_omegaOneCenterOf ha hb
  have hV1V : fsuUL T L I ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hV2V : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hVX := fsuVM_le_omegaOneCenterOf hyp
  intro z hz
  have h1 : z ∈ (↑(fsuUL T L I ⊔
      (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ⊓
        Subgroup.centralizer (L : Set G))) : Set G) :=
    mem_sup_centralizer_fsuUL h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne hz
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (le_normalizer_of_comm hXc (hV1V.trans hVX) inf_le_left)] at h1
  obtain ⟨v1, hv1, c1, hc1, hvc1⟩ := h1
  have h2 : c1 ∈ (↑(⁅fsuVM T L I, CFSG.conjugate L t⁆ ⊔
      (omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ⊓
        Subgroup.centralizer (CFSG.conjugate L t : Set G))) : Set G) :=
    mem_sup_centralizer_conjugate h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne ht hc1.1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (le_normalizer_of_comm hXc (hV2V.trans hVX) inf_le_left)] at h2
  obtain ⟨v2, hv2, c2, hc2, hvc2⟩ := h2
  have hvc1' : v1 * c1 = z := hvc1
  have hvc2' : v2 * c2 = c1 := hvc2
  have hc2L : c2 ∈ Subgroup.centralizer (L : Set G) := by
    have e : c2 = v2⁻¹ * c1 := by rw [← hvc2']; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hV2 hv2)) hc1.2
  have hc2L0 : c2 ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
    rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
    exact mem_centralizer_sup hc2L hc2.2
  have e : z = (v1 * v2) * c2 := by rw [← hvc1', ← hvc2']; group
  rw [e]
  exact Subgroup.mul_mem_sup ((fsuVM T L I).mul_mem (hV1V hv1) (hV2V hv2)) ⟨hc2.1, hc2L0⟩

end CFSG.Quasithin.Vol2.Ch10.SecC
