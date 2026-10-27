module

public import CFSG.Quasithin.Vol2.Ch10SecA1012One

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuCVM_eq_bot_of_cV1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) (hC : Ch10.cV1 T L I = ⊥) : fsuCVM T L I = ⊥ := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hne
    push Not at hne
    exact hyp.not_normal hne
  obtain ⟨hab, -, -, -, -⟩ := hyp.three
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hUV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hUtV : CFSG.conjugate (fsuUL T L I) t ≤ fsuVM T L I := by
    have h' := conjugate_mono hUV t
    rwa [conjugate_fsuVM (le_fsuM T L ht)] at h'
  have hconj : CFSG.conjugate (fsuUL T L I) t = ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
    conjugate_commutator_fsuVM (le_fsuM T L ht)
  have hUtL : CFSG.conjugate (fsuUL T L I) t ≤ Subgroup.centralizer (L : Set G) :=
    hconj ▸ commutator_conjugate_le_centralizer h37 h38 hyp ht htn
  have hsup : fsuUL T L I ⊔ CFSG.conjugate (fsuUL T L I) t = fsuVM T L I := by
    rw [hconj]
    exact (fsuVM_eq_sup h37 h38 hyp ht htn).symm
  have hUL : ∀ u ∈ fsuUL T L I, u ∈ Subgroup.centralizer (L : Set G) → u = 1 := by
    intro u hu huL
    have hmem : (⟨u, hu⟩ : ↥(fsuUL T L I)) ∈ Ch10.cV1 T L I := by
      rw [cV1_eq h37 h38 hyp, Subgroup.mem_subgroupOf]
      exact huL
    rw [hC] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  rw [eq_bot_iff]
  rintro v ⟨hvV, hvC⟩
  rw [Subgroup.mem_bot]
  have htop := InternalSec.sup_subgroupOf_eq_top hUV hUtV hsup
  have hmem : (⟨v, hvV⟩ : ↥(fsuVM T L I)) ∈
      (fsuUL T L I).subgroupOf (fsuVM T L I) ⊔
        (CFSG.conjugate (fsuUL T L I) t).subgroupOf (fsuVM T L I) :=
    htop ▸ Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hmem
  rw [Subgroup.mem_subgroupOf] at hy hz
  have hyz' : (y : G) * (z : G) = v := congrArg Subtype.val hyz
  have hvL : v ∈ Subgroup.centralizer (L : Set G) := Subgroup.centralizer_le (le_fsuL0 T L) hvC
  have hyL : (y : G) ∈ Subgroup.centralizer (L : Set G) := by
    have : (y : G) = v * (z : G)⁻¹ := by rw [← hyz']; group
    rw [this]
    exact Subgroup.mul_mem _ hvL (Subgroup.inv_mem _ (hUtL hz))
  have hy1 : (y : G) = 1 := hUL _ hy hyL
  have hzv : (z : G) = v := by rw [← hyz', hy1, one_mul]
  have hvLt : v ∈ Subgroup.centralizer (CFSG.conjugate L t : Set G) :=
    Subgroup.centralizer_le (conjugate_le_fsuL0 ht) hvC
  have hvU : t * v * t⁻¹ ∈ fsuUL T L I := by
    have := hz
    rw [hzv, mem_conjugate_iff] at this
    exact this
  have hvL' : t * v * t⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : t⁻¹ * l * t ∈ CFSG.conjugate L t := by
      rw [mem_conjugate_iff]
      simpa [mul_assoc] using hl
    have h1 := Subgroup.mem_centralizer_iff.mp hvLt _ hl'
    calc l * (t * v * t⁻¹) = t * ((t⁻¹ * l * t) * v) * t⁻¹ := by group
      _ = t * (v * (t⁻¹ * l * t)) * t⁻¹ := by rw [h1]
      _ = t * v * t⁻¹ * l := by group
  have h1 := hUL _ hvU hvL'
  have := congrArg (fun x => t⁻¹ * x * t) h1
  simpa [mul_assoc] using this

theorem fsuCVM_eq_bot_of_thompsonJ (h3210 : TmpL6_3_2_10_nine) (hyp : Ch10.Hyp10 G T L I)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) : fsuCVM T L I = ⊥ := by
  by_cases hs : Sub326iii T L I
  · exact (h3210 G T L I (fsuVM T L I) hyp.fsu (Or.inl ⟨hs, rfl⟩) hJ).2
  · have hVV : fsuV T I = fsuVM T L I := by
      obtain ⟨hab, -, -, -, -, -, hc⟩ := hyp.three
      rcases hc with ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨he, hsum, h5⟩
      · exact h
      · exact h
      · exact absurd ⟨hyp.lt, hab, he, hsum, h5⟩ hs
    exact (h3210 G T L I (fsuVM T L I) hyp.fsu (Or.inr ⟨hs, hVV.symm⟩) hJ).2

theorem fsuCVM_eq_bot
    (hF : Facts10_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h42 : AsB42) (h51 : AsB51) (h154 : AsB15Part4) (h116 : ASInputs.AS_I_1_6_one)
    (h3210 : TmpL6_3_2_10_nine) (hyp : Ch10.Hyp10 G T L I)
    (hnot : ¬ ((∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Three T L I)) :
    fsuCVM T L I = ⊥ := by
  obtain ⟨hab, -, -, -, -, -, hc⟩ := hyp.three
  by_cases hFF : IsFFModule (V := ↥(fsuVM T L I)) (autOn (fsuL0 T L ⊔ T) (fsuVM T L I))
  · rcases hc with ⟨hUI, hVV⟩ | ⟨-, hVV, hcard, s, hsT, hsN, hsO, hU, hinf⟩ | ⟨he, hsum, h5⟩
    · rcases cases123_of_isFFModule hF h37 h38 h322 hshape h42 h154 h116 hyp hUI hVV hFF with
        h | h | h
      · exact absurd (Or.inl h) hnot
      · exact fsuCVM_eq_bot_of_cV1 h37 h38 hyp h.2
      · exact absurd (Or.inr h) hnot
    · exact absurd hFF (not_isFFModule_of_case_five h37 h38 hshape h322 h154 h51 hyp hVV hcard
        hsT hsN hsO hU hinf)
    · exact absurd hFF (not_isFFModule_of_case_six h37 h38 h322 h154 hyp he hsum h5)
  · exact fsuCVM_eq_bot_of_thompsonJ h3210 hyp
      (thompsonJ_le_centralizer_of_not_isFFModule hyp fun _ => hFF)

end CFSG.Quasithin.Vol2.Ch10.SecA
