module

public import CFSG.Quasithin.Vol2.Ch10SecC8Main4c
public import CFSG.Quasithin.Vol2.Ch10SecC8Main12

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 SecB.L32 L3F
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuVM_inf_centralizer_le (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h484 : ASInputs.AS_B_4_8_four) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {U₂ : Subgroup G}
    (hU₂ : IsU10_2_8 T L I (CFSG.conjugate L t) U₂) {v : G} (hvU : v ∈ U₂)
    (hvC : v ∉ Subgroup.centralizer (fsuL0 T L : Set G)) {x : G} (hxV : x ∈ fsuVM T L I)
    (hxc : x ∈ Subgroup.centralizer
      ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G)) :
    x ∈ fsuCVM T L I ⊔ Subgroup.zpowers v := by
  obtain ⟨hc1, hc2, D, D₂, hF1, hF2⟩ := exists_comp_data h37 h38 hyp h1011 h484 h3 hne ht htn
  have hcv := coord_eq_e0 hF2 hU₂ hvU hvC
  obtain ⟨hKL0, hKN, hTK, hD₂, hact, hsq, hfix, hZc, hFF, hE4⟩ := hF2
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨hVeq, hV1, hV2, -⟩ := hdec t ht htn
  have hV1V : fsuUL T L I ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hV2V : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer hKN
  have hvW : v ∈ Vi T L I (CFSG.conjugate L t) := hU₂.1 hvU
  have hx' : x ∈ (↑(fsuUL T L I ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆) : Set G) := by
    rw [← hVeq]
    exact hxV
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (le_normalizer_of_le_fsuVM hyp hV2V hV1V)] at hx'
  obtain ⟨x₁, hx₁, x₂, hx₂, hxx⟩ := hx'
  have hxx' : x₁ * x₂ = x := hxx
  have hcomm : ∀ d ∈ T ⊓ Subgroup.centralizer ({v} : Set G), d * x * d⁻¹ = x := fun d hd => by
    rw [Subgroup.mem_centralizer_iff.mp hxc d hd, mul_inv_cancel_right]
  have h1 : x₁ ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
    refine mem_centralizer_fsuL0_of_inf h37 h38 hyp h1011 h484 h3 hne hx₁ fun d hd => ?_
    have hdv : d ∈ T ⊓ Subgroup.centralizer ({v} : Set G) := ⟨hd.1,
      mem_centralizer_of_mul_conj_eq (by
        rw [Subgroup.mem_centralizer_iff.mp (hV2 hvW) d hd.2, mul_inv_cancel_right])⟩
    have h2 := hcomm d hdv
    rw [← hxx'] at h2
    have hdx2 : d * x₂ * d⁻¹ = x₂ := by
      rw [Subgroup.mem_centralizer_iff.mp (hV2 hx₂) d hd.2, mul_inv_cancel_right]
    have e : d * (x₁ * x₂) * d⁻¹ = (d * x₁ * d⁻¹) * (d * x₂ * d⁻¹) := by group
    rw [e, hdx2] at h2
    exact mul_right_cancel h2
  have h2 : (⟨x₂, hx₂⟩ : ↥(Vi T L I (CFSG.conjugate L t))) ∈ secSub D₂ e0 := by
    rw [← fixes_ea_iff D₂ hsq hfix]
    intro γ hγ
    obtain ⟨⟨d, hdN⟩, hdTK, hdγ⟩ := SecB.mem_autOn_iff.mp ((hD₂ γ).mpr (ea_le γ hγ).2)
    have hdv : d * v * d⁻¹ = v := by
      have := π_fix_of_ka D₂ hsq hfix (ea_le γ hγ).1 hcv
      rw [← hdγ] at this
      exact congrArg Subtype.val this
    have h3' := hcomm d ⟨hdTK.1, mem_centralizer_of_mul_conj_eq hdv⟩
    rw [← hxx'] at h3'
    have hdx1 : d * x₁ * d⁻¹ = x₁ := by
      rw [Subgroup.mem_centralizer_iff.mp (hV1 hx₁) d hdTK.2, mul_inv_cancel_right]
    have e : d * (x₁ * x₂) * d⁻¹ = (d * x₁ * d⁻¹) * (d * x₂ * d⁻¹) := by group
    rw [e, hdx1] at h3'
    rw [← hdγ]
    exact Subtype.ext (mul_left_cancel h3')
  rw [← hxx']
  have hx1C : x₁ ∈ fsuCVM T L I := ⟨hV1V hx₁, h1⟩
  rcases h2 with h | h
  · have hx2C : x₂ ∈ fsuCVM T L I :=
      ⟨hV2V hx₂, Subgroup.mem_subgroupOf.mp ((coordOf_eq_zero_iff D₂ _).mp h)⟩
    exact Subgroup.mem_sup_left (Subgroup.mul_mem _ hx1C hx2C)
  ·
    have hm : x₂ * v⁻¹ ∈ Vi T L I (CFSG.conjugate L t) :=
      Subgroup.mul_mem _ hx₂ (Subgroup.inv_mem _ hvW)
    have h0 : coordOf D₂ ⟨x₂ * v⁻¹, hm⟩ = 0 := by
      have e : (⟨x₂ * v⁻¹, hm⟩ : ↥(Vi T L I (CFSG.conjugate L t))) =
          ⟨x₂, hx₂⟩ * (⟨v, hvW⟩)⁻¹ := rfl
      rw [e, coordOf_mul, coordOf_inv, h, hcv]
      exact add_neg_cancel _
    have hC : x₂ * v⁻¹ ∈ fsuCVM T L I := mem_fsuCVM_of_coord D₂ hKN hm h0
    have e : x₁ * x₂ = (x₁ * (x₂ * v⁻¹)) * v := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _ hx1C hC))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))

theorem omegaOne_centralizer_v2_eq (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1027 : Stmt10_2_7) (h484 : ASInputs.AS_B_4_8_four)
    (h3210 : TmpL6_3_2_10_nine) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {U₂ : Subgroup G}
    (hU₂ : IsU10_2_8 T L I (CFSG.conjugate L t) U₂) {v : G} (hvU : v ∈ U₂)
    (hvC : v ∉ Subgroup.centralizer (fsuL0 T L : Set G)) :
    omegaOneCenterOf (T ⊓ Subgroup.centralizer ({v} : Set G)) =
      omegaOneCenterOf (T1 T L) ⊔ Subgroup.zpowers v := by
  have hvW : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := hU₂.1 hvU
  have hvV : v ∈ fsuVM T L I := commutator_le_left_of_le_normalizer
    ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) hvW
  set S := T ⊓ Subgroup.centralizer ({v} : Set G) with hS
  have hST1 : S ≤ T1 T L := fun s hs =>
    mem_T1_of_fix h37 h38 hyp h1011 ht htn hvW hvC hs.1 (mul_conj_eq_of_mem_centralizer hs.2)
  have hQS : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ S := fun q hq =>
    ⟨hq.1, mem_centralizer_of_mul_conj_eq (by
      rw [← Subgroup.mem_centralizer_iff.mp hq.2 v hvV, mul_inv_cancel_right])⟩
  have hZQ := (omegaOne_le_Q hyp h1027 h37 h38 h1011).2
  have h1 : omegaOneCenterOf (T1 T L) ≤ omegaOneCenterOf S := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨⟨hzT1, hzc⟩, hz2⟩
    have hzQ := hZQ (Subgroup.subset_closure ⟨⟨hzT1, hzc⟩, hz2⟩)
    exact Subgroup.subset_closure ⟨⟨hQS hzQ, Subgroup.mem_centralizer_iff.mpr fun s hs =>
      Subgroup.mem_centralizer_iff.mp hzc s (hST1 hs)⟩, hz2⟩
  have h2 : v ∈ omegaOneCenterOf S := by
    refine Subgroup.subset_closure ⟨⟨⟨SecA.fsuVM_le_T hyp hvV,
      mem_centralizer_of_mul_conj_eq (by group)⟩, Subgroup.mem_centralizer_iff.mpr fun s hs =>
        (Subgroup.mem_centralizer_iff.mp hs.2 v rfl).symm⟩, ?_⟩
    exact (SecA.isElemAbelian_fsuVM hyp).2 v hvV
  refine le_antisymm ?_ (sup_le h1 (Subgroup.zpowers_le.mpr h2))
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨⟨hxS, hxc⟩, hx2⟩
  have hxcQ : x ∈ Subgroup.centralizer
      ((T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQS) hxc
  have hxQ : x ∈ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) :=
    inf_centralizer_Q_le hyp h1027 ⟨Subgroup.mem_sup_right hxS.1, hxcQ⟩
  have hxX : x ∈ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) :=
    Subgroup.subset_closure ⟨⟨hxQ, hxcQ⟩, hx2⟩
  rw [omegaOne_Q_eq h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne] at hxX
  have hXc : ∀ a ∈ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)),
      ∀ b ∈ omegaOneCenterOf (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)), a * b = b * a :=
    fun a ha b hb => A4.mul_comm_of_mem_omegaOneCenterOf ha hb
  have hT1X := omegaOne_T1_le_omegaOne_Q h37 h38 hyp h1011 h1027
  have hVX := fsuVM_le_omegaOneCenterOf hyp
  have hx' : x ∈ (↑(omegaOneCenterOf (T1 T L) ⊔ fsuVM T L I) : Set G) := hxX
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (le_normalizer_of_comm hXc hT1X hVX)] at hx'
  obtain ⟨z, hz, w, hw, hzw⟩ := hx'
  have hzw' : z * w = x := hzw
  have hzc : z ∈ Subgroup.centralizer (S : Set G) := (A4.omegaOneCenterOf_le_centerOf _ (h1 hz)).2
  have hwc : w ∈ Subgroup.centralizer (S : Set G) := by
    have e : w = z⁻¹ * x := by rw [← hzw']; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzc) hxc
  have hwC := fsuVM_inf_centralizer_le h37 h38 hyp h1011 h484 h3 hne ht htn hU₂ hvU hvC hw hwc
  have hCT1 : fsuCVM T L I ≤ omegaOneCenterOf (T1 T L) := by
    rw [omegaOne_T1_eq h37 h38 hyp h1011 h1012 h1027 h484 h3210 h3 hne]
    exact fun c hc => ⟨hVX hc.1, hc.2⟩
  have hle : fsuCVM T L I ⊔ Subgroup.zpowers v ≤
      omegaOneCenterOf (T1 T L) ⊔ Subgroup.zpowers v := sup_le_sup_right hCT1 _
  rw [← hzw']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hz) (hle hwC)

end CFSG.Quasithin.Vol2.Ch10.SecC
