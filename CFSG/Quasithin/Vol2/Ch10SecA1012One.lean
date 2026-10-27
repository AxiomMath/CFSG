module

public import CFSG.Quasithin.Vol2.Ch10SecA1011OneMain
public import CFSG.Quasithin.Vol2.Ch10SecA1012FiveMain

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem isFFModule_autOn_yOne
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h154 : AsB15Part4) (hyp : Ch10.Hyp10 G T L I)
    [IsMulCommutative ↥(fsuVM T L I)] (hVV : fsuV T I = fsuVM T L I)
    (hFF : IsFFModule (V := ↥(fsuVM T L I)) (autOn (fsuL0 T L ⊔ T) (fsuVM T L I)))
    [IsMulCommutative ↥(fsuUL T L I)] :
    IsFFModule (V := ↥(fsuUL T L I)) (autOn (yOne T L) (fsuUL T L I)) := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hne
    push Not at hne
    exact hyp.not_normal hne
  have hel := isElemAbelian_fsuVM hyp
  have hVt : ∀ v : ↥(fsuVM T L I), v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hel.2 _ v.2)
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hHN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    sup_le (fsuL0_le_normalizer_fsuVM T L I) (le_normalizer_fsuVM T L I)
  have htV : t ∈ Subgroup.normalizer (fsuVM T L I : Set G) := le_normalizer_fsuVM T L I ht
  have hUV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hYU : yOne T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator (inf_le_left.trans hHN) inf_le_right
  have hcomp := isComponentOf_autOn h37 h38 h322 hyp
  have key : ∀ B : Subgroup (MulAut ↥(fsuVM T L I)),
      IsFFStarOffender (autOn (fsuL0 T L ⊔ T) (fsuVM T L I)) B →
        ¬ B ≤ centSub ((fsuUL T L I).subgroupOf (fsuVM T L I)) →
          IsFFModule (V := ↥(fsuUL T L I)) (autOn (yOne T L) (fsuUL T L I)) := by
    intro B hB hnt
    have hBN := h154 _ hVt _ B hB _ hcomp
    have hBY : B ≤ autOn (yOne T L) (fsuVM T L I) :=
      fun φ hφ => mem_autOn_inf_normalizer h37 h38 hyp (hB.1 hφ) (hBN hφ)
    exact InternalSec.isFFModule_autOn_of_offender hel.2 hUV hYU ⟨hBY, hB.2⟩ hnt
  obtain ⟨A, hA⟩ := ((B1_4_5 hVt _).out 1 2).1 hFF
  by_cases hAU : A ≤ centSub ((fsuUL T L I).subgroupOf (fsuVM T L I))
  · set tbar := conjAct (fsuVM T L I) ⟨t, htV⟩
    have htX : tbar ∈ autOn (fsuL0 T L ⊔ T) (fsuVM T L I) :=
      mem_autOn_iff'.mpr ⟨⟨t, htV⟩, Subgroup.mem_sup_right ht, rfl⟩
    refine key (B1.conjAut tbar A) (B1.isFFStarOffender_conjAut hA htX) fun h => hA.2.1 ?_
    have hUtV : CFSG.conjugate (fsuUL T L I) t ≤ fsuVM T L I := by
      have h' := conjugate_mono hUV t
      rwa [conjugate_fsuVM (le_fsuM T L ht)] at h'
    have hVsup := fsuVM_le_sup_of_eq h37 h38 hyp hVV ht htn
    have htop' : (fsuUL T L I).subgroupOf (fsuVM T L I) ⊔
        (CFSG.conjugate (fsuUL T L I) t).subgroupOf (fsuVM T L I) = ⊤ :=
      InternalSec.sup_subgroupOf_eq_top hUV hUtV (le_antisymm (sup_le hUV hUtV) hVsup)
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have h1 : ∀ w ∈ (fsuUL T L I).subgroupOf (fsuVM T L I), a w = w := fun w hw =>
      mem_centSub.mp (hAU ha) w hw
    have h2 : ∀ w ∈ (CFSG.conjugate (fsuUL T L I) t).subgroupOf (fsuVM T L I), a w = w := by
      intro w hw
      rw [subgroupOf_conjugate htV] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      have hmem : tbar * a * tbar⁻¹ ∈ B1.conjAut tbar A := by
        rw [B1.mem_conjAut]
        simpa [mul_assoc] using ha
      show a (tbar⁻¹ u) = tbar⁻¹ u
      have h3 : (tbar * a * tbar⁻¹) u = u := mem_centSub.mp (h hmem) u hu
      rw [MulAut.mul_apply, MulAut.mul_apply] at h3
      calc a (tbar⁻¹ u) = tbar⁻¹ (tbar (a (tbar⁻¹ u))) := (tbar.symm_apply_apply _).symm
        _ = tbar⁻¹ u := by rw [h3]
    have hle : (⊤ : Subgroup ↥(fsuVM T L I)) ≤
        MonoidHom.eqLocus a.toMonoidHom (MonoidHom.id _) := by
      rw [← htop']
      exact sup_le (fun w hw => h1 w hw) (fun w hw => h2 w hw)
    ext v
    exact congrArg Subtype.val (hle (Subgroup.mem_top v))
  · exact key A hA hAU

theorem cases123_of_isFFModule
    (hF : Facts10_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h42 : AsB42) (h154 : AsB15Part4) (h116 : ASInputs.AS_I_1_6_one) (hyp : Ch10.Hyp10 G T L I)
    (hUI : fsuUL T L I = I) (hVV : fsuV T I = fsuVM T L I) [IsMulCommutative ↥(fsuVM T L I)]
    (hFF : IsFFModule (V := ↥(fsuVM T L I)) (autOn (fsuL0 T L ⊔ T) (fsuVM T L I))) :
    (∃ n, Ch10.Case10_1_1One T L I n) ∨ (Ch10.Case10_1_1Two T L I ∧ Ch10.cV1 T L I = ⊥) ∨
      Ch10.Case10_1_1Three T L I := by
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hUV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have : IsMulCommutative ↥(fsuUL T L I) := isMulCommutative_of_le hUV
  have h := oneSec_of h37 h38 h322 hshape hyp hUI
  have := h.simple
  have hFFU := isFFModule_autOn_yOne h37 h38 h322 h154 hyp hVV hFF
  have hFFS := (isec_of_one h37 h38 h322 hyp hUI).isFFModule_sec hFFU
  obtain ⟨A, hA⟩ := ((B1_4_5 h.sq _).out 1 2).1 hFFS
  exact cases_of_b42Out h37 h38 h322 hshape h116 hyp hUI
    (b42_of_isShapeGroup hF h.sq h.b4 hA (h42 _ h.sq _ _ h.b4 A hA) h.shape)

theorem not_isFFModule_of_not_cases123
    (hF : Facts10_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h42 : AsB42) (h51 : AsB51) (h154 : AsB15Part4) (h116 : ASInputs.AS_I_1_6_one)
    (hyp : Ch10.Hyp10 G T L I)
    (hnot : ¬ ((∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I ∨
      Ch10.Case10_1_1Three T L I)) [IsMulCommutative ↥(fsuVM T L I)] :
    ¬ IsFFModule (V := ↥(fsuVM T L I)) (autOn (fsuL0 T L ⊔ T) (fsuVM T L I)) := by
  intro hFF
  obtain ⟨hab, -, -, -, -, -, hc⟩ := hyp.three
  rcases hc with ⟨hUI, hVV⟩ | ⟨-, hVV, hcard, s, hsT, hsN, hsO, hU, hinf⟩ | ⟨he, hsum, h5⟩
  · rcases cases123_of_isFFModule hF h37 h38 h322 hshape h42 h154 h116 hyp hUI hVV hFF with
      h | h | h
    · exact hnot (Or.inl h)
    · exact hnot (Or.inr (Or.inl h.1))
    · exact hnot (Or.inr (Or.inr h))
  · exact not_isFFModule_of_case_five h37 h38 hshape h322 h154 h51 hyp hVV hcard hsT hsN hsO hU
      hinf hFF
  · exact not_isFFModule_of_case_six h37 h38 h322 h154 hyp he hsum h5 hFF

theorem thompsonJ_le_centralizer_of_not_isFFModule (hyp : Ch10.Hyp10 G T L I)
    (hnot : ∀ _ : IsMulCommutative ↥(fsuVM T L I),
      ¬ IsFFModule (V := ↥(fsuVM T L I)) (autOn (fsuL0 T L ⊔ T) (fsuVM T L I))) :
    thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
  have hel : IsElemAbelian 2 (fsuVM T L I) := isElemAbelian_fsuVM hyp
  have := hel.1
  have hVH : fsuVM T L I ≤ fsuL0 T L ⊔ T := (fsuVM_le_T hyp).trans le_sup_right
  have hHN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    sup_le (fsuL0_le_normalizer_fsuVM T L I) (le_normalizer_fsuVM T L I)
  have hTH : IsSylowTwoOf T (fsuL0 T L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right
  refine iSup₂_le fun A hA => ?_
  by_contra hAV
  have hoff : IsFFStarOffender (autI hel (fsuL0 T L ⊔ T)) (autI hel A) :=
    offenderImages_isFFStarOffender hel hVH hHN
      ⟨A, ⟨isMaxElemAbelian_of_isSylowTwoOf hTH hA, hAV⟩, rfl⟩
  exact hnot hel.1 (((B1_4_5 (fun v => IntMod.sq_eq_one v) _).out 2 1).1
    (⟨_, hoff⟩ : {B | IsFFStarOffender (autI hel (fsuL0 T L ⊔ T)) B}.Nonempty))

end CFSG.Quasithin.Vol2.Ch10.SecA
