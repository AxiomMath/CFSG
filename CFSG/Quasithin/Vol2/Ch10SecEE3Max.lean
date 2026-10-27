module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Data
public import CFSG.Quasithin.Vol2.Ch10SecEE3ProdC

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_max_card_subgroup' (P : Subgroup G → Prop) (hP : P ⊥) :
    ∃ A : Subgroup G, P A ∧ ∀ B : Subgroup G, P B → Nat.card B ≤ Nat.card A := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) (fun B => Nat.card B)
    ⟨⊥, by simpa using hP⟩
  exact ⟨A, (Finset.mem_filter.mp hA).2, fun B hB => hmax B (by simpa using hB)⟩

theorem fixV_autI_fsuL0_eq_bot (hyp : Hyp10 G T L I)
    (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥) :
    fixV (autI (SecA.isElemAbelian_fsuVM hyp) (fsuL0 T L)) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  have hc : IntMod.val w ∈ T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) := by
    refine ⟨SecA.fsuVM_le_T hyp w.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have hlN : l ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
      SecA.fsuL0_le_normalizer_fsuVM T L I hl
    have h1 := (convI_fix_iff _ ⟨l, hlN⟩ w).mp (hw _ (convI_mem_autI _ hl hlN))
    calc l * IntMod.val w = (l * IntMod.val w * l⁻¹) * l := by group
      _ = IntMod.val w * l := by rw [h1]
  rw [hC0, Subgroup.mem_bot] at hc
  exact IntMod.val_injective (hc.trans IntMod.val_one.symm)

namespace Case2Data

variable {hyp : Hyp10 G T L I} {t : G} (D : Case2Data hyp t)
include D

theorem commV_sup_eq_top (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥) :
    commV D.K₁ ⊔ commV D.K₂ = ⊤ := by
  have h := D.span
  rwa [fixV_autI_fsuL0_eq_bot hyp hC0, bot_sup_eq] at h

theorem card_le_of_le_thompsonJ (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I) {A : Subgroup G}
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hAJ : A ≤ thompsonJ T) :
    Nat.card A ≤ Nat.card (fsuVM T L I) := by
  have hAN : A ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    hAT.trans (SecA.le_normalizer_fsuVM T L I)
  have h1 := card_autI_mul_card_inf (SecA.isElemAbelian_fsuVM hyp) hAN
  have h3 := card_fixV_autI (SecA.isElemAbelian_fsuVM hyp) hAN
  have hab := hA.1
  have h2 : Nat.card ↥(A ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) ≤
      Nat.card ↥(fsuVM T L I ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hCV ⟨hAT hx.1, hx.2⟩, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => setLike_mul_comm ha hx.1
  have h4 : autI (SecA.isElemAbelian_fsuVM hyp) A ≤ D.P₁ ⊔ D.P₂ :=
    D.thompsonJ_eq ▸ autI_mono _ hAJ
  have h5 := D.prodSetting.card_mul_card_fixV_le D.bound₁ D.bound₂ h4
  rw [D.commV_sup_eq_top hC0, inf_top_eq, Subgroup.card_top] at h5
  have h6 : Nat.card (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) =
      Nat.card (fsuVM T L I) := rfl
  rw [h6, h3] at h5
  rw [← h1]
  exact (Nat.mul_le_mul_left _ h2).trans h5

theorem isMaxElemAbelian_fsuVM (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I) :
    IsMaxElemAbelian T (fsuVM T L I) := by
  refine ⟨SecA.fsuVM_le_T hyp, SecA.isElemAbelian_fsuVM hyp, fun B hBT hB => ?_⟩
  obtain ⟨A, ⟨hAT, hA⟩, hmax⟩ := exists_max_card_subgroup'
    (fun A : Subgroup G => A ≤ T ∧ IsElemAbelian 2 A)
    ⟨bot_le, ⟨inferInstance, fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩⟩
  have hAmax : IsMaxElemAbelian T A := ⟨hAT, hA, fun B hBT hB => hmax B ⟨hBT, hB⟩⟩
  have hAJ : A ≤ thompsonJ T := le_iSup₂_of_le A hAmax le_rfl
  exact (hmax B ⟨hBT, hB⟩).trans (D.card_le_of_le_thompsonJ hC0 hCV hAT hA hAJ)

theorem fsuVM_le_baum (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I) :
    fsuVM T L I ≤ thompsonJ T ∧ fsuVM T L I ≤ baum T := by
  have hVJ : fsuVM T L I ≤ thompsonJ T :=
    le_iSup₂_of_le (fsuVM T L I) (D.isMaxElemAbelian_fsuVM hC0 hCV) le_rfl
  refine ⟨hVJ, le_inf (SecA.fsuVM_le_T hyp) ?_⟩
  rw [Subgroup.le_centralizer_iff]
  refine (Subgroup.closure_le _).mpr ?_
  rintro z ⟨⟨-, hzC⟩, -⟩
  exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
    Subgroup.mem_centralizer_iff.mp hzC v (hVJ hv)

end Case2Data

end CFSG.Quasithin.Vol2.Ch10.SecE
