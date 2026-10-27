module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Max
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Vol2.Ch10SecEE3V
public import CFSG.Quasithin.Vol2.Ch10SecFX

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fixV_autI_fsuL0_eq_bot_case2 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I) :
    fixV (autI (SecA.isElemAbelian_fsuVM hyp) (fsuL0 T L)) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  have hc : IntMod.val w ∈ fsuCVM T L I := by
    refine ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have hlN : l ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
      SecA.fsuL0_le_normalizer_fsuVM T L I hl
    have h1 := (SecE.convI_fix_iff _ ⟨l, hlN⟩ w).mp (hw _ (convI_mem_autI _ hl hlN))
    calc l * IntMod.val w = (l * IntMod.val w * l⁻¹) * l := by group
      _ = IntMod.val w * l := by rw [h1]
  rw [fsuCVM_eq_bot_case2 h37 h38 hyp h2, Subgroup.mem_bot] at hc
  exact IntMod.val_injective (hc.trans IntMod.val_one.symm)

theorem commV_sup_eq_top_case2 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {hyp : Hyp10 G T L I} (h2 : Ch10.Case10_1_1Two T L I)
    {t : G} (D : SecE.Case2Data hyp t) : commV D.K₁ ⊔ commV D.K₂ = ⊤ := by
  have h := D.span
  rwa [fixV_autI_fsuL0_eq_bot_case2 h37 h38 hyp h2, bot_sup_eq] at h

theorem card_autI_mul_card_le (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {hyp : Hyp10 G T L I} (h2 : Ch10.Case10_1_1Two T L I)
    {t : G} (D : SecE.Case2Data hyp t) {A : Subgroup G} (hAT : A ≤ T)
    (hAJ : A ≤ thompsonJ T) :
    Nat.card (autI (SecA.isElemAbelian_fsuVM hyp) A) *
      Nat.card ↥(fsuVM T L I ⊓ Subgroup.centralizer (A : Set G)) ≤ Nat.card (fsuVM T L I) := by
  have hAN : A ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    hAT.trans (SecA.le_normalizer_fsuVM T L I)
  have h4 : autI (SecA.isElemAbelian_fsuVM hyp) A ≤ D.P₁ ⊔ D.P₂ :=
    D.thompsonJ_eq ▸ autI_mono _ hAJ
  have h5 := D.prodSetting.card_mul_card_fixV_le D.bound₁ D.bound₂ h4
  rw [commV_sup_eq_top_case2 h37 h38 h2 D, inf_top_eq, Subgroup.card_top] at h5
  have h6 : Nat.card (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) =
      Nat.card (fsuVM T L I) := rfl
  rw [h6, card_fixV_autI (SecA.isElemAbelian_fsuVM hyp) hAN] at h5
  exact h5

omit [Finite G] in
theorem isElemAbelian_sup_of_commute {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian 2 (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

omit [Finite G] in
theorem isElemAbelian_of_le {A B : Subgroup G} (hA : IsElemAbelian 2 A) (hBA : B ≤ A) :
    IsElemAbelian 2 B := CFSG.Open.IsElemAbelian.mono hA hBA

theorem fsuVM_le_thompsonJ (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {hyp : Hyp10 G T L I} (h2 : Ch10.Case10_1_1Two T L I) {t : G}
    (D : SecE.Case2Data hyp t) : fsuVM T L I ≤ thompsonJ T := by
  obtain ⟨A, ⟨hAT, hA⟩, hmax⟩ := SecE.exists_max_card_subgroup'
    (fun A : Subgroup G => A ≤ T ∧ IsElemAbelian 2 A)
    ⟨bot_le, ⟨inferInstance, fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩⟩
  have hAmax : IsMaxElemAbelian T A := ⟨hAT, hA, fun B hBT hB => hmax B ⟨hBT, hB⟩⟩
  have hAJ : A ≤ thompsonJ T := le_iSup₂_of_le A hAmax le_rfl
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hVT := SecA.fsuVM_le_T hyp
  set B := A ⊓ Subgroup.centralizer (fsuVM T L I : Set G) with hBdef
  have hBab : IsElemAbelian 2 B := isElemAbelian_of_le hA inf_le_left
  have hVB : ∀ v ∈ fsuVM T L I, ∀ b ∈ B, v * b = b * v := fun v hv b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 v hv
  have hA'ab := isElemAbelian_sup_of_commute hV hBab hVB
  have hA'T : fsuVM T L I ⊔ B ≤ T := sup_le hVT (inf_le_left.trans hAT)
  have hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' => by
    have := hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩
    simpa using congrArg Subtype.val this
  have hCA : fsuVM T L I ⊓ Subgroup.centralizer (A : Set G) ≤ A := by
    have hXab : IsElemAbelian 2 (fsuVM T L I ⊓ Subgroup.centralizer (A : Set G)) :=
      isElemAbelian_of_le hV inf_le_left
    have hXA' := isElemAbelian_sup_of_commute hXab hA fun x hx a ha =>
      (Subgroup.mem_centralizer_iff.mp hx.2 a ha).symm
    have hle := hmax _ ⟨sup_le (inf_le_left.trans hVT) hAT, hXA'⟩
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_right :
      A ≤ (fsuVM T L I ⊓ Subgroup.centralizer (A : Set G)) ⊔ A) hle
    exact le_sup_left.trans heq.symm.le
  have hVBinf : B ⊓ fsuVM T L I = fsuVM T L I ⊓ Subgroup.centralizer (A : Set G) := by
    apply le_antisymm
    · rintro x ⟨⟨hxA, -⟩, hxV⟩
      exact ⟨hxV, Subgroup.mem_centralizer_iff.mpr fun a ha => hAc a ha x hxA⟩
    · intro x hx
      exact ⟨⟨hCA hx, Subgroup.mem_centralizer_iff.mpr fun v hv =>
        SecA.comm_of_mem_fsuVM hyp hv hx.1⟩, hx.1⟩
  have hAN : A ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    hAT.trans (SecA.le_normalizer_fsuVM T L I)
  have h1 := card_autI_mul_card_inf hV hAN
  have h2' := card_autI_mul_card_le h37 h38 h2 D hAT hAJ
  have h3 := SecE.relIndex_sup_eq_relIndex (inf_le_left.trans hAN : B ≤ _)
  have h4 := Subgroup.relIndex_mul_card B (fsuVM T L I ⊔ B)
  have h5 := Subgroup.relIndex_mul_card B (fsuVM T L I)
  rw [inf_eq_left.mpr le_sup_right] at h4
  rw [hVBinf] at h5
  have h6 : Nat.card ↥(fsuVM T L I ⊔ B) *
      Nat.card ↥(fsuVM T L I ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card (fsuVM T L I) * Nat.card B := by
    rw [← h4, ← h5, h3]
    ring
  have hpos : 0 < Nat.card ↥(fsuVM T L I ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  have h7 : Nat.card A ≤ Nat.card ↥(fsuVM T L I ⊔ B) := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [h6, ← h1]
    calc Nat.card (autI hV A) * Nat.card B *
          Nat.card ↥(fsuVM T L I ⊓ Subgroup.centralizer (A : Set G)) =
        Nat.card (autI hV A) * Nat.card ↥(fsuVM T L I ⊓ Subgroup.centralizer (A : Set G)) *
          Nat.card B := by ring
      _ ≤ Nat.card (fsuVM T L I) * Nat.card B := Nat.mul_le_mul_right _ h2'
  have hA'max : IsMaxElemAbelian T (fsuVM T L I ⊔ B) :=
    ⟨hA'T, hA'ab, fun B' hB'T hB' => (hmax B' ⟨hB'T, hB'⟩).trans h7⟩
  exact le_sup_left.trans (le_iSup₂_of_le _ hA'max le_rfl)

end CFSG.Quasithin.Vol2.Ch10.SecF
