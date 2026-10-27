module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Setup
public import CFSG.Quasithin.Vol2.Ch10SecEE3Alt
public import CFSG.Quasithin.Vol2.Ch10SecEE3ProdB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.QuasithinUnique.A5.Delta5 (pact isEven)

section Component

variable {W : Type*} [CommGroup W] {K : Subgroup (MulAut W)} {θ : ↥K ≃* Equiv.Perm (Fin 5)}
  {β : ↥(commV K) ≃* Multiplicative (evenWeight 5)}

theorem fixV_oTwoUpper_inf_commV_eq_bot (hβ : A5Equivariant θ β) :
    fixV (oTwoUpper K) ⊓ commV K = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hf, hw⟩
  have hO : ∀ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 → ((θ.symm σ : ↥K) : MulAut W) ∈ oTwoUpper K := by
    intro σ hσ
    by_cases h1 : σ = 1
    · rw [h1, map_one]; exact (oTwoUpper K).one_mem
    · refine mem_oTwoUpper_of_odd (θ.symm σ).2 ?_
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact odd_orderOf_of_pow_three hσ h1
  have hfix : ∀ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 →
      pact σ ((Multiplicative.toAdd (β ⟨w, hw⟩) : evenWeight 5) : Fin 5 → ZMod 2) =
        ((Multiplicative.toAdd (β ⟨w, hw⟩) : evenWeight 5) : Fin 5 → ZMod 2) := by
    intro σ hσ
    have h1 := coord_apply θ β hβ (θ.symm σ) ⟨w, hw⟩
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← h1]
    congr 3
    exact Subtype.ext (hf _ (hO σ hσ))
  have h0 := eq_zero_of_fix_cThree _ (Multiplicative.toAdd (β ⟨w, hw⟩)).2
    (hfix cThree (by decide)) (hfix cThree' (by decide))
  have h1 : β ⟨w, hw⟩ = 1 :=
    Multiplicative.toAdd.injective (Subtype.ext (h0.trans rfl))
  have h2 := β.injective (h1.trans (map_one β).symm)
  exact congrArg Subtype.val h2

end Component

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Case2Data

variable {hyp : Hyp10 G T L I} {t : G} (D : Case2Data hyp t)

noncomputable abbrev P₁ : Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))) :=
  D.K₁ ⊓ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T)

noncomputable abbrev P₂ : Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))) :=
  D.K₂ ⊓ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T)

theorem triv₁ {a} (ha : a ∈ D.K₁) {w} (hw : w ∈ commV D.K₂) : a w = w :=
  fix_commV_of_commute D.equiv₂ (fun k hk => D.comm a ha k hk) hw

theorem triv₂ {b} (hb : b ∈ D.K₂) {w} (hw : w ∈ commV D.K₁) : b w = w :=
  fix_commV_of_commute D.equiv₁ (fun k hk => (D.comm k hk b hb).symm) hw

theorem commV_inf_commV : commV D.K₁ ⊓ commV D.K₂ = ⊥ := by
  rw [eq_bot_iff, ← fixV_oTwoUpper_inf_commV_eq_bot D.equiv₁]
  rintro w ⟨hw₁, hw₂⟩
  exact ⟨fun a ha => D.triv₁ (oTwoUpper_le D.K₁ ha) hw₂, hw₁⟩

theorem prodSetting : ProdSetting (commV D.K₁) (commV D.K₂) D.P₁ D.P₂ :=
  ⟨D.commV_inf_commV, fun a ha b hb => D.comm a ha.1 b hb.1,
    eq_bot_iff.mpr (D.inf ▸ inf_le_inf inf_le_left inf_le_left),
    fun _ ha _ hw => commV_invariant D.K₁ _ ha.1 _ hw,
    fun _ hb _ hw => commV_invariant D.K₂ _ hb.1 _ hw,
    fun _ ha _ hw => D.triv₁ ha.1 hw, fun _ hb _ hw => D.triv₂ hb.1 hw⟩

theorem card_commV₁ : Nat.card ↥(commV D.K₁) = 16 := card_commV_of_isA5Module D.β₁

theorem card_commV₂ : Nat.card ↥(commV D.K₂) = 16 := card_commV_of_isA5Module D.β₂

theorem bound₁ (Y : Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))))
    (hY : Y ≤ D.P₁) : Nat.card Y * Nat.card ↥(fixV Y ⊓ commV D.K₁) ≤ Nat.card ↥(commV D.K₁) :=
  D.card_commV₁ ▸ (factor_bound D.equiv₁ inf_le_left D.memP₁ hY).1

theorem bound₂ (Y : Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))))
    (hY : Y ≤ D.P₂) : Nat.card Y * Nat.card ↥(fixV Y ⊓ commV D.K₂) ≤ Nat.card ↥(commV D.K₂) :=
  D.card_commV₂ ▸ (factor_bound D.equiv₂ inf_le_left D.memP₂ hY).1

end Case2Data

end CFSG.Quasithin.Vol2.Ch10.SecE
