module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Inv
public import CFSG.Quasithin.Vol2.Ch10SecEE3Max

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem autI_thompsonJ_le_iSup (hyp : Hyp10 G T L I) :
    autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T) ≤
      ⨆ (A : Subgroup G) (_ : IsMaxElemAbelian T A), autI (SecA.isElemAbelian_fsuVM hyp) A := by
  set H' := ⨆ (A : Subgroup G) (_ : IsMaxElemAbelian T A), autI (SecA.isElemAbelian_fsuVM hyp) A
  set Q := (H'.comap (convI (SecA.isElemAbelian_fsuVM hyp))).map
    (Subgroup.normalizer (fsuVM T L I : Set G)).subtype
  have hJQ : thompsonJ T ≤ Q := by
    refine iSup₂_le fun A hA a ha => ?_
    have haN : a ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
      SecA.le_normalizer_fsuVM T L I (hA.1 ha)
    refine ⟨⟨a, haN⟩, ?_, rfl⟩
    have hle := le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian T A) =>
      autI (SecA.isElemAbelian_fsuVM hyp) A) A hA
    exact hle (convI_mem_autI _ ha haN)
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := (mem_autI _).mp hφ
  obtain ⟨g', hg', e⟩ := hJQ hg
  have : g' = g := Subtype.ext e
  rw [← this]
  exact hg'

namespace Case2Data

variable {hyp : Hyp10 G T L I} {t : G} (D : Case2Data hyp t)
include D

theorem card_mul_card_fixV_eq_of_max (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) :
    Nat.card ↥(autI (SecA.isElemAbelian_fsuVM hyp) A) *
        Nat.card ↥(fixV (autI (SecA.isElemAbelian_fsuVM hyp) A) ⊓ (commV D.K₁ ⊔ commV D.K₂)) =
      Nat.card ↥(commV D.K₁ ⊔ commV D.K₂) := by
  have hAN : A ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    hA.1.trans (SecA.le_normalizer_fsuVM T L I)
  have h1 := card_autI_mul_card_inf (SecA.isElemAbelian_fsuVM hyp) hAN
  have h3 := card_fixV_autI (SecA.isElemAbelian_fsuVM hyp) hAN
  have hab := hA.2.1.1
  have hVab := (SecA.isElemAbelian_fsuVM hyp).1
  have hCA : fsuVM T L I ⊓ Subgroup.centralizer (A : Set G) ≤ A := by
    have hel : IsElemAbelian 2 (fsuVM T L I ⊓ Subgroup.centralizer (A : Set G)) :=
      ⟨IsMulCommutative.of_setLike_mul_comm fun x hx y hy => setLike_mul_comm hx.1 hy.1,
        fun x hx => (SecA.isElemAbelian_fsuVM hyp).2 x hx.1⟩
    have hB := isElemAbelian_sup_of_commute' hA.2.1 hel fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp hb.2 a ha
    have hBT : A ⊔ (fsuVM T L I ⊓ Subgroup.centralizer (A : Set G)) ≤ T :=
      sup_le hA.1 (inf_le_left.trans (SecA.fsuVM_le_T hyp))
    have heq := Subgroup.eq_of_le_of_card_ge le_sup_left (hA.2.2 _ hBT hB)
    exact le_sup_right.trans heq.symm.le
  have heqC : A ⊓ Subgroup.centralizer (fsuVM T L I : Set G) =
      fsuVM T L I ⊓ Subgroup.centralizer (A : Set G) := by
    refine le_antisymm (fun x hx => ⟨hCV ⟨hA.1 hx.1, hx.2⟩,
      Subgroup.mem_centralizer_iff.mpr fun a ha => setLike_mul_comm ha hx.1⟩) fun x hx =>
      ⟨hCA hx, Subgroup.mem_centralizer_iff.mpr fun v hv => setLike_mul_comm hv hx.1⟩
  have hAV : Nat.card A = Nat.card (fsuVM T L I) := le_antisymm
    (D.card_le_of_le_thompsonJ hC0 hCV hA.1 hA.2.1 (le_iSup₂_of_le A hA le_rfl))
    (hA.2.2 _ (SecA.fsuVM_le_T hyp) (SecA.isElemAbelian_fsuVM hyp))
  rw [D.commV_sup_eq_top hC0, inf_top_eq, Subgroup.card_top, h3, ← heqC, h1, hAV]
  rfl

theorem exists_involution₁ (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ = sA ∨ σ = sB) :
    ∃ g : Subgroup.normalizer (fsuVM T L I : Set G), (g : G) ∈ T ∧ (g : G) ^ 2 = 1 ∧
      convI (SecA.isElemAbelian_fsuVM hyp) g = ((D.θ₁.symm σ : ↥D.K₁) : MulAut _) := by
  set 𝒜 := {X | ∃ A, IsMaxElemAbelian T A ∧ X = autI (SecA.isElemAbelian_fsuVM hyp) A}
  have h𝒜 : ∀ X ∈ 𝒜, X ≤ D.P₁ ⊔ D.P₂ ∧ Nat.card X * Nat.card ↥(fixV X ⊓
      (commV D.K₁ ⊔ commV D.K₂)) = Nat.card ↥(commV D.K₁ ⊔ commV D.K₂) := by
    rintro _ ⟨A, hA, rfl⟩
    exact ⟨D.thompsonJ_eq ▸ autI_mono _ (le_iSup₂_of_le A hA le_rfl),
      D.card_mul_card_fixV_eq_of_max hC0 hCV hA⟩
  have hP : D.P₁ ≤ ⨆ X ∈ 𝒜, X :=
    inf_le_right.trans ((autI_thompsonJ_le_iSup hyp).trans
      (iSup₂_le fun A hA => le_iSup₂_of_le (autI (SecA.isElemAbelian_fsuVM hyp) A) ⟨A, hA, rfl⟩
        le_rfl))
  obtain ⟨_, ⟨A, hA, rfl⟩, hX⟩ := exists_mem_of_side D.prodSetting D.equiv₁ inf_le_left D.memP₁
    D.bound₂ h𝒜 hP hσ
  obtain ⟨g, hgA, hg⟩ := (mem_autI _).mp hX
  exact ⟨g, hA.1 hgA, hA.2.1.2 _ hgA, hg⟩

theorem exists_involution₂ (hC0 : T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥)
    (hCV : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ fsuVM T L I)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ = sA ∨ σ = sB) :
    ∃ g : Subgroup.normalizer (fsuVM T L I : Set G), (g : G) ∈ T ∧ (g : G) ^ 2 = 1 ∧
      convI (SecA.isElemAbelian_fsuVM hyp) g = ((D.θ₂.symm σ : ↥D.K₂) : MulAut _) := by
  set 𝒜 := {X | ∃ A, IsMaxElemAbelian T A ∧ X = autI (SecA.isElemAbelian_fsuVM hyp) A}
  have h𝒜 : ∀ X ∈ 𝒜, X ≤ D.P₂ ⊔ D.P₁ ∧ Nat.card X * Nat.card ↥(fixV X ⊓
      (commV D.K₂ ⊔ commV D.K₁)) = Nat.card ↥(commV D.K₂ ⊔ commV D.K₁) := by
    rintro _ ⟨A, hA, rfl⟩
    rw [sup_comm D.P₂, sup_comm (commV D.K₂)]
    exact ⟨D.thompsonJ_eq ▸ autI_mono _ (le_iSup₂_of_le A hA le_rfl),
      D.card_mul_card_fixV_eq_of_max hC0 hCV hA⟩
  have hP : D.P₂ ≤ ⨆ X ∈ 𝒜, X :=
    inf_le_right.trans ((autI_thompsonJ_le_iSup hyp).trans
      (iSup₂_le fun A hA => le_iSup₂_of_le (autI (SecA.isElemAbelian_fsuVM hyp) A) ⟨A, hA, rfl⟩
        le_rfl))
  obtain ⟨_, ⟨A, hA, rfl⟩, hX⟩ := exists_mem_of_side D.prodSetting.symm D.equiv₂ inf_le_left
    D.memP₂ D.bound₁ h𝒜 hP hσ
  obtain ⟨g, hgA, hg⟩ := (mem_autI _).mp hX
  exact ⟨g, hA.1 hgA, hA.2.1.2 _ hgA, hg⟩

end Case2Data

end CFSG.Quasithin.Vol2.Ch10.SecE
