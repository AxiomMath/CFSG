module

public import CFSG.LocalAnalysis.StandardType.GGWitExcModelAbs

public section

namespace CFSG.StandardType.ZS


theorem owEm_commute_map_iff {G H : Type*} [Group G] [Group H] (φ : G →* H) (hφ : Function.Injective φ) (a b : G) :
    Commute (φ a) (φ b) ↔ Commute a b := by
  constructor
  · intro h
    apply hφ
    simpa [map_mul] using h.eq
  · exact fun h => h.map φ

theorem owEm_card_closure_map {G H : Type*} [Group G] [Group H] (φ : G →* H) (hφ : Function.Injective φ)
    (s : Set G) : Nat.card (Subgroup.closure (φ '' s)) = Nat.card (Subgroup.closure s) := by
  rw [← MonoidHom.map_closure]
  exact Nat.card_congr ((Subgroup.closure s).equivMapOfInjective φ hφ).symm

theorem owEm_isReflMat_conj {n : ℕ} (g m : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) (h : IsReflMat g) :
    IsReflMat (m * g * m⁻¹) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · calc m * g * m⁻¹ * (m * g * m⁻¹) = m * (g * g) * m⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · have e : ((m * g * m⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) : Matrix (Fin n) (Fin n) (ZMod 13)) - 1 =
        (m : Matrix (Fin n) (Fin n) (ZMod 13)) * ((g : Matrix (Fin n) (Fin n) (ZMod 13)) - 1) *
          ((m⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) : Matrix (Fin n) (Fin n) (ZMod 13)) := by
      have hm : (m : Matrix (Fin n) (Fin n) (ZMod 13)) *
          ((m⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) : Matrix (Fin n) (Fin n) (ZMod 13)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [mul_sub, sub_mul, mul_one, hm]
      simp [Units.val_mul, mul_assoc]
    rw [e, Matrix.rank_mul_eq_left_of_isUnit_det
      ((m⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) : Matrix (Fin n) (Fin n) (ZMod 13))
      ((m : Matrix (Fin n) (Fin n) (ZMod 13)) * ((g : Matrix (Fin n) (Fin n) (ZMod 13)) - 1))
      (Matrix.isUnits_det_units _),
      Matrix.rank_mul_eq_right_of_isUnit_det (m : Matrix (Fin n) (Fin n) (ZMod 13))
        ((g : Matrix (Fin n) (Fin n) (ZMod 13)) - 1) (Matrix.isUnits_det_units _), h2]

theorem owEm_transfer {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {n : ℕ} (M : Subgroup (Matrix.GeneralLinearGroup (Fin n) (ZMod 13)))
    (f : ↥M ≃* ↥A)
    (hf : ∀ g : ↥M, IsReflMat (g : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) ↔
      IsRefl p (f g : U ≃ₗ[ZMod p] U))
    (hone : OneClass p A) (r₀ : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) (hr₀M : r₀ ∈ M) (hr₀ : IsReflMat r₀)
    (X : Set (Matrix.GeneralLinearGroup (Fin n) (ZMod 13))) (hX₀ : r₀ ∈ X)
    (hXconj : ∀ x ∈ X, ∃ m ∈ M, x = m * r₀ * m⁻¹) (hXclosed : ∀ m ∈ M, ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hwit : ∀ x ∈ X, orderOf (r₀ * x) = 3 → ∃ t ∈ X, ¬ (Commute t r₀ ∧ Commute t x) ∧
      ¬ Nat.card (Subgroup.closure ({r₀, x, t} : Set (Matrix.GeneralLinearGroup (Fin n) (ZMod 13)))) ∣ 48) :
    ∀ r ∈ A, IsRefl p r → WitL51 p A r := by
  classical
  have hone' : ∀ g ∈ M, IsReflMat g → ∃ m ∈ M, r₀ = m * g * m⁻¹ := by
    intro g hg hgR
    have h1 : IsRefl p (f ⟨g, hg⟩ : U ≃ₗ[ZMod p] U) := (hf ⟨g, hg⟩).mp hgR
    have h0 : IsRefl p (f ⟨r₀, hr₀M⟩ : U ≃ₗ[ZMod p] U) := (hf ⟨r₀, hr₀M⟩).mp hr₀
    obtain ⟨a, ha, hya⟩ := hone _ (f ⟨g, hg⟩).2 _ (f ⟨r₀, hr₀M⟩).2 h1 h0
    refine ⟨((f.symm ⟨a, ha⟩ : ↥M) : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)), (f.symm ⟨a, ha⟩).2, ?_⟩
    have hinj : (⟨r₀, hr₀M⟩ : ↥M) = f.symm ⟨a, ha⟩ * ⟨g, hg⟩ * (f.symm ⟨a, ha⟩)⁻¹ := by
      apply f.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact Subtype.ext hya
    exact congrArg Subtype.val hinj
  have key := owEm_l51_of_class_data M IsReflMat (fun g m _ hg => owEm_isReflMat_conj g m hg) X r₀ hr₀M hX₀ hXconj
    hXclosed hone' hwit
  intro r hrA hr r₂ hr₂A hr₂ hord
  set Φ : ↥M →* (U ≃ₗ[ZMod p] U) := A.subtype.comp f.toMonoidHom with hΦ
  have hΦinj : Function.Injective Φ := Subtype.val_injective.comp f.injective
  have hΦapp : ∀ g, Φ g = (f g : U ≃ₗ[ZMod p] U) := fun g => rfl
  set g₁ : ↥M := f.symm ⟨r, hrA⟩ with hg₁
  set g₂ : ↥M := f.symm ⟨r₂, hr₂A⟩ with hg₂
  have hΦ₁ : Φ g₁ = r := by rw [hΦapp, hg₁, MulEquiv.apply_symm_apply]
  have hΦ₂ : Φ g₂ = r₂ := by rw [hΦapp, hg₂, MulEquiv.apply_symm_apply]
  have hR₁ : IsReflMat (g₁ : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) := (hf g₁).mpr (by rw [← hΦapp, hΦ₁]; exact hr)
  have hR₂ : IsReflMat (g₂ : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) := (hf g₂).mpr (by rw [← hΦapp, hΦ₂]; exact hr₂)
  have hord' : orderOf ((g₁ : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) * (g₂ : Matrix.GeneralLinearGroup (Fin n) (ZMod 13))) = 3 := by
    have h1 : orderOf (g₁ * g₂) = 3 := by
      have e : Φ (g₁ * g₂) = r * r₂ := by rw [map_mul, hΦ₁, hΦ₂]
      rw [← orderOf_injective Φ hΦinj, e]
      exact hord
    rw [← Subgroup.orderOf_coe] at h1
    exact h1
  obtain ⟨m, hm, hnc, hcard⟩ := key g₁ g₁.2 g₂ g₂.2 hR₁ hR₂ hord'
  set m' : ↥M := ⟨m, hm⟩ with hm'
  have e : Φ m' * r * (Φ m')⁻¹ = Φ (m' * g₁ * m'⁻¹) := by rw [map_mul, map_mul, map_inv, hΦ₁]
  refine ⟨Φ m', (f m').2, ?_, ?_⟩
  · rw [e]
    rintro ⟨h1, h2⟩
    apply hnc
    rw [← hΦ₁] at h1
    rw [← hΦ₂] at h2
    exact ⟨((owEm_commute_map_iff Φ hΦinj _ _).mp h1).map M.subtype,
      ((owEm_commute_map_iff Φ hΦinj _ _).mp h2).map M.subtype⟩
  · rw [e]
    have hset : ({r, r₂, Φ (m' * g₁ * m'⁻¹)} : Set (U ≃ₗ[ZMod p] U)) =
        Φ '' ({g₁, g₂, m' * g₁ * m'⁻¹} : Set ↥M) := by
      simp only [Set.image_insert_eq, Set.image_singleton, hΦ₁, hΦ₂]
    have hset' : ({(g₁ : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)),
        (g₂ : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)), m * g₁ * m⁻¹} :
        Set (Matrix.GeneralLinearGroup (Fin n) (ZMod 13))) =
        M.subtype '' ({g₁, g₂, m' * g₁ * m'⁻¹} : Set ↥M) := by
      simp only [Set.image_insert_eq, Set.image_singleton]
      rfl
    rw [hset, owEm_card_closure_map Φ hΦinj]
    rw [hset', owEm_card_closure_map M.subtype Subtype.val_injective] at hcard
    exact hcard

end CFSG.StandardType.ZS

end
