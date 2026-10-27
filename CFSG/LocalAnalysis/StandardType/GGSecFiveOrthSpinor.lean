module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthRefl
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic

public section

namespace CFSG.StandardType.OrthF3

open TauCeti

private theorem ct_ob_sqclass_add_self (u : (ZMod 3)ˣ) :
    TauCeti.squareClass u + TauCeti.squareClass u = 0 := by
  rw [← TauCeti.squareClass_mul, TauCeti.squareClass_eq_zero_iff]
  exact ⟨u, rfl⟩

private theorem ct_ob_mul_neg_one {c₁ c₂ : ZMod 3} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (h12 : c₁ ≠ c₂) : c₁ * c₂ = -1 := by
  revert c₁ c₂
  decide

private theorem ct_ob_sqclass_ne {c₁ c₂ : ZMod 3} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (h12 : c₁ ≠ c₂) :
    TauCeti.squareClass (Units.mk0 c₁ h₁) ≠ TauCeti.squareClass (Units.mk0 c₂ h₂) := by
  intro h
  rw [TauCeti.squareClass_eq_iff_isSquare_mul] at h
  obtain ⟨y, hy⟩ := h
  have hval : c₁ * c₂ = (y : ZMod 3) * (y : ZMod 3) := by
    have hc := congrArg (fun z : (ZMod 3)ˣ => (z : ZMod 3)) hy
    simpa only [Units.val_mul, Units.val_mk0] using hc
  have hsq : IsSquare (-1 : ZMod 3) :=
    ⟨(y : ZMod 3), by rw [← hval, ct_ob_mul_neg_one h₁ h₂ h12]⟩
  exact (by decide : ¬ IsSquare (-1 : ZMod 3)) hsq

private theorem ct_ob_mem_closure_singleton {M : Type*} [Group M] {a x : M}
    (ha : a * a = 1) (hx : x ∈ Subgroup.closure ({a} : Set M)) : x = 1 ∨ x = a := by
  refine Subgroup.closure_induction (p := fun x _ => x = 1 ∨ x = a) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    exact Or.inr hy
  · exact Or.inl rfl
  · intro y z hy hz ih1 ih2
    rcases ih1 with h1 | h1 <;> rcases ih2 with h2 | h2
    · rw [h1, h2]; exact Or.inl (one_mul 1)
    · rw [h1, h2]; exact Or.inr (one_mul a)
    · rw [h1, h2]; exact Or.inr (mul_one a)
    · rw [h1, h2]; exact Or.inl ha
  · intro y hy ih
    rcases ih with h | h
    · rw [h]; exact Or.inl (inv_one)
    · rw [h]; exact Or.inr (inv_eq_of_mul_eq_one_right ha)

theorem orthRefl_not_mem_closure {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c₁ c₂ : ZMod 3} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0)
    (h12 : c₁ ≠ c₂) {g : V ≃ₗ[ZMod 3] V} (hg : OrthReflOfNorm Q c₂ g) :
    g ∉ Subgroup.closure {h : V ≃ₗ[ZMod 3] V | OrthReflOfNorm Q c₁ h} := by
  classical
  have : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  have hQ' : Q.Nondegenerate := (QuadraticMap.nondegenerate_polar_iff).mp hQ
  let χ : QuadraticMap.orthogonalGroup Q →*
      (ZMod 3)ˣ × Multiplicative (TauCeti.SquareClassGroup (ZMod 3)) :=
    (QuadraticMap.orthogonalDet Q).prod (CliffordAlgebra.orthogonalSpinorNorm Q hQ')
  let p : (ZMod 3)ˣ × Multiplicative (TauCeti.SquareClassGroup (ZMod 3)) :=
    (-1, TauCeti.squareClassHom (Units.mk0 c₁ h₁))
  have hp2 : p * p = 1 := by
    ext <;> simp [p, ct_ob_sqclass_add_self]
  let K : Subgroup (QuadraticMap.orthogonalGroup Q) :=
    (Subgroup.closure ({p} : Set _)).comap χ
  have hbase : {h : V ≃ₗ[ZMod 3] V | OrthReflOfNorm Q c₁ h} ⊆
      K.map (QuadraticMap.orthogonalGroup Q).subtype := by
    intro s hs
    obtain ⟨v, hvInv, hQv, hrefl⟩ := hs
    have hsO : s ∈ QuadraticMap.orthogonalGroup Q :=
      (OrthReflOfNorm.mem_orthogonalGroup_and_ne_zero ⟨v, hvInv, hQv, hrefl⟩).1
    refine Subgroup.mem_map.mpr ⟨⟨s, hsO⟩, ?_, rfl⟩
    change χ (⟨s, hsO⟩ : QuadraticMap.orthogonalGroup Q) ∈
      Subgroup.closure ({p} : Set _)
    have hs_eq : (⟨s, hsO⟩ : QuadraticMap.orthogonalGroup Q) =
        QuadraticMap.reflectionOrthogonal Q v := by
      apply Subtype.ext
      exact hrefl.symm
    rw [hs_eq]
    have hdet : QuadraticMap.orthogonalDet Q (QuadraticMap.reflectionOrthogonal Q v) = -1 :=
      _root_.QuadraticMap.orthogonalDet_reflectionOrthogonal (Q := Q) v
    have hspin : CliffordAlgebra.orthogonalSpinorNorm Q hQ'
        (QuadraticMap.reflectionOrthogonal Q v) =
        TauCeti.squareClassHom (unitOfInvertible (Q v)) :=
      CliffordAlgebra.orthogonalSpinorNorm_reflectionOrthogonal Q hQ' v
    have hunit : unitOfInvertible (Q v) = Units.mk0 c₁ h₁ := by
      apply Units.ext
      rw [Units.val_mk0]
      exact hQv
    have hchi : χ (QuadraticMap.reflectionOrthogonal Q v) = p := by
      simp only [χ, MonoidHom.prod_apply, hdet, hspin, hunit, p]
    rw [hchi]
    exact Subgroup.subset_closure (Set.mem_singleton p)
  have hH : Subgroup.closure {h : V ≃ₗ[ZMod 3] V | OrthReflOfNorm Q c₁ h} ≤
      K.map (QuadraticMap.orthogonalGroup Q).subtype := (Subgroup.closure_le _).mpr hbase
  intro hgH
  have hgK : g ∈ K.map (QuadraticMap.orthogonalGroup Q).subtype := hH hgH
  obtain ⟨k, hkK, hk_eq⟩ := Subgroup.mem_map.mp hgK
  have hkT : χ k ∈ Subgroup.closure ({p} : Set _) := hkK
  have hgO : g ∈ QuadraticMap.orthogonalGroup Q :=
    (OrthReflOfNorm.mem_orthogonalGroup_and_ne_zero hg).1
  have hk_eq' : k = (⟨g, hgO⟩ : QuadraticMap.orthogonalGroup Q) := by
    apply Subtype.ext
    exact hk_eq
  obtain ⟨w, hwInv, hQw, hwrefl⟩ := hg
  have hg_eq : (⟨g, hgO⟩ : QuadraticMap.orthogonalGroup Q) =
      QuadraticMap.reflectionOrthogonal Q w := by
    apply Subtype.ext
    exact hwrefl.symm
  have hchi_g : χ (⟨g, hgO⟩ : QuadraticMap.orthogonalGroup Q) =
      (-1, TauCeti.squareClassHom (Units.mk0 c₂ h₂)) := by
    rw [hg_eq]
    have hdet : QuadraticMap.orthogonalDet Q (QuadraticMap.reflectionOrthogonal Q w) = -1 :=
      _root_.QuadraticMap.orthogonalDet_reflectionOrthogonal (Q := Q) w
    have hspin : CliffordAlgebra.orthogonalSpinorNorm Q hQ'
        (QuadraticMap.reflectionOrthogonal Q w) =
        TauCeti.squareClassHom (unitOfInvertible (Q w)) :=
      CliffordAlgebra.orthogonalSpinorNorm_reflectionOrthogonal Q hQ' w
    have hunit : unitOfInvertible (Q w) = Units.mk0 c₂ h₂ := by
      apply Units.ext
      rw [Units.val_mk0]
      exact hQw
    simp only [χ, MonoidHom.prod_apply, hdet, hspin, hunit]
  have hqT : (-1, TauCeti.squareClassHom (Units.mk0 c₂ h₂)) ∈
      Subgroup.closure ({p} : Set _) := by
    rw [← hchi_g, ← hk_eq']
    exact hkT
  rcases ct_ob_mem_closure_singleton hp2 hqT with hq1 | hqp
  · exfalso
    have hfst : (-1 : (ZMod 3)ˣ) = 1 := by
      have := congrArg Prod.fst hq1
      simpa using this
    exact absurd hfst (by decide)
  · exfalso
    have hsnd : TauCeti.squareClass (Units.mk0 c₂ h₂) =
        TauCeti.squareClass (Units.mk0 c₁ h₁) := by
      have hhom : TauCeti.squareClassHom (Units.mk0 c₂ h₂) =
          TauCeti.squareClassHom (Units.mk0 c₁ h₁) := by
        have := congrArg Prod.snd hqp
        change TauCeti.squareClassHom (Units.mk0 c₂ h₂) =
          TauCeti.squareClassHom (Units.mk0 c₁ h₁) at this
        exact this
      have := congrArg Multiplicative.toAdd hhom
      simpa only [TauCeti.squareClassHom_apply, toAdd_ofAdd] using this
    exact (ct_ob_sqclass_ne h₁ h₂ h12) hsnd.symm

end CFSG.StandardType.OrthF3

end
