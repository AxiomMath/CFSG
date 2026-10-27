module

public import CFSG.LocalAnalysis.StandardType.PhanELocalSys

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.ChamberIso

open CFSG.Monster.B.Geometry

variable {I₁ I₂ I₃ I₄ C₁ C₂ C₃ C₄ : Type} {X₁ : ChamberSystem I₁ C₁} {X₂ : ChamberSystem I₂ C₂}
  {X₃ : ChamberSystem I₃ C₃} {X₄ : ChamberSystem I₄ C₄}

@[expose] def trans (h : ChamberIso X₁ X₂) (h' : ChamberIso X₂ X₃) : ChamberIso X₁ X₃ where
  e := h.e.trans h'.e
  Φ := h.Φ.trans h'.Φ
  adj_iff i x y := (h.adj_iff i x y).trans (h'.adj_iff (h.e i) (h.Φ x) (h.Φ y))

theorem trans_Φ_apply (h : ChamberIso X₁ X₂) (h' : ChamberIso X₂ X₃) (x : C₁) :
    (h.trans h').Φ x = h'.Φ (h.Φ x) :=
  rfl

theorem trans_e_apply (h : ChamberIso X₁ X₂) (h' : ChamberIso X₂ X₃) (i : I₁) :
    (h.trans h').e i = h'.e (h.e i) :=
  rfl

@[expose] def prodCongr (h : ChamberIso X₁ X₂) (h' : ChamberIso X₃ X₄) :
    ChamberIso (X₁.prod X₃) (X₂.prod X₄) where
  e := Equiv.sumCongr h.e h'.e
  Φ := Equiv.prodCongr h.Φ h'.Φ
  adj_iff i x y := by
    cases i with
    | inl i =>
      change X₁.adj i x.1 y.1 ∧ x.2 = y.2 ↔
        X₂.adj (h.e i) (h.Φ x.1) (h.Φ y.1) ∧ h'.Φ x.2 = h'.Φ y.2
      rw [h.adj_iff i x.1 y.1, h'.Φ.apply_eq_iff_eq]
    | inr i =>
      change x.1 = y.1 ∧ X₃.adj i x.2 y.2 ↔
        h.Φ x.1 = h.Φ y.1 ∧ X₄.adj (h'.e i) (h'.Φ x.2) (h'.Φ y.2)
      rw [h'.adj_iff i x.2 y.2, h.Φ.apply_eq_iff_eq]

theorem prodCongr_Φ_apply (h : ChamberIso X₁ X₂) (h' : ChamberIso X₃ X₄) (x : C₁ × C₃) :
    (h.prodCongr h').Φ x = (h.Φ x.1, h'.Φ x.2) :=
  rfl

@[expose] def restrictCongr (X : ChamberSystem I₁ C₁) {A A' : Set C₁} (hA : A = A') :
    ChamberIso (X.restrict A) (X.restrict A') where
  e := Equiv.refl I₁
  Φ :=
    { toFun := fun x => ⟨x.1, hA ▸ x.2⟩
      invFun := fun x => ⟨x.1, hA ▸ x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  adj_iff _ _ _ := Iff.rfl

end CFSG.ClassicalInvolution.Phan.PhanE.ChamberIso

end
