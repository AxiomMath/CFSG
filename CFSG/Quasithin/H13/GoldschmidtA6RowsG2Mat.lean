module

public import CFSG.Quasithin.H13.GoldschmidtA6RowsG2Frame
public import CFSG.Quasithin.H13.GoldschmidtA6RowsFrame

public section

noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A6.GR

namespace G2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.H13.VolI Matrix

@[expose] def ixE : Fin 6 ≃ Ix3 := (finSumFinEquiv (m := 3) (n := 3)).symm

@[expose] def Tm : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 1, 1, 1, 0; 1, 0, 0, 0, 0, 1; 1, 0, 0, 0, 1, 1; 0, 0, 0, 1, 1, 0; 0, 0, 1, 1, 1, 0;
    1, 0, 1, 1, 0, 0]

@[expose] def Tinv : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 1, 0, 1, 1; 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 1, 0; 0, 1, 1, 1, 0, 0; 0, 1, 1, 0, 0, 0;
    0, 0, 1, 0, 1, 1]

theorem Tm_Tinv : Tm * Tinv = 1 := by decide +kernel

theorem Tinv_Tm : Tinv * Tm = 1 := by decide +kernel

@[expose] def matG2 (g : ↥subG2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Tinv * (muQ g).submatrix ixE ixE * Tm

theorem matG2_one : matG2 1 = 1 := by
  rw [matG2, muQ_one, Matrix.submatrix_one_equiv, Matrix.mul_one, Tinv_Tm]

theorem matG2_mul (g h : ↥subG2) : matG2 (g * h) = matG2 g * matG2 h := by
  unfold matG2
  rw [muQ_mul, ← Matrix.submatrix_mul_equiv (muQ g) (muQ h) ixE ixE ixE]
  calc Tinv * ((muQ g).submatrix ixE ixE * (muQ h).submatrix ixE ixE) * Tm
      = Tinv * (muQ g).submatrix ixE ixE * 1 * (muQ h).submatrix ixE ixE * Tm := by
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Tinv * (muQ g).submatrix ixE ixE * (Tm * Tinv) * (muQ h).submatrix ixE ixE * Tm := by
        rw [Tm_Tinv]
    _ = Tinv * (muQ g).submatrix ixE ixE * Tm * (Tinv * (muQ h).submatrix ixE ixE * Tm) := by
        simp only [Matrix.mul_assoc]

@[expose] def basisAdd : (Fin 6 → ZMod 2) ≃+ (Fin 6 → ZMod 2) where
  toFun y := Tinv *ᵥ y
  invFun y := Tm *ᵥ y
  left_inv y := by
    show Tm *ᵥ (Tinv *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, Tm_Tinv, Matrix.one_mulVec]
  right_inv y := by
    show Tinv *ᵥ (Tm *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, Tinv_Tm, Matrix.one_mulVec]
  map_add' x y := Matrix.mulVec_add _ _ _

@[expose] def coordMul : Multiplicative (Ix3 → ZMod 2) ≃* Multiplicative (Fin 6 → ZMod 2) :=
  ((LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) ixE).toAddEquiv.trans basisAdd).toMultiplicative

theorem toAdd_coordMul (x : Multiplicative (Ix3 → ZMod 2)) :
    Multiplicative.toAdd (coordMul x) = Tinv *ᵥ (Multiplicative.toAdd x ∘ ixE) := rfl

theorem mulVec_conj_aux {n : Type} [Fintype n] [DecidableEq n] (Ti Tm Q : Matrix n n (ZMod 2))
    (h : Tm * Ti = 1) (y : n → ZMod 2) : Ti *ᵥ (Q *ᵥ y) = (Ti * Q * Tm) *ᵥ (Ti *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (Ti * Q) Tm Ti, h,
    Matrix.mul_one]

theorem matG2_mulVec (g : ↥subG2) (x : Ix3 → ZMod 2) :
    Tinv *ᵥ ((muQ g *ᵥ x) ∘ ixE) = matG2 g *ᵥ (Tinv *ᵥ (x ∘ ixE)) := by
  have h0 : (x ∘ ixE) ∘ ixE.symm = x := by
    funext i
    simp
  have h1 : (muQ g *ᵥ x) ∘ ixE = (muQ g).submatrix ixE ixE *ᵥ (x ∘ ixE) := by
    rw [Matrix.submatrix_mulVec_equiv, h0]
  rw [h1]
  rw [matG2]
  exact mulVec_conj_aux Tinv Tm _ Tm_Tinv _

theorem exists_frame_g2
    {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)} (hB4 : B4Hyp G L)
    (hrow : G2Natural (ffJ G) ⊤ ⊥ 1 ∨ G2NaturalDerived L ⊤ ⊥ 1) :
    ∃ fr : Frame V L ↥subG2 6, ∀ γ, fr.mat γ = matG2 γ := by
  have h : G2NaturalDerived L ⊤ ⊥ 1 := hrow.elim (g2Derived_of_g2 hB4) id
  obtain ⟨e, ψ, hψ, he⟩ := g2_frame_data h
  refine ⟨⟨e.trans coordMul, ψ, hψ, matG2, fun γ w => ?_⟩, fun γ => rfl⟩
  show Multiplicative.toAdd (coordMul (e (((ψ γ : ↥L) : MulAut V) w))) =
    matG2 γ *ᵥ Multiplicative.toAdd (coordMul (e w))
  rw [toAdd_coordMul, toAdd_coordMul, he, matG2_mulVec]

end G2

end CFSG.Quasithin.H13.A6.GR
