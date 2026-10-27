module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmIso
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] {S : Subgroup G}

@[expose] def conjAdd (e : ↥S ≃* Multiplicative F6) (σ : MulAut ↥S) : F6 ≃+ F6 where
  toFun v := Multiplicative.toAdd (e (σ (e.symm (Multiplicative.ofAdd v))))
  invFun v := Multiplicative.toAdd (e (σ.symm (e.symm (Multiplicative.ofAdd v))))
  left_inv v := by simp
  right_inv v := by simp
  map_add' v w := by
    simp only [ofAdd_add, map_mul, toAdd_mul]

theorem conjAdd_apply (e : ↥S ≃* Multiplicative F6) (σ : MulAut ↥S) (v : F6) :
    conjAdd e σ v = Multiplicative.toAdd (e (σ (e.symm (Multiplicative.ofAdd v)))) := rfl

@[expose] def linOfAdd (f : F6 ≃+ F6) : F6 ≃ₗ[ZMod 2] F6 where
  toFun := f
  map_add' := f.map_add
  map_smul' c v := by
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc c with rfl | rfl
    · simp
    · simp
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv

theorem linOfAdd_apply (f : F6 ≃+ F6) (v : F6) : linOfAdd f v = f v := rfl

@[expose] def actLin (e : ↥S ≃* Multiplicative F6) : MulAut ↥S →* (F6 ≃ₗ[ZMod 2] F6) :=
  MonoidHom.mk' (fun σ => linOfAdd (conjAdd e σ)) (by
    intro σ τ
    ext v i
    simp [linOfAdd_apply, conjAdd_apply])

theorem actLin_apply (e : ↥S ≃* Multiplicative F6) (σ : MulAut ↥S) (v : F6) :
    actLin e σ v = Multiplicative.toAdd (e (σ (e.symm (Multiplicative.ofAdd v)))) := rfl

@[expose] noncomputable def psi0 (e : ↥S ≃* Multiplicative F6) :
    ↥(Nor S) →* (F6 ≃ₗ[ZMod 2] F6) :=
  (actLin e).comp S.normalizerMonoidHom

theorem psi0_apply (e : ↥S ≃* Multiplicative F6) (n : ↥(Nor S)) (x : ↥S) :
    psi0 e n (Multiplicative.toAdd (e x)) =
      Multiplicative.toAdd (e ⟨(n : G) * (x : G) * (n : G)⁻¹, (n.2 (x : G)).mp x.2⟩) := by
  simp only [psi0, MonoidHom.comp_apply, actLin_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  rfl

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
