module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.RankThree.E6.RootLatticeTools

public section

namespace CFSG.StandardType.TableBExc.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6

variable {τ : Tag} {p : ℕ}

theorem adAct_eq_dualMatrix (w : WeylGroup τ) (x : Fin τ.rank → ZMod p) :
    adAct τ p w x = (dualMatrix (ZMod p) w⁻¹).mulVec x := rfl

theorem adAct_add (w : WeylGroup τ) (x y : Fin τ.rank → ZMod p) :
    adAct τ p w (x + y) = adAct τ p w x + adAct τ p w y :=
  Matrix.mulVec_add (dualMatrix (ZMod p) w⁻¹) x y

theorem adAct_smul (w : WeylGroup τ) (c : ZMod p) (x : Fin τ.rank → ZMod p) :
    adAct τ p w (c • x) = c • adAct τ p w x :=
  Matrix.mulVec_smul (dualMatrix (ZMod p) w⁻¹) c x

theorem adAct_pairing_smul (w : WeylGroup τ) (x : Fin τ.rank → ZMod p)
    (γ : Fin τ.rank → ℤ) :
    (∑ j, ((w • γ) j : ZMod p) * adAct τ p w x j) = ∑ j, (γ j : ZMod p) * x j := by
  change charVal (adAct τ p w x) (w • γ) = charVal x γ
  rw [adAct_eq_dualMatrix, charVal_dualMatrix, inv_smul_smul]

@[expose] noncomputable def adLinearEquiv (τ : Tag) (p : ℕ) (w : WeylGroup τ) :
    (Fin τ.rank → ZMod p) ≃ₗ[ZMod p] (Fin τ.rank → ZMod p) where
  toFun := adAct τ p w
  invFun := adAct τ p w⁻¹
  left_inv x := by rw [← adAct_mul, inv_mul_cancel, adAct_one]
  right_inv x := by rw [← adAct_mul, mul_inv_cancel, adAct_one]
  map_add' := adAct_add w
  map_smul' := adAct_smul w

@[expose] noncomputable def adMultiplicativeHom (τ : Tag) (p : ℕ) :
    WeylGroup τ →* MulAut (Multiplicative (Fin τ.rank → ZMod p)) where
  toFun w := (adLinearEquiv τ p w).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro x
    change Multiplicative.ofAdd (adAct τ p 1 (Multiplicative.toAdd x)) = x
    rw [adAct_one]
    rfl
  map_mul' w w' := by
    apply MulEquiv.ext
    intro x
    change Multiplicative.ofAdd (adAct τ p (w * w') (Multiplicative.toAdd x)) =
      Multiplicative.ofAdd (adAct τ p w (adAct τ p w' (Multiplicative.toAdd x)))
    rw [adAct_mul]

@[expose] noncomputable def adMulAutHom (τ : Tag) (p : ℕ) :
    WeylGroup τ →* MulAut (Fin τ.rank → Multiplicative (ZMod p)) :=
  (MulAut.congr (MulEquiv.piMultiplicative (fun _ : Fin τ.rank => ZMod p))).toMonoidHom.comp
    (adMultiplicativeHom τ p)

theorem adMulAutHom_apply (w : WeylGroup τ) (f : Fin τ.rank → Multiplicative (ZMod p))
    (i : Fin τ.rank) :
    adMulAutHom τ p w f i =
      Multiplicative.ofAdd (adAct τ p w (fun j => Multiplicative.toAdd (f j)) i) := rfl

end CFSG.StandardType.TableBExc.E6Three

end
