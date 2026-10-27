module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoRoots

import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bAux
import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bClass
import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bCover
import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bCase2
import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bCase3b

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem LevTwoType

private theorem levTwoS2b_data_congr {ι : Type} [Fintype ι] [DecidableEq ι]
    {R R' : Matrix ι ι ℤ} (hR : TauCeti.IsFiniteType R) (hR' : TauCeti.IsFiniteType R')
    (he : R = R') (p : ℕ) (c : ι → ZMod p) (Φ : Set (ι → ℤ)) :
    LevTwoData hR p c Φ ↔ LevTwoData hR' p c Φ := by
  subst he
  rw [Subsingleton.elim hR hR']

private theorem levTwoS2b_tcRoot_congr {ι : Type} [Fintype ι] [DecidableEq ι]
    {R R' : Matrix ι ι ℤ} (hR : TauCeti.IsFiniteType R) (hR' : TauCeti.IsFiniteType R')
    (he : R = R') (Φ : Set (ι → ℤ)) : TCRoot hR Φ ↔ TCRoot hR' Φ := by
  subst he
  rw [Subsingleton.elim hR hR']

private theorem levTwoS2b_engine (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (CFSG.LieType.Universal.Spin.isFiniteType_cartanB n) p c Φ) :
    TCRoot (CFSG.LieType.Universal.Spin.isFiniteType_cartanB n) Φ := by
  rcases levTwoS2b_Phi_cases n hn p hp hp2 c Φ h with
    h1 | ⟨k, h3, hk, hZ, rfl⟩ | ⟨a₀, η, hη, h0, hD, rfl⟩
  · rw [h1]
    exact levTwoS2b_tcRoot_allLong n hn
  · exact levTwoS2b_tcRoot_case2 n hn p hp hp2 c k h3 hk hZ
  · exact levTwoS2b_tcRoot_case3 n hn p hp hp2 c a₀ η hη h0 hD

theorem levTwoEngine_B (n : ℕ) (hn : 2 ≤ n) : LevTwoEngine (LevTwoType.B n) := by
  intro p hp hp2 c Φ h
  have hroot : (LevTwoType.B n).root = CFSG.LieType.Universal.Spin.cartanB n := by
    change (CartanMatrix.B n).transpose = CFSG.LieType.Universal.Spin.cartanB n
    rw [CFSG.LieType.Universal.Spin.cartanB_eq_transpose]
  refine (levTwoS2b_tcRoot_congr (R := (LevTwoType.B n).root)
    (R' := CFSG.LieType.Universal.Spin.cartanB n) (LevTwoType.rootFT (LevTwoType.B n))
    (CFSG.LieType.Universal.Spin.isFiniteType_cartanB n) hroot Φ).mpr ?_
  exact levTwoS2b_engine n hn p hp hp2 c Φ
    ((levTwoS2b_data_congr (R := (LevTwoType.B n).root)
      (R' := CFSG.LieType.Universal.Spin.cartanB n) (LevTwoType.rootFT (LevTwoType.B n))
      (CFSG.LieType.Universal.Spin.isFiniteType_cartanB n) hroot p c Φ).mp h)

end CFSG.StandardType.LevTwo
