module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsDiag
import CFSG.LocalAnalysis.StandardType.GGTorCPlane

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open CFSG CFSG.StandardType CFSG.StandardType.SpJoin Matrix
open CFSG.Open (StatedSp)

variable {K : Type} [Field K]

theorem coe_tau_eq_fromBlocks_planeMat
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2)
    (u : PlaneRaw.V t) :
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks
        (WitSpNs.planeMat fun j =>
          ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K)) 0 0 1 := by
  simp [tau, linTorus, planeExt, planeExtMat, TorC.coe_spPlaneTorus]

theorem coe_tau_eq_fromBlocks_spTau
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2)
    (u : PlaneRaw.V t) :
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (((SpBlocks.tau ζ t u : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :
        Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) 0 0 1 := by
  rw [coe_tau_eq_fromBlocks_planeMat]
  congr 1
  exact (TorC.coe_spPlaneTorus t ζ (fun i => Multiplicative.ofAdd (u i))).symm

theorem planeIdem_eq_fromBlocks {t : ℕ} {ε : Fin 2} (S : Finset (Fin t)) (fix : Bool) :
    (planeIdem t ε S fix : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (SpBlocks.planeIdem t S) 0 0
        (Matrix.diagonal fun _ : Fin ε.val => if fix then (1 : K) else 0) := by
  rw [planeIdem, SpBlocks.planeIdem, ← Matrix.fromBlocks_diagonal]

theorem planeIdem_eq_fromBlocks_smul {t : ℕ} {ε : Fin 2} (S : Finset (Fin t)) (fix : Bool) :
    (planeIdem t ε S fix : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (SpBlocks.planeIdem t S) 0 0
        ((if fix then 1 else 0 : K) • (1 : Matrix (Fin ε.val) (Fin ε.val) K)) := by
  rw [planeIdem_eq_fromBlocks]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem planeIdem_true_eq_fromBlocks {t : ℕ} {ε : Fin 2} (S : Finset (Fin t)) :
    (planeIdem t ε S true : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (SpBlocks.planeIdem t S) 0 0
        (1 : Matrix (Fin ε.val) (Fin ε.val) K) := by
  simpa using planeIdem_eq_fromBlocks (K := K) S true

theorem planeExt_injective (t : ℕ) (ε : Fin 2) :
    Function.Injective (planeExt (K := K) t ε) := by
  intro A B h
  apply Units.ext
  have h' := congrArg (fun x : GL (LinIdx t ε) K =>
    ((x : Matrix (LinIdx t ε) (LinIdx t ε) K))) h
  have h'' : Matrix.fromBlocks (A : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) 0 0 1 =
      Matrix.fromBlocks (B : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) 0 0 1 := h'
  exact (Matrix.fromBlocks_inj.mp h'').1

theorem tau_add (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2)
    (u v : PlaneRaw.V t) : tau ζ t ε (u + v) = tau ζ t ε u * tau ζ t ε v := by
  have h : (fun i => Multiplicative.ofAdd ((u + v) i)) =
      (fun i => Multiplicative.ofAdd (u i)) * fun i => Multiplicative.ofAdd (v i) := by
    funext i
    simp only [Pi.mul_apply, Pi.add_apply, ofAdd_add]
  rw [tau, tau, tau, h, map_mul]

end CFSG.StandardType.GGQ2Frame.LinBlocks

end
