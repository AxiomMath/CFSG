module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9CDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9C4a

public section

namespace CFSG.StandardType.FrameRoute

@[expose] noncomputable def P9coordIso {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {t d : ℕ}
    (Φ : V ≃ₗ[ZMod 2] ((Fin t → F4) × (Fin d → ZMod 2))) :
    ((Fin d → ZMod 2) × (Fin t → F4)) ≃ₗ[ZMod 2] V :=
  (Φ.trans (LinearEquiv.prodComm (ZMod 2) (Fin t → F4) (Fin d → ZMod 2))).symm

theorem P9coordIso_rot {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {t d : ℕ}
    (Φ : V ≃ₗ[ZMod 2] ((Fin t → F4) × (Fin d → ZMod 2))) (a : Fin t → F4ˣ) (v : V) :
    Φ (P9rotV (P9coordIso Φ) a v) = ((fun i => (a i : F4) * (Φ v).1 i), (Φ v).2) := by
  let F := P9coordIso Φ
  have hFsymm : F.symm v = ((Φ v).2, (Φ v).1) := by
    dsimp only [F, P9coordIso]
    rw [LinearEquiv.symm_symm, LinearEquiv.trans_apply]
    rfl
  have hF : ∀ w : (Fin d → ZMod 2) × (Fin t → F4), Φ (F w) = (w.2, w.1) := by
    intro w
    dsimp only [F, P9coordIso]
    have h := LinearEquiv.apply_symm_apply
      (Φ.trans (LinearEquiv.prodComm (ZMod 2) (Fin t → F4) (Fin d → ZMod 2))) w
    rw [LinearEquiv.trans_apply] at h
    have h2 : Φ ((Φ.trans (LinearEquiv.prodComm (ZMod 2) (Fin t → F4)
        (Fin d → ZMod 2))).symm w) =
        (LinearEquiv.prodComm (ZMod 2) (Fin t → F4) (Fin d → ZMod 2)).symm w := by
      have h3 := congrArg (LinearEquiv.prodComm (ZMod 2) (Fin t → F4)
        (Fin d → ZMod 2)).symm h
      rwa [LinearEquiv.symm_apply_apply] at h3
    rw [h2, LinearEquiv.symm_prodComm]
    rfl
  have hrot : P9rotV F a v = F (P9rot a (F.symm v)) := by
    have h := P9rotV_apply F a (F.symm v)
    rwa [LinearEquiv.apply_symm_apply] at h
  rw [hrot, hFsymm, P9rot_apply, hF]

end CFSG.StandardType.FrameRoute
