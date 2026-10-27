module

public import Certificates.Data.Foote82OmegaEightMax
import Certificates.Kernel.Foote82.StabK919011
import Certificates.Kernel.OmegaEight.Bridge3002
import CFSG.Certificates.Kernel.Foote82StabKSound

namespace Certificates

open CertificateChecks

open CFSG.KC.StabT919 CFSG.CGT.Foote82.OmegaEight CFSG.EvenSmallLie.OmegaEightMinus

theorem omegaS_S0 (j x : ℕ) : (omegaS[j]!)[x]! = S0 j x := by
  unfold S0
  by_cases hj : j < 18
  · rw [KernelO8.omegaS_bindM.2 j hj,
      show CFSG.KS.Raw.unpack 136 8 (KernelO8.OmM.S j) =
        CFSG.KC.Census.unpackP 136 8 (KernelO8.OmM.S j) from rfl,
      CFSG.KC.Census.SP.unpackP_get]
    by_cases hx : x < 136 <;> simp [hj, hx]
  · rw [getElem!_neg omegaS j (by rw [KernelO8.omegaS_bindM.1]; omega),
      show (default : Array ℕ) = #[] from rfl]
    simp [hj]

theorem gs0_G0 : ∀ l < 16, ∀ x, (gs0[l]!)[x]! = G0 l x := by
  intro l hl x
  have e : gs0[l]! = omegaS[stabIdx.getD l 0]! := by
    unfold gs0
    rw [getElem!_pos _ l (by simp [stabIdx]; omega), List.getElem_toArray, List.getElem_map,
      List.getD_eq_getElem _ _ (by simp [stabIdx]; omega)]
  rw [e, omegaS_S0]
  rfl

theorem stabTreeCheck_k : stabTreeCheck () = true := by
  have hdc : CFSG.KC.Census.canon1 136 16 dInit = true := canon_dInit
  have hinv := stabTreeK_inv ch919ok hdc
  unfold stabTreeCheck
  dsimp only
  rw [stabTree_eq gs0_G0 ch919ok ch919dInit hdc]
  rw [show outK G0 = (dec 8 (stabTreeK G0).P, dec 8 (stabTreeK G0).L, dec 16 (stabTreeK G0).D,
    dec 8 (stabTreeK G0).C, (stabTreeK G0).R) from rfl]
  dsimp only
  rw [stabTreeOK_eq omegaS_S0 hinv.1 hinv.2.1 hinv.2.2.1 hinv.2.2.2.1]
  exact ch919chk

end Certificates

public section

namespace Certificates

open CertificateChecks

open CFSG.CGT.Foote82.OmegaEight in
theorem certificate919011 : stabTreeCheck () = true := stabTreeCheck_k

end Certificates

end
