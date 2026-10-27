module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSMCheck
public import CFSG.GH74.KGroups.M11Inputs
public import CFSG.GH74.KGroups.L33Inputs
public import CFSG.GH74.KGroups.U33Inputs
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
import CFSG.Certificates.Kernel.ONanSmall.MapSound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import Certificates.Kernel.ONanSmall.M11
import Certificates.Kernel.ONanSmall.L33
import Certificates.Kernel.ONanSmall.U33A
import Certificates.Kernel.ONanSmall.M12A

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM Certificates.Kernel.ONanSmall

theorem certificate397508 :
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM.nqCheck (fun _ => true)
        (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.M11.Q)
        (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
          (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.M11.Q)) = true ∧
      CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM.nqCheck (fun _ => true)
        (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.L33.QA)
        (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
          (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.L33.QA)) = true ∧
      CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM.nqCheck (fun _ => true)
        (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.U33.QA)
        (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
          (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.U33.QA)) = true ∧
      CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM.nqCheck
        CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SM.firstBlock
        (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D ++
          (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D).map
            (fun d => CFSG.Sporadic.Schreier.m12Sigma * d))
        (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
          (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D ++
            (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D).map
              (fun d => CFSG.Sporadic.Schreier.m12Sigma * d))) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm : ∀ L : List (CV 11), L.map ev = L.map (evHom 11) := fun _ => rfl
    rw [elemsT_eq_elemsC, hm, pickReps_map _ ev_injective, nqCheck_map _ ev_injective, nqCheck,
      coverB_pickReps M11.one_mem, Bool.true_and,
      pickReps_of_pickRun _ invC conjC (genC M11.Q) invC_eq conjC_eq (genC_mem M11.Q) _ _ M11.pick]
    have hC : M11.reps.map (centB (elemsC M11.Q)) = M11.cents := by
      exact (map_centB_eq _ _).trans M11.cent_ok
    exact all_cent_of (fun t C => nqAt (fun _ => true) t C) hC M11.k397508
  · have hm : ∀ L : List (CV 26), L.map ev = L.map (evHom 26) := fun _ => rfl
    rw [elemsT_eq_elemsC, hm, pickReps_map _ ev_injective, nqCheck_map _ ev_injective, nqCheck,
      coverB_pickReps L33.oneA_mem, Bool.true_and,
      pickReps_of_pickRun _ invC conjC (genC L33.QA) invC_eq conjC_eq (genC_mem L33.QA) _ _
        L33.pickA]
    have hC : L33.repsA.map (centB (elemsC L33.QA)) = L33.centsA := by
      exact (map_centB_eq _ _).trans L33.centA_ok
    exact all_cent_of (fun t C => nqAt (fun _ => true) t C) hC L33.k397508
  · have hm : ∀ L : List (CV 28), L.map ev = L.map (evHom 28) := fun _ => rfl
    rw [elemsT_eq_elemsC, hm, pickReps_map _ ev_injective, nqCheck_map _ ev_injective, nqCheck,
      coverB_pickReps U33A.one_mem, Bool.true_and,
      pickReps_of_pickRun _ invC conjC (genC U33.QA) invC_eq conjC_eq (genC_mem U33.QA) _ _
        U33A.pick]
    have hC : U33A.reps.map (centB (elemsC U33.QA)) = U33A.cents := by
      exact (map_centB_eq _ _).trans U33A.cent_ok
    exact all_cent_of (fun t C => nqAt (fun _ => true) t C) hC U33A.k397508
  · rw [elemsT_append_map m12D m12Sigma, pickReps_map (evHom 24) ev_injective,
      nqCheck_map (evHom 24) ev_injective, nqCheck,
      coverB_pickReps M12A.one_mem, Bool.true_and,
      pickReps_of_pickRun _ invC conjC (genA m12D M12A.sig) invC_eq conjC_eq
        (genA_mem m12D M12A.sig) _ _ M12A.pick]
    have hC : M12A.reps.map (centB M12A.LA) = M12A.cents := by
      exact (map_centB_eq _ _).trans M12A.cent_ok
    exact all_cent_of (fun t C => nqAt (fun x => firstBlock (ev x)) t C) hC M12A.k397508

end Certificates
