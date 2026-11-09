
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfA8Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks2
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
public import Certificates.Kernel.Census.CatFacts.OrbPre
public import Certificates.Kernel.Census.CatFacts.C2008Y
import Certificates.Kernel.Census.CatFacts.C2008K2

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.Certificates.Kernel.PkEnum CFSG.GH74.KGroups

theorem cfQH_ok' : CFSG.Certificates.ValidSchreier cfQH :=
  check_certificate_of _ _ _ _ _ cfQH2008K.1

@[expose] def cosF (x : Equiv.Perm (Fin 8)) : Bool :=
  !(q0gens.all fun q => siftP QQ8 (x * q * x⁻¹) 0) || siftP QQ8 x 0 || siftP QQ8 (g08⁻¹ * x) 0

@[expose] def normF (x : Equiv.Perm (Fin 8)) : Bool :=
  !(cfHgens.all fun h => siftP cfQH (x * h * x⁻¹) 0) || siftP cfQR x 0

theorem cosF_all : (elemsV WQ).all cosF = true := by decide +kernel

theorem normF_all : (elemsV WH).all normF = true := by decide +kernel

theorem cfCoset2008K : (elemsV QS8).all (fun x => !(q0gens.all fun q =>
    siftP QQ8 (x * q * x⁻¹) 0) || siftP QQ8 x 0 || siftP QQ8 (g08⁻¹ * x) 0) = true := by
  refine List.all_eq_true.2 fun x _ => ?_
  change cosF x = true
  cases hp : preT labQ0 q0gens x
  · unfold cosF
    rw [all_siftP_false QQ8_ok labOK_QQ8 hp]
    rfl
  · have hx := (mem_elemsT WQ WQ_ok x).2 (memWQ hp)
    rw [elemsT_eq_elemsV] at hx
    exact List.all_eq_true.1 cosF_all x hx

theorem cfNorm2008K : (elemsV QS8).all (fun x => !(cfHgens.all fun h =>
    siftP cfQH (x * h * x⁻¹) 0) || siftP cfQR x 0) = true := by
  refine List.all_eq_true.2 fun x _ => ?_
  change normF x = true
  cases hp : preT labH cfHgens x
  · unfold normF
    rw [all_siftP_false cfQH_ok' labOK_cfQH hp]
    rfl
  · have hx := (mem_elemsT WH WH_ok x).2 (memWH hp)
    rw [elemsT_eq_elemsV] at hx
    exact List.all_eq_true.1 normF_all x hx

end CertificateChecks.KernelCatFacts
