module

public import Certificates.Data.Kernel.N6ModClassF
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#kc_repo #kc_json CFSG.KernelN6
  "Certificates/Kernel/Census/N6/data/n6class.json" 8014 10096548783626613819
  (invL : List Nat) (relL : List Nat)

namespace CFSG.KernelN6

open CFSG.KernelN6F

theorem invF : eqNL ((List.range' 0 65536).filter isInvBF)
    (invL.map (· % 65536)) = true := by
  quickRfl

theorem invSRec : invL.all invRecOK = true := by quickRfl

theorem invAll_ok : invAll invL = true := by
  have h := invF
  rw [isInvBF_fun] at h
  unfold invAll
  exact andT h invSRec

theorem rel0S0 : eqNL ((List.range' 0 32768).filter (relBF 0))
    (((relL.map (· % 65536)).drop 0).take 96) = true := by
  quickRfl

theorem rel0S1 : eqNL ((List.range' 32768 32768).filter (relBF 0))
    ((relL.map (· % 65536)).drop 96) = true := by
  quickRfl

theorem rel0SRec : relL.all relRecOK = true := by quickRfl

theorem relAll0_ok : relAll 0 relL = true := by
  have h :
      eqNL ((List.range' 0 65536).filter (relBF 0)) ((relL.map (· % 65536)).drop 0) = true :=
    eqNL_chunk (m := 32768) (k := 32768) (d := 0) (c := 96) rel0S0 rel0S1
  rw [List.drop_zero, relBF_fun] at h
  unfold relAll
  exact andT h rel0SRec

theorem rel1S0 : eqNL ((List.range' 0 32768).filter (relBF 1))
    (((([] : List ℕ).map (· % 65536)).drop 0).take 0) = true := by
  quickRfl

theorem rel1S1 : eqNL ((List.range' 32768 32768).filter (relBF 1))
    ((([] : List ℕ).map (· % 65536)).drop 0) = true := by
  quickRfl

theorem relAll1_ok : relAll 1 [] = true := by
  have h :
      eqNL ((List.range' 0 65536).filter (relBF 1)) ((([] : List ℕ).map (· % 65536)).drop 0) = true :=
    eqNL_chunk (m := 32768) (k := 32768) (d := 0) (c := 0) rel1S0 rel1S1
  rw [List.drop_zero, relBF_fun] at h
  unfold relAll
  exact andT h rfl


end CFSG.KernelN6
