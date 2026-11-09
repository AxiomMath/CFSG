module

public import Certificates.Data.Kernel.N6ModClassF
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#kc_repo #kc_json CFSG.KernelN7
  "Certificates/Kernel/CosPres/data/n7class.json" 8014 1299105999372797068
  (invL : List Nat) (relL : List Nat)

namespace CFSG.KernelN7

open CFSG.KernelN6 CFSG.KernelN6F

theorem inv7F : eqNL ((List.range' 0 65536).filter isInvBF)
    (invL.map (· % 65536)) = true := by
  quickRfl

theorem inv7SRec : invL.all invRecOK7 = true := by quickRfl

theorem invAll7_ok : invAll7 invL = true := by
  have h := inv7F
  rw [isInvBF_fun] at h
  unfold invAll7
  exact andT h inv7SRec

theorem rel70S0 : eqNL ((List.range' 0 32768).filter (relB7F 0))
    (((relL.map (· % 65536)).drop 0).take 96) = true := by
  quickRfl

theorem rel70S1 : eqNL ((List.range' 32768 32768).filter (relB7F 0))
    ((relL.map (· % 65536)).drop 96) = true := by
  quickRfl

theorem rel70SRec : relL.all relRecOK7 = true := by quickRfl

theorem relAll70_ok : relAll7 0 relL = true := by
  have h :
      eqNL ((List.range' 0 65536).filter (relB7F 0)) ((relL.map (· % 65536)).drop 0) = true :=
    eqNL_chunk (m := 32768) (k := 32768) (d := 0) (c := 96) rel70S0 rel70S1
  rw [List.drop_zero, relB7F_fun] at h
  unfold relAll7
  exact andT h rel70SRec

theorem rel71S0 : eqNL ((List.range' 0 32768).filter (relB7F 1))
    (((([] : List ℕ).map (· % 65536)).drop 0).take 0) = true := by
  quickRfl

theorem rel71S1 : eqNL ((List.range' 32768 32768).filter (relB7F 1))
    ((([] : List ℕ).map (· % 65536)).drop 0) = true := by
  quickRfl

theorem relAll71_ok : relAll7 1 [] = true := by
  have h :
      eqNL ((List.range' 0 65536).filter (relB7F 1)) ((([] : List ℕ).map (· % 65536)).drop 0) = true :=
    eqNL_chunk (m := 32768) (k := 32768) (d := 0) (c := 0) rel71S0 rel71S1
  rw [List.drop_zero, relB7F_fun] at h
  unfold relAll7
  exact andT h rfl


end CFSG.KernelN7
