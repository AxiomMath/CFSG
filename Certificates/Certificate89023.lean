module

public import Certificates.Data.CFSGNative.AS91.M24Kzero
import CFSG.Certificates.Kernel.M24G.ReplayFacts
import CFSG.Certificates.Kernel.M24G.DuadSound
import CFSG.Certificates.Kernel.M24G.KzeroSound
import CFSG.Certificates.Kernel.M24G.KzeroDerivSound
import Certificates.Kernel.M24G.KzeroChecks
import Certificates.Kernel.M24G.KzeroDerivChecks

public section

namespace Certificates

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G
open scoped CFSG.KC.M24G.FixOctEq

open CFSG.Quasithin.H13.AS91.M24G in
theorem certificate89023 :
    Native.treeValid Native.kzeroValid (Native.s0Tabs.map Native.kzeroMul) Native.kzeroId
      (Native.kzeroSyl ()) = true ∧
    (Native.kzeroSyl ()).1.size = 1024 ∧
    ((Native.kzeroSyl ()).1.toList.map Native.kzeroKey).Nodup ∧
    Native.kzeroUFix () = true ∧
    (Native.kzeroK0List ()).length = 64 ∧
    ∀ k ∈ Native.kzeroK0List (), k = Native.kzeroId ∨ ∃ D : Array Native.KzEntry,
      Native.kzeroDerivValid (Native.kzeroHs ()) k D = true ∧
        ∀ x ∈ Native.kzeroK0List (), ∃ j < D.size, D[j]!.tab = x := by
  have hr := KzeroC.kzeroSyl_ok
  have hK := kzeroK0List_eq hr KzeroC.kzeroK0_ok
  have hsyl := kzeroSyl_eq hr
  have hlen : KzeroD.zL.length = 1024 := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsyl, kzeroSteps_eq, treeValid_inst _ FixOctEq.decEqArr]
    exact treeValid_of_replay hr Native.kzeroValid fun y hy => by
      unfold Native.kzeroValid
      rw [beq_iff_eq]
      exact (kz_LV hr y hy).1
  · rw [hsyl, List.size_toArray]
    exact hlen
  · rw [hsyl]
    simp only [List.toList_toArray]
    rw [kzeroKey_eq]
    exact nodup_map_of_posOK (replay_facts hr).1
  · rw [kzeroUFix_eq]
    exact KzeroC.kzeroUFix_ok
  · rw [hK]
    exact KzeroC.kzeroKLen_ok
  · rw [hK]
    exact kzDerivAll_sound KzeroC.kzDerivAll_ok

end Certificates
