module

public import Certificates.Data.SMod20UaStab
public import Certificates.Data.Kernel.SmithL6K
import Certificates.Kernel.SmithEK.GlueOD
import Certificates.Kernel.SmithEK.GlueOG

public section

namespace Certificates

open CertificateChecks

open CFSG.SmithE CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th.Native in
theorem certificate21262 :
    (∀ g < 34, ∀ k < 21, uaMem uaPts[0]! (stabAp tvTabs stabWords[g]! (uaPts[0]!)[k]!) = true) ∧
    (uaCls collS2 1 = 1 ∧ uaCls collS2 3 = 2 ∧ uaCls collS2 19 = 3) ∧
    ((List.range 512).countP (fun v => uaCls collS2 v == 1) = 21 ∧
      (List.range 512).countP (fun v => uaCls collS2 v == 2) = 210 ∧
      (List.range 512).countP (fun v => uaCls collS2 v == 3) = 280) ∧
    (∀ g < 46, ∀ j < 891, ∃ j' < 891, ∀ m < 21,
      uaMem uaPts[j']! (ap tvTabs[uPos[tvGens[g]!]!]! (uaPts[j]!)[m]!) = true) ∧
    CFSG.SmithL6.K.Reach 512 34 (fun v => v == uaRoot (uaCls collS2 v))
      (fun g u v => uaCls collS2 u == uaCls collS2 v &&
        collAmat (stabWords.map (stabSig tvTabs uaPts[0]!))[g]! u == v) ∧
    CFSG.SmithL6.K.Reach 891 46 (· == 0) (fun g j' j => allIn 0 21 fun m =>
      uaMem uaPts[j]! (ap tvTabs[uPos[tvGens[g]!]!]! (uaPts[j']!)[m]!)) ∧
    CFSG.SmithL6.K.Reach 891 34 (fun j => j == uaDRoot uaPts (uaMeet uaPts[0]! uaPts[j]!))
      (fun g j' j => uaMeet uaPts[0]! uaPts[j']! == uaMeet uaPts[0]! uaPts[j]! &&
        allIn 0 21 fun m => uaMem uaPts[j]! (stabAp tvTabs stabWords[g]! (uaPts[j']!)[m]!)) :=
  ⟨fun _ hg _ hk => KernelSmithEK.stab_fix hg hk, KernelSmithEK.cls_facts.1,
    KernelSmithEK.cls_facts.2, KernelSmithEK.img46_gen, KernelSmithEK.reachU,
    KernelSmithEK.reach46_gen, KernelSmithEK.reachD⟩

end Certificates
