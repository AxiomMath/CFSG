module

public import Certificates.Kernel.AlphaMc.Fi24Data
public import Certificates.Kernel.McertP.Glue
public import CFSG.Certificates.Kernel.WordsSSound
public import CFSG.Certificates.Kernel.OrbKSound

public section

namespace CertificateChecks.KernelAM.Fi24

open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi24 CFSG.KS.WordsS CFSG.KS.OrbK

theorem w_wCount : decide (3 ^ 16 ≤ (wordsL 3 fi24Mod.basis.length
    (fi24Tidx.map fun i => (fi24Mod.acts.getD i default).mat)).length * 3 ^ fi24Mod.basis.length) =
    true := by
  rw [length_wordsL, List.length_map]
  decide +kernel

theorem w_wOK : fi24Mod.wOK 3 fi24Tops fi24Tidx 16 = true :=
  KernelMP.wOK_of w_wTops (nodup_codes_of_wordsS w_words) w_wCount

theorem w_wfO : fi24Mod.wfO 3 fi24Orb = true := wfO_of_orbK w_mats w_orb

end CertificateChecks.KernelAM.Fi24

end
