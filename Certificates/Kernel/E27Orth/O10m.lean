module

public import Certificates.Data.Kernel.E27Orth.Orth
public import Certificates.Kernel.E27Orth.O10mData

public section

namespace CertificateChecks.KernelE27Orth.O10m

open CFSG.KC.Enum CFSG.KC.E27Orth CFSG.KC.Misc.G24

theorem o10m131005_om : allN 5 (fun j => omI 10 U (G j) (Y j) (Yi j)) = true := by
  decide +kernel

theorem o10m131005_base : baseI (cnF2 10) (oneF2 10) 5 G = true := by decide +kernel

theorem o10m131005_tree : allN 729 (treeI (mulF2 10) (cnF2 10) (oneF2 10) 5 G E Tr) = true := by
  decide +kernel

theorem o10m131005_key : allN 729 (keyI 729 E Ss) = true := by decide +kernel

theorem o10m131005_left : allN 3645 (leftI (mulF2 10) 729 G E Lf) = true := by decide +kernel

theorem o10m131005_conj : allN 729 (conjI (mulF2 10) 729 153 E Rp W) = true := by decide +kernel

theorem o10m131005_rep : allN 153 (repI (mulF2 10) (cnF2 10) (oneF2 10) 729 81 E Rp Cm) = true := by
  decide +kernel

end CertificateChecks.KernelE27Orth.O10m

end
