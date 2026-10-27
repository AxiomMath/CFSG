module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM12Inputs
import Certificates.Kernel.M12Ctr.Facts

public section

namespace Certificates

open CFSG.QuasithinUnique.Vol2Native.A312L in
open Equiv PermLat in
theorem certificate7122 : ∀ w : Perm (Fin 12),
    w ∈ Subgroup.closure {g | g ∈ M12Lat.tGens ++
      [permOf 12 [[0, 4], [1, 8], [2, 5], [3, 10], [6, 7], [9, 11]]]} →
    (∀ g ∈ M12Lat.tGens ++ [permOf 12 [[0, 4], [1, 8], [2, 5], [3, 10], [6, 7], [9, 11]]],
      w * g = g * w) → w = 1 :=
  KernelM12Ctr.center_trivial

end Certificates
