module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocTwoLocalFin

public section

namespace CFSG.Quasithin.Fan86

open Equiv

set_option synthInstance.maxSize 2000 in
theorem isKlein4_mul : ∀ v w : Perm (Fin 4), IsKlein4 v → IsKlein4 w → IsKlein4 (v * w) := by
  decide +kernel

theorem isKlein4_inv : ∀ v : Perm (Fin 4), IsKlein4 v → IsKlein4 v⁻¹ := by
  decide +kernel

end CFSG.Quasithin.Fan86
