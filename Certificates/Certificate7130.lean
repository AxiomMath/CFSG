
module

public import Certificates.Kernel.Ru7130.Glue

public section

namespace Certificates

open CFSG.QuasithinUnique.Ch1.SporLat.Ru Matrix in
theorem certificate7130 :     (∃ ψ : ↥(ruCtx.Y 2) →* SpecialLinearGroup (Fin 3) (ZMod 2), Function.Surjective ψ) ∧
      ∀ (N : Subgroup ↥(ruCtx.Y 2)) [N.Normal], IsPGroup 2 (↥(ruCtx.Y 2) ⧸ N) →
        Nat.card (↥(ruCtx.Y 2) ⧸ N) ≤ 1 :=
  CFSG.KD.Ru7130.ru7130

end Certificates
