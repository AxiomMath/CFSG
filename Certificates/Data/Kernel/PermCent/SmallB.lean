module

public import Certificates.Data.Kernel.PermCent.CV

public section

namespace CFSG.Certificates.Kernel.PkCV

instance smallB10 : Small 10 := ⟨by decide⟩
instance smallB11 : Small 11 := ⟨by decide⟩
instance smallB22 : Small 22 := ⟨by decide⟩
instance smallB23 : Small 23 := ⟨by decide⟩
instance smallB36 : Small 36 := ⟨by decide⟩

variable {n : Nat} [Small n]

@[expose] noncomputable def evCodesB (S : List (CV n)) : List ℤ → CV n
  | [] => 1
  | z :: w => (if 0 < z then S.getD (z.toNat - 1) 1 else (S.getD ((-z).toNat - 1) 1)⁻¹) *
      evCodesB S w

end CFSG.Certificates.Kernel.PkCV

end
