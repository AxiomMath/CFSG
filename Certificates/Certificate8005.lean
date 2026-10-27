module

public import CFSG.RankThree.Asc83Table.M22Data
import Certificates.Kernel.Misc.Perm.M22.Facts
public import CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.M22 in
theorem certificate8005 : ∀ g ∈ CFSG.Blueprint.NativeSporadic.M22, g 0 = 0 → ∀ k < 9, ∀ l < 9,
    g * x = w k * g → g * y = w l * g → (k, l) ∈ m22Q8 :=
  fun g hg h0 k hk l hl hx hy =>
    List.contains_iff_mem.mp (KernelMisc.M22.facts g hg h0 k hk l hl hx hy)

end Certificates
