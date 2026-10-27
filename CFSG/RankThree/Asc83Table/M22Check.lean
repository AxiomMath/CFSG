module

public import Certificates.Certificate8005

public section

namespace CFSG.RankThree.Asc83Table.M22

theorem m22_noBad :
    ∀ g ∈ CFSG.Blueprint.NativeSporadic.M22, g 0 = 0 → ∀ k < 9, ∀ l < 9,
      g * x = w k * g → g * y = w l * g → m22Q8.contains (k, l) = true :=
  fun g hg h0 k hk l hl hx hy =>
    List.contains_iff_mem.mpr (Certificates.certificate8005 g hg h0 k hk l hl hx hy)

end CFSG.RankThree.Asc83Table.M22
