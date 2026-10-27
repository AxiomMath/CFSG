module

public import CFSG.Quasithin.Vol2.Ch3E213MP6A
public import CFSG.Quasithin.Vol2.Ch3E213MP6EA

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.Quasithin.SteinbergBS (rootLong)

theorem pkgSp4_of (h1 : PkgSp4Diag) (h3 : PkgSp4Transv) (h4 : PkgSp4C2) (h5 : PkgSp4One) :
    PkgSp4 := by
  intro G _ _ H T M V K hS h2 n hn hSp hD hB
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · obtain rfl : n = 1 := by omega
    exact h5 G H T M V K hS h2 hSp hD hB
  · obtain ⟨k, _, _, _, hk, ⟨D⟩⟩ := exists_sp4Data hS h2 hge hSp
    by_cases hdiag : ∃ μ : k, μ ≠ 0 ∧ coordIn D.θ V ≤ zLine 1 μ
    · obtain ⟨μ, hμ, hle⟩ := hdiag
      exact h1 G H T M V K hS h2 hD hB k n hge hk D μ hμ hle
    · push Not at hdiag
      by_cases hl : coordIn D.θ V ⊓ rootLong k = ⊥
      · exact h4 G H T M V K hS h2 hD hB k n hge hk D hl hdiag
      · exact h3 G H T M V K hS h2 hD hB k n hge hk D hl

end CFSG.Quasithin.Ch3E213M
