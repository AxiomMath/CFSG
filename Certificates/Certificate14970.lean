module

public import CFSG.RankThree.Native.LyFiveSpec
import CFSG.RankThree.PartOne.KS.LyFiveL1V

public section

namespace Certificates

open CFSG.Sporadic.Ly CFSG.RankThree.Native in
theorem certificate14970 :     ∀ w : J, orderOf w = 5 → ∃ g : J, ∃ r ∈ ({lyFiveXJ, lyFiveVJ 0 * lyFiveVJ 1} : Set J),
      ∃ e : ℕ, 1 ≤ e ∧ e ≤ 4 ∧ g * w * g⁻¹ = r ^ e := CFSG.RankThree.PartOne.LyFive.l1_final

end Certificates
