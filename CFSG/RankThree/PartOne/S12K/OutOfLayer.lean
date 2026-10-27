module

public import CFSG.RankThree.PartOne.S12.Sec12Fus
public import CFSG.RankThree.PartOne.S11d.OutAbstract
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutUnitary

public section

namespace CFSG.RankThree.PartOne.S12K

open CFSG CFSG.Assembly
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne.OutStructure

variable {G : Type} [Group G]

theorem not_dvd_gcd_three {p : ℕ} (hp5 : 5 ≤ p) (m : ℕ) : ¬ p ∣ Nat.gcd 3 (2 ^ m + 1) := fun hd => by
  have h3 : p ∣ 3 := hd.trans (Nat.gcd_dvd_left _ _)
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem outPNice_of_layerModel {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {L I : Subgroup G}
    (hI : LayerModel p L I p) (hr : ∃ r : ℕ, 1 ≤ r ∧ r ≤ 12 ∧ RowModel p L r) :
    OutPNice p (↥I ⧸ Subgroup.center ↥I) := by
  obtain ⟨r, hr1, hr12, hrow⟩ := hr
  by_cases hr8 : r ≤ 8
  · obtain ⟨g, -, -, hg⟩ := hI.2.2 ⟨r, hr1, hr8, hrow⟩
    exact outPNice_PSL_two hp hg
  · have hr9 : 9 ≤ r := by omega
    have hU : ∀ f : ℕ, 1 ≤ f → p ∣ 2 ^ f + 1 →
        (StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 2 f ∨
          StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 5 2 f) →
        OutPNice p (↥I ⧸ Subgroup.center ↥I) := fun f hf hdvd hm =>
      outPNice_PSU hp (hI.1 f hf hdvd hm) (not_dvd_gcd_three hp5 _)
    interval_cases r
    · obtain ⟨f, hf, hdvd, hm⟩ := hrow
      exact hU f hf hdvd (Or.inl hm)
    · obtain ⟨f, hf, hdvd, hm⟩ := hrow
      exact outPNice_PSp_two hp (hI.2.1 f hf hdvd hm)
    · obtain ⟨rfl, -, f, hf, hdvd, hm⟩ := hrow
      exact hU f hf hdvd (Or.inr hm)
    · obtain ⟨rfl, -, f, hf, hdvd, -, hm⟩ := hrow
      exact hU f hf hdvd (Or.inr hm)

end CFSG.RankThree.PartOne.S12K
