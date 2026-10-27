module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KF.K0SU3Form
public import CFSG.RankThree.PartOne.S12.Sec12Two
public import CFSG.RankThree.PartOne.S12.Sec13Base

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem ne_of_inverts_c {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) {hc : c ∈ E} {z t : MulAut E}
    (hz : z ⟨c, hc⟩ = ⟨c, hc⟩⁻¹) (ht : t ∈ torusImage E L) : z ≠ t := by
  intro hzt
  subst hzt
  have h1 : z ⟨c, hc⟩ = ⟨c, hc⟩ := Sec13Base.fixes_c_of_mem_torusImage h hc ht
  rw [hz] at h1
  have h2 : c⁻¹ = c := congrArg Subtype.val h1
  have h3 : c * c = 1 := by
    calc c * c = c * c⁻¹ := by rw [h2]
      _ = 1 := mul_inv_cancel c
  have hp := h.prime
  have hcp : c ^ p = 1 := Sec12Two.c_pow_eq_one h
  have hord : orderOf c = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hcp h.c_ne_one
  have h4 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h3)
  rw [hord] at h4
  have h5 := Nat.le_of_dvd (by norm_num) h4
  have h6 := h.three_lt
  omega

end CFSG.RankThree.PartOne.S13K
