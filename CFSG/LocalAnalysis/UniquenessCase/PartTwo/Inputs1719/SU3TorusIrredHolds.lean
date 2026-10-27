module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSL2U3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3TorusIrredInvolution
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3TorusIrredCases
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3TorusIrredTrichotomy

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

namespace SU3TorusIrred

variable {n : ℕ} {K : Type} [Field K] {T H : Subgroup (unitarySU 2 n K 3)}

theorem eq_top_of_irreducible (h : UnitaryFieldData 2 n K) (hn : 2 ≤ n) (hne : Even n)
    (hTc : IsMulCommutative T) (hT : Nat.card T = 2 ^ n - 1) (hH : Group.IsPerfect H)
    (hTH : T ≤ Subgroup.normalizer (H : Set (unitarySU 2 n K 3)))
    (hirr : ∀ W : Submodule K (Fin 3 → K), (∀ t ∈ T, ∀ w ∈ W, t • w ∈ W) →
      (∀ g ∈ H, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤) :
    H = ⊤ := by
  obtain ⟨F⟩ := nonempty_su3TorusFrame h hn hTc hT
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hT1 : T ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hT
    omega
  have hTodd : Odd (Nat.card T) := by
    rw [hT]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have h3q : 3 ∣ 2 ^ n - 1 := by
    obtain ⟨k, hk⟩ := hne
    rw [hk, ← two_mul, pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one (2 ^ 2) k
  obtain ⟨x, hxHT, hx3⟩ := exists_mem_inf_orderOf_eq_three h h3q hT hTH
    (three_dvd_card hn h3q F hT hH hTH hirr)
  obtain ⟨z, hzH, hz2, hz1, hzv, hze, hzf⟩ :=
    exists_involution_swap h3q F hH hxHT.1 hxHT.2 hx3
  have hTH' : T ≤ H := le_of_swap F hTodd hTH hzH hz2 hzv hze hzf
  have hTN : T ≤ H ⊓ MulAction.stabilizer (unitarySU 2 n K 3) F.v :=
    le_inf hTH' fun t ht => MulAction.mem_stabilizer_iff.2 (F.smul_v ⟨t, ht⟩)
  rcases le_normalizer_or_eq_or_exists_isPGroup hn F hT hTN inf_le_right with hc | hc | hc
  · exact absurd hc (not_inf_stabilizer_le_normalizer hne F hT1 hH hzH hz2 hz1 hzv hze hzf)
  · exact eq_top_of_stabilizer_le hn F (hc.symm.le.trans inf_le_left) fun W hW =>
      hirr W (fun t ht => hW t (hTH' ht)) hW
  · obtain ⟨P, -, hP1, hP2, hNP⟩ := hc
    have hzN : z ∈ H ⊓ MulAction.stabilizer (unitarySU 2 n K 3) F.v :=
      Subgroup.mem_inf.2 ⟨hzH, MulAction.mem_stabilizer_iff.2 hzv⟩
    exact absurd (eq_bot_of_isPGroup_of_le_normalizer F hT1 hze hP2 (hTN.trans hNP) (hNP hzN)) hP1

end SU3TorusIrred

theorem k_19_19_su3TorusIrred_holds : K_19_19_su3TorusIrred := by
  intro K _ _ n hK h4 hne T H hTc hT hH hTH hirr
  have h := unitaryFieldDataOfCard hK
  refine SU3TorusIrred.eq_top_of_irreducible (T := T) (H := H) h (by omega) hne hTc hT
    (Subgroup.isPerfect_iff.2 hH) hTH fun W hTW hHW => hirr W (fun t ht w hw => ?_)
      (fun g hg w hw => ?_)
  · have := hTW t ht w hw
    rwa [unitarySU_smul_def h, Matrix.mulVecLin_apply] at this
  · have := hHW g hg w hw
    rwa [unitarySU_smul_def h, Matrix.mulVecLin_apply] at this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
