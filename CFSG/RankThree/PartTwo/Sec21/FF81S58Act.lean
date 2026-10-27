module

public import CFSG.RankThree.PartTwo.Sec21.FF81S58Faith
public import CFSG.RankThree.PartTwo.Sec21.FF81S58Sym

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S58

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

theorem cen_sq_eq_cen {x : G} (hx : x ^ 3 = 1) : Cen (x ^ 2) = Cen x := by
  ext y
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : y * (x ^ 2) ^ 2 = (x ^ 2) ^ 2 * y :=
      (Commute.pow_right (show Commute y (x ^ 2) from h) 2).eq
    have e : (x ^ 2) ^ 2 = x := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx, one_mul, pow_one]
    rwa [e] at h'
  · intro h
    exact (Commute.pow_right (show Commute y x from h) 2).eq


theorem ff81_5_9Act_holds : KF_McLaughlin6 → KF_HoltThm1 → KF_FF81aProp1 → FF81_3_2 →
    FF81_5_2_6 → FF81_5_7 → S59.FF81_5_9Act := by
  intro hMcl hHolt hP1 h32 h526p h57 G _ _ b L B b₁ b₂ b₃ t₀ s₀ h5 h526 M hM7 h58
  obtain ⟨M', h526', hM7'⟩ := rerun hMcl hHolt hP1 h32 h526p h57 h5 h526 hM7
  obtain ⟨-, -, -, ⟨S₀, S₁, hS0, hS1, hSeq, hinf, hcen⟩, hCZ, hE5, -⟩ := h526'
  have hB := h5.basis
  have hTL : Op 2 (Cen t₀) ⊓ L = ⊥ := S59.op_two_inf_eq_bot hB h5.ht₀L
  refine ⟨?_, ?_⟩
  · rw [hCZ, inf_comm]
    exact hTL
  · haveI : IsSimpleGroup ↥L :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp L 3 2 1
        hB.hyp.model
    have hTcard : Nat.card ↥(Op 2 (Cen t₀)) = 2 ^ 15 := by
      rw [← hSeq]; exact S59.card_sup hS0 hS1 hinf hcen
    have hZcard : Nat.card ↥(Op 2 (Cen t₀) ⊓ CenS (Op 2 (Cen t₀))) = 2 ^ 7 := by
      rw [← hSeq]; exact S59.card_center hS0 hS1 hinf hcen
    have hC5 : Nat.card ↥(Op 2 (Cen t₀) ⊓ Cen b₁) = 2 ^ 5 := by
      have := hE5.2
      rwa [c₂_mul_c₃ h5, cen_sq_eq_cen (b₁_cube_A₁ h5)] at this
    refine eq_one_of_comm_center (S59.le_nor_op_two h5.ht₀L) hB.hb₁ ?_
    rw [hTcard, hZcard, hC5]
    norm_num

end CFSG.RankThree.PartTwo.Sec21.FF81.S58
