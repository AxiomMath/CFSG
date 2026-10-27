module

public import CFSG.RankThree.PartTwo.Sec19.KF1923OutDispatch
import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalOuter
import CFSG.Milestones.ASVolI.F411.Complete

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

section G2Out


theorem isCyclic_outer_adjointGroup_g2_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    IsCyclic (Outer (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) := by
  have hc : Subgroup.center (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field .G2 K
  let eF : CFSG.ASVolI.ChF.G2Native.FullModel K ≃* CFSG.Blueprint.Chevalley.adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hone : ∀ x : Outer (CFSG.ASVolI.ChF.G2Native.FullModel K), x = 1 := by
    intro x
    obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.eq_one_iff]
    obtain ⟨g, hg⟩ := CFSG.ASVolI.burnsideF411_g2Two_inner hK β
    exact MonoidHom.mem_range.mpr ⟨g, hg.symm⟩
  haveI : Subsingleton (Outer (CFSG.ASVolI.ChF.G2Native.FullModel K)) :=
    ⟨fun x y => by rw [hone x, hone y]⟩
  haveI : Subsingleton (Outer (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) := by
    constructor
    intro x y
    apply (equivalence eF.symm).injective
    exact Subsingleton.elim _ _
  infer_instance

theorem isCyclic_outer_adjointGroup_g2_pow (K : Type) [Field K] [Finite K] (m : ℕ)
    (hm : Nat.card K = 2 ^ m) :
    IsCyclic (Outer (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) := by
  rcases Nat.lt_or_ge m 2 with h | h
  · rcases Nat.lt_or_ge m 1 with h0 | h1
    · obtain rfl : m = 0 := by omega
      exfalso
      have h1K : 1 < Nat.card K := Finite.one_lt_card
      simp [hm] at h1K
    · obtain rfl : m = 1 := by omega
      exact isCyclic_outer_adjointGroup_g2_two (by rw [hm, pow_one])
  · have h3 : 3 ≤ 2 ^ m := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
    exact GL83.I713.isCyclic_outer_adjointGroup_G2_of_card Nat.prime_two (by omega) h3 hm

theorem kf1_holds : KF1 :=
  kf1_of_G2 (fun K _ _ m hm => isCyclic_outer_adjointGroup_g2_pow K m hm)

end G2Out

end CFSG.RankThree.PartTwo.Late
