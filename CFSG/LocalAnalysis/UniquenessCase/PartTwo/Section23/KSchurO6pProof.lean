module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineC2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint.Multiplier CFSG.RankThree.PerfectCover

theorem kSchurO6p_holds : KSchurO6p := by
  intro X _ _ Z _ hperf hZc _ hshape
  obtain ⟨n, hn, hOmega⟩ := hshape
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨eZ⟩⟩ := hOmega
  letI := hKfield
  letI := hKfinite
  have heven : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hg : genericOrders .POmegaPlus 3 2 n = (1, 1) := by
    unfold genericOrders
    simp [heven]
  haveI : Subsingleton (generic .POmegaPlus 3 2 n) := by
    unfold generic
    rw [hg]
    infer_instance
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.pomegaPlus_hopfMultiplier
      (n := 3) (p := 2) (f := n) (K := K) (by norm_num) hKcard hK4
  haveI : Subsingleton (griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadPlus 3 K)))) := eM.toEquiv.subsingleton
  haveI : Subsingleton (griessHopfMultiplier (X ⧸ Z)) :=
    (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eZ).injective.subsingleton
  haveI : Subsingleton (hopfMultiplier (X ⧸ Z)) :=
    (hopfMultiplierEquivGriess (X ⧸ Z)).symm.injective.subsingleton
  haveI : Group.IsPerfect X := ⟨hperf⟩
  let q : X →* X ⧸ Z := QuotientGroup.mk' Z
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective Z
  have hkerq : q.ker = Z := QuotientGroup.ker_mk' Z
  have hkerle : q.ker ≤ Subgroup.center X := by
    rw [hkerq]
    exact hZc
  have hψ : Function.Surjective (hopfMultiplierToKer q hq hkerle) :=
    hopfMultiplierToKer_surjective q hq hkerle
  haveI : Subsingleton ↥q.ker := hψ.subsingleton
  rw [← hkerq]
  exact Subgroup.eq_bot_of_subsingleton q.ker

end CFSG.LocalAnalysis.UniquenessCase.UC22
