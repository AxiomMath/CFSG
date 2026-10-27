module

public import CFSG.RankThree.GF2n.Smith81.Orth213Stmts

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

namespace Orth213

theorem concl_of_odd {G : Type} [Group G] {z x y : G} (h : Odd (orderOf (x * y))) :
    Orth213Concl z x y :=
  ⟨Or.inr (Or.inr h), fun h4 => absurd (h4 ▸ h) (by decide)⟩

end Orth213

theorem orth213Outside_of (hF : Orth213FrameStatement)
    (hO : Orth213OddStatement) : Orth213OutsideStatement := by
  intro G _ _ M Q Z B hc z hz hz1 x y hxM hyM hxz hyz hxQ hyQ _
  have H := hc.ctx.hyp
  obtain ⟨X, hX, hxX⟩ := exists_isZConjugate_mem hz hxz
  by_cases hA : ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ⊓ QB X ∧
      A ≤ Subgroup.centralizer ({y} : Set G)
  · obtain ⟨A, hAc, hAle, hAy⟩ := hA
    have hxA : x ∈ QB A := (IsZConjugate.le_QB_iff H hAc hX).mpr (hAle.trans inf_le_right) hxX
    have hyA : y ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mp (hAy ha)
    exact hF G M Q Z B hc z hz hz1 A hAc x y hxz hyz hxA hyA
  · push Not at hA
    exact Orth213.concl_of_odd (hO G M Q Z B hc z hz hz1 x y hxM hyM hxz hyz hxQ hyQ X hX hxX hA)

end CFSG.RankThree.GF2n.Smith81
