module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem mem_inner_of_isPGroup_three
    {X : Type} [Group X] [Finite X] {φ : MulAut X}
    (hφ : IsPGroup 3 (Subgroup.zpowers φ))
    (hOut : ¬ 3 ∣ Nat.card (Outer X)) :
    φ ∈ inner X := by
  let ψ : Outer X := QuotientGroup.mk' (inner X) φ
  have hψP : IsPGroup 3 (Subgroup.zpowers ψ) := by
    have h := hφ.map (QuotientGroup.mk' (inner X))
    rwa [MonoidHom.map_zpowers] at h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hψ1 : ψ = 1 := by
    by_contra hψ
    have hψsub : (⟨ψ, Subgroup.mem_zpowers ψ⟩ : Subgroup.zpowers ψ) ≠ 1 := by
      simpa using hψ
    have h3dvd : 3 ∣ orderOf ψ := by
      have h := hψP.dvd_orderOf hψsub
      simpa using h
    exact hOut (h3dvd.trans (orderOf_dvd_natCard ψ))
  exact (QuotientGroup.eq_one_iff (N := inner X) φ).mp (by simpa [ψ] using hψ1)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
