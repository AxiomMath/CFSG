module

public import CFSG.RankThree.PartTwo.Sec11.Item119
public import CFSG.RankThree.PartTwo.KFacts.K71Item119

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartOne.EmbeddingFixedResidual

variable {G : Type} [Group G] [Finite G]

theorem nonempty_sec11K_quotient_mulEquiv {L : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hQ : IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))))
    (hZ : Subgroup.center ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥) :
    Nonempty (sec11K L x ⧸ aschbacherSolvableCore 3 (sec11K L x) ≃*
      (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) := by
  obtain ⟨hθs, -, hθ3, hmax, -⟩ := solvable_prime_complement_core_characterization
    (H := sec11K L x) Nat.prime_three
  obtain ⟨hθLs, -, hθL3, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  have hkker : ∀ k : (kMap L x).ker,
      Subgroup.inclusion (sec11K_le L x) (k : sec11K L x) ∈ aschbacherSolvableCore 3 L :=
    fun k => by
      have h1 : kMap L x (k : sec11K L x) = 1 := MonoidHom.mem_ker.mp k.2
      change QuotientGroup.mk' (aschbacherSolvableCore 3 L)
        (Subgroup.inclusion (sec11K_le L x) (k : sec11K L x)) = 1 at h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
  set f : (kMap L x).ker →* aschbacherSolvableCore 3 L :=
    ((Subgroup.inclusion (sec11K_le L x)).comp (kMap L x).ker.subtype).codRestrict _ hkker with hf
  have hfinj : Function.Injective f := fun y z hyz => Subtype.ext (Subtype.ext (by
    have := congrArg (fun w : aschbacherSolvableCore 3 L => ((w : L) : G)) hyz
    exact this))
  have hker : (kMap L x).ker = aschbacherSolvableCore 3 (sec11K L x) := by
    apply le_antisymm
    · refine hmax _ inferInstance (Group.isSolvable_of_isSolvable_injective hfinj) ?_
      intro h3
      apply hθL3
      rw [Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv] at h3
      exact h3.trans (Subgroup.card_subgroup_dvd_card _)
    · exact le_ker_kMap_of_normal_solvable hxN hx3 hQ hZ _ hθs
  have hrange : (kMap L x).range =
      (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L)) := by
    rw [range_kMap_eq hxN hx3 hQ.1, range_cMap hxN hx3]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange (kMap L x)).trans (MulEquiv.subgroupCongr hrange))⟩

theorem kType119 : KType119 := by
  intro G _ _ A c L a R Y h d hdL hA
  have haN := h.toHyp81.a_mem_normalizer
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  set τ := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩) with hτ
  have hτ3 : τ ^ 3 = 1 := by
    have h1 : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using ha3)
    rw [hτ, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hout : ¬ KFacts.IsInnerAut τ := h.toHyp81.not_isInnerAut_induced
  obtain ⟨hZ, hQ, -⟩ := fixedPoints_facts_of_isList1016 h.isList1016 hτ3 hout
  obtain ⟨eK⟩ := nonempty_sec11K_quotient_mulEquiv haN ha3 hQ hZ
  refine isType424_of_mulEquiv eK ?_
  rcases h.isList1016 with ⟨p, e, hp, h3, he, ⟨eL⟩⟩ | ⟨n, hn, ⟨eL⟩⟩ | ⟨n, hn, hL⟩
  · obtain ⟨eC⟩ := KFacts.nonempty_eqLocus_mulEquiv_projSL_two he eL hτ3 hout
    exact Or.inr (Or.inl ⟨p, e, hp, h3, he, ⟨eC⟩⟩)
  · obtain ⟨eC⟩ := KFacts.nonempty_eqLocus_mulEquiv_projSL_two (by omega) eL hτ3 hout
    exact Or.inl ⟨n, by omega, ⟨eC⟩⟩
  · exact Or.inr (Or.inr ⟨n, hn, KFacts.isoLThreeMinusPi_eqLocus hn hL hτ3 hout⟩)

end CFSG.RankThree.PartTwo.Sec11
