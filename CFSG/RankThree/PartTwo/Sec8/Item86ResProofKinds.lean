module

public import CFSG.RankThree.PartTwo.KFacts.K71Lift
public import CFSG.RankThree.PartTwo.Sec8.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem inducedAutHom_eq_of_thetaQuotMulAut_eq {M : Type*} [Group M]
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) {x y : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hxy : thetaQuotMulAut L (compAction L ⟨y, hy⟩) = thetaQuotMulAut L (compAction L ⟨x, hx⟩)) :
    inducedAutHom L e ⟨y, hy⟩ = inducedAutHom L e ⟨x, hx⟩ := by
  rw [inducedAutHom_apply, inducedAutHom_apply, hxy]

theorem thetaQuotMulAut_mul_zpow_eq {x c : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hcL : ∀ y ∈ L, c * y = y * c) (k : ℤ)
    (hxc : x * c ^ k ∈ Subgroup.normalizer (L : Set G)) :
    thetaQuotMulAut L (compAction L ⟨x * c ^ k, hxc⟩) =
      thetaQuotMulAut L (compAction L ⟨x, hx⟩) := by
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcL y hy).symm)
  have h1 : (⟨x * c ^ k, hxc⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨x, hx⟩ * ⟨c, hcN⟩ ^ k := Subtype.ext (by simp)
  rw [h1, map_mul, map_mul, map_zpow, map_zpow, thetaQuotMulAut_compAction_eq_one hcN hcL,
    one_zpow, mul_one]


theorem inducesStdKind_of_thetaQuotMulAut_eq {x y : G} {k : AutKind} (h : InducesStdKind L x k)
    (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hxy : ∀ hx : x ∈ Subgroup.normalizer (L : Set G),
      thetaQuotMulAut L (compAction L ⟨y, hy⟩) = thetaQuotMulAut L (compAction L ⟨x, hx⟩)) :
    InducesStdKind L y k := by
  cases h with
  | psl2 K h =>
    obtain ⟨e, hx, hk⟩ := h
    exact .psl2 K ⟨e, hy, by rwa [inducedAutHom_eq_of_thetaQuotMulAut_eq e hx hy (hxy hx)]⟩
  | psl n K hn h =>
    obtain ⟨e, hx, hk⟩ := h
    exact .psl n K hn ⟨e, hy, by rwa [inducedAutHom_eq_of_thetaQuotMulAut_eq e hx hy (hxy hx)]⟩
  | sl n K hn h =>
    obtain ⟨e, hx, hk⟩ := h
    exact .sl n K hn ⟨e, hy, by rwa [inducedAutHom_eq_of_thetaQuotMulAut_eq e hx hy (hxy hx)]⟩
  | psu3 hK hq h =>
    obtain ⟨e, hx, hk⟩ := h
    exact .psu3 hK hq ⟨e, hy, by rwa [inducedAutHom_eq_of_thetaQuotMulAut_eq e hx hy (hxy hx)]⟩
  | su3 hK hq h =>
    obtain ⟨e, hx, hk⟩ := h
    exact .su3 hK hq ⟨e, hy, by rwa [inducedAutHom_eq_of_thetaQuotMulAut_eq e hx hy (hxy hx)]⟩
  | psp r K hr h =>
    obtain ⟨e, hx, hk⟩ := h
    exact .psp r K hr ⟨e, hy, by rwa [inducedAutHom_eq_of_thetaQuotMulAut_eq e hx hy (hxy hx)]⟩
  | psp4even F h =>
    obtain ⟨e, hx, hk⟩ := h
    exact .psp4even F ⟨e, hy, by rwa [inducedAutHom_eq_of_thetaQuotMulAut_eq e hx hy (hxy hx)]⟩
  | g2 K hK3 hK4 h =>
    obtain ⟨e, hx, hk⟩ := h
    exact .g2 K hK3 hK4 ⟨e, hy, by rwa [inducedAutHom_eq_of_thetaQuotMulAut_eq e hx hy (hxy hx)]⟩
  | sz a K ha hK h =>
    obtain ⟨e, hx, hk⟩ := h
    exact .sz a K ha hK ⟨e, hy, by rwa [inducedAutHom_eq_of_thetaQuotMulAut_eq e hx hy (hxy hx)]⟩
  | triality f hf K hK σ hσ h =>
    obtain ⟨e, hx, hk⟩ := h
    exact .triality f hf K hK σ hσ
      ⟨e, hy, by rwa [inducedAutHom_eq_of_thetaQuotMulAut_eq e hx hy (hxy hx)]⟩
  | largeRee a ha K hK h =>
    obtain ⟨e, hx, hk⟩ := h
    exact .largeRee a ha K hK
      ⟨e, hy, by rwa [inducedAutHom_eq_of_thetaQuotMulAut_eq e hx hy (hxy hx)]⟩

theorem inducesStdKind_mul_zpow {x c : G} {k : AutKind} (h : InducesStdKind L x k)
    (hcL : ∀ y ∈ L, c * y = y * c) (j : ℤ) : InducesStdKind L (x * c ^ j) k := by
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcL y hy).symm)
  have hxc : x * c ^ j ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ h.mem_normalizer (Subgroup.zpow_mem _ hcN j)
  exact inducesStdKind_of_thetaQuotMulAut_eq h hxc fun hx =>
    thetaQuotMulAut_mul_zpow_eq hx hcL j hxc

theorem hyp81_commute_of_mem {A : Subgroup G} {c a : G} (h : Hyp81 G A c L a) :
    ∀ y ∈ L, c * y = y * c := by
  obtain ⟨L', -, rfl⟩ := h.mem_thetaComponentsAt
  rintro _ ⟨y, -, rfl⟩
  exact (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm

theorem hyp81_mul_zpow {A : Subgroup G} {c a : G} (h : Hyp81 G A c L a) (k : ℤ)
    (hk : a * c ^ k ≠ 1) : Hyp81 G A c L (a * c ^ k) where
  toPartTwoStanding := h.toPartTwoStanding
  mem_partTwoF := h.mem_partTwoF
  mem_A := h.mem_A
  ne_one := h.ne_one
  mem_thetaComponentsAt := h.mem_thetaComponentsAt
  sectionCentralizer_eq := h.sectionCentralizer_eq
  a_mem := A.mul_mem h.a_mem (A.zpow_mem h.mem_A k)
  a_ne_one := hk
  inducesStdKind := by
    rcases h.inducesStdKind with h' | h'
    · exact Or.inl (inducesStdKind_mul_zpow h' (hyp81_commute_of_mem h) k)
    · exact Or.inr (inducesStdKind_mul_zpow h' (hyp81_commute_of_mem h) k)
  exists_invariant_two := h.exists_invariant_two
  partTwoE_eq := h.partTwoE_eq

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
