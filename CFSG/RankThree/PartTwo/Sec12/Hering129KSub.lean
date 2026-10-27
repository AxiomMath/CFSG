module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HBasic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.PartTwo.KFacts.KS21Mult
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129KSub

variable {G : Type} [Group G]

theorem isSubnormal_subgroupOf_of_le {H C M : Subgroup G} (hHC : (H.subgroupOf C).IsSubnormal)
    (hMC : M ≤ C) : (H.subgroupOf M).IsSubnormal := by
  have h1 : ((H.subgroupOf C).subgroupOf (M.subgroupOf C)).IsSubnormal := hHC.subgroupOf
  let e := Subgroup.subgroupOfEquivOfLe hMC
  have h2 := h1.map (f := e.toMonoidHom) e.surjective
  have heq : ((H.subgroupOf C).subgroupOf (M.subgroupOf C)).map e.toMonoidHom = H.subgroupOf M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨⟨⟨(x : G), hMC x.2⟩, x.2⟩, hx, rfl⟩
  rwa [heq] at h2

end Hering129KSub

variable {G : Type} [Group G] [Finite G]

theorem resCent_isSubnormal {K : Subgroup G} {b x : G} (hK : K ∈ thetaComponentsAt 3 b)
    {M : Subgroup G} (hMb : M ≤ Subgroup.centralizer ({b} : Set G))
    (hMx : M ≤ Subgroup.centralizer ({x} : Set G)) (hXM : resCent K x ≤ M) :
    ((resCent K x).subgroupOf M).IsSubnormal := by
  have hKs : (K.subgroupOf (Subgroup.centralizer ({b} : Set G))).IsSubnormal := by
    rw [thetaComponentsAt_eq_thetaComponentsIn] at hK
    exact ((mem_thetaComponentsIn_iff.mp hK).2).2.1
  have hKM : (K.subgroupOf M).IsSubnormal :=
    Hering129KSub.isSubnormal_subgroupOf_of_le hKs hMb
  have hXK : resCent K x ≤ K := (resCent_le K x).trans inf_le_left
  have hle : (resCent K x).subgroupOf M ≤ K.subgroupOf M := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hXK (Subgroup.mem_subgroupOf.mp hy))
  have hnorm : ∀ s ∈ K ⊓ Subgroup.centralizer ({x} : Set G), s ∈
      Subgroup.normalizer (resCent K x : Set G) := fun s hs =>
    CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map
      (K ⊓ Subgroup.centralizer ({x} : Set G)) (Subgroup.le_normalizer hs)
  have hN : (((resCent K x).subgroupOf M).subgroupOf (K.subgroupOf M)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
    have hgK : ((g : ↥(K.subgroupOf M)) : ↥M).1 ∈ K := g.2
    have hgx : ((g : ↥(K.subgroupOf M)) : ↥M).1 ∈ Subgroup.centralizer ({x} : Set G) :=
      hMx ((g : ↥(K.subgroupOf M)) : ↥M).2
    have := (Subgroup.mem_normalizer_iff.mp (hnorm _ ⟨hgK, hgx⟩) _).mp hn
    simpa using this
  exact Subgroup.IsSubnormal.trans hle hN.isSubnormal hKM

end CFSG.RankThree.PartTwo.Sec12
