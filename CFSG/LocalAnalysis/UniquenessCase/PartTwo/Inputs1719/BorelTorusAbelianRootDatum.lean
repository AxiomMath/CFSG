module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianFamilies
public import CFSG.LocalAnalysis.StandardType.GGSteinbergAutLemmas
public import CFSG.LieType.Steinberg.BorelCommutator
public import CFSG.GroupTheory.QuasisimpleOddCenterQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open CFSG.LieType.Steinberg
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)

variable {G : Type} [Group G] [Finite G] {D : UniversalRootDatum G} {n : Fin D.rank → G}
  {H : Fin D.rank → Subgroup G}

theorem isSylowTwoOf_posUnipotent
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup G))) :
    IsSylowTwoOf (posUnipotent D) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, isPGroup_iSup_pos hext hX, ?_⟩
  rw [show ((posUnipotent D).subgroupOf ⊤).index = (posUnipotent D).index from
    Subgroup.relIndex_top_right _]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1
    (CFSG.LieType.Steinberg.CentralExt.BorelIndex.coprime_index_posUnipotent hct hext hBU hX hT)

theorem k_BorelFamily_of_odd_cover_rootDatum {K : Type} [Group K] [Finite K]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (hT : Nat.Coprime 2 (Nat.card (⨆ i, H i : Subgroup G)))
    (α : G →* K) (hα : Function.Surjective α) (hodd : Odd (Nat.card α.ker))
    (S : Subgroup K) (hS : IsSylowTwoOf S ⊤) :
    IsMulCommutative (normalizerQuotient S) :=
  k_BorelFamily_of_odd_cover α hα hodd (isSylowTwoOf_posUnipotent hct hext hBU hX hT)
    (CFSG.StandardType.SteinbergAut.normalizer_posUnipotent hct hext)
    (commutator_mem_posUnipotent_of_mem_borel hct hext) S hS

theorem k_BorelFamily_of_odd_card_center (t : CFSG.Open.StatedLieTag)
    (h : ∀ (K : Type) [Group K] [Finite K] (m f : ℕ), CFSG.Open.StatedLieAdmissible t m 2 f →
      CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) t m 2 f → CFSG.Open.IsQuasisimple K →
      Odd (Nat.card (Subgroup.center K)) →
      ∀ S : Subgroup K, IsSylowTwoOf S ⊤ → IsMulCommutative (normalizerQuotient S)) :
    KBorelFamily t := by
  intro K _ _ m f hadm hL hq S hS
  have : (CFSG.Open.pCoreOf 2 (Subgroup.center K)).Normal :=
    Subgroup.normal_of_le_center (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 _)
  exact CFSG.GroupTheory.isMulCommutative_normalizerQuotient_of_forall_quotient_pCoreOf_center
    (h _ m f hadm (CFSG.Blueprint.LieModel.of_mulEquiv
        (CFSG.GroupTheory.quotientPCoreOfCenterEquiv hq).symm hL)
      (CFSG.GroupTheory.isQuasisimple_quotient_pCoreOf_center hq)
      (CFSG.GroupTheory.odd_card_center_quotient_pCoreOf_center hq)) S hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
