module

public import CFSG.RankThree.GF2n.Tim79aIdentU3
public import CFSG.RankThree.GF2n.Tim79aRootStatements

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G]

namespace MinCex

variable {M V Q P H : Subgroup G} [Finite G]

theorem Rtilde_le_centralizer (hc : MinCex M V Q P H) :
    Rtilde V H P ≤ Subgroup.centralizer (VZ V H : Set (XbarZ V H)) := by
  rintro _ ⟨r, hr, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨v, hv, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  obtain ⟨p, hp, hpr⟩ := mem_barOf_iff.mp (mem_Rbar.mp hr)
  obtain ⟨u, hu, huv⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp hv)
  simp only [Subgroup.coe_mul]
  rw [← hpr, ← huv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc.commute_of_mem_P hp hu)

theorem Rtilde_le_pCoreOf (hc : MinCex M V Q P H) (hd : Sec23Data V H) :
    Rtilde V H P ≤ pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hc.Rtilde_le_centralizer.trans (Subgroup.centralizer_le_normalizer _)) ?_ hc.isPGroup_Rtilde
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨fun hr => hc.conj_mem_Rtilde hd hg hr, fun hr => ?_⟩
  have := hc.conj_mem_Rtilde hd (Subgroup.inv_mem _ hg) hr
  simpa [mul_assoc] using this

theorem Rtilde_eq_or_of_rootIrrModel (hc : MinCex M V Q P H) (hd : Sec23Data V H)
    (hm : RootIrrModel (XbarZ V H) (VZ V H)) :
    Rtilde V H P = VZ V H ∨
      Rtilde V H P = pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) :=
  hm _ hc.VZ_le_Rtilde (hc.Rtilde_le_pCoreOf hd) fun _ hb _ hr => hc.conj_mem_Rtilde hd hb hr

end MinCex

theorem tim79aSec24IrrTildeStatement_of_model (hk : RootPairOfKindStatement) (hm : RootIrrAll) :
    Tim79aSec24IrrTildeStatement := by
  intro G _ _ M V Q P H hs hcase
  exact hs.mc.toMinCex.Rtilde_eq_or_of_rootIrrModel hs.data (hm _ _ (hk G M V Q P H hs hcase))

end CFSG.RankThree.GF2n.Tim79a
