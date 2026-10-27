module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

private theorem mem_pCore_iff_mem_pCoreOf' {N : Subgroup G} (x : ↥N) :
    x ∈ CFSG.pCore 2 ↥N ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 N := by
  unfold CFSG.Open.pCoreOf
  exact (Subgroup.mem_map_iff_mem N.subtype_injective).symm

theorem fstar_eq_pCoreOf_of_le {H L : Subgroup G} (hLH : L ≤ H)
    (hOL : CFSG.Open.pCoreOf 2 H ≤ L)
    (hF : CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H = CFSG.Open.pCoreOf 2 H) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar L = CFSG.Open.pCoreOf 2 L := by
  have hF' : (CFSG.generalizedFitting ↥H).map H.subtype = CFSG.Open.pCoreOf 2 H := by
    rw [← hF]
    unfold CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar
    rw [CFSG.Adapters.genFittingFStar_eq_foundations]
  have hcenH : H ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 H : Set G) ≤
      CFSG.Open.pCoreOf 2 H := by
    rintro y ⟨hyH, hyc⟩
    have hc : (⟨y, hyH⟩ : ↥H) ∈
        Subgroup.centralizer (CFSG.generalizedFitting ↥H : Set ↥H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : (w : G) ∈ CFSG.Open.pCoreOf 2 H := by
        rw [← hF']
        exact Subgroup.mem_map_of_mem _ hw
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hyc) _ hw')
    have := CFSG.centralizer_generalizedFitting_le ↥H hc
    rw [← hF']
    exact ⟨_, this, rfl⟩
  have hRQ : CFSG.Open.pCoreOf 2 H ≤ CFSG.Open.pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOL
      (hLH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  have hP : CFSG.IsCharacteristicP 2 ↥L := by
    change Subgroup.centralizer (CFSG.pCore 2 ↥L : Set ↥L) ≤ CFSG.pCore 2 ↥L
    intro x hx
    have hxc : (x : G) ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      obtain ⟨q', hq'', rfl⟩ := hRQ hq
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx q' hq'')
    exact (mem_pCore_iff_mem_pCoreOf' x).mpr (hRQ (hcenH ⟨hLH x.2, hxc⟩))
  have hgf : CFSG.generalizedFitting ↥L = CFSG.pCore 2 ↥L :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥L 2).mp hP
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar CFSG.Open.pCoreOf
  rw [CFSG.Adapters.genFittingFStar_eq_foundations, hgf]

end CFSG.LocalAnalysis.WeakClosure81
