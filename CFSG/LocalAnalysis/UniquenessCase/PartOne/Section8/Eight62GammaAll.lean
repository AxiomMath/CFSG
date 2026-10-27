module

public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
public import CFSG.HardMathSupport.AschbacherGilmanLyons.PartOne.SigmaSylowSubgroups.IsElemAbelianOfLe
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Proving (GLBCore_mono)

theorem gamma_le_of_isPGroup_le_of_isSylowOf
    {G : Type} [Group G] [Finite G] {L Q E M : Subgroup G}
    (hLM : L ≤ M) (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ M)
    (hE : E ≤ L) (hEp : IsPGroup 3 E) :
    CFSG.Open.rankThreeGamma 1 3 E ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hEp' : IsPGroup 3 (E.subgroupOf L) :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hE).symm
  obtain ⟨S, hES⟩ := hEp'.exists_le_sylow
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 (S.map L.subtype) L := ⟨S, rfl⟩
  obtain ⟨k, hkL, hconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hQ hS
  have hES' : E ≤ S.map L.subtype := by
    intro x hx
    exact ⟨⟨x, hE hx⟩, hES (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hEconj : E.map (MulAut.conj k⁻¹).toMonoidHom ≤ Q := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using (hconj y).mp (hES' hy)
  have hΓ' : CFSG.Open.rankThreeGamma 1 3 (E.map (MulAut.conj k⁻¹).toMonoidHom) ≤ M :=
    le_trans (by
      simpa [CFSG.Open.rankThreeGamma] using
        GLBCore_mono (p := 3) (k := 1) hEconj) hΓ
  have h := CFSG.HardMathSupport.AschbacherGilmanLyons.PartOne.SigmaSylowSubgroups.gamma_conj
    (p := 3) (k := 1) (by norm_num) (M := M)
    (E := E.map (MulAut.conj k⁻¹).toMonoidHom) (g := k⁻¹) (inv_mem (hLM hkL)) hΓ'
  have hEE : (E.map (MulAut.conj k⁻¹).toMonoidHom).map
      (MulAut.conj (k⁻¹)⁻¹).toMonoidHom = E := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id E using 2
    ext x
    simp [MulAut.conj_apply]
    group
  rw [hEE] at h
  exact h

theorem gamma_le_of_isElemAbelian_le_of_isSylowOf
    {G : Type} [Group G] [Finite G] {L Q E M : Subgroup G}
    (hLM : L ≤ M) (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ M)
    (hE : E ≤ L) (hEel : CFSG.Open.IsElemAbelian 3 E) :
    CFSG.Open.rankThreeGamma 1 3 E ≤ M :=
  gamma_le_of_isPGroup_le_of_isSylowOf hLM hQ hΓ hE hEel.isPGroup


theorem uniqueMax_of_isElemAbelian_card_nine_le_of_isSylowOf
    {G : Type} [Group G] [Finite G]
    {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G}
    (h63 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_3 D)
    {L Q E : Subgroup G} (hLM : L ≤ D.M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ D.M)
    (hE : E ≤ L) (hEel : CFSG.Open.IsElemAbelian 3 E) (hEcard : Nat.card E = 9) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.UniqueMax D.M E :=
  h63 3 (by norm_num) (by norm_num) E (hE.trans hLM) hEel (by rw [hEcard]; norm_num)
    (gamma_le_of_isElemAbelian_le_of_isSylowOf hLM hQ hΓ hE hEel)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
