module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentPermutesGeneric
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndQuot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_mem_normalizer_imageOTwoQuot {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) {t : G} (htM : t ∈ D.M)
    (htbar : (QuotientGroup.mk ⟨t, htM⟩ : Mbar9 D) ∈
      Subgroup.normalizer (K1Nine D L : Set (Mbar9 D))) :
    t ∈ Subgroup.normalizer (L : Set G) := by
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hnorm : (K1Nine D L).map (MulAut.conj (QuotientGroup.mk ⟨t, htM⟩ :
      Mbar9 D)).toMonoidHom = K1Nine D L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp htbar
  have hnorm' : CFSG.Quasithin.imageOTwoQuot D.M (CFSG.Quasithin.conjByElt t L) =
      CFSG.Quasithin.imageOTwoQuot D.M L := by
    rw [CFSG.Quasithin.C2Push.imageOTwoQuot_conjByElt htM hLM]
    exact hnorm
  have hMM : D.M.map (MulAut.conj t).toMonoidHom = D.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htM)
  have hLt : CFSG.Quasithin.conjByElt t L ∈ calC D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map D.M (MulAut.conj t) hMM hL
  have heq : CFSG.Quasithin.conjByElt t L = L :=
    eq_of_mem_calC_of_imageOTwoQuot_eq hLt hL hnorm'
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem imageOTwoQuot_normalizer {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    CFSG.Quasithin.imageOTwoQuot D.M (Subgroup.normalizer (L : Set G)) =
      Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)) := by
  apply le_antisymm
  · exact CFSG.Quasithin.S152Y.imageOTwoQuot_le_normalizer
      (X := Subgroup.normalizer (L : Set G)) (Y := L) le_rfl
  · intro s hs
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective (s := (CFSG.Open.pCore 2 ↥D.M)) s
    exact CFSG.Quasithin.mem_imageOTwoQuot_iff.mpr
      ⟨(t : G), t.2, mem_normalizer_of_mem_normalizer_imageOTwoQuot hL t.2 hs, rfl⟩

theorem imageOTwoQuot_inf_normalizer {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    CFSG.Quasithin.imageOTwoQuot D.M (D.T ⊓ Subgroup.normalizer (L : Set G)) =
      Tbar9 D ⊓ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)) := by
  let π : ↥D.M →* Mbar9 D := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)
  have hker : π.ker ≤ D.T.subgroupOf D.M := by
    rw [show π.ker = CFSG.Open.pCore 2 ↥D.M from QuotientGroup.ker_mk' _]
    exact Subgroup.map_le_iff_le_comap.mp (s16c7_pCoreOf_le_of_isSylowOf D.sylowM)
  have hinf : (D.T.subgroupOf D.M) ⊓ (Subgroup.normalizer (L : Set G)).subgroupOf D.M =
      (D.T ⊓ Subgroup.normalizer (L : Set G)).subgroupOf D.M := by
    change D.T.comap D.M.subtype ⊓ (Subgroup.normalizer (L : Set G)).comap D.M.subtype =
      (D.T ⊓ Subgroup.normalizer (L : Set G)).comap D.M.subtype
    rw [Subgroup.comap_inf]
  calc CFSG.Quasithin.imageOTwoQuot D.M (D.T ⊓ Subgroup.normalizer (L : Set G))
      = ((D.T.subgroupOf D.M) ⊓
          (Subgroup.normalizer (L : Set G)).subgroupOf D.M).map π := by
        rw [CFSG.Quasithin.imageOTwoQuot, hinf]
    _ = (D.T.subgroupOf D.M).map π ⊓
        ((Subgroup.normalizer (L : Set G)).subgroupOf D.M).map π :=
        (CFSG.CGT.PushingUpLit.CGT6.EndQuot.map_inf_of_ker_le π hker).symm
    _ = Tbar9 D ⊓ CFSG.Quasithin.imageOTwoQuot D.M (Subgroup.normalizer (L : Set G)) := rfl
    _ = Tbar9 D ⊓ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)) := by
        rw [imageOTwoQuot_normalizer (D := D) (L := L) hL]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
