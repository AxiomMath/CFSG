module

public import CFSG.RankThree.PartOne.HNB.NativeAssembly

public section

namespace CFSG.RankThree.PartOne.HNB

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native
open CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.NativeSporadic (Carrier)


theorem nativeData_JH : NativeData JH := by
  obtain ⟨hcomm, hinf, hsup, hord, -⟩ := ctuc_hn_five_centralizer_perfect_factor
  have hmodel := model_IJ
  obtain ⟨Y, ⟨σ⟩⟩ := exists_sl2_of_psu35 hmodel
  have hIC : IJ ≤ Subgroup.centralizer {fJ} := IJ_le_CJ
  have hs : IsSimpleGroup IJ := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity IJ 3 5 1 hmodel).2
  have hna : ∃ a b : IJ, a * b ≠ b * a := by
    have : Finite JH := inferInstance
    have : Finite IJ := inferInstance
    exact exists_noncomm_of_simple_card (G := IJ) card_IJ
  have hzc : Subgroup.zpowers fJ ≤ Subgroup.centralizer (IJ : Set JH) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcomm a ha h hh).symm
  have hfn : Subgroup.zpowers fJ ≤ Subgroup.normalizer (IJ : Set JH) :=
    hzc.trans (Subgroup.centralizer_le_normalizer _)
  have hnormal : (IJ.subgroupOf (Subgroup.centralizer {fJ})).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hIC).mpr ?_
    rw [← hsup]
    exact sup_le hfn Subgroup.le_normalizer
  set Y' : Subgroup JH := Y.map IJ.subtype with hY'
  have hYle : Y' ≤ IJ := Subgroup.map_subtype_le Y
  let eY : Y ≃* Y' := Y.equivMapOfInjective IJ.subtype IJ.subtype_injective
  let σ' : Y' ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) := eY.symm.trans σ
  obtain ⟨t0, ht02, ht0c⟩ := exists_central_involution_sl2
  refine ⟨fJ, ((σ'.symm t0 : Y') : JH), IJ, Y', hord, hIC, hnormal, hinf, hs, hna, hmodel, hYle,
    ⟨σ'⟩, (σ'.symm t0).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ht02
  · intro y hy
    obtain ⟨y', rfl⟩ : ∃ y' : Y', (y' : JH) = y := ⟨⟨y, hy⟩, rfl⟩
    have : y' * σ'.symm t0 = σ'.symm t0 * y' :=
      σ'.injective (by rw [map_mul, map_mul, MulEquiv.apply_symm_apply]; exact ht0c _)
    have h3 := congrArg Subtype.val this
    rwa [Subgroup.coe_mul, Subgroup.coe_mul] at h3

end CFSG.RankThree.PartOne.HNB
