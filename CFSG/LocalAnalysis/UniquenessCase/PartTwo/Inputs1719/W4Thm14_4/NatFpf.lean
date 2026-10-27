module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Defs
public import CFSG.Quasithin.Vol2.KGNatSL2Borel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open

theorem le_commSub_zpowers_of_binaryNaturalSL {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {I : Subgroup W}
    (hnat : BinaryNaturalSL L I ⊥ 2 2) {z : MulAut W} (hzL : z ∈ L) (hz3 : orderOf z = 3) :
    I ≤ commSub ⊤ (Subgroup.zpowers z) := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := hnat
  have hodd : Odd (Nat.card (Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers, hz3]
    exact ⟨1, by norm_num⟩
  have hstab : ∀ g ∈ Subgroup.zpowers z, ∀ w ∈ I, g w ∈ I := fun g hg w hw =>
    hπ.2.2.2.1 ⟨g, Subgroup.zpowers_le.mpr hzL hg⟩ w hw
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz3
    exact absurd hz3 (by norm_num)
  have hbot : I ⊓ fixV (Subgroup.zpowers z) = ⊥ := by
    refine eq_bot_iff.mpr fun u hu => ?_
    refine CFSG.Quasithin.Vol2.KGNat.factSL2NatFPF_holds K 2 le_rfl hK W L I ⊥ π hπ z hzL
      (by rw [hz3]; exact ⟨1, by norm_num⟩) hz1 u hu.1 ?_
    rw [mem_fixV_zpowers_iff_apply.mp hu.2, mul_inv_cancel]
    exact Subgroup.one_mem _
  have h := (CFSG.Quasithin.coprime_decomp hodd hW hstab).1
  rw [hbot, sup_bot_eq] at h
  rw [← h]
  exact commSub_mono le_top le_rfl

theorem kA5NatFpf_holds : KA5NatFpf := by
  intro W _ _ hW L _ hsup hnat z hzL hz3
  have hodd : Odd (Nat.card (Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers, hz3]
    exact ⟨1, by norm_num⟩
  have hle : (⨆ I ∈ irrSet L, I) ≤ commSub ⊤ (Subgroup.zpowers z) :=
    iSup₂_le fun I hI => le_commSub_zpowers_of_binaryNaturalSL hW (hnat I hI) hzL hz3
  rw [hsup, top_le_iff] at hle
  have h := (CFSG.Quasithin.coprime_decomp hodd hW (W := ⊤)
    (fun g _ w _ => Subgroup.mem_top (g w))).2
  rwa [hle, top_inf_eq, top_inf_eq] at h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
