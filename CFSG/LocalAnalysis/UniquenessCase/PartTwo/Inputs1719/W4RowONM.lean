module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONInv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowIndex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique.Setup.X1

theorem w4Thm11_1RowM_ONan_holds :
    W4Thm11_1RowM .ONan := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hcard : Nat.card (NativeSporadic.Carrier .ONan) = 460815505920 := CFSG.Sporadic.ON.card_ON
  obtain ⟨t₀, ht₀, ht₀o⟩ := W4Row.exists_orderOf_eq_two_of_cq e₀ (by rw [hcard]; norm_num)
  have hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  have hfin : Finite (MulAut W) := Finite.of_injective _ DFunLike.coe_injective
  have hperf : Group.IsPerfect ↥L := hq.1
  have hker : (redHom L e₀).ker = Subgroup.center ↥L := by
    ext b
    rw [MonoidHom.mem_ker, redHom_eq_one_iff]
  have hON : Nonempty (NativeSporadic.Carrier .ONan ≃* NativeSporadic.ON) :=
    ⟨CFSG.ONSchreier.onEquivPv.trans CFSG.ONSchreier.onEquivPv.symm⟩
  have hZ7 : ¬ 7 ∣ Nat.card (Subgroup.center ↥L) := by
    have h7 := CFSG.RankThree.Native.not_seven_dvd_card_ker_ON hON (redHom L e₀)
      (redHom_surjective L e₀) hker.le
    rwa [hker] at h7
  show tableM .ONan ≤ E3.mParam Y
  rw [show tableM .ONan = 21 from rfl]
  exact W4Row.le_mParam_of_index_sq hW' ⟨t₀, hLY ht₀, ht₀o⟩ fun t ht hto =>
    W4Row.two_pow_le_index_sq_of_inv_heis hW' hLY hF hperf hO2 hY e₀ hZ7
      W4Row.on_exists_inv_heis ht hto

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
