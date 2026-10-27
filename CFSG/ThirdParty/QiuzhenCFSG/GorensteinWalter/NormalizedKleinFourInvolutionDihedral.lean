module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourSupInvolutionSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # A normalized Klein four and outside involution generate D8 -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If the ambient Sylow `2`-subgroups have order eight and a dihedral
model, then a normalized Klein four joined with a normalizing outside
involution is itself isomorphic to `D8`. -/
public theorem normalized_kleinFour_sup_involution_is_dihedral_four
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ}
    (hScard : Nat.card (S : Subgroup G) = 8)
    (eS : S ≃* DihedralGroup (2 ^ m))
    (V : Subgroup G) (hVK : IsKleinFour V)
    {y : G} (hy : IsInvolution y) (hyV : y ∉ V)
    (hyNV : y ∈ Subgroup.normalizer (V : Set G)) :
    Nonempty ((V ⊔ Subgroup.zpowers y : Subgroup G) ≃*
      DihedralGroup 4) := by
  classical
  let P : Subgroup G := V ⊔ Subgroup.zpowers y
  obtain ⟨_Q, _hPQ, hPcardRaw, _hQcard⟩ :=
    exists_sylow_sup_zpowers_of_normalized_kleinFour
      S hScard V V le_rfl hVK hy hyV hyNV hyNV
  have hPcard : Nat.card P = 8 := by
    change Nat.card P = Nat.card V * 2 at hPcardRaw
    rw [hVK.card_four] at hPcardRaw
    norm_num at hPcardRaw ⊢
    exact hPcardRaw
  have hPp : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by
    rw [hPcard]
    norm_num)
  have hPindexEq : P.index = (S : Subgroup G).index := by
    have hPmul := Subgroup.card_mul_index P
    have hSmul := Subgroup.card_mul_index (S : Subgroup G)
    rw [hPcard] at hPmul
    rw [hScard] at hSmul
    omega
  have hPindexOdd : ¬ 2 ∣ P.index := by
    rw [hPindexEq]
    exact S.not_dvd_index
  let PS : Sylow 2 G := hPp.toSylow hPindexOdd
  have hPScoe : (PS : Subgroup G) = P :=
    IsPGroup.toSylow_coe hPp hPindexOdd
  have hScardModel : Nat.card (S : Subgroup G) = 2 * 2 ^ m := by
    simpa using (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
  have hmPow : 2 ^ m = 4 := by omega
  have hm2 : m = 2 := by
    apply (Nat.pow_right_injective (a := 2) (by norm_num : 2 ≤ 2))
    simpa using hmPow
  have eS4 : S ≃* DihedralGroup 4 := by
    rw [hm2] at eS
    exact eS
  exact ⟨(MulEquiv.subgroupCongr hPScoe).symm |>.trans
    ((Sylow.equiv PS S).trans eS4)⟩

end CFSG.GorensteinWalter
