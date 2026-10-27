module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeInnerMat
import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticEndNode
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Main


theorem ggTwE6EndNodeInnerInput_of_core (hRK : TwE6RootKill.RootKill)
    (hDat : TwE6FieldCore.SubfieldLangDatumFive) (hCore : TwE6RootAs.TwE6CorootCore) :
    GGTwE6EndNodeInnerInput := by
  intro K _ _ n p hn hK hp hpn hp3 B hB h5 hU
  obtain ⟨U, hU1, hU2, hBU⟩ := hU
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  have hp4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by norm_num)
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    omega
  have h2 : ringChar K = 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    refine FiniteField.even_card_iff_char_two.2 ?_
    rw [← Nat.card_eq_fintype_card, hK]
    exact Nat.even_iff.1 (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, two_ne_zero⟩)
  obtain ⟨σ, hσ, ε, -⟩ := TwE6Transport.exists_recipeConj hn hK
  have hA : IsElemAbelian p (B.comap ε.toMonoidHom) := hB.comap ε.injective
  have hcard : Nat.card (B.comap ε.toMonoidHom) = Nat.card B := by
    have h := TwE6Transport.card_eltMat σ ε B
    rwa [TwE6Transport.eltMat, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at h
  obtain ⟨t, htA, ht1, hcomp, hcent⟩ := TwE6EndInner.endNodeInner_core hRK hDat hCore hK hσ h2 hp
    hp5 hpn hA (hcard ▸ h5) (TwE6Transport.twNormTwo_eltMat σ ε hU1 hU2 hBU)
  have hC := TableBSymp.map_centralizer_singleton ε t
  have hL : LargeEvenLayer (Subgroup.centralizer ({ε t} : Set (TwE6Delta.RecipeR K n))) =
      (LargeEvenLayer (Subgroup.centralizer ({t} : Set (twistedE6RootGroup K σ)))).map
        ε.toMonoidHom := by
    rw [← hC, largeEvenLayer_map_of_injective _ ε.injective]
  refine ⟨ε t, htA, fun h => ht1 (ε.injective (h.trans (map_one ε).symm)), ?_,
    fun s hs hsL => ?_⟩
  · rw [hL, ← hC]
    exact isComponentOf_map_of_injective _ ε.injective hcomp
  · have hs' : ε.symm s ∈ B.comap ε.toMonoidHom := by
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hcent _ hs' fun j hj => by
      have h := hsL (ε j) (by rw [hL]; exact ⟨j, hj, rfl⟩)
      apply ε.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h)
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← map_zpow, hk, MulEquiv.apply_symm_apply]

end Main

end CFSG.StandardType

end
