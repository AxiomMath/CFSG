module

public import CFSG.Quasithin.H13.NQCatKG68Singer
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersCentral

public section

namespace CFSG.Quasithin.H13.KG68.Singer.F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem cartanSingerCover_f4
    {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CartanSingerCover ↥(F4.reeGamma K a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) :=
    ⟨hUC, isPGroup_reeFixedPosUnipotent_subgroupOf.of_equiv (Subgroup.subgroupOfEquivOfLe hUC),
      not_dvd_index_reeFixedPosUnipotent⟩
  have hHC : F4.reeFixedTorus K a ≤ F4.reeGamma K a := inf_le_right
  refine cartanSingerCover_of_le hUC hU hHC
    (reeFixedTorus_le_reeFixedBorel.trans reeFixedBorel_le_normalizer_reeFixedPosUnipotent) ?_
    (centralZ_injective (a := a)) centralZ_zero (fun c => hUC (centralZ_mem ha hK c))
    (fun c t ht => (commute_centralZ ha hK ht c).symm) (fun g hg hgc => ?_) (fun h hh => ?_)
    (fun w => ?_)
  · rw [reeGamma_inf_normalizer_reeFixedPosUnipotent, reeFixedBorel_eq_sup, sup_comm]
  · have hgZ : g ∈ ((Subgroup.center ↥(F4.reeFixedPosUnipotent K a)).map
        (F4.reeFixedPosUnipotent K a).subtype : Set (ModGL F4.tag K)) :=
      ⟨⟨g, hg⟩, Subgroup.mem_center_iff.2 fun t => Subtype.ext (hgc t t.2).symm, rfl⟩
    rw [coe_center_eq_range_centralZ ha hK] at hgZ
    exact hgZ
  · obtain ⟨u, v, rfl⟩ := rankOne_exists_torusPair_eq hK hh
    exact ⟨u ^ 2 ^ a, fun c => by rw [torusPair_conj_centralZ hK u v c, Units.val_pow_eq_pow_val]⟩
  · refine ⟨torusPair a (w ^ (2 * 2 ^ a), 1), rankOne_torusPair_mem_reeFixedTorus hK _ _,
      fun c => ?_⟩
    have : Fintype K := Fintype.ofFinite K
    rw [torusPair_conj_centralZ hK, Units.val_pow_eq_pow_val, ← pow_mul,
      show 2 * 2 ^ a * 2 ^ a = Fintype.card K by rw [← Nat.card_eq_fintype_card, hK]; ring,
      FiniteField.pow_card]

end CFSG.Quasithin.H13.KG68.Singer.F4
