module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

theorem ggNbr_inndiag_pRank_ge_three {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {K : Subgroup G} (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K)
    {S : ℕ → LargeEvenLabel → Prop} (hrow : GGInnerDiagOnLabel S p Bs K) :
    StandardType.LargeEvenMarking ↥K (fun lab R _ I _ _ => S p lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  obtain ⟨y, hy⟩ := hK.1
  obtain ⟨⟨hBel, hBcard, -⟩, hyB, -, -, -, hSc⟩ := hy.1
  obtain ⟨hp, -, -, h4⟩ := hcfg.1.1.1.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hcfg.1.1.2.1.1
  refine largeEvenMarking_mono ?_ hrow
  intro lab R _ I _ θ hP
  obtain ⟨hSlab, hN, hind⟩ := hP
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  refine ⟨hSlab, (ggBeta K θ hBN).range, ?_, isElemAbelian_range_ggBeta θ hBel hBN, ?_⟩
  · rintro _ ⟨b, rfl⟩
    exact ggBeta_mem K θ hBN (fun b hb => hind b (hBBs hb)) b
  have hker : (ggBeta K θ hBN).ker.map B.subtype ≤ Subgroup.zpowers y := by
    rintro _ ⟨b, hb, rfl⟩
    have hb1 : ggLAut K θ ⟨b, hBN b.2⟩ = 1 :=
      (ggBeta_eq K θ hBN b).symm.trans (MonoidHom.mem_ker.mp hb)
    have hc := mem_centralizer_of_ggLAut_eq_one K θ hrow.1 hb1
    refine (hSc b).mp ⟨b.2, hBN b.2, ?_⟩
    refine (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_).trans_le bot_le
    exact Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hc)
  have hcard : Nat.card (ggBeta K θ hBN).ker ≤ p := by
    rw [← Subgroup.card_map_of_injective B.subtype_injective]
    refine (Subgroup.card_le_of_le hker).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos (hBel.2 y hyB)
  refine Nat.le_of_mul_le_mul_right ?_ hp.pos
  calc p ^ 3 * p = p ^ 4 := by ring
    _ ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
    _ = Nat.card ↥B := hBcard.symm
    _ = Nat.card (ggBeta K θ hBN).range * Nat.card (ggBeta K θ hBN).ker :=
      (TableB.card_range_mul_card_ker _).symm
    _ ≤ Nat.card (ggBeta K θ hBN).range * p := Nat.mul_le_mul_left _ hcard

end CFSG.StandardType

end
