module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def ggNEE_tagOf : LargeEvenLieTag → Tag
  | .E7 => .E7
  | .E8 => .E8
  | _ => .E7

theorem ggNEE_largeEvenLabelAll_model_excPlus
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (h : lab.tag = .E7 ∨ lab.tag = .E8) (hpn : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGExcPlusWeylModelSCr (ggNEE_tagOf lab.tag) p (ggNbrExcPlusRank lab.tag) R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at h hpn
  rcases h with rfl | rfl
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    have hframe : GGExcPlusFrameModel .E7 p K := by
      by_cases h35 : p = 3 ∨ p = 5
      · exact excPlusFrameModel_E7_threeFive h35 K hpq
      · have h11 : 11 ≤ p := ExcFramesHalf.eleven_le_of_dvd_two_pow_add_one hp hp2 hpn
          (fun h3 => h35 (Or.inl h3)) (fun h5 => h35 (Or.inr h5))
        exact excPlusFrameModel_large (Or.inl rfl) hp h11 K hpq (fun Fr hFr X hX hXC hXF => by
          haveI := hX
          exact finite_fixed_le_map_adjointGroup_E7 Fr hFr X hXC hXF)
    refine ⟨K, inferInstance, inferInstance, hK, hQ', ?_⟩
    have := ggExcPlusWeylModelSCr_of_frameModel (Or.inl rfl) hp hp2 K hframe
    exact this
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    have hframe : GGExcPlusFrameModel .E8 p K := by
      by_cases h35 : p = 3 ∨ p = 5
      · exact excPlusFrameModel_E8_threeFive h35 K hpq
      · have h11 : 11 ≤ p := ExcFramesHalf.eleven_le_of_dvd_two_pow_add_one hp hp2 hpn
          (fun h3 => h35 (Or.inl h3)) (fun h5 => h35 (Or.inr h5))
        exact excPlusFrameModel_large (Or.inr rfl) hp h11 K hpq (fun Fr hFr X hX hXC hXF => by
          haveI := hX
          exact Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1
            (CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational_perfect (τ := .E8) (K := K)
              (L := AlgebraicClosure K) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC hXF).1))
    refine ⟨K, inferInstance, inferInstance, hK, hQ', ?_⟩
    have := ggExcPlusWeylModelSCr_of_frameModel (Or.inr rfl) hp hp2 K hframe
    exact this

end CFSG.StandardType

end
