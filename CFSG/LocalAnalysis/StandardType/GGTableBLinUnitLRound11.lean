module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLID
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLinePSL
public import CFSG.LocalAnalysis.StandardType.GGAssemblyElevenDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB LocalAnalysis.ComponentInitial.LinearFlag

theorem largeEvenLabelAll_linDvd_twoLocal {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGLinDvdLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarTwoLocalSCr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpn, hpd⟩ := h
  dsimp only at ht hl hpn hpd
  subst ht
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hlab.1 hpn
  have hd5 : 5 ≤ l + 1 := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    rcases hpd with ⟨k, hk⟩
    rcases k with _ | _ | k
    · omega
    · have : p ≠ 4 := by
        intro h4
        rw [h4] at hp
        exact absurd hp (by decide)
      omega
    · nlinarith
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', l + 1 - 2,
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TypeA.ggTorusLift_sub_two hp hpK (by omega) (TypeA.slHasSections_of_five_le hd5)),
    ggBstarTwoLocalSCr_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
      (LinUnitL.ggBstarTwoLocalSCr_PSL hp hpK hd5 le_rfl)⟩

theorem ggBstarInnerDiagLInputOn_of_le_linDvd {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGLinDvdLabel p lab) : GGBstarInnerDiagLInputOn S :=
  ggBstarInnerDiagLInputOn_of_labelsTwoLocal (fun p lab h => Or.inl (hS p lab h).1)
    fun _ _ hp hlab h => largeEvenLabelAll_linDvd_twoLocal hp hlab (hS _ _ h)

theorem ggBstarInnerDiagLInputOn_linDvd : GGBstarInnerDiagLInputOn GGLinDvdLabel :=
  ggBstarInnerDiagLInputOn_of_le_linDvd fun _ _ h => h

theorem ggTableBCxInputOn_linDvd_holds : GGTableBCxInputOn GGLinDvdLabel :=
  ggTableBCxInputOn_linDvd ggBstarInnerDiagLInputOn_linDvd

end CFSG.StandardType

end
