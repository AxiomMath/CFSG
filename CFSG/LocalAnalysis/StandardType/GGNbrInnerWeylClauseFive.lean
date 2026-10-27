module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMore
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open NbrInnerMore

section Main

theorem ggNbrInnerWeylOn_of_clauseFive {S : ℕ → LargeEvenLabel → Prop}
    (h3 : ∀ p lab, S p lab → p ≠ 3 ∨ ∀ (X : Type) [Group X], MarkedModel lab X →
      ∀ lab' : LargeEvenLabel, markChar lab' ≠ 2 → ¬ MarkedModel lab' X)
    (hout : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      S p lab → LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I))
    (hdet : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      S p lab → ∀ (X : Type) [Group X], MarkedModel lab X → ∀ lab' : LargeEvenLabel,
        LargeEvenInLambda2 lab' → markChar lab' = 2 → MarkedModel lab' X →
          ∀ c, ¬ LargeEvenHalfSplit p lab' c) :
    GGNbrInnerWeylOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN hxK P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have h5 : GGNbrClauseFiveMarking p x K :=
    (hcfg.1.2.2.2.2.2.2.2.2.2.1 y K ⟨hnb.1, D, J, hcfg.2.2, hnb.2⟩).2
  have hxB : x ∈ B := hcfg.1.2.2.2.2.2.2.1.2.1
  have hxp : x ^ p = 1 := hcfg.1.2.2.2.2.2.2.1.1.1.2 x hxB
  obtain ⟨hK, lab, hlab, hraw⟩ := largeEvenMarking_markedModel hP
  by_cases hSl : S p lab
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ (hout p lab hp hp2 hlab hSl _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ, hMM⟩, hO⟩
    refine ⟨hs, hna, θ, hPθ, fun _ hxI => ?_⟩
    exfalso
    have hφp : ggLAut K θ ⟨x, hxK⟩ ^ p = 1 := by
      have e : (⟨x, hxK⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 :=
        Subtype.ext (by simpa using hxp)
      rw [← map_pow, e, map_one]
    obtain ⟨r, hr⟩ := hO hs hna _ hxI hφp
    obtain ⟨k, hk, hkx⟩ := exists_conj_of_ggLAut_eq_conj hK θ hxK hr.symm
    have hMK : MarkedModel lab (K ⧸ Subgroup.center K) := MarkedModel.of_mulEquiv θ.symm hMM
    rcases h3 p lab hSl with hp3 | hX3
    · exact ClNonsplit.not_ggNbrClauseFiveMarking_of_inner hp hp3 ⟨k, hk, hkx⟩
        (fun lab' hlab' hc' hM' => hdet p lab hp hp2 hlab hSl _ hMK lab' hlab' hc' hM' _)
        (fun lab' hlab' _ _ => ggRawInnFieldInput_holds p hp hp2 lab' hlab') h5
    · exact not_ggNbrClauseFiveMarking_of_inner' ⟨k, hk, hkx⟩
        (fun lab' hlab' hc' hM' => hdet p lab hp hp2 hlab hSl _ hMK lab' hlab' hc' hM' _)
        (fun lab' hc' hM' => hX3 _ hMK lab' hc' hM')
        (fun lab' hlab' _ _ => ggRawInnFieldInput_holds p hp hp2 lab' hlab') h5
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ, -⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS hSl⟩

theorem ggNbrInnerWeylOn_nsSp : GGNbrInnerWeylOn GGNbrNsSpLabel :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.1 h.2.2))
    (fun p _ _ _ hlab h =>
      (NbrInnerMore.largeEvenLabelAll_outdiagPrime_sp p hlab h.1).mono fun _ _ _ _ h _ _ => h)
    (fun _ _ _ _ _ h _ _ hX _ _ hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_sp h.1 h.2.1 h.2.2 hX hc' hX' c)

theorem ggNbrInnerWeylOn_nsOrth : GGNbrInnerWeylOn GGNbrNsOrthLabel :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.2.1 h.2.2.2))
    (fun p _ _ _ _ h =>
      (NbrInnerMore.largeEvenLabelAll_outdiagPrime_orth p h.1 h.2.1).mono fun _ _ _ _ h _ _ => h)
    (fun _ _ hp hp2 _ h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_orth hp hp2 h.1 h.2.1 h.2.2.1 h.2.2.2 hX hlab'
        hc' hX' c)

theorem ggNbrInnerWeylOn_nsLin : GGNbrInnerWeylOn GGNbrNsLinLabel :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inr fun _ _ hX _ hc =>
      NbrInnerMore.not_markedModel_char_ne_two_lin h.1 h.2.1 hX hc)
    (fun _ _ hp _ hlab h =>
      (NbrInnerMore.largeEvenLabelAll_outdiagPrime_linear hp hlab h.1 h.2.2.1).mono
        fun _ _ _ _ h _ _ => h)
    (fun _ _ _ _ _ h _ _ hX _ _ hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_lin h hX hc' hX' c)

theorem ggNbrInnerWeylOn_nsUnit : GGNbrInnerWeylOn GGNbrNsUnitLabel :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inr fun _ _ hX _ hc =>
      NbrInnerMore.not_markedModel_char_ne_two_unit h.1 h.2.1 hX hc)
    (fun _ _ hp _ hlab h =>
      (NbrInnerMore.largeEvenLabelAll_outdiagPrime_unitary hp hlab h.1 h.2.2.1).mono
        fun _ _ _ _ h _ _ => h)
    (fun _ _ _ _ _ h _ _ hX _ _ hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_unit h hX hc' hX' c)

theorem ggNbrInnerWeylOn_nsE7 : GGNbrInnerWeylOn GGNbrNsE7Label :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.1 h.2.2))
    (fun p _ _ _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_E7 p hlab h.1)
    (fun _ _ _ _ _ h _ _ hX _ _ hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_E7 h hX hc' hX' c)

theorem ggNbrInnerWeylOn_nsE6 : GGNbrInnerWeylOn GGNbrNsE6Label :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inr fun _ _ hX _ hc => NbrInnerMore.not_markedModel_char_ne_two_E6 h.1 hX hc)
    (fun _ _ hp _ _ h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_E6 hp h.1 h.2.1)
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_E6 hlab h hX hlab' hc' hX' c)

theorem ggNbrInnerWeylOn_nsTwE6 : GGNbrInnerWeylOn GGNbrNsTwE6Label :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.1 h.2.2))
    (fun _ _ hp _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_twE6 hp
      (LinNonsplit.ne_three_of_not_dvd h.2.1 h.2.2) hlab h.1)
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_twE6 hlab h hX hlab' hc' hX' c)

theorem ggNbrInnerWeylOn_nsF4 : GGNbrInnerWeylOn GGNbrNsF4Label :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.1 h.2.2))
    (fun _ _ _ _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_of_subset_inn
      (largeEvenLabelAll_subset_inn hlab (Or.inr (Or.inr (Or.inl h.1)))))
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_F4 hlab h hX hlab' hc' hX' c)

theorem ggNbrInnerWeylOn_nsE8 : GGNbrInnerWeylOn GGNbrNsE8Label :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.1 h.2.2))
    (fun _ _ _ _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_of_subset_inn
      (largeEvenLabelAll_subset_inn hlab (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.1)))))))
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_E8 hlab h hX hlab' hc' hX' c)

theorem ggNbrInnerWeylOn_nsTriD4 : GGNbrInnerWeylOn GGNbrNsTriD4Label :=
  ggNbrInnerWeylOn_of_clauseFive (fun _ _ h => Or.inl h.2.2)
    (fun _ _ _ _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_of_subset_inn
      (TableBExcSmallRest.largeEvenLabelAll_subset_inn_triD4 hlab h.1))
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_triD4 hlab h hX hlab' hc' hX' c)

theorem ggNbrInnerWeylOn_nsTwF4 : GGNbrInnerWeylOn GGNbrNsTwF4Label :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.1 h.2.2))
    (fun _ _ _ _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_of_subset_inn
      (largeEvenLabelAll_subset_inn_twF4 hlab h.1))
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_twF4 hlab h hX hlab' hc' hX' c)

theorem ggNbrInnerWeylOn_nsVac : GGNbrInnerWeylOn GGNbrNsVacLabel :=
  ggNbrInnerWeylOn_nsSp.or (ggNbrInnerWeylOn_nsOrth.or
    (ggNbrInnerWeylOn_nsLin.or (ggNbrInnerWeylOn_nsUnit.or
      (ggNbrInnerWeylOn_nsE7.or (ggNbrInnerWeylOn_nsE6.or
        (ggNbrInnerWeylOn_nsTwE6.or (ggNbrInnerWeylOn_nsF4.or
          (ggNbrInnerWeylOn_nsE8.or (ggNbrInnerWeylOn_nsTriD4.or
            ggNbrInnerWeylOn_nsTwF4)))))))))

end Main


end CFSG.StandardType

end
