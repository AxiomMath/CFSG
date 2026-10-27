module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerSCrComp
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section F4


theorem largeEvenLabelAll_torusNbrSCrComp_f4 (hKG : GGNbrKGF4ThreeAddSC) {p : ℕ}
    {lab : LargeEvenLabel} (h : GGNbrInner937F4Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbrSCrComp p r R I := by
  obtain ⟨htag, hp3, hpn⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag hp3
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 3,
    ggTorusLift_F4Plus Nat.prime_three (by norm_num) hpq, hKG K hpq⟩

theorem ggTableBNbrInnerInputOn_937F4 (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hKG : GGNbrKGF4ThreeAddSC) : GGTableBNbrInnerInputOn GGNbrInner937F4Label :=
  ggTableBNbrInnerInputOn_of_labelsSCrComp hL hPJ fun _ _ _ _ h =>
    largeEvenLabelAll_torusNbrSCrComp_f4 hKG h

end F4

section ExcPlus


theorem largeEvenLabelAll_torusNbrSCrComp_excPlus (hKG : GGNbrKGExcPlusSCWeylIrred) {p : ℕ}
    (hp : p.Prime) {lab : LargeEvenLabel} (h : GGNbrInner937ExcPlusLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusNbrSCrComp p r R I := by
  obtain ⟨htag, hp35, hpn⟩ := h
  have hp2 : p ≠ 2 := by omega
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  rcases htag with rfl | rfl
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    have hKf : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
    refine ⟨K, inferInstance, inferInstance, hK, hQ', 6, ggTorusLift_E7Plus hp hp2 hpq, ?_⟩
    exact ggTorusNbrSCrComp_of_ggTorusNbrSCr
      (ggTorusNbrSCr_of_scWeylIrred hp (TableBExc.center_recipeGroup_eq_bot .E7 K)
        (fun φ hφ _ => TableBExc.idImage_subset_inn_E7 K hφ)
        (ExcSplitL.ggCenterPrime_recipe_E7 (f := (f : ℕ)) f.pos hKf hp hp2)
        (hKG K p hp35 hpq).1)
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    refine ⟨K, inferInstance, inferInstance, hK, hQ', 7, ggTorusLift_E8Plus hp hp2 hpq, ?_⟩
    exact ggTorusNbrSCrComp_of_ggTorusNbrSCr
      (ggTorusNbrSCr_of_scWeylIrred hp (TableBExc.center_recipeGroup_eq_bot .E8 K)
        (fun φ hφ _ => TableBExc.idImage_subset_inn_E8 K hφ)
        (ExcSplitL.ggCenterPrime_recipe_E8 hp hp2) (hKG K p hp35 hpq).2)

theorem ggTableBNbrInnerInputOn_937ExcPlus (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hKG : GGNbrKGExcPlusSCWeylIrred) : GGTableBNbrInnerInputOn GGNbrInner937ExcPlusLabel :=
  ggTableBNbrInnerInputOn_of_labelsSCrComp hL hPJ fun _ _ hp _ h =>
    largeEvenLabelAll_torusNbrSCrComp_excPlus hKG hp h

end ExcPlus

end CFSG.StandardType

end
