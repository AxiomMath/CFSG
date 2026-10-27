module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLineDecomp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Main

theorem largeEvenLabelAll_noLine_excPlus_largePrime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel}
    (h : (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n + 1)
    (h78 : (lab.tag = .E7 ∨ lab.tag = .E8) → ¬ GGNbrExcPlusSmallPrimeE7E8 p)
    (hF4 : lab.tag = .F4 → ¬ GGNbrExcPlusSmallPrimeF4 p) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLine p (ggNbrExcPlusRank lab.tag) R I := by
  obtain ⟨htag, hpn⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn h78 hF4
  rcases htag with rfl | rfl | rfl
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      fun _ _ => ggTorusNoLine_E7Plus_largePrime hp hp2 hpq (h78 (Or.inl rfl))⟩
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      fun _ _ => ggTorusNoLine_E8Plus_largePrime hp hp2 hpq (h78 (Or.inr rfl))⟩
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      fun _ _ => ggTorusNoLine_F4Plus_largePrime hp hp2 hpq (hF4 rfl)⟩

theorem largeEvenLabelAll_torusLift_noLine_excPlus_largePrime {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (h : (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n + 1)
    (h78 : (lab.tag = .E7 ∨ lab.tag = .E8) → ¬ GGNbrExcPlusSmallPrimeE7E8 p)
    (hF4 : lab.tag = .F4 → ¬ GGNbrExcPlusSmallPrimeF4 p) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∃ r, (GGTorusLift p r R ∨ r = 0) ∧ GGTorusNoLine p r R I :=
  (largeEvenLabelAll_and (largeEvenLabelAll_torusLift_excPlus hp hp2 h)
    (largeEvenLabelAll_noLine_excPlus_largePrime hp hp2 h h78 hF4)).mono
      fun _ _ _ _ ⟨hl, hn⟩ hs hna => ⟨_, Or.inl hl, hn hs hna⟩

theorem ggNbrInnerWeylOn_excPlusLarge : GGNbrInnerWeylOn GGNbrWeylExcPlusLargePrimeLabel :=
  ggNbrInnerWeylOn_of_labels fun p lab hp hp2 hlab ⟨⟨hpow, ht, hE⟩, hns⟩ =>
    largeEvenLabelAll_weylInnerKLevel_of_noLine_or
      (largeEvenLabelAll_pow_mem_powMem hp hp2 hlab hpow)
      (largeEvenLabelAll_torusLift_noLine_excPlus_largePrime hp hp2 ⟨ht, hE⟩
        (fun h78 h' => hns ⟨⟨hpow, ht, hE⟩, Or.inl ⟨h78, h'⟩⟩)
        (fun hF4 h' => hns ⟨⟨hpow, ht, hE⟩, Or.inr ⟨hF4, h'⟩⟩))

end Main

end CFSG.StandardType

end
