module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreSp
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsLiftOmega
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsLiftSp
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylIrredLabels
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem recipeSymplectic_innLiftNs {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n + 1) (hl : 4 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ((∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift p 3 R) := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    fun g => RecipeFieldSp.mem_conjImage_iff_inn.mpr ⟨g, rfl⟩,
    TableBSymp.ggTorusLift_symplecticNs hp hp2 hpq hl⟩

theorem largeEvenLabelAll_innLift_spNs {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : (lab.tag = .B ∨ lab.tag = .C) ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift p 3 R := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl, hpn⟩ := h
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h hl hpn <;> subst h <;>
    exact recipeSymplectic_innLiftNs hp hp2 hpn hl hQ

theorem largeEvenLabelAll_innLift_omegaPlusNs {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : lab.tag = .D ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift p 3 R := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn2, hpn⟩ := h
  dsimp only at ht hl hn2 hpn ⊢
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h3
  · omega
  · obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    exact ⟨K, inferInstance, inferInstance, hK, hQ', fun g => ⟨g, rfl⟩,
      TableBSymp.ggTorusLift_omegaPlusNs hp hp2 hpq hK4 hl⟩

theorem largeEvenLabelAll_innLift_omegaMinusNs {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : lab.tag = .twD ∧ 5 ≤ lab.rank ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift p 3 R := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn2, hpn⟩ := h
  dsimp only at ht hl hn2 hpn ⊢
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
    have := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', fun g => ⟨g, rfl⟩,
      TableBSymp.ggTorusLift_omegaMinusNs hp hp2 hpq hK4 (by omega) b c⟩

section Rows

theorem largeEvenLabelAll_rowPlain_of_fieldFixNsRowLabel {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab) (h : GGFieldFixNsRowLabel p lab) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p 3) := by
  obtain ⟨hpn, h⟩ := h
  rcases h with ⟨hBC, h4⟩ | ⟨hD, h4, -, hn2⟩ | ⟨hT, h5, hn2⟩
  · exact (largeEvenLabelAll_and (largeEvenLabelAll_innLift_spNs hp hp2 ⟨hBC, h4, hpn⟩)
      (largeEvenLabelAll_torusIrredSC_spNonsplit hp hlab ⟨hBC, hpn⟩)).mono
      fun _ _ _ _ ⟨⟨hi, hl⟩, hs⟩ => ⟨hi, hl, fun _ _ => ggTorusNoLine_of_ggTorusIrredSC hp hs⟩
  · exact (largeEvenLabelAll_and (largeEvenLabelAll_innLift_omegaPlusNs hp hp2 ⟨hD, h4, hn2, hpn⟩)
      (largeEvenLabelAll_torusIrredSC_orthNs hp ⟨Or.inl hD, h4, hpn⟩)).mono
      fun _ _ _ _ ⟨⟨hi, hl⟩, hs⟩ => ⟨hi, hl, fun _ _ => ggTorusNoLine_of_ggTorusIrredSC hp hs⟩
  · exact (largeEvenLabelAll_and (largeEvenLabelAll_innLift_omegaMinusNs hp hp2 ⟨hT, h5, hn2, hpn⟩)
      (largeEvenLabelAll_torusIrredSC_orthNs hp ⟨Or.inr hT, by omega, hpn⟩)).mono
      fun _ _ _ _ ⟨⟨hi, hl⟩, hs⟩ => ⟨hi, hl, fun _ _ => ggTorusNoLine_of_ggTorusIrredSC hp hs⟩

end Rows

end CFSG.StandardType

end
