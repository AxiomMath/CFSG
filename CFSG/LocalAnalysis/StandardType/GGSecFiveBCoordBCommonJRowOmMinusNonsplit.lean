module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeConj

import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmMinusNonsplitAux1
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmMinusNonsplitAux2
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmMinusNonsplitAux3
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmMinusNonsplitAux4
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSecFiveBNativeRow_omMinusNonsplit {K : Type} [Field K] [Finite K] {f p m : ℕ}
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) (hm : 3 ≤ m)
    (hmo : Odd m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGSecFiveBNativeRow (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) p m
      (fun lab => lab = ⟨.twA, m - 1, f⟩) (fun lab => lab = ⟨.D, m, f⟩) := by
  haveI : CharP K 2 := by
    haveI := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      have h2 : p ∣ 2 := by rw [h0] at hpq; simpa using hpq
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      have hge : 2 ≤ p := hp.two_le
      omega
    · exact h0
  intro T hT hcardT
  have h3 : p ^ 3 ≤ Nat.card T := by
    rw [hcardT]
    exact Nat.pow_le_pow_right hp.one_le hm
  have hsc := CommonJOmMinusNonsplit.ggCommonJRowOmMinusNonsplit_sc hK hp hp2 hpq hm hmo hirr
    hT hcardT
  obtain ⟨k, τ, hτ, hrange, hsgn, hperm, hnorm⟩ :=
    (ggOrthSignedTorusInput_holds.2 K m p b c hm hirr hp (Or.inr ⟨hmo, hpq'⟩)) T hT h3 hsc
  have hkcard : Nat.card T = p ^ k := by
    haveI : NeZero p := ⟨hp.ne_zero⟩
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv, Nat.card_fun,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
  have hkm : k = m := Nat.pow_right_injective hp.two_le (hkcard.symm.trans hcardT)
  subst k
  have hsign : CommonJOmMinusNonsplit.GGOmMinusNonsplitSignedNormalizer τ := by
    intro g hg
    obtain ⟨π, ε, hε, hrel⟩ := hnorm g (by
      intro e he
      have he' : e ∈ τ.range := by rwa [← hrange] at he
      have h := hg e he'
      rwa [hrange] at h)
    have hex : ∀ f, ∃ f', τ f' = g * τ f * g⁻¹ := fun f => hg (τ f) ⟨f, rfl⟩
    choose u hu using hex
    exact ⟨u, ⟨π, ε, hε, fun f i => hrel f (u f) (hu f).symm i⟩, fun f => (hu f).symm⟩
  rw [← hrange]
  refine GGSecFiveBNativeAt.of_torus τ hτ hsign ?_
  intro g J hJ hcardJ
  rcases CommonJOmMinusNonsplit.ggCommonJRowOmMinusNonsplit_position hK hp hp2 hpq hm hmo hirr
      hτ hsign hsgn hperm g J hJ hcardJ with ⟨hD, hΛ⟩ | ⟨hS, hg1⟩
  · refine Or.inl ⟨hD, ⟨⟨.twA, m - 1, f⟩, rfl, hΛ, ?_, ?_⟩⟩
    · exact CommonJOmMinusNonsplit.ggCommonJRowOmMinusNonsplit_dense hK hp hp2 hpq hm hmo hirr
        hτ hsign hsgn hperm hD hΛ J hJ hcardJ
    · rintro hlab
      exfalso
      have hm4 : m - 1 = 3 := by simpa using congrArg LargeEvenLabel.rank hlab
      rcases hmo with ⟨t, ht⟩
      omega
  · refine Or.inr ⟨hS, ⟨⟨.D, m, f⟩, rfl, ⟨hf1, hm⟩, ?_⟩⟩
    exact CommonJOmMinusNonsplit.ggCommonJRowOmMinusNonsplit_sparse hK hp hp2 hpq hm hmo hirr
      hτ hsign hsgn hperm hS hg1 J hJ hcardJ

end CFSG.StandardType

end
