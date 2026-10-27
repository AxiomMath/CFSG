module

public import CFSG.LocalAnalysis.StandardType.GGExcKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesIsogenyTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Exceptional
open CFSG.Open (IsElemAbelian)

private theorem ktw_regime_arith (f : ℕ) (hf : f ≠ 0) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : ¬ GGExcRegime p f) :
    ¬ p ∣ 2 ^ f ∧ 3 < p ∧ ¬ p ∣ 2 ^ f + 1 ∧ orderOf (((2 ^ f : ℕ) : ZMod p)) ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : ¬ p ∣ 2 ^ f := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have ha : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hsq : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
    have : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [ha, this]; ring
  have hp3 : 3 < p := by
    have h2 := hp.two_le
    by_contra h
    have hp3 : p = 3 := by omega
    subst hp3
    apply hreg
    have hne : ((2 : ZMod 3) ^ f) ≠ 0 := by
      intro h0
      have := (ZMod.natCast_eq_zero_iff (2 ^ f) 3).1 (by push_cast; exact h0)
      exact hpK this
    have h1 := ZMod.pow_card_sub_one_eq_one hne
    have h3 : (((2 ^ f) ^ 2 - 1 : ℕ) : ZMod 3) = 0 := by
      have hq1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
      rw [Nat.cast_sub hq1]; push_cast
      have : ((2 : ZMod 3) ^ f) ^ 2 = 1 := by simpa using h1
      rw [this]; simp
    have h4 := (ZMod.natCast_eq_zero_iff _ 3).1 h3
    rw [hsq] at h4
    rcases (Nat.Prime.dvd_mul hp).1 h4 with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨hpK, hp3, fun h => hreg (Or.inr h), ?_⟩
  intro h
  apply hreg; left
  have h1 := orderOf_eq_one_iff.1 h
  have : (((2 ^ f - 1 : ℕ)) : ZMod p) = 0 := by
    rw [Nat.cast_sub ha, h1]; simp
  exact (ZMod.natCast_eq_zero_iff _ p).1 this

private theorem ktw_isElemAbelian_comap {H H' : Type*} [Group H] [Group H'] {p : ℕ} (χ : H →* H')
    (hχ : Function.Injective χ) {E : Subgroup H'} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap χ) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (hχ ?_)⟩⟩, fun x hx => hχ ?_⟩
  · have h := congrArg Subtype.val (hE.1.1.1 ⟨χ x, x.2⟩ ⟨χ y, y.2⟩)
    simpa only [map_mul, Subgroup.coe_mul] using h
  · rw [map_pow, hE.2 _ hx, map_one]

private theorem ktw_card_comap {H H' : Type*} [Group H] [Group H'] (χ : H →* H')
    (hχ : Function.Injective χ) {E : Subgroup H'} (hER : E ≤ χ.range) :
    Nat.card (E.comap χ) = Nat.card E := by
  have h := Subgroup.card_map_of_injective (K := E.comap χ) hχ
  rw [Subgroup.map_comap_eq_self hER] at h
  exact h.symm

section ExcCertTwE6Holds

theorem ggExcKGRankTwE6_holds : GGExcKGRankTwE6 := by
  intro n f G _ _ ψ hset p hp hp2 hreg E hEn hE hdiag
  obtain ⟨⟨hadm, _hrk⟩, hker, ⟨hcomm, _hlie⟩, hcent⟩ := hset
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨hpq, hp3, hpq1, hne1⟩ := ktw_regime_arith f (by omega) p hp hp2 hreg
  have h5 : 5 ≤ p := by
    by_contra h
    have h4' : p = 4 := by omega
    rw [h4'] at hp
    exact absurd hp (by norm_num)
  obtain ⟨χ, hχinj, hχrange⟩ := ExcFrames.exists_injective_factor_twistedE6 hf ψ hker hcent
  have hER : E ≤ χ.range := by
    rw [hχrange]
    intro b hb
    exact ExcFrames.mem_range_of_innerDiag_twistedE6 hp hp2 hf
      (fun h => absurd h.1 (by omega)) ψ hker hcomm hcent (hEn hb) (hE.2 b hb) (hdiag b hb)
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hle
  have hlt : p ^ 3 < Nat.card E := not_le.mp hle
  have hP : IsPGroup p E := fun g =>
    ⟨1, by simpa only [pow_one] using Subtype.ext (hE.2 g.1 g.2)⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk4 : 4 ≤ k := by
    have hlt' : p ^ 3 < p ^ k := by rwa [hk] at hlt
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt'
    omega
  have hcardE4 : p ^ 4 ≤ Nat.card E := by
    rw [hk]
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mpr hk4
  have hAel : IsElemAbelian p (E.comap χ) := ktw_isElemAbelian_comap χ hχinj hE
  have hAc : p ^ 4 ≤ Nat.card (E.comap χ) := by
    rw [ktw_card_comap χ hχinj hER]
    exact hcardE4
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  set σ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f) :=
    iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ f := fun c => iterateFrobeniusEquiv_def _ 2 f c
  have hσθ : σ.toRingHom = frobQ 2 f := RingHom.ext fun c => by
    change σ c = frobQ 2 f c
    rw [hσ, frobQ_apply]
  have he1 : orderOf (((2 ^ f : ℕ)) : ZMod p) = 1 :=
    ExcFrames.orderOf_eq_one_of_four_le_card_graphFixed Nat.prime_two hf
      (GaloisField 2 (2 * f)) hK σ hσ hσθ hp h5 hpq hpq1 hAel hAc
  exact hne1 he1

end ExcCertTwE6Holds

end CFSG.StandardType
