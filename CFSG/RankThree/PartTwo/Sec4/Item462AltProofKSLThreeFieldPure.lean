module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeFieldFixed
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeDatumFixed
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeQuasisimpleSL
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeFixedDatumQs
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeCornerSU32

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG CFSG.RankThree.PartTwo.Sec4

theorem core_field_pure {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {β' : MulAut (slPi π 3 (p ^ f) K)}
    (hβ' : ∀ s : slPi π 3 (p ^ f) K,
      ((β' s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = frobGL σ (s : GL (Fin 3) K))
    (hD : NoncyclicDatum β') : False := by
  haveI := hK.finite
  have hβ'3 : β' ^ 3 = 1 := by
    refine MulEquiv.ext fun s => ?_
    simp only [pow_three, MulAut.mul_apply, MulAut.one_apply]
    apply Subtype.ext
    rw [hβ' (β' (β' s)), hβ' (β' s), hβ' s]
    exact frobGL_three hσ _
  have hZS : Nat.card (Subgroup.center (slPi π 3 (p ^ f) K)) = 3 :=
    KFacts.card_center_slPi hK hq
  have hF : ∀ s : slPi π 3 (p ^ f) K, s ∈ fixedSub β' ↔
      frobGL σ (s : GL (Fin 3) K) = (s : GL (Fin 3) K) := by
    intro s
    rw [mem_fixedSub, ← Subtype.coe_inj, hβ' s]
  obtain ⟨f₀, K₀, _, hf, hK₀, ⟨e⟩⟩ := fixed_equiv hK hq2 hσ (fixedSub β') hF
  have hq₀ : ModThree π (p ^ f₀) :=
    modThree_of_cube (by rw [← pow_mul, mul_comm, ← hf]; exact hq)
  have hZF : Nat.card (Subgroup.center (fixedSub β')) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact KFacts.card_center_slPi hK₀ hq₀
  have hFD : FixedDatumZ (fixedSub β') := fixedDatumZ_of_noncyclicDatum hZS hβ'3 hZF hD
  by_cases hq₀2 : 2 < p ^ f₀
  · have hqF : IsQuasisimple ↥(fixedSub β') :=
      IsQuasisimple.of_mulEquiv e (isQuasisimple_slPi hK₀ hq₀2)
    have hZ3 : ∀ z ∈ Subgroup.center (fixedSub β'), z ^ 3 = 1 := by
      intro z hz
      have h : (⟨z, hz⟩ : Subgroup.center (fixedSub β')) ^ Nat.card (Subgroup.center (fixedSub β'))
          = 1 := pow_card_eq_one'
      rw [hZF] at h
      exact congrArg Subtype.val h
    exact false_of_fixedDatum_isQuasisimple hqF hZ3 hFD.fixedDatum
  · have hp := hK₀.prime
    have hf₀ := hK₀.one_le
    have h2 : p ^ f₀ = 2 := by
      have : 2 ≤ p ^ f₀ := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (h2 ▸ dvd_pow_self p (by omega))
    subst hp2
    have hf1 : f₀ = 1 := Nat.pow_right_injective le_rfl (by simpa using h2)
    subst hf1
    cases π
    · exact false_of_fixedDatumZ_su32 hK₀ e hFD
    · exfalso
      change 2 ^ 1 % 3 = 1 at hq₀
      norm_num at hq₀

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
