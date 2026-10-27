module

public import CFSG.RankThree.PartOne.K133H.D4Odd
public import CFSG.RankThree.PartOne.K133B.Defs
public import CFSG.RankThree.PartOne.K133X.D4

public section

namespace CFSG.RankThree.PartOne.K133H

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133 CFSG.RankThree.PartOne.Q1327T
  CFSG.RankThree.PartOne.K133B
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem row8OddAt_leaf7_eight : Row8OddAt (K133.leaf7 8) := by
  intro Q _ _ p g Ē hp11 hZ hX h
  obtain ⟨q, hq2, hiso⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hmodel := K133X.chevalleyExceptionalModel_trialityD4_of_isoLie hq2 hiso
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hf1 : 1 ≤ q.exponent := hmodel.1.2.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨θ⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_two hf1 hmodel.2
  have hKq : Nat.card K = (2 ^ q.exponent) ^ 3 := hK
  let ce : Q ≃* Q ⧸ Subgroup.center Q :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let eQ : Q ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ce.trans θ
  let ι₀ : Q →* ModGL Tag.D4 K :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp eQ.toMonoidHom
  have hι₀ : Function.Injective ι₀ := Subtype.val_injective.comp eQ.injective
  have hι₀Y : ∀ x, ι₀ x ∈ adjointGroup Tag.D4 K := fun x =>
    (Subgroup.mem_inf.1 (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom (eQ x).2)).1
  have : Fact p.Prime := ⟨hp⟩
  have := h.elem
  have hpow : ∀ x ∈ Ē, x ^ p = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (A := Ē) x hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hKq]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := q.exponent * 3) (by omega) (by rw [hKq, pow_mul])
  have : NeZero (p - 1) := ⟨by omega⟩
  let K' := FiniteField.Extension K 2 (p - 1)
  let ι : K →+* K' := algebraMap K K'
  have hpKn : ¬ p ∣ Nat.card K := by
    intro hd
    rw [hKq] at hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hd)))
  have hpK : p ∣ Nat.card K' - 1 := by
    have h1 : ((Nat.card K : ℕ) : ZMod p) ^ (p - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one (by rwa [Ne, ZMod.natCast_eq_zero_iff])
    rw [FiniteField.natCard_extension, ← ZMod.natCast_eq_zero_iff,
      Nat.cast_sub (Nat.one_le_pow _ _ Nat.card_pos), Nat.cast_pow, h1, Nat.cast_one, sub_self]
  let ι₁ : Q →* ModGL Tag.D4 K' := (baseChangeGL ι).comp ι₀
  have hι₁ : Function.Injective ι₁ := (baseChangeGL_injective ι).comp hι₀
  have hι₁Y : ∀ x, ι₁ x ∈ adjointGroup Tag.D4 K' := fun x =>
    baseChangeGL_mem_adjointGroup ι (hι₀Y x)
  intro _
  exact oddOrderOneOrThree_torusImage_of_embedding_D4 hp hp5 hpK ι₁ hι₁ hι₁Y hpow

end CFSG.RankThree.PartOne.K133H
