module

public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusCentrallyClosed
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenIso
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalTwoMultiplier

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.LieType.Steinberg.CentralExt
open CFSG.RankThree.PerfectCover

theorem rPlus_injective_of_cover_two
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 5 ≤ m) (L' : Type) [Group L'] [Finite L']
    (ψ : L' →* OrthRest.RPlus K m) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    Function.Injective ψ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) (hK.trans (pow_one 2).symm)
  let X := StatedProj (StatedOmega (StatedQuadPlus m K))
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.OrthogonalTwo.pomegaPlus_two_hopfMultiplier
      (K := K) (n := m) (p := 2) (f := 1) hm (by rw [hK, pow_one]) hK
  haveI : Subsingleton (CFSG.Blueprint.Multiplier.generic .POmegaPlus m 2 1) := by
    have hg : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus m 2 1 = (1, 1) := by
      simp [CFSG.Blueprint.Multiplier.genericOrders]
    change Subsingleton (Multiplicative (ZMod (CFSG.Blueprint.Multiplier.genericOrders
      .POmegaPlus m 2 1).1) × Multiplicative (ZMod (CFSG.Blueprint.Multiplier.genericOrders
      .POmegaPlus m 2 1).2))
    rw [hg]
    infer_instance
  haveI : Subsingleton (CFSG.Open.griessHopfMultiplier X) := eM.toEquiv.subsingleton
  haveI : Subsingleton (CFSG.RankThree.PerfectCover.hopfMultiplier X) :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).symm.toEquiv.subsingleton
  let ψ' : L' →* X := ψ
  have hψ' : Function.Surjective ψ' := hψ
  have hker' : ψ'.ker ≤ Subgroup.center L' := hker
  haveI : Group.IsPerfect L' := ⟨hperf⟩
  let φ : CFSG.RankThree.PerfectCover.hopfMultiplier X →* ψ'.ker :=
    CFSG.RankThree.PerfectCover.hopfMultiplierToKer ψ' hψ' hker'
  have hφ : Function.Surjective φ :=
    CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective ψ' hψ' hker'
  haveI : Subsingleton ψ'.ker := hφ.subsingleton
  have hbot : ψ'.ker = ⊥ := Subgroup.eq_bot_of_subsingleton _
  exact (MonoidHom.ker_eq_bot_iff ψ').mp hbot

theorem rMinus_injective_of_cover_two
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (L' : Type) [Group L'] [Finite L']
    (ψ : L' →* OrthRest.RMinus K m b c) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    Function.Injective ψ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) (hK.trans (pow_one 2).symm)
  let X := StatedProj (StatedOmega (StatedQuadMinus (m + 1) K b c))
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.OrthogonalTwo.pomegaMinus_two_hopfMultiplier
      (K := K) (n := m + 1) (b := b) (c := c) (p := 2) (f := 1)
      (by omega) hbc (by rw [hK, pow_one]) hK
  have hodd : Odd (2 ^ (m + 1) + 1) :=
    (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hcop : Nat.Coprime 4 (2 ^ (m + 1) + 1) := by
    simpa using Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
  have hgcd : Nat.gcd 4 ((2 ^ 1) ^ (m + 1) + 1) = 1 := by
    rw [pow_one]
    exact hcop.gcd_eq_one
  haveI : Subsingleton (Multiplicative (ZMod (Nat.gcd 4 ((2 ^ 1) ^ (m + 1) + 1)))) := by
    rw [hgcd]
    infer_instance
  haveI : Subsingleton (CFSG.Open.griessHopfMultiplier X) := eM.toEquiv.subsingleton
  haveI : Subsingleton (CFSG.RankThree.PerfectCover.hopfMultiplier X) :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).symm.toEquiv.subsingleton
  have hbot : (LargeEvenScalars (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K).subgroupOf
      (LargeEvenOmega (StatedQuadMinus (m + 1) K b c)) = ⊥ := by
    refine TableBOrth.scalars_subgroupOf_omega_eq_bot
      (Q := StatedQuadMinus (m + 1) K b c)
      (v₀ := Pi.single (Sum.inr (Sum.inr 0)) 1) (fun x v => ?_) ?_
    · rw [← CFSG.LieType.Universal.Spin.coe_quadMinus, QuadraticMap.map_smul, smul_eq_mul, sq]
    · rw [← CFSG.LieType.Universal.Spin.coe_quadMinus,
        CFSG.LieType.Universal.Spin.quadMinus_apply]
      simp
  let eProj : StatedOmega (StatedQuadMinus (m + 1) K b c) ≃* X :=
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm
  let e : OrthRest.RMinus K m b c ≃* X :=
    (rMinusEquivStatedOmega K m b c).trans eProj
  let ψ' : L' →* X := e.toMonoidHom.comp ψ
  have hψ' : Function.Surjective ψ' := e.surjective.comp hψ
  have hker' : ψ'.ker ≤ Subgroup.center L' := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact e.injective (hx.trans (map_one e).symm)
  haveI : Group.IsPerfect L' := ⟨hperf⟩
  let φ : CFSG.RankThree.PerfectCover.hopfMultiplier X →* ψ'.ker :=
    CFSG.RankThree.PerfectCover.hopfMultiplierToKer ψ' hψ' hker'
  have hφ : Function.Surjective φ :=
    CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective ψ' hψ' hker'
  haveI : Subsingleton ψ'.ker := hφ.subsingleton
  have hbot' : ψ'.ker = ⊥ := Subgroup.eq_bot_of_subsingleton _
  exact fun x y hxy => (MonoidHom.ker_eq_bot_iff ψ').mp hbot' (by
    change e (ψ x) = e (ψ y)
    rw [hxy])

end CFSG.StandardType

end
