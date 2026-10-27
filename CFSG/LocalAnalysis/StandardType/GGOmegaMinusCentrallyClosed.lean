module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed

public section

namespace CFSG.StandardType

open CFSG.LieType.Steinberg.CentralExt
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

theorem rMinus_injective_of_cover
    {K : Type} [Field K] [Finite K] {f m : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 3 ≤ m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (L' : Type) [Group L'] [Finite L']
    (ψ : L' →* OrthRest.RMinus K m b c) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) : Function.Injective ψ := by
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨hbij, -⟩ := OrthRest.spinMinus_bij (K := K) (n := m + 1) (by omega) hbc
  let e : spinGroup (quadMinus (m + 1) K b c) ≃* OrthRest.RMinus K m b c :=
    (MulEquiv.ofBijective _ hbij).trans (omegaMinusProjEquiv (m + 1) b c).symm
  let ψ' : L' →* spinGroup (quadMinus (m + 1) K b c) := e.symm.toMonoidHom.comp ψ
  have hψ' : Function.Surjective ψ' := e.symm.surjective.comp hψ
  have hker' : ψ'.ker ≤ Subgroup.center L' := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact e.symm.injective (hx.trans (map_one e.symm).symm)
  obtain ⟨σ, hσ⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_exists_section_of_central
      hbc (by omega) h4 hψ' hker'
  haveI : Group.IsPerfect L' := ⟨hperf⟩
  have hbot : ψ'.ker = ⊥ := SL2Closed.ker_eq_bot_of_section ψ' hker' σ hσ
  exact fun x y hxy => (MonoidHom.ker_eq_bot_iff ψ').mp hbot (by
    change e.symm (ψ x) = e.symm (ψ y)
    rw [hxy])

end CFSG.StandardType
