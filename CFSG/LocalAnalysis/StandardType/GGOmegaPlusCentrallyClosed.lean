module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly
open CFSG.LieType.Steinberg.CentralExt
open CFSG.LieType.Universal.Spin

@[expose] noncomputable def rPlusEquivStatedOmega (K : Type) [Field K] [CharP K 2] (m : ℕ)
    [NeZero m] : OrthRest.RPlus K m ≃* StatedOmega (StatedQuadPlus m K) := by
  have hbot : (LargeEvenScalars (Fin m ⊕ Fin m) K).subgroupOf
      (LargeEvenOmega (LargeEvenQPlus K m)) = ⊥ := by
    refine TableBOrth.scalars_subgroupOf_omega_eq_bot (Q := LargeEvenQPlus K m)
      (v₀ := Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) (fun x v => ?_) ?_
    · change StatedQuadPlus m K (x • v) = x ^ 2 * StatedQuadPlus m K v
      rw [← coe_quadPlus, QuadraticMap.map_smul, smul_eq_mul, sq]
    · change StatedQuadPlus m K _ ≠ 0
      rw [← coe_quadPlus, quadPlus_apply]
      simp [Pi.single_apply]
  exact (TableBOrth.projMkEquiv hbot).symm

theorem rPlus_injective_of_cover {K : Type} [Field K] [Finite K] {f m : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 3 ≤ m) (L' : Type) [Group L'] [Finite L']
    (ψ : L' →* OrthRest.RPlus K m) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) : Function.Injective ψ := by
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨hbij, -⟩ := OrthRest.spinPlus_bij (K := K) hm
  let e : spinGroup (quadPlus m K) ≃* OrthRest.RPlus K m := MulEquiv.ofBijective _ hbij
  let ψ' : L' →* spinGroup (quadPlus m K) := e.symm.toMonoidHom.comp ψ
  have hψ' : Function.Surjective ψ' := e.symm.surjective.comp hψ
  have hker' : ψ'.ker ≤ Subgroup.center L' := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact e.symm.injective (hx.trans (map_one e.symm).symm)
  obtain ⟨σ, hσ⟩ := SpinPlusClosed.spinPlus_exists_section_of_central hm h4 hψ' hker'
  haveI : Group.IsPerfect L' := ⟨hperf⟩
  have hbot : ψ'.ker = ⊥ := SL2Closed.ker_eq_bot_of_section ψ' hker' σ hσ
  exact fun x y hxy => (MonoidHom.ker_eq_bot_iff ψ').mp hbot (by
    change e.symm (ψ x) = e.symm (ψ y)
    rw [hxy])

end CFSG.StandardType

end
