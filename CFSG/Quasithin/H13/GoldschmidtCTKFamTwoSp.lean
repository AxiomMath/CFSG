module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoClass
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFourModel
public import CFSG.Quasithin.H13.GoldschmidtCTKFamImg

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
open scoped commutatorElement

variable {K : Type} [Field K]

theorem lam_mul_tauS [CharP K 2] (a b c d : K) :
    lam a * tauS b c d = tauS (b + a ^ 2 * d) (c + a * d) d * lam a :=
  mul_inv_eq_iff_eq_mul.mp (lam_mul_tauS_mul_inv a b c d)

theorem tauS_lam_mul_tauS_lam [CharP K 2] (b c d a b' c' d' a' : K) :
    (tauS b c d * lam a) * (tauS b' c' d' * lam a') =
      tauS (b + (b' + a ^ 2 * d')) (c + (c' + a * d')) (d + d') * lam (a + a') := by
  calc (tauS b c d * lam a) * (tauS b' c' d' * lam a')
      = tauS b c d * (lam a * tauS b' c' d') * lam a' := by group
    _ = tauS b c d * (tauS (b' + a ^ 2 * d') (c' + a * d') d' * lam a) * lam a' := by
      rw [lam_mul_tauS]
    _ = (tauS b c d * tauS (b' + a ^ 2 * d') (c' + a * d') d') * (lam a * lam a') := by group
    _ = _ := by rw [tauS_mul_tauS, lam_mul]

theorem commutator_tauS_lam [CharP K 2] (b c d a b' c' d' a' : K) :
    ⁅tauS b c d * lam a, tauS b' c' d' * lam a'⁆ =
      tauS (a ^ 2 * d' - a' ^ 2 * d) (a * d' - a' * d) 0 := by
  have h : (tauS b c d * lam a) * (tauS b' c' d' * lam a') =
      tauS (a ^ 2 * d' - a' ^ 2 * d) (a * d' - a' * d) 0 *
        ((tauS b' c' d' * lam a') * (tauS b c d * lam a)) := by
    rw [tauS_lam_mul_tauS_lam, tauS_lam_mul_tauS_lam, ← mul_assoc, tauS_mul_tauS]
    have e1 : a ^ 2 * d' - a' ^ 2 * d + (b' + (b + a' ^ 2 * d)) = b + (b' + a ^ 2 * d') := by ring
    have e2 : a * d' - a' * d + (c' + (c + a' * d)) = c + (c' + a * d') := by ring
    have e3 : (0 : K) + (d' + d) = d + d' := by ring
    rw [e1, e2, e3, add_comm a' a]
  rw [commutatorElement_def]
  calc tauS b c d * lam a * (tauS b' c' d' * lam a') * (tauS b c d * lam a)⁻¹ *
        (tauS b' c' d' * lam a')⁻¹
      = ((tauS b c d * lam a) * (tauS b' c' d' * lam a')) *
          ((tauS b' c' d' * lam a') * (tauS b c d * lam a))⁻¹ := by group
    _ = _ := by rw [h]; group

theorem unipotent_class_two [CharP K 2] {x y z : StatedSp 2 K} (hx : x ∈ unipotent 2 K)
    (hy : y ∈ unipotent 2 K) (hz : z ∈ unipotent 2 K) : ⁅⁅x, y⁆, z⁆ = 1 := by
  obtain ⟨C, hC, a, rfl⟩ := mem_unipotent_iff.1 hx
  obtain ⟨C', hC', a', rfl⟩ := mem_unipotent_iff.1 hy
  rw [tau_eq_tauS hC, tau_eq_tauS hC', commutator_tauS_lam, commutatorElement_eq_one_iff_mul_comm]
  exact tauS_zero_mul_comm hz _ _

theorem twoGroupsClassTwo_statedSp [Finite K] [CharP K 2] :
    TwoGroupsClassTwo (StatedSp 2 K) := by
  obtain ⟨-, ⟨Q, hQ⟩, -⟩ := unique_symplectic_four_Sylow_center (K := K) (Nat.card K) rfl
  refine TwoGroupsClassTwo.of_sylow Q fun x hx y hy z hz => ?_
  rw [hQ] at hx hy hz
  exact unipotent_class_two hx hy hz

theorem exclA5BlockFor_two_sp :
    ExclA5BlockFor fun S _ =>
      ∃ f : ℕ, 2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSp 2 2 f := by
  refine ExclA5BlockFor.of_not_config fun S _ _ hS hc => ?_
  obtain ⟨f, -, ⟨-, hf, -⟩, K, _, hfin, hcard, ⟨e⟩⟩ := hS
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
  exact hc.false_of_classTwo
    (twoGroupsClassTwo_statedSp.of_mulEquiv (e.trans ((QuotientGroup.quotientMulEquivOfEq
      (statedScalars_subgroupOf_eq_bot 2)).trans QuotientGroup.quotientBot)))

end CFSG.Quasithin.H13.CTK
