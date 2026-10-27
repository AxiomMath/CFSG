module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSuzukiOddCore
public import CFSG.RankThree.PartOne.KD4L.TriStd
public import CFSG.RankThree.PartOne.KE.SuzukiPlane
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ComponentClassification.UnbalancedGS

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem sz_two_element_of_comm (hK : Nat.card K = 2 ^ (2 * a + 1)) {t : suzukiGroup a K}
    (ht : orderOf t = 2) {d : suzukiGroup a K} (hc : d * t = t * d) :
    ∃ k : ℕ, orderOf d = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := SuzukiOddCore.suzuki_involution_centralizer_sylow hK t ht
  have hd : d ∈ (S : Subgroup (suzukiGroup a K)) := by
    rw [hS]
    exact Subgroup.mem_centralizer_singleton_iff.2 hc
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 S.isPGroup') ⟨d, hd⟩
  exact ⟨k, by rw [← hk]; exact (Subgroup.orderOf_mk d hd).symm⟩

omit [Finite K] in
theorem suzukiS_zero_one :
    suzukiS a (0 : K) 1 = !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 1, 0, 1] := by
  have h1 : (0 : K) ^ 2 ^ (a + 1) = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  have h2 : (0 : K) ^ (2 ^ (a + 1) + 1) = 0 := zero_pow (Nat.succ_ne_zero _)
  have h3 : (0 : K) ^ (2 ^ (a + 1) + 2) = 0 := zero_pow (by positivity)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiS, suzukiN, h1, h2, h3]

theorem sz_noncomm_involutions [CharP K 2] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ t₁ t₂ : suzukiGroup a K, orderOf t₁ = 2 ∧ orderOf t₂ = 2 ∧ t₁ * t₂ ≠ t₂ * t₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (1 : K) + 1 = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa [one_add_one_eq_two] using this
  set t₁ : suzukiGroup a K := suzukiSElt a K 0 1 with ht₁
  have hsq : t₁ ^ 2 = 1 := by
    rw [pow_two, ht₁, suzukiSElt_mul hK, add_zero, zero_pow (pow_ne_zero _ two_ne_zero), zero_mul,
      add_zero, h2, suzukiSElt_zero_zero hK]
  have hne : t₁ ≠ 1 := by
    intro h
    rw [← suzukiSElt_zero_zero hK (a := a) (K := K)] at h
    exact one_ne_zero (suzukiSElt_inj.1 h).2
  have ho₁ : orderOf t₁ = 2 := orderOf_eq_prime hsq hne
  refine ⟨t₁, suzukiWElt a K * t₁ * (suzukiWElt a K)⁻¹, ho₁, ?_, ?_⟩
  · have := orderOf_injective (MulAut.conj (suzukiWElt a K)).toMonoidHom
      (MulAut.conj (suzukiWElt a K)).injective t₁
    simpa [MulAut.conj_apply, ho₁] using this
  · intro h
    rw [suzukiWElt_inv] at h
    have e := congrArg (fun g : suzukiGroup a K =>
      (((g : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) 0 1) h
    simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, ht₁, coe_suzukiSElt,
      coe_suzukiWElt, suzukiS_zero_one, Matrix.mul_apply, Fin.sum_univ_four] at e
    simp [suzukiW] at e

theorem sz_isQuasisimple [CharP K 2] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.IsQuasisimple (suzukiGroup a K) := by
  obtain ⟨t₁, t₂, -, -, h⟩ := sz_noncomm_involutions hK
  exact CFSG.RankThree.PartOne.KD4L.isQuasisimple_of_isSimpleGroup (suzuki_simple ha hK).2.2
    ⟨t₁, t₂, h⟩

theorem sz_lieModel [CharP K 2] {G : Type} [Group G] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : suzukiGroup a K ≃* G) {f : ℕ} (hf : f = 2 * a + 1) :
    LieModel (G ⧸ Subgroup.center G) .twistedB2 0 2 f := by
  have hS : Subgroup.center (suzukiGroup a K) = ⊥ := CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK
  have hZ : Subgroup.center G = ⊥ := by
    rw [← Subgroup.map_center_eq e, hS, Subgroup.map_bot]
  let e' : (G ⧸ Subgroup.center G) ≃* suzukiGroup a K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e.symm
  exact CFSG.RankThree.PartOne.Sec66T.lieModel_twistedB2_iff.mpr
    ⟨rfl, rfl, a, ha, K, inferInstance, inferInstance, hf, by rw [hK, hf], ⟨e'⟩⟩

end CFSG.RankThree.PartOne.TCX.Ree
