module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylData
import CFSG.LocalAnalysis.StandardType.GGTriD4LineComponent
import CFSG.LieType.BorelTits.LeviOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

private lemma triD4LineArith_commutatorElement_prod {M N : Type*} [Group M] [Group N]
    (a₁ a₂ : M) (b₁ b₂ : N) :
    ⁅(a₁, b₁), (a₂, b₂)⁆ = (⁅a₁, a₂⁆, ⁅b₁, b₂⁆) := by
  rw [commutatorElement_def, commutatorElement_def]
  rfl

private lemma triD4LineArith_commutator_mem_N0 (k K : Type) [Field k] [Field K] [Algebra k K]
    (x y : TriD4LineX k K) : ⁅x, y⁆ ∈ triD4LineN0 k K := by
  obtain ⟨g, c, h, rfl⟩ := triD4LineMk_surjective k K x
  obtain ⟨g', c', h', rfl⟩ := triD4LineMk_surjective k K y
  let a : triD4LineFibre k K := ⟨(g, c), h⟩
  let b : triD4LineFibre k K := ⟨(g', c'), h'⟩
  have ha : triD4LineMk k K g c h = QuotientGroup.mk' (triD4LineDiag k K) a := rfl
  have hb : triD4LineMk k K g' c' h' = QuotientGroup.mk' (triD4LineDiag k K) b := rfl
  rw [ha, hb, ← map_commutatorElement]
  have hcomm : ((⁅a, b⁆ : triD4LineFibre k K) : GL (Fin 3) k × Kˣ) = (⁅g, g'⁆, 1) := by
    have h1 : ((⁅a, b⁆ : triD4LineFibre k K) : GL (Fin 3) k × Kˣ) =
        ⁅(a : GL (Fin 3) k × Kˣ), (b : GL (Fin 3) k × Kˣ)⁆ :=
      map_commutatorElement (Subgroup.subtype (triD4LineFibre k K)) a b
    rw [h1]
    have hca : (a : GL (Fin 3) k × Kˣ) = (g, c) := rfl
    have hcb : (b : GL (Fin 3) k × Kˣ) = (g', c') := rfl
    rw [hca, hcb, triD4LineArith_commutatorElement_prod]
    have hcc : ⁅c, c'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (mul_comm c c')
    simp only [hcc, Prod.mk.injEq, true_and]
  have hdet : Matrix.GeneralLinearGroup.det ⁅g, g'⁆ =
      Units.map (Algebra.norm k (S := K)) 1 := by
    have hmem := (⁅a, b⁆ : triD4LineFibre k K).2
    rw [hcomm] at hmem
    exact hmem
  have hab : ⁅a, b⁆ = ⟨(⁅g, g'⁆, 1), hdet⟩ := Subtype.ext hcomm
  rw [hab]
  exact (mem_triD4LineN0_iff k K _).2 ⟨⁅g, g'⁆, hdet, rfl⟩

private lemma triD4LineArith_perfect_of_isQuasisimple {X : Type*} [Group X] {J : Subgroup X}
    (h : Assembly.IsQuasisimple ↥J) : ⁅J, J⁆ = J := by
  have hmap : (commutator ↥J).map J.subtype = ⁅J, J⁆ := by
    unfold commutator
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have htop : (commutator ↥J).map J.subtype = J := by
    rw [h.1, Subgroup.map_top, Subgroup.range_subtype]
  rwa [hmap] at htop

private lemma triD4LineArith_commutator_eq_N0 (k K : Type) [Field k] [Field K] [Algebra k K] :
    commutator (TriD4LineX k K) = triD4LineN0 k K := by
  refine le_antisymm ?_ ?_
  · unfold commutator
    exact Subgroup.commutator_le.2 fun x _ y _ => triD4LineArith_commutator_mem_N0 k K x y
  · have hq : Assembly.IsQuasisimple ↥(triD4LineN0 k K) :=
      ((triD4LineN0_unique_component k K (triD4LineN0 k K)).2 rfl).2.2
    rw [← triD4LineArith_perfect_of_isQuasisimple hq]
    exact Subgroup.commutator_mono le_top le_top

private lemma triD4LineArith_card_commutator (k K : Type) [Field k] [Field K] [Algebra k K] :
    Nat.card (commutator (TriD4LineX k K)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) k) := by
  rw [triD4LineArith_commutator_eq_N0 k K]
  let e : Matrix.SpecialLinearGroup (Fin 3) k ≃* ↥(triD4LineN0 k K) :=
    (MonoidHom.ofInjective (triD4LineSL3_injective k K)).trans
      (MulEquiv.subgroupCongr (triD4LineSL3_range k K))
  exact (Nat.card_congr e.toEquiv).symm

private lemma triD4LineArith_not_dvd_pow (q : ℕ) (hq : 4 ≤ q) :
    ¬ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ∣ q ^ 3 * (q ^ 6 - 1) := by
  intro h
  have hq_le_q3 : q ≤ q ^ 3 := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < q) (by norm_num : 1 ≤ 3)
  have hq3 : 0 < q ^ 3 := lt_of_lt_of_le (by omega : 0 < q) hq_le_q3
  have hq31 : 0 < q ^ 3 - 1 := by omega
  have h61 : q ^ 6 - 1 = (q ^ 3 + 1) * (q ^ 3 - 1) := by
    have hsq : (q ^ 3) ^ 2 - 1 = (q ^ 3 + 1) * (q ^ 3 - 1) := by
      simpa using Nat.sq_sub_sq (q ^ 3) 1
    have hpow : q ^ 6 = (q ^ 3) ^ 2 := by rw [← pow_mul]
    rwa [hpow]
  rw [show q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) =
      q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) by ac_rfl, h61] at h
  have h3 : q ^ 3 * ((q ^ 3 - 1) * (q ^ 2 - 1)) ∣
      q ^ 3 * ((q ^ 3 - 1) * (q ^ 3 + 1)) := by
    have h' := h
    rw [show q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) =
        q ^ 3 * ((q ^ 3 - 1) * (q ^ 2 - 1)) by ac_rfl,
      show q ^ 3 * ((q ^ 3 + 1) * (q ^ 3 - 1)) =
        q ^ 3 * ((q ^ 3 - 1) * (q ^ 3 + 1)) by ac_rfl] at h'
    exact h'
  have h2 : (q ^ 3 - 1) * (q ^ 2 - 1) ∣ (q ^ 3 - 1) * (q ^ 3 + 1) :=
    Nat.dvd_of_mul_dvd_mul_left hq3 h3
  have h4 : q ^ 2 - 1 ∣ q ^ 3 + 1 := Nat.dvd_of_mul_dvd_mul_left hq31 h2
  have h5 : q ^ 2 - 1 ∣ q + 1 := by
    have hmul : q * (q ^ 2 - 1) = q ^ 3 - q := by
      rw [Nat.mul_sub_left_distrib, mul_one, show q * q ^ 2 = q ^ 3 by ring]
    have hdecomp : q * (q ^ 2 - 1) + (q + 1) = q ^ 3 + 1 := by
      rw [hmul]
      omega
    have hd : q ^ 2 - 1 ∣ q * (q ^ 2 - 1) := dvd_mul_left _ _
    have h4' : q ^ 2 - 1 ∣ q * (q ^ 2 - 1) + (q + 1) := by rw [hdecomp]; exact h4
    exact (Nat.dvd_add_iff_right hd).2 h4'
  have hle : q ^ 2 - 1 ≤ q + 1 := Nat.le_of_dvd (by omega : 0 < q + 1) h5
  have hlt : q + 1 < q ^ 2 - 1 := by
    have hsq : q + 3 ≤ q ^ 2 := by nlinarith [hq]
    omega
  omega

private lemma triD4LineArith_not_dvd_mul {c q : ℕ} (hc : c = q ^ 3) (hq : 4 ≤ q) :
    ¬ c * (q ^ 2 - 1) * (q ^ 3 - 1) ∣ c * (q ^ 6 - 1) := by
  rw [hc]
  exact triD4LineArith_not_dvd_pow q hq

theorem triD4Line_not_dvd_commutator {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (k : Type) [Field k] [Algebra k K]
    (hk : Nat.card k = 2 ^ n) (D : TriD4LineKGXData n K k) :
    ¬ Nat.card (commutator (Subgroup.centralizer {D.z₀})) ∣ (2 ^ n) ^ 3 * ((2 ^ n) ^ 6 - 1) := by
  intro h
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ (by norm_num))
  have hcard : Nat.card (commutator (Subgroup.centralizer {D.z₀})) =
      Nat.card (commutator (TriD4LineX k K)) := by
    have hmap : Subgroup.map D.Θ.toMonoidHom
        (commutator (Subgroup.centralizer {D.z₀})) = commutator (TriD4LineX k K) := by
      have h := Subgroup.map_commutator
        (⊤ : Subgroup ↥(Subgroup.centralizer {D.z₀})) ⊤ D.Θ.toMonoidHom
      have htop : D.Θ.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.2 D.Θ.surjective
      rw [Subgroup.map_top, htop] at h
      exact h
    rw [← hmap, Subgroup.card_map_of_injective D.Θ.injective]
  rw [hcard, triD4LineArith_card_commutator k K,
      CFSG.LieType.BorelTits.card_specialLinearGroup_fin_three (K := k) hk] at h
  rw [show (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) =
        Nat.card K * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) by rw [hK],
      show (2 ^ n) ^ 3 * ((2 ^ n) ^ 6 - 1) =
        Nat.card K * ((2 ^ n) ^ 6 - 1) by rw [hK]] at h
  exact triD4LineArith_not_dvd_mul hK
    (by simpa using Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) hn) h

end CFSG.StandardType
