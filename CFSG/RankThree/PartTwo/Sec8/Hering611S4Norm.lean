module

public import CFSG.RankThree.PartTwo.KFacts.K426RestMcL
public import CFSG.RankThree.PartTwo.Sec8.Hering611S4V0

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

open Subgroup CFSG CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.RankThree.PartTwo.KFacts.K426
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest (evalW)
open scoped commutatorElement

variable {Rg : ℕ → Gp}

theorem finish_case {c s : Gp} (hcP : c ∈ j3P) (hs : c * s = Rg r_uu * c)
    (hx : c * Rg r_x0 = Rg r_x0 * c ∨ c * Rg r_x0 = Rg r_x0 * Rg r_x0 * c)
    (hx3 : Rg r_x0 ^ 3 = 1) :
    ∃ c ∈ j3P, c * s * c⁻¹ = Rg r_uu ∧
      (c * Rg r_x0 * c⁻¹ = Rg r_x0 ∨ c * Rg r_x0 * c⁻¹ = (Rg r_x0)⁻¹) := by
  refine ⟨c, hcP, by rw [hs]; group, ?_⟩
  rcases hx with hx | hx
  · left
    rw [hx]
    group
  · right
    have h3 : Rg r_x0 * Rg r_x0 * Rg r_x0 = 1 := by rw [← pow_two, ← pow_succ]; exact hx3
    have : Rg r_x0 * Rg r_x0 = (Rg r_x0)⁻¹ := eq_inv_of_mul_eq_one_left h3
    rw [hx, mul_inv_cancel_right, this]

theorem S_conj (hR : Reg Rg) {s : Gp} (hs : s ∈ Ksub Rg gens_S) (hs1 : s ≠ 1) :
    ∃ c ∈ j3P, c * s * c⁻¹ = Rg r_uu ∧
      (c * Rg r_x0 * c⁻¹ = Rg r_x0 ∨ c * Rg r_x0 * c⁻¹ = (Rg r_x0)⁻¹) := by
  have hS : Ksub Rg gens_S = closure ({Rg r_uu, Rg r_vv} : Set Gp) := by
    rw [Ksub]
    congr 1
    ext x
    simp [gens_S, eq_comm]
  rw [hS] at hs
  obtain ⟨a, b, ha, hb, rfl⟩ := mem_closure_pair_pow (commute_of_prod hR.comm_uu_vv)
    (pow_of_ord hR.ord_uu) (pow_of_ord hR.ord_vv) hs
  have hx3 : Rg r_x0 ^ 3 = 1 := pow_of_ord hR.ord_x0
  interval_cases a <;> interval_cases b
  · exact absurd (by simp) hs1
  · exact finish_case (by simpa using hR.gpi1_P) (by simpa [prodG, mul_assoc] using hR.gpi1_s)
      (Or.inr (by simpa [prodG, mul_assoc] using hR.gpi1_x0)) hx3
  · exact finish_case (by simpa using hR.gpi5_P)
      (by simpa [prodG, pow_two, mul_assoc] using hR.gpi5_s)
      (Or.inr (by simpa [prodG, mul_assoc] using hR.gpi5_x0)) hx3
  · exact ⟨1, one_mem _, by simp, Or.inl (by simp)⟩
  · exact finish_case (by simpa using hR.gpi2_P) (by simpa [prodG, mul_assoc] using hR.gpi2_s)
      (Or.inl (by simpa [prodG, mul_assoc] using hR.gpi2_x0)) hx3
  · exact finish_case (by simpa using hR.gpi3_P)
      (by simpa [prodG, pow_two, mul_assoc] using hR.gpi3_s)
      (Or.inr (by simpa [prodG, mul_assoc] using hR.gpi3_x0)) hx3
  · exact finish_case (by simpa using hR.gpi4_P)
      (by simpa [prodG, pow_two, mul_assoc] using hR.gpi4_s)
      (Or.inl (by simpa [prodG, mul_assoc] using hR.gpi4_x0)) hx3
  · exact finish_case (by simpa using hR.gpi7_P)
      (by simpa [prodG, pow_two, mul_assoc] using hR.gpi7_s)
      (Or.inr (by simpa [prodG, mul_assoc] using hR.gpi7_x0)) hx3
  · exact finish_case (by simpa using hR.gpi6_P)
      (by simpa [prodG, pow_two, mul_assoc] using hR.gpi6_s)
      (Or.inl (by simpa [prodG, mul_assoc] using hR.gpi6_x0)) hx3

theorem evalW_mem_range_closure {m : ℕ} {G : Type*} [Group G] (g : Fin m → G)
    (w : List (Fin m × Bool)) : evalW g w ∈ closure (Set.range g) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons x w ih =>
    have : evalW g (x :: w) = (cond x.2 (g x.1) (g x.1)⁻¹) * evalW g w := by
      simp [CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW]
    rw [this]
    refine Subgroup.mul_mem _ ?_ ih
    cases x.2
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨x.1, rfl⟩)
    · exact Subgroup.subset_closure ⟨x.1, rfl⟩

theorem reduce_to_D
    {kb ab : Gp} (hkb : kb ∈ j3P) (hk3 : orderOf kb = 3)
    (Pb : Subgroup Gp) [hperf : Group.IsPerfect Pb] (hPb : Pb ≤ centralizer {kb} ⊓ j3P)
    (hab : ab ∈ Pb) (h360 : 360 ∣ Nat.card Pb) :
    ∃ k ∈ j3P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ kb = k * j3tXA ^ e * k⁻¹ ∧
      k⁻¹ * ab * k ∈ closure (Set.range j3tD) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk, z, hz, e, he, hkbeq⟩ := j3t_fusion hkb hk3
  set P₁ := Pb.map (MulAut.conj k⁻¹).toMonoidHom with hP₁def
  have hperf₁ : Group.IsPerfect P₁ := Group.IsPerfect.map _
  have hz3 : z ^ 3 = 1 := by
    rcases hz with rfl | rfl <;> exact (j3tReps_spec (by norm_num)).2
  have hP₁C : P₁ ≤ centralizer {z} ⊓ j3P := by
    rintro _ ⟨q, hq, rfl⟩
    refine mem_inf.2 ⟨?_, ?_⟩
    · have hqkb : q * kb = kb * q := mem_centralizer_singleton_iff.1 (hPb hq).1
      have hce : (MulAut.conj k⁻¹ q) * z ^ e = z ^ e * (MulAut.conj k⁻¹ q) := by
        rw [MulAut.conj_apply, inv_inv]
        rw [hkbeq] at hqkb
        calc k⁻¹ * q * k * z ^ e = k⁻¹ * (q * (k * z ^ e * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * z ^ e * k⁻¹) * q) * k := by rw [hqkb]
          _ = z ^ e * (k⁻¹ * q * k) := by group
      rw [← CFSG.RankThree.PartTwo.KFacts.K426Rest.centralizer_pow_eq hz3 he]
      exact mem_centralizer_singleton_iff.2 hce
    · exact j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hk) (hPb hq).2) (by simpa using hk)
  have hab' : k⁻¹ * ab * k ∈ P₁ := ⟨ab, hab, by simp [MulAut.conj_apply]⟩
  rcases hz with rfl | rfl
  · refine ⟨k, hk, e, he, hkbeq, ?_⟩
    have hPD : P₁ ≤ closure (Set.range j3tD) :=
      (le_commutator_of_isPerfect hP₁C).trans j3t_derived.1
    exact hPD hab'
  · exfalso
    have hbot : P₁ = ⊥ := eq_bot_of_isPerfect_of_isPGroup (isPGroup_j3t_caseB.to_le hP₁C)
    have hcard : Nat.card Pb = 1 := by
      have h1 : Nat.card P₁ = Nat.card Pb :=
        card_map_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom) (MulAut.conj k⁻¹).injective
      rw [← h1, hbot, card_bot]
    rw [hcard] at h360
    omega

theorem sylow_D
    (hR : Reg Rg) {y : Gp} (hy : y ∈ closure (Set.range j3tD))
    (hy3 : orderOf y = 3) : ∃ d ∈ closure (Set.range j3tD), d * y * d⁻¹ ∈ Ksub Rg gens_S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSD : Ksub Rg gens_S ≤ closure (Set.range j3tD) := by
    refine Ksub_le fun r hr => ?_
    simp only [gens_S, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hR.init_uu]; exact evalW_mem_range_closure _ _
    · rw [hR.init_vv]; exact evalW_mem_range_closure _ _
  have hfac : (Nat.card (closure (Set.range j3tD))).factorization 3 = 2 := by
    rw [j3t_derived.2, show (360 : ℕ) = 3 ^ 2 * 40 by norm_num]
    exact CFSG.RankThree.PartOne.factorization_pow_mulG Nat.prime_three (by norm_num)
  have hS9 : Nat.card (Ksub Rg gens_S) =
      3 ^ (Nat.card (closure (Set.range j3tD))).factorization 3 := by
    rw [hR.card_S, hfac]
    norm_num
  obtain ⟨x, hx, hxS⟩ := exists_conj_mem_of_card_prime 3 hSD hS9 hy hy3
  refine ⟨x⁻¹, (closure (Set.range j3tD)).inv_mem hx, ?_⟩
  simpa using hxS

theorem D_le
    (hR : Reg Rg) :
    closure (Set.range j3tD) ≤ j3P ⊓ centralizer {Rg r_x0} := by
  have e0 : j3tD 0 = Rg r_d1 := hR.init_d1.symm
  have e1 : j3tD 1 = Rg r_d2 := hR.init_d2.symm
  rw [closure_le]
  rintro _ ⟨i, rfl⟩
  refine ⟨j3tD_mem i, ?_⟩
  show j3tD i ∈ centralizer {Rg r_x0}
  rw [mem_centralizer_singleton_iff]
  fin_cases i
  · show j3tD 0 * Rg r_x0 = Rg r_x0 * j3tD 0
    rw [e0]
    exact (commute_of_prod hR.d1_x0).eq
  · show j3tD 1 * Rg r_x0 = Rg r_x0 * j3tD 1
    rw [e1]
    exact (commute_of_prod hR.d2_x0).eq

theorem normal_form
    (hR : Reg Rg) {kb ab : Gp} (hkb : kb ∈ j3P)
    (hk3 : orderOf kb = 3) (ha3 : orderOf ab = 3) (Pb : Subgroup Gp)
    [hperf : Group.IsPerfect Pb] (hPb : Pb ≤ centralizer {kb} ⊓ j3P) (hab : ab ∈ Pb)
    (h360 : 360 ∣ Nat.card Pb) :
    ∃ c ∈ j3P, (c * kb * c⁻¹ = Rg r_x0 ∨ c * kb * c⁻¹ = (Rg r_x0)⁻¹) ∧
      c * ab * c⁻¹ = Rg r_uu := by
  obtain ⟨k, hk, e, he, hkbeq, hab'D⟩ := reduce_to_D hkb hk3 Pb hPb hab h360
  have hab'3 : orderOf (k⁻¹ * ab * k) = 3 := by
    have h := orderOf_injective (MulAut.conj k⁻¹).toMonoidHom (MulAut.conj k⁻¹).injective ab
    simpa [MulAut.conj_apply, ha3] using h
  obtain ⟨d, hdD, hdS⟩ := sylow_D hR hab'D hab'3
  have hs1 : d * (k⁻¹ * ab * k) * d⁻¹ ≠ 1 := by
    intro h
    have h1 : k⁻¹ * ab * k = 1 := by
      have : d * (k⁻¹ * ab * k) = d := mul_inv_eq_one.1 h
      simpa using this
    rw [h1, orderOf_one] at hab'3
    exact absurd hab'3 (by norm_num)
  obtain ⟨c, hcP, hcs, hcx⟩ := S_conj hR hdS hs1
  obtain ⟨hdP, hdC⟩ := D_le hR hdD
  have hdx : d * Rg r_x0 = Rg r_x0 * d := mem_centralizer_singleton_iff.1 hdC
  have hx3 : Rg r_x0 ^ 3 = 1 := pow_of_ord hR.ord_x0
  have hx2 : Rg r_x0 ^ 2 = (Rg r_x0)⁻¹ :=
    inv_eq_of_mul_eq_one_left (by rw [← pow_succ]; exact hx3) |>.symm
  refine ⟨c * d * k⁻¹, j3P.mul_mem (j3P.mul_mem hcP hdP) (j3P.inv_mem hk), ?_, ?_⟩
  · have step : (c * d * k⁻¹) * kb * (c * d * k⁻¹)⁻¹ = (c * Rg r_x0 * c⁻¹) ^ e := by
      rw [conj_pow, hkbeq, ← hR.init_x0]
      have hde : d * Rg r_x0 ^ e = Rg r_x0 ^ e * d := (Commute.pow_right hdx e).eq
      calc c * d * k⁻¹ * (k * Rg r_x0 ^ e * k⁻¹) * (c * d * k⁻¹)⁻¹
          = c * (d * Rg r_x0 ^ e) * d⁻¹ * c⁻¹ := by group
        _ = c * Rg r_x0 ^ e * c⁻¹ := by rw [hde]; group
    rw [step]
    rcases hcx with h | h <;> rcases he with rfl | rfl
    · left; rw [h, pow_one]
    · right; rw [h, hx2]
    · right; rw [h, pow_one]
    · left; rw [h, inv_pow, hx2, inv_inv]
  · calc c * d * k⁻¹ * ab * (c * d * k⁻¹)⁻¹ = c * (d * (k⁻¹ * ab * k) * d⁻¹) * c⁻¹ := by group
      _ = Rg r_uu := hcs

end CFSG.RankThree.PartTwo.Sec8.Hering611.J3T
