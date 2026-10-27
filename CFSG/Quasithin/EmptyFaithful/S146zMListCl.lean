module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven CFSG.QuasithinUnique.Vol2Native.EvenWit Matrix

section Proj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem three_dvd_card_statedProj {H : Subgroup (GL ι K)} {x : GL ι K} (hxH : x ∈ H)
    (hx3 : x ^ 3 = 1) (hx1 : x ∉ StatedScalars ι K) : 3 ∣ Nat.card (StatedProj H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : H →* StatedProj H := QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)
  have hpow : π ⟨x, hxH⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxH⟩ : H) ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hx3)
    rw [this, map_one]
  have hne : π ⟨x, hxH⟩ ≠ 1 := by
    intro h
    have : (⟨x, hxH⟩ : H) ∈ (StatedScalars ι K).subgroupOf H := (QuotientGroup.eq_one_iff _).mp h
    exact hx1 (Subgroup.mem_subgroupOf.mp this)
  have := orderOf_eq_prime hpow hne
  exact this ▸ orderOf_dvd_natCard _

theorem rotGL_not_mem_scalars {i j : ι} (hij : i ≠ j) : rotGL (K := K) i j ∉ StatedScalars ι K :=
  fun hx => mul_scalar_ne (g := 1) hij (one_mulVec _) (rotMatrix_mulVec_left _ _) hx (one_mul _)

end Proj

section Models

variable {K : Type} [Field K]

theorem three_dvd_card_psl {n : ℕ} (hn : 2 ≤ n) : 3 ∣ Nat.card (StatedProj (StatedSL n K)) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := fun h => by simpa [i, j] using congrArg Fin.val h
  exact three_dvd_card_statedProj (x := rotGL i j) (Subgroup.subset_closure (det_rotMatrix _ _))
    (rotGL_pow_three _ _) (rotGL_not_mem_scalars hij)

theorem three_dvd_card_psp {n : ℕ} (hn : 1 ≤ n) : 3 ∣ Nat.card (StatedProj (StatedSp n K)) := by
  let i : Fin n := ⟨0, by omega⟩
  exact three_dvd_card_statedProj (x := rotGL (.inl i) (.inr i))
    (Subgroup.subset_closure (rotMatrix_inl_inr_symplectic _)) (rotGL_pow_three _ _)
    (rotGL_not_mem_scalars Sum.inl_ne_inr)

theorem cycGL_pow_three : cycGL K ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_cycGL, Units.val_one]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cycMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem cycGL_not_mem_scalars : cycGL K ∉ StatedScalars (Fin 3) K := by
  intro hx
  refine mul_scalar_ne (g := 1) (a := (0 : Fin 3)) (b := (1 : Fin 3)) (by decide)
    (one_mulVec _) ?_ hx (one_mul _)
  rw [coe_cycGL]
  ext a
  fin_cases a <;> simp [cycMat, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem three_dvd_card_psu_three {q : ℕ} (hq : q ≠ 0) :
    3 ∣ Nat.card (StatedProj (StatedSU 3 q K)) :=
  three_dvd_card_statedProj (cycGL_mem_SU K hq) cycGL_pow_three cycGL_not_mem_scalars

theorem three_dvd_card_psl_model {S : Type} [Group S] {n p f : ℕ}
    (hm : StatedClassicalModel S .PSL n p f) : 3 ∣ Nat.card S := by
  obtain ⟨⟨-, -, hn, -⟩, K, _, _, -, ⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv]
  exact three_dvd_card_psl hn

theorem three_dvd_card_psp_model {S : Type} [Group S] {n p f : ℕ}
    (hm : StatedClassicalModel S .PSp n p f) : 3 ∣ Nat.card S := by
  obtain ⟨⟨-, -, hn, -⟩, K, _, _, -, ⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv]
  exact three_dvd_card_psp (by omega)

theorem three_dvd_card_psu_three_model {S : Type} [Group S] {p f : ℕ}
    (hm : StatedClassicalModel S .PSU 3 p f) : 3 ∣ Nat.card S := by
  obtain ⟨⟨hp, -, -⟩, K, _, _, -, ⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv]
  exact three_dvd_card_psu_three (pow_ne_zero _ hp.ne_zero)

end Models

end CFSG.Quasithin
