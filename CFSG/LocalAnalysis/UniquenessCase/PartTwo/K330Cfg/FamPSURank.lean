module


import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubUR
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open Matrix CFSG.Open Subgroup
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Blueprint (LieModel)

private theorem k330c_exists_su2_prime_order {K : Type} [Field K] {p f : ℕ}
    (h : UnitaryFieldData p f K) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : r ∣ (p ^ f) ^ 2 - 1) :
    ∃ g : GL (Fin 2) K,
      CFSG.HardMathSupport.Timmesfeld.FieldBonus.IsSU2 (p ^ f)
        (g : Matrix (Fin 2) (Fin 2) K) ∧ g ^ r = 1 ∧
      ∀ c : Kˣ, (g : Matrix (Fin 2) (Fin 2) K) ≠ Matrix.scalar (Fin 2) (c : K) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Finite K := h.finite
  have hint :=
    CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h (n := 2) (by norm_num)
  rw [CFSG.GH74.GLS.Stage2.Final.ModelOrd.prod_Icc_two_two,
    show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one] at hint
  have h1 : 1 ≤ (p ^ f) ^ 2 := one_le_pow₀ (one_le_pow₀ h.prime.one_le)
  have hcard : Nat.card (StatedSU 2 (p ^ f) K) = p ^ f * ((p ^ f) ^ 2 - 1) := by
    apply Nat.cast_injective (R := ℤ)
    rw [hint]
    push_cast [Nat.cast_sub h1]
    ring
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := StatedSU 2 (p ^ f) K) r
    (by rw [hcard]; exact Dvd.dvd.mul_left hrq _)
  have hgr : g ^ r = 1 := hg ▸ pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg
    exact hr.one_lt.ne hg
  obtain ⟨hdet, hu⟩ := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).1 g.2
  have hgS : CFSG.HardMathSupport.Timmesfeld.FieldBonus.IsSU2 (p ^ f)
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    refine ⟨?_, hdet⟩
    have e : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map (· ^ p ^ f) =
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map h.bar := by
      ext i j
      simp [h.bar_apply]
    rw [e]
    exact hu
  refine ⟨(g : GL (Fin 2) K), hgS, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, hgr]
    rfl
  · intro c hc
    have hc2 : (c : K) ^ 2 = 1 := by
      have h' := congrArg Matrix.det hc
      rw [hdet] at h'
      simpa [Matrix.scalar_apply, Matrix.det_diagonal] using h'.symm
    have hc2u : c ^ 2 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact hc2
    have hcgl : (g : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 2) c :=
      Units.ext (by rw [GeneralLinearGroup.coe_scalar]; exact hc)
    have hg2 : ((g : GL (Fin 2) K)) ^ 2 = 1 := by
      rw [hcgl, ← map_pow, hc2u, map_one]
    have hord : orderOf ((g : StatedSU 2 (p ^ f) K) : GL (Fin 2) K) = r :=
      (Subgroup.orderOf_coe g).trans hg
    have hdvd2 : r ∣ 2 := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hg2
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hdvd2)

private theorem k330c_two_le_pRank_psu_of_dvd {X : Type} [Group X] [Finite X] {n p f : ℕ}
    (hn : 4 ≤ n) (hC : StatedClassicalModel X .PSU n p f) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrq : r ∣ (p ^ f) ^ 2 - 1) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  obtain ⟨⟨hp, hf, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ := hC
  letI : Field K := hfield
  letI : Finite K := hfinite
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨g, hgS, hgr, hns⟩ := k330c_exists_su2_prime_order h hr hr2 hrq
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
  exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.two_le_pRank_statedSU_of_su2_block
    hn (pow_ne_zero f hp.ne_zero) hgS hgr hns

theorem rank_PSU (n : ℕ) (hn : n = 4 ∨ n = 5) {J : Type} [Group J] [Finite J] {p f : ℕ}
    (e : LieModel J .PSU n p f) (hcase : p = 7 ∨ 7 ∣ (p ^ f) ^ 2 - 1) :
    2 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup J) := by
  have hn4 : 4 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hn3 : n ≠ 3 := by rcases hn with h | h <;> omega
  rcases hcase with hp7 | hdvd
  · subst hp7
    have hcl : StatedClassicalModel J .PSU n 7 f :=
      e.statedClassicalModel_of_ne_zero (by omega)
    obtain ⟨-, -, hr⟩ :=
      CFSG.SectionRank.classical_model_rank (t := .PSU) (p := 7) (by norm_num) hcl
    rcases hr with ⟨ht, -⟩ | ⟨-, hcases⟩ | ⟨ht, -⟩ | h4
    · exact absurd ht (by decide)
    · rcases hcases with ⟨hn3', -⟩ | h4
      · exact absurd hn3' hn3
      · omega
    · exact absurd ht (by decide)
    · omega
  · have hcl : StatedClassicalModel J .PSU n p f := e.statedClassicalModel_of_ne_zero (by omega)
    exact k330c_two_le_pRank_psu_of_dvd hn4 hcl Nat.prime_seven (by norm_num) hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
