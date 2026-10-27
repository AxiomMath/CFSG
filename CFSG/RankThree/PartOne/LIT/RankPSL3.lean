module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartOne.LIT.RankProjective
import CFSG.RankThree.PartOne.LIT.RankMatrix
import CFSG.LocalAnalysis.SectionRank.OddCover.ThreeRank

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix Module CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.SectionRank.OddCover

theorem statedSL_eq_det_ker (n : ℕ) (K : Type) [Field K] :
    StatedSL n K = (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker :=
  CFSG.Open.StatedAPI.statedSL_eq_ker_det n K

@[expose] noncomputable def statedProjEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) : StatedProj H ≃* projImage H :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [StatedScalars, ← GeneralLinearGroup.center_eq_range_scalar])).trans (projEquiv H)

theorem factorization_six_mul_eq {x : ℕ} (hx : x ≠ 0) :
    (6 * x).factorization 3 = (3 * x).factorization 3 := by
  rw [show 6 * x = 2 * (3 * x) by ring, Nat.factorization_mul (by norm_num) (by positivity),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by norm_num), zero_add]

theorem scalar_injective {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Function.Injective (GeneralLinearGroup.scalar ι : Kˣ →* GL ι K) := by
  intro c c' h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have := congrFun (congrFun (congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h) i) i
  apply Units.ext
  simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this

theorem card_scalars_le {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {m : ℕ} (hm : 0 < m) (H : Subgroup (GL ι K))
    (h : ∀ g ∈ H, g ∈ Subgroup.center (GL ι K) → g ^ m = 1) :
    Nat.card ((Subgroup.center (GL ι K)).subgroupOf H) ≤ m := by
  set D := (Subgroup.center (GL ι K)).subgroupOf H
  have hle : D.map H.subtype ≤ (rootsOfUnity m K).map (GeneralLinearGroup.scalar ι) := by
    rintro _ ⟨d, hd, rfl⟩
    have hc := Subgroup.mem_subgroupOf.mp hd
    have hc' := hc
    rw [GeneralLinearGroup.center_eq_range_scalar] at hc'
    obtain ⟨c, hcd⟩ := hc'
    refine ⟨c, (mem_rootsOfUnity m c).mpr ?_, hcd⟩
    apply scalar_injective (ι := ι)
    rw [map_pow, map_one, hcd]
    exact h d.1 d.2 hc
  calc Nat.card D = Nat.card (D.map H.subtype) :=
        (Subgroup.card_map_of_injective H.subtype_injective).symm
    _ ≤ Nat.card ((rootsOfUnity m K).map (GeneralLinearGroup.scalar ι)) :=
        Subgroup.card_le_of_le hle
    _ = Nat.card (rootsOfUnity m K) := Subgroup.card_map_of_injective scalar_injective
    _ ≤ m := by
      have := NeZero.of_pos hm
      exact card_rootsOfUnity K m

theorem pRank_three_projSL_three_le {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f)
    (hD : Nat.card ((Subgroup.center (GL (Fin 3) K)).subgroupOf (StatedSL 3 K)) = 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (projImage (StatedSL 3 K))) ≤ 2 := by
  have hcen : StatedScalars (Fin 3) K = Subgroup.center (GL (Fin 3) K) := by
    rw [StatedScalars, ← GeneralLinearGroup.center_eq_range_scalar]
  have hD' : Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) = 3 := by
    rw [hcen]; exact hD
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_pow _ _ (by norm_num)
  have h3e : 3 ∣ 2 ^ f - 1 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3D : 3 ∣ Nat.card ((Subgroup.center (GL (Fin 3) K)).subgroupOf (StatedSL 3 K)) :=
      ⟨1, by rw [hD]⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
      (G := ((Subgroup.center (GL (Fin 3) K)).subgroupOf (StatedSL 3 K))) 3 h3D
    obtain ⟨c, hc⟩ : ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin 3) c = x.1.1 := by
      have hmem : (x.1.1 : GL (Fin 3) K) ∈ (GeneralLinearGroup.scalar (Fin 3)).range := by
        rw [← GeneralLinearGroup.center_eq_range_scalar]
        exact Subgroup.mem_subgroupOf.mp x.2
      exact hmem
    have hord : orderOf c = 3 := by
      rw [← hx, ← Subgroup.orderOf_coe x, ← Subgroup.orderOf_coe x.1, ← hc]
      exact (orderOf_injective _ scalar_injective c).symm
    have := orderOf_dvd_natCard c
    rw [hord, card_units_eq, hK] at this
    exact this
  have hcard : (Nat.card (StatedSL 3 K)).factorization 3 =
      (3 * Nat.card (⊤ : Subgroup Kˣ) ^ 2).factorization 3 := by
    have hM : Nat.card (⊤ : Subgroup Kˣ) = 2 ^ f - 1 := by
      rw [Subgroup.card_top, card_units_eq, hK]
    have hpos : 0 < 2 ^ f - 1 := by
      have : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega
    rw [card_statedSL_three, hK, hM, ← factorization_six_mul_eq (by positivity)]
    have e1 : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      zify [hq1, Nat.one_le_pow 2 _ hq1]; ring
    have e2 : (2 ^ f) ^ 3 - 1 = (2 ^ f - 1) * ((2 ^ f) ^ 2 + 2 ^ f + 1) := by
      zify [hq1, Nat.one_le_pow 3 _ hq1]; ring
    rw [e1, e2]
    have h3q : ¬ 3 ∣ 2 ^ f := fun h =>
      absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
    exact factorization_order_eq Nat.prime_three (by norm_num) (by positivity) (by omega)
      (by omega) (by positivity) h3q (by omega)
      (factorization_sq_add_add_one Nat.prime_three hq1 h3e)
  have h := three_pRank_statedProj_le_two monomialData_statedSL hcard hD'
  have := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
    (statedProjEquiv (StatedSL 3 K))
  rw [← this]
  exact h

theorem not_dvd_three {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) : ¬ r ∣ 3 := fun h =>
  hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h)

theorem pRank_projSL_three_le {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup (projSL 3 K)) ≤ 2 := by
  have : Fact r.Prime := ⟨hr⟩
  have hrK : (r : K) ≠ 0 := natCast_ne_zero_of_charTwo hr hr2
  have hH : ∀ h ∈ StatedSL 3 K, (h : Matrix (Fin 3) (Fin 3) K).det = 1 := fun h hh => by
    have := MonoidHom.mem_ker.mp ((statedSL_eq_det_ker 3 K) ▸ hh)
    simpa [Units.ext_iff] using this
  have hproj : projSL 3 K = projImage (StatedSL 3 K) := by
    rw [statedSL_eq_det_ker]
    rfl
  have hcube : ∀ g ∈ StatedSL 3 K, g ∈ Subgroup.center (GL (Fin 3) K) → g ^ 3 = 1 :=
    fun g hg hc => by
      simpa using pow_card_eq_one_of_det g hc (hH g hg)
  by_cases hdiv : r = 3 ∧ 3 ∣ Nat.card ((Subgroup.center (GL (Fin 3) K)).subgroupOf
      (StatedSL 3 K))
  · obtain ⟨rfl, h3⟩ := hdiv
    have hD3 : Nat.card ((Subgroup.center (GL (Fin 3) K)).subgroupOf (StatedSL 3 K)) = 3 :=
      le_antisymm (card_scalars_le (by norm_num) (StatedSL 3 K) hcube)
        (Nat.le_of_dvd Nat.card_pos h3)
    rw [hproj]
    exact pRank_three_projSL_three_le hf hK hD3
  · have hN : ¬ r ∣ Nat.card ((Subgroup.center (GL (Fin 3) K)).subgroupOf (StatedSL 3 K)) := by
      intro hrD
      by_cases hr3 : r = 3
      · exact hdiv ⟨hr3, hr3 ▸ hrD⟩
      · exact not_dvd_card_scalars (m := 3) hr (not_dvd_three hr hr3) (StatedSL 3 K) hcube hrD
    rw [hproj, pRank_projImage_eq (StatedSL 3 K) hN]
    exact pRank_le_two_of_det_gl hr hrK (by simp) (StatedSL 3 K) hH

theorem pRank_projSU_three_le {n : ℕ} (hn : 1 ≤ n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup (projSU 3 2 n)) ≤ 2 :=
  (pRank_projSU_le_projSL 3 2 n hr.one_lt).trans
    (pRank_projSL_three_le (K := GaloisField 2 (2 * n)) (f := 2 * n) (by omega)
      (GaloisField.card 2 (2 * n) (by omega)) hr hr2)

end CFSG.RankThree.PartOne.LIT
