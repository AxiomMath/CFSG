module

public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194PsuOdd
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SU
public import CFSG.RankThree.PartTwo.Sec19.Census194.Arith
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Mult
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SUBlock

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

open CFSG CFSG.RankThree.PartTwo.Sec19 CFSG.Assembly.LowTwoRank

section Scalars

variable {K : Type} [Field K] [Finite K]

theorem card_scalars_statedSU_dvd {f n : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 1 ≤ n) :
    Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) ∣ n ∧
      Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) ∣ 2 ^ f + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (f := f * 2) (by
    rw [hK, pow_mul])
  refine ⟨CFSG.SectionRank.OddCover.card_scalars_dvd hn _ fun x c hc => ?_,
    CFSG.SectionRank.OddCover.card_scalars_dvd hn _ fun x c hc => ?_⟩
  · have hdet := CFSG.SectionRank.OddCover.det_eq_one_of_linUni (p := 2) (f := f)
      (Or.inr ⟨hK, rfl⟩) x.1.2
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  · have hu := CFSG.SectionRank.OddCover.unitary_of_mem_statedSU hK x.1.2
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar] at hu
    have h00 := congrFun (congrFun hu ⟨0, hn⟩) ⟨0, hn⟩
    have hq0 : 2 ^ f ≠ 0 := by positivity
    rw [Matrix.scalar_apply, Matrix.diagonal_map (by simp [zero_pow hq0]),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq] at h00
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one]
    exact h00

end Scalars

theorem psu_odd_false
    {Y : Type} [Group Y] [Finite Y] (hR : Census194RankHyp Y)
    {a f : ℕ} (ha : 4 ≤ a) (hae : Even a)
    (hm : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU (a + 1) 2 f) : False := by
  have hf1 : 1 ≤ f := hm.1.2.1
  have hmodel := hm
  obtain ⟨⟨-, -, hn3, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (f := f * 2) (by
    rw [hK, pow_mul])
  haveI : Group.IsPerfect Y := hR.quasisimple.1
  have hodd := odd_card_center_of_pCore_eq_bot hR.pCore_two
  obtain ⟨k, hk⟩ := hae
  by_cases hspecial : a = 4 ∧ (f = 1 ∨ f = 3)
  ·
    obtain ⟨rfl, hf13⟩ := hspecial
    obtain ⟨-, ⟨ε⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row hmodel
      (by decide : ¬ Even (4 + 1))
    have hcard : Nat.card (CFSG.Blueprint.Multiplier.generic .PSU (4 + 1) 2 f ×
        CFSG.Blueprint.Multiplier.exceptional .PSU (4 + 1) 2 f) = 1 := by
      rcases hf13 with rfl | rfl <;>
        simp [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
          CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
          Nat.card_prod]
    have hZdvd := card_center_dvd_of_row hR.quasisimple (Y := Y)
      (MulEquiv.refl (Y ⧸ Subgroup.center Y)) ⟨ε⟩ hcard
    have hZ : Subgroup.center Y = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 hZdvd)
    have h3 : 3 ∣ 2 ^ f + 1 := by rcases hf13 with rfl | rfl <;> norm_num
    have hDn := (card_scalars_statedSU_dvd (K := K) hK (by omega : 1 ≤ 4 + 1)).1
    have hrk : ¬ 3 ∣ Nat.card ((StatedScalars (Fin (4 + 1)) K).subgroupOf
        (StatedSU (4 + 1) (2 ^ f) K)) := fun h => by
      have : 3 ∣ 5 := h.trans hDn
      omega
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have htor := (CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank Nat.prime_two
      (by omega : 2 ≤ 4 + 1) (by norm_num : (3 : ℕ) ≠ 2) (Or.inr ⟨hK, rfl, h3⟩)
      ((StatedScalars (Fin (4 + 1)) K).subgroupOf (StatedSU (4 + 1) (2 ^ f) K)) le_rfl).2 hrk
    exact hR.false_of_tooBig (((tooBig_of_three (by omega : 4 ≤ _ )).of_mulEquiv
      ((mulEquivQuotientCenterOfEqBot hZ).trans e).symm))
  ·
    obtain ⟨β, hβ⟩ := su_block_lift hK (by omega : 2 ≤ a) ⟨k, hk⟩ (le_refl 1) hodd e
    have hbl : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ f + 1 →
        a - 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedSU a (2 ^ f) K)) := fun r hr hr2 hrd => by
      haveI : Fact r.Prime := ⟨hr⟩
      exact pRank_statedSU_torus hK (by omega) hr2 hrd
    have hTB : TooBig (StatedSU a (2 ^ f) K) → False := fun h =>
      hR.false_of_tooBig (h.of_injective β hβ)
    rcases (show (f = 2 ∨ 4 ≤ f) ∨ ((f = 1 ∨ f = 3) ∧ 6 ≤ a) by omega) with hf24 | ⟨hf13, ha6⟩
    · obtain ⟨r, hr, hr3, hrd⟩ := exists_prime_gt_three_dvd_two_pow_add_one hf24
      exact hTB (tooBig_of_prime hr hr3 (by have := hbl r hr (by omega) hrd; omega))
    · have h3 : 3 ∣ 2 ^ f + 1 := by rcases hf13 with rfl | rfl <;> norm_num
      exact hTB (tooBig_of_three (by have := hbl 3 Nat.prime_three (by norm_num) h3; omega))

theorem survPSU_holds :
    Census194SurvPSU := by
  intro Y _ _ n f hR hm hn4
  have hf1 : 1 ≤ f := hm.1.2.1
  have hmodel := hm
  obtain ⟨⟨-, -, hn3, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (f := f * 2) (by
    rw [hK, pow_mul])
  haveI : Group.IsPerfect Y := hR.quasisimple.1
  have hodd := odd_card_center_of_pCore_eq_bot hR.pCore_two
  by_contra hcon
  rcases Nat.even_or_odd n with hev | hod
  ·
    obtain ⟨φ, hφs, hker, hD⟩ := evenSU_perfect_odd_cover_map hK (by omega) hev hodd e
    have hDn := (card_scalars_statedSU_dvd (K := K) hK (by omega : 1 ≤ n)).1
    have hkerD : Nat.card φ.ker ∣
        Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) :=
      Subgroup.card_dvd_of_le hker
    let eY : StatedSU n (2 ^ f) K ⧸ φ.ker ≃* Y := QuotientGroup.quotientKerEquivOfSurjective φ hφs
    have hTB : TooBig (StatedSU n (2 ^ f) K ⧸ φ.ker) → False := fun h =>
      hR.false_of_tooBig (h.of_mulEquiv eY)
    have htorus : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ f + 1 →
        n - 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedSU n (2 ^ f) K ⧸ φ.ker)) ∧
        (¬ r ∣ Nat.card φ.ker →
          n - 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedSU n (2 ^ f) K ⧸ φ.ker))) := by
      intro r hr hr2 hrd
      haveI : Fact r.Prime := ⟨hr⟩
      exact CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank Nat.prime_two
        (by omega) hr2 (Or.inr ⟨hK, rfl, hrd⟩) φ.ker hker
    obtain ⟨m, hm2⟩ := hev
    rcases Nat.lt_or_ge n 6 with h6 | h6
    · obtain rfl : n = 4 := by omega
      have hf24 : f = 2 ∨ 4 ≤ f := by omega
      obtain ⟨r, hr, hr3, hrd⟩ := exists_prime_gt_three_dvd_two_pow_add_one hf24
      obtain ⟨h1, h2⟩ := htorus r hr (by omega) hrd
      have hrk : ¬ r ∣ Nat.card φ.ker := fun h => by
        have h4 : r ∣ 2 ^ 2 := by simpa using h.trans (hkerD.trans hDn)
        have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h4)
        omega
      exact hTB (tooBig_of_prime hr hr3 (by have := h2 hrk; omega))
    · obtain ⟨r, hr, hr2, hrd⟩ := CFSG.RankThree.PartTwo.Census.exists_odd_prime_dvd_two_pow_add_one
        (by omega : 0 < f)
      obtain ⟨h1, -⟩ := htorus r hr hr2 hrd
      by_cases hr3 : r = 3
      · subst hr3
        exact hTB (tooBig_of_three (by omega))
      · exact hTB (tooBig_of_prime hr (by have := hr.two_le; omega) (by omega))
  ·
    obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
    obtain ⟨k, hk⟩ := hod
    exact psu_odd_false hR (a := a) (f := f) (by omega) ⟨k, by omega⟩ hmodel

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194
