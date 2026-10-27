module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdBorelGeneric
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e2
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218d
public import CFSG.Quasithin.H13.A6S13816j
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOB

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsOmegaMinus)

theorem two_pow_sub_one_dvd (n : ℕ) : 2 ^ n - 1 ∣ 2 ^ (2 * n) - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2
  rwa [one_pow, ← pow_mul, mul_comm] at h

private theorem two_pow_add_one_dvd (n : ℕ) : 2 ^ n + 1 ∣ 2 ^ (2 * n) - 1 := by
  have h : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [mul_comm, pow_mul, ← one_pow 2, Nat.sq_sub_sq]
    simp
  exact ⟨2 ^ n - 1, h⟩

private theorem isSylowOf_top {X : Type} [Group X] [Finite X] (S : Sylow 2 X) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup X) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, S.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact S.not_dvd_index

theorem kob_Sz {X : Type} [Group X] [Finite X] {n r : ℕ}
    (hX : IsSz X n) (hr : r.Prime) (hr2 : r ≠ 2) (hrn : ¬ r ∣ n) (hrq : ¬ r ∣ 2 ^ n - 1)
    (S : Sylow 2 X) {θ : MulAut X} (hθ : θ ^ r = 1)
    (hS : ∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) : θ = 1 :=
  eq_one_of_inner_of_noR
    (CFSG.Quasithin.H13.A6.SzSec.center_eq_bot_of_isSz (CFSG.Blueprint.LieModel.suzukiModel hX).2) S
    (noR_of_not_dvd_card hr S fun hN => hrq (uc22p2214_borel_prime_Sz hX (isSylowOf_top S) hr hr2 hN))
    (uc22p2214_inner_of_prime_Sz hX hr hrn hθ) hθ hS

theorem kob_L2 {X : Type} [Group X] [Finite X] {n r : ℕ} (hX : IsL2 X n) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrn : ¬ r ∣ n) (hrq : ¬ r ∣ 2 ^ n - 1) (S : Sylow 2 X) {θ : MulAut X}
    (hθ : θ ^ r = 1) (hS : ∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) : θ = 1 :=
  eq_one_of_inner_of_noR (uc22p22g_center_bot hX) S
    (noR_of_not_dvd_card hr S fun hN => hrq (uc22p2214_borel_prime_L2 hX (isSylowOf_top S) hr hr2 hN))
    (uc22p2214_inner_of_prime_L2 hX hr hrn hθ) hθ hS

theorem kob_Sp4 {X : Type} [Group X] [Finite X] {n r : ℕ} (hX : IsSp4 X n) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrn : ¬ r ∣ 2 * n) (hrq : ¬ r ∣ 2 ^ n - 1) (S : Sylow 2 X) {θ : MulAut X}
    (hθ : θ ^ r = 1) (hS : ∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) : θ = 1 :=
  eq_one_of_inner_of_noR (uc22p218d_center_eq_bot_sp4 hX) S
    (noR_of_not_dvd_card hr S fun hN => hrq (uc22p2214_borel_prime_Sp4 hX (isSylowOf_top S) hr hr2 hN))
    (uc22p2214_inner_of_prime_Sp4 hX hr hrn hθ) hθ hS

theorem kob_U3 {Y : Type} [Group Y] [Finite Y] {n r : ℕ} (hX : IsU3 Y n)
    (hZ : Subgroup.center Y = ⊥) (hr : r.Prime) (hr2 : r ≠ 2) (hrn : ¬ r ∣ 6 * n)
    (hrq : ¬ r ∣ 2 ^ (2 * n) - 1) (S : Sylow 2 Y) {θ : MulAut Y} (hθ : θ ^ r = 1)
    (hS : ∀ x ∈ (S : Subgroup Y), θ x ∈ (S : Subgroup Y)) : θ = 1 :=
  eq_one_of_inner_of_noR hZ S
    (noR_of_not_dvd_card hr S fun hN => by
      rcases uc22p2214_borel_prime_U3 hX (isSylowOf_top S) hr hr2 hN with h | h
      · exact hrq (h.trans (two_pow_sub_one_dvd n))
      · exact hrq (h.trans (two_pow_add_one_dvd n)))
    (uc22p2214_inner_of_prime_U3 hX hr hrn hθ) hθ hS

private theorem isL2_of_isOmegaMinus_four {X : Type} [Group X] {k : ℕ} (hk : 1 ≤ k)
    (h : IsOmegaMinus X 4 k) : IsL2 X (2 * k) := by
  obtain ⟨-, K, hKf, hKfin, b, c, hcard, hbc, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  haveI hchar : CharP K 2 := uc22p22d_charP_two hk hcard
  let Q : QuadraticForm K (Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K) :=
    CFSG.LieType.Universal.Spin.quadMinus (4 / 2) K b c
  have hQ : ⇑Q = StatedQuadMinus (4 / 2) K b c :=
    CFSG.LieType.Universal.Spin.coe_quadMinus (n := 4 / 2) (K := K) b c
  have hv : ∃ v, Q v ≠ 0 := by
    refine ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, ?_⟩
    rw [show Q = CFSG.LieType.Universal.Spin.quadMinus (4 / 2) K b c from rfl,
      CFSG.LieType.Universal.Spin.quadMinus_apply]
    simp [Pi.single_eq_same, Pi.single_eq_of_ne]
  have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot hQ hv
  let eΩ : StatedProj (StatedOmega (StatedQuadMinus (4 / 2) K b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus (4 / 2) K b c)) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact uc22p22d_isL2_of_omegaMinus4 (k := k) hk hcard b c hbc (e.trans eΩ)

theorem kob_Omega {X : Type} [Group X] [Finite X] {m r : ℕ} (hX : IsOmegaMinus X 4 m) (hm : 1 ≤ m)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrm : ¬ r ∣ 2 * m) (hrq : ¬ r ∣ 2 ^ (2 * m) - 1)
    (S : Sylow 2 X) {θ : MulAut X} (hθ : θ ^ r = 1)
    (hS : ∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) : θ = 1 :=
  kob_L2 (isL2_of_isOmegaMinus_four hm hX) hr hr2 hrm hrq S hθ hS

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOB

end
