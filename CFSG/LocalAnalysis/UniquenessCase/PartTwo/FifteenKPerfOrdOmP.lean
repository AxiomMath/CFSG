module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

private theorem s15k_pord_omp_units_subsingleton {K : Type} [Field K]
    (hK : Nat.card K = 2) : Subsingleton Kˣ :=
  (Nat.card_eq_one_iff_unique.mp (by rw [Nat.card_units, hK])).1

private theorem s15k_pord_omp_scalars_eq_bot {K : Type} [Field K] (hK : Nat.card K = 2)
    (ι : Type) [Fintype ι] [DecidableEq ι] : StatedScalars ι K = ⊥ := by
  have : Subsingleton Kˣ := s15k_pord_omp_units_subsingleton hK
  rw [eq_bot_iff]
  rintro _ ⟨c, rfl⟩
  rw [Subsingleton.elim c 1, map_one]
  exact Subgroup.one_mem _

private theorem s15k_pord_omp_card_statedProj {K : Type} [Field K] (hK : Nat.card K = 2)
    {ι : Type} [Fintype ι] [DecidableEq ι] (H : Subgroup (GL ι K)) :
    Nat.card (StatedProj H) = Nat.card H := by
  have hbot : (StatedScalars ι K).subgroupOf H = ⊥ := by
    rw [s15k_pord_omp_scalars_eq_bot hK, Subgroup.bot_subgroupOf]
  change Nat.card (H ⧸ (StatedScalars ι K).subgroupOf H) = Nat.card H
  rw [hbot]
  exact Nat.card_congr (QuotientGroup.quotientBot).toEquiv

private theorem s15k_pord_omp_card_elem {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) :
    (Nat.card ↥(CFSG.ClassicalGroups.Orthogonal.elementaryGroup
        (CFSG.LieType.Universal.Spin.quadPlus n K)) : ℤ) =
      (Nat.card K : ℤ) ^ (n * (n - 1)) * ((Nat.card K : ℤ) ^ n - 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hn0 : 0 < m + 1 := by omega
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (m + 1) K
  have hidx := CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_eq_two_mul hnd
    (CFSG.ClassicalGroups.Orthogonal.plusPair_orth (K := K) (i := ⟨0, by omega⟩)
      (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
    (CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (by omega)).2
    (CFSG.ClassicalGroups.Orthogonal.orthogonalGroup_le_closure_of_two_eq_zero
      (CFSG.ClassicalGroups.Orthogonal.plusFamily_orth hn0) hnd h2
      (fun x hx _ => CFSG.ClassicalGroups.Orthogonal.eq_zero_of_mem_tailSpace_plusFamily hn0 hx)
      (fun x hx hx0 => absurd
        (CFSG.ClassicalGroups.Orthogonal.eq_zero_of_mem_tailSpace_plusFamily hn0 hx) hx0)
      (by omega))
  have hO := (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := K) m).2
  rw [hidx] at hO
  push_cast at hO
  rw [Nat.add_sub_cancel, show (m + 1) * m = m * (m + 1) by ring]
  linarith

private theorem s15k_pord_omp_card_plus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 3 ≤ m) :
    (Nat.card ↥(StatedOmega (StatedQuadPlus m K)) : ℤ) =
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m - 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_quadPlus_eq_map hm,
    Subgroup.card_map_of_injective (MulEquiv.injective _)]
  exact s15k_pord_omp_card_elem hm

private theorem s15k_pord_omp_charP_two {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

theorem s15k_pord_omega_plus {X : Type} [Group X] {n : ℕ} (hn : 6 ≤ n)
    (h : IsOmegaPlus X n 1) :
    (n = 6 → Nat.card X = 20160) ∧ (8 ≤ n → 2 ^ 7 ∣ Nat.card X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  haveI : CharP K 2 := s15k_pord_omp_charP_two (f := 1) hK
  have hm3 : 3 ≤ n / 2 := by omega
  have hcardX : Nat.card X = Nat.card ↥(StatedOmega (StatedQuadPlus (n / 2) K)) := by
    rw [Nat.card_congr e.toEquiv]
    exact s15k_pord_omp_card_statedProj hK2 _
  have horder : (Nat.card X : ℤ) = (2 : ℤ) ^ ((n / 2) * (n / 2 - 1)) *
      ((2 : ℤ) ^ (n / 2) - 1) *
      ∏ i ∈ Finset.Icc 1 (n / 2 - 1), ((2 : ℤ) ^ (2 * i) - 1) := by
    rw [hcardX, s15k_pord_omp_card_plus (m := n / 2) hm3, hK2]
    norm_num
  constructor
  · intro hn6
    have hd : n / 2 = 3 := by omega
    have h6 : (Nat.card X : ℤ) = 20160 := by
      rw [horder, hd]
      norm_num [Finset.prod_Icc_succ_top]
    exact_mod_cast h6
  · intro hn8
    have hdvd : ((2 ^ 7 : ℕ) : ℤ) ∣ (Nat.card X : ℤ) := by
      rw [horder]
      push_cast
      have hd4 : 4 ≤ n / 2 := by omega
      have hge : 7 ≤ (n / 2) * (n / 2 - 1) :=
        le_trans (by norm_num) (Nat.mul_le_mul hd4 (by omega : 3 ≤ n / 2 - 1))
      have hA : (2 : ℤ) ^ 7 ∣ (2 : ℤ) ^ ((n / 2) * (n / 2 - 1)) :=
        pow_dvd_pow (2 : ℤ) hge
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right hA _) _
    exact Int.natCast_dvd_natCast.mp hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
