module

public import CFSG.Walter.ReeOrder.WardLocal.NP

public section

open scoped BigOperators Classical MatrixGroups

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P)

namespace Block

include B hq hK hG in
theorem card_centralizer_dvd_two_q2 {x : G} (hx : x ∈ PP1 S)
    (hxC : x ∉ CC S hq hK (B.hcT hq hK hG) hG) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 2 * q ^ 2 := by
  have hcT := B.hcT hq hK hG
  have hx1 : x ≠ 1 := by rintro rfl; exact hxC (Subgroup.one_mem _)
  by_cases hinv : ∃ t : G, orderOf t = 2 ∧ x * t = t * x
  · obtain ⟨t, ht, hxt⟩ := hinv
    have hxp : IsPGroup 3 (Subgroup.zpowers x) :=
      (isPGroup_PP1 (S := S)).to_le (Subgroup.zpowers_le.mpr hx)
    rcases isConj_T_of_commute hq hK hx1 hxp ht hxt with h | h
    · rw [card_centralizer_of_isConj h, B.card_CT hq hK hG]
    · rw [card_centralizer_of_isConj h, centralizer_inv, B.card_CT hq hK hG]
  · push Not at hinv
    rcases B.xi4_of_no_involution hq hK hG hx hx1 hinv with ⟨hc, -⟩ | ⟨hc, -⟩
    · rw [hc]; exact dvd_mul_left _ _
    · exact absurd (AA_subset_CC hq hK hcT hG (B.card_AA hq hK hG)
        (mem_AA.mpr ⟨hx, hx1, hinv, hc⟩)) hxC

include B hq hK hG hP1P hPc hPn in
theorem inf_centralizer_PP1 {x : G} (hx : x ∈ PP1 S) (hxZ : x ∉ zcen P) :
    P ⊓ Subgroup.centralizer ({x} : Set G) = PP1 S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcT := B.hcT hq hK hG
  have hA := B.card_AA hq hK hG
  have hZ := zcen_eq_CC hq hK hcT hG hA hP1P hPc hPn
  have hxC : x ∉ CC S hq hK hcT hG := by rw [← hZ]; exact hxZ
  have hdvd := B.card_centralizer_dvd_two_q2 hq hK hG hx hxC
  have hle : PP1 S ≤ P ⊓ Subgroup.centralizer ({x} : Set G) := fun y hy =>
    ⟨hP1P hy, Subgroup.mem_centralizer_singleton_iff.mpr (PP1_comm hq hK hcT hG hy hx)⟩
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_PP1 hq hK hcT hG]
  have hp : IsPGroup 3 (P ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) :=
    (isPGroup_P hq hPc).to_le inf_le_left
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  have h1 : Nat.card (P ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ∣ 2 * q ^ 2 :=
    (Subgroup.card_dvd_of_le inf_le_right).trans hdvd
  rw [ha] at h1 ⊢
  have h2 : 3 ^ a ∣ q ^ 2 :=
    (Nat.Coprime.pow_left a (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left h1
  exact Nat.le_of_dvd (by rw [hq]; positivity) h2

end Block

end CFSG.Walter.WardLocal
