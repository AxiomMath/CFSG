module

public import CFSG.RankThree.GF2n.Smith81.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Smith81.E5Tr

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem commute_of_conj_mem_of_odd {Q Z : Subgroup G} (hQ : IsPGroup 2 Q) (hZQ : Z ≤ Q)
    {v q : G} (hv : Odd (orderOf v)) (hvZ : ∀ w ∈ Z, v * w = w * v)
    (hδ : q⁻¹ * (v * q * v⁻¹) ∈ Z) : v * q = q * v := by
  obtain ⟨w, hwdef⟩ : ∃ w : G, w = q⁻¹ * (v * q * v⁻¹) := ⟨_, rfl⟩
  rw [← hwdef] at hδ
  have hσ : v * q * v⁻¹ = q * w := by rw [hwdef]; group
  have hvw : Commute v w := hvZ w hδ
  have key : ∀ j : ℕ, v ^ j * q * (v ^ j)⁻¹ = q * w ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hc : v * w ^ j * v⁻¹ = w ^ j := by
        rw [(hvw.pow_right j).eq]
        group
      calc v ^ (j + 1) * q * (v ^ (j + 1))⁻¹
          = v * (v ^ j * q * (v ^ j)⁻¹) * v⁻¹ := by
            rw [pow_succ', mul_inv_rev]
            group
        _ = v * (q * w ^ j) * v⁻¹ := by rw [ih]
        _ = (v * q * v⁻¹) * (v * w ^ j * v⁻¹) := by group
        _ = q * w ^ (j + 1) := by rw [hσ, hc, pow_succ', mul_assoc]
  have hu : w ^ orderOf v = 1 := by
    have hk := key (orderOf v)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hk
    calc w ^ orderOf v = q⁻¹ * (q * w ^ orderOf v) := by group
      _ = q⁻¹ * q := by rw [← hk]
      _ = 1 := by group
  obtain ⟨k, hk⟩ := hQ ⟨w, hZQ hδ⟩
  have hu2 : w ^ 2 ^ k = 1 := by
    have h' := congrArg Subtype.val hk
    simpa using h'
  have hcop : Nat.Coprime (2 ^ k) (orderOf v) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hv)
  have hg : w ^ Nat.gcd (2 ^ k) (orderOf v) = 1 := pow_gcd_eq_one.mpr ⟨hu2, hu⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hg
  calc v * q = (v * q * v⁻¹) * v := by group
    _ = q * w * v := by rw [hσ]
    _ = q * v := by rw [hg, mul_one]

theorem Q_le_H0 [Finite G] {M Q Z : Subgroup G} (Hs : StrothHyp M Q Z) : Q ≤ H0 M Z := by
  intro x hx
  refine ⟨Hs.Q_normal.1 hx, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hzC : z ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Hs.centralizer_Q]
    exact hz
  exact ((Subgroup.mem_centralizer_iff.mp hzC) x hx).symm

theorem mem_Cv_of_pi_fixed [Finite G] {M Q Z : Subgroup G} (Hs : StrothHyp M Q Z) {K : Type}
    [Field K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) {v : G} (hvM : v ∈ M)
    (hv : Odd (orderOf v)) (hvZ : ∀ w ∈ Z, v * w = w * v) {x : G} (hx : x ∈ Q)
    (h : M₀.π (v * x * v⁻¹) = M₀.π x) : v * x = x * v := by
  have hvx : v * x * v⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (Hs.Q_normal.2 hvM) x).mp hx
  have hδ : x⁻¹ * (v * x * v⁻¹) ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ hx hvx).mp h.symm
  exact commute_of_conj_mem_of_odd (isPGroup_Q' Hs) Hs.Z_normal.1 hv hvZ hδ

end CFSG.RankThree.GF2n.Smith81.E5Tr
