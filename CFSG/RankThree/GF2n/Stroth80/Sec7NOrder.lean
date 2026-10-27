module

public import CFSG.RankThree.GF2n.Stroth80.Sec78RootOrders
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z0Data
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z1
public import CFSG.RankThree.GF2n.Stroth80.Sec711Step6
public import CFSG.RankThree.GF2n.Stroth80.Sec85Normal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem sec7NOrder_exp {q Qc Nc a Lc k p : ℕ} (hq : 0 < q)
    (hQ : Qc = q ^ (2 * (k + 1) + 1)) (hLn : Lc = Qc * q ^ k) (hLd : Lc = a * q ^ (2 * p))
    (hprod : Nc * (Qc * q) = a * a) : Nc * q ^ (4 * (p + 1)) = Qc ^ 2 := by
  have hLa : Qc * q ^ k = a * q ^ (2 * p) := hLn.symm.trans hLd
  have hQpos : 0 < Qc := by
    rw [hQ]
    exact pow_pos hq _
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hQpos hq)
  calc Nc * q ^ (4 * (p + 1)) * (Qc * q) = (Nc * (Qc * q)) * q ^ (4 * (p + 1)) := by ring
    _ = a * a * q ^ (4 * (p + 1)) := by rw [hprod]
    _ = (a * q ^ (2 * p)) ^ 2 * q ^ 4 := by ring
    _ = (Qc * q ^ k) ^ 2 * q ^ 4 := by rw [hLa]
    _ = Qc ^ 2 * q ^ (2 * k + 4) := by ring
    _ = Qc ^ 2 * (Qc * q) := by
      rw [hQ]
      ring


theorem sec7NOrder_of (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement) : Sec7NOrderStatement := by
  intro G _ _ M Q Z B hc n t hs m hm hmO
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre hs.toSec5.mem
  have hZN : Z0 ≤ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0 hZN
  have hZcard : Nat.card Z0 = Nat.card Q * Nat.card Z :=
    sec7ctr_card_Z0 h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0 hZN
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have hNeq : conjSubgroup r (hc.CN t) = hc.CN t :=
    conjSubgroup_CN_eq hc hrM
      (CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hr.mem))
      (CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.mpr
        (hc.Rt_normalizes_Vt hs.toSec5.mem hr.mem))
  have hA₂ : LB M Q (conjSubgroup r B) ⊓ hc.CN t = conjSubgroup r (LB M Q B ⊓ hc.CN t) := by
    rw [hc.LB_conj hrM, CFSG.RankThree.GF2n.conjSubgroup_inf, hNeq]
  have hcardA₂ : Nat.card ↥(LB M Q (conjSubgroup r B) ⊓ hc.CN t) =
      Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
    rw [hA₂, CFSG.RankThree.GF2n.card_conjSubgroup]
  have hprod : Nat.card ↥(hc.CN t) * Nat.card ↥Z0 =
      Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card ↥(LB M Q (conjSubgroup r B) ⊓ hc.CN t) :=
    card_mul_card_isOppDecomp hopp
  rw [hcardA₂, hZcard] at hprod
  obtain ⟨d, -, hVd, hLd⟩ := sec7ctr_card_LB hPts hc hs hr
  have hq2 : 2 ≤ Nat.card ↥Z := by
    have := hc.hyp.q4
    omega
  have hdm : d = 2 * m := by
    have h2 : Nat.card ↥Z * Nat.card ↥Z ^ d = Nat.card ↥Z * Nat.card ↥Z ^ (2 * m) :=
      hVd.symm.trans (n12N_card_V hc t m hm hmO)
    exact Nat.pow_right_injective hq2 (Nat.eq_of_mul_eq_mul_left (by omega) h2)
  have hLn := (stroth_3_5 h34 hc hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2
    hs.toSec5.gen).2.2.1
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := hs.toSec5.n_gt; omega⟩
  obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  have hQ : Nat.card ↥Q = Nat.card ↥Z ^ (2 * (k + 1) + 1) := by
    rw [← hk]
    exact hs.toSec5.width
  have hLn' : Nat.card ↥(LB M Q B) = Nat.card ↥Q * Nat.card ↥Z ^ k := by
    rw [hLn, show n - 1 = k by omega]
  have hLd' : Nat.card ↥(LB M Q B) =
      Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card ↥Z ^ (2 * p) := by
    rw [hLd, hdm, hp, show 2 * (p + 1) - 2 = 2 * p by omega]
  rw [hp]
  exact sec7NOrder_exp (by omega) hQ hLn' hLd' hprod

end CFSG.RankThree.GF2n.Stroth80
