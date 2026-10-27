module

public import CFSG.RankThree.GF2n.Stroth80.Sec8SectionOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec84Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix


theorem sec86MinOrder_of (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hPts : Sec5NatPointsSpStatement) : Sec86MinOrderStatement := by
  classical
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 A hZA hAN hinv hAZ m hm hmSp
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨r, hr, -, hopp, hIZ⟩ := sec8_Z0_data h51 hA hc hs hZ0
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  obtain ⟨K, fK, finK, hK, m', hm', φ, u, u', hφ, hker, hact, huu', hL, hL'⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.spNat r hrR hr.plane
  have hpts : Sec8Pts hc t r m' K φ u u' := ⟨hm', hK, hφ, hker, hact, huu', hL, hL'⟩
  have hmm : m = m' := hmSp.m_unique hpts.spMNat
  subst hmm
  haveI : CharP K 2 := hpts.charP
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLCR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := hc.LB_conj_le_Rt_of_mem ht hrR
  have hnormQ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hRM hρ)) y).mp hy
  have hI : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Z0, ρ * x * ρ⁻¹ ∈ Z0 := fun ρ hρ x hx =>
    (Subgroup.mem_normalizer_iff.mp (hZ0.mem_normalizer hnormQ hρ) x).mp hx
  have hNcomm : ∀ n ∈ hc.CN t, ∀ y ∈ A, ⁅n, y⁆ ∈ Z0 := fun n hn y hy =>
    hopp.2.2.2.2.2.2.1 n hn y (hAN hy)
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ = LspGL m K u' := by
    rw [hc.LB_conj hrM]
    exact hL'
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  obtain ⟨hd', a, ha⟩ := sec8_invariant_section (R := Rt M (LB M Q B) t) (N := hc.CN t)
    (P := hc.CN t) (I := Z0) (L₁ := LB M Q B) (L₂ := LB M Q (conjSubgroup r B))
    (A₁ := LB M Q B ⊓ hc.CN t) (A₂ := LB M Q (conjSubgroup r B) ⊓ hc.CN t) (U := A) φ hφ
    (by have := hpts.two_le; omega) hker (fun ρ hρ x hx => hc.CN_conj_mem ht hρ hx) hI
    (fun n hn y hy => hopp.2.2.2.2.2.2.1 n hn y hy) hopp hLR hLCR huu' hpts.u_ne_zero hL hL2
    (fun x hx => hQN (hc.sq_mem_Q_of_mem_LB hx)) hrR (hc.LB_conj hrM).symm hZA hAN hinv
  have hq : 1 ≤ Nat.card Z := Nat.card_pos
  have ha1 : 1 ≤ a := by
    by_contra h0
    have h00 : a = 0 := by omega
    rw [h00, mul_zero, pow_zero, mul_one] at ha
    exact hAZ (Subgroup.eq_of_le_of_card_ge hZA ha.le).symm
  rw [ha, hK]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq (Nat.le_mul_of_pos_right _ ha1))

end CFSG.RankThree.GF2n.Stroth80
