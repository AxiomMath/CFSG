module

public import CFSG.RankThree.GF2n.Stroth80.Sec84CaseOnePrep
public import CFSG.RankThree.GF2n.Stroth80.Sec84AbelianN
public import CFSG.RankThree.GF2n.Stroth80.Sec84InputStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec85Normal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem commSec_le_CN {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} (hc : Ctx M Q Z B)
    {t : G} (ht : t ∈ LB M Q B) {x : G} (hx : x ∈ Rt M (LB M Q B) t) :
    CommSec (hc.CN t) Q x ≤ hc.CN t := by
  refine sup_le ?_ (sec8_Q_le_CN hc ht)
  refine Subgroup.commutator_le.mpr fun c hc' y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hxk : x ^ k ∈ Rt M (LB M Q B) t := zpow_mem hx k
  have h1 : (x ^ k) * c⁻¹ * (x ^ k)⁻¹ ∈ hc.CN t :=
    hc.CN_conj_mem ht hxk ((hc.CN t).inv_mem hc')
  have e : ⁅c, x ^ k⁆ = c * ((x ^ k) * c⁻¹ * (x ^ k)⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (hc.CN t).mul_mem hc' h1

theorem step84CaseOne_of_leaves (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hPts : Sec5NatPointsSpStatement) (hirr : Sec86IrredStatement) (hTI : Sec8TIStatement)
    (hU : Sec84CommUpperStatement) (hNA : Sec84NAbelianStatement) : Step84CaseOneStatement := by
  classical
  intro G _ _ M Q Z B hc n t hs hC83 Z0 hZ0 hν hNab hSC
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0card : Nat.card ↥Z0 = Nat.card Q * Nat.card Z :=
    sec86ZCard_of_51 h51 hA G M Q Z B hc n t hs Z0 hZ0
  have hZLB : Z0 ≤ LB M Q B := sec8_Z0_le_LB h51 hA hc hs hZ0
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun y hy => (Ctx.mem_CN.1 hy).1
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hQn : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  have hirrC := hirr G M Q Z B hc n t hs Z0 hZ0
  obtain ⟨r, hr, -, hopp, hIZ⟩ := sec8_Z0_data h51 hA hc hs hZ0
  have hLCR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := hc.LB_conj_le_Rt_of_mem ht hr.mem
  have hsq : ∀ c ∈ hc.CN t, c ^ 2 ∈ Q :=
    sq_mem_of_abelian_irred hirrC hopp hLR hLCR (sec8_Q_le_CN hc ht)
      (fun c hc' y hy => hQn c (hRM (hNR hc')) y hy) (fun ρ hρ y hy => hQn ρ (hRM hρ) y hy)
      (fun ρ hρ c hc' => hc.CN_conj_mem ht hρ hc')
      (fun c hc' c' hc'' => hNab (Subgroup.commutator_mem_commutator hc' hc''))
      (fun z hz ρ hρ => hZ0.comm_mem hz hρ) (fun z hz => hc.sq_mem_Q_of_mem_LB (hZLB hz))
  rcases hC83 with ⟨hn11, hsp3, hN9⟩ | ⟨hn17, hsp4, hN17⟩
  · have hN8 : Nat.card ↥(hc.CN t) = Nat.card ↥Z0 * Nat.card Z ^ 8 := by
      rw [hN9, hZ0card]
      ring
    exact hNA G M Q Z B hc n t hs hsp3 Z0 hZ0 hN8 hirrC hNab hsq
  · have hN16 : Nat.card ↥(hc.CN t) = Nat.card ↥Z0 * Nat.card Z ^ (2 ^ 4) := by
      rw [hN17, hZ0card]
      ring
    push Not at hν
    obtain ⟨ν, hνM, hνL, hνZ⟩ := hν
    obtain ⟨z, hz, hzQ⟩ := sec8_exists_Z0_not_Q h51 hA hc hs hZ0
    have hxX : ν * z * ν⁻¹ ∈ conjSubgroup ν Z0 := by
      rw [mem_conjSubgroup]
      have e : ν⁻¹ * (ν * z * ν⁻¹) * ν = z := by group
      rw [e]
      exact hz
    have hxQ : ν * z * ν⁻¹ ∉ Q := by
      intro h
      apply hzQ
      have h1 := hQn ν⁻¹ (M.inv_mem hνM) _ h
      have e : ν⁻¹ * (ν * z * ν⁻¹) * ν⁻¹⁻¹ = z := by group
      rwa [e] at h1
    have hxL : ν * z * ν⁻¹ ∈ LB M Q B := (Subgroup.mem_normalizer_iff.mp hνL z).mp (hZLB hz)
    have hxN : ν * z * ν⁻¹ ∉ hc.CN t := by
      intro hxN
      have hy : ν * z * ν⁻¹ ∈ Z0 := hSC z hz ν hνM ⟨hxL, hxN⟩
      exact hνZ (hTI G M Q Z B hc n t hs Z0 hZ0 ν hνM z hz hzQ hy)
    have hlow := sec8_CN_commSec_lower h51 hA hPts hc hs hZ0 hsp4 hN16 hxL hxN
    have hup := hU G M Q Z B hc n t hs hsp4 Z0 hZ0 hN16 hNab hsq hSC
      (fun g hg u hu huQ hgu => hTI G M Q Z B hc n t hs Z0 hZ0 g hg u hu huQ hgu) ν hνM hνL hνZ
      _ hxX hxQ
    have hsup : CommSec (hc.CN t) Z0 (ν * z * ν⁻¹) =
        CommSec (hc.CN t) Q (ν * z * ν⁻¹) ⊔ Z0 := by
      unfold CommSec
      rw [sup_assoc, sup_eq_right.mpr hQZ0]
    have hnormQ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
      hQn ρ (hRM hρ) y hy
    have hYle := commSec_le_CN hc ht (hLR hxL)
    have hcard := card_sup_mul_card_le_of_normalizes (CommSec (hc.CN t) Q (ν * z * ν⁻¹)) Z0 Q
      le_sup_right hQZ0 (fun a ha b hb =>
        (Subgroup.mem_normalizer_iff.mp (hZ0.mem_normalizer hnormQ (hNR (hYle ha))) b).mp hb)
    rw [← hsup] at hcard
    have h4 : (2 : ℕ) ^ (4 - 2) = 4 := by norm_num
    rw [h4] at hlow
    have hq : 4 ≤ Nat.card Z := hc.hyp.q4
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have hZ0pos : 0 < Nat.card ↥Z0 := Nat.card_pos
    set Y := Nat.card ↥(CommSec (hc.CN t) Q (ν * z * ν⁻¹)) with hY
    set C0 := Nat.card ↥(CommSec (hc.CN t) Z0 (ν * z * ν⁻¹)) with hC0
    have h5 : Nat.card ↥Z0 * Nat.card Z ^ 4 * Nat.card Q ≤ Nat.card Q * Nat.card Z ^ 3 *
        Nat.card ↥Z0 := by
      calc Nat.card ↥Z0 * Nat.card Z ^ 4 * Nat.card Q ≤ C0 * Nat.card Q :=
            Nat.mul_le_mul_right _ hlow
        _ ≤ Y * Nat.card ↥Z0 := hcard
        _ ≤ Nat.card Q * Nat.card Z ^ 3 * Nat.card ↥Z0 := Nat.mul_le_mul_right _ hup
    have h6 : Nat.card Z ^ 4 ≤ Nat.card Z ^ 3 := by
      have h7 : (Nat.card ↥Z0 * Nat.card Q) * Nat.card Z ^ 4 ≤
          (Nat.card ↥Z0 * Nat.card Q) * Nat.card Z ^ 3 := by
        calc (Nat.card ↥Z0 * Nat.card Q) * Nat.card Z ^ 4
            = Nat.card ↥Z0 * Nat.card Z ^ 4 * Nat.card Q := by ring
          _ ≤ Nat.card Q * Nat.card Z ^ 3 * Nat.card ↥Z0 := h5
          _ = (Nat.card ↥Z0 * Nat.card Q) * Nat.card Z ^ 3 := by ring
      exact Nat.le_of_mul_le_mul_left h7 (Nat.mul_pos hZ0pos hQpos)
    have h8 : Nat.card Z ^ 3 < Nat.card Z ^ 4 :=
      Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

end CFSG.RankThree.GF2n.Stroth80
