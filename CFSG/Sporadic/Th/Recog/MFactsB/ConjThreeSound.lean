module

public import CFSG.Sporadic.Th.Recog.MFactsB.Rows
public import CFSG.Sporadic.Th.Recog.MFactsB.QCount
public import Certificates.Certificate687008

public section

namespace CFSG.Sporadic.Th.Recog.MFactsB

open CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Th.Recog.MFactsDData CFSG.Sporadic.Th.Recog.MFactsBData
open CFSG.Sporadic.Th.Recog.MFactsCData


private theorem eq_one_or_eq_z_of_mem_commFilter {G : Array V4} {g : ↥Max3.M}
    (hG : IsRows G (g : J)) {w : ↥Max3.M} (hw : (w : J) ∈ Max3.Q) (h2 : w * w = 1)
    (hcomm : (w : J) * (g : J) = (g : J) * (w : J))
    (hcheck : ∀ k ∈ commFilter G,
      (decide (k.val ≤ 1) || !eqRows (mulRows (rowsNfAt k) (rowsNfAt k)) idRows) = true) :
    w = 1 ∨ (w : J) = Max3.z := by
  obtain ⟨k, hk⟩ := Max3.InvRep.exists_nfAt_eq hw
  have hmem : k ∈ commFilter G := (mem_commFilter_iff hG k).mpr (by rw [hk]; exact hcomm)
  have hkall := hcheck k hmem
  rw [Bool.or_eq_true] at hkall
  rcases hkall with hle | hnot
  · have hle' : k.val ≤ 1 := of_decide_eq_true hle
    have hk01 : k = 0 ∨ k = 1 := by
      have h : k.val = 0 ∨ k.val = 1 := by omega
      rcases h with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hk01 with h | h
    · left
      apply Subtype.ext
      have h1 : (w : J) = 1 := by rw [← hk, h, nfAt_zero]
      simpa using h1
    · right
      rw [← hk, h, nfAt_one]
  · have he : eqRows (mulRows (rowsNfAt k) (rowsNfAt k)) idRows = false :=
      Bool.eq_false_of_not_eq_true' hnot
    have hne : nfAt k * nfAt k ≠ (1 : J) :=
      ((isRows_nfAt k).mul (isRows_nfAt k)).ne_of_eqRows IsRows.one he
    have hw2 : (w : J) * (w : J) = 1 := by simpa using congrArg Subtype.val h2
    rw [← hk] at hw2
    exact absurd hw2 hne

theorem eq_one_or_eq_z_of_comm_ω₁_mul_ω₂ (w : ↥Max3.M) (hw : (w : J) ∈ Max3.Q)
    (h2 : w * w = 1) (hc : w * (ω₁ * ω₂) = ω₁ * ω₂ * w) :
    w = 1 ∨ (w : J) = Max3.z := by
  have hG : IsRows (mulRows (rowsW1 (rowsWJ 3) (rowsWJ 4))
      (rowsW2 (rowsWJ 7) (rowsW1 (rowsWJ 3) (rowsWJ 4)) (rowsUI (rowsWJ 7))))
      (((ω₁ * ω₂ : ↥Max3.M) : J)) := by
    simpa only [Subgroup.coe_mul] using isRows_ω₁.mul isRows_ω₂
  have hcomm : (w : J) * (((ω₁ * ω₂ : ↥Max3.M) : J)) =
      (((ω₁ * ω₂ : ↥Max3.M) : J)) * (w : J) := by
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val hc
  have hcheck : ∀ k ∈ commFilter (mulRows (rowsW1 (rowsWJ 3) (rowsWJ 4))
      (rowsW2 (rowsWJ 7) (rowsW1 (rowsWJ 3) (rowsWJ 4)) (rowsUI (rowsWJ 7)))),
      (decide (k.val ≤ 1) || !eqRows (mulRows (rowsNfAt k) (rowsNfAt k)) idRows) = true := by
    have h := Certificates.certificate687008.1
    simpa only [checkT3687008, List.all_eq_true] using h
  exact eq_one_or_eq_z_of_mem_commFilter hG hw h2 hcomm hcheck

theorem eq_one_or_eq_z_of_comm_ω₁ (w : ↥Max3.M) (hw : (w : J) ∈ Max3.Q)
    (h2 : w * w = 1) (hc : w * ω₁ = ω₁ * w) :
    w = 1 ∨ (w : J) = Max3.z := by
  have hcomm : (w : J) * ((ω₁ : ↥Max3.M) : J) = ((ω₁ : ↥Max3.M) : J) * (w : J) := by
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val hc
  have hcheck : ∀ k ∈ commFilter (rowsW1 (rowsWJ 3) (rowsWJ 4)),
      (decide (k.val ≤ 1) || !eqRows (mulRows (rowsNfAt k) (rowsNfAt k)) idRows) = true := by
    have h := Certificates.certificate687008.2.1
    simpa only [checkT333687008, List.all_eq_true] using h
  exact eq_one_or_eq_z_of_mem_commFilter isRows_ω₁ hw h2 hcomm hcheck

theorem card_Q_inf_centralizer_s :
    Nat.card ↥(Max3.Q.subgroupOf Max3.M ⊓ Subgroup.centralizer ({sLetter} : Set ↥Max3.M)) = 8 := by
  have hlen : (commFilter (rowsWJ 5)).length = 8 := Certificates.certificate687008.2.2
  rw [card_Q_inf_centralizer_eq_length (g := sLetter) (G := rowsWJ 5) isRows_sLetter, hlen]

end CFSG.Sporadic.Th.Recog.MFactsB
