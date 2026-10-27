
module

public import CFSG.Quasithin.Vol2.KGFactG2RuE64Base

public import Certificates.Certificate7162

public noncomputable section

namespace CFSG.Quasithin.H13.Ch4.G2Ru

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native

section Inv

end Inv

theorem g2E64Local_spec {i : ℕ} (hi : i < g2Inv.size) :
    g2E64Local i = true := by
  have hcheck := Certificates.certificate7162
  rw [g2E64Check, Bool.and_eq_true] at hcheck
  exact allLt_spec hcheck.1 hi

theorem g2Multi_count :
    ((Finset.range g2Inv.size).filter fun k => g2Multi k = true).card ≤ 62 := by
  have hcheck := Certificates.certificate7162
  rw [g2E64Check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rw [← countP_range_eq_card]
  exact hcheck.2

theorem exists_wr_of_local {i : ℕ} (hi : i < g2Inv.size)
    (hdeg : 62 ≤ g2DegA[i]!) (hm : g2Multi i = false) :
    ∃ r < 4, (g2InWM[r]!)[i]! = true ∧ ∀ j < g2Inv.size, (g2KeepM[i]!)[j]! = true →
      62 ≤ g2DegA[j]! → (g2InWM[r]!)[j]! = true := by
  have hloc := g2E64Local_spec hi
  have hd' : decide (g2DegA[i]! < 62) = false := by
    rw [decide_eq_false_iff_not]
    omega
  rw [g2E64Local, hm, Bool.or_false, hd', Bool.false_or, List.any_eq_true] at hloc
  obtain ⟨r, hr, hloc⟩ := hloc
  rw [Bool.and_eq_true, allLt_iff] at hloc
  refine ⟨r, List.mem_range.1 hr, hloc.1, fun j hj hk hdj => ?_⟩
  have h1 := hloc.2 j hj
  have hdj' : decide (g2DegA[j]! < 62) = false := by
    rw [decide_eq_false_iff_not]
    omega
  rwa [hk, Bool.not_true, Bool.false_or, hdj', Bool.false_or] at h1

section Idx

variable
  {E : Subgroup (Equiv.Perm (Fin 4060))}

end Idx

theorem le_g2Wr_of_card
    {E : Subgroup (Equiv.Perm (Fin 4060))} (hES : E ≤ ruS)
    (hE : ∀ x ∈ E, x * x = 1) (hcard : 64 ≤ Nat.card E) : ∃ r < 4, E ≤ g2Wr r := by
  have h63 : 63 ≤ (g2Idx E).card := by
    have := card_g2Idx hES hE
    omega
  obtain ⟨i, hi, hni⟩ : ∃ i ∈ g2Idx E, g2Multi i = false := by
    by_contra hall
    simp only [not_exists, not_and, Bool.not_eq_false] at hall
    have : (g2Idx E).card ≤ 62 :=
      le_trans (Finset.card_le_card fun k hk =>
        Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_of_mem_g2Idx hk), hall k hk⟩) g2Multi_count
    omega
  obtain ⟨r, hr, hri, hnb⟩ := exists_wr_of_local (lt_of_mem_g2Idx hi)
    (deg_of_mem_g2Idx hE h63 hi) hni
  refine ⟨r, hr, fun x hx => ?_⟩
  by_cases hx1 : x = 1
  · rw [hx1]
    exact (g2Wr r).one_mem
  obtain ⟨j, hj, rfl⟩ := exists_mem_g2Idx hES hE hx hx1
  have hjr : (g2InWM[r]!)[j]! = true := by
    by_cases hij : i = j
    · rw [← hij]
      exact hri
    · exact hnb j (lt_of_mem_g2Idx hj) (keepM_of_mem_g2Idx hE h63 hi hj hij)
        (deg_of_mem_g2Idx hE h63 hj)
  rw [g2InWM_get hr (lt_of_mem_g2Idx hj)] at hjr
  exact mem_g2Wr_of_any hr (rep_g2InvElt (lt_of_mem_g2Idx hj)) hjr

end CFSG.Quasithin.H13.Ch4.G2Ru
