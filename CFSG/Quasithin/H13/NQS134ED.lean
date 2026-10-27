module

public import CFSG.Quasithin.H13.NQS134EB
public import CFSG.Quasithin.H13.U3S1347Q

public section

namespace CFSG.Quasithin.H13.NQS134

open Equiv CFSG.Quasithin.H13.A6 CFSG.Quasithin.H13.U3.S6Out

theorem fix01_fix23 : ∀ x : P6, ∑ i, Multiplicative.toAdd x i = 0 →
    ∃ a : P6, ∑ i, Multiplicative.toAdd a i = 0 ∧ G6.permAct 6 (swap 0 1) a = a ∧
      G6.permAct 6 (swap 2 3) (a * x) = a * x := by
  decide +kernel

theorem card_fix45 : (Finset.univ.filter fun x : P6 => ∑ i, Multiplicative.toAdd x i = 0 ∧
    G6.permAct 6 (swap 4 5) x = x).card = 16 := by
  decide +kernel

theorem card_fixR1 : (Finset.univ.filter fun x : P6 => ∑ i, Multiplicative.toAdd x i = 0 ∧
    G6.permAct 6 (d6 8) x = x ∧ G6.permAct 6 (d6 6) x = x ∧
      G6.permAct 6 (d6 1) x = x).card = 4 := by
  decide +kernel

theorem d6_canonical : d6 4 = swap 0 1 ∧ d6 2 = swap 2 3 ∧ d6 1 = swap 4 5 := by decide

theorem span3_length (i j k : Fin 16) : (span3 i j k).length = 8 := rfl

theorem D_e8 {R : Subgroup (Perm (Fin 6))} (hRD : ∀ a ∈ R, InD6 a) (hR2 : ∀ a ∈ R, a * a = 1)
    (hR : 4 < Nat.card R) :
    Nat.card R ≤ 8 ∧ ((swap 0 1 ∈ R ∧ swap 2 3 ∈ R) ∨
      (d6 8 ∈ R ∧ d6 6 ∈ R ∧ d6 1 ∈ R ∧ ∀ a ∈ R, a ∈ span3 8 6 1)) := by
  classical
  have hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hR2 x hx)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hR2 y hy)
    have h3 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hR2 _ (R.mul_mem hx hy))
    rw [mul_inv_rev, hxi, hyi] at h3
    exact h3.symm
  have hex : ∀ s : Finset (Perm (Fin 6)), s.card ≤ 4 → ∃ a ∈ R, a ∉ s := fun s hs =>
    exists_mem_not_mem_of_lt s (by omega)
  obtain ⟨a, haR, ha⟩ := hex {1} (by simp)
  have ha1 : a ≠ 1 := by simpa using ha
  obtain ⟨i, rfl⟩ := mem_d6 a (hRD a haR)
  obtain ⟨b, hbR, hb⟩ := hex {1, d6 i} (Finset.card_le_two.trans (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  obtain ⟨hb1, hba⟩ := hb
  obtain ⟨j, rfl⟩ := mem_d6 b (hRD b hbR)
  obtain ⟨c, hcR, hc⟩ := hex {1, d6 i, d6 j, d6 i * d6 j} Finset.card_le_four
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨hc1, hci, hcj, hcij⟩ := hc
  obtain ⟨k, rfl⟩ := mem_d6 c (hRD c hcR)
  have hij : U3.S6Out.InvPair i j := ⟨hR2 _ haR, ha1, hR2 _ hbR, hb1, fun h => hba h.symm,
    hcomm _ haR _ hbR⟩
  have hijk : U3.S6Out.InvTriple i j k := ⟨hij, hR2 _ hcR, hcomm _ hcR _ haR,
    hcomm _ hcR _ hbR, hc1, hci, hcj, hcij⟩
  have hj := mem_cl i j hij
  have hk := mem_cl i k ⟨hR2 _ haR, ha1, hR2 _ hcR, hc1, fun h => hci h.symm,
    hcomm _ haR _ hcR⟩
  have hspan : ∀ x ∈ span3 i j k, x ∈ R := by
    intro x hx
    simp only [span3, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact R.one_mem
    · exact haR
    · exact hbR
    · exact hcR
    · exact R.mul_mem haR hbR
    · exact R.mul_mem haR hcR
    · exact R.mul_mem hbR hcR
    · exact R.mul_mem (R.mul_mem haR hbR) hcR
  obtain ⟨h01, h23, h45⟩ := d6_canonical
  rcases e8_cases i j hj k hk hijk with ⟨h4, h2, h1⟩ | ⟨h8, h6, h1⟩
  · have hsub : ∀ x ∈ R, x ∈ span3 4 2 1 := by
      intro x hx
      obtain ⟨l, rfl⟩ := mem_d6 x (hRD x hx)
      exact e8_max.1 l ⟨hR2 _ hx, hcomm _ hx _ (hspan _ h4), hcomm _ hx _ (hspan _ h2),
        hcomm _ hx _ (hspan _ h1)⟩
    refine ⟨(card_le_length hsub).trans (span3_length 4 2 1).le, Or.inl ⟨?_, ?_⟩⟩
    · rw [← h01]
      exact hspan _ h4
    · rw [← h23]
      exact hspan _ h2
  · have hsub : ∀ x ∈ R, x ∈ span3 8 6 1 := by
      intro x hx
      obtain ⟨l, rfl⟩ := mem_d6 x (hRD x hx)
      exact e8_max.2 l ⟨hR2 _ hx, hcomm _ hx _ (hspan _ h8), hcomm _ hx _ (hspan _ h6),
        hcomm _ hx _ (hspan _ h1)⟩
    exact ⟨(card_le_length hsub).trans (span3_length 8 6 1).le,
      Or.inr ⟨hspan _ h8, hspan _ h6, hspan _ h1, hsub⟩⟩

end CFSG.Quasithin.H13.NQS134
