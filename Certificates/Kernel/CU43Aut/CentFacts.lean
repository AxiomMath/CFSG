
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43CountBase
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU43Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Model

public section

namespace CertificateChecks.KernelCU43Aut

open CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.LieType.Multipliers.U43

theorem commGens_iff {k : ℕ} (hk : k < 8) {g : Equiv.Perm (Fin 820)} (hg : g ∈ P) :
    CommGens k g ↔ k = 0 ∧ g = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hle : P ≤ Subgroup.centralizer {g * tP k} := by
      rw [P_eq_closure, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 h1.symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 h2.symm
    have hc : g * tP k = 1 := CFSG.EvenSmallLie.Child3.SelU43.eq_one_of_comm_tT fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
    have ht : tP k = g⁻¹ := eq_inv_of_mul_eq_one_right hc
    have hk0 : k = 0 := by
      by_contra hne
      have h := tP_mul_inv_not_mem hk (by norm_num : 0 < 8) hne
      rw [tP_zero, inv_one, mul_one, ht] at h
      exact h (P.inv_mem hg)
    subst hk0
    rw [tP_zero, mul_one] at hc
    exact ⟨rfl, hc⟩
  · rintro ⟨rfl, rfl⟩
    simp [CommGens, tP_zero]

theorem card_commGens {k : ℕ} (hk : k < 8) :
    Nat.card {g : P // CommGens k g} = if k = 0 then 1 else 0 := by
  split_ifs with h0
  · refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩,
      ⟨⟨1, (commGens_iff hk P.one_mem).2 ⟨h0, rfl⟩⟩⟩⟩
    rw [((commGens_iff hk a.1.2).1 a.2).2, ((commGens_iff hk b.1.2).1 b.2).2]
  · have : IsEmpty {g : P // CommGens k g} := ⟨fun a => h0 ((commGens_iff hk a.1.2).1 a.2).1⟩
    exact Nat.card_of_isEmpty

theorem injC : injCounts = true := by
  classical
  unfold injCounts
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.1 hk
  have hc := card_eq_countW_P (f := commW (tArr k) [tabA, tabB]) (Pr := CommGens k)
    fun w g hw _ => by
      have hH : RepW 820 (tArr k :: w) (g * tP k) := RepW.cons (rep_tArr k) hw
      simp only [commW, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      exact and_congr (allLt_comm_iff hH rep_tabA) (allLt_comm_iff hH rep_tabB)
  rw [← hc, card_commGens hk']
  by_cases h0 : k = 0 <;> simp [h0]

end CertificateChecks.KernelCU43Aut

end
