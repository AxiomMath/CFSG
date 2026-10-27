module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelNonIso
import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitSmall
import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitAut
import CFSG.LocalAnalysis.WeakClosure81.TransvectionCenterCard

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {X : Type} [Group X] [Finite X] {S : Subgroup X}

theorem borel86_ra_four_le_card_of_linearShape (h : SevenElevenLinearShape X S) :
    4 ≤ Nat.card S := by
  obtain ⟨m', n', hm', -, htc, -⟩ := h
  obtain ⟨F, hF, hFin, hcard, e, a, ha, hiff⟩ := htc
  have hsub : transvectionCenterSet m' F a ⊆
      Set.range (fun x : S => e (QuotientGroup.mk (x : X))) := by
    intro z hz
    obtain ⟨x, hx, hxeq⟩ := (hiff (e.symm z)).mpr (by simpa using hz)
    exact ⟨⟨x, hx⟩, by simpa using congrArg e hxeq⟩
  have hle : (transvectionCenterSet m' F a).ncard ≤ Nat.card S := by
    have h1 : (transvectionCenterSet m' F a).ncard ≤
        (Set.range (fun x : S => e (QuotientGroup.mk (x : X)))).ncard :=
      Set.ncard_le_ncard hsub (Set.finite_range _)
    have h2 : (Set.range (fun x : S => e (QuotientGroup.mk (x : X)))).ncard ≤ Nat.card S := by
      rw [← Nat.card_coe_set_eq]
      exact Finite.card_range_le _
    exact h1.trans h2
  have hcount := ncard_transvectionCenterSet m' F (by omega : 2 ≤ m') a ha
  have hq : 2 ≤ Nat.card F := by
    have h2 := Finite.one_lt_card (α := F)
    omega
  have hexp : 2 ≤ m' - 1 := by omega
  have h4 : 4 ≤ Nat.card F ^ (m' - 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hq 2
      _ ≤ Nat.card F ^ (m' - 1) := Nat.pow_le_pow_right (by omega) hexp
  have h5 : Nat.card F ^ (m' - 1) ≤ Nat.card S := by
    rw [← hcount]
    exact hle
  exact h4.trans h5

theorem borel86_ra_false_of_rootGroupShape (hS : BarSituation X S) (g1 : W3Lem85TwoGap1)
    (hS2 : Nat.card S = 2) {m n : ℕ} (hm : 3 < m) (hn : 1 < n)
    (hY : IsSpGp (X ⧸ Subgroup.center X) m n ∨ IsPSUGp (X ⧸ Subgroup.center X) m n)
    {n' : ℕ} (h : IsRootGroupShape X n' S) : False := by
  rcases h with ⟨m', hSp, hR⟩ | ⟨m', hU, hR⟩ | ⟨hSz, hR⟩
  · have h1 : 2 ^ n' = 2 ^ 1 := by rw [← hR.1, hS2]; norm_num
    have hn' : n' = 1 := Nat.pow_right_injective le_rfl h1
    subst hn'
    exact not_isSpGp_one_of_isSpGp_or_isPSUGp hm hn hY m' hSp
  · have h1 : 2 ^ n' = 2 ^ 1 := by rw [← hR.1, hS2]; norm_num
    have hn' : n' = 1 := Nat.pow_right_injective le_rfl h1
    subst hn'
    exact not_isPSUGp_one_of_isSpGp_or_isPSUGp hm hn hY m' hU
  · have h1 : 2 ^ n' = 2 ^ 1 := by
      rw [← card_eq_of_suzukiRoot hS g1 hSz hR, hS2]
      norm_num
    have hn' : n' = 1 := Nat.pow_right_injective le_rfl h1
    subst hn'
    unfold IsSzGp CFSG.Blueprint.SuzukiModel at hSz
    obtain ⟨-, a, ha, K, hK, hKfin, hf, hKcard, hne⟩ := hSz
    omega

theorem borel86_ra_of_alt4 (hS : BarSituation X S) (hc : CentralInSylow X S)
    (g4 : W3Lem85TwoGap4) (hS2 : Nat.card S = 2) {m n : ℕ} (hm : 3 < m) (hn : 1 < n)
    (hY : IsSpGp (X ⧸ Subgroup.center X) m n ∨ IsPSUGp (X ⧸ Subgroup.center X) m n)
    {m' n' : ℕ}
    (h : (IsSpGp (X ⧸ Subgroup.center X) m' n' ∧
        ∀ s ∈ S, s ≠ 1 → IsSymplecticTransvection X m' n' s) ∨
      (IsPSUGp (X ⧸ Subgroup.center X) m' n' ∧
        ∀ s ∈ S, s ≠ 1 → IsUnitaryTransvection X m' n' s) ∨
      IsOrthGp (X ⧸ Subgroup.center X) m' n' ∨ IsL2WrSymGp (X ⧸ Subgroup.center X) n' m') :
    1 < n' ∧ ((2 ≤ m' ∧ ∀ s ∈ S, s ≠ 1 → IsSymplecticTransvection X m' n' s) ∨
      (3 ≤ m' ∧ ∀ s ∈ S, s ≠ 1 → IsUnitaryTransvection X m' n' s)) := by
  rcases h with ⟨hSp, hT⟩ | ⟨hU, hT⟩ | hO | hW
  · have hn'1 : 1 ≤ n' := one_le_of_isSpGp hSp
    have hn'ne : n' ≠ 1 := by
      rintro rfl
      exact not_isSpGp_one_of_isSpGp_or_isPSUGp hm hn hY m' hSp
    have hn' : 1 < n' := by omega
    have hSp' : IsSpGp (X ⧸ Subgroup.center X) m' n' := hSp
    obtain ⟨k, hk, -⟩ := hSp
    have hm'2 : 2 ≤ m' := by
      by_contra hle
      have hlt : m' < 2 := not_le.1 hle
      have hm'0 : m' = 0 := by omega
      have hSp0 : IsSpGp (X ⧸ Subgroup.center X) 0 n' := hm'0 ▸ hSp'
      have hbot := eq_bot_of_subsingleton_quot hS (subsingleton_of_isSpGp_zero hSp0)
      rw [hbot] at hS2
      simp at hS2
    exact ⟨hn', Or.inl ⟨hm'2, hT⟩⟩
  · obtain ⟨h3, hn'1⟩ := three_le_of_isPSUGp hU
    have hn'ne : n' ≠ 1 := by
      rintro rfl
      exact not_isPSUGp_one_of_isSpGp_or_isPSUGp hm hn hY m' hU
    have hn' : 1 < n' := by omega
    exact ⟨hn', Or.inr ⟨h3, hT⟩⟩
  · exact (g4 X S hS hS2 (Or.inl ⟨m', n', hO⟩) hc).elim
  · rcases Nat.lt_or_ge m' 2 with hm2 | hm2
    · interval_cases m'
      · have hbot := eq_bot_of_subsingleton_quot hS (subsingleton_of_isL2WrSymGp_zero hW)
        rw [hbot] at hS2
        simp at hS2
      · exact (not_isL2Gp_of_isSpGp_or_isPSUGp hm hn hY n'
          (isL2Gp_of_isL2WrSymGp_one hW)).elim
    · exact (g4 X S hS hS2 (Or.inr ⟨n', m', hm2, hW⟩) hc).elim

end CFSG.LocalAnalysis.WeakClosure81

end
