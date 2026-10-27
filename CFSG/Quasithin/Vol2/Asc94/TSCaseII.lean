module

public import CFSG.Quasithin.Vol2.Asc94.TSCaseLM
public import CFSG.Quasithin.Vol2.Asc94.TSFrame4
public import CFSG.Quasithin.Vol2.Asc94.TS40e
public import CFSG.Quasithin.Vol2.Asc94.TS40h
public import CFSG.Quasithin.Vol2.Asc94.TSFrame5
public import CFSG.Quasithin.Vol2.Asc94.Defs

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.CGT.M24S CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {z : G}

theorem caseII_both (hF6 : L52.F6Model) {e : ↥(Cz z) ≃* L52.Hc} (S : Setting G z e)
    (h1 : Subgroup.normalizer (tr e L52.U1 : Set G) = Cz z)
    (h2 : Subgroup.normalizer (tr e L52.U2 : Set G) = Cz z) :
    (∀ u ∈ tr e L52.U1, u ≠ 1 → InZG z u) ∧ (∀ u ∈ tr e L52.U2, u ≠ 1 → InZG z u) := by
  have hz := S.ord
  have hU : (frame3 e hz hF6).U = tr e L52.U1 := rfl
  have hU2 : (frame3 e hz hF6).U2 = tr e L52.U2 := rfl
  have hU' : (frame3 (swapIso e) hz hF6).U = tr e L52.U2 := tr_swap_U1 e
  have hU2' : (frame3 (swapIso e) hz hF6).U2 = tr e L52.U1 := tr_swap_U2 e
  rcases s39_5 (frame3 e hz hF6).toFrame1 S.notWC with hA | hB
  · by_cases hB : ∀ u ∈ tr e L52.U2, u ≠ 1 → InZG z u
    · exact ⟨hA, hB⟩
    · exfalso
      have := (s39_7 (frame3 e hz hF6) hA hB).2.2
      exact this h1
  · have hB' : ∀ u ∈ (frame3 (swapIso e) hz hF6).U, u ≠ 1 → InZG z u := by
      rw [hU']
      exact hB
    by_cases hA : ∀ u ∈ tr e L52.U1, u ≠ 1 → InZG z u
    · exact ⟨hA, hB⟩
    · exfalso
      have hA' : ¬ ∀ u ∈ (frame3 (swapIso e) hz hF6).U2, u ≠ 1 → InZG z u := by
        rw [hU2']
        exact hA
      have := (s39_7 (frame3 (swapIso e) hz hF6) hB' hA').2.2
      rw [hU'] at this
      exact this h2

@[expose] def Frame5.OmegaFacts (F : Frame5 G z) : Prop :=
  F.Ω.ncard = 18 ∧
    (∀ a ∈ F.Ω, ∀ b ∈ F.Ω, ∃ n ∈ Subgroup.normalizer (F.A : Set G), b = n⁻¹ * a * n) ∧
    (∀ a ∈ F.Ω, ∃ t ∈ F.TQ, ∃ g : G, a = g⁻¹ * t * g) ∧
    (∀ a ∈ F.A, a ≠ 1 → (∃ t ∈ F.TQ, ∃ g : G, a = g⁻¹ * t * g) → a ∈ F.Ω)

theorem caseII_facts (hF6 : L52.F6Model) {e : ↥(Cz z) ≃* L52.Hc} (S : Setting G z e)
    (h1 : Subgroup.normalizer (tr e L52.U1 : Set G) = Cz z)
    (h2 : Subgroup.normalizer (tr e L52.U2 : Set G) = Cz z) :
    (frame4 e S.ord hF6).Gz.ncard = 9 ∧
      Nat.card ↥(Subgroup.normalizer ((frame4 e S.ord hF6).J : Set G)) = 9 * 1024 ∧
      (frame5 e S.ord hF6).Sz.ncard = 45 ∧ (frame5 (swapIso e) S.ord hF6).Sz.ncard = 45 ∧
      (frame5 e S.ord hF6).OmegaFacts ∧ (frame5 (swapIso e) S.ord hF6).OmegaFacts := by
  obtain ⟨hA, hB⟩ := caseII_both hF6 S h1 h2
  have hz := S.ord
  have hU' : (frame4 (swapIso e) hz hF6).U = tr e L52.U2 := tr_swap_U1 e
  have hU2' : (frame4 (swapIso e) hz hF6).U2 = tr e L52.U1 := tr_swap_U2 e
  have hA' : ∀ u ∈ (frame4 (swapIso e) hz hF6).U, u ≠ 1 → InZG z u := by
    rw [hU']
    exact hB
  have hB' : ∀ u ∈ (frame4 (swapIso e) hz hF6).U2, u ≠ 1 → InZG z u := by
    rw [hU2']
    exact hA
  have h2' : Subgroup.normalizer ((frame4 (swapIso e) hz hF6).U : Set G) = Cz z := by
    rw [hU']
    exact h2
  obtain ⟨c1, c2, -⟩ := s40_1 (frame4 e hz hF6) hA hB
  have n1 : (frame4 e hz hF6).Sz.ncard = 45 := by
    rcases s40_2_card (frame4 e hz hF6) hA hB with h | h
    · exact absurd h (fun h21 => Frame3.false_of_card_21 (frame4 e hz hF6).toFrame3 hA hB h1 h21)
    · exact h
  have n2 : (frame4 (swapIso e) hz hF6).Sz.ncard = 45 := by
    rcases s40_2_card (frame4 (swapIso e) hz hF6) hA' hB' with h | h
    · exact absurd h (fun h21 =>
        Frame3.false_of_card_21 (frame4 (swapIso e) hz hF6).toFrame3 hA' hB' h2' h21)
    · exact h
  exact ⟨c1, c2, n1, n2, s40_2_T (frame5 e hz hF6) hA hB n1, s40_2_T (frame5 (swapIso e) hz hF6) hA' hB' n2⟩

end CFSG.Quasithin.A94
