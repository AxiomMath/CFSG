module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.Yardstones.Md0ec50421ce4

open CFSG.Open

variable {G : Type} [Group G]

theorem centMod_of_mem_centralizer {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (L : Set G)) : CentMod p L g := by
  refine ⟨Subgroup.centralizer_le_normalizer _ hg, ?_⟩
  have h : (⁅L, Subgroup.zpowers g⁆ : Subgroup G) = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer,
      Subgroup.zpowers_le]
    exact hg
  rw [h]
  exact bot_le

theorem sStar_of_sStarMax [Finite G] {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) (hq : IsQuasisimple L) : GLASStar p B x L := by
  obtain ⟨⟨⟨⟨hB, ⟨hxB, hx1, -⟩, hL⟩, -⟩, -, -⟩, hcyc⟩ := h
  exact ⟨hB, hxB, hx1, ⟨hL.1, hL.2.1, hq⟩, fun S hS hpS =>
    hcyc S (fun g hg => centMod_of_mem_centralizer (hS hg)) hpS⟩

theorem clause4_of_essential {p : ℕ} {B : Subgroup G} {x : G} (h : IsEssential p B x) :
    ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥ := by
  obtain ⟨-, -, T, hT, h2, hN, hTB, -⟩ := h
  exact ⟨T, hT, h2, hN, hTB⟩

theorem theorem_a_of_yardstones (h01 : YS01) (h02 : YS02) (h03 : YS03) (h04 : YS04)
    (h05 : YS05) (h06 : YS06) (h07 : YS07) (h08 : YS08) (h09 : YS09) (h10 : YS10)
    (h11 : YS11) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) → IsKProper G → IsCharTwoType G → 4 ≤ evenRank G →
      ∀ m : ℕ, 4 ≤ m →
        (∀ q ∈ GLABeta (m + 1) G, GLAWeakCoreLocal G q) →
        (∀ q ∈ GLABeta m G, GLAWeakCoreLocal G q ∨ GLADeltaZero G q) →
        (∃ q ∈ GLABeta m G, GLATwoLocalRank q G = m ∧ GLADeltaZero G q) →
        ∃ p ∈ GLABeta m G, GLATwoLocalRank p G = m ∧ GLADeltaZero G p ∧
          ((p = 3 ∧ GLAGF2Type G) ∨
            ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
              GLASStar p B x L ∧ GLAStandardType p B x L) := by
  intro G _ _ _ hnonab hK hchar he m hm ha hb hc
  have hyp : ThmAHyp G m := ⟨inferInstance, hnonab, hK, hchar, he, hm, ha, hb, hc⟩
  by_cases hI : 3 ∈ Mu G m ∧ GLAGF2Type G
  · exact ⟨3, hI.1.1, hI.1.2.1, hI.1.2.2, Or.inl ⟨rfl, hI.2⟩⟩
  have ctx : ThmACtx G m := ⟨hyp, hI⟩
  have facts : StageFacts G m := by
    intro q hq
    have s3 := h01 G m ctx q hq
    have s4o := h02 G m ctx q hq s3
    have s4 := h03 G m ctx q hq s3 s4o
    have s5 := h04 G m ctx q hq s3 s4o s4
    obtain ⟨s6, s7⟩ := h05 G m ctx q hq s3 s4o s4 s5
    have s8 := h06 G m ctx q hq s3 s4o s4 s5 s6 s7
    have s9 := h07 G m ctx q hq s3 s4o s4 s5 s6 s7 s8
    exact ⟨s3, s4o, s4, s5, s6, s7, s8, s9, fun B x L hBxL =>
      h08 L (s9.1 B x L hBxL).1 (s9.1 B x L hBxL).2⟩
  by_cases hi : ∀ q ∈ Mu G m, ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
      IsSStarMax q B x L ∧ InnerDiagMarking B L
  swap
  · have hne : ∃ q ∈ Mu G m, ¬ ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
        IsSStarMax q B x L ∧ InnerDiagMarking B L := by
      by_contra hcon
      exact hi fun q hq => by_contra fun hq' => hcon ⟨q, hq, hq'⟩
    obtain ⟨q, hq, hqi⟩ := hne
    rcases h09 G m ctx facts q hq with h | ⟨rfl, B, x, L, hS, hT, -⟩
    · exact absurd h hqi
    · exact ⟨3, hq.1, hq.2.1, hq.2.2, Or.inr ⟨B, x, L, hS, hT⟩⟩
  obtain ⟨h11f, p, hp, B, x, L, hmax, hmark⟩ := h10 G m ctx facts hi
  obtain ⟨-, -, -, -, -, -, -, s9, -⟩ := facts p hp
  have hq : IsQuasisimple L := (s9.1 B x L hmax).1
  have hess : IsEssential p B x := hmax.1.1.1.2.1
  obtain ⟨h5, h6⟩ := h11 G m ctx facts h11f p hp B x L hmax hmark
  refine ⟨p, hp.1, hp.2.1, hp.2.2, Or.inr ⟨B, x, L, sStar_of_sStarMax hmax hq, ?_⟩⟩
  unfold GLAStandardType
  exact ⟨hmark, clause4_of_essential hess, h5, h6⟩

end CFSG.Yardstones.Md0ec50421ce4
