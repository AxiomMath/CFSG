module

public import CFSG.Timmesfeld.Transvection.OddResidueOrder
import CFSG.Timmesfeld.Transvection.OddResidueBlockPrev
import CFSG.Timmesfeld.Transvection.OddSU3Torus
import CFSG.Timmesfeld.Transvection.HyperbolicLine
import CFSG.Timmesfeld.Transvection.LineConjugates
import CFSG.Combinatorics.QuadrangleGraphThasEq
public import CFSG.Timmesfeld.Transvection.OddSU3Chord

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LocalAnalysis.UniquenessCase CFSG.LieType.CurtisTits CFSG.LieType.BorelTits
open CFSG.Timmesfeld.Transvection.Pres CFSG.Combinatorics.QuadrangleGraph

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r}

section Certificates


private theorem ncard_commuting_frameResidue_eq (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) {i : Fin r} (hik : i ≠ k) {M : Subgroup H}
    (hM : M ∈ frameResidue Δ P Q i) (hMl : M ∉ lineOf Δ (P i) (Q i)) :
    {X | X ∈ frameResidue Δ P Q k ∧ Commuting M X}.ncard = Nat.card (P k) + 1 := by
  classical
  haveI : Finite H := h.finite
  letI : Fintype ↥(rankTwoResidue Δ P Q i k) := Fintype.ofFinite _
  let adj := residueAdj Δ P Q i k
  let x : ↥(rankTwoResidue Δ P Q i k) :=
    ⟨P i, hF.toIsFrame.memP_rankTwoResidue_left i k⟩
  let y : ↥(rankTwoResidue Δ P Q i k) :=
    ⟨Q i, hF.toIsFrame.memQ_rankTwoResidue_left i k⟩
  let w : ↥(rankTwoResidue Δ P Q i k) :=
    ⟨M, frameResidue_subset_rankTwoResidue_left i k hM⟩
  have hO : IsQuadrangleOfOrder adj (Nat.card (P k) ^ 2) (Nat.card (P k) ^ 3) :=
    hF.isQuadrangleOfOrder_residueAdj h hML hq hik hns
  have hp : (span2 adj x y).card = Nat.card (P k) + 1 :=
    hF.card_span2_residueAdj h hML hq hik hns
  have hspan : Subtype.val '' (↑(span2 adj x y) : Set ↥(rankTwoResidue Δ P Q i k)) =
      lineOf Δ (P i) (Q i) :=
    hF.image_span2_residueAdj_eq_lineOf h hML hq hik hns
  have hxy : ¬ adj x y :=
    ModelRank.not_commuting_of_opposite (hF.opposite i)
  have hq4 : 4 ≤ Nat.card (P k) := hq _ (hF.memP k)
  have ht : 1 ≤ Nat.card (P k) ^ 3 :=
    Nat.succ_le_of_lt (pow_pos (by omega : 0 < Nat.card (P k)) 3)
  have hwu : ∀ u ∈ span2 adj x y, ¬ adj w u := by
    intro u hu
    have huLine : (u : Subgroup H) ∈ lineOf Δ (P i) (Q i) := by
      rw [← hspan]
      exact ⟨u, hu, rfl⟩
    have huR : (u : Subgroup H) ∈ frameResidue Δ P Q i :=
      hF.toIsFrame.lineOf_subset_frameResidue i huLine
    have hne : (u : Subgroup H) ≠ M := by
      intro hEq
      exact hMl (hEq ▸ huLine)
    exact ModelRank.not_commuting_of_opposite
      (hF.opposite_of_mem_frameResidue h.cls hML hM huR hne.symm)
  have hT : Nat.card (P k) * ((perp2 adj x y).filter (adj w)).card =
      Nat.card (P k) ^ 2 + Nat.card (P k) :=
    hO.mul_card_filter_adj_eq ht hxy hp (by ring) hwu
  let T := (perp2 adj x y).filter (adj w)
  have hTcard : T.card = Nat.card (P k) + 1 := by
    have hqpos : 0 < Nat.card (P k) := by omega
    refine Nat.eq_of_mul_eq_mul_left hqpos ?_
    calc Nat.card (P k) * T.card = Nat.card (P k) ^ 2 + Nat.card (P k) := hT
      _ = Nat.card (P k) * (Nat.card (P k) + 1) := by ring
  let S : Set (Subgroup H) := {X | X ∈ frameResidue Δ P Q k ∧ Commuting M X}
  have hS : S = Subtype.val '' (↑T : Set ↥(rankTwoResidue Δ P Q i k)) := by
    ext X
    constructor
    · intro hX
      have hXr : X ∈ rankTwoResidue Δ P Q i k :=
        frameResidue_subset_rankTwoResidue_right i k hX.1
      refine ⟨⟨X, hXr⟩, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [mem_perp2]
        exact ⟨(hX.1.2 i hik).1, (hX.1.2 i hik).2⟩
      · simpa [adj, w, residueAdj] using hX.2
    · rintro ⟨u, hu, rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter, mem_perp2] at hu
      refine ⟨mem_frameResidue_of_mem_rankTwoResidue_right u.2 hu.1.1 hu.1.2, ?_⟩
      simpa [adj, w, residueAdj] using hu.2
  have hS_card : S.ncard = Nat.card (P k) + 1 := by
    rw [hS, Set.ncard_image_of_injective _ Subtype.coe_injective, Set.ncard_coe_finset]
    exact hTcard
  exact hS_card

theorem IsMaxFrame.setOf_commuting_frameResidue_eq_lineOf (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) {i : Fin r} (hik : i ≠ k) {M : Subgroup H}
    (hM : M ∈ frameResidue Δ P Q i) (hMl : M ∉ lineOf Δ (P i) (Q i)) :
    {X | X ∈ frameResidue Δ P Q k ∧ Commuting M X} = lineOf Δ (P k) (Q k) := by
  classical
  haveI : Finite H := h.finite
  have hS_card : {X | X ∈ frameResidue Δ P Q k ∧ Commuting M X}.ncard =
      Nat.card (P k) + 1 :=
    ncard_commuting_frameResidue_eq h hML hq hF hns hik hM hMl
  have hsub : lineOf Δ (P k) (Q k) ⊆ {X | X ∈ frameResidue Δ P Q k ∧ Commuting M X} := by
    intro X hX
    exact ⟨hF.toIsFrame.lineOf_subset_frameResidue k hX,
      hX.2 M hM.1 (hM.2 k hik.symm).1 (hM.2 k hik.symm).2⟩
  have hline_ge : Nat.card (P k) + 1 ≤ (lineOf Δ (P k) (Q k)).ncard := by
    calc Nat.card (P k) + 1 =
        (insert (Q k) ((fun b => conjSub (P k) b) '' (Q k : Set H))).ncard :=
          (ncard_insert_image_conjSub h.cls (hF.memP k) (hF.memQ k) (hF.opposite k)).symm
      _ ≤ (lineOf Δ (P k) (Q k)).ncard :=
          Set.ncard_le_ncard
            (insert_image_conjSub_subset_lineOf h.cls (hF.memP k) (hF.memQ k))
            (Set.toFinite _)
  exact (Set.eq_of_subset_of_ncard_le hsub (hS_card.trans_le hline_ge)).symm

theorem IsMaxFrame.exists_mem_frameResidue_not_mem_lineOf (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) {i : Fin r} (hik : i ≠ k) :
    ∃ M ∈ frameResidue Δ P Q i, M ∉ lineOf Δ (P i) (Q i) := by
  classical
  have hi : ¬ IsSmallFrame Δ P Q i :=
    hF.not_isSmallFrame_of_ne h hML hq hik.symm hns
  rw [isSmallFrame_iff hF.toIsFrame] at hi
  push Not at hi
  obtain ⟨M, hM, hMle⟩ := hi
  refine ⟨M, hM, ?_⟩
  intro hMl
  exact hMle ((lineOf_eq_of_opposite h hML hq (hF.memP i) (hF.memQ i) (hF.opposite i)).2 M hMl)

section Field

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem IsMaxFrame.mem_of_mem_map_heis_of_conjSub_eq (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q k) (hθk : Odd (Nat.card θ.ker))
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    {i : Fin r} (hik : i ≠ k) {M : Subgroup H} (hM : M ∈ frameResidue Δ P Q i)
    (hMl : M ∉ lineOf Δ (P i) (Q i)) {b : H}
    (hb : b ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hbM : conjSub M b = M) : b ∈ P k := by
  classical
  haveI : Finite H := h.finite
  let B : Subgroup H := (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ
  have hbB : b ∈ B := hb
  have hB_le : B ≤ residueGroup Δ P Q k := by
    simpa [B, hθr] using
      Subgroup.map_le_range θ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn))
  let X : Subgroup H := conjSub (Q k) b
  have hXR : X ∈ frameResidue Δ P Q k :=
    conjSub_mem_frameResidue h.cls (hF.toIsFrame.memQ_frameResidue k) (hB_le hbB)
  have hXM : Commuting M X := by
    have h := (hM.2 k hik.symm).2.conjSub b
    simpa [X, hbM] using h
  have hXP : X ≠ P k := by
    have hPb : conjSub (P k) b = P k :=
      conjSub_eq_of_mem_map_heis (unitaryInvolution_involutive hFn) hθt hb
    intro hXeq
    exact (hF.opposite k).ne (conjSub_injective b (hPb.trans hXeq.symm))
  have hPkB : P k ≤ B := by
    rw [← hθt]
    exact Subgroup.map_mono (su3Top_le_X (unitaryInvolution_involutive hFn))
  have hXline : X ∈ lineOf Δ (P k) (Q k) := by
    rw [← hF.setOf_commuting_frameResidue_eq_lineOf h hML hq hns hik hM hMl]
    exact ⟨hXR, hXM⟩
  rw [lineOf_comm,
    (lineOf_eq_of_opposite h hML hq (hF.memQ k) (hF.memP k) (hF.opposite k).symm).1] at hXline
  rcases Set.mem_insert_iff.1 hXline with hXeq | hXa
  · exact absurd hXeq hXP
  · obtain ⟨a, haP, haX⟩ := hXa
    have huniq := hF.existsUnique_conjSub_heis (X := X) h hML hq hns hFn hcard hθr hθk
      hθt hθb hmem hXR hXP
    have hba : b = a := huniq.unique ⟨hb, rfl⟩ ⟨hPkB haP, haX⟩
    rw [hba]
    exact haP

end Field

end Certificates

end CFSG.Timmesfeld.Transvection
