module

public import CFSG.Timmesfeld.Transvection.RankTwoResidue
public import CFSG.Combinatorics.QuadrangleGraph

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Combinatorics.QuadrangleGraph

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)}

@[expose] def residueAdj (Δ : Set (Subgroup H)) {r : ℕ} (P Q : Fin r → Subgroup H) (j k : Fin r)
    (a b : ↥(rankTwoResidue Δ P Q j k)) : Prop :=
  Commuting (a : Subgroup H) (b : Subgroup H)

variable {r : ℕ} {P Q : Fin r → Subgroup H}

theorem residueAdj_iff {j k : Fin r} {a b : ↥(rankTwoResidue Δ P Q j k)} :
    residueAdj Δ P Q j k a b ↔ Commuting (a : Subgroup H) (b : Subgroup H) :=
  Iff.rfl

theorem IsMaxFrame.isQuadrangle_residueAdj [Finite H] (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) (j k : Fin r) :
    IsQuadrangle (residueAdj Δ P Q j k) where
  refl x := hΔ.root.commuting_self x.2.1
  symm h := h.symm
  clique := by
    intro x y u v hxy hadj hux huy hvx hvy
    have hne : (x : Subgroup H) ≠ (y : Subgroup H) := fun e => hxy (Subtype.ext e)
    have hu :=
      hF.mem_lineOf_of_mem_rankTwoResidue hΔ hpts hML x.2 y.2 hne hadj u.2 hux huy
    have hv :=
      hF.mem_lineOf_of_mem_rankTwoResidue hΔ hpts hML x.2 y.2 hne hadj v.2 hvx hvy
    exact commuting_of_mem_lineOf_of_mem_lineOf hΔ x.2.1 y.2.1 hadj hu hv
  meets := by
    intro x y z hxy hadj
    have hne : (x : Subgroup H) ≠ (y : Subgroup H) := fun e => hxy (Subtype.ext e)
    obtain ⟨D, hD, hzD⟩ := hML x x.2.1 y y.2.1 hne hadj z z.2.1
    have hc := commuting_of_mem_lineOf' hΔ x.2.1 y.2.1 hadj hD
    exact ⟨⟨D, hF.toIsFrame.lineOf_subset_rankTwoResidue x.2 y.2 hD⟩,
      hc.1.symm, hc.2.symm, hzD⟩

theorem IsFrame.exists_third_mem_frameResidue (hF : IsFrame Δ P Q) (hΔ : IsTransvectionClass Δ)
    (k : Fin r) : ∃ X ∈ frameResidue Δ P Q k, X ≠ P k ∧ X ≠ Q k := by
  obtain ⟨x, hx, hx1⟩ := hΔ.root.exists_ne_one (hF.memQ k)
  have hxL : x ∈ residueGroup Δ P Q k :=
    le_iSup₂_of_le (f := fun X _ => X) (Q k) (hF.memQ_frameResidue k) le_rfl hx
  refine ⟨conjSub (P k) x, conjSub_mem_frameResidue hΔ (hF.memP_frameResidue k) hxL, ?_, ?_⟩
  · intro e
    exact hx1 ((hF.opposite k).symm.eq_one_of_conjSub_eq hx e)
  · intro e
    refine (hF.opposite k).ne (conjSub_injective x ?_)
    show conjSub (P k) x = conjSub (Q k) x
    rw [e, conjSub_of_mem hx]

theorem IsFrame.two_lt_card_perp2_left (hF : IsFrame Δ P Q) (hΔ : IsTransvectionClass Δ)
    {j k : Fin r} (hjk : j ≠ k) [Fintype ↥(rankTwoResidue Δ P Q j k)] :
    2 < (perp2 (residueAdj Δ P Q j k) ⟨P j, hF.memP_rankTwoResidue_left j k⟩
      ⟨Q j, hF.memQ_rankTwoResidue_left j k⟩).card := by
  obtain ⟨X, hX, hXP, hXQ⟩ := hF.exists_third_mem_frameResidue hΔ k
  have hXR : X ∈ rankTwoResidue Δ P Q j k :=
    frameResidue_subset_rankTwoResidue_right j k hX
  refine Finset.two_lt_card_iff.2
    ⟨⟨P k, hF.memP_rankTwoResidue_right j k⟩,
      ⟨Q k, hF.memQ_rankTwoResidue_right j k⟩, ⟨X, hXR⟩, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
  · exact mem_perp2.2 ⟨hF.commuting_PP (Ne.symm hjk), hF.commuting_PQ (Ne.symm hjk)⟩
  · exact mem_perp2.2 ⟨hF.commuting_QP (Ne.symm hjk), hF.commuting_QQ (Ne.symm hjk)⟩
  · exact mem_perp2.2 (by simpa only [residueAdj_iff] using hX.2 j hjk)
  · intro e
    exact (hF.opposite k).ne (congrArg Subtype.val e)
  · intro e
    exact hXP (congrArg Subtype.val e).symm
  · intro e
    exact hXQ (congrArg Subtype.val e).symm

theorem IsFrame.two_lt_card_perp2_right (hF : IsFrame Δ P Q) (hΔ : IsTransvectionClass Δ)
    {j k : Fin r} (hjk : j ≠ k) [Fintype ↥(rankTwoResidue Δ P Q j k)] :
    2 < (perp2 (residueAdj Δ P Q j k) ⟨P k, hF.memP_rankTwoResidue_right j k⟩
      ⟨Q k, hF.memQ_rankTwoResidue_right j k⟩).card := by
  obtain ⟨Y, hY, hYP, hYQ⟩ := hF.exists_third_mem_frameResidue hΔ j
  have hYR : Y ∈ rankTwoResidue Δ P Q j k :=
    frameResidue_subset_rankTwoResidue_left j k hY
  refine Finset.two_lt_card_iff.2
    ⟨⟨P j, hF.memP_rankTwoResidue_left j k⟩,
      ⟨Q j, hF.memQ_rankTwoResidue_left j k⟩, ⟨Y, hYR⟩, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
  · exact mem_perp2.2 ⟨hF.commuting_PP hjk, hF.commuting_PQ hjk⟩
  · exact mem_perp2.2 ⟨hF.commuting_QP hjk, hF.commuting_QQ hjk⟩
  · exact mem_perp2.2 (by simpa only [residueAdj_iff] using hY.2 k (Ne.symm hjk))
  · intro e
    exact (hF.opposite j).ne (congrArg Subtype.val e)
  · intro e
    exact hYP (congrArg Subtype.val e).symm
  · intro e
    exact hYQ (congrArg Subtype.val e).symm

theorem IsMaxFrame.isThickQuadrangle_residueAdj [Finite H] (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hML : MeetsLines Δ) (hthick : ThickLines Δ)
    (hF : IsMaxFrame Δ P Q) {j k : Fin r} (hjk : j ≠ k) :
    IsThickQuadrangle (residueAdj Δ P Q j k) := by
  classical
  letI : Fintype ↥(rankTwoResidue Δ P Q j k) := Fintype.ofFinite _
  refine (hF.isQuadrangle_residueAdj hΔ hpts hML j k).isThickQuadrangle_of_base ?_ ?_
  · intro x y hxy hadj
    have hne : (x : Subgroup H) ≠ (y : Subgroup H) := fun e => hxy (Subtype.ext e)
    obtain ⟨C, hC, hCx, hCy⟩ := thickLines_iff.1 hthick x x.2.1 y y.2.1 hne hadj
    obtain ⟨hcCx, hcCy⟩ := commuting_of_mem_lineOf' hΔ x.2.1 y.2.1 hadj hC
    exact ⟨⟨C, hF.toIsFrame.lineOf_subset_rankTwoResidue x.2 y.2 hC⟩,
      hcCx.symm, hcCy.symm, fun e => hCx (congrArg Subtype.val e),
      fun e => hCy (congrArg Subtype.val e)⟩
  · intro x
    by_cases hPj : Commuting (x : Subgroup H) (P j)
    · by_cases hQj : Commuting (x : Subgroup H) (Q j)
      · by_cases hPk : Commuting (x : Subgroup H) (P k)
        · by_cases hQk : Commuting (x : Subgroup H) (Q k)
          · exact (hF.maximal x x.2.1 fun i => by
              by_cases hij : i = j
              · subst hij
                exact ⟨hPj, hQj⟩
              · by_cases hik : i = k
                · subst hik
                  exact ⟨hPk, hQk⟩
                · exact x.2.2 i hij hik).elim
          · exact ⟨⟨Q k, hF.toIsFrame.memQ_rankTwoResidue_right j k⟩, hQk,
              ⟨⟨P k, hF.toIsFrame.memP_rankTwoResidue_right j k⟩,
                ModelRank.not_commuting_of_opposite (hF.opposite k).symm,
                by rw [perp2_comm]
                   exact hF.toIsFrame.two_lt_card_perp2_right hΔ hjk⟩⟩
        · exact ⟨⟨P k, hF.toIsFrame.memP_rankTwoResidue_right j k⟩, hPk,
            ⟨⟨Q k, hF.toIsFrame.memQ_rankTwoResidue_right j k⟩,
              ModelRank.not_commuting_of_opposite (hF.opposite k),
              hF.toIsFrame.two_lt_card_perp2_right hΔ hjk⟩⟩
      · exact ⟨⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩, hQj,
          ⟨⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩,
            ModelRank.not_commuting_of_opposite (hF.opposite j).symm,
            by rw [perp2_comm]
               exact hF.toIsFrame.two_lt_card_perp2_left hΔ hjk⟩⟩
    · exact ⟨⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩, hPj,
        ⟨⟨Q j, hF.toIsFrame.memQ_rankTwoResidue_left j k⟩,
          ModelRank.not_commuting_of_opposite (hF.opposite j),
          hF.toIsFrame.two_lt_card_perp2_left hΔ hjk⟩⟩

theorem IsFrame.image_perp2_residueAdj_PQ (hF : IsFrame Δ P Q) {j k : Fin r}
    (hjk : j ≠ k) [Fintype ↥(rankTwoResidue Δ P Q j k)] :
    Subtype.val '' (↑(perp2 (residueAdj Δ P Q j k)
        ⟨P k, hF.memP_rankTwoResidue_right j k⟩
        ⟨Q k, hF.memQ_rankTwoResidue_right j k⟩) : Set ↥(rankTwoResidue Δ P Q j k)) =
      frameResidue Δ P Q j := by
  ext X
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Finset.mem_coe, mem_perp2] at ha
    exact mem_frameResidue_of_mem_rankTwoResidue_left a.2 ha.1 ha.2
  · intro hX
    refine ⟨⟨X, frameResidue_subset_rankTwoResidue_left j k hX⟩, ?_, rfl⟩
    rw [Finset.mem_coe, mem_perp2]
    exact hX.2 k (Ne.symm hjk)

theorem IsFrame.image_perp2_residueAdj_PQ_left (hF : IsFrame Δ P Q) {j k : Fin r}
    (hjk : j ≠ k) [Fintype ↥(rankTwoResidue Δ P Q j k)] :
    Subtype.val '' (↑(perp2 (residueAdj Δ P Q j k) ⟨P j, hF.memP_rankTwoResidue_left j k⟩
      ⟨Q j, hF.memQ_rankTwoResidue_left j k⟩) : Set ↥(rankTwoResidue Δ P Q j k)) =
      frameResidue Δ P Q k := by
  ext X
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Finset.mem_coe, mem_perp2] at ha
    exact mem_frameResidue_of_mem_rankTwoResidue_right a.2 ha.1 ha.2
  · intro hX
    refine ⟨⟨X, frameResidue_subset_rankTwoResidue_right j k hX⟩, ?_, rfl⟩
    rw [Finset.mem_coe, mem_perp2]
    exact hX.2 j hjk

theorem IsFrame.card_perp2_residueAdj_PQ_left (hF : IsFrame Δ P Q) {j k : Fin r} (hjk : j ≠ k)
    [Fintype ↥(rankTwoResidue Δ P Q j k)] :
    (perp2 (residueAdj Δ P Q j k) ⟨P j, hF.memP_rankTwoResidue_left j k⟩
      ⟨Q j, hF.memQ_rankTwoResidue_left j k⟩).card = (frameResidue Δ P Q k).ncard := by
  rw [← IsFrame.image_perp2_residueAdj_PQ_left hF hjk,
    Set.ncard_image_of_injective _ Subtype.coe_injective, Set.ncard_coe_finset]

theorem IsFrame.card_perp2_residueAdj_PQ (hF : IsFrame Δ P Q) {j k : Fin r} (hjk : j ≠ k)
    [Fintype ↥(rankTwoResidue Δ P Q j k)] :
    (perp2 (residueAdj Δ P Q j k) ⟨P k, hF.memP_rankTwoResidue_right j k⟩
      ⟨Q k, hF.memQ_rankTwoResidue_right j k⟩).card = (frameResidue Δ P Q j).ncard := by
  rw [← IsFrame.image_perp2_residueAdj_PQ hF hjk,
    Set.ncard_image_of_injective _ Subtype.coe_injective, Set.ncard_coe_finset]

theorem IsMaxFrame.image_perp2_residueAdj_eq_lineOf [Finite H] (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) {j k : Fin r}
    [Fintype ↥(rankTwoResidue Δ P Q j k)] {X Y : Subgroup H}
    (hX : X ∈ rankTwoResidue Δ P Q j k) (hY : Y ∈ rankTwoResidue Δ P Q j k) (hXY : X ≠ Y)
    (hc : Commuting X Y) :
    Subtype.val '' (↑(perp2 (residueAdj Δ P Q j k) ⟨X, hX⟩ ⟨Y, hY⟩) :
      Set ↥(rankTwoResidue Δ P Q j k)) = lineOf Δ X Y := by
  ext W
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Finset.mem_coe, mem_perp2] at ha
    exact hF.mem_lineOf_of_mem_rankTwoResidue hΔ hpts hML hX hY hXY hc a.2 ha.1 ha.2
  · intro hW
    have hWR : W ∈ rankTwoResidue Δ P Q j k :=
      hF.toIsFrame.lineOf_subset_rankTwoResidue hX hY hW
    refine ⟨⟨W, hWR⟩, ?_, rfl⟩
    rw [Finset.mem_coe, mem_perp2]
    exact ⟨(commuting_of_mem_lineOf' hΔ hX.1 hY.1 hc hW).1.symm,
      (commuting_of_mem_lineOf' hΔ hX.1 hY.1 hc hW).2.symm⟩

theorem IsMaxFrame.card_perp2_residueAdj_PP [Finite H] (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) {j k : Fin r}
    (hjk : j ≠ k) [Fintype ↥(rankTwoResidue Δ P Q j k)] :
    (perp2 (residueAdj Δ P Q j k) ⟨P j, hF.toIsFrame.memP_rankTwoResidue_left j k⟩
      ⟨P k, hF.toIsFrame.memP_rankTwoResidue_right j k⟩).card =
      (lineOf Δ (P j) (P k)).ncard := by
  rw [← hF.image_perp2_residueAdj_eq_lineOf hΔ hpts hML
      (hF.toIsFrame.memP_rankTwoResidue_left j k)
      (hF.toIsFrame.memP_rankTwoResidue_right j k)
      (hF.toIsFrame.P_ne hjk) (hF.toIsFrame.commuting_PP hjk),
    Set.ncard_image_of_injective _ Subtype.coe_injective, Set.ncard_coe_finset]

theorem IsFrame.lineOf_subset_image_span2 (hF : IsFrame Δ P Q) (j k : Fin r)
    [Fintype ↥(rankTwoResidue Δ P Q j k)] :
    lineOf Δ (P j) (Q j) ⊆
      Subtype.val '' (↑(span2 (residueAdj Δ P Q j k)
        ⟨P j, hF.memP_rankTwoResidue_left j k⟩
        ⟨Q j, hF.memQ_rankTwoResidue_left j k⟩) : Set ↥(rankTwoResidue Δ P Q j k)) := by
  intro D hD
  have hDR : D ∈ rankTwoResidue Δ P Q j k :=
    ⟨hD.1, fun i hij _ =>
      ⟨(hD.2 (P i) (hF.memP i) (hF.commuting_PP hij) (hF.commuting_PQ hij)).symm,
        (hD.2 (Q i) (hF.memQ i) (hF.commuting_QP hij) (hF.commuting_QQ hij)).symm⟩⟩
  refine ⟨⟨D, hDR⟩, ?_, rfl⟩
  rw [Finset.mem_coe, mem_span2]
  intro w hwP hwQ
  exact (hD.2 w w.2.1 hwP hwQ).symm

theorem IsFrame.ncard_lineOf_le_card_span2 (hF : IsFrame Δ P Q) (j k : Fin r)
    [Fintype ↥(rankTwoResidue Δ P Q j k)] :
    (lineOf Δ (P j) (Q j)).ncard ≤
      (span2 (residueAdj Δ P Q j k) ⟨P j, hF.memP_rankTwoResidue_left j k⟩
        ⟨Q j, hF.memQ_rankTwoResidue_left j k⟩).card := by
  calc (lineOf Δ (P j) (Q j)).ncard
      ≤ (Subtype.val '' (↑(span2 (residueAdj Δ P Q j k)
          ⟨P j, hF.memP_rankTwoResidue_left j k⟩
          ⟨Q j, hF.memQ_rankTwoResidue_left j k⟩) :
            Set ↥(rankTwoResidue Δ P Q j k))).ncard :=
        Set.ncard_le_ncard (IsFrame.lineOf_subset_image_span2 hF j k)
          ((Finset.finite_toSet _).image _)
    _ = (span2 (residueAdj Δ P Q j k) ⟨P j, hF.memP_rankTwoResidue_left j k⟩
          ⟨Q j, hF.memQ_rankTwoResidue_left j k⟩).card := by
        rw [Set.ncard_image_of_injective _ Subtype.coe_injective, Set.ncard_coe_finset]

end CFSG.Timmesfeld.Transvection
