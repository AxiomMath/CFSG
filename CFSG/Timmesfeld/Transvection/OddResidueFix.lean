module

public import CFSG.Timmesfeld.Transvection.OddResidueOrder
import CFSG.Timmesfeld.Transvection.HyperbolicLine
import CFSG.Combinatorics.QuadrangleGraphFix
import CFSG.Combinatorics.QuadrangleGraphCount

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Combinatorics.QuadrangleGraph

section Group

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)}

@[expose] def rankTwoResidueGroup (Δ : Set (Subgroup H)) {r : ℕ} (P Q : Fin r → Subgroup H)
    (j k : Fin r) : Subgroup H :=
  ⨆ X ∈ rankTwoResidue Δ P Q j k, X

variable {r : ℕ} {P Q : Fin r → Subgroup H}

theorem le_rankTwoResidueGroup {j k : Fin r} {X : Subgroup H}
    (hX : X ∈ rankTwoResidue Δ P Q j k) : X ≤ rankTwoResidueGroup Δ P Q j k :=
  le_iSup₂_of_le X hX le_rfl

theorem residueGroup_le_rankTwoResidueGroup_left (j k : Fin r) :
    residueGroup Δ P Q j ≤ rankTwoResidueGroup Δ P Q j k :=
  iSup₂_le fun _ hX => le_rankTwoResidueGroup (frameResidue_subset_rankTwoResidue_left j k hX)

theorem residueGroup_le_rankTwoResidueGroup_right (j k : Fin r) :
    residueGroup Δ P Q k ≤ rankTwoResidueGroup Δ P Q j k :=
  iSup₂_le fun _ hX => le_rankTwoResidueGroup (frameResidue_subset_rankTwoResidue_right j k hX)

theorem IsFrame.lineGroup_le_rankTwoResidueGroup (hF : IsFrame Δ P Q) {j k : Fin r}
    {X Y : Subgroup H} (hX : X ∈ rankTwoResidue Δ P Q j k) (hY : Y ∈ rankTwoResidue Δ P Q j k) :
    lineGroup Δ X Y ≤ rankTwoResidueGroup Δ P Q j k :=
  iSup₂_le fun _ hC => le_rankTwoResidueGroup (hF.lineOf_subset_rankTwoResidue hX hY hC)

theorem commuting_rankTwoResidueGroup {j k l : Fin r} (hlj : l ≠ j) (hlk : l ≠ k) :
    Commuting (rankTwoResidueGroup Δ P Q j k) (P l ⊔ Q l) := by
  refine Commuting.symm (commuting_iff_le_centralizer.2 (iSup₂_le fun X hX => ?_))
  exact commuting_iff_le_centralizer.1 ((hX.2 l hlj hlk).1.sup_right (hX.2 l hlj hlk).2).symm

theorem conjSub_mem_rankTwoResidue (hΔ : IsTransvectionClass Δ) {j k : Fin r}
    {X : Subgroup H} (hX : X ∈ rankTwoResidue Δ P Q j k) {g : H}
    (hg : g ∈ rankTwoResidueGroup Δ P Q j k) : conjSub X g ∈ rankTwoResidue Δ P Q j k := by
  refine ⟨hΔ.root.conjSub_mem hX.1 g, fun i hij hik => ?_⟩
  have hc := commuting_rankTwoResidueGroup (Δ := Δ) (P := P) (Q := Q) hij hik
  have hfix : ∀ {B : Subgroup H}, B ≤ P i ⊔ Q i → conjSub B g = B := fun hB =>
    conjSub_eq_self_iff.2 (Subgroup.centralizer_le_normalizer _
      (commuting_iff_le_centralizer.1 (hc.mono le_rfl hB).symm hg))
  refine ⟨?_, ?_⟩
  · simpa only [hfix le_sup_left] using (hX.2 i hij hik).1.conjSub g
  · simpa only [hfix le_sup_right] using (hX.2 i hij hik).2.conjSub g

private def rankTwoResidueConj (hΔ : IsTransvectionClass Δ) {j k : Fin r} {g : H}
    (hg : g ∈ rankTwoResidueGroup Δ P Q j k) (X : ↥(rankTwoResidue Δ P Q j k)) :
    ↥(rankTwoResidue Δ P Q j k) :=
  ⟨conjSub (X : Subgroup H) g, conjSub_mem_rankTwoResidue hΔ X.2 hg⟩

private theorem residueAdj_rankTwoResidueConj_iff (hΔ : IsTransvectionClass Δ) {j k : Fin r}
    {g : H} (hg : g ∈ rankTwoResidueGroup Δ P Q j k) (x y : ↥(rankTwoResidue Δ P Q j k)) :
    residueAdj Δ P Q j k (rankTwoResidueConj hΔ hg x) (rankTwoResidueConj hΔ hg y) ↔
      residueAdj Δ P Q j k x y :=
  Aux.commuting_conjSub_iff g

private theorem coe_iterate_rankTwoResidueConj (hΔ : IsTransvectionClass Δ) {j k : Fin r}
    {g : H} (hg : g ∈ rankTwoResidueGroup Δ P Q j k) (m : ℕ)
    (X : ↥(rankTwoResidue Δ P Q j k)) :
    (((rankTwoResidueConj hΔ hg)^[m] X : ↥(rankTwoResidue Δ P Q j k)) : Subgroup H) =
      conjSub (X : Subgroup H) (g ^ m) := by
  induction m with
  | zero => simp [pow_zero]
  | succ m ih =>
      rw [Function.iterate_succ_apply', pow_succ']
      show conjSub (((rankTwoResidueConj hΔ hg)^[m] X : ↥(rankTwoResidue Δ P Q j k)) :
        Subgroup H) g = conjSub (X : Subgroup H) (g * g ^ m)
      rw [ih, conjSub_mul]

private theorem fixesLinesThrough_rankTwoResidueConj (hΔ : IsTransvectionClass Δ)
    (hF : IsFrame Δ P Q) {j k : Fin r} {g : H}
    (hg : g ∈ rankTwoResidueGroup Δ P Q j k) (hgP : conjSub (P j) g = P j)
    (hgl : ∀ C ∈ Δ, C ≠ P j → Commuting (P j) C → g ∈ lineStab Δ (P j) C) :
    FixesLinesThrough (residueAdj Δ P Q j k) (rankTwoResidueConj hΔ hg)
      ⟨P j, hF.memP_rankTwoResidue_left j k⟩ := by
  intro y hy
  show Commuting (conjSub (y : Subgroup H) g) (y : Subgroup H)
  by_cases hyP : (y : Subgroup H) = P j
  · rw [hyP, hgP]
    exact hΔ.root.commuting_self (hF.memP j)
  · have hD : conjSub (y : Subgroup H) g ∈ lineOf Δ (P j) (y : Subgroup H) :=
      ((mem_lineStab_iff.1 (hgl (y : Subgroup H) y.2.1 hyP hy)) (y : Subgroup H)).2
        (right_mem_lineOf y.2.1)
    exact (commuting_of_mem_lineOf' hΔ (hF.memP j) y.2.1 hy hD).2.symm

theorem IsMaxFrame.exists_opposite_mem_rankTwoResidue (hΔ : IsTransvectionClass Δ)
    (hF : IsMaxFrame Δ P Q) {j k : Fin r} {Y : Subgroup H}
    (hY : Y ∈ rankTwoResidue Δ P Q j k) : ∃ X ∈ rankTwoResidue Δ P Q j k, Opposite Y X := by
  by_contra hne
  have h : ∀ X ∈ rankTwoResidue Δ P Q j k, ¬ Opposite Y X := fun X hX ho =>
    hne ⟨X, hX, ho⟩
  have hc : ∀ X ∈ rankTwoResidue Δ P Q j k, Commuting Y X := by
    intro X hX
    by_cases hYX : Y = X
    · subst hYX
      exact hΔ.root.commuting_self hY.1
    · exact (hΔ.commuting_or_opposite hY.1 hX.1 hYX).resolve_right (h X hX)
  exact hF.maximal Y hY.1 fun l => by
    by_cases hlj : l = j
    · rw [hlj]
      exact ⟨hc _ (hF.toIsFrame.memP_rankTwoResidue_left j k),
        hc _ (hF.toIsFrame.memQ_rankTwoResidue_left j k)⟩
    · by_cases hlk : l = k
      · rw [hlk]
        exact ⟨hc _ (hF.toIsFrame.memP_rankTwoResidue_right j k),
          hc _ (hF.toIsFrame.memQ_rankTwoResidue_right j k)⟩
      · exact hY.2 l hlj hlk

theorem IsMaxFrame.commute_of_forall_conjSub_eq (hΔ : IsTransvectionClass Δ)
    (hF : IsMaxFrame Δ P Q) {j k : Fin r} {g : H}
    (hg : ∀ X ∈ rankTwoResidue Δ P Q j k, conjSub X g = X) {Y : Subgroup H}
    (hY : Y ∈ rankTwoResidue Δ P Q j k) {y : H} (hy : y ∈ Y) : Commute g y := by
  obtain ⟨X, hX, hYX⟩ := hF.exists_opposite_mem_rankTwoResidue hΔ hY
  have hy' : g * y * g⁻¹ ∈ Y := by
    rw [← hg Y hY]
    exact conj_mem_conjSub g hy
  have hXy : conjSub X y ∈ rankTwoResidue Δ P Q j k :=
    conjSub_mem_rankTwoResidue hΔ hX (le_rankTwoResidueGroup hY hy)
  have hXg : conjSub X g⁻¹ = X := by
    have h := Aux.conjSub_conjSub_inv X g
    rwa [hg X hX] at h
  have hfix : conjSub X (g * y * g⁻¹) = conjSub X y := by
    rw [mul_assoc, conjSub_mul, conjSub_mul, hXg, hg _ hXy]
  have hX1 : conjSub X (y⁻¹ * (g * y * g⁻¹)) = X := by
    rw [conjSub_mul, hfix, Aux.conjSub_conjSub_inv]
  have h1 : y⁻¹ * (g * y * g⁻¹) = 1 :=
    hYX.eq_one_of_conjSub_eq (Y.mul_mem (Y.inv_mem hy) hy') hX1
  have h2 : g * y * g⁻¹ = y := by
    rw [← mul_inv_cancel_left y (g * y * g⁻¹), h1, mul_one]
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem IsMaxFrame.conjSub_eq_of_mem_frameResidue [Finite H] (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) {k i : Fin r}
    (hik : i ≠ k) {g : H} (hg : g ∈ rankTwoResidueGroup Δ P Q k i)
    (hgP : conjSub (P k) g = P k) (hgQ : conjSub (Q k) g = Q k)
    (hgl : ∀ C ∈ Δ, C ≠ P k → Commuting (P k) C → g ∈ lineStab Δ (P k) C) {X : Subgroup H}
    (hX : X ∈ frameResidue Δ P Q i) : conjSub X g = X := by
  classical
  letI : Fintype ↥(rankTwoResidue Δ P Q k i) := Fintype.ofFinite _
  have hGQ : IsQuadrangle (residueAdj Δ P Q k i) :=
    hF.isQuadrangle_residueAdj hΔ hpts hML k i
  let a : ↥(rankTwoResidue Δ P Q k i) := ⟨P k, hF.toIsFrame.memP_rankTwoResidue_left k i⟩
  let q : ↥(rankTwoResidue Δ P Q k i) := ⟨Q k, hF.toIsFrame.memQ_rankTwoResidue_left k i⟩
  have haq : ¬ residueAdj Δ P Q k i a q := ModelRank.not_commuting_of_opposite (hF.opposite k)
  have hfa : rankTwoResidueConj hΔ hg a = a := Subtype.ext hgP
  have hfq : rankTwoResidueConj hΔ hg q = q := Subtype.ext hgQ
  have ha : FixesLinesThrough (residueAdj Δ P Q k i) (rankTwoResidueConj hΔ hg) a :=
    fixesLinesThrough_rankTwoResidueConj hΔ hF.toIsFrame hg hgP hgl
  have hw : (⟨X, frameResidue_subset_rankTwoResidue_right k i hX⟩ :
      ↥(rankTwoResidue Δ P Q k i)) ∈ perp2 (residueAdj Δ P Q k i) a q :=
    mem_perp2.2 (hX.2 k hik.symm)
  exact congrArg Subtype.val
    (hGQ.apply_eq_of_mem_perp2 (residueAdj_rankTwoResidueConj_iff hΔ hg) haq hfa hfq ha hw)

end Group

section Order

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r}


theorem IsMaxFrame.commute_of_pow_two_pow_eq_one (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) {i : Fin r} (hik : i ≠ k) {g : H}
    (hg : g ∈ rankTwoResidueGroup Δ P Q k i) (hgP : conjSub (P k) g = P k)
    (hgQ : conjSub (Q k) g = Q k)
    (hgl : ∀ C ∈ Δ, C ≠ P k → Commuting (P k) C → g ∈ lineStab Δ (P k) C) {e : ℕ}
    (hge : g ^ 2 ^ e = 1) {Y : Subgroup H} (hY : Y ∈ rankTwoResidue Δ P Q k i) {y : H}
    (hy : y ∈ Y) : Commute g y := by
  classical
  haveI : Finite H := h.finite
  letI : Fintype ↥(rankTwoResidue Δ P Q k i) := Fintype.ofFinite _
  have hnsi : ¬ IsSmallFrame Δ P Q i := hF.not_isSmallFrame_of_ne h hML hq hik.symm hns
  have hO : IsQuadrangleOfOrder (residueAdj Δ P Q k i) (Nat.card (P i) ^ 2)
      (Nat.card (P i) ^ 3) :=
    hF.isQuadrangleOfOrder_residueAdj h hML hq hik.symm hnsi
  have hst : Nat.card (P i) ^ 2 < Nat.card (P i) ^ 3 :=
    Nat.pow_lt_pow_right (lt_of_lt_of_le (by norm_num) (hq _ (hF.memP i))) (by norm_num)
  have hs : Even (Nat.card (P i) ^ 2) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (h.cls.root.isPGroup (hF.memP i))
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      have h4 : 4 ≤ Nat.card (P i) := hq _ (hF.memP i)
      rw [hm] at h4
      exact absurd h4 (by norm_num)
    rw [hm, ← pow_mul]
    exact Nat.even_pow.mpr ⟨even_two, Nat.mul_ne_zero hm0 (by norm_num)⟩
  have hfe : (rankTwoResidueConj h.cls hg)^[2 ^ e] = id := by
    funext z
    apply Subtype.ext
    rw [coe_iterate_rankTwoResidueConj, hge, conjSub_one]
    rfl
  let a : ↥(rankTwoResidue Δ P Q k i) := ⟨P k, hF.toIsFrame.memP_rankTwoResidue_left k i⟩
  let q : ↥(rankTwoResidue Δ P Q k i) := ⟨Q k, hF.toIsFrame.memQ_rankTwoResidue_left k i⟩
  have haq : ¬ residueAdj Δ P Q k i a q := ModelRank.not_commuting_of_opposite (hF.opposite k)
  have hfa : rankTwoResidueConj h.cls hg a = a := Subtype.ext hgP
  have hfq : rankTwoResidueConj h.cls hg q = q := Subtype.ext hgQ
  have ha : FixesLinesThrough (residueAdj Δ P Q k i) (rankTwoResidueConj h.cls hg) a :=
    fixesLinesThrough_rankTwoResidueConj h.cls hF.toIsFrame hg hgP hgl
  have hfix : ∀ z : ↥(rankTwoResidue Δ P Q k i), rankTwoResidueConj h.cls hg z = z := fun z =>
    hO.apply_eq_self_of_iterate_eq_id hst hs (residueAdj_rankTwoResidueConj_iff h.cls hg) hfe
      haq hfa hfq ha z
  have hg' : ∀ X ∈ rankTwoResidue Δ P Q k i, conjSub X g = X := fun X hX =>
    congrArg Subtype.val (hfix ⟨X, hX⟩)
  exact hF.commute_of_forall_conjSub_eq h.cls hg' hY hy

theorem IsMaxFrame.ncard_rankTwoResidue_not_commuting_eq (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) {i : Fin r} (hik : i ≠ k) :
    {X | X ∈ rankTwoResidue Δ P Q k i ∧ ¬ Commuting X (P k)}.ncard = Nat.card (P k) ^ 7 := by
  classical
  haveI : Finite H := h.finite
  letI : Fintype ↥(rankTwoResidue Δ P Q k i) := Fintype.ofFinite _
  have hnsi : ¬ IsSmallFrame Δ P Q i := hF.not_isSmallFrame_of_ne h hML hq hik.symm hns
  have hO : IsQuadrangleOfOrder (residueAdj Δ P Q k i) (Nat.card (P i) ^ 2)
      (Nat.card (P i) ^ 3) :=
    hF.isQuadrangleOfOrder_residueAdj h hML hq hik.symm hnsi
  let a : ↥(rankTwoResidue Δ P Q k i) := ⟨P k, hF.toIsFrame.memP_rankTwoResidue_left k i⟩
  set O : Finset ↥(rankTwoResidue Δ P Q k i) :=
    Finset.univ.filter fun w => ¬ residueAdj Δ P Q k i a w with hOdef
  have hOcard : O.card * (Nat.card (P i) ^ 3 + 1) = ((Nat.card (P i) ^ 3 + 1) *
      Nat.card (P i) ^ 2) * (Nat.card (P i) ^ 3 * Nat.card (P i) ^ 2) :=
    hO.card_mul_of_mem_iff_not_adj (x := a) (F := O) fun w => by
      simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]
  have hOcard' : O.card = Nat.card (P i) ^ 2 * Nat.card (P i) ^ 2 * Nat.card (P i) ^ 3 := by
    have h : O.card * (Nat.card (P i) ^ 3 + 1) =
        (Nat.card (P i) ^ 2 * Nat.card (P i) ^ 2 * Nat.card (P i) ^ 3) *
          (Nat.card (P i) ^ 3 + 1) := by
      rw [hOcard]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) h
  have hmem : ∀ w : ↥(rankTwoResidue Δ P Q k i), w ∈ O ↔ ¬ residueAdj Δ P Q k i a w := by
    intro w
    simp only [hOdef, Finset.mem_filter, Finset.mem_univ, true_and]
  have hset : {X : Subgroup H | X ∈ rankTwoResidue Δ P Q k i ∧ ¬ Commuting X (P k)} =
      Subtype.val '' (O : Set ↥(rankTwoResidue Δ P Q k i)) := by
    ext X
    constructor
    · rintro ⟨hX, hXP⟩
      exact ⟨⟨X, hX⟩, (hmem _).2 fun hc => hXP (residueAdj_iff.1 hc).symm, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, fun hc => (hmem w).1 hw (residueAdj_iff.2 (Commuting.symm hc))⟩
  calc {X : Subgroup H | X ∈ rankTwoResidue Δ P Q k i ∧ ¬ Commuting X (P k)}.ncard
      = (Subtype.val '' (O : Set ↥(rankTwoResidue Δ P Q k i))).ncard := by rw [hset]
    _ = O.card := by
        rw [Set.ncard_image_of_injective _ Subtype.coe_injective, Set.ncard_coe_finset]
    _ = Nat.card (P i) ^ 2 * Nat.card (P i) ^ 2 * Nat.card (P i) ^ 3 := hOcard'
    _ = Nat.card (P i) ^ 7 := by ring
    _ = Nat.card (P k) ^ 7 := by rw [h.cls.root.card_eq (hF.memP i) (hF.memP k)]

theorem IsMaxFrame.mem_lineOf_of_conjSub_eq (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q k)
    {i : Fin r} (hik : i ≠ k) {g : H} (hg : g ∈ rankTwoResidueGroup Δ P Q k i)
    (hgP : conjSub (P k) g = P k) (hgQ : conjSub (Q k) g = Q k)
    (hgl : ∀ C ∈ Δ, C ≠ P k → Commuting (P k) C → g ∈ lineStab Δ (P k) C)
    (hne : ∃ Y ∈ rankTwoResidue Δ P Q k i, conjSub Y g ≠ Y) {X : Subgroup H}
    (hX : X ∈ rankTwoResidue Δ P Q k i) (hXP : ¬ Commuting X (P k))
    (hXg : conjSub X g = X) : X ∈ lineOf Δ (P k) (Q k) := by
  classical
  haveI : Finite H := h.finite
  letI : Fintype ↥(rankTwoResidue Δ P Q k i) := Fintype.ofFinite _
  have hnsi : ¬ IsSmallFrame Δ P Q i := hF.not_isSmallFrame_of_ne h hML hq hik.symm hns
  have hO : IsQuadrangleOfOrder (residueAdj Δ P Q k i) (Nat.card (P i) ^ 2)
      (Nat.card (P i) ^ 3) :=
    hF.isQuadrangleOfOrder_residueAdj h hML hq hik.symm hnsi
  have hst : Nat.card (P i) ^ 2 < Nat.card (P i) ^ 3 :=
    Nat.pow_lt_pow_right (lt_of_lt_of_le (by norm_num) (hq _ (hF.memP i))) (by norm_num)
  let a : ↥(rankTwoResidue Δ P Q k i) := ⟨P k, hF.toIsFrame.memP_rankTwoResidue_left k i⟩
  let q : ↥(rankTwoResidue Δ P Q k i) := ⟨Q k, hF.toIsFrame.memQ_rankTwoResidue_left k i⟩
  have haq : ¬ residueAdj Δ P Q k i a q := ModelRank.not_commuting_of_opposite (hF.opposite k)
  have hfa : rankTwoResidueConj h.cls hg a = a := Subtype.ext hgP
  have hfq : rankTwoResidueConj h.cls hg q = q := Subtype.ext hgQ
  have ha : FixesLinesThrough (residueAdj Δ P Q k i) (rankTwoResidueConj h.cls hg) a :=
    fixesLinesThrough_rankTwoResidueConj h.cls hF.toIsFrame hg hgP hgl
  have hne' : ∃ z : ↥(rankTwoResidue Δ P Q k i), rankTwoResidueConj h.cls hg z ≠ z := by
    obtain ⟨Y, hY, hYg⟩ := hne
    exact ⟨⟨Y, hY⟩, fun e => hYg (congrArg Subtype.val e)⟩
  have hz : (⟨X, hX⟩ : ↥(rankTwoResidue Δ P Q k i)) ∈ span2 (residueAdj Δ P Q k i) a q :=
    hO.mem_span2_of_apply_eq hst (residueAdj_rankTwoResidueConj_iff h.cls hg) haq hfa hfq ha hne'
      hXP (Subtype.ext hXg)
  rw [← hF.image_span2_residueAdj_eq_lineOf h hML hq hik.symm hnsi]
  exact ⟨_, hz, rfl⟩

theorem IsMaxFrame.eq_of_not_commuting_of_conjSub_eq (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) {i : Fin r} (hik : i ≠ k) {g : H}
    (hg : g ∈ rankTwoResidueGroup Δ P Q k i) (hgP : conjSub (P k) g = P k)
    (hgQ : conjSub (Q k) g = Q k)
    (hgl : ∀ C ∈ Δ, C ≠ P k → Commuting (P k) C → g ∈ lineStab Δ (P k) C)
    (hfree : ∀ a ∈ P k, g * a * g⁻¹ = a → a = 1) {X : Subgroup H}
    (hX : X ∈ rankTwoResidue Δ P Q k i) (hXP : ¬ Commuting X (P k))
    (hXg : conjSub X g = X) : X = Q k := by
  have hne : ∃ Y ∈ rankTwoResidue Δ P Q k i, conjSub Y g ≠ Y := by
    by_contra hno
    have hgall : ∀ Y ∈ rankTwoResidue Δ P Q k i, conjSub Y g = Y := fun Y hY => by
      by_contra hYg
      exact hno ⟨Y, hY, hYg⟩
    obtain ⟨a, ha, ha1⟩ := h.cls.root.exists_ne_one (hF.memP k)
    have hga : Commute g a :=
      hF.commute_of_forall_conjSub_eq h.cls hgall (hF.toIsFrame.memP_rankTwoResidue_left k i) ha
    exact ha1 (hfree a ha (mul_inv_eq_iff_eq_mul.2 hga))
  have hline := hF.mem_lineOf_of_conjSub_eq h hML hq hns hik hg hgP hgQ hgl hne hX hXP hXg
  rw [lineOf_comm, (lineOf_eq_of_opposite h hML hq (hF.memQ k) (hF.memP k)
    (hF.opposite k).symm).1] at hline
  simp only [Set.mem_insert_iff, Set.mem_image] at hline
  rcases hline with hXPk | ⟨a, ha, haX⟩
  · rw [hXPk] at hXP
    exact absurd (h.cls.root.commuting_self (hF.memP k)) hXP
  · have hQg : conjSub (Q k) g⁻¹ = Q k := by
      have h1 := Aux.conjSub_conjSub_inv (Q k) g
      rwa [hgQ] at h1
    have ha' : g * a * g⁻¹ ∈ P k := hgP ▸ conj_mem_conjSub g ha
    have hQa' : conjSub (Q k) (g * a * g⁻¹) = X := by
      rw [mul_assoc, conjSub_mul, conjSub_mul, hQg, haX, hXg]
    have hXa : conjSub (Q k) (a⁻¹ * (g * a * g⁻¹)) = Q k := by
      rw [conjSub_mul, hQa', ← haX, Aux.conjSub_conjSub_inv]
    have ha'a : g * a * g⁻¹ = a := by
      have h1 : a⁻¹ * (g * a * g⁻¹) = 1 :=
        (hF.opposite k).eq_one_of_conjSub_eq ((P k).mul_mem ((P k).inv_mem ha) ha') hXa
      rw [← mul_inv_cancel_left a (g * a * g⁻¹), h1, mul_one]
    rw [← haX, hfree a ha ha'a, conjSub_one]

end Order

end CFSG.Timmesfeld.Transvection
