module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Assembly.OpenBridges
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry reciprocalPolynomial)
open CFSG.RankThree.Classical (IsReciprocalTransversal)

private lemma ggK1Dk_hasOrbit_om (eps : Bool) (m : ℕ) :
    ggK1DCo_Kind.hasOrbit (ggK1DCo_Kind.om eps m) = decide (2 ≤ m) := rfl

private lemma ggK1Dk_hasOrbit_sl (m : ℕ) :
    ggK1DCo_Kind.hasOrbit (ggK1DCo_Kind.sl m) = decide (2 ≤ m) := rfl

private lemma ggK1Dk_hasOrbit_su (m : ℕ) :
    ggK1DCo_Kind.hasOrbit (ggK1DCo_Kind.su m) = decide (2 ≤ m) := rfl

private lemma ggK1Dk_decide_and (a b : Prop) [Decidable a] [Decidable b] :
    decide (a ∧ b) = (decide a && decide b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp_all

private lemma ggK1Dk_bool_aux (j t : ℕ) :
    (decide (2 ≤ t) && decide (1 ≤ j ∧ 1 ≤ t)) = decide (1 ≤ j ∧ 2 ≤ t) := by
  rw [← ggK1Dk_decide_and, decide_eq_decide]
  omega

private lemma ggK1Dk_hasOrbit_and (d j t : ℕ) :
    (ggK1DCo_Kind.hasOrbit
        (if d = 1 then ggK1DCo_Kind.sl t else ggK1DCo_Kind.su t) &&
      decide (1 ≤ j ∧ 1 ≤ t)) = decide (1 ≤ j ∧ 2 ≤ t) := by
  by_cases hd : d = 1
  · rw [if_pos hd, ggK1Dk_hasOrbit_sl]
    exact ggK1Dk_bool_aux j t
  · rw [if_neg hd, ggK1Dk_hasOrbit_su]
    exact ggK1Dk_bool_aux j t

private lemma ggK1Dk_blockA_eq (r nf d : ℕ) (hd : d ≠ 1) :
    ggMultBlockA r nf 2 = ggMultBlockA r nf d := by
  rw [ggMultBlockA, ggMultBlockA]
  simp [hd]

private lemma ggK1Dk_kindOrbits_blockA (nf d t : ℕ) (ht : 2 ≤ t) :
    ggK1DCo_kindOrbits nf (if d = 1 then ggK1DCo_Kind.sl t else ggK1DCo_Kind.su t) =
      [ggMultBlockA (t - 1) nf d] := by
  by_cases hd : d = 1
  · subst hd
    rw [if_pos rfl]
    rcases t with _ | _ | t
    · omega
    · omega
    · simp [ggK1DCo_kindOrbits, if_neg (by omega : ¬ (t + 1 + 1) ≤ 1)]
  · rw [if_neg hd]
    rcases t with _ | _ | t
    · omega
    · omega
    · rw [show ggK1DCo_kindOrbits nf (ggK1DCo_Kind.su (t + 1 + 1)) =
            [ggMultBlockA (t + 1 + 1 - 1) nf 2] from by
          simp [ggK1DCo_kindOrbits, if_neg (by omega : ¬ (t + 1 + 1) ≤ 1)]]
      rw [ggK1Dk_blockA_eq _ _ _ hd]

private lemma ggK1Dk_flatten_map_singleton {α : Type*} (l : List α) (g : α → GGKacOrbit) :
    (l.map (fun a => [g a])).flatten = l.map g := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

private lemma ggK1Dk_filter_map_kindOrbit (L : List ℕ) (d nf : ℕ) (f : ℕ → ℕ) :
    ((((L.filter (fun j => decide (1 ≤ j ∧ 1 ≤ f j))).map
        (fun j => if d = 1 then ggK1DCo_Kind.sl (f j) else ggK1DCo_Kind.su (f j))).filter
        (fun k => ggK1DCo_Kind.hasOrbit k)).map (ggK1DCo_kindOrbits nf)).flatten =
      (L.filter (fun j => decide (1 ≤ j ∧ 2 ≤ f j))).map
          (fun j => ggMultBlockA (f j - 1) nf d) := by
  rw [List.filter_map, List.filter_filter, List.map_map]
  simp only [Function.comp_apply]
  have hQ : L.filter (fun a =>
        ggK1DCo_Kind.hasOrbit
            (if d = 1 then ggK1DCo_Kind.sl (f a) else ggK1DCo_Kind.su (f a)) &&
          decide (1 ≤ a ∧ 1 ≤ f a)) =
      L.filter (fun j => decide (1 ≤ j ∧ 2 ≤ f j)) := by
    apply List.filter_congr
    intro j _
    exact ggK1Dk_hasOrbit_and d j (f j)
  rw [hQ]
  have hmap : (L.filter (fun j => decide (1 ≤ j ∧ 2 ≤ f j))).map
        (ggK1DCo_kindOrbits nf ∘ fun j => if d = 1 then ggK1DCo_Kind.sl (f j)
          else ggK1DCo_Kind.su (f j)) =
      (L.filter (fun j => decide (1 ≤ j ∧ 2 ≤ f j))).map
          (fun a => [ggMultBlockA (f a - 1) nf d]) := by
    apply List.map_congr_left
    intro a ha
    have h2 : 2 ≤ f a := by
      have h := (List.mem_filter.mp ha).2
      rw [decide_eq_true_eq] at h
      exact h.2
    exact ggK1Dk_kindOrbits_blockA nf d (f a) h2
  rw [hmap]
  exact ggK1Dk_flatten_map_singleton _ _

private lemma ggK1Dk_om_part (nf m0 : ℕ) (eps : Bool) :
    (([ggK1DCo_Kind.om eps m0].filter (fun k => ggK1DCo_Kind.hasOrbit k)).map
        (ggK1DCo_kindOrbits nf)).flatten = ggMultV0 m0 eps nf := by
  rcases Nat.lt_or_ge m0 2 with h | h
  · have h1 : m0 ≤ 1 := by omega
    have h2 : ggK1DCo_Kind.hasOrbit (ggK1DCo_Kind.om eps m0) = false := by
      rw [ggK1Dk_hasOrbit_om, decide_eq_false_iff_not]; omega
    simp [ggMultV0, h1, h2]
  · have h1 : ¬ m0 ≤ 1 := by omega
    have h2 : ggK1DCo_Kind.hasOrbit (ggK1DCo_Kind.om eps m0) = true := by
      rw [ggK1Dk_hasOrbit_om, decide_eq_true_eq]; exact h
    simp [ggMultV0, ggK1DCo_kindOrbits, h1, h2]

theorem ggK1DCo_kindOrbit_multiset (p nf d : ℕ) (tw : Bool) (m : List ℕ) :
    ggK1DCo_expectedOrbits p nf d tw m = (ggMultDatumD p nf d tw m).orbits := by
  simp only [ggK1DCo_expectedOrbits, ggK1DCo_expectedKindList, ggMultDatumD]
  rw [List.filter_append, List.map_append, List.flatten_append]
  rw [ggK1Dk_om_part, ggK1Dk_filter_map_kindOrbit]

private lemma ggK1Dk_lambda2_A (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (h : r = 1 → 2 ≤ n) :
    LargeEvenInLambda2 (⟨.A, r, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  exact ⟨hn, hr, h⟩

private lemma ggK1Dk_lambda2_twA (n r : ℕ) (hn : 1 ≤ n) (hr : 2 ≤ r) (h : r = 2 → 2 ≤ n) :
    LargeEvenInLambda2 (⟨.twA, r, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  exact ⟨hn, hr, h⟩

private lemma ggK1Dk_lambda2_D (n r : ℕ) (hn : 1 ≤ n) (hr : 3 ≤ r) :
    LargeEvenInLambda2 (⟨.D, r, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  exact ⟨hn, hr⟩

private lemma ggK1Dk_lambda2_twD (n r : ℕ) (hn : 1 ≤ n) (hr : 2 ≤ r) :
    LargeEvenInLambda2 (⟨.twD, r, n⟩ : LargeEvenLabel) := by
  simp only [LargeEvenInLambda2]
  exact ⟨hn, hr⟩

private lemma ggK1Dk_blockA_arith {r nf d : ℕ} (hnf : 1 ≤ nf) (hr : 1 ≤ r)
    (hqs : (ggMultBlockA r nf d).qs = true) :
    nf ∣ (ggMultBlockA r nf d).lab.n ∧ LargeEvenInLambda2 (ggMultBlockA r nf d).lab := by
  by_cases hd : d = 1
  · rw [ggMultBlockA, if_pos hd] at hqs ⊢
    rw [decide_eq_true_eq] at hqs
    exact ⟨dvd_refl nf, ggK1Dk_lambda2_A nf r hnf hr (by rintro rfl; omega)⟩
  · rw [ggMultBlockA, if_neg hd] at hqs ⊢
    by_cases h2 : 2 ≤ r
    · rw [if_pos h2] at hqs ⊢
      rw [decide_eq_true_eq] at hqs
      exact ⟨dvd_refl nf, ggK1Dk_lambda2_twA nf r hnf h2 (by rintro rfl; omega)⟩
    · rw [if_neg h2] at hqs ⊢
      have hr1 : r = 1 := by omega
      subst hr1
      rw [decide_eq_true_eq] at hqs
      exact ⟨dvd_refl nf, ggK1Dk_lambda2_A nf 1 hnf le_rfl (by intro _; omega)⟩

private lemma ggK1Dk_v0_arith {m0 nf : ℕ} (hnf : 1 ≤ nf) (eps : Bool) {o : GGKacOrbit}
    (ho : o ∈ ggMultV0 m0 eps nf) (hqs : o.qs = true) :
    nf ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab := by
  rcases m0 with _ | _ | _ | _ | k
  · rw [show ggMultV0 0 eps nf = [] from by simp [ggMultV0]] at ho
    simp at ho
  · rw [show ggMultV0 1 eps nf = [] from by simp [ggMultV0]] at ho
    simp at ho
  · cases eps
    · rw [show ggMultV0 2 false nf = [⟨⟨.A, 1, 2 * nf⟩, true⟩] from by simp [ggMultV0]] at ho
      rw [List.mem_singleton] at ho
      rw [ho] at hqs ⊢
      exact ⟨⟨2, by ring⟩,
        ggK1Dk_lambda2_A (2 * nf) 1 (by omega) le_rfl (by intro _; omega)⟩
    · rw [show ggMultV0 2 true nf =
          [⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩, ⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩]
          from by simp [ggMultV0]] at ho
      rw [List.mem_cons, List.mem_singleton] at ho
      rcases ho with ho | ho
      · rw [ho] at hqs ⊢
        rw [decide_eq_true_eq] at hqs
        exact ⟨dvd_refl nf, ggK1Dk_lambda2_A nf 1 hnf le_rfl (by intro _; omega)⟩
      · rw [ho] at hqs ⊢
        rw [decide_eq_true_eq] at hqs
        exact ⟨dvd_refl nf, ggK1Dk_lambda2_A nf 1 hnf le_rfl (by intro _; omega)⟩
  · cases eps
    · rw [show ggMultV0 3 false nf = [⟨⟨.twA, 3, nf⟩, true⟩] from by
          rw [ggMultV0]
          simp only [if_neg (by omega : ¬ (3:ℕ) ≤ 1),
            if_neg (by omega : ¬ (3:ℕ) = 2)] at *
          rfl] at ho
      rw [List.mem_singleton] at ho
      rw [ho] at hqs ⊢
      exact ⟨dvd_refl nf, ggK1Dk_lambda2_twA nf 3 hnf (by omega) (by intro _; omega)⟩
    · rw [show ggMultV0 3 true nf = [⟨⟨.A, 3, nf⟩, true⟩] from by
          rw [ggMultV0]
          simp only [if_neg (by omega : ¬ (3:ℕ) ≤ 1),
            if_neg (by omega : ¬ (3:ℕ) = 2)] at *
          rfl] at ho
      rw [List.mem_singleton] at ho
      rw [ho] at hqs ⊢
      exact ⟨dvd_refl nf, ggK1Dk_lambda2_A nf 3 hnf (by omega) (by intro _; omega)⟩
  · cases eps
    · rw [show ggMultV0 (k + 4) false nf = [⟨⟨.twD, k + 4, nf⟩, true⟩] from by
          rw [ggMultV0]
          simp only [if_neg (by omega : ¬ (k + 4) ≤ 1),
            if_neg (by omega : ¬ (k + 4) = 2), if_neg (by omega : ¬ (k + 4) = 3)] at *
          rfl] at ho
      rw [List.mem_singleton] at ho
      rw [ho] at hqs ⊢
      exact ⟨dvd_refl nf, ggK1Dk_lambda2_twD nf (k + 4) hnf (by omega)⟩
    · rw [show ggMultV0 (k + 4) true nf = [⟨⟨.D, k + 4, nf⟩, true⟩] from by
          rw [ggMultV0]
          simp only [if_neg (by omega : ¬ (k + 4) ≤ 1),
            if_neg (by omega : ¬ (k + 4) = 2), if_neg (by omega : ¬ (k + 4) = 3)] at *
          rfl] at ho
      rw [List.mem_singleton] at ho
      rw [ho] at hqs ⊢
      exact ⟨dvd_refl nf, ggK1Dk_lambda2_D nf (k + 4) hnf (by omega)⟩

theorem ggK1DCo_orbit_arith {p nf d : ℕ} {tw : Bool} {m : List ℕ} (hnf : 1 ≤ nf) {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumD p nf d tw m).orbits) (hqs : o.qs = true) :
    nf ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab := by
  simp only [ggMultDatumD] at ho
  rw [List.mem_append] at ho
  rcases ho with ho | ho
  · exact ggK1Dk_v0_arith hnf _ ho hqs
  · obtain ⟨j, hj, hjeq⟩ := List.mem_map.mp ho
    have hj' : 2 ≤ m.getD j 0 := by
      have h := (List.mem_filter.mp hj).2
      rw [decide_eq_true_eq] at h
      exact h.2
    have hr : 1 ≤ m.getD j 0 - 1 := by omega
    rw [← hjeq] at hqs ⊢
    exact ggK1Dk_blockA_arith hnf hr hqs
private theorem ggK1Dk_projSU {a m : ℕ} {E : Type} [Field E] [Finite E] {X : Type} [Group X]
    (hE : Nat.card E = (2 ^ m) ^ 2) (e : X ≃* StatedSU a (2 ^ m) E) (ha : 3 ≤ a)
    (ham : (a, 2 ^ m) ≠ (3, 2)) :
    Nonempty (X ⧸ Subgroup.center X ≃* StatedProj (StatedSU a (2 ^ m) E)) := by
  obtain ⟨τ, hτm, hτ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_frob_equiv (n := m) hE
  obtain ⟨eC⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv e
  obtain ⟨eP⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds τ hτ hτm hE ha ham
  rw [CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU
    (a := a) (Q := 2 ^ m) hτm] at eP
  exact ⟨eC.trans eP⟩

private theorem ggK1Dk_hasLabel_twA {nf b : ℕ} {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = (2 ^ nf) ^ 2) {X : Type} [Group X]
    (e : X ≃* StatedSU (b + 1) (2 ^ nf) E) (hb : 2 ≤ b) (hbm : b = 2 → 2 ≤ nf) :
    GGHasLabel (⟨.twA, b, nf⟩ : LargeEvenLabel) (X ⧸ Subgroup.center X) := by
  have ha : 3 ≤ b + 1 := by omega
  have ham : (b + 1, 2 ^ nf) ≠ (3, 2) := by
    rintro h
    have hb2 : b = 2 := by
      have := congrArg Prod.fst h
      omega
    have h2 : 2 ^ nf = 2 := congrArg Prod.snd h
    have hnf1 : nf = 1 :=
      Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using h2)
    have := hbm hb2
    omega
  obtain ⟨eP⟩ := ggK1Dk_projSU hE e ha ham
  exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA hE eP

private theorem ggK1Dk_not_su3_2 {E : Type} [Field E] [Finite E] {X : Type} [Group X]
    (hE4 : Nat.card E = 4) (e : X ≃* StatedSU 3 2 E) (hq : CFSG.IsQuasisimple X) : False := by
  obtain ⟨τ, hτm, hτ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_frob_equiv (n := 1) (by simpa using hE4)
  have hτ2 : ∀ x, τ x = x ^ 2 := by
    intro x
    rw [hτm x]
    norm_num
  have hsol : Group.IsSolvable
      (CFSG.LieType.SemisimpleCentralizers.Held.heldSU 3 E τ hτ ⧸
        Subgroup.center (CFSG.LieType.SemisimpleCentralizers.Held.heldSU 3 E τ hτ)) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.isSolvable_quot_heldSU_three_two τ hτ hτ2 hE4
  rw [CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU
    (a := 3) (Q := 2) hτ2] at hsol
  obtain ⟨eC⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv e
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  have hsol' : Group.IsSolvable (X ⧸ Subgroup.center X) :=
    Group.isSolvable_of_surjective (f := eC.symm.toMonoidHom) eC.symm.surjective
  exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.not_isSolvable_quot_center (J := X) hsol'

private theorem ggK1Dk_projOmegaPlus {r : ℕ} (hr : 3 ≤ r) {K : Type} [Field K] [Finite K]
    [CharP K 2] {X : Type} [Group X] (e : X ≃* StatedOmega (StatedQuadPlus r K)) :
    Nonempty (X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))) := by
  obtain ⟨eC⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv e
  have hcen : Subgroup.center (↥(StatedOmega (StatedQuadPlus r K))) =
      (LargeEvenScalars (Fin r ⊕ Fin r) K).subgroupOf
        (LargeEvenOmega (LargeEvenQPlus K r)) :=
    CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus hr
  exact ⟨eC.trans (QuotientGroup.quotientMulEquivOfEq hcen)⟩

private theorem ggK1Dk_hasLabel_D {nf r : ℕ} (hr : 4 ≤ r) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ nf) {X : Type} [Group X]
    (e : X ≃* StatedOmega (StatedQuadPlus r K)) :
    GGHasLabel (⟨.D, r, nf⟩ : LargeEvenLabel) (X ⧸ Subgroup.center X) := by
  have hr3 : r ≠ 3 := by omega
  obtain ⟨eP⟩ := ggK1Dk_projOmegaPlus (r := r) (by omega) e
  simp only [GGHasLabel, LargeEvenRawDatum]
  rw [if_neg hr3]
  simp only [LargeEvenRecipeOmegaPlus]
  exact ⟨K, inferInstance, inferInstance, hK, ⟨eP⟩⟩

private theorem ggK1Dk_projOmegaMinus {r : ℕ} (hr : 4 ≤ r) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {X : Type} [Group X]
    (e : X ≃* StatedOmega (StatedQuadMinus r K b c)) :
    Nonempty (X ⧸ Subgroup.center X ≃*
      LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))) := by
  obtain ⟨eC⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv e
  have hcen : Subgroup.center (↥(StatedOmega (StatedQuadMinus r K b c))) =
      (LargeEvenScalars (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) K).subgroupOf
        (StatedOmega (StatedQuadMinus r K b c)) :=
    CFSG.LieType.Universal.Spin.center_statedOmega_quadMinus hr hirr
  refine ⟨(eC.trans (QuotientGroup.quotientMulEquivOfEq hcen)).trans
    (omegaMinusProjEquiv r b c).symm⟩

private theorem ggK1Dk_hasLabel_twD {nf r : ℕ} (hr : 4 ≤ r) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {X : Type} [Group X]
    (e : X ≃* StatedOmega (StatedQuadMinus r K b c)) :
    GGHasLabel (⟨.twD, r, nf⟩ : LargeEvenLabel) (X ⧸ Subgroup.center X) := by
  have hr2 : r ≠ 2 := by omega
  have hr3 : r ≠ 3 := by omega
  obtain ⟨eP⟩ := ggK1Dk_projOmegaMinus hr hirr e
  simp only [GGHasLabel, LargeEvenRawDatum]
  rw [if_neg hr2, if_neg hr3]
  simp only [LargeEvenRecipeOmegaMinus]
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hirr, ⟨eP⟩⟩

private theorem ggK1Dk_projSL {d : ℕ} {E : Type} [Field E] {X : Type} [Group X]
    (e : X ≃* Matrix.SpecialLinearGroup (Fin d) E) :
    Nonempty (X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) E)) := by
  obtain ⟨eZ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl d e
  rw [largeEvenSLGroup_eq_statedSL]
  exact ⟨eZ⟩

private theorem ggK1Dk_hasLabel_A {nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ nf)
    {X : Type} [Group X] (e : X ≃* Matrix.SpecialLinearGroup (Fin (r + 1)) K) :
    GGHasLabel (⟨.A, r, nf⟩ : LargeEvenLabel) (X ⧸ Subgroup.center X) := by
  obtain ⟨eZ⟩ := ggK1Dk_projSL e
  simp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeLinear]
  exact ⟨K, inferInstance, inferInstance, hK, ⟨eZ⟩⟩

theorem ggK1DCo_orbit_label {nf : ℕ} {K : Type} [Field K] [Finite K] (hnf : 1 ≤ nf)
    (hK : Nat.card K = 2 ^ nf) {R : Type} [Group R] {o : GGKacOrbit}
    (hn : o.lab.n = nf ∨ (o.lab.tag = .A ∧ o.lab.rank = 1 ∧ o.lab.n = 2 * nf))
    (hr : (o.lab.tag = .A → 1 ≤ o.lab.rank) ∧ (o.lab.tag = .twA → 2 ≤ o.lab.rank) ∧
      (o.lab.tag = .D → 4 ≤ o.lab.rank) ∧ (o.lab.tag = .twD → 4 ≤ o.lab.rank))
    (ho : o.qs = true) (H : Subgroup R)
    (hq : CFSG.IsQuasisimple ↥H) (hm : ggK1DCo_OrbitModel nf K o ↥H) :
    GGHasLabel o.lab (↥H ⧸ Subgroup.center ↥H) := by
  obtain ⟨⟨tag, r, n⟩, qs⟩ := o
  cases tag
  ·
    simp only [ggK1DCo_OrbitModel] at hm
    by_cases hsp : r = 1 ∧ n = 2 * nf
    · rw [if_pos hsp] at hm
      obtain ⟨E, hEfield, hEfin, hEcard, ⟨eH⟩⟩ := hm
      letI : Field E := hEfield
      letI : Fintype E := hEfin
      have hEcard' : Nat.card E = 2 ^ (2 * nf) := by
        rw [Nat.card_eq_fintype_card, hEcard, hK, ← pow_mul]
        congr 1
        ring
      obtain ⟨rfl, hn2⟩ := hsp
      subst hn2
      exact ggK1Dk_hasLabel_A hEcard' eH
    · rw [if_neg hsp] at hm
      obtain ⟨eH⟩ := hm
      have hn' : n = nf := by
        rcases hn with h | h
        · exact h
        · exact absurd ⟨h.2.1, h.2.2⟩ hsp
      subst hn'
      exact ggK1Dk_hasLabel_A hK eH
  ·
    simp only [ggK1DCo_OrbitModel] at hm
    obtain ⟨E, hEfield, hEfin, hEcard, ⟨eH0⟩⟩ := hm
    letI : Field E := hEfield
    letI : Fintype E := hEfin
    have hEcard' : Nat.card E = (2 ^ nf) ^ 2 := by
      rw [Nat.card_eq_fintype_card, hEcard, hK]
    have hn' : n = nf := by
      rcases hn with h | h
      · exact h
      · exact absurd h.1 (by
          have hne : (LargeEvenLieTag.twA : LargeEvenLieTag) ≠ .A := by decide
          exact hne)
    rw [hn'] at *
    have eH : ↥H ≃* StatedSU (r + 1) (2 ^ nf) E := by
      rw [hK] at eH0
      exact eH0
    rcases r with _ | _ | k
    · exact absurd (by simpa using hr.2.1 rfl) (by omega : ¬ (2 ≤ 0))
    · exact absurd (by simpa using hr.2.1 rfl) (by omega : ¬ (2 ≤ 1))
    · have hbm : k + 2 = 2 → 2 ≤ nf := by
        intro hk2
        by_contra hlt
        have hnf1 : nf = 1 := by omega
        have hk : k = 0 := by omega
        subst hk
        rw [hnf1] at eH hEcard'
        have hE4 : Nat.card E = 4 := by simpa using hEcard'
        exact (ggK1Dk_not_su3_2 hE4 eH hq).elim
      exact ggK1Dk_hasLabel_twA hEcard' eH (by omega) hbm
  ·
    simp only [ggK1DCo_OrbitModel] at hm
  ·
    simp only [ggK1DCo_OrbitModel] at hm
  ·
    simp only [ggK1DCo_OrbitModel] at hm
    obtain ⟨eH0⟩ := hm
    have hn' : n = nf := by
      rcases hn with h | h
      · exact h
      · exact absurd h.1 (by
          have hne : (LargeEvenLieTag.D : LargeEvenLieTag) ≠ .A := by decide
          exact hne)
    rw [hn'] at *
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (R := K) (p := 2) (f := nf)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
    rcases r with _ | _ | _ | _ | k
    · exact absurd (by simpa using hr.2.2.1 rfl) (by omega : ¬ (4 ≤ 0))
    · exact absurd (by simpa using hr.2.2.1 rfl) (by omega : ¬ (4 ≤ 1))
    · exact absurd (by simpa using hr.2.2.1 rfl) (by omega : ¬ (4 ≤ 2))
    · exact absurd (by simpa using hr.2.2.1 rfl) (by omega : ¬ (4 ≤ 3))
    · exact ggK1Dk_hasLabel_D (by omega) hK eH0
  ·
    simp only [ggK1DCo_OrbitModel] at hm
    obtain ⟨b, c, hirr, ⟨eH0⟩⟩ := hm
    have hn' : n = nf := by
      rcases hn with h | h
      · exact h
      · exact absurd h.1 (by
          have hne : (LargeEvenLieTag.twD : LargeEvenLieTag) ≠ .A := by decide
          exact hne)
    rw [hn'] at *
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (R := K) (p := 2) (f := nf)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
    rcases r with _ | _ | _ | _ | k
    · exact absurd (by simpa using hr.2.2.2 rfl) (by omega : ¬ (4 ≤ 0))
    · exact absurd (by simpa using hr.2.2.2 rfl) (by omega : ¬ (4 ≤ 1))
    · exact absurd (by simpa using hr.2.2.2 rfl) (by omega : ¬ (4 ≤ 2))
    · exact absurd (by simpa using hr.2.2.2 rfl) (by omega : ¬ (4 ≤ 3))
    · exact ggK1Dk_hasLabel_twD (by omega) hK hirr eH0
  all_goals simp only [ggK1DCo_OrbitModel] at hm

private lemma ggK1Dk_v0_n {m0 nf : ℕ} {eps : Bool} {o : GGKacOrbit}
    (ho : o ∈ ggMultV0 m0 eps nf) :
    o.lab.n = nf ∨ (o.lab.tag = .A ∧ o.lab.rank = 1 ∧ o.lab.n = 2 * nf) := by
  rcases m0 with _ | _ | _ | _ | k
  · rw [show ggMultV0 0 eps nf = [] from by simp [ggMultV0]] at ho
    simp at ho
  · rw [show ggMultV0 1 eps nf = [] from by simp [ggMultV0]] at ho
    simp at ho
  · cases eps
    · rw [show ggMultV0 2 false nf = [⟨⟨.A, 1, 2 * nf⟩, true⟩] from by simp [ggMultV0]] at ho
      rw [List.mem_singleton] at ho
      right
      rw [ho]
      exact ⟨rfl, rfl, rfl⟩
    · rw [show ggMultV0 2 true nf =
          [⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩, ⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩]
          from by simp [ggMultV0]] at ho
      rw [List.mem_cons, List.mem_singleton] at ho
      left
      rcases ho with ho | ho <;> rw [ho] <;> rfl
  · cases eps
    · rw [show ggMultV0 3 false nf = [⟨⟨.twA, 3, nf⟩, true⟩] from by
          rw [ggMultV0]
          simp only [if_neg (by omega : ¬ (3:ℕ) ≤ 1),
            if_neg (by omega : ¬ (3:ℕ) = 2)] at *
          rfl] at ho
      rw [List.mem_singleton] at ho
      left
      rw [ho]
    · rw [show ggMultV0 3 true nf = [⟨⟨.A, 3, nf⟩, true⟩] from by
          rw [ggMultV0]
          simp only [if_neg (by omega : ¬ (3:ℕ) ≤ 1),
            if_neg (by omega : ¬ (3:ℕ) = 2)] at *
          rfl] at ho
      rw [List.mem_singleton] at ho
      left
      rw [ho]
  · cases eps
    · rw [show ggMultV0 (k + 4) false nf = [⟨⟨.twD, k + 4, nf⟩, true⟩] from by
          rw [ggMultV0]
          simp only [if_neg (by omega : ¬ (k + 4) ≤ 1),
            if_neg (by omega : ¬ (k + 4) = 2), if_neg (by omega : ¬ (k + 4) = 3)] at *
          rfl] at ho
      rw [List.mem_singleton] at ho
      left
      rw [ho]
    · rw [show ggMultV0 (k + 4) true nf = [⟨⟨.D, k + 4, nf⟩, true⟩] from by
          rw [ggMultV0]
          simp only [if_neg (by omega : ¬ (k + 4) ≤ 1),
            if_neg (by omega : ¬ (k + 4) = 2), if_neg (by omega : ¬ (k + 4) = 3)] at *
          rfl] at ho
      rw [List.mem_singleton] at ho
      left
      rw [ho]

private lemma ggK1Dk_blockA_n {r nf d : ℕ} {o : GGKacOrbit}
    (ho : o ∈ [ggMultBlockA r nf d]) :
    o.lab.n = nf ∨ (o.lab.tag = .A ∧ o.lab.rank = 1 ∧ o.lab.n = 2 * nf) := by
  rw [List.mem_singleton] at ho
  left
  rw [ho]
  unfold ggMultBlockA
  split_ifs <;> rfl

private lemma ggK1Dk_dummy_n {nf : ℕ} {o : GGKacOrbit} (ho : o ∈ [ggK1DCo_dummyOrbit nf]) :
    o.lab.n = nf ∨ (o.lab.tag = .A ∧ o.lab.rank = 1 ∧ o.lab.n = 2 * nf) := by
  rw [List.mem_singleton] at ho
  left
  rw [ho]
  rfl

theorem ggK1DCo_kindOrbits_n (nf : ℕ) (k : ggK1DCo_Kind) {o : GGKacOrbit}
    (ho : o ∈ ggK1DCo_kindOrbits nf k) :
    o.lab.n = nf ∨ (o.lab.tag = .A ∧ o.lab.rank = 1 ∧ o.lab.n = 2 * nf) := by
  cases k with
  | om eps m =>
      by_cases h : m ≤ 1
      · exact ggK1Dk_dummy_n (by simpa [ggK1DCo_kindOrbits, h] using ho)
      · exact ggK1Dk_v0_n (by simpa [ggK1DCo_kindOrbits, h] using ho)
  | sl m =>
      by_cases h : m ≤ 1
      · exact ggK1Dk_dummy_n (by simpa [ggK1DCo_kindOrbits, h] using ho)
      · exact ggK1Dk_blockA_n (by simpa [ggK1DCo_kindOrbits, h] using ho)
  | su m =>
      by_cases h : m ≤ 1
      · exact ggK1Dk_dummy_n (by simpa [ggK1DCo_kindOrbits, h] using ho)
      · exact ggK1Dk_blockA_n (by simpa [ggK1DCo_kindOrbits, h] using ho)

private lemma ggK1Dk_v0_rank {m0 nf : ℕ} (hm : 2 ≤ m0) {eps : Bool} {o : GGKacOrbit}
    (ho : o ∈ ggMultV0 m0 eps nf) (hqs : o.qs = true) :
    (o.lab.tag = .A → 1 ≤ o.lab.rank) ∧ (o.lab.tag = .twA → 2 ≤ o.lab.rank) ∧
      (o.lab.tag = .D → 4 ≤ o.lab.rank) ∧ (o.lab.tag = .twD → 4 ≤ o.lab.rank) := by
  rcases m0 with _ | _ | _ | _ | k
  · omega
  · omega
  · cases eps
    · rw [show ggMultV0 2 false nf = [⟨⟨.A, 1, 2 * nf⟩, true⟩] from by simp [ggMultV0]] at ho
      rw [List.mem_singleton] at ho
      rw [ho]
      simp
    · rw [show ggMultV0 2 true nf =
          [⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩, ⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩]
          from by simp [ggMultV0]] at ho
      rw [List.mem_cons, List.mem_singleton] at ho
      rcases ho with ho | ho <;> rw [ho] <;> simp
  · cases eps
    · rw [show ggMultV0 3 false nf = [⟨⟨.twA, 3, nf⟩, true⟩] from by
          rw [ggMultV0]
          simp only [if_neg (by omega : ¬ (3:ℕ) ≤ 1),
            if_neg (by omega : ¬ (3:ℕ) = 2)] at *
          rfl] at ho
      rw [List.mem_singleton] at ho
      rw [ho]
      simp
    · rw [show ggMultV0 3 true nf = [⟨⟨.A, 3, nf⟩, true⟩] from by
          rw [ggMultV0]
          simp only [if_neg (by omega : ¬ (3:ℕ) ≤ 1),
            if_neg (by omega : ¬ (3:ℕ) = 2)] at *
          rfl] at ho
      rw [List.mem_singleton] at ho
      rw [ho]
      simp
  · cases eps
    · rw [show ggMultV0 (k + 4) false nf = [⟨⟨.twD, k + 4, nf⟩, true⟩] from by
          rw [ggMultV0]
          simp only [if_neg (by omega : ¬ (k + 4) ≤ 1),
            if_neg (by omega : ¬ (k + 4) = 2), if_neg (by omega : ¬ (k + 4) = 3)] at *
          rfl] at ho
      rw [List.mem_singleton] at ho
      rw [ho]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> omega
    · rw [show ggMultV0 (k + 4) true nf = [⟨⟨.D, k + 4, nf⟩, true⟩] from by
          rw [ggMultV0]
          simp only [if_neg (by omega : ¬ (k + 4) ≤ 1),
            if_neg (by omega : ¬ (k + 4) = 2), if_neg (by omega : ¬ (k + 4) = 3)] at *
          rfl] at ho
      rw [List.mem_singleton] at ho
      rw [ho]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> omega

private lemma ggK1Dk_blockA_rank {r nf d : ℕ} (hr : 1 ≤ r) {o : GGKacOrbit}
    (ho : o ∈ [ggMultBlockA r nf d]) (hqs : o.qs = true) :
    (o.lab.tag = .A → 1 ≤ o.lab.rank) ∧ (o.lab.tag = .twA → 2 ≤ o.lab.rank) ∧
      (o.lab.tag = .D → 4 ≤ o.lab.rank) ∧ (o.lab.tag = .twD → 4 ≤ o.lab.rank) := by
  rw [List.mem_singleton] at ho
  rw [ho]
  unfold ggMultBlockA
  split_ifs <;> simp_all

theorem ggK1DCo_kindOrbits_rank (nf : ℕ) (k : ggK1DCo_Kind) {o : GGKacOrbit}
    (ho : o ∈ ggK1DCo_kindOrbits nf k) (hqs : o.qs = true) :
    (o.lab.tag = .A → 1 ≤ o.lab.rank) ∧ (o.lab.tag = .twA → 2 ≤ o.lab.rank) ∧
      (o.lab.tag = .D → 4 ≤ o.lab.rank) ∧ (o.lab.tag = .twD → 4 ≤ o.lab.rank) := by
  cases k with
  | om eps m =>
      by_cases h : m ≤ 1
      · rw [ggK1DCo_kindOrbits, if_pos h] at ho
        rw [List.mem_singleton] at ho
        rw [ho] at hqs
        simp [ggK1DCo_dummyOrbit] at hqs
      · exact ggK1Dk_v0_rank (m0 := m) (by omega) (by simpa [ggK1DCo_kindOrbits, h] using ho) hqs
  | sl m =>
      by_cases h : m ≤ 1
      · rw [ggK1DCo_kindOrbits, if_pos h] at ho
        rw [List.mem_singleton] at ho
        rw [ho] at hqs
        simp [ggK1DCo_dummyOrbit] at hqs
      · exact ggK1Dk_blockA_rank (r := m - 1) (by omega)
          (by simpa [ggK1DCo_kindOrbits, h] using ho) hqs
  | su m =>
      by_cases h : m ≤ 1
      · rw [ggK1DCo_kindOrbits, if_pos h] at ho
        rw [List.mem_singleton] at ho
        rw [ho] at hqs
        simp [ggK1DCo_dummyOrbit] at hqs
      · exact ggK1Dk_blockA_rank (r := m - 1) (by omega)
          (by simpa [ggK1DCo_kindOrbits, h] using ho) hqs

end CFSG.StandardType

end
