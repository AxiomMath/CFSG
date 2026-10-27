module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts
public import CFSG.LieType.SemisimpleCentralizers.OrderThree.CenterQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoverSU3
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
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
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.LieType.SemisimpleCentralizers.OrderThree
  (nonempty_quotientCenter_equiv_statedProj_statedSU)
open CFSG.Quasithin.Background.Harris.OrdinaryProofs (card_statedSU_three_two_of_card_four)

private theorem ggK1Ak_hasOrbit_sl (mm e : ℕ) :
    ggK1ACo_Kind.hasOrbit (ggK1ACo_Kind.sl mm e) = decide (mm ≠ 1) := by
  cases mm with
  | zero => simp [ggK1ACo_Kind.hasOrbit]
  | succ k => cases k with
    | zero => simp [ggK1ACo_Kind.hasOrbit]
    | succ k => simp [ggK1ACo_Kind.hasOrbit]

private theorem ggK1Ak_hasOrbit_su (mm e : ℕ) :
    ggK1ACo_Kind.hasOrbit (ggK1ACo_Kind.su mm e) = decide (mm ≠ 1) := by
  cases mm with
  | zero => simp [ggK1ACo_Kind.hasOrbit]
  | succ k => cases k with
    | zero => simp [ggK1ACo_Kind.hasOrbit]
    | succ k => simp [ggK1ACo_Kind.hasOrbit]

private theorem ggK1Ak_filter_pred_sl {mm e : ℕ} :
    (ggK1ACo_Kind.hasOrbit (ggK1ACo_Kind.sl mm e) && decide (0 < mm)) = decide (2 ≤ mm) := by
  rw [ggK1Ak_hasOrbit_sl]
  by_cases h : 0 < mm
  · by_cases h1 : mm = 1
    · subst h1; rfl
    · have h2 : 2 ≤ mm := by omega
      rw [decide_eq_true_eq.mpr h1, decide_eq_true_eq.mpr h, decide_eq_true_eq.mpr h2]
      rfl
  · have h2 : ¬ 2 ≤ mm := by omega
    rw [decide_eq_false_iff_not.mpr h, decide_eq_false_iff_not.mpr h2, Bool.and_false]

private theorem ggK1Ak_filter_pred_su {mm e : ℕ} :
    (ggK1ACo_Kind.hasOrbit (ggK1ACo_Kind.su mm e) && decide (0 < mm)) = decide (2 ≤ mm) := by
  rw [ggK1Ak_hasOrbit_su]
  by_cases h : 0 < mm
  · by_cases h1 : mm = 1
    · subst h1; rfl
    · have h2 : 2 ≤ mm := by omega
      rw [decide_eq_true_eq.mpr h1, decide_eq_true_eq.mpr h, decide_eq_true_eq.mpr h2]
      rfl
  · have h2 : ¬ 2 ≤ mm := by omega
    rw [decide_eq_false_iff_not.mpr h, decide_eq_false_iff_not.mpr h2, Bool.and_false]

private theorem ggK1Ak_hasOrbit_if (tw : Bool) (mm : ℕ) :
    ggK1ACo_Kind.hasOrbit
        (if tw then ggK1ACo_Kind.su mm 1 else ggK1ACo_Kind.sl mm 1) = decide (mm ≠ 1) := by
  cases tw
  · rw [if_neg (by simp)]
    exact ggK1Ak_hasOrbit_sl mm 1
  · rw [if_pos rfl]
    exact ggK1Ak_hasOrbit_su mm 1

private theorem ggK1Ak_filter_pred_if (tw : Bool) (mm : ℕ) :
    (ggK1ACo_Kind.hasOrbit (if tw then ggK1ACo_Kind.su mm 1 else ggK1ACo_Kind.sl mm 1) &&
        decide (0 < mm)) = decide (2 ≤ mm) := by
  cases tw
  · rw [if_neg (by simp)]
    exact ggK1Ak_filter_pred_sl
  · rw [if_pos rfl]
    exact ggK1Ak_filter_pred_su

private theorem ggK1Ak_filter_pred_j (m : List ℕ) (j : ℕ) :
    (ggK1ACo_Kind.hasOrbit (ggK1ACo_Kind.sl (m.getD j 0) 2) &&
        decide (1 ≤ j ∧ 0 < m.getD j 0)) = decide (1 ≤ j ∧ 2 ≤ m.getD j 0) := by
  by_cases hj : 1 ≤ j
  · have hR : decide (1 ≤ j ∧ 2 ≤ m.getD j 0) = decide (2 ≤ m.getD j 0) := by
      congr 1
      exact propext ⟨fun h => h.2, fun h => ⟨hj, h⟩⟩
    have hL : decide (1 ≤ j ∧ 0 < m.getD j 0) = decide (0 < m.getD j 0) := by
      congr 1
      exact propext ⟨fun h => h.2, fun h => ⟨hj, h⟩⟩
    rw [hR, hL, ggK1Ak_filter_pred_sl]
  · have hP : ¬ (1 ≤ j ∧ 0 < m.getD j 0) := fun h => hj h.1
    have hQ : ¬ (1 ≤ j ∧ 2 ≤ m.getD j 0) := fun h => hj h.1
    rw [decide_eq_false_iff_not.mpr hP, decide_eq_false_iff_not.mpr hQ, Bool.and_false]

private theorem ggK1Ak_head_list {nf : ℕ} (tw : Bool) {h : ℕ} (hh : 0 < h) :
    List.map (ggK1ACo_kindOrbit nf)
        (List.filter ggK1ACo_Kind.hasOrbit
          [if tw then ggK1ACo_Kind.su h 1 else ggK1ACo_Kind.sl h 1]) =
      (if 2 ≤ h then
        (if tw = false then [⟨⟨.A, h - 1, nf⟩, decide (¬ (h - 1 = 1 ∧ nf = 1))⟩]
         else [ggMultBlockA (h - 1) nf 2]) else []) := by
  by_cases h2 : 2 ≤ h
  · rw [if_pos h2]
    rcases h with _ | _ | k
    · omega
    · omega
    · cases tw <;> simp [ggK1ACo_Kind.hasOrbit, ggK1ACo_kindOrbit, ggMultBlockA]
  · rw [if_neg h2]
    have h1 : h = 1 := by omega
    subst h1
    cases tw <;> simp [ggK1ACo_Kind.hasOrbit]

private theorem ggK1Ak_kindOrbit_sl_one {nf m : ℕ} (hm : 2 ≤ m) :
    ggK1ACo_kindOrbit nf (ggK1ACo_Kind.sl m 1) = ggMultBlockA (m - 1) nf 1 := by
  rcases m with _ | _ | k
  · omega
  · omega
  · simp [ggK1ACo_kindOrbit, ggMultBlockA]

private theorem ggK1Ak_kindOrbit_su_one {nf m : ℕ} (hm : 2 ≤ m) :
    ggK1ACo_kindOrbit nf (ggK1ACo_Kind.su m 1) = ggMultBlockA (m - 1) nf 2 := by
  rcases m with _ | _ | k
  · omega
  · omega
  · simp [ggK1ACo_kindOrbit, ggMultBlockA]

private theorem ggK1Ak_kindOrbit_sl_two {nf m : ℕ} (hm : 2 ≤ m) :
    ggK1ACo_kindOrbit nf (ggK1ACo_Kind.sl m 2) =
      (⟨⟨.A, m - 1, 2 * nf⟩, true⟩ : GGKacOrbit) := by
  rcases m with _ | _ | k
  · omega
  · omega
  · simp [ggK1ACo_kindOrbit, ggMultBlockA]

private theorem ggK1Ak_blockA_arith {nf r d : ℕ} (hnf : 1 ≤ nf) (hr : 1 ≤ r)
    (hd : d = 1 ∨ d = 2) (hqs : (ggMultBlockA r nf d).qs = true) :
    nf ∣ (ggMultBlockA r nf d).lab.n ∧ LargeEvenInLambda2 (ggMultBlockA r nf d).lab := by
  rcases hd with rfl | rfl
  · have hP : r ≠ 1 ∨ nf ≠ 1 := by simpa [ggMultBlockA] using hqs
    rw [ggMultBlockA]
    rw [if_pos (rfl : (1 : ℕ) = 1)]
    constructor
    · exact dvd_rfl
    · simp only [LargeEvenInLambda2]
      refine ⟨hnf, hr, ?_⟩
      intro hr1
      rcases hP with h | h
      · exact absurd hr1 h
      · omega
  · by_cases h2 : 2 ≤ r
    · have hP : r ≠ 2 ∨ nf ≠ 1 := by simpa [ggMultBlockA, h2] using hqs
      rw [ggMultBlockA]
      rw [if_neg (by decide : ¬ (2 : ℕ) = 1), if_pos h2]
      constructor
      · exact dvd_rfl
      · simp only [LargeEvenInLambda2]
        refine ⟨hnf, h2, ?_⟩
        intro hr2
        rcases hP with h | h
        · exact absurd hr2 h
        · omega
    · have hr1 : r = 1 := by omega
      have hP : nf ≠ 1 := by simpa [ggMultBlockA, h2] using hqs
      rw [ggMultBlockA]
      rw [if_neg (by decide : ¬ (2 : ℕ) = 1), if_neg h2]
      subst hr1
      constructor
      · exact dvd_rfl
      · simp only [LargeEvenInLambda2]
        refine ⟨hnf, le_rfl, ?_⟩
        intro _; omega

private theorem ggK1Ak_A2nf_arith {nf r : ℕ} (hnf : 1 ≤ nf) (hr : 1 ≤ r) :
    nf ∣ (2 * nf) ∧ LargeEvenInLambda2 (⟨.A, r, 2 * nf⟩ : LargeEvenLabel) := by
  constructor
  · exact dvd_mul_left nf 2
  · simp only [LargeEvenInLambda2]
    constructor
    · omega
    · constructor
      · exact hr
      · intro _; omega

private theorem ggK1Ak_orbits_eq_trivial {p nf : ℕ} {tw : Bool} {m : List ℕ}
    (h : (tw = false ∧ ggMultOrd p nf = 1) ∨ (tw = true ∧ ggMultOrd p nf = 2)) :
    (ggMultDatumA p nf (ggMultOrd p nf) tw m).orbits =
      ((List.range p).filter (fun j => decide (2 ≤ m.getD j 0))).map
        (fun j => ggMultBlockA (m.getD j 0 - 1) nf (ggMultOrd p nf)) := by
  simp only [ggMultDatumA, if_pos h]

private theorem ggK1Ak_orbits_eq_nontrivial {p nf : ℕ} {tw : Bool} {m : List ℕ}
    (h : ¬ ((tw = false ∧ ggMultOrd p nf = 1) ∨ (tw = true ∧ ggMultOrd p nf = 2))) :
    (ggMultDatumA p nf (ggMultOrd p nf) tw m).orbits =
      (if 2 ≤ m.headD 0 then
        (if tw = false then
          [⟨⟨.A, m.headD 0 - 1, nf⟩, decide (¬ (m.headD 0 - 1 = 1 ∧ nf = 1))⟩]
         else [ggMultBlockA (m.headD 0 - 1) nf 2])
       else []) ++
      ((List.range ((p - 1) / 2 + 1)).filter (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0))).map
        (fun j => (⟨⟨.A, m.getD j 0 - 1, 2 * nf⟩, true⟩ : GGKacOrbit)) := by
  simp only [ggMultDatumA, if_neg h]

theorem ggK1ACo_kindOrbit_multiset (p nf : ℕ) (tw : Bool) (m : List ℕ) :
    (ggK1ACo_orbitKindList p nf tw m).map (ggK1ACo_kindOrbit nf) =
      (ggMultDatumA p nf (ggMultOrd p nf) tw m).orbits := by
  classical
  rw [ggK1ACo_orbitKindList]
  by_cases htriv : (tw = false ∧ ggMultOrd p nf = 1) ∨ (tw = true ∧ ggMultOrd p nf = 2)
  · rw [ggK1ACo_expectedKindList, if_pos htriv, ggK1Ak_orbits_eq_trivial htriv]
    rw [List.filter_map, List.map_map]
    rw [List.filter_filter]
    simp only [Function.comp_apply]
    rw [List.filter_congr (fun j _ => ggK1Ak_filter_pred_if tw (m.getD j 0))]
    apply List.map_congr_left
    intro j hj
    rw [List.mem_filter] at hj
    obtain ⟨-, hj2⟩ := hj
    have hj2' : 2 ≤ m.getD j 0 := by simpa using hj2
    cases tw
    · have hd1 : ggMultOrd p nf = 1 := by
        rcases htriv with ⟨-, hh⟩ | ⟨hh, -⟩
        · exact hh
        · exact absurd hh (by simp)
      rw [hd1]
      change ggK1ACo_kindOrbit nf (ggK1ACo_Kind.sl (m.getD j 0) 1) =
        ggMultBlockA (m.getD j 0 - 1) nf 1
      rw [ggK1Ak_kindOrbit_sl_one hj2']
    · have hd2 : ggMultOrd p nf = 2 := by
        rcases htriv with ⟨hh, -⟩ | ⟨-, hh⟩
        · exact absurd hh (by simp)
        · exact hh
      rw [hd2]
      change ggK1ACo_kindOrbit nf (ggK1ACo_Kind.su (m.getD j 0) 1) =
        ggMultBlockA (m.getD j 0 - 1) nf 2
      rw [ggK1Ak_kindOrbit_su_one hj2']
  · rw [ggK1ACo_expectedKindList, if_neg htriv, ggK1Ak_orbits_eq_nontrivial htriv]
    rw [List.filter_append, List.map_append]
    congr 1
    · by_cases h0 : 0 < m.headD 0
      · rw [if_pos h0]
        exact ggK1Ak_head_list tw h0
      · rw [if_neg h0, if_neg (by omega : ¬ 2 ≤ m.headD 0)]
        rfl
    · rw [List.filter_map, List.map_map, List.filter_filter]
      simp only [Function.comp_apply]
      rw [List.filter_congr (fun j _ => ggK1Ak_filter_pred_j m j)]
      apply List.map_congr_left
      intro j hj
      rw [List.mem_filter] at hj
      obtain ⟨-, hj2⟩ := hj
      have hj2' : 2 ≤ m.getD j 0 := (of_decide_eq_true hj2).2
      change ggK1ACo_kindOrbit nf (ggK1ACo_Kind.sl (m.getD j 0) 2) =
        (⟨⟨.A, m.getD j 0 - 1, 2 * nf⟩, true⟩ : GGKacOrbit)
      rw [ggK1Ak_kindOrbit_sl_two hj2']

private theorem ggK1Ak_natCard_eq {E : Type} (hF : Fintype E) {N : ℕ}
    (h : @Fintype.card E hF = N) : Nat.card E = N := by
  rw [@Nat.card_eq_fintype_card E hF]
  exact h

private theorem ggK1Ak_statedProj_equiv_largeEvenProj {d : ℕ} {E : Type} [Field E] :
    Nonempty (StatedProj (StatedSL d E) ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) E)) := by
  let eG : ↥(LargeEvenSLGroup (Fin d) E) ≃* ↥(StatedSL d E) :=
    MulEquiv.subgroupCongr (largeEvenSLGroup_eq_statedSL (K := E) d)
  have hM : Subgroup.map (↑eG)
        ((LargeEvenScalars (Fin d) E).subgroupOf (LargeEvenSLGroup (Fin d) E)) =
      (StatedScalars (Fin d) E).subgroupOf (StatedSL d E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' : (y : GL (Fin d) E) ∈ LargeEvenScalars (Fin d) E :=
        Subgroup.mem_subgroupOf.mp hy
      exact Subgroup.mem_subgroupOf.mpr (by
        change (MulEquiv.subgroupCongr (largeEvenSLGroup_eq_statedSL (K := E) d) y :
          GL (Fin d) E) ∈ StatedScalars (Fin d) E
        rw [MulEquiv.subgroupCongr_apply, ← largeEvenScalars_eq_statedScalars]
        exact hy')
    · intro hx
      have hx' : (x : GL (Fin d) E) ∈ LargeEvenScalars (Fin d) E := by
        rw [largeEvenScalars_eq_statedScalars]
        exact Subgroup.mem_subgroupOf.mp hx
      refine ⟨eG.symm x, Subgroup.mem_subgroupOf.mpr ?_, eG.apply_symm_apply x⟩
      change ((MulEquiv.subgroupCongr (largeEvenSLGroup_eq_statedSL (K := E) d)).symm x :
        GL (Fin d) E) ∈ LargeEvenScalars (Fin d) E
      rw [MulEquiv.subgroupCongr_symm_apply]
      exact hx'
  exact ⟨(QuotientGroup.congr _ _ eG hM).symm⟩

theorem ggK1ACo_kind_label {nf : ℕ} {K : Type} [Field K] (kind : ggK1ACo_Kind)
    (H : Type) [Group H] (hq : CFSG.IsQuasisimple H)
    (hm : ggK1ACo_Kind.Model nf K kind H) :
    GGHasLabel (ggK1ACo_kindOrbit nf kind).lab (H ⧸ Subgroup.center H) := by
  classical
  cases kind with
  | sl m e =>
    obtain ⟨E, hFieldE, hFintypeE, hcard, ⟨eH⟩⟩ := hm
    haveI : Fintype E := hFintypeE
    haveI : Finite E := inferInstance
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · exfalso
      have hm01 : m = 0 ∨ m = 1 := by omega
      haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin m) E) := by
        rcases hm01 with rfl | rfl
        · exact Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
        · exact Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
      haveI : Subsingleton H :=
        ⟨fun x y => eH.injective (Subsingleton.elim (eH x) (eH y))⟩
      haveI : Subsingleton (H ⧸ Subgroup.center H) := inferInstance
      obtain ⟨-, -, a, b, hab⟩ := hq
      exact hab (Subsingleton.elim _ _)
    · have hlabel : (ggK1ACo_kindOrbit nf (ggK1ACo_Kind.sl m e)).lab =
          ⟨.A, m - 1, e * nf⟩ := by
        rcases m with _ | _ | k
        · omega
        · omega
        · simp [ggK1ACo_kindOrbit, ggMultBlockA]
      rw [hlabel]
      simp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeLinear]
      refine ⟨E, hFieldE, (inferInstance : Finite E), ?_, ?_⟩
      · have hcard' : Nat.card E = (2 ^ nf) ^ e := ggK1Ak_natCard_eq hFintypeE hcard
        rw [hcard', show (2 ^ nf) ^ e = 2 ^ (e * nf) by rw [← pow_mul, Nat.mul_comm]]
      · have hm' : (m - 1) + 1 = m := by omega
        have eSL : H ≃* StatedSL ((m - 1) + 1) E := by
          rw [hm']
          exact eH.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E)
        obtain ⟨e2⟩ := ggK1Ak_statedProj_equiv_largeEvenProj (d := (m - 1) + 1) (E := E)
        exact (nonempty_quotientCenter_equiv_statedProj eSL).map (fun e => e.trans e2)
  | su m e =>
    obtain ⟨E, hFieldE, hFintypeE, hcard, ⟨eH⟩⟩ := hm
    haveI : Finite E := inferInstance
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · exfalso
      have hcommH : ∀ x y : StatedSU m ((2 ^ nf) ^ e) E, x * y = y * x := by
        intro x y
        rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
        · exact Subsingleton.elim _ _
        · exact CFSG.LieType.SemisimpleCentralizers.OrderThree.mul_comm_statedSU_of_le_one
            le_rfl x y
      have hcommHe : ∀ x y : H, x * y = y * x := by
        intro x y
        apply eH.injective
        rw [map_mul, map_mul]
        exact hcommH (eH x) (eH y)
      obtain ⟨-, -, a, b, hab⟩ := hq
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      refine hab ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact hcommHe x y
    · have hp : (2 ^ nf) ^ e = 2 ^ (e * nf) := by rw [← pow_mul, Nat.mul_comm]
      have hcard0 : Nat.card E = ((2 ^ nf) ^ e) ^ 2 := by
        rw [ggK1Ak_natCard_eq hFintypeE hcard]
        rw [show (2 ^ nf) ^ (2 * e) = ((2 ^ nf) ^ e) ^ 2 by rw [← pow_mul, ← pow_mul]; ring]
      have hcard2 : Nat.card E = (2 ^ (e * nf)) ^ 2 := by rw [hcard0, hp]
      rw [hp] at eH
      rcases Nat.lt_or_ge m 3 with hm3 | hm3
      ·
        have hm_eq : m = 2 := by omega
        subst hm_eq
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hFcard : Fintype.card E = 2 ^ (2 * (e * nf)) := by
          rw [hcard, show (2 ^ nf) ^ (2 * e) = 2 ^ (2 * (e * nf)) by rw [← pow_mul]; ring]
        haveI : CharP E 2 := charP_of_card_eq_prime_pow (f := 2 * (e * nf)) hFcard
        have hlabel : (ggK1ACo_kindOrbit nf (ggK1ACo_Kind.su 2 e)).lab =
            ⟨.A, 1, e * nf⟩ := by
          simp [ggK1ACo_kindOrbit, ggMultBlockA]
        rw [hlabel]
        simp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeLinear]
        refine ⟨CFSG.LieType.Steinberg.fixedSubfield E 2 (e * nf), inferInstance, inferInstance,
          CFSG.LieType.Steinberg.card_fixedSubfield hcard2, ?_⟩
        obtain ⟨e2⟩ :=
          CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
            (K := E) (r := 2) (f := e * nf) hcard2
        have eSL : H ≃* StatedSL 2 (CFSG.LieType.Steinberg.fixedSubfield E 2 (e * nf)) :=
          (eH.trans e2.symm).trans
            (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 _)
        obtain ⟨e2'⟩ := ggK1Ak_statedProj_equiv_largeEvenProj (d := 2)
          (E := CFSG.LieType.Steinberg.fixedSubfield E 2 (e * nf))
        exact (nonempty_quotientCenter_equiv_statedProj eSL).map (fun ee => ee.trans e2')
      ·
        have hlabel : (ggK1ACo_kindOrbit nf (ggK1ACo_Kind.su m e)).lab =
            ⟨.twA, m - 1, e * nf⟩ := by
          rcases m with _ | _ | _ | k
          · omega
          · omega
          · omega
          · simp [ggK1ACo_kindOrbit, ggMultBlockA]
        rw [hlabel]
        by_cases hf : 2 ≤ e * nf
        · obtain ⟨eiso⟩ :=
            nonempty_quotientCenter_equiv_statedProj_statedSU
              (K := E) hcard2 hf (by omega : 2 ≤ m) eH
          have hm1 : (m - 1) + 1 = m := by omega
          have eiso' : H ⧸ Subgroup.center H ≃*
              StatedProj (StatedSU ((m - 1) + 1) (2 ^ (e * nf)) E) := by
            rw [hm1]; exact eiso
          exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA
            (b := m - 1) (m := e * nf) hcard2 eiso'
        · have hf1 : e * nf = 1 := by
            have hne : e * nf ≠ 0 := by
              intro h0
              have h1 : 1 < Fintype.card E := Fintype.one_lt_card
              rw [hcard] at h1
              rcases Nat.eq_zero_or_pos e with he | he
              · subst he; simp at h1
              · rcases Nat.eq_zero_or_pos nf with hnf | hnf
                · subst hnf; simp at h1
                · exact absurd h0 (Nat.mul_ne_zero he.ne' hnf.ne')
            omega
          rw [hf1] at eH ⊢
          have hcard4 : Nat.card E = (2 ^ 1) ^ 2 := by rw [hcard2, hf1]
          by_cases hm3eq : m = 3
          · exfalso
            subst hm3eq
            haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
            have hFcard4 : Fintype.card E = 2 ^ 2 := by
              rw [← Nat.card_eq_fintype_card, hcard4]
              norm_num
            haveI : CharP E 2 := charP_of_card_eq_prime_pow (f := 2) hFcard4
            have h216 := card_statedSU_three_two_of_card_four (K := E) hcard4
            haveI : Fintype (StatedSU 3 (2 ^ 1) E) := Fintype.ofFinite _
            have hcardF : Fintype.card (StatedSU 3 (2 ^ 1) E) = 2 ^ 3 * 3 ^ 3 := by
              rw [← Nat.card_eq_fintype_card, h216]
              norm_num
            have hsolv : Group.IsSolvable (StatedSU 3 (2 ^ 1) E) :=
              CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
                Nat.prime_two Nat.prime_three (by norm_num) hcardF
            haveI hsolvH : Group.IsSolvable H :=
              solvable_of_solvable_injective (f := eH.toMonoidHom) eH.injective
            obtain ⟨-, hsimple, -⟩ := hq
            exact @CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.not_isSolvable_quot_center H _ hsimple
              (Group.instIsSolvableQuotientSubgroup (Subgroup.center H))
          · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
            have hFcard4 : Fintype.card E = 2 ^ 2 := by
              rw [← Nat.card_eq_fintype_card, hcard4]
              norm_num
            haveI : CharP E 2 := charP_of_card_eq_prime_pow (f := 2) hFcard4
            have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
                (F := E) (p := 2) (f := 1) (n := m) hcard4 (by omega)
                (by intro hcon; exact hm3eq (Prod.mk.inj hcon).1)).2
            have eiso : H ⧸ Subgroup.center H ≃* StatedProj (StatedSU m (2 ^ 1) E) :=
              (QuotientGroup.congr (Subgroup.center H) (Subgroup.center (StatedSU m (2 ^ 1) E))
                eH (Subgroup.map_center_eq eH)).trans (QuotientGroup.quotientMulEquivOfEq hZ)
            have hm1 : (m - 1) + 1 = m := by omega
            have eiso' : H ⧸ Subgroup.center H ≃*
                StatedProj (StatedSU ((m - 1) + 1) (2 ^ 1) E) := by
              rw [hm1]; exact eiso
            exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA
              (b := m - 1) (m := 1) hcard4 eiso'

theorem ggK1ACo_orbit_arith {p nf : ℕ} {tw : Bool} {m : List ℕ} (hnf : 1 ≤ nf) {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumA p nf (ggMultOrd p nf) tw m).orbits) (hqs : o.qs = true) :
    nf ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab := by
  classical
  by_cases htriv : (tw = false ∧ ggMultOrd p nf = 1) ∨ (tw = true ∧ ggMultOrd p nf = 2)
  · rw [ggK1Ak_orbits_eq_trivial (p := p) (nf := nf) (tw := tw) (m := m) htriv] at ho
    rw [List.mem_map] at ho
    obtain ⟨j, hj, rfl⟩ := ho
    rw [List.mem_filter] at hj
    obtain ⟨-, hj2⟩ := hj
    have hj2' : 2 ≤ m.getD j 0 := by simpa using hj2
    have hd : ggMultOrd p nf = 1 ∨ ggMultOrd p nf = 2 :=
      htriv.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
    exact ggK1Ak_blockA_arith hnf (by omega) hd (by simpa using hqs)
  · rw [ggK1Ak_orbits_eq_nontrivial (p := p) (nf := nf) (tw := tw) (m := m) htriv] at ho
    rw [List.mem_append] at ho
    rcases ho with ho | ho
    · by_cases h0 : 2 ≤ m.headD 0
      · rw [if_pos h0] at ho
        by_cases htw : tw = false
        · rw [if_pos htw] at ho
          rw [List.mem_singleton] at ho
          rw [ho] at hqs ⊢
          change nf ∣ (ggMultBlockA (m.headD 0 - 1) nf 1).lab.n ∧
            LargeEvenInLambda2 (ggMultBlockA (m.headD 0 - 1) nf 1).lab
          exact ggK1Ak_blockA_arith hnf (by omega) (Or.inl rfl) hqs
        · rw [if_neg htw] at ho
          rw [List.mem_singleton] at ho
          rw [ho] at hqs ⊢
          exact ggK1Ak_blockA_arith hnf (by omega) (Or.inr rfl) hqs
      · rw [if_neg h0] at ho
        simp at ho
    · rw [List.mem_map] at ho
      obtain ⟨j, hj, ho⟩ := ho
      rw [List.mem_filter] at hj
      obtain ⟨-, hj2⟩ := hj
      have hj2' : 2 ≤ m.getD j 0 := (of_decide_eq_true hj2).2
      rw [← ho] at hqs ⊢
      exact ggK1Ak_A2nf_arith hnf (by omega)

private theorem ggK1Ak_card_fiber {ι γ : Type} [Fintype ι] [DecidableEq γ] (f : ι → γ) (c : γ) :
    Fintype.card {i : ι // f i = c} =
      Multiset.count c (Multiset.map f (Finset.univ : Finset ι).val) := by
  classical
  rw [Fintype.card_subtype, Finset.card_def, Multiset.count_map, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun a _ => eq_comm

private theorem ggK1Ak_exists_equiv_of_multiset {α β γ : Type} [Fintype α] [Fintype β]
    [DecidableEq γ] (f : α → γ) (g : β → γ)
    (h : Multiset.map f (Finset.univ : Finset α).val =
      Multiset.map g (Finset.univ : Finset β).val) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a := by
  have hcard : ∀ c : γ, Fintype.card {a : α // f a = c} = Fintype.card {b : β // g b = c} := by
    intro c
    rw [ggK1Ak_card_fiber f c, ggK1Ak_card_fiber g c, h]
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hcard c)), ?_⟩
  intro a
  exact Equiv.ofFiberEquiv_map _ a

private theorem ggK1Ak_map_subtype_filter {α γ : Type} [Fintype α] (f : α → γ) (q : γ → Bool) :
    Multiset.map (fun a : {a : α // q (f a) = true} => f a.1)
        (Finset.univ : Finset {a : α // q (f a) = true}).val =
      (Multiset.map f (Finset.univ : Finset α).val).filter (fun o => q o = true) := by
  classical
  rw [Multiset.ext]
  intro c
  rw [← ggK1Ak_card_fiber (fun a : {a : α // q (f a) = true} => f a.1) c,
    Multiset.count_filter]
  by_cases hc : q c = true
  · rw [if_pos hc, ← ggK1Ak_card_fiber f c]
    exact Fintype.card_congr
      { toFun := fun a => ⟨a.1.1, a.2⟩
        invFun := fun a => ⟨⟨a.1, by rw [a.2]; exact hc⟩, a.2⟩
        left_inv := fun a => by ext <;> rfl
        right_inv := fun a => by ext <;> rfl }
  · rw [if_neg hc, Fintype.card_eq_zero_iff]
    refine ⟨fun a => ?_⟩
    exact hc (by rw [← a.2]; exact a.1.2)

private theorem ggK1Ak_filter_map_eq {α γ : Type} (p : α → Bool) (q : γ → Bool)
    (f : α → γ) (l : List α) (hf : ∀ a, p a = false → q (f a) = false) :
    (Multiset.map f (l : Multiset α)).filter (fun o => q o = true) =
      (Multiset.map f ((l.filter p) : Multiset α)).filter (fun o => q o = true) := by
  classical
  rw [Multiset.map_coe, Multiset.map_coe, Multiset.filter_coe, Multiset.filter_coe]
  congr 1
  rw [List.filter_map, List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro a _
  simp only [Function.comp_apply]
  cases hq : q (f a) <;> cases hp : p a <;> simp_all

private theorem ggK1Ak_map_finRange {γ : Type} (l : List γ) :
    Multiset.map (fun k : Fin l.length => l[k]) (Finset.univ : Finset (Fin l.length)).val =
      (l : Multiset γ) := by
  rw [Finset.val_univ_fin]
  rw [Multiset.map_coe]
  rw [show (List.finRange l.length).map (fun k : Fin l.length => l[k]) = l from by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_get l]

theorem ggK1ACo_pos_equiv {nf : ℕ} {ι : Type} [Fintype ι] (kind : ι → ggK1ACo_Kind)
    (L : List ggK1ACo_Kind) (O : List GGKacOrbit)
    (hmult : (Finset.univ : Finset ι).val.map kind = (L : Multiset ggK1ACo_Kind))
    (hO : (L.filter (fun k => ggK1ACo_Kind.hasOrbit k)).map (ggK1ACo_kindOrbit nf) = O) :
    ∃ g : {i : ι // (ggK1ACo_kindOrbit nf (kind i)).qs = true} ≃
        {k : Fin O.length // O[k].qs = true},
      ∀ i, O[(g i).1] = ggK1ACo_kindOrbit nf (kind i.1) := by
  classical
  let f : ι → GGKacOrbit := fun i => ggK1ACo_kindOrbit nf (kind i)
  have hf : Multiset.map f (Finset.univ : Finset ι).val =
      Multiset.map (ggK1ACo_kindOrbit nf) (L : Multiset ggK1ACo_Kind) := by
    have h1 : Multiset.map (fun i => ggK1ACo_kindOrbit nf (kind i))
          (Finset.univ : Finset ι).val =
        Multiset.map (ggK1ACo_kindOrbit nf)
          (Multiset.map kind (Finset.univ : Finset ι).val) := by
      simp [Multiset.map_map, Function.comp_def]
    rw [h1, hmult]
  have hO' : (Multiset.map (ggK1ACo_kindOrbit nf)
      ((L.filter (fun k => ggK1ACo_Kind.hasOrbit k)) : Multiset ggK1ACo_Kind)) =
      (O : Multiset GGKacOrbit) := by
    rw [← hO, Multiset.map_coe]
  have hval : (Multiset.map f (Finset.univ : Finset ι).val).filter (fun o => o.qs = true) =
      (Multiset.map (fun k : Fin O.length => O[k]) (Finset.univ : Finset (Fin O.length)).val).filter
        (fun o => o.qs = true) := by
    rw [ggK1Ak_map_finRange O, hf, ← hO']
    rw [ggK1Ak_filter_map_eq (fun k => ggK1ACo_Kind.hasOrbit k) (fun o => o.qs)
      (ggK1ACo_kindOrbit nf) L (fun k hk => by
        cases k with
        | sl a b =>
          cases a with
          | zero => simp [ggK1ACo_Kind.hasOrbit] at hk
          | succ j =>
            cases j with
            | zero => rfl
            | succ j => simp [ggK1ACo_Kind.hasOrbit] at hk
        | su a b =>
          cases a with
          | zero => simp [ggK1ACo_Kind.hasOrbit] at hk
          | succ j =>
            cases j with
            | zero => rfl
            | succ j => simp [ggK1ACo_Kind.hasOrbit] at hk)]
  have hsub : Multiset.map (fun i : {i : ι // (f i).qs = true} => f i.1)
        (Finset.univ : Finset {i : ι // (f i).qs = true}).val =
      Multiset.map (fun k : {k : Fin O.length // O[k].qs = true} => O[k.1])
        (Finset.univ : Finset {k : Fin O.length // O[k].qs = true}).val := by
    rw [ggK1Ak_map_subtype_filter f (fun o => o.qs),
      ggK1Ak_map_subtype_filter (fun k : Fin O.length => O[k]) (fun o => o.qs)]
    exact hval
  obtain ⟨e, he⟩ := ggK1Ak_exists_equiv_of_multiset
    (fun i : {i : ι // (f i).qs = true} => f i.1)
    (fun k : {k : Fin O.length // O[k].qs = true} => O[k.1]) hsub
  exact ⟨e, fun i => he i⟩

end CFSG.StandardType

end
