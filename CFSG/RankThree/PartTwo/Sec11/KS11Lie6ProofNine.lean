module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofTheta
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofOut

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof

@[expose] def shortExp9 (r : ZMod 9) (j : Fin TwistTag.D4.tag.rank) : ZMod 9 :=
  ((TwistTag.D4.tag.cartan n0 j : ℤ) : ZMod 9) + r * ((TwistTag.D4.tag.cartan n1 j : ℤ) : ZMod 9) +
    r ^ 2 * ((TwistTag.D4.tag.cartan n3 j : ℤ) : ZMod 9)

@[expose] def shortVal9 (r : ZMod 9) (v : Fin TwistTag.D4.tag.rank → ℤ) : ZMod 9 :=
  ∑ j, ((v j : ℤ) : ZMod 9) * shortExp9 r j

@[expose] def units9 : List (ZMod 9) := [1, 2, 4, 5, 7, 8]

theorem cast_shortVal (q : ℤ) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    ((shortVal q v : ℤ) : ZMod 9) = shortVal9 (q : ZMod 9) v := by
  simp only [shortVal, shortVal9, shortExp, shortExp9]
  push_cast
  rfl

theorem shortVal9_single : ∀ (r : ZMod 9) (i : Fin TwistTag.D4.tag.rank),
    shortVal9 r (Pi.single i 1) = shortExp9 r i := by
  decide

theorem mem_units9 {q : ℕ} (hq : ¬ 3 ∣ q) : (q : ZMod 9) ∈ units9 := by
  have h : q % 9 = 1 ∨ q % 9 = 2 ∨ q % 9 = 4 ∨ q % 9 = 5 ∨ q % 9 = 7 ∨ q % 9 = 8 := by omega
  rw [← ZMod.natCast_mod]
  rcases h with h | h | h | h | h | h <;> rw [h] <;> decide

theorem kerCheck9 : ∀ r ∈ units9, ∀ k : Fin 24,
    shortVal9 r (d4RootVec k) = 0 → k = 22 ∨ k = 23 := by
  decide

@[expose] def sThetaWord : List (Fin TwistTag.D4.tag.rank) := [2, 0, 1, 3, 2, 3, 1, 0, 2]

@[expose] def stabCheck9 : Bool :=
  d4WeylTab.all fun e => units9.all fun r =>
    !(decide (∀ i, shortVal9 r (colOf e i) = shortExp9 r i)) ||
      decide (∀ i, colOf e i = Pi.single i 1) ||
      decide (∀ i, colOf e i = wordVec sThetaWord (Pi.single i 1))

theorem stabCheck9_eq : stabCheck9 = true := by decide +kernel

theorem wordVec_theta : wordVec [2, 0, 1, 3] (Pi.single n2 1) = thetaVec := by decide

theorem shortVal_theta (q : ℤ) : shortVal q thetaVec = 0 := by
  rw [shortVal_eq]
  have h0 : pairK n0 thetaVec = 0 := by decide
  have h1 : pairK n1 thetaVec = 0 := by decide
  have h3 : pairK n3 thetaVec = 0 := by decide
  rw [h0, h1, h3]
  ring

variable
  {L : Type} [Field L]

theorem outerTriple_HSL_short (q : ℕ) (μ : Lˣ) :
    outerTriple L (HSL μ, HSL (μ ^ q), HSL (μ ^ (q ^ 2))) =
      rootDiagUnit TwistTag.D4.tag (fun j => μ ^ shortExp (q : ℤ) j) := by
  rw [outerTriple_HSL_units]
  congr 1
  funext j
  simp only [shortExp, zpow_add, zpow_mul, zpow_natCast, ← Nat.cast_pow]

theorem nine_dvd_of_zpow_eq_one {μ : Lˣ} (hμ : 9 ∣ orderOf μ) {n : ℤ} (h : μ ^ n = 1) :
    ((n : ℤ) : ZMod 9) = 0 := by
  have h1 := orderOf_dvd_iff_zpow_eq_one.2 h
  have h2 : (9 : ℤ) ∣ n := (Int.natCast_dvd_natCast.2 hμ).trans h1
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd n 9).2 h2

theorem rootCharKernel_short_subset {q : ℕ} (hq : ¬ 3 ∣ q) {μ : Lˣ} (hμ : 9 ∣ orderOf μ) :
    rootCharKernel (fun j => μ ^ shortExp (q : ℤ) j) ⊆ {thetaVec, -thetaVec} := by
  rintro α ⟨hα, h1⟩
  obtain ⟨k, rfl⟩ := isRoot_iff_exists_d4RootVec.1 hα
  have h1' : μ ^ shortVal (q : ℤ) (d4RootVec k) = 1 :=
    (KS11Lie5Proof.rootChar_pow_tuple μ (shortExp (q : ℤ)) (d4RootVec k)).symm.trans h1
  have h9 := nine_dvd_of_zpow_eq_one hμ h1'
  have h9' : shortVal9 ((q : ℤ) : ZMod 9) (d4RootVec k) = 0 :=
    (cast_shortVal _ _).symm.trans h9
  have hr : ((q : ℤ) : ZMod 9) ∈ units9 := by
    rw [Int.cast_natCast]
    exact mem_units9 hq
  rcases kerCheck9 _ hr k h9' with rfl | rfl
  · exact Or.inl rfl
  · have h23 : (d4RootVec 23 : Fin TwistTag.D4.tag.rank → ℤ) = -thetaVec := by
      funext i
      fin_cases i <;> rfl
    exact Or.inr h23

theorem wordProd_sTheta_mem_closure {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (ha : rootChar a thetaVec = 1) :
    (coxeterSystem TwistTag.D4.tag).wordProd sThetaWord ∈ Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} := by
  have hw : (coxeterSystem TwistTag.D4.tag).wordProd [2, 0, 1, 3] •
      (Pi.single n2 1 : Fin TwistTag.D4.tag.rank → ℤ) = thetaVec := by
    rw [KS11Lie5Proof.wordProd_smul, wordVec_theta]
  have hθ : IsRoot TwistTag.D4.tag thetaVec := by
    rw [← hw]
    exact IsRoot.smul (isRoot_single _ n2) _
  refine Subgroup.subset_closure ⟨thetaVec, ⟨hθ, ha⟩, ?_⟩
  rw [rootReflection_eq_conj hw, sThetaWord,
    show ([2, 0, 1, 3, 2, 3, 1, 0, 2] : List (Fin TwistTag.D4.tag.rank)) =
      [2, 0, 1, 3] ++ [2] ++ [2, 0, 1, 3].reverse by rfl,
    CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append,
    CoxeterSystem.wordProd_reverse, CoxeterSystem.wordProd_singleton]
  rfl

theorem stab_short_subset_closure {q : ℕ} (hq : ¬ 3 ∣ q) {μ : Lˣ} (hμ : 9 ∣ orderOf μ) :
    rootCharStabilizer (fun j => μ ^ shortExp (q : ℤ) j) ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel (fun j => μ ^ shortExp (q : ℤ) j), s = rootReflection α} :
        Set (WeylGroup TwistTag.D4.tag)) := by
  intro w hw
  obtain ⟨e, he, hwe⟩ := exists_mem_d4WeylTab w
  have hcol : ∀ i, w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = colOf e i := hwe
  have hr : ((q : ℤ) : ZMod 9) ∈ units9 := by
    rw [Int.cast_natCast]
    exact mem_units9 hq
  have hcong : ∀ i, shortVal9 ((q : ℤ) : ZMod 9) (colOf e i) =
      shortExp9 ((q : ℤ) : ZMod 9) i := by
    intro i
    have h := hw (Pi.single i 1)
    rw [hcol, KS11Lie5Proof.rootChar_pow_tuple, KS11Lie5Proof.rootChar_pow_tuple] at h
    have h1 : μ ^ (shortVal (q : ℤ) (colOf e i) - shortVal (q : ℤ) (Pi.single i 1)) = 1 := by
      rw [zpow_sub]
      exact mul_inv_eq_one.2 h
    have h2 := nine_dvd_of_zpow_eq_one hμ h1
    rw [Int.cast_sub, cast_shortVal, cast_shortVal, shortVal9_single, sub_eq_zero] at h2
    exact h2
  have h := List.all_eq_true.1 stabCheck9_eq e he
  have h' := List.all_eq_true.1 h _ hr
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h'
  rcases h' with (h' | h') | h'
  · exact absurd hcong h'
  · have hw1 : w = 1 := ext_single fun i => by rw [hcol, h', one_smul]
    rw [hw1]
    exact one_mem _
  · have hw2 : w = (coxeterSystem TwistTag.D4.tag).wordProd sThetaWord :=
      eq_wordProd_of_col hcol h'
    rw [hw2]
    refine wordProd_sTheta_mem_closure ?_
    rw [KS11Lie5Proof.rootChar_pow_tuple]
    change μ ^ shortVal (q : ℤ) thetaVec = 1
    rw [shortVal_theta, zpow_zero]

theorem toralCentralizer_short_le {q : ℕ} (hq : ¬ 3 ∣ q) {μ : Lˣ} (hμ : 9 ∣ orderOf μ) :
    toralCentralizer TwistTag.D4.tag L (fun j => μ ^ shortExp (q : ℤ) j) ≤
      torusGroup TwistTag.D4.tag L ⊔ thetaPair L := by
  have hθ : IsRoot TwistTag.D4.tag thetaVec := by
    rw [← wordVec_theta, ← KS11Lie5Proof.wordProd_smul]
    exact IsRoot.smul (isRoot_single _ n2) _
  have h := toralCentralizer_le_sup_rootSpan_of_stab (stab_short_subset_closure hq hμ)
    (S := {thetaVec, -thetaVec}) (by
      rintro α (rfl | rfl)
      · exact hθ
      · exact IsRoot.neg hθ) (by
      rintro α (rfl | rfl)
      · exact Or.inr rfl
      · left
        exact neg_neg _) (rootCharKernel_short_subset hq hμ)
  rwa [rootSpan, iSup_insert, iSup_singleton] at h

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
