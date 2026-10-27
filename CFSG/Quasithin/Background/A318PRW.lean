module

public import CFSG.LieType.Chevalley.CharTwoRank

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

section RootWitnessFacts

open CFSG.LieType.Chevalley.RootWitness

theorem charTwo_facts_of_rankOne
    {τ : Tag} {n : ℕ} (W : RootWitness τ n) (hW : W.check = true)
    (hO : W.orthoCheck = true) {K : Type} [Field K] [CharP K 2]
    (hZ : ∀ i, rankOneZ (τ := τ) (K := K) (W.simple i) ^ 3 = 1 ∧
      ¬ Commute (rankOneZ (K := K) (W.simple i))
        ((rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1) ∧
      ¬ Commute (rankOneZ (K := K) (W.simple i) ^ 2)
        ((rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1)) :
    (∀ i, W.elemZ K i ^ 3 = 1 ∧ ¬ Commute (W.elemZ K i) (W.elemA K i) ∧
      ¬ Commute (W.elemZ K i ^ 2) (W.elemA K i)) ∧
    (∀ i j, i ≠ j → Commute (W.elemZ K j) (W.elemA K i)) ∧
    (∀ i j, i ≠ j → Commute (W.elemZ K i) (W.elemZ K j)) ∧
    (∀ i j, i ≠ j → Commute (W.elemA K i) (W.elemA K j) ∧ Commute (W.elemB K i) (W.elemB K j) ∧
      Commute (W.elemA K i) (W.elemB K j)) := by
  simp only [check, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq] at hW
  simp only [orthoCheck, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq] at hO
  have hpos : ∀ i, 0 < height (W.root i).1 := fun i => by rw [root_val]; exact (hW i).1.1.1
  have hnn : ∀ i k, 0 ≤ (W.root i).1 k := fun i k => by rw [root_val]; exact (hW i).1.1.2 k
  have hne0 : ∀ i, (W.root i).1 ≠ 0 := fun i h => by
    have := hpos i
    rw [h] at this
    simp [height] at this
  set s : Fin n → WeylGroup τ := fun i => (coxeterSystem τ).wordProd (W.sepWord i)
  have hact : ∀ i j, (s i) • (W.root j).1 = (W.sepWord i).foldr (reflect τ) (W.vec j) :=
    fun i j => by rw [root_val, wordProd_smul]
  have hfix : ∀ i j, i ≠ j → s i • W.root j = W.root j := fun i j hij => Subtype.ext (by
    rw [coe_smul_root, hact, root_val]
    rcases (hO i).2 j with h | h
    · exact absurd h hij
    · exact h)
  have hflip : ∀ i, s i • W.root i = -W.root i := fun i => Subtype.ext (by
    rw [coe_smul_root, hact, coe_neg_root, root_val]
    exact (hO i).1)
  have hroot_ne : ∀ i j, i ≠ j → W.root i ≠ W.root j := fun i j hij h => by
    have h1 := hflip i
    rw [h, hfix i j hij] at h1
    have h3 := congrArg (fun r : Root τ => height r.1) h1
    simp only [coe_neg_root, height_neg] at h3
    have := hpos j
    omega
  have hXX : ∀ i j, i ≠ j → ∀ x ∈ (rootOperatorFamily τ).rootSubgroup K (W.root i),
      ∀ y ∈ (rootOperatorFamily τ).rootSubgroup K (W.root j), Commute x y := by
    intro i j hij x hx y hy
    obtain ⟨c, rfl⟩ := (rootOperatorFamily τ).mem_rootSubgroup.1 hx
    obtain ⟨d, rfl⟩ := (rootOperatorFamily τ).mem_rootSubgroup.1 hy
    have hpf : pairFree τ (W.root i).1 (W.root j).1 = true := by
      rw [root_val, root_val]
      rcases (hW i).2 j with h | h
      · exact absurd h hij
      · exact h.1
    exact commute_rootHom_of_not_isRoot (hpos i) (hpos j) (hroot_ne i j hij)
      (fun a b ha hb => not_isRoot_of_pairFree (hnn i) (hne0 i) (hnn j) (hne0 j) hpf ha hb)
      (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)
  have hXX' : ∀ i j, i ≠ j → ∀ (εi εj : Bool),
      ∀ x ∈ (rootOperatorFamily τ).rootSubgroup K (if εi then W.root i else -W.root i),
      ∀ y ∈ (rootOperatorFamily τ).rootSubgroup K (if εj then W.root j else -W.root j),
      Commute x y := by
    intro i j hij εi εj x hx y hy
    cases εi <;> cases εj <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx hy
    · refine commute_X_of_smul (s i * s j) ?_ ?_ (hXX i j hij) hx hy
      · rw [mul_smul, smul_neg_root, hfix j i (Ne.symm hij), smul_neg_root, hflip, neg_neg]
      · rw [mul_smul, smul_neg_root, hflip, neg_neg, hfix i j hij]
    · refine commute_X_of_smul (s i) ?_ ?_ (hXX i j hij) hx hy
      · rw [smul_neg_root, hflip, neg_neg]
      · exact hfix i j hij
    · refine commute_X_of_smul (s j) ?_ ?_ (hXX i j hij) hx hy
      · exact hfix j i (Ne.symm hij)
      · rw [smul_neg_root, hflip, neg_neg]
    · exact hXX i j hij x hx y hy
  have hA := W.elemA_mem K
  have hB := W.elemB_mem K
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · set nn := nrep τ K ((coxeterSystem τ).wordProd (W.word i))
    obtain ⟨h3, h1, h2'⟩ := hZ i
    have hconj : ∀ (g : adjointGroup τ K) (m : ℕ), (nn * g * nn⁻¹) ^ m = nn * g ^ m * nn⁻¹ :=
      fun g m => by
        induction m with
        | zero => simp
        | succ m ih => rw [pow_succ, ih, pow_succ]; group
    have hcomm : ∀ g h : adjointGroup τ K, Commute (nn * g * nn⁻¹) (nn * h * nn⁻¹) →
        Commute g h := fun g h hc => by
      have e := hc.eq
      have : nn * (g * h) * nn⁻¹ = nn * (h * g) * nn⁻¹ := by
        calc _ = nn * g * nn⁻¹ * (nn * h * nn⁻¹) := by group
          _ = nn * h * nn⁻¹ * (nn * g * nn⁻¹) := e
          _ = _ := by group
      exact mul_right_cancel (mul_left_cancel this)
    refine ⟨?_, fun hc => h1 (hcomm _ _ hc), fun hc => h2' (hcomm _ _ ?_)⟩
    · change (nn * rankOneZ (W.simple i) * nn⁻¹) ^ 3 = 1
      rw [hconj, h3, mul_one, mul_inv_cancel]
    · change Commute ((nn * rankOneZ (W.simple i) * nn⁻¹) ^ 2) _ at hc
      rw [← hconj]; exact hc
  · rw [elemZ_eq]
    exact (hXX' j i (Ne.symm hij) true true _ (by simpa using hA j) _
      (by simpa using hA i)).mul_left
      (hXX' j i (Ne.symm hij) false true _ (by simpa using hB j) _ (by simpa using hA i))
  · rw [elemZ_eq, elemZ_eq]
    have hAA := hXX' i j hij true true _ (by simpa using hA i) _ (by simpa using hA j)
    have hAB := hXX' i j hij true false _ (by simpa using hA i) _ (by simpa using hB j)
    have hBA := hXX' i j hij false true _ (by simpa using hB i) _ (by simpa using hA j)
    have hBB := hXX' i j hij false false _ (by simpa using hB i) _ (by simpa using hB j)
    exact (hAA.mul_right hAB).mul_left (hBA.mul_right hBB)
  · exact ⟨hXX' i j hij true true _ (by simpa using hA i) _ (by simpa using hA j),
      hXX' i j hij false false _ (by simpa using hB i) _ (by simpa using hB j),
      hXX' i j hij true false _ (by simpa using hA i) _ (by simpa using hB j)⟩

end RootWitnessFacts

end A318P

end CFSG.Quasithin
