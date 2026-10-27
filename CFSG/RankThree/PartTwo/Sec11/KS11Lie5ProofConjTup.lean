module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofConjWeyl
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6

variable {L : Type} [Field L] {ζ : Lˣ}

theorem zpow_eq_pow_val (hζ : ζ ^ 3 = 1) (n : ℤ) : ζ ^ n = ζ ^ ((n : ZMod 3).val) := by
  rw [zpow_eq_zpow_emod' n hζ, ← ZMod.val_intCast n, zpow_natCast]

theorem pow_val_add (hζ : ζ ^ 3 = 1) (a b : ZMod 3) :
    ζ ^ a.val * ζ ^ b.val = ζ ^ (a + b).val := by
  rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ hζ]

theorem pow_val_inj (hζ : orderOf ζ = 3) {a b : ZMod 3} (h : ζ ^ a.val = ζ ^ b.val) : a = b := by
  have h1 := pow_inj_mod.1 h
  rw [hζ, Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h1
  exact ZMod.val_injective 3 h1

theorem rootChar_tup (hζ : ζ ^ 3 = 1) (β : Exp3) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar (tup ζ β) v = ζ ^ (∑ i, (v i : ZMod 3) * β i).val := by
  rw [rootChar]
  have h : ∀ i, tup ζ β i ^ v i = ζ ^ ((v i : ZMod 3) * β i).val := by
    intro i
    rw [tup, ← zpow_natCast, ← zpow_mul, zpow_eq_pow_val hζ]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id', id, mul_comm]
  simp only [h]
  induction (Finset.univ : Finset (Fin TwistTag.D4.tag.rank)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, pow_val_add hζ]

theorem weylTuple_tup (hζ : ζ ^ 3 = 1) (w : WeylGroup TwistTag.D4.tag) (β : Exp3) :
    weylTuple w (tup ζ β) = tup ζ (fun i => ∑ j, (((w⁻¹ • (Pi.single i 1 :
      Fin TwistTag.D4.tag.rank → ℤ)) j : ℤ) : ZMod 3) * β j) := by
  funext i
  rw [weylTuple, rootChar_tup hζ]
  rfl

theorem weylTuple_tup_of_tab (hζ : ζ ^ 3 = 1) {w : WeylGroup TwistTag.D4.tag} {e : ℕ}
    (he : ∀ i, w⁻¹ • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = colOf e i) (β : Exp3) :
    weylTuple w (tup ζ β) = tup ζ (tabExp e β) := by
  rw [weylTuple_tup hζ]
  funext i
  simp only [he]
  rfl

theorem gen_sum_single_add {ι : Type} [Fintype ι] [DecidableEq ι] (i j : ι) (c : ℤ)
    (β : ι → ZMod 3) :
    ∑ x, ((((Pi.single i 1 : ι → ℤ) x + c * (Pi.single j 1 : ι → ℤ) x : ℤ) : ZMod 3) * β x) =
      β i + (c : ZMod 3) * β j := by
  simp only [Int.cast_add, Int.cast_mul, add_mul, Finset.sum_add_distrib, mul_assoc,
    ← Finset.mul_sum]
  congr 1
  · rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
    simp
  · congr 1
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp

theorem weylTuple_simple_tup (hζ : ζ ^ 3 = 1) (j : Fin TwistTag.D4.tag.rank) (β : Exp3) :
    weylTuple (simple TwistTag.D4.tag j) (tup ζ β) = tup ζ (sExp j β) := by
  rw [weylTuple_tup hζ]
  congr 1
  funext i
  have hinv : (simple TwistTag.D4.tag j)⁻¹ = simple TwistTag.D4.tag j :=
    (coxeterSystem TwistTag.D4.tag).inv_simple j
  have hsum : ∑ k, TwistTag.D4.tag.cartan j k * (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) k =
      TwistTag.D4.tag.cartan j i := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
    simp
  have hv : ∀ x, ((simple TwistTag.D4.tag j)⁻¹ • (Pi.single i 1 :
      Fin TwistTag.D4.tag.rank → ℤ)) x = (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) x +
        (-TwistTag.D4.tag.cartan j i) * (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ) x := by
    intro x
    rw [hinv, simple_smul, reflect, hsum]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [hv]
  exact gen_sum_single_add i j _ β

theorem weylTuple_wordProd_tup (hζ : ζ ^ 3 = 1) (ω : List (Fin TwistTag.D4.tag.rank))
    (β : Exp3) :
    weylTuple ((coxeterSystem TwistTag.D4.tag).wordProd ω) (tup ζ β) = tup ζ (wordExp ω β) := by
  induction ω with
  | nil =>
    rw [CoxeterSystem.wordProd_nil, weylTuple_one]
    rfl
  | cons j ω ih =>
    rw [CoxeterSystem.wordProd_cons, ← weylTuple_weylTuple, ih]
    exact weylTuple_simple_tup hζ j _

theorem tup_injective (hζ : orderOf ζ = 3) : Function.Injective (tup ζ) := fun _ _ h =>
  funext fun i => pow_val_inj hζ (congrFun h i)

theorem wordProd_smul (ω : List (Fin TwistTag.D4.tag.rank)) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    (coxeterSystem TwistTag.D4.tag).wordProd ω • v = wordVec ω v := by
  induction ω generalizing v with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul]; rfl
  | cons j ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih]
    exact simple_smul j _

theorem exists_word_of_rho (hζ : orderOf ζ = 3) {β : Exp3} (hβ : β ≠ 0)
    {w : WeylGroup TwistTag.D4.tag}
    (hw : weylTuple w (tup ζ (rhoExp β)) = tup ζ β ∨
      weylTuple w (tup ζ (fun i => 2 * rhoExp β i)) = tup ζ β) :
    ∃ ω : List (Fin TwistTag.D4.tag.rank), wordExp ω β = gA ∨ wordExp ω β = gB := by
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  obtain ⟨e, he, hwe⟩ := exists_mem_d4WeylTab w⁻¹
  have hcol : ∀ i, w⁻¹ • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = colOf e i := hwe
  rcases typeCheck_spec β with h | h | h
  · exact absurd h hβ
  · have h' := List.all_eq_true.1 h e he
    simp only [decide_eq_true_eq] at h'
    exfalso
    rcases hw with hw | hw
    · rw [weylTuple_tup_of_tab hζ3 hcol] at hw
      exact h'.1 (tup_injective hζ hw)
    · rw [weylTuple_tup_of_tab hζ3 hcol] at hw
      exact h'.2 (tup_injective hζ hw)
  · obtain ⟨ω, -, hω⟩ := List.any_eq_true.1 h
    exact ⟨ω, of_decide_eq_true hω⟩

theorem rootReflection_single_D4
    (j : Fin TwistTag.D4.tag.rank) :
    rootReflection (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ) = simple TwistTag.D4.tag j := by
  rw [rootReflection_eq_conj (w := 1) (j := j) (by rw [one_smul]), one_mul, inv_one, mul_one]

theorem tabExp_eq_of_mem_stab (hζ : orderOf ζ = 3) {γ : Exp3} {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ rootCharStabilizer (tup ζ γ)) {e : ℕ}
    (he : ∀ i, w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = colOf e i) :
    tabExp e γ = γ := by
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  funext i
  have h := hw (Pi.single i 1)
  rw [he, rootChar_tup hζ3, rootChar_tup hζ3] at h
  have h2 := pow_val_inj hζ h
  change (∑ j, ((colOf e i j : ℤ) : ZMod 3) * γ j) = γ i
  rw [h2, Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp

theorem simple_mem_closure
    {a : Fin TwistTag.D4.tag.rank → Lˣ} {j : Fin TwistTag.D4.tag.rank}
    (hj : a j = 1) :
    simple TwistTag.D4.tag j ∈ Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} := by
  refine Subgroup.subset_closure ⟨Pi.single j 1, ⟨isRoot_single _ j, ?_⟩, ?_⟩
  · have := rootChar_nsmul_single a j 1
    rwa [one_nsmul, pow_one, hj] at this
  · exact (rootReflection_single_D4 j).symm

theorem wordProd_mem_closure
    {a : Fin TwistTag.D4.tag.rank → Lˣ}
    {ω : List (Fin TwistTag.D4.tag.rank)} (hω : ∀ j ∈ ω, a j = 1) :
    (coxeterSystem TwistTag.D4.tag).wordProd ω ∈ Subgroup.closure
      {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil]; exact one_mem _
  | cons j ω ih =>
    rw [CoxeterSystem.wordProd_cons]
    exact mul_mem (simple_mem_closure (hω j List.mem_cons_self))
      (ih fun k hk => hω k (List.mem_cons_of_mem j hk))

theorem eq_wordProd_of_col {w : WeylGroup TwistTag.D4.tag} {e : ℕ}
    (he : ∀ i, w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = colOf e i)
    {ω : List (Fin TwistTag.D4.tag.rank)}
    (hω : ∀ i, colOf e i = wordVec ω (Pi.single i 1)) :
    w = (coxeterSystem TwistTag.D4.tag).wordProd ω :=
  ext_single fun i => by rw [he, hω, wordProd_smul]

theorem stab_subset_closure_A
    (hζ : orderOf ζ = 3) :
    rootCharStabilizer (tup ζ gA) ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel (tup ζ gA), s = rootReflection α} :
        Set (WeylGroup TwistTag.D4.tag)) := by
  intro w hw
  obtain ⟨e, he, hwe⟩ := exists_mem_d4WeylTab w
  have hcol : ∀ i, w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = colOf e i := hwe
  have htab := tabExp_eq_of_mem_stab hζ hw hcol
  have h := List.all_eq_true.1 stabCheckA_eq e he
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  rcases h with h | h
  · exact absurd htab h
  · obtain ⟨ω, hωA, hω⟩ := List.any_eq_true.1 h
    rw [eq_wordProd_of_col hcol (of_decide_eq_true hω)]
    refine wordProd_mem_closure fun j hj => ?_
    have hj' : j = 0 ∨ j = 2 := by
      have hall : ∀ ω ∈ wordsA, ∀ j ∈ ω, j = 0 ∨ j = 2 := by decide
      exact hall ω hωA j hj
    rcases hj' with rfl | rfl <;> simp [tup, gA]

theorem stab_subset_closure_B
    (hζ : orderOf ζ = 3) :
    rootCharStabilizer (tup ζ gB) ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel (tup ζ gB), s = rootReflection α} :
        Set (WeylGroup TwistTag.D4.tag)) := by
  intro w hw
  obtain ⟨e, he, hwe⟩ := exists_mem_d4WeylTab w
  have hcol : ∀ i, w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = colOf e i := hwe
  have htab := tabExp_eq_of_mem_stab hζ hw hcol
  have h := List.all_eq_true.1 stabCheckB_eq e he
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  rcases h with h | h
  · exact absurd htab h
  · obtain ⟨ω, hωB, hω⟩ := List.any_eq_true.1 h
    rw [eq_wordProd_of_col hcol (of_decide_eq_true hω)]
    refine wordProd_mem_closure fun j hj => ?_
    have hj' : j = 0 ∨ j = 1 ∨ j = 3 := by
      have hall : ∀ ω ∈ wordsB, ∀ j ∈ ω, j = 0 ∨ j = 1 ∨ j = 3 := by decide
      exact hall ω hωB j hj
    rcases hj' with rfl | rfl | rfl <;> simp [tup, gB]

@[expose] def sigmaA : Set (Fin TwistTag.D4.tag.rank → ℤ) :=
  {r | ∃ i j : Fin 3, i ≠ j ∧ r = chainRoot d4ChainA2 i j}

@[expose] def sigmaB : Set (Fin TwistTag.D4.tag.rank → ℤ) :=
  {r | ∃ k : Fin 24, (k = 0 ∨ k = 4 ∨ k = 1 ∨ k = 6 ∨ k = 3 ∨ k = 10) ∧ r = d4RootVec k}

theorem rootCharKernel_tup_gA_subset (hζ : orderOf ζ = 3) :
    rootCharKernel (tup ζ gA) ⊆ sigmaA := by
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  rintro α ⟨hα, h1⟩
  obtain ⟨k, rfl⟩ := isRoot_iff_exists_d4RootVec.1 hα
  have h1' := (rootChar_tup hζ3 gA (d4RootVec k)).symm.trans h1
  have h0 : (∑ j, ((d4RootVec k j : ℤ) : ZMod 3) * gA j) = 0 :=
    pow_val_inj hζ (b := 0) (by rw [ZMod.val_zero, pow_zero]; exact h1')
  exact kerCheckA_spec k h0

theorem rootCharKernel_tup_gB_subset (hζ : orderOf ζ = 3) :
    rootCharKernel (tup ζ gB) ⊆ sigmaB := by
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  rintro α ⟨hα, h1⟩
  obtain ⟨k, rfl⟩ := isRoot_iff_exists_d4RootVec.1 hα
  have h1' := (rootChar_tup hζ3 gB (d4RootVec k)).symm.trans h1
  have h0 : (∑ j, ((d4RootVec k j : ℤ) : ZMod 3) * gB j) = 0 :=
    pow_val_inj hζ (b := 0) (by rw [ZMod.val_zero, pow_zero]; exact h1')
  exact ⟨k, kerCheckB_spec k h0, rfl⟩

end CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
