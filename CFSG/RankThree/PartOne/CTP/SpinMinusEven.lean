module

public import CFSG.ClassicalInvolution.WeakCT.SpinMinus
public import CFSG.LieType.Steinberg.Classical.SpinPlus

public section

namespace CFSG.RankThree.PartOne.CTP

open CliffordAlgebra QuadraticMap CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

section SpinMap

variable {F : Type*} [Field F] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁]
  [AddCommGroup V₂] [Module F V₂] {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

theorem spinAction_spinGroupMap (f : Q₁ →qᵢ Q₂) (x : spinGroup Q₁) (v : V₁) :
    spinAction Q₂ (f.spinGroupMap x) (f v) = f (spinAction Q₁ x v) := by
  apply ι_injective' Q₂
  rw [ι_spinAction, ← map_inv, QuadraticMap.Isometry.coe_spinGroupMap_apply,
    QuadraticMap.Isometry.coe_spinGroupMap_apply, ← CliffordAlgebra.map_apply_ι f v,
    ← map_mul, ← map_mul, ← ι_spinAction, CliffordAlgebra.map_apply_ι]

theorem spinGroupMap_injective_of_ker_bot (f : Q₁ →qᵢ Q₂) (hf : Function.Injective f)
    (hker : (spinAction Q₁).ker = ⊥) : Function.Injective f.spinGroupMap := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : x ∈ (spinAction Q₁).ker := by
    rw [MonoidHom.mem_ker]
    refine LinearEquiv.ext fun v => hf ?_
    rw [← spinAction_spinGroupMap, hx, map_one]
    rfl
  rw [hker] at hmem
  exact Subgroup.mem_bot.mp hmem

end SpinMap

section MinusShift

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem spinGroupMap_minusShift_injective_even (n : ℕ) (hn : 3 ≤ n) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (minusShift n hn b c).spinGroupMap := by
  have := isCentral_cliffordAlgebra_quadMinus 3 b c hirr
  exact spinGroupMap_injective_of_ker_bot _ (minusShift_injective n hn b c)
    (ker_spinAction_eq_bot_of_isCentral _ CharTwo.two_eq_zero)

end MinusShift

section ShortBlock

theorem center_sl2_eq_bot_of_two_eq_zero {E : Type*} [Field E] (h2 : (2 : E) = 0) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E) = ⊥ := by
  have hneg : (-1 : E) = 1 := by rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  rcases (CFSG.Semidihedral.ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity E g).mp hg
    with h | h
  · exact h
  · rw [h]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity, hneg]

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem shortBlock_injective_even (n : ℕ) (k : Fin (n - 1)) :
    Function.Injective (shortBlock hirr n k) := by
  have := finite_shortField (b := b) (c := c)
  have h2E : (2 : ShortField b c) = 0 := by
    have h := map_ofNat (algebraMap F (ShortField b c)) 2
    rw [CharTwo.two_eq_zero (R := F), map_zero] at h
    exact h.symm
  have hqs := CFSG.Semidihedral.DefiningCharacteristicDimension.nativeSL2_quasisimple
    (four_le_card_shortField' (b := b) (c := c))
  have hne : shortBlock hirr n k (tv 0 1 (1 : ShortField b c)) ≠ 1 := by
    rw [shortBlock_tv01]
    intro h
    rw [← map_one (shortPosHom n hirr k)] at h
    have h1 := shortPosHom_injective n hirr k h
    exact fieldCoord_ne_zero (one_ne_zero (α := ShortField b c)) (ofAdd_eq_one.mp h1)
  have hproper : (shortBlock hirr n k).ker ≠ ⊤ := fun htop => hne (by
    have hmem : tv 0 1 (1 : ShortField b c) ∈ (shortBlock hirr n k).ker := by
      rw [htop]
      trivial
    exact MonoidHom.mem_ker.mp hmem)
  have hle := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hqs _ hproper
  rw [center_sl2_eq_bot_of_two_eq_zero h2E] at hle
  exact (MonoidHom.ker_eq_bot_iff _).mp (le_bot_iff.mp hle)

@[expose] noncomputable def nodeDataShortEven {n : ℕ} {X : Type} [Group X] {U : Subgroup X}
    (ρ : SL(2, ShortField b c) →* X) (hU : ρ.range = U) {k : Fin (n - 1)}
    (hk : ¬ k.val + 1 < n - 1) : NodeData (minusDatum n hirr) X k U :=
  NodeData.ofParam (shortBlock hirr n k) ρ hU (shortBlock_injective_even hirr n k)
    (shortBlock_upper_mem hirr hk) (shortBlock_lower_mem hirr hk) (shortBlock_param_upper hirr hk)
    (shortBlock_param_lower hirr hk)

theorem nodeDataShortEven_isParam {n : ℕ} {X : Type} [Group X] {U : Subgroup X}
    (ρ : SL(2, ShortField b c) →* X) (hU : ρ.range = U) {k : Fin (n - 1)}
    (hk : ¬ k.val + 1 < n - 1) :
    (nodeDataShortEven hirr ρ hU hk).IsParam (shortBlock hirr n k) ρ :=
  NodeData.ofParam_isParam hU (shortBlock_injective_even hirr n k) (shortBlock_upper_mem hirr hk)
    (shortBlock_lower_mem hirr hk) (shortBlock_param_upper hirr hk) (shortBlock_param_lower hirr hk)

end ShortBlock

section SL3

variable {F : Type} [Field F]

@[expose] noncomputable def plusToMinus (n : ℕ) (b c : F) :
    (quadPlus (n - 1) F).Isometry (quadMinus n F b c) where
  toFun v := fun x => match x with
    | .inl i => v (.inl i)
    | .inr (.inl i) => v (.inr i)
    | .inr (.inr _) => 0
  map_add' v w := by
    funext x
    rcases x with i | i | t
    · rfl
    · rfl
    · simp
  map_smul' a v := by
    funext x
    rcases x with i | i | t
    · rfl
    · rfl
    · simp
  map_app' v := by
    simp [quadMinus_apply, quadPlus_apply]

@[simp] theorem plusToMinus_apply_inl (n : ℕ) (b c : F) (v : Fin (n - 1) ⊕ Fin (n - 1) → F)
    (i : Fin (n - 1)) : plusToMinus n b c v (.inl i) = v (.inl i) := rfl

@[simp] theorem plusToMinus_apply_inr_inl (n : ℕ) (b c : F) (v : Fin (n - 1) ⊕ Fin (n - 1) → F)
    (i : Fin (n - 1)) : plusToMinus n b c v (.inr (.inl i)) = v (.inr i) := rfl

@[simp] theorem plusToMinus_apply_inr_inr (n : ℕ) (b c : F) (v : Fin (n - 1) ⊕ Fin (n - 1) → F)
    (t : Fin 2) : plusToMinus n b c v (.inr (.inr t)) = 0 := rfl

theorem plusToMinus_plusVec (n : ℕ) (b c : F) (i : Fin (n - 1)) (s : Bool) :
    plusToMinus n b c (plusVec (n - 1) F i s) = minusVec n i s := by
  funext x
  rcases x with j | j | t <;> cases s <;>
    simp [plusVec, minusVec, eVec, fVec, Pi.single_apply]

theorem plusToMinus_injective (n : ℕ) (b c : F) : Function.Injective (plusToMinus n b c) := by
  intro v w h
  funext x
  rcases x with i | i
  · exact congrFun h (.inl i)
  · exact congrFun h (.inr (.inl i))

theorem spinGroupMap_plusToMinus_injective_even [CharP F 2] (n : ℕ) (b c : F) :
    Function.Injective (plusToMinus n b c).spinGroupMap := by
  have := isCentral_cliffordAlgebra_quadPlus F (n - 1)
  exact spinGroupMap_injective_of_ker_bot _ (plusToMinus_injective n b c)
    (ker_spinAction_eq_bot_of_isCentral _ CharTwo.two_eq_zero)

theorem spinGroupMap_plusToMinus_longRoot (n : ℕ) (hn : 3 ≤ n - 1) (b c : F) {i j : Fin (n - 1)}
    (hij : i ≠ j) (s t : Bool) (x : F) :
    (plusToMinus n b c).spinGroupMap ((plusFrame (n - 1) F hn).longRoot hij s t (.ofAdd x)) =
      (minusFrame n b c).longRoot hij s t (.ofAdd x) := by
  apply Subtype.ext
  rw [QuadraticMap.Isometry.coe_spinGroupMap_apply, HypFrame.coe_longRoot, HypFrame.coe_longRoot]
  simp only [map_add, map_one, map_smul, map_mul, CliffordAlgebra.map_apply_ι, plusFrame_vec,
    minusFrame_vec, plusToMinus_plusVec]

theorem spinGroupMap_plusToMinus_longSL2 (n : ℕ) (hn : 3 ≤ n - 1) (b c : F) {i j : Fin (n - 1)}
    (hij : i ≠ j) (s t : Bool) :
    (plusToMinus n b c).spinGroupMap.comp ((plusFrame (n - 1) F hn).longSL2 hij s t) =
      (minusFrame n b c).longSL2 hij s t := by
  refine hom_ext_sl2 (fun x => ?_) (fun x => ?_)
  · rw [MonoidHom.comp_apply, tv01_eq_upperSL2, HypFrame.longSL2_upperSL2,
      HypFrame.longSL2_upperSL2, spinGroupMap_plusToMinus_longRoot]
  · rw [MonoidHom.comp_apply, tv10_eq_lowerSL2, HypFrame.longSL2_lowerSL2,
      HypFrame.longSL2_lowerSL2, spinGroupMap_plusToMinus_longRoot]

theorem spinGroupMap_plusToMinus_rankOneD (n : ℕ) (hn : 3 ≤ n - 1) (b c : F) {k : Fin (n - 1)}
    (hk : k.val + 1 < n - 1) :
    (plusToMinus n b c).spinGroupMap.comp (rankOneD F hn k) = rLong n b c hk := by
  have h := spinGroupMap_plusToMinus_longSL2 n hn b c (rootIdxD_ne (n - 1) (by omega) k) true
    (rootSignD (n - 1) k)
  refine h.trans ?_
  rw [rootSignD_of_lt (n - 1) hk, rLong]
  exact longSL2_congr _ _ _ (rootIdxD_of_lt (n - 1) hk) (rootIdxD'_of_lt (n - 1) hk) _ _

theorem cartanD_sl3_data {m : ℕ} {i j k : Fin m} (hij : i.val + 1 = j.val) (hj : j.val + 1 < m)
    (hk : k.val = j.val + 1) :
    cartanD m i j = -1 ∧ cartanD m j i = -1 ∧
      ¬ (3 : ℤ) ∣ cartanD m i k + 2 * cartanD m j k := by
  have e1 : cartanD m i j = -1 := by
    simp only [cartanD, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  have e2 : cartanD m j i = -1 := by
    simp only [cartanD, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  refine ⟨e1, e2, ?_⟩
  by_cases h2 : j.val + 2 < m
  · have e3 : cartanD m i k = 0 := by
      simp only [cartanD, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    have e4 : cartanD m j k = -1 := by
      simp only [cartanD, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    rw [e3, e4]
    omega
  · have e3 : cartanD m i k = -1 := by
      simp only [cartanD, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    have e4 : cartanD m j k = 0 := by
      simp only [cartanD, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    rw [e3, e4]
    omega

theorem exists_sl3_minus_even [Finite F] [CharP F 2] {n : ℕ} (b c : F)
    {i j : Fin (n - 1)} (hij : i.val + 1 = j.val) (hi : i.val + 1 < n - 1)
    (hj : j.val + 1 < n - 1) :
    ∃ emb : SL(3, F) →* spinGroup (quadMinus n F b c), Function.Injective emb ∧
      emb.comp (blk F 0) = rLong n b c hi ∧ emb.comp (blk F 1) = rLong n b c hj := by
  classical
  have hn3 : 3 ≤ n - 1 := by omega
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.plusDatum (n - 1) F hn3).isFiniteType
    (Dv := (Spin.plusDatum (n - 1) F hn3).divisible) rfl
  have hE := Steinberg.SpinPlus.chevalleyExtras hn3 O Steinberg.SpinPlus.commC
    (Steinberg.SpinPlus.commutatorFormula hn3 O)
  obtain ⟨hc1, hc2, hk'⟩ := cartanD_sl3_data (k := ⟨j.val + 1, hj⟩) hij hj rfl
  obtain ⟨emb, hinj, -, hv⟩ := exists_sl3Levi hE rfl (Fin.ne_of_val_ne (by omega)) hc1 hc2 hk'
  have hv1 : ∀ x : F, emb (tv 0 1 x) = rankOneD F hn3 i (tv 0 1 x) := fun x => by
    rw [(hv x).1, tv01_eq_upperSL2]
    exact Steinberg.SpinPlus.x_single hn3 i x
  have hv2 : ∀ x : F, emb (tv 1 0 x) = rankOneD F hn3 i (tv 1 0 x) := fun x => by
    rw [(hv x).2.1, tv10_eq_lowerSL2]
    exact Steinberg.SpinPlus.x_neg_single hn3 i x
  have hv3 : ∀ x : F, emb (tv 1 2 x) = rankOneD F hn3 j (tv 0 1 x) := fun x => by
    rw [(hv x).2.2.1, tv01_eq_upperSL2]
    exact Steinberg.SpinPlus.x_single hn3 j x
  have hv4 : ∀ x : F, emb (tv 2 1 x) = rankOneD F hn3 j (tv 1 0 x) := fun x => by
    rw [(hv x).2.2.2, tv10_eq_lowerSL2]
    exact Steinberg.SpinPlus.x_neg_single hn3 j x
  have hri := spinGroupMap_plusToMinus_rankOneD n hn3 b c hi
  have hrj := spinGroupMap_plusToMinus_rankOneD n hn3 b c hj
  refine ⟨(plusToMinus n b c).spinGroupMap.comp emb,
    (spinGroupMap_plusToMinus_injective_even n b c).comp hinj, ?_, ?_⟩
  · refine hom_ext_sl2 (fun x => ?_) (fun x => ?_)
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, blk_zero_tv01, hv1]
      exact DFunLike.congr_fun hri (tv 0 1 x)
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, blk_zero_tv10, hv2]
      exact DFunLike.congr_fun hri (tv 1 0 x)
  · refine hom_ext_sl2 (fun x => ?_) (fun x => ?_)
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, blk_one_tv01, hv3]
      exact DFunLike.congr_fun hrj (tv 0 1 x)
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, blk_one_tv10, hv4]
      exact DFunLike.congr_fun hrj (tv 1 0 x)

end SL3

theorem weakCT_spinMinus_even {n f : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 2 f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f) (hq : 4 ≤ Nat.card F)
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {X : Type} [Group X]
    (U : Fin (n - 1) → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (hpair : ∀ i j : Fin (n - 1), i.val + 1 = j.val → j.val + 2 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (htw : ∀ i j : Fin (n - 1), i.val + 3 = n → j.val + 2 = n →
      ∃ W, TwistedB2BlockStandardPair hirr W (U i) (U j)) :
    ∃ Ψ : spinGroup (quadMinus n F b c) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (spinGroup (quadMinus n F b c))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .POmegaMinus n 2 f ∧
      ∀ k, (CurtisTits.rankOne (minusDatum n hirr).rootGroup k).map Ψ = U k := by
  classical
  have hn4 : 4 ≤ n := hadm.2.2
  have := fact_shortField hirr
  have hn3 : 3 ≤ n := by omega
  obtain ⟨W, θ, hθW, -, hθl, hθs, hθU, hθV⟩ :=
    htw ⟨n - 3, by omega⟩ ⟨n - 2, by omega⟩ (by simp only; omega) (by simp only; omega)
  let P := spinMinusModel hirr
  have hν : ∃ t, P.nu t ≠ 1 := exists_spinNu_ne hq
  let U' : Fin (n - 2) → Subgroup X := fun k => U ⟨k.val, by omega⟩
  have hcomm' : ∀ i j : Fin (n - 2), i ≠ j → ¬ edgeUp (n - 2) i j → ¬ edgeUp (n - 2) j i →
      ∀ u ∈ U' i, ∀ v ∈ U' j, u * v = v * u := by
    intro i j hne h1 h2' u hu v hv
    simp only [edgeUp] at h1 h2'
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : i.val ≠ j.val) with hlt | hgt
    · exact hcomm _ _ (by simp only; omega) u hu v hv
    · exact (hcomm _ _ (by simp only; omega) v hv u hu).symm
  have hpair' : ∀ i j : Fin (n - 2), edgeUp (n - 2) i j →
      ∃ W, LinearBlockStandardPair F W (U' i) (U' j) := by
    intro i j hij
    simp only [edgeUp] at hij
    have hj := j.isLt
    exact hpair ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij (by dsimp only; omega)
  have hU' : (θ.comp P.lb).range = U' ⟨n - 2 - 1, by omega⟩ := by
    rw [MonoidHom.range_comp]
    exact hθU
  have hV' : ∀ q : Fin (n - 2), (edgeUp (n - 2) ⟨n - 2 - 1, by omega⟩ q ∨
      edgeUp (n - 2) q ⟨n - 2 - 1, by omega⟩) → ∀ x ∈ (θ.comp P.sb).range, ∀ y ∈ U' q,
      x * y = y * x := by
    intro q hq' x hx y hy
    have hq'' : q.val + 1 = n - 2 - 1 := by
      rcases hq' with h | h
      · simp only [edgeUp] at h
        have := q.2
        omega
      · simpa only [edgeUp] using h
    rw [MonoidHom.range_comp] at hx
    have hx' : x ∈ U ⟨n - 2, by omega⟩ := hθV ▸ hx
    exact (hcomm ⟨q.val, by omega⟩ ⟨n - 2, by omega⟩ (by simp only; omega) y hy x hx').symm
  obtain ⟨ρ', hρ'₀, hρ'U, hρ'ψ⟩ := exists_frame_of_tree_long P hν hq
    (rootedTree_edgeUp_last (m := n - 2) (by omega))
    ⟨⟨n - 4, by omega⟩, Or.inr (by simp only [edgeUp]; omega)⟩ hcomm' hpair' hθl hU' hV'
  let ρL : Fin (n - 1) → SL(2, F) →* X := fun k => if h : k.val < n - 2 then ρ' ⟨k.val, h⟩ else 1
  let ρS : SL(2, ShortField b c) →* X := θ.comp P.sb
  have hρL : ∀ k : Fin (n - 1), (h : k.val < n - 2) → ρL k = ρ' ⟨k.val, h⟩ := fun k h =>
    dite_eq_left h
  have hρLU : ∀ k : Fin (n - 1), k.val + 1 < n - 1 → (ρL k).range = U k := fun k hk => by
    rw [hρL k (by omega)]
    exact (hρ'U ⟨k.val, by omega⟩).2
  have hρLinj : ∀ k : Fin (n - 1), (h : k.val + 1 < n - 1) → Function.Injective (ρL k) :=
    fun k hk => by
      rw [hρL k (by omega)]
      exact (hρ'U ⟨k.val, by omega⟩).1
  have hρSU : ∀ k : Fin (n - 1), ¬ k.val + 1 < n - 1 → ρS.range = U k := fun k hk => by
    have hkb : k = ⟨n - 2, by omega⟩ := Fin.ext (by have := k.2; simp only; omega)
    rw [hkb, MonoidHom.range_comp]
    exact hθV
  have hCT : CurtisTits.CurtisTitsConclusion.{0} (minusDatum n hirr) .POmegaMinus n 2 f :=
    CurtisTits.curtisTitsConclusion_spinMinus hirr hadm hF
  have hCTG := minusDatum_isCTGroupDatum n hirr hn4
  have hL := leviConePresented_spinMinus hirr hn4
  have hdiv : (minusDatum n hirr).divisible = ∅ := rfl
  let nd : ∀ k, NodeData (minusDatum n hirr) X k (U k) := fun k =>
    if hk : k.val + 1 < n - 1 then nodeDataLong hirr (ρL k) (hρLU k hk) hk
    else nodeDataShortEven hirr ρS (hρSU k hk) hk
  have ndL : ∀ (k : Fin (n - 1)) (hk : k.val + 1 < n - 1),
      (nd k).IsParam (rLong n b c hk) (ρL k) := fun k hk => by
    have e : nd k = nodeDataLong hirr (ρL k) (hρLU k hk) hk := dite_eq_left hk
    rw [e]
    exact nodeDataLong_isParam hirr _ _ hk
  have ndS : ∀ (k : Fin (n - 1)) (hk : ¬ k.val + 1 < n - 1),
      (nd k).IsParam (shortBlock hirr n k) ρS := fun k hk => by
    have e : nd k = nodeDataShortEven hirr ρS (hρSU k hk) hk := dite_eq_right hk
    rw [e]
    exact nodeDataShortEven_isParam hirr _ _ hk
  have hnt : ∃ k, ∃ g, (nd k).ψp g ≠ 1 := by
    let k₁ : Fin (n - 1) := ⟨0, by omega⟩
    have hk₁ : k₁.val + 1 < n - 1 := by simp only [k₁]; omega
    refine ⟨k₁, ⟨rLong n b c hk₁ (tv 0 1 1), rLong_upper hirr hk₁ 1⟩, ?_⟩
    rw [(ndL k₁ hk₁).ψp_eq 1]
    intro h
    exact tv_zero_one_one_ne_one (hρLinj k₁ hk₁ (h.trans (map_one _).symm))
  have hloc : ∀ i j : Fin (minusDatum n hirr).rank, i ≤ j →
      ∃ (E : LeviEmbedding (minusDatum n hirr) i j) (φ : E.L →* X), ∀ k, (k = i ∨ k = j) →
      (∀ g : (minusDatum n hirr).rootGroup (Pi.single k 1), φ (E.preimage g) = (nd k).ψp g) ∧
        ∀ g : (minusDatum n hirr).rootGroup (-Pi.single k 1), φ (E.preimage g) = (nd k).ψm g := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hlt
    · by_cases hi : i.val + 1 < n - 1
      · exact exists_levi_node hdiv hCTG nd (ndL i hi) (rLong_injective hi)
      · exact exists_levi_node hdiv hCTG nd (ndS i hi) (shortBlock_injective_even hirr n i)
    · have hlt' : i.val < j.val := hlt
      have hi2 : i.val < n - 1 := i.2
      have hj2 : j.val < n - 1 := j.2
      by_cases hadj : i.val + 1 = j.val
      · by_cases hj : j.val + 1 < n - 1
        ·
          have hi : i.val + 1 < n - 1 := by omega
          obtain ⟨emb, hinj, hemb0, hemb1⟩ := exists_sl3_minus_even b c hadj hi hj
          obtain ⟨ψ, hψ0, hψ1⟩ := hρ'ψ ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
            (by simpa [edgeUp] using hadj)
          exact exists_levi_of_model hdiv hCTG nd (ndL i hi) (ndL j hj) emb hinj (blk F 0)
            (blk F 1) hemb0 hemb1 ψ (hψ0.trans (hρL i (by omega)).symm)
            (hψ1.trans (hρL j (by omega)).symm)
        ·
          have hia : i.val + 3 = n := by omega
          have hjb : j.val + 2 = n := by omega
          have hi : i.val + 1 < n - 1 := by omega
          have hi' : ρL i = θ.comp P.lb := by
            have hk : (⟨i.val, by omega⟩ : Fin (n - 2)) = ⟨n - 2 - 1, by omega⟩ :=
              Fin.ext (by simp only; omega)
            rw [hρL i (by omega), hk, hρ'₀]
          exact exists_levi_of_model hdiv hCTG nd (ndL i hi) (ndS j hj)
            (minusShift n hn3 b c).spinGroupMap (spinGroupMap_minusShift_injective_even n hn3 hirr)
            (minusLongBlock b c) (shortBlock hirr 3 finOne) (minusShift_comp_longBlock hn3 hia hi)
            (minusShift_comp_shortBlock hn3 hirr hjb) θ hi'.symm rfl
      ·
        have hlt2 : i.val + 1 < j.val := by omega
        have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
        have hi : i.val + 1 < n - 1 := by omega
        have hcU : ∀ (A : SL(2, F)) (B : SL(2, F)), ∀ (hj : j.val + 1 < n - 1),
            Commute (ρL i A) (ρL j B) := fun A B hj =>
          hcomm i j hlt2 _ (hρLU i hi ▸ ⟨A, rfl⟩) _ (hρLU j hj ▸ ⟨B, rfl⟩)
        by_cases hj : j.val + 1 < n - 1
        · exact exists_levi_orth hdiv hCTG nd (ndL i hi) (ndL j hj) (rLong_injective hi)
            (rLong_injective hj) (commute_rLong_rLong hi hj hlt2)
            (hZ_of_torus (minusDatum_torus_iSupIndep n hirr) hne _ _
              (rLong_center_mem_torus hirr hi) (rLong_center_mem_torus hirr hj))
            (fun A B => hcU A B hj)
        · exact exists_levi_orth hdiv hCTG nd (ndL i hi) (ndS j hj) (rLong_injective hi)
            (shortBlock_injective_even hirr n j) (commute_rLong_shortBlock hirr hi hlt2)
            (hZ_of_torus (minusDatum_torus_iSupIndep n hirr) hne _ _
              (rLong_center_mem_torus hirr hi) (shortBlock_center_mem_torus hirr hj))
            (fun A B => hcomm i j hlt2 _ (hρLU i hi ▸ ⟨A, rfl⟩) _ (hρSU j hj ▸ ⟨B, rfl⟩))
  exact weakCT_of_twisted_nodes hCT hL hdiv hgen nd hnt hloc

end CFSG.RankThree.PartOne.CTP
