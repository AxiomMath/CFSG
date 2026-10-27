module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicUnitary
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicSymplectic
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggLayerCenterCyclicInput_of_rest
    (hrest : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGLayerLinearLabel lab →
        LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I)) :
    GGLayerCenterCyclicInput := by
  intro p lab hp hp2 hlab hsplit
  by_cases h : GGLayerLinearLabel lab
  · exact largeEvenLabelAll_layerCenterCyclic_linear hp hp2 hlab h
  · exact hrest p lab hp hp2 hlab hsplit h

@[expose] def GGLayerUnitaryModelInput : Prop :=
  ∀ (d n : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 → 1 ≤ n → 3 ≤ d →
    (d, 2 ^ n) ≠ (3, 2) → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ (A : GL (Fin d) K)
        (hA : A ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))),
        A ∈ LargeEvenGUSet (Fin d) K (2 ^ n) → GGModelLayerCyclic p (ggMatConjAut hA)

theorem recipeUnitary_layerCenterCyclic
    (hU : GGLayerUnitaryModelInput) {d n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧
      LargeEvenSimpleGuard (fun R _ I _ => GGLayerCenterCyclic p R I) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdata := TableBU.unitaryFieldData_of_card hK hn
  have : CharP K 2 := hdata.charP
  have hperf : Group.IsPerfect (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hd hdq
  have hmodel := hU d n K hK hn hd hdq p hp hp2
  refine ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ => ?_⟩
  exact ggLayerCenterCyclic_matConj hp hperf.commutator_eq_top (ggPSections_su hK hn hd hp hp2)
    (TableBUE.gu_subset_normalizer hdata) fun A hA => hmodel A _ hA

@[expose] def GGLayerUnitaryLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)

theorem largeEvenLabelAll_layerCenterCyclic_unitary
    (hU : GGLayerUnitaryModelInput) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGLayerUnitaryLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hlab⟩ := hlab
  dsimp only at hn
  intro Q hQ
  rcases h with h | ⟨h, hl⟩
  · dsimp only at h
    subst h
    obtain ⟨hl1, hl2⟩ := hlab
    dsimp only at hl1 hl2
    refine recipeUnitary_layerCenterCyclic (d := l + 1) (n := n) hU hp hp2 hn (by omega)
      (fun hdq => ?_) hQ
    have h1 : l + 1 = 3 := congrArg Prod.fst hdq
    have h2 : 2 ^ n = 2 := congrArg Prod.snd hdq
    have h3 : 2 ≤ n := hl2 (by omega)
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    omega
  · dsimp only at h hl
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [show (3 : ℕ) ≠ 2 by norm_num, ite_true, ite_false] at hQ ⊢
    exact recipeUnitary_layerCenterCyclic hU hp hp2 hn (by norm_num)
      (fun hdq => absurd (congrArg Prod.fst hdq) (by norm_num)) hQ

@[expose] def GGLayerSymplecticModelInput : Prop :=
  ∀ (m n : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n → 1 ≤ n → 2 ≤ m →
    (m = 2 → 2 ≤ n) → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ (A : GL (Fin m ⊕ Fin m) K)
        (hA : A ∈ Subgroup.normalizer (LargeEvenSpGroup K m : Set (GL (Fin m ⊕ Fin m) K))),
        A ∈ LargeEvenGSpSet K m → GGModelLayerCyclic p (ggMatConjAut hA)

theorem recipeSymplectic_layerCenterCyclic
    (hS : GGLayerSymplecticModelInput) {m n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) (hm : 2 ≤ m) (hm2 : m = 2 → 2 ≤ n)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic m (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic m (2 ^ n) false fun R _ I F => Q R I F ∧
      LargeEvenSimpleGuard (fun R _ I _ => GGLayerCenterCyclic p R I) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := LayerCC.charP_two_of_natCard hK
  have hmodel := hS m n K hK hn hm hm2 p hp hp2
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ =>
    ggLayerCenterCyclic_matConj hp (LayerCC.commutator_largeEvenSpGroup hK hn hm hm2)
      (ggPSections_sp hm hp hp2) (fun _ hA => LayerCC.gsp_subset_normalizer_sp hA)
      fun A hA => hmodel A _ hA⟩

theorem LayerCC.largeEvenScalars_subgroupOf_le_center {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (H : Subgroup (GL ι K)) :
    (LargeEvenScalars ι K).subgroupOf H ≤ Subgroup.center H := by
  have h := LayerCC.ker_largeEvenProjMk_le_center H
  rwa [LargeEvenProjMk, QuotientGroup.ker_mk'] at h

@[expose] def GGLayerOmegaPlusModelInput : Prop :=
  ∀ (m n : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n → 1 ≤ n → 4 ≤ m →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      commutator (LargeEvenOmega (LargeEvenQPlus K m)) = ⊤ ∧
        GGPSections p (LargeEvenOmega (LargeEvenQPlus K m)) ∧
        ∀ h : LargeEvenOmega (LargeEvenQPlus K m), GGModelLayerCyclic p (MulAut.conj h)

@[expose] def GGLayerOmegaMinusModelInput : Prop :=
  ∀ (m n : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n → 1 ≤ n → 3 ≤ m →
    ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) → ∀ p : ℕ, p.Prime → p ≠ 2 →
      commutator (LargeEvenOmega (LargeEvenQMinus m b c)) = ⊤ ∧
        GGPSections p (LargeEvenOmega (LargeEvenQMinus m b c)) ∧
        ∀ h : LargeEvenOmega (LargeEvenQMinus m b c), GGModelLayerCyclic p (MulAut.conj h)

theorem recipeOmegaPlus_layerCenterCyclic (hO : GGLayerOmegaPlusModelInput) {m n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) (hm : 4 ≤ m) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus m (2 ^ n) fun R _ I F => Q R I F ∧
      LargeEvenSimpleGuard (fun R _ I _ => GGLayerCenterCyclic p R I) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨hperf, hsec, hmodel⟩ := hO m n K hK hn hm p hp hp2
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ =>
    ggLayerCenterCyclic_inn hp _ (LayerCC.largeEvenScalars_subgroupOf_le_center _) hperf hsec
      hmodel⟩

theorem recipeOmegaMinus_layerCenterCyclic (hO : GGLayerOmegaMinusModelInput) {m n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) (hm : 3 ≤ m) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F => Q R I F ∧
      LargeEvenSimpleGuard (fun R _ I _ => GGLayerCenterCyclic p R I) R I F := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  obtain ⟨hperf, hsec, hmodel⟩ := hO m n K hK hn hm b c hbc p hp hp2
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, fun _ _ =>
    ggLayerCenterCyclic_inn hp _ (LayerCC.largeEvenScalars_subgroupOf_le_center _) hperf hsec
      hmodel⟩

@[expose] def GGLayerClassicalLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD

theorem largeEvenLabelAll_layerCenterCyclic_classical
    (hU : GGLayerUnitaryModelInput)
    (hS : GGLayerSymplecticModelInput) (hOp : GGLayerOmegaPlusModelInput)
    (hOm : GGLayerOmegaMinusModelInput) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGLayerClassicalLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I) := by
  by_cases hlin : GGLayerLinearLabel lab
  · exact largeEvenLabelAll_layerCenterCyclic_linear hp hp2 hlab hlin
  by_cases hun : GGLayerUnitaryLabel lab
  · exact largeEvenLabelAll_layerCenterCyclic_unitary hU hp hp2 hlab hun
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hlab⟩ := hlab
  dsimp only at hn
  intro Q hQ
  rcases h with h | h | h | h | h | h
  · exact absurd (Or.inl h) hlin
  · exact absurd (Or.inl h) hun
  · dsimp only at h
    subst h
    obtain ⟨hl1, hl2⟩ := hlab
    dsimp only at hl1 hl2
    exact recipeSymplectic_layerCenterCyclic (m := l) (n := n) hS hp hp2 hn hl1 hl2 hQ
  · dsimp only at h
    subst h
    obtain ⟨hl1, hl2⟩ := hlab
    dsimp only at hl1 hl2
    exact recipeSymplectic_layerCenterCyclic (m := l) (n := n) hS hp hp2 hn hl1 hl2 hQ
  · dsimp only at h
    subst h
    have hl : l ≠ 3 := fun hl => hlin (Or.inr (Or.inl ⟨rfl, hl⟩))
    have hl4 : 4 ≤ l := by
      have := hlab
      dsimp only at this
      omega
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [hl, ite_false] at hQ ⊢
    exact recipeOmegaPlus_layerCenterCyclic (m := l) (n := n) hOp hp hp2 hn hl4 hQ
  · dsimp only at h
    subst h
    have hl2 : l ≠ 2 := fun hl => hlin (Or.inr (Or.inr ⟨rfl, hl⟩))
    have hl3 : l ≠ 3 := fun hl => hun (Or.inr ⟨rfl, hl⟩)
    have hl4 : 4 ≤ l := by
      have := hlab
      dsimp only at this
      omega
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [hl2, hl3, ite_false] at hQ ⊢
    exact recipeOmegaMinus_layerCenterCyclic (m := l - 1) (n := n) hOm hp hp2 hn (by omega) hQ

theorem ggLayerCenterCyclicInput_of_classical
    (hU : GGLayerUnitaryModelInput)
    (hS : GGLayerSymplecticModelInput) (hOp : GGLayerOmegaPlusModelInput)
    (hOm : GGLayerOmegaMinusModelInput)
    (hexc : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGLayerClassicalLabel lab →
        LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I)) :
    GGLayerCenterCyclicInput := by
  intro p lab hp hp2 hlab hsplit
  by_cases h : GGLayerClassicalLabel lab
  · exact largeEvenLabelAll_layerCenterCyclic_classical hU hS hOp hOm hp hp2 hlab h
  · exact hexc p lab hp hp2 hlab hsplit h

end CFSG.StandardType

end
