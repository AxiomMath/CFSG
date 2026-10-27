module

public import CFSG.LocalAnalysis.StandardType.E6GraphNoneStepFiveMoved

public section

namespace CFSG.StandardType.E6GraphNoneSteps

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.E6GraphNoneSteps CFSG.RankThree.E6

abbrev V6 := Fin TwistTag.E6.tag.rank → ℤ

@[expose] def piF (i : Fin TwistTag.E6.tag.rank) : Fin Tag.F4.rank := e6IndexToF4 i

private abbrev eR (m : Fin 72) : V6 := e6R m

private theorem perm_perm : ∀ i : Fin TwistTag.E6.tag.rank,
    TwistTag.E6.perm (TwistTag.E6.perm i) = i := by
  decide

private theorem perm_symm : ∀ i : Fin TwistTag.E6.tag.rank,
    TwistTag.E6.perm.symm i = TwistTag.E6.perm i := by
  decide

private theorem foldT : ∀ m : Fin 72, ∀ i : Fin TwistTag.E6.tag.rank,
    (∀ k : Fin Tag.F4.rank, ((∑ j : Fin TwistTag.E6.tag.rank, if piF j = k then
        eR m j else 0 : ℤ) : ZMod 3) = if piF i = k then -1 else 0) →
    eR m = -Pi.single i 1 ∨ eR m = -Pi.single (TwistTag.E6.perm i) 1 := by
  decide +kernel

private def selT (c : Fin TwistTag.E6.tag.rank → Bool) (i : Fin TwistTag.E6.tag.rank) :
    Fin TwistTag.E6.tag.rank :=
  if c i then TwistTag.E6.perm i else i

private def imgT (c : Fin TwistTag.E6.tag.rank → Bool) (v : V6) : V6 :=
  fun j => -∑ i, if selT c i = j then v i else 0

private def testT : List V6 :=
  [![1,0,1,0,0,0], ![0,0,0,0,1,1], ![1,0,1,1,1,0], ![0,0,1,1,1,1]]

private theorem selCasesT : ∀ c : Fin TwistTag.E6.tag.rank → Bool,
    (∀ v ∈ testT, ∃ m : Fin 72, eR m = imgT c v) →
    (∀ i, selT c i = i) ∨ (∀ i, selT c i = TwistTag.E6.perm i) := by
  decide +kernel

private theorem testT_isRoot : ∀ v ∈ testT, ∃ m : Fin 72, eR m = v := by
  decide +kernel


private theorem smul_eq_imgT (w : WeylGroup TwistTag.E6.tag)
    (c : Fin TwistTag.E6.tag.rank → Bool)
    (hr : ∀ i, w • (Pi.single i 1 : V6) = -(Pi.single (selT c i) 1 : V6)) (v : V6) :
    w • v = imgT c v := by
  rw [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.smul_eq_sum_single]
  funext j
  simp only [hr, Finset.sum_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, imgT]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : selT c i = j
  · subst h; simp
  · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h)]; simp

private theorem imgT_id {c : Fin TwistTag.E6.tag.rank → Bool} (h : ∀ i, selT c i = i)
    (v : V6) : imgT c v = -v := by
  funext j
  simp only [imgT, h, Pi.neg_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem imgT_perm {c : Fin TwistTag.E6.tag.rank → Bool}
    (h : ∀ i, selT c i = TwistTag.E6.perm i) (v : V6) :
    imgT c v = -permLattice TwistTag.E6.perm v := by
  funext j
  simp only [imgT, h, Pi.neg_apply, permLattice, Function.comp_apply, perm_symm]
  congr 1
  rw [Finset.sum_eq_single (TwistTag.E6.perm j)]
  · rw [perm_perm, if_pos rfl]
  · intro b _ hb
    rw [if_neg]
    intro h'
    exact hb (by rw [← h', perm_perm])
  · simp

private theorem smul_cases (w : WeylGroup TwistTag.E6.tag)
    (h : (∀ v : V6, w • v = -v) ∨ (∀ v : V6, w • v = -permLattice TwistTag.E6.perm v)) :
    (∀ v : V6, w⁻¹ • v = -v) ∨
      (∀ v : V6, w⁻¹ • v = -permLattice TwistTag.E6.perm v) := by
  rcases h with h | h
  · refine Or.inl fun v => ?_
    have := h (w⁻¹ • v)
    rw [smul_inv_smul] at this
    exact neg_eq_iff_eq_neg.1 this.symm
  · refine Or.inr fun v => ?_
    have := h (w⁻¹ • v)
    rw [smul_inv_smul] at this
    have h2 : permLattice TwistTag.E6.perm v = -(w⁻¹ • v) :=
      calc permLattice TwistTag.E6.perm v =
          permLattice TwistTag.E6.perm (-permLattice TwistTag.E6.perm (w⁻¹ • v)) :=
            congrArg _ this
        _ = -(w⁻¹ • v) := by rw [rho_neg, rho_rho]
    exact neg_eq_iff_eq_neg.1 h2.symm

theorem exists_orderOf_three (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] :
    ∃ ζ : Lˣ, orderOf ζ = 3 := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : L) ≠ 0 := by
    intro h
    have h1 : (1 : L) = 0 := by linear_combination h - h2
    exact one_ne_zero h1
  have : NeZero (3 : L) := ⟨h3⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  have hu : IsUnit ζ := hζ.isUnit (by norm_num)
  exact ⟨hu.unit, (IsPrimitiveRoot.coe_units_iff.1 (by simpa using hζ)).eq_orderOf.symm⟩

private theorem rootChar_fold {L : Type} [Field L] (ζ : Lˣ) (k : Fin Tag.F4.rank) (v : V6) :
    rootChar (fun i : Fin TwistTag.E6.tag.rank =>
        (Pi.mulSingle k ζ : Fin Tag.F4.rank → Lˣ) (e6IndexToF4 i)) v =
      ζ ^ (∑ j, if piF j = k then v j else 0) := by
  rw [rootChar, ← CFSG.RankThree.PartOne.KLR.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases h : piF j = k
  · rw [if_pos h]; simp only [piF] at h; rw [h, Pi.mulSingle_eq_same]
  · rw [if_neg h, zpow_zero]; simp only [piF] at h
    rw [Pi.mulSingle_eq_of_ne h, one_zpow]

private theorem fold_eq_neg_of_inverts {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (w : WeylGroup TwistTag.E6.tag)
    (hw : ∀ b : Fin Tag.F4.rank → Lˣ,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w (fun i => b (e6IndexToF4 i)) =
        (fun i => b (e6IndexToF4 i))⁻¹)
    (i : Fin TwistTag.E6.tag.rank) (k : Fin Tag.F4.rank) :
    ((∑ j : Fin TwistTag.E6.tag.rank, if piF j = k then
        (w⁻¹ • (Pi.single i 1 : V6)) j else 0 : ℤ) : ZMod 3) =
      if piF i = k then -1 else 0 := by
  obtain ⟨ζ, hζ⟩ := exists_orderOf_three L
  have h : rootChar (fun j : Fin TwistTag.E6.tag.rank =>
      (Pi.mulSingle k ζ : Fin Tag.F4.rank → Lˣ) (e6IndexToF4 j))
      (w⁻¹ • (Pi.single i 1 : V6)) =
      ((Pi.mulSingle k ζ : Fin Tag.F4.rank → Lˣ) (e6IndexToF4 i))⁻¹ :=
    congrFun (hw (Pi.mulSingle k ζ)) i
  rw [rootChar_fold] at h
  have h' : (Pi.mulSingle k ζ : Fin Tag.F4.rank → Lˣ) (e6IndexToF4 i) =
      ζ ^ (if piF i = k then (1 : ℤ) else 0) := by
    by_cases hi : piF i = k
    · rw [if_pos hi, zpow_one]; simp only [piF] at hi; rw [hi, Pi.mulSingle_eq_same]
    · rw [if_neg hi, zpow_zero]; simp only [piF] at hi; rw [Pi.mulSingle_eq_of_ne hi]
  rw [h', ← zpow_neg, zpow_eq_zpow_iff_modEq, hζ] at h
  rw [(ZMod.intCast_eq_intCast_iff _ _ 3).2 h]
  split_ifs <;> simp

private theorem wt_inv_smul_basis_eq_neg_or_neg_perm {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] (w : WeylGroup TwistTag.E6.tag)
    (hw : ∀ b : Fin Tag.F4.rank → Lˣ,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w (fun i => b (e6IndexToF4 i)) =
        (fun i => b (e6IndexToF4 i))⁻¹) :
    ∀ i, w⁻¹ • (Pi.single i 1 : V6) = -Pi.single i 1 ∨
      w⁻¹ • (Pi.single i 1 : V6) = -Pi.single (TwistTag.E6.perm i) 1 := by
  intro i
  obtain ⟨m, hm⟩ := isRoot_iff_exists_e6RootVec.1
    (IsRoot.smul (IsRoot.basis (τ := TwistTag.E6.tag) i) w⁻¹)
  have hm' : eR m = w⁻¹ • (Pi.single i 1 : V6) := hm
  rw [← hm']
  exact foldT m i (fun k => by
    rw [hm']
    exact fold_eq_neg_of_inverts w hw i k)

private theorem wt_inv_smul_eq_neg_or_neg_perm {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] (w : WeylGroup TwistTag.E6.tag)
    (hw : ∀ b : Fin Tag.F4.rank → Lˣ,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w (fun i => b (e6IndexToF4 i)) =
        (fun i => b (e6IndexToF4 i))⁻¹) :
    (∀ v : V6, w⁻¹ • v = -v) ∨
      (∀ v : V6, w⁻¹ • v = -permLattice TwistTag.E6.perm v) := by
  classical
  have hcase := wt_inv_smul_basis_eq_neg_or_neg_perm (L := L) w hw
  set c : Fin TwistTag.E6.tag.rank → Bool :=
    fun i => decide (w⁻¹ • (Pi.single i 1 : V6) ≠ -Pi.single i 1)
  have hr : ∀ i, w⁻¹ • (Pi.single i 1 : V6) = -(Pi.single (selT c i) 1 : V6) := by
    intro i
    by_cases h : w⁻¹ • (Pi.single i 1 : V6) = -Pi.single i 1
    · have : c i = false := by simp [c, h]
      simp only [selT, this]; exact h
    · have : c i = true := by simp [c, h]
      simp only [selT, this, if_true]
      exact (hcase i).resolve_left h
  have himg := smul_eq_imgT w⁻¹ c hr
  have hsel := selCasesT c fun v hv => by
    obtain ⟨m, hm⟩ := testT_isRoot v hv
    obtain ⟨m', hm'⟩ := isRoot_iff_exists_e6RootVec.1
      (IsRoot.smul (isRoot_iff_exists_e6RootVec.2 ⟨m, hm⟩) w⁻¹)
    exact ⟨m', hm'.trans (himg v)⟩
  rcases hsel with hs | hs
  · exact Or.inl fun v => (himg v).trans (imgT_id hs v)
  · exact Or.inr fun v => (himg v).trans (imgT_perm hs v)

theorem wt_cases {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (w : WeylGroup TwistTag.E6.tag)
    (hw : ∀ b : Fin Tag.F4.rank → Lˣ,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w (fun i => b (e6IndexToF4 i)) =
        (fun i => b (e6IndexToF4 i))⁻¹) :
    (∀ v : V6, w • v = -v) ∨ (∀ v : V6, w • v = -permLattice TwistTag.E6.perm v) := by
  simpa using smul_cases w⁻¹ (wt_inv_smul_eq_neg_or_neg_perm w hw)

end CFSG.StandardType.E6GraphNoneSteps
