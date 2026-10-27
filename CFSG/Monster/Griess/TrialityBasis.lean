module

public import CFSG.Monster.Griess.TrialityBasis.Classes
public import CFSG.Monster.Griess.Space

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice Matrix Module
  Subgroup

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem sgn_mul_self' (t : ZMod 2) : sgn t * sgn t = 1 := by
  rcases zmod2_cases t with rfl | rfl <;> norm_num [sgn]

private theorem sgn_mem_dyadic (t : ZMod 2) : sgn t ∈ dyadic := by
  rcases zmod2_cases t with rfl | rfl
  · exact dyadic.one_mem
  · exact dyadic.neg_mem dyadic.one_mem

theorem Xlift_labelElt (l : ShortLabel) : Xlift (labelElt l) = Pi.single (labelIdx l) 1 := by
  rw [Xlift_eq (isShortCoord_labelElt l), centralCoord_labelElt, sgn_zero, one_smul]
  rfl

theorem Xlift_labelElt_dotProduct (l l' : ShortLabel) :
    Xlift (labelElt l) ⬝ᵥ Xlift (labelElt l') = if l = l' then 1 else 0 := by
  rw [Xlift_labelElt, Xlift_labelElt, single_dotProduct_single]
  simp only [labelIdx_injective.eq_iff]

abbrev AIdx : Type := Fin 24 ⊕ LtPair

abbrev XIdx : Type := (LtPair × Fin 2) ⊕ (C₀ × Fin 24) ⊕ OctIdx

abbrev WIdx : Type := C₀ × Fin 24 × Fin 2

abbrev BlockIdx : Type := AIdx ⊕ XIdx ⊕ WIdx

noncomputable instance : DecidableEq XIdx :=
  @instDecidableEqSum _ _ inferInstance (@instDecidableEqSum _ _ inferInstance inferInstance)

noncomputable instance : DecidableEq BlockIdx :=
  @instDecidableEqSum _ _ inferInstance (@instDecidableEqSum _ _ inferInstance inferInstance)

@[expose] def aPair : AIdx → PairIdx
  | .inl i => s(i, i)
  | .inr p => s(p.1.1, p.1.2)

theorem aPair_injective : Function.Injective aPair := by
  rintro (i | p) (i' | p') h <;> simp only [aPair, Sym2.eq_iff] at h
  · rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (h1.symm.trans h2) p'.2.ne
    · exact absurd (h2.symm.trans h1) p'.2.ne
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) p.2.ne
    · exact absurd (h1.trans h2.symm) p.2.ne
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact congrArg Sum.inr (ltPair_eq h1 h2)
    · have h3 : p'.1.2 < p'.1.1 := by
        rw [← h1, ← h2]
        exact p.2
      exact absurd p'.2 (lt_asymm h3)

@[expose] noncomputable def xVec : XIdx → SpaceX
  | .inl (p, k) => ![Xlift (rMinus p.1.1 p.1.2) - Xlift (rPlus p.1.1 p.1.2),
      Xlift (rMinus p.1.1 p.1.2) + Xlift (rPlus p.1.1 p.1.2)] k
  | .inr (.inl q) => Xlift (rOdd q.1 q.2)
  | .inr (.inr o) => Xlift (rOctQ o.1 o.2)

@[expose] def wEta : Fin 2 → ZMod 2 := ![1, 0]

@[expose] noncomputable def wSign (c : C₀) (i : Fin 24) : Fin 2 → ℚ :=
  ![sgn (((c : C) : Fin 24 → ZMod 2) i), sgn (P ((c : C) : Fin 24 → ZMod 2))]

@[expose] noncomputable def wVec : WIdx → SpaceW
  | (c, i, k) => wSign c i k • tensor (Spin.E (wEta k) c) (Pi.single i 1)

@[expose] noncomputable def blockVec : BlockIdx → SpaceB
  | .inl a => (basisA (aPair a), 0, 0)
  | .inr (.inl x) => (0, xVec x, 0)
  | .inr (.inr w) => (0, 0, wVec w)

@[expose] def blockNorm : BlockIdx → ℚ
  | .inl (.inr _) => 2
  | .inr (.inl (.inl _)) => 2
  | _ => 1

theorem bform_mk (a a' : symMat) (x x' : SpaceX) (w w' : SpaceW) :
    bform (a, x, w) (a', x', w') = trace ((a : Matrix (Fin 24) (Fin 24) ℚ) *
      (a' : Matrix (Fin 24) (Fin 24) ℚ)) + x ⬝ᵥ x' + ∑ j, ∑ i, w j i * w' j i := rfl

theorem trace_basisA_aPair (a a' : AIdx) :
    trace ((basisA (aPair a) : Matrix (Fin 24) (Fin 24) ℚ) *
      (basisA (aPair a') : Matrix (Fin 24) (Fin 24) ℚ)) =
      if a = a' then blockNorm (.inl a) else 0 := by
  rw [trace_basisA_mul]
  by_cases h : a = a'
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl]
    rcases a with i | p
    · simp [gramDiag, aPair, blockNorm]
    · simp [gramDiag, aPair, blockNorm, p.2.ne]
  · rw [ite_eq_right (aPair_injective.ne h), ite_eq_right h]

theorem xVec_inl (p : LtPair) (k : Fin 2) :
    xVec (.inl (p, k)) = ![Xlift (labelElt (.inl p)) - Xlift (labelElt (.inr (.inl p))),
      Xlift (labelElt (.inl p)) + Xlift (labelElt (.inr (.inl p)))] k := rfl

theorem xVec_odd (q : C₀ × Fin 24) :
    xVec (.inr (.inl q)) = Xlift (labelElt (.inr (.inr (.inl q)))) := rfl

theorem xVec_oct (o : OctIdx) : xVec (.inr (.inr o)) = Xlift (labelElt (.inr (.inr (.inr o)))) :=
  rfl

theorem xVec_dotProduct (x x' : XIdx) :
    xVec x ⬝ᵥ xVec x' = if x = x' then blockNorm (.inr (.inl x)) else 0 := by
  rcases x with ⟨p, k⟩ | q | o <;> rcases x' with ⟨p', k'⟩ | q' | o'
  · rw [xVec_inl, xVec_inl]
    by_cases hp : p = p'
    · subst hp
      fin_cases k <;> fin_cases k' <;>
        simp [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add,
          Xlift_labelElt_dotProduct, blockNorm] <;> norm_num
    · fin_cases k <;> fin_cases k' <;>
        simp [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add,
          Xlift_labelElt_dotProduct, hp]
  · rw [xVec_inl, xVec_odd]
    fin_cases k <;>
      simp [sub_dotProduct, add_dotProduct, Xlift_labelElt_dotProduct]
  · rw [xVec_inl, xVec_oct]
    fin_cases k <;>
      simp [sub_dotProduct, add_dotProduct, Xlift_labelElt_dotProduct]
  · rw [xVec_odd, xVec_inl]
    fin_cases k' <;>
      simp [dotProduct_sub, dotProduct_add, Xlift_labelElt_dotProduct]
  · rw [xVec_odd, xVec_odd, Xlift_labelElt_dotProduct]
    simp [blockNorm]
  · rw [xVec_odd, xVec_oct, Xlift_labelElt_dotProduct]
    simp
  · rw [xVec_oct, xVec_inl]
    fin_cases k' <;>
      simp [dotProduct_sub, dotProduct_add, Xlift_labelElt_dotProduct]
  · rw [xVec_oct, xVec_odd, Xlift_labelElt_dotProduct]
    simp
  · rw [xVec_oct, xVec_oct, Xlift_labelElt_dotProduct]
    simp [blockNorm]

theorem wEta_injective : Function.Injective wEta := by decide

theorem wSign_mul_self (c : C₀) (i : Fin 24) (k : Fin 2) : wSign c i k * wSign c i k = 1 := by
  fin_cases k <;> exact sgn_mul_self' _

theorem wVec_eq_tensor (w : WIdx) :
    wVec w = tensor (wSign w.1 w.2.1 w.2.2 • Spin.E (wEta w.2.2) w.1) (Pi.single w.2.1 1) := by
  obtain ⟨c, i, k⟩ := w
  rw [wVec, tensor, tensor, smul_vecMulVec]

theorem bform_wVec (w w' : WIdx) :
    bform (0, 0, wVec w) (0, 0, wVec w') = if w = w' then 1 else 0 := by
  rw [wVec_eq_tensor, wVec_eq_tensor, bform_tensor, smul_dotProduct, dotProduct_smul,
    E_dotProduct_E, single_dotProduct_single]
  obtain ⟨c, i, k⟩ := w
  obtain ⟨c', i', k'⟩ := w'
  simp only [smul_eq_mul, Prod.mk.injEq, wEta_injective.eq_iff]
  by_cases hk : k = k'
  · subst hk
    by_cases hc : c = c'
    · subst hc
      by_cases hi : i = i'
      · subst hi
        simp only [and_self, ite_true, mul_one]
        rw [mul_comm]
        exact wSign_mul_self c i k
      · simp [hi]
    · simp [hc]
  · simp [hk]

theorem bform_blockVec (β β' : BlockIdx) :
    bform (blockVec β) (blockVec β') = if β = β' then blockNorm β else 0 := by
  rcases β with a | x | w <;> rcases β' with a' | x' | w'
  · rw [blockVec, blockVec, bform_mk, trace_basisA_aPair]
    simp
  · rw [blockVec, blockVec, bform_mk]
    simp
  · rw [blockVec, blockVec, bform_mk]
    simp
  · rw [blockVec, blockVec, bform_mk]
    simp
  · rw [blockVec, blockVec, bform_mk, xVec_dotProduct]
    simp
  · rw [blockVec, blockVec, bform_mk]
    simp
  · rw [blockVec, blockVec, bform_mk]
    simp
  · rw [blockVec, blockVec, bform_mk]
    simp
  · rw [blockVec, blockVec, bform_wVec]
    simp [blockNorm]

abbrev TIdx : Type := Fin 24 ⊕ (LtPair × Fin 3) ⊕ (C₀ × Fin 24 × Fin 3) ⊕ OctIdx

noncomputable instance : DecidableEq TIdx :=
  @instDecidableEqSum _ _ inferInstance
    (@instDecidableEqSum _ _ inferInstance (@instDecidableEqSum _ _ inferInstance inferInstance))

@[expose] def toBlock : TIdx → BlockIdx
  | .inl i => .inl (.inl i)
  | .inr (.inl (p, k)) => ![.inl (.inr p), .inr (.inl (.inl (p, 0))), .inr (.inl (.inl (p, 1)))] k
  | .inr (.inr (.inl (c, i, k))) =>
    ![.inr (.inl (.inr (.inl (c, i)))), .inr (.inr (c, i, 0)), .inr (.inr (c, i, 1))] k
  | .inr (.inr (.inr o)) => .inr (.inl (.inr (.inr o)))

@[expose] def ofBlock : BlockIdx → TIdx
  | .inl (.inl i) => .inl i
  | .inl (.inr p) => .inr (.inl (p, 0))
  | .inr (.inl (.inl (p, k))) => .inr (.inl (p, k.succ))
  | .inr (.inl (.inr (.inl q))) => .inr (.inr (.inl (q.1, q.2, 0)))
  | .inr (.inl (.inr (.inr o))) => .inr (.inr (.inr o))
  | .inr (.inr (c, i, k)) => .inr (.inr (.inl (c, i, k.succ)))

theorem ofBlock_toBlock (x : TIdx) : ofBlock (toBlock x) = x := by
  rcases x with i | ⟨p, k⟩ | ⟨c, i, k⟩ | o
  · rfl
  · fin_cases k <;> rfl
  · fin_cases k <;> rfl
  · rfl

theorem toBlock_injective : Function.Injective toBlock :=
  Function.LeftInverse.injective ofBlock_toBlock

@[expose] noncomputable def tvec (x : TIdx) : SpaceB := blockVec (toBlock x)

@[expose] def tnorm : TIdx → ℚ
  | .inr (.inl _) => 2
  | _ => 1

theorem tnorm_eq (x : TIdx) : tnorm x = blockNorm (toBlock x) := by
  rcases x with i | ⟨p, k⟩ | ⟨c, i, k⟩ | o
  · rfl
  · fin_cases k <;> rfl
  · fin_cases k <;> rfl
  · rfl

theorem tnorm_ne_zero (x : TIdx) : tnorm x ≠ 0 := by
  rcases x with i | ⟨p, k⟩ | ⟨c, i, k⟩ | o <;> norm_num [tnorm]

theorem bform_tvec (x y : TIdx) : bform (tvec x) (tvec y) = if x = y then tnorm x else 0 := by
  rw [tvec, tvec, bform_blockVec]
  simp only [toBlock_injective.eq_iff]
  rw [tnorm_eq]

theorem linearIndependent_tvec : LinearIndependent ℚ tvec := by
  refine LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := bform) ?_ ?_
  · intro x y hxy
    change bform (tvec x) (tvec y) = 0
    rw [bform_tvec, ite_eq_right hxy]
  · intro x
    rw [bform_tvec, ite_eq_left rfl]
    exact tnorm_ne_zero x

theorem card_ltPair : Fintype.card LtPair = 276 := by
  rw [Fintype.card_subtype]
  decide +kernel

theorem card_octadWord : Fintype.card OctadWord = 759 := by
  rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ C)
      (fun x => hammingNorm x = 8)), Fintype.card_of_subtype octFin (fun _ => mem_octFin),
    card_octFin]

theorem card_evenQuot_octSupp (d : OctadWord) : Fintype.card (Octad.EvenQuot (octSupp d)) = 64 :=
  Octad.card_evenQuot (card_octSupp d)

theorem card_octIdx : Fintype.card OctIdx = 759 * 64 := by
  rw [Fintype.card_sigma, Finset.sum_congr rfl fun d _ => card_evenQuot_octSupp d,
    Finset.sum_const, Finset.card_univ, card_octadWord, smul_eq_mul]

theorem card_tIdx : Fintype.card TIdx = 196884 := by
  simp only [TIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_ltPair, card_C₀,
    card_octIdx]

theorem card_shortLabel : Fintype.card ShortLabel = 98280 := by
  simp only [ShortLabel, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_ltPair,
    card_C₀, card_octIdx]

@[expose] noncomputable def tbasis : Basis TIdx ℚ SpaceB :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_tvec (card_tIdx.trans finrank_B.symm)

theorem coe_tbasis : ⇑tbasis = tvec := coe_basisOfLinearIndependentOfCardEqFinrank _ _

theorem tbasis_apply (x : TIdx) : tbasis x = blockVec (toBlock x) := congrFun coe_tbasis x

theorem bform_tbasis (x y : TIdx) : bform (tbasis x) (tbasis y) = if x = y then tnorm x else 0 := by
  rw [coe_tbasis]
  exact bform_tvec x y

theorem tbasis_diag (i : Fin 24) : tbasis (.inl i) = (basisA s(i, i), 0, 0) := tbasis_apply _

theorem tbasis_pair_zero (p : LtPair) :
    tbasis (.inr (.inl (p, 0))) = (basisA s(p.1.1, p.1.2), 0, 0) := tbasis_apply _

theorem tbasis_pair_one (p : LtPair) :
    tbasis (.inr (.inl (p, 1))) = (0, Xlift (rMinus p.1.1 p.1.2) - Xlift (rPlus p.1.1 p.1.2), 0) :=
  tbasis_apply _

theorem tbasis_pair_two (p : LtPair) :
    tbasis (.inr (.inl (p, 2))) = (0, Xlift (rMinus p.1.1 p.1.2) + Xlift (rPlus p.1.1 p.1.2), 0) :=
  tbasis_apply _

theorem tbasis_odd_zero (c : C₀) (i : Fin 24) :
    tbasis (.inr (.inr (.inl (c, i, 0)))) = (0, Xlift (rOdd c i), 0) := tbasis_apply _

theorem tbasis_odd_one (c : C₀) (i : Fin 24) :
    tbasis (.inr (.inr (.inl (c, i, 1)))) =
      (0, 0, sgn (((c : C) : Fin 24 → ZMod 2) i) • tensor (Spin.E 1 c) (Pi.single i 1)) :=
  tbasis_apply _

theorem tbasis_odd_two (c : C₀) (i : Fin 24) :
    tbasis (.inr (.inr (.inl (c, i, 2)))) =
      (0, 0, sgn (P ((c : C) : Fin 24 → ZMod 2)) • tensor (Spin.E 0 c) (Pi.single i 1)) :=
  tbasis_apply _

theorem tbasis_oct (o : OctIdx) : tbasis (.inr (.inr (.inr o))) = (0, Xlift (rOctQ o.1 o.2), 0) :=
  tbasis_apply _

theorem tbasis_oct_cls {d : OctadWord} {δ : Finset (Fin 24)} (hδ : δ ⊆ octSupp d)
    (he : Even δ.card) :
    tbasis (.inr (.inr (.inr ⟨d, Octad.cls (octSupp d) δ⟩))) = (0, Xlift (rOct d δ), 0) := by
  rw [tbasis_oct, rOctQ_cls hδ he]

theorem basisB_mem_BR (b : BIdx) : basisB b ∈ BR := Submodule.subset_span ⟨b, rfl⟩

theorem Xlift_labelElt_mem_BR (l : ShortLabel) :
    ((0 : symMat), Xlift (labelElt l), (0 : SpaceW)) ∈ BR := by
  rw [Xlift_labelElt, ← basisB_inr_inl]
  exact basisB_mem_BR _

theorem blockVec_W (c : C₀) (i : Fin 24) (k : Fin 2) :
    blockVec (.inr (.inr (c, i, k))) = wSign c i k • basisB (.inr (.inr ((wEta k, c), i))) := by
  rw [basisB_inr_inr, Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero]
  rfl

theorem blockVec_pair_zero (p : LtPair) :
    blockVec (.inr (.inl (.inl (p, 0)))) =
      ((0 : symMat), Xlift (labelElt (.inl p)), (0 : SpaceW)) -
        ((0 : symMat), Xlift (labelElt (.inr (.inl p))), (0 : SpaceW)) := by
  rw [Prod.mk_sub_mk, Prod.mk_sub_mk, sub_zero, sub_zero]
  rfl

theorem blockVec_pair_one (p : LtPair) :
    blockVec (.inr (.inl (.inl (p, 1)))) =
      ((0 : symMat), Xlift (labelElt (.inl p)), (0 : SpaceW)) +
        ((0 : symMat), Xlift (labelElt (.inr (.inl p))), (0 : SpaceW)) := by
  rw [Prod.mk_add_mk, Prod.mk_add_mk, add_zero, add_zero]
  rfl

theorem wSign_mem_dyadic (c : C₀) (i : Fin 24) (k : Fin 2) : wSign c i k ∈ dyadic := by
  fin_cases k <;> exact sgn_mem_dyadic _

theorem blockVec_mem_BR (β : BlockIdx) : blockVec β ∈ BR := by
  rcases β with a | (⟨p, k⟩ | q | o) | ⟨c, i, k⟩
  · rw [blockVec, ← basisB_inl]
    exact basisB_mem_BR _
  · have h₁ := Xlift_labelElt_mem_BR (.inl p)
    have h₂ := Xlift_labelElt_mem_BR (.inr (.inl p))
    fin_cases k
    · show blockVec (.inr (.inl (.inl (p, 0)))) ∈ BR
      rw [blockVec_pair_zero]
      exact BR.sub_mem h₁ h₂
    · show blockVec (.inr (.inl (.inl (p, 1)))) ∈ BR
      rw [blockVec_pair_one]
      exact BR.add_mem h₁ h₂
  · exact Xlift_labelElt_mem_BR (.inr (.inr (.inl q)))
  · exact Xlift_labelElt_mem_BR (.inr (.inr (.inr o)))
  · rw [blockVec_W]
    exact BR.smul_mem ⟨_, wSign_mem_dyadic c i k⟩ (basisB_mem_BR _)

theorem tbasis_mem_BR (x : TIdx) : tbasis x ∈ BR := by
  rw [tbasis_apply]
  exact blockVec_mem_BR _

abbrev tspan : Submodule dyadic SpaceB := Submodule.span dyadic (Set.range tbasis)

theorem tbasis_mem_tspan (x : TIdx) : tbasis x ∈ tspan := Submodule.subset_span ⟨x, rfl⟩

theorem Xlift_labelElt_mem_tspan (l : ShortLabel) :
    ((0 : symMat), Xlift (labelElt l), (0 : SpaceW)) ∈ tspan := by
  rcases l with p | p | q | o
  · have e : ((0 : symMat), Xlift (labelElt (.inl p)), (0 : SpaceW)) =
        (2 : ℚ)⁻¹ • (tbasis (.inr (.inl (p, 1))) + tbasis (.inr (.inl (p, 2)))) := by
      rw [tbasis_pair_one, tbasis_pair_two, Prod.mk_add_mk, Prod.mk_add_mk, Prod.smul_mk,
        Prod.smul_mk, add_zero, add_zero, smul_zero, smul_zero]
      congr 2
      change _ = (2 : ℚ)⁻¹ • (Xlift (labelElt (.inl p)) - Xlift (labelElt (.inr (.inl p))) +
        (Xlift (labelElt (.inl p)) + Xlift (labelElt (.inr (.inl p)))))
      rw [sub_add_add_cancel, ← two_smul ℚ, smul_smul]
      norm_num
    rw [e]
    exact tspan.smul_mem ⟨_, two_mem_dyadic_inv⟩ (tspan.add_mem (tbasis_mem_tspan _)
      (tbasis_mem_tspan _))
  · have e : ((0 : symMat), Xlift (labelElt (.inr (.inl p))), (0 : SpaceW)) =
        (2 : ℚ)⁻¹ • (tbasis (.inr (.inl (p, 2))) - tbasis (.inr (.inl (p, 1)))) := by
      rw [tbasis_pair_one, tbasis_pair_two, Prod.mk_sub_mk, Prod.mk_sub_mk, Prod.smul_mk,
        Prod.smul_mk, sub_zero, sub_zero, smul_zero, smul_zero]
      congr 2
      change _ = (2 : ℚ)⁻¹ • (Xlift (labelElt (.inl p)) + Xlift (labelElt (.inr (.inl p))) -
        (Xlift (labelElt (.inl p)) - Xlift (labelElt (.inr (.inl p)))))
      rw [add_sub_sub_cancel, ← two_smul ℚ, smul_smul]
      norm_num
    rw [e]
    exact tspan.smul_mem ⟨_, two_mem_dyadic_inv⟩ (tspan.sub_mem (tbasis_mem_tspan _)
      (tbasis_mem_tspan _))
  · have e : tbasis (.inr (.inr (.inl (q.1, q.2, 0)))) =
        ((0 : symMat), Xlift (labelElt (.inr (.inr (.inl q)))), (0 : SpaceW)) :=
      tbasis_odd_zero q.1 q.2
    rw [← e]
    exact tbasis_mem_tspan _
  · have e : tbasis (.inr (.inr (.inr o))) =
        ((0 : symMat), Xlift (labelElt (.inr (.inr (.inr o)))), (0 : SpaceW)) := tbasis_oct o
    rw [← e]
    exact tbasis_mem_tspan _

theorem basisB_mem_tspan (b : BIdx) : basisB b ∈ tspan := by
  rcases b with z | c | ⟨⟨η, c⟩, i⟩
  · induction z using Sym2.ind with
    | h i j =>
      rw [basisB_inl]
      rcases lt_trichotomy i j with h | rfl | h
      · rw [← tbasis_pair_zero ⟨(i, j), h⟩]
        exact tbasis_mem_tspan _
      · rw [← tbasis_diag]
        exact tbasis_mem_tspan _
      · rw [Sym2.eq_swap, ← tbasis_pair_zero ⟨(j, i), h⟩]
        exact tbasis_mem_tspan _
  · obtain ⟨l, rfl⟩ := labelIdx_surjective c
    rw [basisB_inr_inl, ← Xlift_labelElt]
    exact Xlift_labelElt_mem_tspan l
  · have hk : ∃ k : Fin 2, wEta k = η := by
      rcases zmod2_cases η with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
    obtain ⟨k, rfl⟩ := hk
    have e2 : tbasis (.inr (.inr (.inl (c, i, k.succ)))) = blockVec (.inr (.inr (c, i, k))) := by
      rw [tbasis_apply]
      fin_cases k <;> rfl
    have e : basisB (.inr (.inr ((wEta k, c), i))) =
        wSign c i k • tbasis (.inr (.inr (.inl (c, i, k.succ)))) := by
      rw [e2, blockVec_W, smul_smul, wSign_mul_self, one_smul]
    rw [e]
    exact tspan.smul_mem ⟨_, wSign_mem_dyadic c i k⟩ (tbasis_mem_tspan _)

theorem span_tbasis : Submodule.span dyadic (Set.range tbasis) = BR := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact tbasis_mem_BR x
  · rw [BR, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact basisB_mem_tspan b

theorem short_vector_triality_basis :
    (∀ i j : Fin 24, deltaPair i j = Submodule.Quotient.mk (Pi.single i 1 + Pi.single j 1) ∧
      rMinus i j = DQ (deltaPair i j) ∧ rPlus i j = XQ ⟨ΩC, 0⟩ * DQ (deltaPair i j)) ∧
    (∀ (c : C₀) (i : Fin 24),
      mOdd c i = ((c : C) : Fin 24 → ZMod 2) i + P ((c : C) : Fin 24 → ZMod 2) ∧
      rOdd c i = XQ ⟨(c : C) + mOdd c i • ΩC, 0⟩ * DQ (Submodule.Quotient.mk (Pi.single i 1))) ∧
    (∀ (d : C) (δ : Finset (Fin 24)), nOct δ = ((δ.card / 2 : ℕ) : ZMod 2) ∧
      rOct d δ = XQ ⟨d + nOct δ • ΩC, 0⟩ * DQ (Submodule.Quotient.mk (Octad.ind δ))) ∧
    (∀ (d : OctadWord) (δ : Finset (Fin 24)), δ ⊆ octSupp d → Even δ.card →
      rOct d (octSupp d \ δ) = rOct d δ ∧ rOctQ d (Octad.cls (octSupp d) δ) = rOct d δ) ∧
    (∀ p : LtPair,
      IsShort (QuotientGroup.mk (rMinus p.1.1 p.1.2)) ∧
      IsShort (QuotientGroup.mk (rPlus p.1.1 p.1.2)) ∧
      (4 : ℤ) • eℤ p.1.1 - (4 : ℤ) • eℤ p.1.2 ∈ minVecs ∧
      (4 : ℤ) • eℤ p.1.1 + (4 : ℤ) • eℤ p.1.2 ∈ minVecs ∧
      Multiplicative.toAdd (phi (QuotientGroup.mk (rMinus p.1.1 p.1.2))) =
        classOf ((4 : ℤ) • eℤ p.1.1 - (4 : ℤ) • eℤ p.1.2) ∧
      Multiplicative.toAdd (phi (QuotientGroup.mk (rPlus p.1.1 p.1.2))) =
        classOf ((4 : ℤ) • eℤ p.1.1 + (4 : ℤ) • eℤ p.1.2)) ∧
    (∀ (c : C₀) (i : Fin 24), IsShort (QuotientGroup.mk (rOdd c i)) ∧
      oddMin i ((c : C) : Fin 24 → ZMod 2) ∈ minVecs ∧
      Multiplicative.toAdd (phi (QuotientGroup.mk (rOdd c i))) =
        classOf (oddMin i ((c : C) : Fin 24 → ZMod 2))) ∧
    (∀ (d : OctadWord) (δ : Finset (Fin 24)), δ ⊆ octSupp d → Even δ.card →
      IsShort (QuotientGroup.mk (rOct d δ)) ∧
      (2 : ℤ) • liftℤ ((d : C) : Fin 24 → ZMod 2) - (4 : ℤ) • liftℤ (Octad.ind δ) ∈ minVecs ∧
      Multiplicative.toAdd (phi (QuotientGroup.mk (rOct d δ))) =
        classOf ((2 : ℤ) • liftℤ ((d : C) : Fin 24 → ZMod 2) - (4 : ℤ) • liftℤ (Octad.ind δ))) ∧
    (∀ p : LtPair, labelElt (.inl p) = rMinus p.1.1 p.1.2 ∧
      labelElt (.inr (.inl p)) = rPlus p.1.1 p.1.2) ∧
    (∀ q : C₀ × Fin 24, labelElt (.inr (.inr (.inl q))) = rOdd q.1 q.2) ∧
    (∀ o : OctIdx, labelElt (.inr (.inr (.inr o))) = rOctQ o.1 o.2) ∧
    (∀ l l' : ShortLabel,
      (QuotientGroup.mk (labelElt l) : Q ⧸ center Q) = QuotientGroup.mk (labelElt l') ↔ l = l') ∧
    (∀ c : Q ⧸ center Q, IsShort c ↔ ∃ l : ShortLabel, QuotientGroup.mk (labelElt l) = c) ∧
    (∀ (d d' : OctadWord) (δ δ' : Finset (Fin 24)), δ ⊆ octSupp d → Even δ.card →
      δ' ⊆ octSupp d' → Even δ'.card →
      ((QuotientGroup.mk (rOct d δ) : Q ⧸ center Q) = QuotientGroup.mk (rOct d' δ') ↔
        d = d' ∧ (δ' = δ ∨ δ' = octSupp d \ δ))) ∧
    Function.Bijective labelIdx ∧ (∀ l : ShortLabel, (labelIdx l).1 = coordOf (labelElt l)) ∧
    Fintype.card LtPair = 276 ∧ Fintype.card (C₀ × Fin 24) = 49152 ∧
    Fintype.card OctadWord = 759 ∧
    (∀ d : OctadWord, Fintype.card (Octad.EvenQuot (octSupp d)) = 64) ∧
    Fintype.card ShortLabel = 98280 ∧ Nat.card ShortIdx = 98280 ∧
    (∀ i : Fin 24, tbasis (.inl i) = (basisA s(i, i), 0, 0) ∧
      (basisA s(i, i) : Matrix (Fin 24) (Fin 24) ℚ) = Matrix.single i i 1) ∧
    (∀ p : LtPair, tbasis (.inr (.inl (p, 0))) = (basisA s(p.1.1, p.1.2), 0, 0) ∧
      (basisA s(p.1.1, p.1.2) : Matrix (Fin 24) (Fin 24) ℚ) =
        Matrix.single p.1.1 p.1.2 1 + Matrix.single p.1.2 p.1.1 1 ∧
      tbasis (.inr (.inl (p, 1))) =
        (0, Xlift (rMinus p.1.1 p.1.2) - Xlift (rPlus p.1.1 p.1.2), 0) ∧
      tbasis (.inr (.inl (p, 2))) =
        (0, Xlift (rMinus p.1.1 p.1.2) + Xlift (rPlus p.1.1 p.1.2), 0)) ∧
    (∀ (c : C₀) (i : Fin 24), tbasis (.inr (.inr (.inl (c, i, 0)))) = (0, Xlift (rOdd c i), 0) ∧
      tbasis (.inr (.inr (.inl (c, i, 1)))) =
        (0, 0, sgn (((c : C) : Fin 24 → ZMod 2) i) • tensor (Spin.E 1 c) (Pi.single i 1)) ∧
      tbasis (.inr (.inr (.inl (c, i, 2)))) =
        (0, 0, sgn (P ((c : C) : Fin 24 → ZMod 2)) • tensor (Spin.E 0 c) (Pi.single i 1))) ∧
    (∀ o : OctIdx, tbasis (.inr (.inr (.inr o))) = (0, Xlift (rOctQ o.1 o.2), 0)) ∧
    (∀ (d : OctadWord) (δ : Finset (Fin 24)), δ ⊆ octSupp d → Even δ.card →
      tbasis (.inr (.inr (.inr ⟨d, Octad.cls (octSupp d) δ⟩))) = (0, Xlift (rOct d δ), 0)) ∧
    (∀ x y : TIdx, bform (tbasis x) (tbasis y) = if x = y then tnorm x else 0) ∧
    (∀ q : LtPair × Fin 3, tnorm (.inr (.inl q)) = 2) ∧ (∀ i : Fin 24, tnorm (.inl i) = 1) ∧
    (∀ q : (C₀ × Fin 24 × Fin 3) ⊕ OctIdx, tnorm (.inr (.inr q)) = 1) ∧
    Fintype.card TIdx = 196884 ∧
    Submodule.span dyadic (Set.range tbasis) = BR := by
  refine ⟨fun i j => ⟨rfl, rfl, rfl⟩, fun c i => ⟨rfl, rfl⟩, fun d δ => ⟨rfl, rfl⟩,
    fun d δ hδ he => ⟨rOct_compl d.2 hδ he, rOctQ_cls hδ he⟩, fun p => ?_, fun c i => ?_,
    fun d δ hδ he => ?_, fun p => ⟨rfl, rfl⟩, fun q => rfl, fun o => rfl, mk_labelElt_eq_iff,
    fun c => ⟨exists_labelElt_of_isShort, fun ⟨l, hl⟩ => (congrArg IsShort hl).mp
      (isShort_labelElt l)⟩, fun d d' δ δ' hδ he hδ' he' => mk_rOct_eq_iff hδ he hδ' he',
    labelIdx_bijective, fun l => rfl, card_ltPair, ?_, card_octadWord, card_evenQuot_octSupp,
    card_shortLabel, card_shortIdx, fun i => ⟨tbasis_diag i, ?_⟩, fun p => ⟨tbasis_pair_zero p, ?_,
      tbasis_pair_one p, tbasis_pair_two p⟩,
    fun c i => ⟨tbasis_odd_zero c i, tbasis_odd_one c i, tbasis_odd_two c i⟩, tbasis_oct,
    fun d δ hδ he => tbasis_oct_cls hδ he, bform_tbasis, fun q => rfl, fun i => rfl,
    fun q => by rcases q with q | q <;> rfl, card_tIdx, span_tbasis⟩
  · exact ⟨isShort_labelElt (.inl p), isShort_labelElt (.inr (.inl p)), vMinus_mem p.2,
      vPlus_mem p.2, (toAdd_phi_mk _).trans (phi0_coordOf_rMinus p.2),
      (toAdd_phi_mk _).trans (phi0_coordOf_rPlus p.2)⟩
  · exact ⟨isShort_labelElt (.inr (.inr (.inl (c, i)))), oddMin_mem c i,
      (toAdd_phi_mk _).trans (phi0_coordOf_rOdd c i)⟩
  · refine ⟨?_, vOct_mem (d : C).2 d.2 hδ he, (toAdd_phi_mk _).trans (phi0_coordOf_rOct d.2 hδ he)⟩
    rw [← rOctQ_cls hδ he]
    exact isShort_labelElt (.inr (.inr (.inr ⟨d, Octad.cls (octSupp d) δ⟩)))
  · rw [Fintype.card_prod, card_C₀, Fintype.card_fin]
  · rw [coe_basisA, ite_eq_left rfl]
  · rw [coe_basisA, ite_eq_right p.2.ne]

end CFSG.Monster.Griess
