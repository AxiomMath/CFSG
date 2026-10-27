
module

public import CFSG.Sporadic.ON.ActionBase

public import CFSG.Sporadic.ON.Setup
public import CFSG.Sporadic.Th.OrbitSpec

public section

namespace CFSG.Sporadic.ON

open Native Matrix
open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm.Native

theorem smul_vec (g : J) (v : Vec) : g • v = mat g *ᵥ v := rfl

theorem orbit_parts :
    orb.keys.size = nPts ∧ orb.alpha.size = nPts ∧ orb.beta.size = nPts ∧
    ∀ i < nPts, canon154 orb.keys[i]! = true ∧ posF orb.keys[i]! = i ∧
      ap orb.alpha i < nPts ∧ orb.keys[ap orb.alpha i]! = mulVecT colsA orb.keys[i]! ∧
      ap orb.beta i < nPts ∧ orb.keys[ap orb.beta i]! = mulVecT colsB orb.keys[i]! := by
  have h := facts.orbit
  unfold CFSG.Sporadic.ON.Native.orbitOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_⟩
  have := parAll_eq_true h4 i hi
  simp only [CFSG.Sporadic.ON.Native.orbitCheckAt, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at this
  obtain ⟨⟨⟨⟨⟨h5, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := this
  exact ⟨h5, h6, h7, h8, h9, h10⟩

theorem keys_wf
    {i : ℕ} (hi : i < nPts) : orb.keys[i]!.toV.wf = true :=
  wf_of_canon154 (orbit_parts.2.2.2 i hi).1

theorem P_injective : ∀ i < nPts, ∀ j < nPts, P i = P j → i = j := by
  intro i hi j hj h
  have hi' := orbit_parts.2.2.2 i hi
  have hj' := orbit_parts.2.2.2 j hj
  have e := vecOf_inj hi'.1 hj'.1 h
  rw [← hi'.2.1, ← hj'.2.1, e]

theorem ga_smul_P :
    ∀ i < nPts, ap orb.alpha i < nPts ∧ ga • P i = P (ap orb.alpha i) := by
  intro i hi
  obtain ⟨hc, -, hlt, he, -, -⟩ := orbit_parts.2.2.2 i hi
  refine ⟨hlt, ?_⟩
  rw [smul_vec, mat_ga, ← toMat_rowsA, P, P, he]
  unfold colsA
  exact (vecOf_mulVecT rowsA (wf_of_canon154 hc)).symm

theorem gb_smul_P :
    ∀ i < nPts, ap orb.beta i < nPts ∧ gb • P i = P (ap orb.beta i) := by
  intro i hi
  obtain ⟨hc, -, -, -, hlt, he⟩ := orbit_parts.2.2.2 i hi
  refine ⟨hlt, ?_⟩
  rw [smul_vec, mat_gb, ← toMat_rowsB, P, P, he]
  unfold colsB
  exact (vecOf_mulVecT rowsB (wf_of_canon154 hc)).symm

theorem smul_mem_ptSet (g : J) : ∀ v ∈ ptSet, g • v ∈ ptSet := by
  refine smul_mem_of_closure closure_gab ((Set.finite_Iio nPts).image _) ?_ ?_ g
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨_, (ga_smul_P i hi).1, (ga_smul_P i hi).2.symm⟩
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨_, (gb_smul_P i hi).1, (gb_smul_P i hi).2.symm⟩

@[expose] noncomputable def ptSub : SubMulAction J Vec where
  carrier := ptSet
  smul_mem' g _ hv := smul_mem_ptSet g _ hv

@[expose] noncomputable def ptEquiv : Fin nPts ≃ ptSub :=
  Equiv.ofBijective (fun i => ⟨P i, ⟨i, i.isLt, rfl⟩⟩)
    ⟨fun i j h => Fin.ext (P_injective i i.isLt j j.isLt (congrArg Subtype.val h)), by
      rintro ⟨v, ⟨i, hi, rfl⟩⟩
      exact ⟨⟨i, hi⟩, rfl⟩⟩

theorem ptEquiv_apply (i : Fin nPts) : (ptEquiv i : Vec) = P i := rfl

noncomputable instance idxAction :
    MulAction J (Fin nPts) := ptEquiv.mulAction J

theorem smul_def
    (g : J) (i : Fin nPts) : g • i = ptEquiv.symm (g • ptEquiv i) := rfl

theorem ptEquiv_smul
    (g : J) (i : Fin nPts) : ptEquiv (g • i) = g • ptEquiv i := by
  rw [smul_def, Equiv.apply_symm_apply]

theorem P_smul
    (g : J) (i : Fin nPts) : P (g • i).val = g • P i.val := by
  have := congrArg Subtype.val (ptEquiv_smul g i)
  rwa [ptEquiv_apply, SubMulAction.val_smul, ptEquiv_apply] at this

theorem idx_eq_iff
    {g : J} {i j : ℕ} (hi : i < nPts) (hj : j < nPts) :
    idx nPts g i = j ↔ g • P i = P j := by
  rw [idx_of_lt g hi]
  constructor
  · intro h
    rw [← P_smul g ⟨i, hi⟩, h]
  · intro h
    apply P_injective _ (g • (⟨i, hi⟩ : Fin nPts)).isLt _ hj
    rw [P_smul g ⟨i, hi⟩]
    exact h

theorem rep_ga : Rep nPts orb.alpha ga := by
  intro i hi
  symm
  exact (idx_eq_iff hi (ga_smul_P i hi).1).2 (ga_smul_P i hi).2

theorem rep_gb : Rep nPts orb.beta gb := by
  intro i hi
  symm
  exact (idx_eq_iff hi (gb_smul_P i hi).1).2 (gb_smul_P i hi).2

theorem neg_parts :
    ∀ i < nPts, ap negT i < nPts ∧ orb.keys[ap negT i]! = orb.keys[i]!.neg := by
  have h := facts.neg
  unfold negOK at h
  intro i hi
  have := (allIn_eq_true.1 h) i (Nat.zero_le _) hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact this

theorem P_neg {i : ℕ} (hi : i < nPts) : P (ap negT i) = -P i := by
  rw [P, (neg_parts i hi).2, vecOf_neg (keys_wf hi)]

theorem rep_neg {g : J} (hg : mat g = -1) : Rep nPts negT g := by
  intro i hi
  symm
  apply (idx_eq_iff hi (neg_parts i hi).1).2
  rw [smul_vec, hg, P_neg hi]
  exact (Matrix.neg_mulVec (P i) 1).trans (congrArg Neg.neg (Matrix.one_mulVec (P i)))

theorem basis_parts :
    chainQ.size = 154 ∧ (∀ t < chainQ.size, chainQ[t]! < nPts) ∧
    basisX.size = 154 ∧ (∀ x ∈ basisX, x.wf = true) ∧ mulW 154 basisX basisR = idW 154 := by
  have h := facts.basis
  unfold basisChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun t ht => ?_, h3, fun x hx => ?_, h5⟩
  · rw [getElem!_pos chainQ t ht]; simpa using h2 t ht
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
    exact h4 i hi

theorem chainQ_size : chainQ.size = 154 := basis_parts.1

theorem chainQ_lt
    {t : ℕ} (ht : t < chainQ.size) : chainQ[t]! < nPts := basis_parts.2.1 t ht

theorem basisR_size : basisR.size = 154 := by
  unfold basisR basisRows; rw [Array.size_map, chainQ_size]

theorem basisR_getElem
    {t : ℕ} (ht : t < 154) : basisR[t]! = orb.keys[chainQ[t]!]! := by
  have ht' : t < chainQ.size := by rw [chainQ_size]; exact ht
  unfold basisR basisRows
  rw [getElem!_pos _ t (by rw [Array.size_map]; exact ht'), Array.getElem_map,
    getElem!_pos chainQ t ht']

theorem rowsWF_basisR : RowsWF (toVM basisR) := by
  intro t
  rw [toVM_getElem!]
  by_cases ht : t < 154
  · rw [basisR_getElem ht]
    exact keys_wf (chainQ_lt (by rw [chainQ_size]; exact ht))
  · rw [getElem!_neg basisR t (by rw [basisR_size]; exact ht), W.toV_default]
    exact V.wf_zero

theorem rowsWF_basisX : RowsWF (toVM basisX) := by
  intro t
  rw [toVM_getElem!]
  by_cases ht : t < basisX.size
  · rw [getElem!_pos basisX t ht]
    exact W.wf_spec (basis_parts.2.2.2.1 _ (Array.getElem_mem ht))
  · rw [getElem!_neg basisX t ht, W.toV_default]
    exact V.wf_zero

theorem Xmat_mul_Umat : Xmat * Umat = 1 := by
  have e := congrArg (fun Y => toMat 154 (toVM Y)) basis_parts.2.2.2.2
  rwa [toVM_mulW, toVM_idW (by norm_num), toMat_idM,
    toMat_mul (by rw [toVM_size]; exact basis_parts.2.2.1) rowsWF_basisX rowsWF_basisR] at e

theorem Umat_row (t : Fin 154) : Umat t = P chainQ[t.val]! := by
  funext j
  show toMat 154 (toVM basisR) t j = vecOf orb.keys[chainQ[t.val]!]! j
  rw [toMat_apply, toVM_getElem!, basisR_getElem t.isLt]
  rfl

theorem sep
    (g : J) (hg : ∀ t < chainQ.size, idx nPts g chainQ[t]! = chainQ[t]!) : g = 1 := by
  apply mat_injective
  rw [mat_one, ← one_smul (ZMod 3) (1 : Matrix (Fin 154) (Fin 154) (ZMod 3))]
  apply eq_smul_one_of_rows Xmat_mul_Umat
  intro t
  have ht : t.val < chainQ.size := by rw [chainQ_size]; exact t.isLt
  rw [Umat_row, one_smul, ← smul_vec]
  exact (idx_eq_iff (chainQ_lt ht) (chainQ_lt ht)).1 (hg t.val ht)

instance faithful : FaithfulSMul J (Fin nPts) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := by
    apply sep
    intro t ht
    rw [idx_of_lt _ (chainQ_lt ht), mul_smul, hgh, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

end CFSG.Sporadic.ON
