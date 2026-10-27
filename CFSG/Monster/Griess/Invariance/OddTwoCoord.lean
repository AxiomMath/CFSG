module

public import CFSG.Monster.Griess.Invariance.XYZ

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice Matrix XYZInv

namespace OddTwoInv

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

noncomputable abbrev pairVec (p : LtPair) (h : Fin 3) : SpaceB := tbasis (.inr (.inl (p, h)))

@[expose] noncomputable def pairSpan : Submodule ℚ SpaceB :=
  Submodule.span ℚ (Set.range fun q : LtPair × Fin 3 => pairVec q.1 q.2)

@[expose] noncomputable def oddTwoS (c : C₀) (p : LtPair) : ℚ :=
  sgn (((c : C) : Fin 24 → ZMod 2) p.1.1 + ((c : C) : Fin 24 → ZMod 2) p.1.2)

@[expose] noncomputable def oddTwoF (c : C₀) (i j : Fin 24) (p : LtPair) : ℚ :=
  if i = j then oddTwoS c p * (1 / 4 - if i = p.1.1 ∨ i = p.1.2 then 1 else 0) else 0

@[expose] def oddTwoG (i j : Fin 24) (p : LtPair) : ℚ :=
  if i ≠ j ∧ ((i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1)) then 1 else 0

@[expose] noncomputable def oddTwoEntry (d : Fin 3) (c : C₀) (i j : Fin 24) (p : LtPair) : ℚ :=
  ![oddTwoF c i j p, oddTwoG i j p, oddTwoS c p * oddTwoG i j p] d

theorem pairVec_mem_pairSpan (p : LtPair) (h : Fin 3) : pairVec p h ∈ pairSpan :=
  Submodule.subset_span ⟨(p, h), rfl⟩

theorem pairVec_zero (p : LtPair) : pairVec p 0 = inA (basisA s(p.1.1, p.1.2)) :=
  tbasis_pair_zero p

theorem pairVec_one (p : LtPair) :
    pairVec p 1 = inX (Xlift (rMinus p.1.1 p.1.2)) - inX (Xlift (rPlus p.1.1 p.1.2)) := by
  rw [Prod.mk_sub_mk, Prod.mk_sub_mk, sub_zero, sub_zero]
  exact tbasis_pair_one p

theorem pairVec_two (p : LtPair) :
    pairVec p 2 = inX (Xlift (rMinus p.1.1 p.1.2)) + inX (Xlift (rPlus p.1.1 p.1.2)) := by
  rw [Prod.mk_add_mk, Prod.mk_add_mk, add_zero, add_zero]
  exact tbasis_pair_two p

theorem isShortCoord_rMinus (p : LtPair) : IsShortCoord (coordOf (rMinus p.1.1 p.1.2)) :=
  isShortCoord_labelElt (.inl p)

theorem isShortCoord_rPlus (p : LtPair) : IsShortCoord (coordOf (rPlus p.1.1 p.1.2)) :=
  isShortCoord_labelElt (.inr (.inl p))

noncomputable abbrev idxOdd (c : C₀) (i : Fin 24) : ShortIdx :=
  ⟨coordOf (rOdd c i), isShortCoord_rOdd c i⟩

noncomputable abbrev idxMinus (p : LtPair) : ShortIdx :=
  ⟨coordOf (rMinus p.1.1 p.1.2), isShortCoord_rMinus p⟩

noncomputable abbrev idxPlus (p : LtPair) : ShortIdx :=
  ⟨coordOf (rPlus p.1.1 p.1.2), isShortCoord_rPlus p⟩

theorem Xlift_rOdd_eq (c : C₀) (i : Fin 24) : Xlift (rOdd c i) = Pi.single (idxOdd c i) 1 := by
  rw [Xlift_eq (isShortCoord_rOdd c i), centralCoord_rOdd, sgn_zero, one_smul]

theorem Xlift_rMinus_eq (p : LtPair) : Xlift (rMinus p.1.1 p.1.2) = Pi.single (idxMinus p) 1 := by
  rw [Xlift_eq (isShortCoord_rMinus p), centralCoord_rMinus, sgn_zero, one_smul]

theorem Xlift_rPlus_eq (p : LtPair) : Xlift (rPlus p.1.1 p.1.2) = Pi.single (idxPlus p) 1 := by
  rw [Xlift_eq (isShortCoord_rPlus p), centralCoord_rPlus, sgn_zero, one_smul]

theorem idxOdd_eq_iff (c c' : C₀) (i j : Fin 24) : idxOdd c' j = idxOdd c i ↔ c' = c ∧ j = i := by
  constructor
  · intro h
    have h' : labelIdx (.inr (.inr (.inl (c', j)))) = labelIdx (.inr (.inr (.inl (c, i)))) := h
    have := labelIdx_injective h'
    simpa only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] using this
  · rintro ⟨rfl, rfl⟩
    rfl

theorem T_single_single_inA (d d' : ShortIdx) (A : symMat) :
    T (inX (Pi.single d 1)) (inX (Pi.single d' 1)) (inA A) =
      if d' = d then qf d A / 8 else 0 := by
  rw [T_XXA]
  have h := sum_single_mul_single d d' 1 1 (fun e => qf e A)
  simp only [one_smul, one_mul] at h
  rw [h]
  split_ifs <;> ring

theorem T_single_single_single (d₁ d₂ d₃ : ShortIdx) :
    T (inX (Pi.single d₁ 1)) (inX (Pi.single d₂ 1)) (inX (Pi.single d₃ 1)) = tau d₁ d₂ d₃ := by
  have h := sum3_single d₁ d₂ d₃ 1 1 1
  simp only [one_smul, one_mul] at h
  rw [T_XXX, h]

theorem qf_basisA_pair (x : ShortIdx) {k l : Fin 24} (hkl : k ≠ l) :
    qf x (basisA s(k, l)) = 2 * (uQ x k * uQ x l) := by
  rw [coe_basisA, ite_eq_right hkl, qf, add_mulVec, single_mulVec_eq, single_mulVec_eq,
    dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_single, dotProduct_single,
    smul_eq_mul, smul_eq_mul]
  ring

theorem uQ_mul_uQ_of_classOf {x : ShortIdx} {v : Fin 24 → ℤ} (hv : v ∈ minVecs)
    (hcl : phi0 x.1 = classOf v) (i j : Fin 24) : uQ x i * uQ x j = (v i : ℚ) * (v j : ℚ) := by
  show ((uvec x i : ℤ) : ℚ) * ((uvec x j : ℤ) : ℚ) = _
  rcases (classOf_eq_iff (uvec_mem x) hv).1 ((classOf_uvec x).trans hcl) with h | h
  · rw [h]
  · rw [h, Pi.neg_apply, Pi.neg_apply, Int.cast_neg, Int.cast_neg, neg_mul_neg]

theorem cast_vMinus (k l m : Fin 24) :
    ((vMinus k l m : ℤ) : ℚ) = 4 * (if m = k then 1 else 0) - 4 * (if m = l then 1 else 0) := by
  simp only [vMinus, eℤ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> norm_num

theorem cast_vPlus (k l m : Fin 24) :
    ((vPlus k l m : ℤ) : ℚ) = 4 * (if m = k then 1 else 0) + 4 * (if m = l then 1 else 0) := by
  simp only [vPlus, eℤ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> norm_num

theorem uQ_idxMinus_mul (p : LtPair) (i j : Fin 24) :
    uQ ⟨coordOf (rMinus p.1.1 p.1.2), isShortCoord_rMinus p⟩ i *
        uQ ⟨coordOf (rMinus p.1.1 p.1.2), isShortCoord_rMinus p⟩ j =
      (4 * (if i = p.1.1 then 1 else 0) - 4 * (if i = p.1.2 then 1 else 0)) *
        (4 * (if j = p.1.1 then 1 else 0) - 4 * (if j = p.1.2 then 1 else 0)) := by
  rw [uQ_mul_uQ_of_classOf (x := idxMinus p) (vMinus_mem p.2) (phi0_coordOf_rMinus p.2),
    cast_vMinus, cast_vMinus]

theorem uQ_idxPlus_mul (p : LtPair) (i j : Fin 24) :
    uQ ⟨coordOf (rPlus p.1.1 p.1.2), isShortCoord_rPlus p⟩ i *
        uQ ⟨coordOf (rPlus p.1.1 p.1.2), isShortCoord_rPlus p⟩ j =
      (4 * (if i = p.1.1 then 1 else 0) + 4 * (if i = p.1.2 then 1 else 0)) *
        (4 * (if j = p.1.1 then 1 else 0) + 4 * (if j = p.1.2 then 1 else 0)) := by
  rw [uQ_mul_uQ_of_classOf (x := idxPlus p) (vPlus_mem p.2) (phi0_coordOf_rPlus p.2),
    cast_vPlus, cast_vPlus]

theorem uQ_idxOdd_mul (c : C₀) (i j k : Fin 24) :
    uQ (idxOdd c i) j * uQ (idxOdd c i) k =
      sgn (((c : C) : Fin 24 → ZMod 2) j) * (1 - 4 * if j = i then 1 else 0) *
        (sgn (((c : C) : Fin 24 → ZMod 2) k) * (1 - 4 * if k = i then 1 else 0)) :=
  uQ_rOdd_mul c i _ j k

theorem hammingNorm_le_four (i j k l : Fin 24) :
    hammingNorm ((Pi.single i 1 + Pi.single j 1 - (Pi.single k 1 + Pi.single l 1) :
      Fin 24 → ZMod 2)) ≤ 4 := by
  refine (Finset.card_le_card (t := {i, j, k, l}) fun m hm => ?_).trans Finset.card_le_four
  rw [Finset.mem_filter] at hm
  by_contra hne
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
  obtain ⟨h1, h2, h3, h4⟩ := hne
  apply hm.2
  simp [h1, h2, h3, h4]

theorem mk_single_add_mk_single_eq_deltaPair_iff {i j k l : Fin 24} (hkl : k ≠ l) :
    (Submodule.Quotient.mk (Pi.single i 1) + Submodule.Quotient.mk (Pi.single j 1) : Cocode) =
      deltaPair k l ↔ (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  constructor
  · intro h
    rw [deltaPair, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at h
    have h0 : (Pi.single i 1 + Pi.single j 1 - (Pi.single k 1 + Pi.single l 1) :
        Fin 24 → ZMod 2) = 0 := by
      by_contra hne
      have := eight_le_wt h hne
      have := hammingNorm_le_four i j k l
      omega
    have h1 : (Pi.single i 1 + Pi.single j 1 : Fin 24 → ZMod 2) = Pi.single k 1 + Pi.single l 1 :=
      sub_eq_zero.1 h0
    have hk := congrFun h1 k
    have hl := congrFun h1 l
    rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hkl, add_zero] at hk
    rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hkl),
      zero_add] at hl
    rw [Pi.single_apply, Pi.single_apply] at hk hl
    split_ifs at hk hl <;> first
      | exact absurd hk (by decide) | exact absurd hl (by decide)
      | (subst_vars
         first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩ | exact absurd rfl hkl)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [deltaPair, Submodule.Quotient.mk_add]
    · rw [deltaPair, Submodule.Quotient.mk_add, add_comm]

theorem pair_deltaPair (a : C) (k l : Fin 24) :
    pair a (deltaPair k l) = (a : Fin 24 → ZMod 2) k + (a : Fin 24 → ZMod 2) l := by
  rw [deltaPair, pair_mk, dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one]

theorem pair_ΩC_deltaPair (k l : Fin 24) : pair ΩC (deltaPair k l) = 0 := by
  rw [pair_deltaPair, coe_ΩC]
  rfl

theorem coe_rMinus (k l : Fin 24) :
    ((rMinus k l : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = qmatR ℚ 0 0 (deltaPair k l) := by
  rw [coe_Q_eq, centralCoord_rMinus, coordOf_rMinus]

theorem coe_rPlus (k l : Fin 24) :
    ((rPlus k l : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      qmatR ℚ 0 ΩC (thetaD ΩC + deltaPair k l) := by
  rw [coe_Q_eq, centralCoord_rPlus, coordOf_rPlus]

theorem E_vecMul_rMinus (η : ZMod 2) (c : C₀) (k l : Fin 24) :
    Spin.E η c ᵥ* ((rMinus k l : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      sgn (((c : C) : Fin 24 → ZMod 2) k + ((c : C) : Fin 24 → ZMod 2) l) • Spin.E η c := by
  rw [coe_rMinus, Spin.E, single_vecMul_qmatR, sgnR_rat]
  have hp : qPerm 0 (deltaPair k l) (η, c) = (η, c) := by
    rw [qPerm, pair_ΩC_deltaPair, add_zero, shift_zero]
  have hs : qSign 0 0 (deltaPair k l) (η, c) =
      ((c : C) : Fin 24 → ZMod 2) k + ((c : C) : Fin 24 → ZMod 2) l := by
    rw [qSign, map_zero, mul_zero, zero_add, zero_add, shift_zero, pair_deltaPair]
  rw [hp, hs]

theorem E_vecMul_rPlus (η : ZMod 2) (c : C₀) (k l : Fin 24) :
    Spin.E η c ᵥ* ((rPlus k l : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      sgn (η + (((c : C) : Fin 24 → ZMod 2) k + ((c : C) : Fin 24 → ZMod 2) l)) • Spin.E η c := by
  rw [coe_rPlus, Spin.E, single_vecMul_qmatR, sgnR_rat]
  have hp : qPerm ΩC (thetaD ΩC + deltaPair k l) (η, c) = (η, c) := by
    rw [qPerm, thetaD_ΩC, zero_add, pair_ΩC_deltaPair, add_zero, shift_ΩC]
  have hs : qSign 0 ΩC (thetaD ΩC + deltaPair k l) (η, c) =
      η + (((c : C) : Fin 24 → ZMod 2) k + ((c : C) : Fin 24 → ZMod 2) l) := by
    rw [qSign, μ₀_ΩC, mul_one, zero_add, thetaD_ΩC, zero_add, shift_ΩC, pair_deltaPair]
  rw [hp, hs]

theorem trace_basisA_pair {k l : Fin 24} (hkl : k ≠ l) :
    trace (basisA s(k, l) : Matrix (Fin 24) (Fin 24) ℚ) = 0 := by
  rw [coe_basisA, ite_eq_right hkl, trace_add, trace_single_eq_of_ne _ _ _ hkl,
    trace_single_eq_of_ne _ _ _ (Ne.symm hkl), add_zero]

theorem single_dotProduct_basisA_mulVec (i j k l : Fin 24) :
    Pi.single i 1 ⬝ᵥ ((basisA s(k, l) : Matrix (Fin 24) (Fin 24) ℚ) *ᵥ Pi.single j 1) =
      if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then 1 else 0 := by
  rw [single_dotProduct, one_mul, mulVec_single_one, col_apply, basisA_apply]
  exact if_congr Sym2.eq_iff rfl rfl

theorem T_tensor_tensor_basisA (η : ZMod 2) (σ σ' : ℚ) (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    T (inW (tensor (σ • Spin.E η c) (Pi.single i 1))) (inW (tensor (σ' • Spin.E η c')
      (Pi.single j 1))) (inA (basisA s(p.1.1, p.1.2))) =
      σ * σ' * (if c = c' then 1 else 0) *
        (if (i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1) then 1 else 0) := by
  rw [T_tensor_tensor_A, trace_basisA_pair p.2.ne, single_dotProduct_basisA_mulVec,
    smul_dotProduct, dotProduct_smul, E_dotProduct_E, smul_eq_mul, smul_eq_mul]
  by_cases h : c = c'
  · subst h
    simp only [ite_true]
    ring
  · rw [ite_eq_right (fun h' => h (congrArg Prod.snd h')), ite_eq_right h]
    ring

theorem T_tensor_tensor_Xlift_of_vecMul (η : ZMod 2) (σ σ' : ℚ) (c c' : C₀) (i j : Fin 24)
    {r : Q} (hr : IsShortCoord (coordOf r)) (t : ZMod 2)
    (hM : Spin.E η c ᵥ* ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = sgn t • Spin.E η c) :
    T (inW (tensor (σ • Spin.E η c) (Pi.single i 1))) (inW (tensor (σ' • Spin.E η c')
      (Pi.single j 1))) (inX (Xlift r)) =
      σ * σ' * (if c = c' then sgn t else 0) * ((if i = j then 1 else 0) -
        uQ ⟨coordOf r, hr⟩ i * uQ ⟨coordOf r, hr⟩ j / 4) / 8 := by
  rw [T_tensor_tensor_Xlift _ _ _ _ hr, smul_vecMul, hM, smul_smul, smul_dotProduct,
    dotProduct_smul, E_dotProduct_E, single_dotProduct_single, single_dotProduct,
    single_dotProduct, one_mul, one_mul, smul_eq_mul, smul_eq_mul]
  by_cases h : c = c'
  · subst h
    simp only [ite_true]
    ring
  · rw [ite_eq_right (fun h' => h (congrArg Prod.snd h')), ite_eq_right h]
    ring

theorem thetaD_aOdd (c : C₀) (i : Fin 24) : thetaD (aOdd c i) = thetaD c :=
  thetaD_unique fun u => by rw [pair_thetaD, θ_aOdd]

theorem coordOf_rOdd_add (c c' : C₀) (i j : Fin 24) :
    coordOf (rOdd c i) + coordOf (rOdd c' j) =
      (aOdd c i + aOdd c' j, thetaD c + thetaD c' +
        (Submodule.Quotient.mk (Pi.single i 1) + Submodule.Quotient.mk (Pi.single j 1))) := by
  rw [coordOf_rOdd, coordOf_rOdd, Prod.mk_add_mk, thetaD_aOdd, thetaD_aOdd]
  exact congrArg (Prod.mk _) (by abel)

theorem aOdd_add_aOdd (c c' : C₀) (i j : Fin 24) :
    aOdd c i + aOdd c' j = ((c + c' : C₀) : C) + (mOdd c i + mOdd c' j) • ΩC := by
  rw [aOdd, aOdd, Submodule.coe_add, add_smul]
  abel

theorem coe_add_smul_ΩC_eq_smul_ΩC_iff (x : C₀) (t m : ZMod 2) :
    (x : C) + t • ΩC = m • ΩC ↔ x = 0 ∧ t = m := by
  constructor
  · intro h
    have h1 := congrArg π₀ h
    have h2 := congrArg μ₀ h
    simp only [map_add, map_smul, π₀_coe, π₀_ΩC, smul_zero, add_zero, μ₀_coe, μ₀_ΩC, smul_eq_mul,
      mul_one, zero_add] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rw [Submodule.coe_zero, zero_add]

theorem aOdd_add_aOdd_eq_smul_iff (c c' : C₀) (i j : Fin 24) (m : ZMod 2) :
    aOdd c i + aOdd c' j = m • ΩC ↔
      c = c' ∧ ((c : C) : Fin 24 → ZMod 2) i + ((c : C) : Fin 24 → ZMod 2) j = m := by
  rw [aOdd_add_aOdd, coe_add_smul_ΩC_eq_smul_ΩC_iff, add_eq_zero_iff' (M := C₀)]
  constructor
  · rintro ⟨h0, h⟩
    obtain rfl := h0.symm
    refine ⟨rfl, ?_⟩
    rw [← h, mOdd, mOdd]
    linear_combination (-P ((c : C) : Fin 24 → ZMod 2)) * two_eq_zero'
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← h, mOdd, mOdd]
    linear_combination (P ((c : C) : Fin 24 → ZMod 2)) * two_eq_zero'

theorem zero_eq_aOdd_add_aOdd_iff (c c' : C₀) (i j : Fin 24) :
    (0 : C) = aOdd c i + aOdd c' j ↔
      c = c' ∧ ((c : C) : Fin 24 → ZMod 2) i + ((c : C) : Fin 24 → ZMod 2) j = 0 := by
  have h := aOdd_add_aOdd_eq_smul_iff c c' i j 0
  rw [zero_smul] at h
  exact eq_comm.trans h

theorem ΩC_eq_aOdd_add_aOdd_iff (c c' : C₀) (i j : Fin 24) :
    ΩC = aOdd c i + aOdd c' j ↔
      c = c' ∧ ((c : C) : Fin 24 → ZMod 2) i + ((c : C) : Fin 24 → ZMod 2) j = 1 := by
  have h := aOdd_add_aOdd_eq_smul_iff c c' i j 1
  rw [one_smul] at h
  exact eq_comm.trans h

theorem coordOf_rMinus_eq_iff (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    coordOf (rMinus p.1.1 p.1.2) = coordOf (rOdd c i) + coordOf (rOdd c' j) ↔
      c = c' ∧ ((c : C) : Fin 24 → ZMod 2) i + ((c : C) : Fin 24 → ZMod 2) j = 0 ∧
        ((i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1)) := by
  rw [coordOf_rMinus, coordOf_rOdd_add, Prod.mk.injEq, zero_eq_aOdd_add_aOdd_iff]
  constructor
  · rintro ⟨⟨rfl, h1⟩, h2⟩
    rw [add_self_cocode, zero_add] at h2
    exact ⟨rfl, h1, (mk_single_add_mk_single_eq_deltaPair_iff p.2.ne).1 h2.symm⟩
  · rintro ⟨rfl, h1, h2⟩
    refine ⟨⟨rfl, h1⟩, ?_⟩
    rw [add_self_cocode, zero_add]
    exact ((mk_single_add_mk_single_eq_deltaPair_iff p.2.ne).2 h2).symm

theorem coordOf_rPlus_eq_iff (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    coordOf (rPlus p.1.1 p.1.2) = coordOf (rOdd c i) + coordOf (rOdd c' j) ↔
      c = c' ∧ ((c : C) : Fin 24 → ZMod 2) i + ((c : C) : Fin 24 → ZMod 2) j = 1 ∧
        ((i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1)) := by
  rw [coordOf_rPlus, coordOf_rOdd_add, Prod.mk.injEq, ΩC_eq_aOdd_add_aOdd_iff, thetaD_ΩC,
    zero_add]
  constructor
  · rintro ⟨⟨rfl, h1⟩, h2⟩
    rw [add_self_cocode, zero_add] at h2
    exact ⟨rfl, h1, (mk_single_add_mk_single_eq_deltaPair_iff p.2.ne).1 h2.symm⟩
  · rintro ⟨rfl, h1, h2⟩
    refine ⟨⟨rfl, h1⟩, ?_⟩
    rw [add_self_cocode, zero_add]
    exact ((mk_single_add_mk_single_eq_deltaPair_iff p.2.ne).2 h2).symm

theorem pair_aOdd_thetaD_aOdd (c : C₀) (i j : Fin 24) :
    pair (aOdd c j) (thetaD (aOdd c i) + Submodule.Quotient.mk (Pi.single i 1)) =
      ((c : C) : Fin 24 → ZMod 2) i + ((c : C) : Fin 24 → ZMod 2) j := by
  rw [pair_add_right, pair_thetaD, pair_mk_single, θ_aOdd, aOdd, θ_add_right, θ_smul_right,
    θ_ΩC_right, mul_zero, add_zero, θ_self, mOdd]
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, coe_ΩC,
    smul_eq_mul, Ω, mul_one]
  linear_combination (P ((c : C) : Fin 24 → ZMod 2)) * two_eq_zero'

theorem tau_idxOdd_idxOdd_idxMinus (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    tau (idxOdd c i) (idxOdd c' j) (idxMinus p) =
      if c = c' ∧ ((c : C) : Fin 24 → ZMod 2) i + ((c : C) : Fin 24 → ZMod 2) j = 0 ∧
        ((i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1)) then 1 else 0 := by
  unfold tau
  by_cases h : c = c' ∧ ((c : C) : Fin 24 → ZMod 2) i + ((c : C) : Fin 24 → ZMod 2) j = 0 ∧
      ((i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1))
  · have h' : (idxMinus p).1 = (idxOdd c i).1 + (idxOdd c' j).1 :=
      (coordOf_rMinus_eq_iff c c' i j p).2 h
    rw [ite_eq_left h', ite_eq_left h]
    obtain ⟨rfl, h1, -⟩ := h
    show sgn (pair (coordOf (rOdd c j)).1 (coordOf (rOdd c i)).2) = 1
    rw [coordOf_rOdd, coordOf_rOdd]
    dsimp only
    rw [pair_aOdd_thetaD_aOdd, h1, sgn_zero]
  · rw [ite_eq_right (fun h' => h ((coordOf_rMinus_eq_iff c c' i j p).1 h')), ite_eq_right h]

theorem tau_idxOdd_idxOdd_idxPlus (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    tau (idxOdd c i) (idxOdd c' j) (idxPlus p) =
      if c = c' ∧ ((c : C) : Fin 24 → ZMod 2) i + ((c : C) : Fin 24 → ZMod 2) j = 1 ∧
        ((i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1)) then -1 else 0 := by
  unfold tau
  by_cases h : c = c' ∧ ((c : C) : Fin 24 → ZMod 2) i + ((c : C) : Fin 24 → ZMod 2) j = 1 ∧
      ((i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1))
  · have h' : (idxPlus p).1 = (idxOdd c i).1 + (idxOdd c' j).1 :=
      (coordOf_rPlus_eq_iff c c' i j p).2 h
    rw [ite_eq_left h', ite_eq_left h]
    obtain ⟨rfl, h1, -⟩ := h
    show sgn (pair (coordOf (rOdd c j)).1 (coordOf (rOdd c i)).2) = -1
    rw [coordOf_rOdd, coordOf_rOdd]
    dsimp only
    rw [pair_aOdd_thetaD_aOdd, h1]
    rfl
  · rw [ite_eq_right (fun h' => h ((coordOf_rPlus_eq_iff c c' i j p).1 h')), ite_eq_right h]

theorem ne_of_pair {i j : Fin 24} {p : LtPair}
    (h : (i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1)) : i ≠ j := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact p.2.ne
  · exact p.2.ne'

theorem oddTwoG_eq (i j : Fin 24) (p : LtPair) :
    oddTwoG i j p = if (i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1) then 1 else 0 := by
  unfold oddTwoG
  by_cases h : (i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1)
  · rw [ite_eq_left ⟨ne_of_pair h, h⟩, ite_eq_left h]
  · rw [ite_eq_right (fun h' => h h'.2), ite_eq_right h]

theorem add_eq_of_pair (c : C₀) {i j : Fin 24} {p : LtPair}
    (h : (i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1)) :
    ((c : C) : Fin 24 → ZMod 2) i + ((c : C) : Fin 24 → ZMod 2) j =
      ((c : C) : Fin 24 → ZMod 2) p.1.1 + ((c : C) : Fin 24 → ZMod 2) p.1.2 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact add_comm _ _

theorem bracket_add {k l : Fin 24} (hkl : k ≠ l) (i j : Fin 24) :
    ((if i = j then 1 else 0) -
        (4 * (if i = k then 1 else 0) - 4 * (if i = l then 1 else 0)) *
          (4 * (if j = k then 1 else 0) - 4 * (if j = l then 1 else 0)) / 4 +
      ((if i = j then 1 else 0) -
        (4 * (if i = k then 1 else 0) + 4 * (if i = l then 1 else 0)) *
          (4 * (if j = k then 1 else 0) + 4 * (if j = l then 1 else 0)) / 4)) / 8 =
      if i = j then 1 / 4 - (if i = k ∨ i = l then 1 else 0) else (0 : ℚ) := by
  split_ifs <;> subst_vars <;> simp_all <;> norm_num

theorem bracket_sub {k l : Fin 24} (hkl : k ≠ l) (i j : Fin 24) :
    ((if i = j then 1 else 0) -
        (4 * (if i = k then 1 else 0) - 4 * (if i = l then 1 else 0)) *
          (4 * (if j = k then 1 else 0) - 4 * (if j = l then 1 else 0)) / 4 -
      ((if i = j then 1 else 0) -
        (4 * (if i = k then 1 else 0) + 4 * (if i = l then 1 else 0)) *
          (4 * (if j = k then 1 else 0) + 4 * (if j = l then 1 else 0)) / 4)) / 8 =
      if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then 1 else (0 : ℚ) := by
  split_ifs <;> subst_vars <;> simp_all <;> norm_num

private theorem sgn_one' : sgn 1 = -1 := rfl

theorem oddTwoF_eq (c : C₀) (i j : Fin 24) (p : LtPair) :
    oddTwoF c i j p = oddTwoS c p * (if i = j then 1 / 4 - (if i = p.1.1 ∨ i = p.1.2 then 1 else 0)
      else 0) := by
  unfold oddTwoF
  split_ifs <;> ring

private theorem uua_arith (x y : ZMod 2) {k l : Fin 24} (hkl : k ≠ l) (i : Fin 24) :
    2 * (sgn x * (1 - 4 * (if k = i then 1 else 0)) *
      (sgn y * (1 - 4 * (if l = i then 1 else 0)))) / 8 =
        sgn (x + y) * (1 / 4 - if i = k ∨ i = l then 1 else 0) := by
  rw [sgn_add]
  simp only [@eq_comm _ k i, @eq_comm _ l i]
  split_ifs <;> subst_vars <;> first | ring1 | simp_all

private theorem arith_V (a x BM BP Y : ℚ) (key : (BM + BP) / 8 = Y) (ha : a * Y = Y) :
    a * x * BM / 8 - a * (-1 * x) * BP / 8 = x * Y := by
  linear_combination (a * x) * key + x * ha

private theorem arith_VC (a x BM BP Y : ℚ) (key : (BM - BP) / 8 = Y) (h : a * x * Y = Y) :
    a * x * BM / 8 + a * (-1 * x) * BP / 8 = Y := by
  linear_combination (a * x) * key + h

private theorem arith_WB (a x BM BP Y : ℚ) (key : (BM - BP) / 8 = Y) (ha : a = 1) :
    a * x * BM / 8 - a * x * BP / 8 = x * Y := by
  subst ha
  linear_combination x * key

private theorem arith_WC (a x BM BP Y : ℚ) (key : (BM + BP) / 8 = Y) (ha : a = 1) :
    a * x * BM / 8 + a * x * BP / 8 = x * Y := by
  subst ha
  linear_combination x * key

theorem E_zero_vecMul_rPlus (c : C₀) (k l : Fin 24) :
    Spin.E 0 c ᵥ* ((rPlus k l : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      sgn (((c : C) : Fin 24 → ZMod 2) k + ((c : C) : Fin 24 → ZMod 2) l) • Spin.E 0 c := by
  rw [E_vecMul_rPlus, zero_add]

theorem T_odd2_UUA (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    T (oddVec c i 0) (oddVec c' j 0) (pairVec p 0) = if c = c' then oddTwoF c i j p else 0 := by
  rw [oddVec_zero, oddVec_zero, pairVec_zero, Xlift_rOdd_eq, Xlift_rOdd_eq, T_single_single_inA]
  by_cases h : c' = c ∧ j = i
  · obtain ⟨rfl, rfl⟩ := h
    rw [ite_eq_left rfl, ite_eq_left rfl, oddTwoF, ite_eq_left rfl, qf_basisA_pair _ p.2.ne,
      uQ_idxOdd_mul, oddTwoS]
    exact uua_arith _ _ p.2.ne _
  · rw [ite_eq_right (fun h' => h ((idxOdd_eq_iff c c' i j).1 h'))]
    by_cases hc : c = c'
    · subst hc
      have hij : i ≠ j := fun hij => h ⟨rfl, hij.symm⟩
      rw [ite_eq_left rfl, oddTwoF, ite_eq_right hij]
    · rw [ite_eq_right hc]

theorem T_odd2_UUB (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    T (oddVec c i 0) (oddVec c' j 0) (pairVec p 1) = if c = c' then oddTwoG i j p else 0 := by
  rw [oddVec_zero, oddVec_zero, pairVec_one, map_sub, Xlift_rOdd_eq, Xlift_rOdd_eq,
    Xlift_rMinus_eq, Xlift_rPlus_eq, T_single_single_single, T_single_single_single,
    tau_idxOdd_idxOdd_idxMinus, tau_idxOdd_idxOdd_idxPlus, oddTwoG_eq]
  by_cases hpr : (i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1)
  · rcases zmod2_cases (((c : C) : Fin 24 → ZMod 2) i + ((c : C) : Fin 24 → ZMod 2) j) with
      hS | hS <;> rw [hS] <;> split_ifs <;> simp_all
  · split_ifs <;> simp_all

theorem T_odd2_UUC (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    T (oddVec c i 0) (oddVec c' j 0) (pairVec p 2) =
      if c = c' then oddTwoS c p * oddTwoG i j p else 0 := by
  rw [oddVec_zero, oddVec_zero, pairVec_two, map_add, Xlift_rOdd_eq, Xlift_rOdd_eq,
    Xlift_rMinus_eq, Xlift_rPlus_eq, T_single_single_single, T_single_single_single,
    tau_idxOdd_idxOdd_idxMinus, tau_idxOdd_idxOdd_idxPlus, oddTwoG_eq, oddTwoS]
  by_cases hpr : (i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1)
  · rw [← add_eq_of_pair c hpr]
    rcases zmod2_cases (((c : C) : Fin 24 → ZMod 2) i + ((c : C) : Fin 24 → ZMod 2) j) with
      hS | hS <;> rw [hS] <;> split_ifs <;> simp_all [sgn_zero, sgn_one']
  · split_ifs <;> simp_all

theorem T_odd2_VVA (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    T (oddVec c i 1) (oddVec c' j 1) (pairVec p 0) =
      if c = c' then oddTwoS c p * oddTwoG i j p else 0 := by
  rw [oddVec_one, oddVec_one, pairVec_zero, T_tensor_tensor_basisA, oddTwoG_eq, oddTwoS]
  by_cases hc : c = c'
  · subst hc
    rw [ite_eq_left rfl, ite_eq_left rfl]
    split_ifs with h
    · rw [← sgn_add, add_eq_of_pair c h]
      ring
    · ring
  · rw [ite_eq_right hc, ite_eq_right hc]
    ring

theorem T_odd2_VVB (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    T (oddVec c i 1) (oddVec c' j 1) (pairVec p 1) = if c = c' then oddTwoF c i j p else 0 := by
  rw [oddVec_one, oddVec_one, pairVec_one, map_sub,
    T_tensor_tensor_Xlift_of_vecMul 1 _ _ c c' i j (isShortCoord_rMinus p) _
      (E_vecMul_rMinus 1 c _ _),
    T_tensor_tensor_Xlift_of_vecMul 1 _ _ c c' i j (isShortCoord_rPlus p) _
      (E_vecMul_rPlus 1 c _ _), uQ_idxMinus_mul, uQ_idxPlus_mul]
  by_cases hc : c = c'
  · subst hc
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, oddTwoF_eq, oddTwoS,
      sgn_add (1 : ZMod 2), sgn_one']
    refine arith_V _ _ _ _ _ (bracket_add p.2.ne i j) ?_
    by_cases h : i = j
    · subst h
      rw [sgn_mul_self, one_mul]
    · rw [ite_eq_right h, mul_zero]
  · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right hc]
    ring

theorem T_odd2_VVC (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    T (oddVec c i 1) (oddVec c' j 1) (pairVec p 2) = if c = c' then oddTwoG i j p else 0 := by
  rw [oddVec_one, oddVec_one, pairVec_two, map_add,
    T_tensor_tensor_Xlift_of_vecMul 1 _ _ c c' i j (isShortCoord_rMinus p) _
      (E_vecMul_rMinus 1 c _ _),
    T_tensor_tensor_Xlift_of_vecMul 1 _ _ c c' i j (isShortCoord_rPlus p) _
      (E_vecMul_rPlus 1 c _ _), uQ_idxMinus_mul, uQ_idxPlus_mul]
  by_cases hc : c = c'
  · subst hc
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, oddTwoG_eq, sgn_add (1 : ZMod 2),
      sgn_one']
    refine arith_VC _ _ _ _ _ (bracket_sub p.2.ne i j) ?_
    split_ifs with h
    · rw [← sgn_add, add_eq_of_pair c h, sgn_mul_self, one_mul]
    · rw [mul_zero]
  · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right hc]
    ring

theorem T_odd2_WWA (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    T (oddVec c i 2) (oddVec c' j 2) (pairVec p 0) = if c = c' then oddTwoG i j p else 0 := by
  rw [oddVec_two, oddVec_two, pairVec_zero, T_tensor_tensor_basisA, oddTwoG_eq]
  by_cases hc : c = c'
  · subst hc
    rw [ite_eq_left rfl, ite_eq_left rfl, sgn_mul_self]
    ring
  · rw [ite_eq_right hc, ite_eq_right hc]
    ring

theorem T_odd2_WWB (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    T (oddVec c i 2) (oddVec c' j 2) (pairVec p 1) =
      if c = c' then oddTwoS c p * oddTwoG i j p else 0 := by
  rw [oddVec_two, oddVec_two, pairVec_one, map_sub,
    T_tensor_tensor_Xlift_of_vecMul 0 _ _ c c' i j (isShortCoord_rMinus p) _
      (E_vecMul_rMinus 0 c _ _),
    T_tensor_tensor_Xlift_of_vecMul 0 _ _ c c' i j (isShortCoord_rPlus p) _
      (E_zero_vecMul_rPlus c _ _), uQ_idxMinus_mul, uQ_idxPlus_mul]
  by_cases hc : c = c'
  · subst hc
    rw [ite_eq_left rfl, ite_eq_left rfl, oddTwoG_eq, oddTwoS]
    exact arith_WB _ _ _ _ _ (bracket_sub p.2.ne i j) (sgn_mul_self _)
  · rw [ite_eq_right hc, ite_eq_right hc]
    ring

theorem T_odd2_WWC (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    T (oddVec c i 2) (oddVec c' j 2) (pairVec p 2) = if c = c' then oddTwoF c i j p else 0 := by
  rw [oddVec_two, oddVec_two, pairVec_two, map_add,
    T_tensor_tensor_Xlift_of_vecMul 0 _ _ c c' i j (isShortCoord_rMinus p) _
      (E_vecMul_rMinus 0 c _ _),
    T_tensor_tensor_Xlift_of_vecMul 0 _ _ c c' i j (isShortCoord_rPlus p) _
      (E_zero_vecMul_rPlus c _ _), uQ_idxMinus_mul, uQ_idxPlus_mul]
  by_cases hc : c = c'
  · subst hc
    rw [ite_eq_left rfl, ite_eq_left rfl, oddTwoF_eq, oddTwoS]
    exact arith_WC _ _ _ _ _ (bracket_add p.2.ne i j) (sgn_mul_self _)
  · rw [ite_eq_right hc, ite_eq_right hc]
    ring

theorem T_oddVec_pairVec (r h : Fin 3) (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    T (oddVec c i r) (oddVec c' j r) (pairVec p h) =
      if c = c' then oddTwoEntry (h - r) c i j p else 0 := by
  fin_cases r <;> fin_cases h
  · exact T_odd2_UUA c c' i j p
  · exact T_odd2_UUB c c' i j p
  · exact T_odd2_UUC c c' i j p
  · exact T_odd2_VVA c c' i j p
  · exact T_odd2_VVB c c' i j p
  · exact T_odd2_VVC c c' i j p
  · exact T_odd2_WWA c c' i j p
  · exact T_odd2_WWB c c' i j p
  · exact T_odd2_WWC c c' i j p

theorem tauB_pairVec (p : LtPair) (h : Fin 3) : tauB (pairVec p h) = pairVec p (h + 1) :=
  tauB_pair p h

theorem tauB_symm_pairVec (p : LtPair) (h : Fin 3) :
    tauB.symm (pairVec p h) = pairVec p (h - 1) := by
  rw [LinearEquiv.symm_apply_eq, tauB_pairVec, sub_add_cancel]

theorem tauB_symm_oddVec' (c : C₀) (i : Fin 24) (r : Fin 3) :
    tauB.symm (oddVec c i r) = oddVec c i (r - 1) := by
  rw [LinearEquiv.symm_apply_eq, tauB_oddVec, sub_add_cancel]

theorem T_tauB_oddVec_pairVec (r h : Fin 3) (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    T (tauB (oddVec c i r)) (tauB (oddVec c' j r)) (tauB (pairVec p h)) =
      T (oddVec c i r) (oddVec c' j r) (pairVec p h) := by
  rw [tauB_oddVec, tauB_oddVec, tauB_pairVec, T_oddVec_pairVec, T_oddVec_pairVec,
    add_sub_add_right_eq_sub]

theorem T_tauB_symm_oddVec_pairVec (r h : Fin 3) (c c' : C₀) (i j : Fin 24) (p : LtPair) :
    T (tauB.symm (oddVec c i r)) (tauB.symm (oddVec c' j r)) (tauB.symm (pairVec p h)) =
      T (oddVec c i r) (oddVec c' j r) (pairVec p h) := by
  rw [tauB_symm_oddVec', tauB_symm_oddVec', tauB_symm_pairVec, T_oddVec_pairVec, T_oddVec_pairVec,
    sub_sub_sub_cancel_right]

end OddTwoInv

open OddTwoInv

theorem triality_Griess_odd_two_coordinate_invariance :
    (∀ (r : Fin 3) {u v w : SpaceB}, u ∈ oddSpan r → v ∈ oddSpan r → w ∈ pairSpan →
      T (tauB u) (tauB v) (tauB w) = T u v w ∧
        T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w) ∧
    (∀ (r h : Fin 3) (c c' : C₀) (i j : Fin 24) (p : LtPair), c ≠ c' →
      T (oddVec c i r) (oddVec c' j r) (pairVec p h) = 0) ∧
    ∀ (c : C₀) (i j : Fin 24) (p : LtPair),
      T (oddVec c i 0) (oddVec c j 0) (pairVec p 0) = oddTwoF c i j p ∧
      T (oddVec c i 0) (oddVec c j 0) (pairVec p 1) = oddTwoG i j p ∧
      T (oddVec c i 0) (oddVec c j 0) (pairVec p 2) = oddTwoS c p * oddTwoG i j p ∧
      T (oddVec c i 1) (oddVec c j 1) (pairVec p 0) = oddTwoS c p * oddTwoG i j p ∧
      T (oddVec c i 1) (oddVec c j 1) (pairVec p 1) = oddTwoF c i j p ∧
      T (oddVec c i 1) (oddVec c j 1) (pairVec p 2) = oddTwoG i j p ∧
      T (oddVec c i 2) (oddVec c j 2) (pairVec p 0) = oddTwoG i j p ∧
      T (oddVec c i 2) (oddVec c j 2) (pairVec p 1) = oddTwoS c p * oddTwoG i j p ∧
      T (oddVec c i 2) (oddVec c j 2) (pairVec p 2) = oddTwoF c i j p := by
  refine ⟨fun r {u v w} hu hv hw => ⟨?_, ?_⟩, fun r h c c' i j p hc => ?_, fun c i j p => ?_⟩
  · have e : T (tauB u) (tauB v) (tauB w) = Tcomp₃ (tauB : SpaceB →ₗ[ℚ] SpaceB) u v w := by
      rw [Tcomp₃_apply]
      rfl
    rw [e]
    refine trilinear_eq_of_mem_span₃ ?_ hu hv hw
    rintro _ ⟨⟨c, i⟩, rfl⟩ _ ⟨⟨c', j⟩, rfl⟩ _ ⟨⟨p, h⟩, rfl⟩
    rw [Tcomp₃_apply]
    exact T_tauB_oddVec_pairVec r h c c' i j p
  · have e : T (tauB.symm u) (tauB.symm v) (tauB.symm w) =
        Tcomp₃ (tauB.symm : SpaceB →ₗ[ℚ] SpaceB) u v w := by
      rw [Tcomp₃_apply]
      rfl
    rw [e]
    refine trilinear_eq_of_mem_span₃ ?_ hu hv hw
    rintro _ ⟨⟨c, i⟩, rfl⟩ _ ⟨⟨c', j⟩, rfl⟩ _ ⟨⟨p, h⟩, rfl⟩
    rw [Tcomp₃_apply]
    exact T_tauB_symm_oddVec_pairVec r h c c' i j p
  · rw [T_oddVec_pairVec, ite_eq_right hc]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [T_oddVec_pairVec, ite_eq_left rfl] <;> rfl

end CFSG.Monster.Griess
