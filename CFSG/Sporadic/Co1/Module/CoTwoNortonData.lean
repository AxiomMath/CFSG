module

public import CFSG.Monster.GMS.CoTwoRep
public import CFSG.Sporadic.Co1.Module.CoTwoNorton
public import CFSG.Sporadic.Co1.Module.OddNative
public import CFSG.Sporadic.Co1.Module.Pairs
public import Certificates.Data.CFSGNative.Co1.CoTwoNorton
public import CFSG.Sporadic.Co1.Module.CoTwoNortonDataInputs
public import Certificates.Certificate10068
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import CFSG.Sporadic.Co1.Module.PairsCheck
public meta import Certificates.Data.CFSGNative.Co1.CoTwoNorton
public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Sporadic.Co1.Module.OddFacts
public import Certificates.Certificate10073Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1.Module.CoTwo

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1.CoTwoNative Matrix

@[expose] def repRows (l : ℕ) : Array ℕ := if l = 0 then r1Rows else r2Rows

theorem nortonCheck_ok : nortonCheck 22 genRows nortonCert = true :=
  Certificates.certificate10068.1

theorem repCheck_ok :
    repCheck (transposeRows 24 qRows) (transposeRows 24 f0Rows) r1Rows r2Rows
    wRows mt1 mt2 2 359217 = true :=
  Certificates.certificate10068.2.1

theorem y₀_inPts :
    Pairs.inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
    359217 = true :=
  Certificates.certificate10068.2.2

theorem toVecD_one_shiftLeft (d : ℕ) (i : Fin d) : toVecD d (1 <<< (i : ℕ)) = Pi.single i 1 := by
  funext j
  rw [toVecD_apply, Nat.one_shiftLeft, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : j = i
  · subst h; simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem rowsMatrix_addRowsD (d : ℕ) (X Y : Array ℕ) :
    rowsMatrix d (addRowsD d X Y) = rowsMatrix d X + rowsMatrix d Y := by
  ext i j
  rw [Matrix.add_apply, rowsMatrix_apply, rowsMatrix_apply, rowsMatrix_apply]
  unfold addRowsD
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_xor]
  rfl

theorem rowsMatrix_zeroRowsD (d : ℕ) : rowsMatrix d (zeroRowsD d) = 0 := by
  ext i j
  rw [rowsMatrix_apply]
  unfold zeroRowsD
  simp [toVecD_zero]

theorem rowsMatrix_wordRowsD (d : ℕ) (G : ℕ → Array ℕ) (w : List ℕ) :
    rowsMatrix d (wordRowsD d G w) = (w.map fun l => rowsMatrix d (G l)).prod := by
  have key : ∀ (w : List ℕ) (acc : Array ℕ),
      rowsMatrix d (w.foldl (fun acc l => mulRows d acc (G l)) acc) =
        rowsMatrix d acc * (w.map fun l => rowsMatrix d (G l)).prod := by
    intro w
    induction w with
    | nil => intro acc; simp
    | cons l w ih =>
      intro acc
      rw [List.foldl_cons, ih, rowsMatrix_mulRows, List.map_cons, List.prod_cons,
        Matrix.mul_assoc]
  rw [wordRowsD, key, rowsMatrix_idRows, Matrix.one_mul]

theorem rowsMatrix_polyRowsD (d : ℕ) (G : ℕ → Array ℕ) (theta : List (List ℕ)) :
    rowsMatrix d (polyRowsD d G theta) = polyMat (fun l => rowsMatrix d (G l)) theta := by
  have key : ∀ (theta : List (List ℕ)) (acc : Array ℕ),
      rowsMatrix d (theta.foldl (fun acc w => addRowsD d acc (wordRowsD d G w)) acc) =
        rowsMatrix d acc +
          (theta.map fun w => (w.map fun l => rowsMatrix d (G l)).prod).sum := by
    intro theta
    induction theta with
    | nil => intro acc; simp
    | cons w theta ih =>
      intro acc
      rw [List.foldl_cons, ih, rowsMatrix_addRowsD, rowsMatrix_wordRowsD, List.map_cons,
        List.sum_cons, add_assoc]
  rw [polyRowsD, key, rowsMatrix_zeroRowsD, zero_add]
  rfl

theorem rowsMatrix_diagRowsD (d : ℕ) {ℓ : ℕ} (hℓ : ℓ < d) :
    rowsMatrix d (diagRowsD d ℓ) = diagOne (⟨ℓ, hℓ⟩ : Fin d) := by
  ext i j
  rw [rowsMatrix_apply]
  unfold diagRowsD diagOne
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  by_cases hi : i.val = ℓ
  · have hi' : i = ⟨ℓ, hℓ⟩ := Fin.ext hi
    subst hi'
    simp [toVecD_zero, Matrix.diagonal_apply]
  · have hi' : i ≠ ⟨ℓ, hℓ⟩ := fun h => hi (congrArg Fin.val h)
    simp only [hi, ↓reduceIte, toVecD_one_shiftLeft, Matrix.diagonal_apply, hi']
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]

theorem toVecD_act_col (d : ℕ) (G : Array ℕ) (x : ℕ) :
    toVecD d (vecMulN d (transposeRows d G) x) = rowsMatrix d G *ᵥ toVecD d x :=
  (rowsMatrix_mulVec d G x).symm

theorem toVecD_act_row (d : ℕ) (G : Array ℕ) (x : ℕ) :
    toVecD d (vecMulN d G x) = (rowsMatrix d G)ᵀ *ᵥ toVecD d x := by
  rw [toVecD_vecMulN, Matrix.mulVec_transpose]

theorem spinCheck_sound {d : ℕ} {act : ℕ → ℕ → ℕ} {B : ℕ → Matrix (Fin d) (Fin d) (ZMod 2)}
    (hact : ∀ l x, toVecD d (act l x) = B l *ᵥ toVecD d x) {v0 : ℕ} {L par lab : Array ℕ}
    (h : spinCheck d act v0 L par lab = true) :
    IsSpin B (toVecD d v0) (fun k => toVecD d (L[k]?.getD 0)) (fun k => par[k]?.getD 0)
      (fun k => lab[k]?.getD 0) := by
  unfold spinCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨h0, hall⟩ := h
  refine ⟨by simp [h0], fun k hk hkd => ?_⟩
  rcases hall k hkd with h1 | ⟨h2, h3⟩
  · omega
  · refine ⟨h2, ?_⟩
    show toVecD d (L[k]?.getD 0) = B _ *ᵥ toVecD d (L[par[k]?.getD 0]?.getD 0)
    rw [h3, hact]

theorem colsMat_toVecD (d : ℕ) (L : Array ℕ) :
    colsMat (fun k => toVecD d (L[k]?.getD 0)) = rowsMatrix d (transposeRows d L) := by
  rw [rowsMatrix_transposeRows]
  ext i k
  rfl

theorem nortonCheck_sound {d : ℕ} {G : ℕ → Array ℕ} {C : NortonCert}
    (h : nortonCheck d G C = true) (U : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hU : IsInv (fun l => rowsMatrix d (G l)) U) : U = ⊥ ∨ U = ⊤ := by
  unfold nortonCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hPP⟩, hQQ⟩, hD⟩, hv⟩, hw⟩, hsV⟩, hVi⟩, hsW⟩, hWi⟩ := h
  have hmul : ∀ {X Y : Array ℕ}, mulRows d X Y = idRows d →
      rowsMatrix d X * rowsMatrix d Y = 1 := by
    intro X Y hXY
    have := congrArg (rowsMatrix d) hXY
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  have hPP' := hmul hPP
  have hQQ' := hmul hQQ
  have hD' : rowsMatrix d C.Q * polyMat (fun l => rowsMatrix d (G l)) C.theta * rowsMatrix d C.P =
      diagOne (⟨C.ell, hl⟩ : Fin d) := by
    have := congrArg (rowsMatrix d) hD
    rwa [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_polyRowsD,
      rowsMatrix_diagRowsD d hl] at this
  have hvv : toVecD d C.v = rowsMatrix d C.P *ᵥ Pi.single (⟨C.ell, hl⟩ : Fin d) 1 := by
    rw [hv, toVecD_act_col, ← toVecD_one_shiftLeft d ⟨C.ell, hl⟩]
  have hww : toVecD d C.w = rowsMatrix d C.Q (⟨C.ell, hl⟩ : Fin d) := by
    rw [hw]
    rfl
  have hsV' := spinCheck_sound (B := fun l => rowsMatrix d (G l))
    (fun l x => toVecD_act_col d (G l) x) hsV
  have hsW' := spinCheck_sound (B := fun l => (rowsMatrix d (G l))ᵀ)
    (fun l x => toVecD_act_row d (G l) x) hsW
  rw [hvv] at hsV'
  rw [hww] at hsW'
  have hVi' := hmul hVi
  have hWi' := hmul hWi
  rw [← colsMat_toVecD] at hVi' hWi'
  exact norton_criterion (fun l => rowsMatrix d (G l)) C.theta ⟨C.ell, hl⟩ hPP' hQQ' hD'
    hsV' hVi' hsW' hWi' U hU

structure RepParts : Prop where
  fix₁_v₂ : isFixedN (transposeRows 24 r1Rows) 2 = true
  fix₁_y₀ : isFixedN (transposeRows 24 r1Rows) 359217 = true
  fix₂_v₂ : isFixedN (transposeRows 24 r2Rows) 2 = true
  fix₂_y₀ : isFixedN (transposeRows 24 r2Rows) 359217 = true
  perp_v₂ : perpCheck 22 (transposeRows 24 f0Rows) wRows 2 = true
  perp_y₀ : perpCheck 22 (transposeRows 24 f0Rows) wRows 359217 = true
  lift₁ : liftCheck 22 24 r1Rows wRows mt1 = true
  lift₂ : liftCheck 22 24 r2Rows wRows mt2 = true
  w₀_lt : (wRows[0]?.getD 0) < 2 ^ 24
  moves₁ : isFixedN (transposeRows 24 r1Rows) (wRows[0]?.getD 0) = false
  bil_pair : bilN (transposeRows 24 f0Rows) (wRows[0]?.getD 0) (wRows[21]?.getD 0) = true
  q₀_sum : q0N (transposeRows 24 qRows) (2 ^^^ 359217) = true

theorem repCheck_parts : RepParts := by
  have h := repCheck_ok
  unfold repCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem y₀_mem :
    toVecD 24 359217 ∈ CFSG.Monster.GMS.co1Orbit 0 := by
  rw [Pairs.co1Orbit_zero]
  exact (Pairs.inO_iff 359217 (by norm_num)).1 y₀_inPts

theorem v₂_add_y₀_mem :
    v₂ + toVecD 24 359217 ∈ CFSG.Monster.GMS.co1Orbit 1 := by
  apply CFSG.Monster.GMS.Leech.mem_co1Orbit_one_of_q₀_eq_one
  rw [← toVecD_v₂, ← toVecD_xor, Odd.q₀_toVecD]
  simp only [repCheck_parts.q₀_sum, ↓reduceIte]

@[expose] def wVec (j : Fin 22) : Fin 24 → ZMod 2 := toVecD 24 (wRows[j.val]?.getD 0)

@[expose] def wMat : Matrix (Fin 24) (Fin 22) (ZMod 2) := Matrix.of fun i j => wVec j i

@[expose] noncomputable def wEmbed : (Fin 22 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  Matrix.mulVecLin wMat

theorem wEmbed_eq_sum (a : Fin 22 → ZMod 2) : wEmbed a = ∑ j, a j • wVec j := by
  funext i
  simp [wEmbed, wMat, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem wMat_mulVec_toVecD (c : ℕ) : wMat *ᵥ toVecD 22 c = toVecD 24 (vecMulN 22 wRows c) := by
  unfold vecMulN
  rw [foldl_xor_toVecD, toVecD_zero, zero_add]
  funext i
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, wMat, Matrix.of_apply, wVec]
  rw [← Fin.sum_univ_eq_sum_range (fun j =>
    (if c.testBit j = true then toVecD 24 (wRows[j]?.getD 0) else 0) i) 22]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toVecD_apply 22 c j]
  by_cases hc : c.testBit j = true <;> simp [hc]

theorem rowsMatrix_mul_wMat {R Mt : Array ℕ} (h : liftCheck 22 24 R wRows Mt = true) :
    rowsMatrix 24 R * wMat = wMat * (rowsMatrix 22 Mt)ᵀ := by
  ext i j
  have hj := (List.all_eq_true.1 h) j.val (List.mem_range.2 j.isLt)
  rw [beq_iff_eq] at hj
  have e1 : rowsMatrix 24 R *ᵥ wVec j =
      toVecD 24 (vecMulN 24 (transposeRows 24 R) (wRows[j.val]?.getD 0)) :=
    rowsMatrix_mulVec 24 R _
  have e2 : wMat *ᵥ toVecD 22 (Mt[j.val]?.getD 0) =
      toVecD 24 (vecMulN 22 wRows (Mt[j.val]?.getD 0)) := wMat_mulVec_toVecD _
  have e3 : (rowsMatrix 24 R * wMat) i j = (rowsMatrix 24 R *ᵥ wVec j) i := rfl
  have e4 : (wMat * (rowsMatrix 22 Mt)ᵀ) i j = (wMat *ᵥ toVecD 22 (Mt[j.val]?.getD 0)) i := rfl
  rw [e3, e4, e1, e2, hj]

theorem rowsMatrix_mulVec_wEmbed {R Mt : Array ℕ} (h : liftCheck 22 24 R wRows Mt = true)
    (a : Fin 22 → ZMod 2) :
    rowsMatrix 24 R *ᵥ wEmbed a = wEmbed ((rowsMatrix 22 Mt)ᵀ *ᵥ a) := by
  rw [wEmbed, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, rowsMatrix_mul_wMat h]

theorem repMat_wEmbed (l : ℕ) (a : Fin 22 → ZMod 2) :
    rowsMatrix 24 (repRows l) *ᵥ wEmbed a = wEmbed (rowsMatrix 22 (genRows l) *ᵥ a) := by
  by_cases hl : l = 0
  · simp only [repRows, genRows, hl, ↓reduceIte, rowsMatrix_transposeRows]
    exact rowsMatrix_mulVec_wEmbed repCheck_parts.lift₁ a
  · simp only [repRows, genRows, hl, ↓reduceIte, rowsMatrix_transposeRows]
    exact rowsMatrix_mulVec_wEmbed repCheck_parts.lift₂ a

theorem norton_irred
    (U : Submodule (ZMod 2) (Fin 22 → ZMod 2))
    (hU : IsInv (fun l => rowsMatrix 22 (genRows l)) U) : U = ⊥ ∨ U = ⊤ :=
  nortonCheck_sound nortonCheck_ok U hU

@[expose] noncomputable def perpMap : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun y i := bil₀ y (![v₂, toVecD 24 359217] i)
  map_add' u u' := by
    funext i
    exact CFSG.Monster.GMS.Leech.bil₀_add_left _ _ _
  map_smul' c w := by
    funext i
    simp [bil₀, smul_dotProduct]

theorem mem_ker_perpMap {y : Fin 24 → ZMod 2} :
    y ∈ LinearMap.ker perpMap ↔ bil₀ y v₂ = 0 ∧ bil₀ y (toVecD 24 359217) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i
    · exact h1
    · exact h2

theorem perpMap_surjective :
    Function.Surjective perpMap := by
  have hy0 : toVecD 24 359217 ≠ 0 := CFSG.Monster.GMS.Leech.ne_zero_of_mem_co1Orbit y₀_mem
  have hli : LinearIndependent (ZMod 2) ![v₂, toVecD 24 359217] :=
    CFSG.Monster.GMS.Leech.linearIndependent_pair_of_add_mem v₂_ne_zero hy0 v₂_add_y₀_mem
  intro ε
  obtain ⟨w, hw⟩ := CFSG.Monster.GMS.Leech.exists_bil₀_eq hli ε
  exact ⟨w, funext hw⟩

theorem finrank_ker_perpMap :
    Module.finrank (ZMod 2) (LinearMap.ker perpMap) = 22 := by
  have hrk := LinearMap.finrank_range_add_finrank_ker perpMap
  rw [LinearMap.range_eq_top.2 perpMap_surjective, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fin_fun] at hrk
  simp only [Fintype.card_fin] at hrk
  omega

theorem bil₀_wVec_v₂ (j : Fin 22) : bil₀ (wVec j) v₂ = 0 := by
  have h := (List.all_eq_true.1 repCheck_parts.perp_v₂) j.val (List.mem_range.2 j.isLt)
  simp only [Bool.not_eq_true'] at h
  unfold wVec
  rw [← toVecD_v₂, Odd.bil₀_toVecD]
  simp [h]

theorem bil₀_wVec_y₀
    (j : Fin 22) : bil₀ (wVec j) (toVecD 24 359217) = 0 := by
  have h := (List.all_eq_true.1 repCheck_parts.perp_y₀) j.val (List.mem_range.2 j.isLt)
  simp only [Bool.not_eq_true'] at h
  unfold wVec
  rw [Odd.bil₀_toVecD]
  simp [h]

theorem range_wEmbed_le :
    LinearMap.range wEmbed ≤ LinearMap.ker perpMap := by
  rintro _ ⟨a, rfl⟩
  rw [LinearMap.mem_ker, wEmbed_eq_sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, LinearMap.mem_ker.1 (mem_ker_perpMap.2 ⟨bil₀_wVec_v₂ j, bil₀_wVec_y₀ j⟩),
    smul_zero]

theorem wRows_zero : wRows[0]?.getD 0 = 1 := rfl

theorem wEmbed_injective :
    Function.Injective wEmbed := by
  rw [← LinearMap.ker_eq_bot]
  have hinv : IsInv (fun l => rowsMatrix 22 (genRows l)) (LinearMap.ker wEmbed) := by
    intro l x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← repMat_wEmbed, hx, Matrix.mulVec_zero]
  rcases norton_irred _ hinv with h | h
  · exact h
  · exfalso
    have h0 : wEmbed (Pi.single (⟨0, by norm_num⟩ : Fin 22) 1) = 0 := by
      rw [← LinearMap.mem_ker, h]
      trivial
    have h1 : wEmbed (Pi.single (⟨0, by norm_num⟩ : Fin 22) 1) = wVec ⟨0, by norm_num⟩ := by
      rw [wEmbed, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
      rfl
    have h2 := congrFun (h1.symm.trans h0) ⟨0, by norm_num⟩
    simp only [wVec, toVecD_apply, wRows_zero, Pi.zero_apply] at h2
    simp at h2

theorem eq_wEmbed_of_perp
    {y : Fin 24 → ZMod 2} (h1 : bil₀ y v₂ = 0)
    (h2 : bil₀ y (toVecD 24 359217) = 0) : ∃ a, wEmbed a = y := by
  have hrange : LinearMap.range wEmbed = LinearMap.ker perpMap := by
    refine Submodule.eq_of_le_of_finrank_eq range_wEmbed_le ?_
    rw [LinearMap.finrank_range_of_inj wEmbed_injective, finrank_ker_perpMap,
      Module.finrank_fin_fun]
  have : y ∈ LinearMap.range wEmbed := by
    rw [hrange, mem_ker_perpMap]
    exact ⟨h1, h2⟩
  exact this

theorem irred_matrix
    (Y : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (hperp : ∀ y ∈ Y, bil₀ y v₂ = 0 ∧ bil₀ y (toVecD 24 359217) = 0)
    (h1 : ∀ y ∈ Y, rowsMatrix 24 r1Rows *ᵥ y ∈ Y) (h2 : ∀ y ∈ Y, rowsMatrix 24 r2Rows *ᵥ y ∈ Y) :
    Y = ⊥ ∨ ∀ y : Fin 24 → ZMod 2, bil₀ y v₂ = 0 → bil₀ y (toVecD 24 359217) = 0 → y ∈ Y := by
  have hinv : IsInv (fun l => rowsMatrix 22 (genRows l)) (Y.comap wEmbed) := by
    intro l x hx
    rw [Submodule.mem_comap] at hx ⊢
    rw [← repMat_wEmbed]
    by_cases hl : l = 0
    · simp only [repRows, hl, ↓reduceIte]
      exact h1 _ hx
    · simp only [repRows, hl, ↓reduceIte]
      exact h2 _ hx
  rcases norton_irred _ hinv with hbot | htop
  · left
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨a, rfl⟩ := eq_wEmbed_of_perp (hperp y hy).1 (hperp y hy).2
    have ha : a ∈ Y.comap wEmbed := hy
    rw [hbot, Submodule.mem_bot] at ha
    rw [ha, map_zero]
    exact Submodule.zero_mem _
  · right
    intro y hy1 hy2
    obtain ⟨a, rfl⟩ := eq_wEmbed_of_perp hy1 hy2
    have ha : a ∈ Y.comap wEmbed := by
      rw [htop]
      trivial
    exact ha

theorem mclRepFacts_of
    {c₁ c₂ : NativeSporadic.Co1}
    (h₁ : Odd.mat c₁ = rowsMatrix 24 r1Rows) (h₂ : Odd.mat c₂ = rowsMatrix 24 r2Rows) :
    CFSG.Monster.GMS.McLRepFacts c₁ c₂ (toVecD 24 359217) where
  mem_y₀ := y₀_mem
  sum_mem := v₂_add_y₀_mem
  fix_c₁ := by
    show Odd.mat c₁ *ᵥ v₂ = v₂ ∧ Odd.mat c₁ *ᵥ toVecD 24 359217 = toVecD 24 359217
    rw [h₁, ← toVecD_v₂]
    exact ⟨(Odd.isFixedN_iff r1Rows (by norm_num)).1 repCheck_parts.fix₁_v₂,
      (Odd.isFixedN_iff r1Rows (by norm_num)).1 repCheck_parts.fix₁_y₀⟩
  fix_c₂ := by
    show Odd.mat c₂ *ᵥ v₂ = v₂ ∧ Odd.mat c₂ *ᵥ toVecD 24 359217 = toVecD 24 359217
    rw [h₂, ← toVecD_v₂]
    exact ⟨(Odd.isFixedN_iff r2Rows (by norm_num)).1 repCheck_parts.fix₂_v₂,
      (Odd.isFixedN_iff r2Rows (by norm_num)).1 repCheck_parts.fix₂_y₀⟩
  irred := fun Y hperp hc₁ hc₂ => irred_matrix Y hperp
    (fun y hy => by rw [← h₁]; exact hc₁ y hy) (fun y hy => by rw [← h₂]; exact hc₂ y hy)
  nontriv := by
    refine ⟨wVec ⟨0, by norm_num⟩, bil₀_wVec_v₂ _, bil₀_wVec_y₀ _, Or.inl ?_⟩
    show Odd.mat c₁ *ᵥ wVec ⟨0, by norm_num⟩ ≠ wVec ⟨0, by norm_num⟩
    rw [h₁]
    intro h
    have h' := (Odd.isFixedN_iff r1Rows repCheck_parts.w₀_lt).2 h
    rw [repCheck_parts.moves₁] at h'
    exact Bool.false_ne_true h'
  nondeg := by
    refine ⟨wVec ⟨0, by norm_num⟩, wVec ⟨21, by norm_num⟩, bil₀_wVec_v₂ _, bil₀_wVec_y₀ _,
      bil₀_wVec_v₂ _, bil₀_wVec_y₀ _, ?_⟩
    show bil₀ (toVecD 24 (wRows[0]?.getD 0)) (toVecD 24 (wRows[21]?.getD 0)) = 1
    rw [Odd.bil₀_toVecD]
    simp [repCheck_parts.bil_pair]

end CFSG.Sporadic.Co1.Module.CoTwo
