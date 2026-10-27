module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.Weyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.SmithRootFree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

local notation "spMat " g =>
  (((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem mem_range_leviSp_of_blocks {x : StatedSp 2 K}
    (hx : ∀ i j : Fin 2,
      (spMat x) (Sum.inl i) (Sum.inr j) = 0 ∧ (spMat x) (Sum.inr i) (Sum.inl j) = 0) :
    x ∈ (leviSp : GL (Fin 2) K →* StatedSp 2 K).range := by
  let M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := spMat x
  let A : Matrix (Fin 2) (Fin 2) K := M.submatrix Sum.inl Sum.inl
  let D : Matrix (Fin 2) (Fin 2) K := M.submatrix Sum.inr Sum.inr
  have hblocks : M = Matrix.fromBlocks A 0 0 D := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · simp [M, A, D]
    · simp [M, A, D, (hx a b).1]
    · simp [M, A, D, (hx a b).2]
    · simp [M, A, D]
  have hsp : Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M =
      Matrix.fromBlocks 0 1 (-1) 0 := mem_statedSp_iff.mp x.2
  rw [hblocks] at hsp
  have hcomp : Matrix.fromBlocks 0 (Aᵀ * D) (-(Dᵀ * A)) 0 =
      Matrix.fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) K) (-1) 0 := by
    rw [← hsp]
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_inj] at hcomp
  have hAD : Aᵀ * D = 1 := hcomp.2.1
  have hDA : Dᵀ * A = 1 := neg_injective (by simpa using hcomp.2.2.1)
  have hdet : Matrix.det A ≠ 0 := by
    have h1 : Matrix.det (Dᵀ * A) = 1 := by rw [hDA]; simp
    rw [Matrix.det_mul, Matrix.det_transpose] at h1
    intro h0
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  let u : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet
  have hu : (u : Matrix (Fin 2) (Fin 2) K) = A := by simp [u]
  have hinv : ((u⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Dᵀ := by
    rw [Matrix.GeneralLinearGroup.coe_inv, hu]
    exact Matrix.inv_eq_left_inv hDA
  refine ⟨u, ?_⟩
  apply statedSp_ext
  rw [coe_leviSp, hu, hinv, Matrix.transpose_transpose]
  exact hblocks.symm

theorem leviSp_scalar_eq_torusHom (c : Kˣ) :
    leviSp (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = torusHom (fun _ : Fin 2 => c) := by
  apply statedSp_ext
  rw [coe_leviSp, coe_torusHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← map_inv, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_transpose, Matrix.fromBlocks_diagonal]

theorem utriElt_eq_sl2Up (s : K) : CFSG.CGT.Timmesfeld75.utriElt s = sl2Up K s := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.CGT.Timmesfeld75.utriElt, sl2Up]

theorem ltriElt_eq_sl2Low (s : K) : CFSG.CGT.Timmesfeld75.ltriElt s = sl2Low K s := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem rho_torusElt_eq_torusHom (hij : (0 : Fin 2) ≠ 1) (a : Kˣ) :
    rho 0 1 hij (CFSG.CGT.Timmesfeld75.torusElt a) =
      torusHom (fun i : Fin 2 => if i = 0 then a else a⁻¹) := by
  have hpair : ∀ M : Matrix (Fin 2) (Fin 2) K, pairMat (0 : Fin 2) 1 M = M := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pairMat]
  have hdiag : (CFSG.CGT.Timmesfeld75.torusElt a : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then (a : K) else (a⁻¹ : K)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.CGT.Timmesfeld75.torusElt_apply_00,
        CFSG.CGT.Timmesfeld75.torusElt_apply_01, CFSG.CGT.Timmesfeld75.torusElt_apply_10,
        CFSG.CGT.Timmesfeld75.torusElt_apply_11]
  have hinv : (CFSG.CGT.Timmesfeld75.torusElt a)⁻¹ =
      CFSG.CGT.Timmesfeld75.torusElt a⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← CFSG.CGT.Timmesfeld75.torusElt_mul, mul_inv_cancel,
      CFSG.CGT.Timmesfeld75.torusElt_one]
  have hdiag' : (CFSG.CGT.Timmesfeld75.torusElt a⁻¹ : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then (a⁻¹ : K) else (a : K)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.CGT.Timmesfeld75.torusElt_apply_00,
        CFSG.CGT.Timmesfeld75.torusElt_apply_01, CFSG.CGT.Timmesfeld75.torusElt_apply_10,
        CFSG.CGT.Timmesfeld75.torusElt_apply_11]
  apply statedSp_ext
  rw [coe_rho', coe_torusHom, hpair, hinv, hpair, hdiag, hdiag', Matrix.diagonal_transpose,
    Matrix.fromBlocks_diagonal]
  congr 1
  funext y
  rcases y with y | y <;> fin_cases y <;> simp

theorem isLinePerm_rho_of_zero_diagonal [CharP K 2] (hij : (0 : Fin 2) ≠ 1)
    {g : Matrix.SpecialLinearGroup (Fin 2) K} (h00 : g 0 0 = 0) (h11 : g 1 1 = 0) :
    IsLinePerm (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS.planeSwap)
      (((rho 0 1 hij g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  have hb : g 0 1 ≠ 0 := by
    intro h0
    have hd := g.2
    rw [Matrix.det_fin_two, h00, h11, h0] at hd
    simp at hd
  have hc : g 1 0 ≠ 0 := by
    intro h0
    have hd := g.2
    rw [Matrix.det_fin_two, h00, h11, h0] at hd
    simp at hd
  have hpair : ∀ M : Matrix (Fin 2) (Fin 2) K, pairMat (0 : Fin 2) 1 M = M := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pairMat]
  have hginv : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![g 1 1, -g 0 1; -g 1 0, g 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  intro x y
  rw [coe_rho', hpair, hpair, hginv]
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [Matrix.fromBlocks, Matrix.transpose_apply, h00, h11, hb, hc,
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS.planeSwap] <;> decide


theorem torus_le_comap_rho (hij : (0 : Fin 2) ≠ 1) {X : Subgroup (StatedSp 2 K)}
    (hT : torus 2 K ≤ X) : CFSG.CGT.Timmesfeld75.torus K ≤ X.comap (rho 0 1 hij) := by
  intro g hg
  rw [Subgroup.mem_comap]
  obtain ⟨a, rfl⟩ := CFSG.CGT.Timmesfeld75.eq_torusElt_of_mem_torus hg
  rw [rho_torusElt_eq_torusHom]
  exact hT (torusHom_mem_torus _)

theorem comap_rho_inf_utri_eq_bot (hij : (0 : Fin 2) ≠ 1) {X : Subgroup (StatedSp 2 K)}
    (hX : IsRootFree X) :
    X.comap (rho 0 1 hij) ⊓ CFSG.CGT.Timmesfeld75.utri K = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgN, hgU⟩ := hg
  rw [Subgroup.mem_comap] at hgN
  set s : K := g 0 1 with hs
  have hg_eq : g = CFSG.CGT.Timmesfeld75.utriElt s := by
    rw [CFSG.CGT.Timmesfeld75.eq_utriElt_of_mem_utri hgU, ← hs]
  have hroot : pairRootElt (fun h => hij (Sum.inl_injective h)) s ∈ X := by
    have h : rho 0 1 hij (CFSG.CGT.Timmesfeld75.utriElt s) ∈ X := by
      rwa [hg_eq] at hgN
    rw [utriElt_eq_sl2Up, ← pairRootElt_short hij s] at h
    exact h
  have hs0 : s = 0 := hX (Sum.inl 0) (Sum.inl 1)
    (fun h => hij (Sum.inl_injective h)) s hroot
  rw [hg_eq, hs0, CFSG.CGT.Timmesfeld75.utriElt_zero]

theorem comap_rho_inf_ltri_eq_bot (hij : (0 : Fin 2) ≠ 1) {X : Subgroup (StatedSp 2 K)}
    (hX : IsRootFree X) :
    X.comap (rho 0 1 hij) ⊓ CFSG.CGT.Timmesfeld75.ltri K = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgN, hgL⟩ := hg
  rw [Subgroup.mem_comap] at hgN
  set s : K := g 1 0 with hs
  have hg_eq : g = CFSG.CGT.Timmesfeld75.ltriElt s := by
    rw [CFSG.CGT.Timmesfeld75.eq_ltriElt_of_mem_ltri hgL, ← hs]
  have hroot : pairRootElt (fun h => hij (Sum.inl_injective h).symm) s ∈ X := by
    have h : rho 0 1 hij (CFSG.CGT.Timmesfeld75.ltriElt s) ∈ X := by
      rwa [hg_eq] at hgN
    rw [ltriElt_eq_sl2Low, ← pairRootElt_short' hij s] at h
    exact h
  have hs0 : s = 0 := hX (Sum.inl 1) (Sum.inl 0)
    (fun h => hij (Sum.inl_injective h).symm) s hroot
  have hltri0 : CFSG.CGT.Timmesfeld75.ltriElt (0 : K) = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CFSG.CGT.Timmesfeld75.ltriElt]
  rw [hg_eq, hs0, hltri0]

theorem rho_mem_normalizer_torus_of_mem_torus (hij : (0 : Fin 2) ≠ 1)
    {g : Matrix.SpecialLinearGroup (Fin 2) K} (hg : g ∈ CFSG.CGT.Timmesfeld75.torus K) :
    rho 0 1 hij g ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) := by
  obtain ⟨a, ha⟩ := CFSG.CGT.Timmesfeld75.eq_torusElt_of_mem_torus hg
  have hrho : rho 0 1 hij g = torusHom (fun i : Fin 2 => if i = 0 then a else a⁻¹) := by
    rw [ha, rho_torusElt_eq_torusHom]
  exact mem_normalizer_torus_of_isLinePerm (by rw [hrho]; exact isLinePerm_torusHom _)

theorem mem_normalizer_torus_of_mem_range_leviSp [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X)
    {x : StatedSp 2 K} (hx : x ∈ X) (hxL : x ∈ (leviSp : GL (Fin 2) K →* StatedSp 2 K).range) :
    x ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) := by
  obtain ⟨A, rfl⟩ := hxL
  have hdetA : Matrix.det (A : Matrix (Fin 2) (Fin 2) K) ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero A
  obtain ⟨c, hc2⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
    (Matrix.det (A : Matrix (Fin 2) (Fin 2) K))
  have hc : c ≠ 0 := by
    intro hc0
    apply hdetA
    rw [hc2, hc0, mul_zero]
  let cu : Kˣ := Units.mk0 c hc
  let C : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) cu
  have hC : (C : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal (fun _ => c) := by
    simp [C, cu]
  have hCinv : ((C⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal (fun _ => c⁻¹) := by
    rw [Matrix.GeneralLinearGroup.coe_inv, hC]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    have hfun : (fun _ : Fin 2 => c⁻¹ * c) = fun _ => (1 : K) := by
      funext i
      exact inv_mul_cancel₀ hc
    rw [hfun, Matrix.diagonal_one]
  have hleviC : leviSp C = torusHom (fun _ : Fin 2 => cu) :=
    leviSp_scalar_eq_torusHom cu
  have hCmem : leviSp C ∈ X := by
    rw [hleviC]
    exact hT (torusHom_mem_torus _)
  have hdetA₀ : Matrix.det (c⁻¹ • (A : Matrix (Fin 2) (Fin 2) K)) = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hc2, pow_two]
    calc (c⁻¹ * c⁻¹) * (c * c) = (c⁻¹ * c) * (c⁻¹ * c) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hc]; simp
  let A₀ : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨c⁻¹ • (A : Matrix (Fin 2) (Fin 2) K), hdetA₀⟩
  let hij : (0 : Fin 2) ≠ 1 := by decide
  let y : StatedSp 2 K := rho 0 1 hij A₀
  have hpair : ((pairGL hij A₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      c⁻¹ • (A : Matrix (Fin 2) (Fin 2) K) := by
    rw [coe_pairGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pairMat, A₀]
  have hAeq : A = C * pairGL hij A₀ := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, hC, hpair, ← Matrix.smul_eq_diagonal_mul,
      smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hx_split : leviSp A = leviSp C * y := by
    change leviSp A = leviSp C * rho 0 1 hij A₀
    rw [hAeq, map_mul]
    rfl
  have hy : y ∈ X := by
    have h1 : (leviSp C)⁻¹ * leviSp A ∈ X := X.mul_mem (X.inv_mem hCmem) hx
    rw [hx_split] at h1
    simpa only [inv_mul_cancel_left] using h1
  have hA₀N : A₀ ∈ X.comap (rho 0 1 hij) := by
    rw [Subgroup.mem_comap]
    exact hy
  have h4 : 4 ≤ Nat.card K := by omega
  have hTN := torus_le_comap_rho hij hT
  have hUN := comap_rho_inf_utri_eq_bot hij hX
  have hLN := comap_rho_inf_ltri_eq_bot hij hX
  have hA₀norm := le_normalizer_torus_of_inf_eq_bot h4 hTN hUN hLN hA₀N
  have hyNorm : y ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) := by
    rcases CFSG.RankThree.GF2n.Smith81.SL2Torus.mem_torus_or_antidiagonal_of_mem_normalizer
      h4 hA₀norm with hdiag | hanti
    · exact rho_mem_normalizer_torus_of_mem_torus hij hdiag
    · exact mem_normalizer_torus_of_isLinePerm
        (isLinePerm_rho_of_zero_diagonal hij hanti.1 hanti.2)
  have hCn : leviSp C ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) :=
    mem_normalizer_torus_of_isLinePerm (by rw [hleviC]; exact isLinePerm_torusHom _)
  have hxnm : leviSp C * y ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) :=
    (Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K))).mul_mem hCn hyNorm
  rw [hx_split]
  exact hxnm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
