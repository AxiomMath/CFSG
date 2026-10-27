module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.Adapters.LieModelSmallOrders
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open scoped commutatorElement

private theorem k328r5s_model (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 2) :
    ∃ (L : Type) (_ : Field L) (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) (ω : L),
      Nat.card L = 4 ∧ ℓ ω = rhoOmega F ∧
      ∀ g : Matrix (Fin 2) (Fin 2) F, rhoOmega F * g = g * rhoOmega F → ∃ a : L, ℓ a = g := by
  have hsq : ∀ r : F, r ^ 2 = r := fun r => by
    have := FiniteField.pow_card r
    rwa [hF] at this
  have : Fact (∀ r : F, r ^ 2 ≠ 1 + 1 * r) := ⟨fun r hr => by
    have h := hsq r
    exact one_ne_zero (by linear_combination h - hr)⟩
  have hM : rhoOmega F * rhoOmega F =
      (1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) + (1 : F) • rhoOmega F := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rhoOmega, Matrix.mul_apply, Fin.sum_univ_two]
  let ℓ : QuadraticAlgebra F 1 1 →ₐ[F] Matrix (Fin 2) (Fin 2) F :=
    QuadraticAlgebra.lift ⟨rhoOmega F, hM⟩
  refine ⟨QuadraticAlgebra F 1 1, inferInstance, ℓ.toRingHom, QuadraticAlgebra.omega, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (QuadraticAlgebra.equivProd 1 1), Nat.card_prod, Nat.card_eq_fintype_card,
      hF]
  · simp [ℓ]
  · intro g hg
    refine ⟨⟨g 0 0, g 0 1⟩, ?_⟩
    have e00 := congrFun (congrFun hg 0) 0
    have e01 := congrFun (congrFun hg 0) 1
    simp [rhoOmega, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ℓ, rhoOmega, QuadraticAlgebra.lift_apply_apply, e00, e01]

private def k328r5s_Phi (F : Type) [Field F] :
    Matrix (Fin 6) (Fin 6) F ≃+* Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) F) :=
  (Matrix.reindexRingEquiv F finProdFinEquiv.symm).trans
    (Matrix.compRingEquiv (Fin 3) (Fin 2) F).symm

private theorem k328r5s_Phi_apply {F : Type} [Field F] (g : Matrix (Fin 6) (Fin 6) F)
    (i j : Fin 3) (r s : Fin 2) :
    k328r5s_Phi F g i j r s = g (finProdFinEquiv (i, r)) (finProdFinEquiv (j, s)) := by
  simp [k328r5s_Phi]

private theorem k328r5s_Phi_blockDiag3 {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (A₀ A₁ A₂ : Matrix (Fin 2) (Fin 2) F) :
    k328r5s_Phi F (blockDiag3 F 6 A₀ A₁ A₂) = Matrix.diagonal ![A₀, A₁, A₂] := by
  ext i j r s
  rw [k328r5s_Phi_apply]
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases s <;>
    simp [blockDiag3, finProdFinEquiv, Matrix.diagonal]

private def k328r5s_rho {F L : Type} [Field F] [Field L] (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 3) (Fin 3) L →+* Matrix (Fin 6) (Fin 6) F :=
  (k328r5s_Phi F).symm.toRingHom.comp ℓ.mapMatrix

private theorem k328r5s_Phi_rho {F L : Type} [Field F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) (A : Matrix (Fin 3) (Fin 3) L) :
    k328r5s_Phi F (k328r5s_rho ℓ A) = ℓ.mapMatrix A := by
  simp [k328r5s_rho]

private theorem k328r5s_rho_injective {F L : Type} [Field F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) : Function.Injective (k328r5s_rho ℓ) := by
  intro A B h
  have h1 := congrArg (k328r5s_Phi F) h
  rw [k328r5s_Phi_rho, k328r5s_Phi_rho] at h1
  exact Matrix.map_injective ℓ.injective h1

private theorem k328r5s_exists_rho {F L : Type} [Field F] [Fintype F] [DecidableEq F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F)
    (hsurj : ∀ g : Matrix (Fin 2) (Fin 2) F, rhoOmega F * g = g * rhoOmega F → ∃ a : L, ℓ a = g)
    (g : Matrix (Fin 6) (Fin 6) F)
    (hg : blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F) * g =
      g * blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F)) :
    ∃ A : Matrix (Fin 3) (Fin 3) L, k328r5s_rho ℓ A = g := by
  have h1 := congrArg (k328r5s_Phi F) hg
  rw [map_mul, map_mul, k328r5s_Phi_blockDiag3] at h1
  have hb : ∀ i j, rhoOmega F * k328r5s_Phi F g i j = k328r5s_Phi F g i j * rhoOmega F := by
    intro i j
    have := congrFun (congrFun h1 i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    fin_cases i <;> fin_cases j <;> simpa using this
  choose a ha using fun i j => hsurj _ (hb i j)
  refine ⟨Matrix.of a, (k328r5s_Phi F).injective ?_⟩
  rw [k328r5s_Phi_rho]
  refine Matrix.ext fun i j => ?_
  exact ha i j

private def k328r5s_ext {F : Type} [Field F] :
    Matrix (Fin 6) (Fin 6) F →* Matrix (Fin 7) (Fin 7) F where
  toFun B := Matrix.reindexAlgEquiv F F (finSumFinEquiv : Fin 6 ⊕ Fin 1 ≃ Fin 7)
    (Matrix.fromBlocks B 0 0 1)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' B B' := by
    rw [← map_mul]
    congr 1
    simp [Matrix.fromBlocks_multiply]

private theorem k328r5s_symm_last :
    (finSumFinEquiv.symm (6 : Fin 7) : Fin 6 ⊕ Fin 1) = Sum.inr 0 := rfl

private theorem k328r5s_ext_cc {F : Type} [Field F] (B : Matrix (Fin 6) (Fin 6) F) (i j : Fin 6) :
    k328r5s_ext B i.castSucc j.castSucc = B i j := by
  simp [k328r5s_ext, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

private theorem k328r5s_ext_cl {F : Type} [Field F] (B : Matrix (Fin 6) (Fin 6) F) (i : Fin 6) :
    k328r5s_ext B i.castSucc (Fin.last 6) = 0 := by
  simp [k328r5s_ext, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, k328r5s_symm_last]

private theorem k328r5s_ext_lc {F : Type} [Field F] (B : Matrix (Fin 6) (Fin 6) F) (j : Fin 6) :
    k328r5s_ext B (Fin.last 6) j.castSucc = 0 := by
  simp [k328r5s_ext, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, k328r5s_symm_last]

private theorem k328r5s_ext_ll {F : Type} [Field F] (B : Matrix (Fin 6) (Fin 6) F) :
    k328r5s_ext B (Fin.last 6) (Fin.last 6) = 1 := by
  simp [k328r5s_ext, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, k328r5s_symm_last]

private theorem k328r5s_ext_inj {F : Type} [Field F] :
    Function.Injective (k328r5s_ext (F := F)) := by
  intro B B' h
  ext i j
  have := congrFun (congrFun h i.castSucc) j.castSucc
  rwa [k328r5s_ext_cc, k328r5s_ext_cc] at this

private theorem k328r5s_ext_eq {F : Type} [Field F] (g : Matrix (Fin 7) (Fin 7) F)
    (h1 : ∀ i : Fin 6, g i.castSucc (Fin.last 6) = 0)
    (h2 : ∀ j : Fin 6, g (Fin.last 6) j.castSucc = 0)
    (h3 : g (Fin.last 6) (Fin.last 6) = 1) :
    g = k328r5s_ext (Matrix.of fun i j => g i.castSucc j.castSucc) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [h3]; exact (k328r5s_ext_ll _).symm
    | cast j => rw [h2]; exact (k328r5s_ext_lc _ _).symm
  | cast i =>
    induction j using Fin.lastCases with
    | last => rw [h1]; exact (k328r5s_ext_cl _ _).symm
    | cast j => rw [k328r5s_ext_cc]; rfl

private theorem k328r5s_ext_blockDiag3 {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (A B C : Matrix (Fin 2) (Fin 2) F) :
    blockDiag3 F 7 A B C = k328r5s_ext (blockDiag3 F 6 A B C) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      rw [k328r5s_ext_ll]
      simp [blockDiag3]
    | cast j =>
      rw [k328r5s_ext_lc]
      simp only [blockDiag3, Matrix.of_apply, Fin.val_last, Fin.val_castSucc]
      have := j.isLt
      rw [if_neg (by omega)]
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [k328r5s_ext_cl]
      simp only [blockDiag3, Matrix.of_apply, Fin.val_last, Fin.val_castSucc]
      have := i.isLt
      rw [if_neg (by omega)]
    | cast j =>
      rw [k328r5s_ext_cc]
      simp [blockDiag3]

private theorem k328r5s_vanish {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (g : Matrix (Fin 7) (Fin 7) F)
    (hg : blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F) * g =
      g * blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F)) :
    (∀ i : Fin 6, g i.castSucc (Fin.last 6) = 0) ∧ ∀ j : Fin 6, g (Fin.last 6) j.castSucc = 0 := by
  have e : ∀ i j : Fin 7,
      ∑ k, blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F) i k * g k j =
      ∑ k, g i k * blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F) k j := fun i j => by
    simpa only [Matrix.mul_apply] using congrFun (congrFun hg i) j
  simp only [Fin.sum_univ_seven] at e
  have e06 := e 0 6
  have e16 := e 1 6
  have e26 := e 2 6
  have e36 := e 3 6
  have e46 := e 4 6
  have e56 := e 5 6
  have e60 := e 6 0
  have e61 := e 6 1
  have e62 := e 6 2
  have e63 := e 6 3
  have e64 := e 6 4
  have e65 := e 6 5
  simp [blockDiag3, rhoOmega] at e06 e16 e26 e36 e46 e56 e60 e61 e62 e63 e64 e65
  have h16 : g 1 6 = 0 := by rw [e06, e16]
  have h36 : g 3 6 = 0 := by rw [e26, e36]
  have h56 : g 5 6 = 0 := by rw [e46, e56]
  have h61 : g 6 1 = 0 := by rw [← e60, e61]
  have h63 : g 6 3 = 0 := by rw [← e62, e63]
  have h65 : g 6 5 = 0 := by rw [← e64, e65]
  refine ⟨fun i => ?_, fun j => ?_⟩
  · fin_cases i
    exacts [e16, h16, e36, h36, e56, h56]
  · fin_cases j
    exacts [e61, h61, e63, h63, e65, h65]

private theorem k328r5s_zero_or_one {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (r : F) : r = 0 ∨ r = 1 := by
  have h := FiniteField.pow_card r
  rw [hF] at h
  have h0 : r * (r - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (sub_eq_zero.1 h1)

private theorem k328r5s_shape {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 2) (z₀ : GL (Fin 7) F)
    (hz : (z₀ : Matrix (Fin 7) (Fin 7) F) =
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F))
    (g : GL (Fin 7) F) (hg : z₀ * g = g * z₀) :
    ∃ B : Matrix (Fin 6) (Fin 6) F, (g : Matrix (Fin 7) (Fin 7) F) = k328r5s_ext B ∧
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F) * B =
        B * blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F) := by
  have hc : Commute z₀ g := hg
  have hmat : ∀ h : GL (Fin 7) F, Commute z₀ h →
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F) * (h : Matrix (Fin 7) (Fin 7) F) =
        (h : Matrix (Fin 7) (Fin 7) F) *
          blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F) := by
    intro h hh
    have := congrArg (fun u : GL (Fin 7) F => (u : Matrix (Fin 7) (Fin 7) F)) hh.eq
    simpa [hz] using this
  obtain ⟨hv1, hv2⟩ := k328r5s_vanish _ (hmat g hc)
  obtain ⟨-, hw2⟩ := k328r5s_vanish _ (hmat g⁻¹ hc.inv_right)
  have h66 : (g : Matrix (Fin 7) (Fin 7) F) (Fin.last 6) (Fin.last 6) = 1 := by
    have h1 : ((g⁻¹ : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) * (g : Matrix (Fin 7) (Fin 7) F) =
        1 := g.inv_mul
    have h2 := congrFun (congrFun h1 (Fin.last 6)) (Fin.last 6)
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc,
      Finset.sum_eq_zero (fun k _ => by rw [hw2 k, zero_mul]), zero_add,
      Matrix.one_apply_eq] at h2
    rcases k328r5s_zero_or_one hF ((g : Matrix (Fin 7) (Fin 7) F) (Fin.last 6) (Fin.last 6)) with
      h0 | h0
    · rw [h0, mul_zero] at h2
      exact absurd h2 zero_ne_one
    · exact h0
  have hext := k328r5s_ext_eq (g : Matrix (Fin 7) (Fin 7) F) hv1 hv2 h66
  refine ⟨Matrix.of fun i j => (g : Matrix (Fin 7) (Fin 7) F) i.castSucc j.castSucc, hext, ?_⟩
  apply k328r5s_ext_inj
  rw [map_mul, map_mul, ← hext, ← k328r5s_ext_blockDiag3, ← hz]
  simpa using congrArg (fun u : GL (Fin 7) F => (u : Matrix (Fin 7) (Fin 7) F)) hg

private def k328r5s_rhoG {F L : Type} [Field F] [Field L] (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) :
    GL (Fin 3) L →* GL (Fin 7) F :=
  Units.map (k328r5s_ext.comp (k328r5s_rho ℓ).toMonoidHom)

private theorem k328r5s_rhoG_val {F L : Type} [Field F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) (a : GL (Fin 3) L) :
    ((k328r5s_rhoG ℓ a : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) =
      k328r5s_ext (k328r5s_rho ℓ (a : Matrix (Fin 3) (Fin 3) L)) := rfl

private theorem k328r5s_rhoG_injective {F L : Type} [Field F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) : Function.Injective (k328r5s_rhoG ℓ) := by
  intro a b h
  apply Units.ext
  apply k328r5s_rho_injective ℓ
  apply k328r5s_ext_inj
  have := congrArg (fun u : GL (Fin 7) F => (u : Matrix (Fin 7) (Fin 7) F)) h
  simpa [k328r5s_rhoG_val] using this

private theorem k328r5s_exists_rhoG {F L : Type} [Field F] [Fintype F] [DecidableEq F] [Field L]
    (hF : Fintype.card F = 2) (ℓ : L →+* Matrix (Fin 2) (Fin 2) F)
    (hsurj : ∀ g : Matrix (Fin 2) (Fin 2) F, rhoOmega F * g = g * rhoOmega F → ∃ a : L, ℓ a = g)
    (z₀ : GL (Fin 7) F)
    (hz : (z₀ : Matrix (Fin 7) (Fin 7) F) =
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F))
    (g : GL (Fin 7) F) (hg : z₀ * g = g * z₀) : ∃ a : GL (Fin 3) L, k328r5s_rhoG ℓ a = g := by
  have hc : Commute z₀ g := hg
  obtain ⟨B, hB, hBc⟩ := k328r5s_shape hF z₀ hz g hg
  obtain ⟨B', hB', hBc'⟩ := k328r5s_shape hF z₀ hz g⁻¹ hc.inv_right
  obtain ⟨A, hA⟩ := k328r5s_exists_rho ℓ hsurj B hBc
  obtain ⟨A', hA'⟩ := k328r5s_exists_rho ℓ hsurj B' hBc'
  have hAB : A * A' = 1 := by
    apply k328r5s_rho_injective ℓ
    apply k328r5s_ext_inj
    rw [map_mul, map_mul, hA, hA', ← hB, ← hB', map_one, map_one]
    exact g.mul_inv
  have hBA : A' * A = 1 := by
    apply k328r5s_rho_injective ℓ
    apply k328r5s_ext_inj
    rw [map_mul, map_mul, hA, hA', ← hB, ← hB', map_one, map_one]
    exact g.inv_mul
  refine ⟨⟨A, A', hAB, hBA⟩, Units.ext ?_⟩
  rw [k328r5s_rhoG_val]
  exact (congrArg _ hA).trans hB.symm


private theorem k328r5s_stdComp_le {F L : Type} [Field F] [Fintype F] [DecidableEq F] [Field L]
    (hF : Fintype.card F = 2) (ℓ : L →+* Matrix (Fin 2) (Fin 2) F)
    (hsurj : ∀ g : Matrix (Fin 2) (Fin 2) F, rhoOmega F * g = g * rhoOmega F → ∃ a : L, ℓ a = g)
    (z₀ : GL (Fin 7) F)
    (hz : (z₀ : Matrix (Fin 7) (Fin 7) F) =
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F)) :
    stdComp (StatedSL 7 F) z₀ ≤ (StatedSL 3 L).map (k328r5s_rhoG ℓ) := by
  have hcard : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card]; exact hF
  have hC : StatedSL 7 F ⊓ Subgroup.centralizer {z₀} = Subgroup.centralizer {z₀} := by
    rw [CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hcard 7, top_inf_eq]
  unfold stdComp
  rw [hC, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨a, rfl⟩ := k328r5s_exists_rhoG hF ℓ hsurj z₀ hz g₁
    (Subgroup.mem_centralizer_iff.1 hg₁ z₀ rfl)
  obtain ⟨b, rfl⟩ := k328r5s_exists_rhoG hF ℓ hsurj z₀ hz g₂
    (Subgroup.mem_centralizer_iff.1 hg₂ z₀ rfl)
  refine ⟨⁅a, b⁆, ?_, map_commutatorElement _ _ _⟩
  show ⁅a, b⁆ ∈ StatedSL 3 L
  rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)

private theorem k328r5s_card_gl (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = 2) :
    Nat.card (GL (Fin 7) F) = 163849992929280 := by
  rw [Matrix.card_GL_field, hF, Fin.prod_univ_seven]
  norm_num

private theorem k328r5s_card_pos {K : Type} [Group K] [Finite K] {Z X : Subgroup K}
    (h : Pos K Z X) : Nat.card X = 60480 ∨ Nat.card X = 16547328 := by
  obtain ⟨-, -, -, -, -, hZ, hL⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥X), hZ]
  rcases hL with h | h
  · left
    rw [CFSG.Blueprint.LieModel.card_psl_three_four h]
  · right
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight
      (h.statedClassicalModel (by decide))]

private theorem k328r5s_card_of_pos {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 2) {Z : Subgroup ↥(StatedSL 7 F)} {Y : Subgroup (GL (Fin 7) F)}
    (hY : Y ≤ StatedSL 7 F) (h : Pos ↥(StatedSL 7 F) Z (Y.subgroupOf (StatedSL 7 F))) :
    Nat.card Y = 60480 := by
  have hc : Nat.card Y = 60480 ∨ Nat.card Y = 16547328 := by
    rw [← card_subgroupOf_of_le hY]
    exact k328r5s_card_pos h
  have hd : Nat.card Y ∣ 163849992929280 := by
    rw [← k328r5s_card_gl F hF]
    exact Subgroup.card_subgroup_dvd_card Y
  rcases hc with hc | hc
  · exact hc
  · rw [hc] at hd
    exact absurd hd (by norm_num)

theorem row5_size (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 2) (z₀ t₀ : GL (Fin 7) F)
    (hz : (z₀ : Matrix (Fin 7) (Fin 7) F) =
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F))
    (ht : (t₀ : Matrix (Fin 7) (Fin 7) F) =
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F ^ 2) 1) :
    SizeLeaf (StatedSL 7 F) z₀ := by
  have _ := ht
  intro hz₀ X hX hP
  obtain ⟨L, _, ℓ, ω, hL, hω, hsurj⟩ := k328r5s_model F hF
  have hfin : Finite L := Nat.finite_of_card_ne_zero (by omega)
  have hle := k328r5s_stdComp_le hF ℓ hsurj z₀ hz
  have hY : Nat.card ↥((StatedSL 3 L).map (k328r5s_rhoG ℓ)) = 60480 := by
    rw [Subgroup.card_map_of_injective (k328r5s_rhoG_injective ℓ),
      CFSG.Open.StatedAPI.card_statedSL_three, hL]
    norm_num
  have h1 : Nat.card ↥(stdComp (StatedSL 7 F) z₀) ≤ 60480 :=
    hY ▸ Subgroup.card_le_of_le hle
  have h2 : Nat.card X = 60480 := k328r5s_card_of_pos hF (hX.trans (stdComp_le _ _)) hP
  have h3 : Nat.card X ≤ Nat.card ↥(stdComp (StatedSL 7 F) z₀) := Subgroup.card_le_of_le hX
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
