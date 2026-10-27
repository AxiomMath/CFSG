module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows
import CFSG.Adapters.StatedQuasisimple
import CFSG.Open.StatedCenterThree
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open scoped commutatorElement

private theorem k328r5p_model (F : Type) [Field F] [Fintype F] [DecidableEq F]
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

private def k328r5p_Phi (F : Type) [Field F] :
    Matrix (Fin 6) (Fin 6) F ≃+* Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) F) :=
  (Matrix.reindexRingEquiv F finProdFinEquiv.symm).trans
    (Matrix.compRingEquiv (Fin 3) (Fin 2) F).symm

private theorem k328r5p_Phi_apply {F : Type} [Field F] (g : Matrix (Fin 6) (Fin 6) F)
    (i j : Fin 3) (r s : Fin 2) :
    k328r5p_Phi F g i j r s = g (finProdFinEquiv (i, r)) (finProdFinEquiv (j, s)) := by
  simp [k328r5p_Phi]

private theorem k328r5p_Phi_blockDiag3 {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (A₀ A₁ A₂ : Matrix (Fin 2) (Fin 2) F) :
    k328r5p_Phi F (blockDiag3 F 6 A₀ A₁ A₂) = Matrix.diagonal ![A₀, A₁, A₂] := by
  ext i j r s
  rw [k328r5p_Phi_apply]
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases s <;>
    simp [blockDiag3, finProdFinEquiv, Matrix.diagonal]

private def k328r5p_rho {F L : Type} [Field F] [Field L] (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 3) (Fin 3) L →+* Matrix (Fin 6) (Fin 6) F :=
  (k328r5p_Phi F).symm.toRingHom.comp ℓ.mapMatrix

private theorem k328r5p_Phi_rho {F L : Type} [Field F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) (A : Matrix (Fin 3) (Fin 3) L) :
    k328r5p_Phi F (k328r5p_rho ℓ A) = ℓ.mapMatrix A := by
  simp [k328r5p_rho]

private theorem k328r5p_rho_injective {F L : Type} [Field F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) : Function.Injective (k328r5p_rho ℓ) := by
  intro A B h
  have h1 := congrArg (k328r5p_Phi F) h
  rw [k328r5p_Phi_rho, k328r5p_Phi_rho] at h1
  exact Matrix.map_injective ℓ.injective h1

private theorem k328r5p_rho_scalar {F L : Type} [Field F] [Fintype F] [DecidableEq F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) (ω : L) (hω : ℓ ω = rhoOmega F) :
    k328r5p_rho ℓ (Matrix.scalar (Fin 3) ω) =
      blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F) := by
  apply (k328r5p_Phi F).injective
  rw [k328r5p_Phi_rho, k328r5p_Phi_blockDiag3, RingHom.mapMatrix_apply, Matrix.scalar_apply,
    Matrix.diagonal_map (map_zero ℓ), hω]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem k328r5p_exists_rho {F L : Type} [Field F] [Fintype F] [DecidableEq F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F)
    (hsurj : ∀ g : Matrix (Fin 2) (Fin 2) F, rhoOmega F * g = g * rhoOmega F → ∃ a : L, ℓ a = g)
    (g : Matrix (Fin 6) (Fin 6) F)
    (hg : blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F) * g =
      g * blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F)) :
    ∃ A : Matrix (Fin 3) (Fin 3) L, k328r5p_rho ℓ A = g := by
  have h1 := congrArg (k328r5p_Phi F) hg
  rw [map_mul, map_mul, k328r5p_Phi_blockDiag3] at h1
  have hb : ∀ i j, rhoOmega F * k328r5p_Phi F g i j = k328r5p_Phi F g i j * rhoOmega F := by
    intro i j
    have := congrFun (congrFun h1 i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    fin_cases i <;> fin_cases j <;> simpa using this
  choose a ha using fun i j => hsurj _ (hb i j)
  refine ⟨Matrix.of a, (k328r5p_Phi F).injective ?_⟩
  rw [k328r5p_Phi_rho]
  refine Matrix.ext fun i j => ?_
  exact ha i j

private def k328r5p_ext {F : Type} [Field F] :
    Matrix (Fin 6) (Fin 6) F →* Matrix (Fin 7) (Fin 7) F where
  toFun B := Matrix.reindexAlgEquiv F F (finSumFinEquiv : Fin 6 ⊕ Fin 1 ≃ Fin 7)
    (Matrix.fromBlocks B 0 0 1)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' B B' := by
    rw [← map_mul]
    congr 1
    simp [Matrix.fromBlocks_multiply]

private theorem k328r5p_symm_last :
    (finSumFinEquiv.symm (6 : Fin 7) : Fin 6 ⊕ Fin 1) = Sum.inr 0 := rfl

private theorem k328r5p_ext_cc {F : Type} [Field F] (B : Matrix (Fin 6) (Fin 6) F) (i j : Fin 6) :
    k328r5p_ext B i.castSucc j.castSucc = B i j := by
  simp [k328r5p_ext, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

private theorem k328r5p_ext_cl {F : Type} [Field F] (B : Matrix (Fin 6) (Fin 6) F) (i : Fin 6) :
    k328r5p_ext B i.castSucc (Fin.last 6) = 0 := by
  simp [k328r5p_ext, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, k328r5p_symm_last]

private theorem k328r5p_ext_lc {F : Type} [Field F] (B : Matrix (Fin 6) (Fin 6) F) (j : Fin 6) :
    k328r5p_ext B (Fin.last 6) j.castSucc = 0 := by
  simp [k328r5p_ext, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, k328r5p_symm_last]

private theorem k328r5p_ext_ll {F : Type} [Field F] (B : Matrix (Fin 6) (Fin 6) F) :
    k328r5p_ext B (Fin.last 6) (Fin.last 6) = 1 := by
  simp [k328r5p_ext, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, k328r5p_symm_last]

private theorem k328r5p_ext_inj {F : Type} [Field F] :
    Function.Injective (k328r5p_ext (F := F)) := by
  intro B B' h
  ext i j
  have := congrFun (congrFun h i.castSucc) j.castSucc
  rwa [k328r5p_ext_cc, k328r5p_ext_cc] at this

private theorem k328r5p_ext_eq {F : Type} [Field F] (g : Matrix (Fin 7) (Fin 7) F)
    (h1 : ∀ i : Fin 6, g i.castSucc (Fin.last 6) = 0)
    (h2 : ∀ j : Fin 6, g (Fin.last 6) j.castSucc = 0)
    (h3 : g (Fin.last 6) (Fin.last 6) = 1) :
    g = k328r5p_ext (Matrix.of fun i j => g i.castSucc j.castSucc) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [h3]; exact (k328r5p_ext_ll _).symm
    | cast j => rw [h2]; exact (k328r5p_ext_lc _ _).symm
  | cast i =>
    induction j using Fin.lastCases with
    | last => rw [h1]; exact (k328r5p_ext_cl _ _).symm
    | cast j => rw [k328r5p_ext_cc]; rfl

private theorem k328r5p_ext_blockDiag3 {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (A B C : Matrix (Fin 2) (Fin 2) F) :
    blockDiag3 F 7 A B C = k328r5p_ext (blockDiag3 F 6 A B C) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      rw [k328r5p_ext_ll]
      simp [blockDiag3]
    | cast j =>
      rw [k328r5p_ext_lc]
      simp only [blockDiag3, Matrix.of_apply, Fin.val_last, Fin.val_castSucc]
      have := j.isLt
      rw [if_neg (by omega)]
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [k328r5p_ext_cl]
      simp only [blockDiag3, Matrix.of_apply, Fin.val_last, Fin.val_castSucc]
      have := i.isLt
      rw [if_neg (by omega)]
    | cast j =>
      rw [k328r5p_ext_cc]
      simp [blockDiag3]

private theorem k328r5p_vanish {F : Type} [Field F] [Fintype F] [DecidableEq F]
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

private theorem k328r5p_zero_or_one {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (r : F) : r = 0 ∨ r = 1 := by
  have h := FiniteField.pow_card r
  rw [hF] at h
  have h0 : r * (r - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (sub_eq_zero.1 h1)

private theorem k328r5p_shape {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 2) (z₀ : GL (Fin 7) F)
    (hz : (z₀ : Matrix (Fin 7) (Fin 7) F) =
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F))
    (g : GL (Fin 7) F) (hg : z₀ * g = g * z₀) :
    ∃ B : Matrix (Fin 6) (Fin 6) F, (g : Matrix (Fin 7) (Fin 7) F) = k328r5p_ext B ∧
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
  obtain ⟨hv1, hv2⟩ := k328r5p_vanish _ (hmat g hc)
  obtain ⟨-, hw2⟩ := k328r5p_vanish _ (hmat g⁻¹ hc.inv_right)
  have h66 : (g : Matrix (Fin 7) (Fin 7) F) (Fin.last 6) (Fin.last 6) = 1 := by
    have h1 : ((g⁻¹ : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) * (g : Matrix (Fin 7) (Fin 7) F) =
        1 := g.inv_mul
    have h2 := congrFun (congrFun h1 (Fin.last 6)) (Fin.last 6)
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc,
      Finset.sum_eq_zero (fun k _ => by rw [hw2 k, zero_mul]), zero_add,
      Matrix.one_apply_eq] at h2
    rcases k328r5p_zero_or_one hF ((g : Matrix (Fin 7) (Fin 7) F) (Fin.last 6) (Fin.last 6)) with
      h0 | h0
    · rw [h0, mul_zero] at h2
      exact absurd h2 zero_ne_one
    · exact h0
  have hext := k328r5p_ext_eq (g : Matrix (Fin 7) (Fin 7) F) hv1 hv2 h66
  refine ⟨Matrix.of fun i j => (g : Matrix (Fin 7) (Fin 7) F) i.castSucc j.castSucc, hext, ?_⟩
  apply k328r5p_ext_inj
  rw [map_mul, map_mul, ← hext, ← k328r5p_ext_blockDiag3, ← hz]
  simpa using congrArg (fun u : GL (Fin 7) F => (u : Matrix (Fin 7) (Fin 7) F)) hg

private def k328r5p_rhoG {F L : Type} [Field F] [Field L] (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) :
    GL (Fin 3) L →* GL (Fin 7) F :=
  Units.map (k328r5p_ext.comp (k328r5p_rho ℓ).toMonoidHom)

private theorem k328r5p_rhoG_val {F L : Type} [Field F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) (a : GL (Fin 3) L) :
    ((k328r5p_rhoG ℓ a : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) =
      k328r5p_ext (k328r5p_rho ℓ (a : Matrix (Fin 3) (Fin 3) L)) := rfl

private theorem k328r5p_rhoG_injective {F L : Type} [Field F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) : Function.Injective (k328r5p_rhoG ℓ) := by
  intro a b h
  apply Units.ext
  apply k328r5p_rho_injective ℓ
  apply k328r5p_ext_inj
  have := congrArg (fun u : GL (Fin 7) F => (u : Matrix (Fin 7) (Fin 7) F)) h
  simpa [k328r5p_rhoG_val] using this

private theorem k328r5p_exists_rhoG {F L : Type} [Field F] [Fintype F] [DecidableEq F] [Field L]
    (hF : Fintype.card F = 2) (ℓ : L →+* Matrix (Fin 2) (Fin 2) F)
    (hsurj : ∀ g : Matrix (Fin 2) (Fin 2) F, rhoOmega F * g = g * rhoOmega F → ∃ a : L, ℓ a = g)
    (z₀ : GL (Fin 7) F)
    (hz : (z₀ : Matrix (Fin 7) (Fin 7) F) =
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F))
    (g : GL (Fin 7) F) (hg : z₀ * g = g * z₀) : ∃ a : GL (Fin 3) L, k328r5p_rhoG ℓ a = g := by
  have hc : Commute z₀ g := hg
  obtain ⟨B, hB, hBc⟩ := k328r5p_shape hF z₀ hz g hg
  obtain ⟨B', hB', hBc'⟩ := k328r5p_shape hF z₀ hz g⁻¹ hc.inv_right
  obtain ⟨A, hA⟩ := k328r5p_exists_rho ℓ hsurj B hBc
  obtain ⟨A', hA'⟩ := k328r5p_exists_rho ℓ hsurj B' hBc'
  have hAB : A * A' = 1 := by
    apply k328r5p_rho_injective ℓ
    apply k328r5p_ext_inj
    rw [map_mul, map_mul, hA, hA', ← hB, ← hB', map_one, map_one]
    exact g.mul_inv
  have hBA : A' * A = 1 := by
    apply k328r5p_rho_injective ℓ
    apply k328r5p_ext_inj
    rw [map_mul, map_mul, hA, hA', ← hB, ← hB', map_one, map_one]
    exact g.inv_mul
  refine ⟨⟨A, A', hAB, hBA⟩, Units.ext ?_⟩
  rw [k328r5p_rhoG_val]
  exact (congrArg _ hA).trans hB.symm

private theorem k328r5p_rhoG_commute {F L : Type} [Field F] [Fintype F] [DecidableEq F] [Field L]
    (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) (ω : L) (hω : ℓ ω = rhoOmega F) (z₀ : GL (Fin 7) F)
    (hz : (z₀ : Matrix (Fin 7) (Fin 7) F) =
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F))
    (a : GL (Fin 3) L) : z₀ * k328r5p_rhoG ℓ a = k328r5p_rhoG ℓ a * z₀ := by
  apply Units.ext
  simp only [Units.val_mul, k328r5p_rhoG_val, hz]
  rw [k328r5p_ext_blockDiag3, ← k328r5p_rho_scalar ℓ ω hω, ← map_mul, ← map_mul, ← map_mul,
    ← map_mul]
  congr 2
  exact (Matrix.scalar_commute ω (fun r => Commute.all _ _) _).eq

private theorem k328r5p_stdComp_eq {F L : Type} [Field F] [Fintype F] [DecidableEq F] [Field L]
    (hF : Fintype.card F = 2) (ℓ : L →+* Matrix (Fin 2) (Fin 2) F) (ω : L)
    (hω : ℓ ω = rhoOmega F)
    (hsurj : ∀ g : Matrix (Fin 2) (Fin 2) F, rhoOmega F * g = g * rhoOmega F → ∃ a : L, ℓ a = g)
    (z₀ : GL (Fin 7) F)
    (hz : (z₀ : Matrix (Fin 7) (Fin 7) F) =
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F)) :
    stdComp (StatedSL 7 F) z₀ = (StatedSL 3 L).map (k328r5p_rhoG ℓ) := by
  have hcard : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card]; exact hF
  have hC : StatedSL 7 F ⊓ Subgroup.centralizer {z₀} = Subgroup.centralizer {z₀} := by
    rw [CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hcard 7, top_inf_eq]
  have hYC : (StatedSL 3 L).map (k328r5p_rhoG ℓ) ≤ Subgroup.centralizer {z₀} := by
    rintro _ ⟨a, -, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact k328r5p_rhoG_commute ℓ ω hω z₀ hz a
  apply le_antisymm
  · unfold stdComp
    rw [hC, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨a, rfl⟩ := k328r5p_exists_rhoG hF ℓ hsurj z₀ hz g₁
      (Subgroup.mem_centralizer_iff.1 hg₁ z₀ rfl)
    obtain ⟨b, rfl⟩ := k328r5p_exists_rhoG hF ℓ hsurj z₀ hz g₂
      (Subgroup.mem_centralizer_iff.1 hg₂ z₀ rfl)
    refine ⟨⁅a, b⁆, ?_, map_commutatorElement _ _ _⟩
    show ⁅a, b⁆ ∈ StatedSL 3 L
    rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  · have : Group.IsPerfect ↥(StatedSL 3 L) :=
      (CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) le_rfl L).1
    have hperf : ⁅StatedSL 3 L, StatedSL 3 L⁆ = StatedSL 3 L := Subgroup.commutator_eq_self
    have hY : (StatedSL 3 L).map (k328r5p_rhoG ℓ) =
        ⁅(StatedSL 3 L).map (k328r5p_rhoG ℓ), (StatedSL 3 L).map (k328r5p_rhoG ℓ)⁆ := by
      rw [← Subgroup.map_commutator, hperf]
    unfold stdComp
    rw [hC]
    exact hY.le.trans (Subgroup.commutator_mono hYC hYC)

private theorem k328r5p_centralizer_zpowers_eq {G : Type} [Group G] (H : Subgroup G) (z₀ : G)
    (hz₀ : z₀ ∈ H) :
    Subgroup.centralizer ((Subgroup.zpowers (⟨z₀, hz₀⟩ : H) : Subgroup H) : Set H) =
      (H ⊓ Subgroup.centralizer {z₀}).subgroupOf H := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨x.2, fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact congrArg Subtype.val (h _ (Subgroup.mem_zpowers _))
  · rintro ⟨-, h⟩ y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute (⟨z₀, hz₀⟩ : H) x := Subtype.ext (h z₀ rfl)
    exact (hc.zpow_left k).eq

private theorem k328r5p_subgroupOf_commutator_self {A : Type} [Group A] (K : Subgroup A) :
    ⁅K, K⁆.subgroupOf K = commutator K := by
  rw [← Subgroup.map_subtype_commutator K]
  exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

private theorem k328r5p_pos_of_equiv {G : Type} [Group G] [Finite G] (H : Subgroup G) (z₀ : G)
    (hz₀ : z₀ ∈ H) (hz : z₀ ∈ stdComp H z₀) (ho : orderOf z₀ = 3) {L : Type} [Field L]
    (hL : Nat.card L = 4) (e : ↥(stdComp H z₀) ≃* ↥(StatedSL 3 L)) :
    Pos ↥H (Subgroup.zpowers (⟨z₀, hz₀⟩ : H)) ((stdComp H z₀).subgroupOf H) := by
  have hfin : Finite L := Nat.finite_of_card_ne_zero (by omega)
  have hSC : stdComp H z₀ ≤ H ⊓ Subgroup.centralizer {z₀} :=
    Subgroup.commutator_le_self (H ⊓ Subgroup.centralizer {z₀})
  let eX : ↥((stdComp H z₀).subgroupOf H) ≃* ↥(StatedSL 3 L) :=
    (Subgroup.subgroupOfEquivOfLe (stdComp_le H z₀)).trans e
  have hcen : Subgroup.center ↥(StatedSL 3 L) =
      (StatedScalars (Fin 3) L).subgroupOf (StatedSL 3 L) := by
    rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 3 L,
      Subgroup.map_center_eq (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 L)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact ho
  · rw [Subgroup.zpowers_le]
    exact hz
  · rw [k328r5p_centralizer_zpowers_eq]
    exact fun x hx => Subgroup.mem_subgroupOf.2 (hSC (Subgroup.mem_subgroupOf.1 hx))
  · rw [k328r5p_centralizer_zpowers_eq]
    have h1 : (stdComp H z₀).subgroupOf H =
        ⁅(H ⊓ Subgroup.centralizer {z₀}).subgroupOf H,
          (H ⊓ Subgroup.centralizer {z₀}).subgroupOf H⁆ := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le inf_le_left,
        Subgroup.map_subgroupOf_eq_of_le (hSC.trans inf_le_left)]
      rfl
    rw [h1, k328r5p_subgroupOf_commutator_self]
    exact Subgroup.Normal.isSubnormal inferInstance
  · have hq := CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) le_rfl L
    exact isQuasisimple_of_mulEquiv' eX.symm ⟨hq.1.1, hq.2.1⟩
  · have h3 : 3 ∣ Nat.card L - 1 := by rw [hL]
    rw [← CFSG.Open.StatedCenterThree.card_center_statedSL_three h3]
    exact Nat.card_congr (Subgroup.centerCongr eX).toEquiv
  · let f : ↥((stdComp H z₀).subgroupOf H) ⧸ Subgroup.center ↥((stdComp H z₀).subgroupOf H) ≃*
        StatedProj (StatedSL 3 L) :=
      QuotientGroup.congr _ ((StatedScalars (Fin 3) L).subgroupOf (StatedSL 3 L)) eX
        ((Subgroup.map_center_eq eX).trans hcen)
    refine Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv f.symm ?_)
    exact Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, L,
      inferInstance, inferInstance, by rw [hL]; norm_num, ⟨MulEquiv.refl _⟩⟩

theorem row5_pos (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 2) (z₀ t₀ : GL (Fin 7) F)
    (hz : (z₀ : Matrix (Fin 7) (Fin 7) F) =
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F))
    (ht : (t₀ : Matrix (Fin 7) (Fin 7) F) =
      blockDiag3 F 7 (rhoOmega F) (rhoOmega F ^ 2) 1) :
    PosLeaf (StatedSL 7 F) z₀ := by
  have _ := ht
  intro hz₀
  obtain ⟨L, _, ℓ, ω, hL, hω, hsurj⟩ := k328r5p_model F hF
  have hS := k328r5p_stdComp_eq hF ℓ ω hω hsurj z₀ hz
  have hfin : Finite L := Nat.finite_of_card_ne_zero (by omega)
  have hω0 : ω ≠ 0 := fun h => by
    have h1 := congrFun (congrFun (hω ▸ congrArg ℓ h) 0) 1
    simp [rhoOmega] at h1
  have hu : (Units.mk0 ω hω0) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Lˣ) (x := Units.mk0 ω hω0)
    rwa [Nat.card_units, hL] at h
  have hω3 : ω ^ 3 = 1 := by simpa using congrArg Units.val hu
  set a₀ : GL (Fin 3) L := Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ω hω0) with ha₀
  have ha₀z : k328r5p_rhoG ℓ a₀ = z₀ :=
    Units.ext (by rw [k328r5p_rhoG_val, ha₀, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0,
      k328r5p_rho_scalar ℓ ω hω, ← k328r5p_ext_blockDiag3, hz])
  have ha₀S : a₀ ∈ StatedSL 3 L := by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff, ha₀, Matrix.GeneralLinearGroup.coe_scalar,
      Units.val_mk0, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    exact hω3
  have hz3 : z₀ ^ 3 = 1 := by
    rw [← ha₀z, ← map_pow, ha₀, ← map_pow, hu, map_one, map_one]
  have hz1 : z₀ ≠ 1 := fun h => by
    have h1 := congrFun (congrFun
      (congrArg (fun u : GL (Fin 7) F => (u : Matrix (Fin 7) (Fin 7) F)) h) 0) 0
    simp [hz, blockDiag3, rhoOmega] at h1
  have ho : orderOf z₀ = 3 := orderOf_eq_prime hz3 hz1
  have hzS : z₀ ∈ stdComp (StatedSL 7 F) z₀ := by
    rw [hS]
    exact ⟨a₀, ha₀S, ha₀z⟩
  let e : ↥(stdComp (StatedSL 7 F) z₀) ≃* ↥(StatedSL 3 L) :=
    (MulEquiv.subgroupCongr hS).trans
      (Subgroup.equivMapOfInjective (StatedSL 3 L) (k328r5p_rhoG ℓ)
        (k328r5p_rhoG_injective ℓ)).symm
  exact k328r5p_pos_of_equiv (StatedSL 7 F) z₀ hz₀ hzS ho hL e

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
