module

public import CFSG.LocalAnalysis.StandardType.FS81.N6Split
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreTransvOrth
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def tauSign (n : ℕ) : Fin (n + 1) → ZMod 3 := fun i => if i = 0 then 1 else -1

theorem diagonal_tauSign_mem_evenFix0 {n : ℕ} (hn : Even n) :
    Matrix.diagonal (tauSign n) ∈ evenFix0 n := by
  refine ⟨1, tauSign n, fun i => ?_, ⟨rfl, rfl, ?_⟩, ?_⟩
  · by_cases hi : i = 0
    · exact Or.inl (by simp [tauSign, hi])
    · exact Or.inr (by show (if i = 0 then (1 : ZMod 3) else -1) = -1; rw [if_neg hi])
  · simp [tauSign, Fin.succ_ne_zero, hn.neg_one_pow]
  · ext i j
    by_cases h : i = j
    · subst h
      simp [spMat_apply]
    · simp [spMat_apply, Matrix.diagonal_apply_ne _ h, h]

theorem diagonal_tauSign_mem_monoFix0 (n : ℕ) : Matrix.diagonal (tauSign n) ∈ monoFix0 n := by
  refine ⟨1, tauSign n, fun i => ?_, ⟨rfl, rfl⟩, ?_⟩
  · by_cases hi : i = 0
    · exact Or.inl (by simp [tauSign, hi])
    · exact Or.inr (by show (if i = 0 then (1 : ZMod 3) else -1) = -1; rw [if_neg hi])
  · ext i j
    by_cases h : i = j
    · subst h
      simp [spMat_apply]
    · simp [spMat_apply, Matrix.diagonal_apply_ne _ h, h]

theorem eq_zero_of_diagonal_tauSign_mulVec {n : ℕ} {w : Fin (n + 1) → ZMod 3}
    (h : Matrix.diagonal (tauSign n) *ᵥ w = w) {i : Fin (n + 1)} (hi : i ≠ 0) : w i = 0 := by
  have e := congrFun h i
  simp only [Matrix.mulVec_diagonal, tauSign, if_neg hi, neg_one_mul] at e
  exact eq_zero_of_neg_eq_self e

theorem apply_zero_eq_zero_of_commute_tau {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (h : A * Matrix.diagonal (tauSign n) = Matrix.diagonal (tauSign n) * A) {i : Fin (n + 1)}
    (hi : i ≠ 0) : A i 0 = 0 := by
  have e := congrFun (congrFun h i) 0
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, tauSign, if_neg hi, ↓reduceIte, mul_one,
    neg_one_mul] at e
  exact eq_zero_of_neg_eq_self e.symm

theorem eq_diagonal_tauSign_of_mem_monoFix0 {n : ℕ}
    {S : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)} (hS : S ∈ monoFix0 n) (h2 : S * S = 1)
    (hfix : ∀ v, S *ᵥ v = v → ∀ i, i ≠ 0 → v i = 0) : S = Matrix.diagonal (tauSign n) := by
  obtain ⟨σ, s, hs, ⟨hσ0, hs0⟩, rfl⟩ := hS
  have hcol : ∀ j c, spMat σ s *ᵥ Pi.single j c = Pi.single (σ j) (s j * c) := by
    intro j c
    funext i
    rw [spMat_mulVec]
    by_cases h : i = σ j
    · subst h
      simp
    · have hne : σ.symm i ≠ j := fun e => h (by rw [← e, Equiv.apply_symm_apply])
      simp [Pi.single_apply, hne, h]
  have hsq : ∀ j, σ (σ j) = j ∧ s (σ j) * s j = 1 := by
    intro j
    have e := congrFun (congrFun h2 (σ (σ j))) j
    rw [spMat_mul, spMat_apply, Equiv.Perm.mul_apply, if_pos rfl, Matrix.one_apply] at e
    have hne : s (σ j) * s j ≠ 0 := by
      rcases hs (σ j) with h1 | h1 <;> rcases hs j with h3 | h3 <;> rw [h1, h3] <;> decide
    by_cases hj : σ (σ j) = j
    · rw [if_pos hj] at e
      exact ⟨hj, e⟩
    · rw [if_neg hj] at e
      exact absurd e hne
  have hfixed : ∀ i, i ≠ 0 → σ i = i ∧ s i = -1 := by
    intro i hi
    by_cases hσi : σ i = i
    · refine ⟨hσi, ?_⟩
      rcases hs i with h1 | h1
      · exfalso
        have hv := hfix (Pi.single i 1) (by rw [hcol, hσi, h1, mul_one]) i hi
        simp at hv
      · exact h1
    · exfalso
      obtain ⟨hii, hsi⟩ := hsq i
      have hv : spMat σ s *ᵥ (Pi.single i 1 + Pi.single (σ i) (s i)) =
          Pi.single i 1 + Pi.single (σ i) (s i) := by
        rw [Matrix.mulVec_add, hcol, hcol, hii, hsi, mul_one]
        exact add_comm _ _
      have h0 := hfix _ hv i hi
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hσi), add_zero] at h0
      exact one_ne_zero h0
  have hσ1 : σ = 1 := Equiv.ext fun i => by
    by_cases hi : i = 0
    · subst hi
      exact hσ0
    · exact (hfixed i hi).1
  have hs' : s = tauSign n := funext fun i => by
    by_cases hi : i = 0
    · subst hi
      simp [tauSign, hs0]
    · simp [tauSign, hi, (hfixed i hi).2]
  subst hσ1 hs'
  ext i j
  by_cases h : i = j
  · subst h
    simp [spMat_apply]
  · simp [spMat_apply, Matrix.diagonal_apply_ne _ h, h]

theorem false_of_normalizer_le_monoFix0 {G : Type} [Group G] [Finite G] {n : ℕ} (hn : n ≠ 0)
    (B : Basis3 G (n + 1)) {b₀ : G} (hb0 : B.b 0 = b₀) (hfus : Fus42 B b₀)
    (hodd : OddCoreTrivial B.span)
    (hle : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ⊆ monoFix0 n)
    (hτ : Matrix.diagonal (tauSign n) ∈
      B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))) : False := by
  classical
  set X := ggAutomizer ⊤ B.span with hX
  have : Finite (MulAut ↥B.span) :=
    Finite.of_injective (fun f : MulAut ↥B.span => (f : ↥B.span → ↥B.span)) DFunLike.coe_injective
  have : Fintype ↥X := Fintype.ofFinite _
  set T : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3) := Matrix.diagonal (tauSign n) with hT
  have hnorm0 : ∀ (φ : MulAut ↥B.span) (x : G),
      (∀ b : ↥B.span, ((φ b : ↥B.span) : G) = x * b * x⁻¹) →
      B.matOf φ * T = T * B.matOf φ → x ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    intro φ x hφ hc
    have hcol : B.matOf φ *ᵥ Pi.single 0 1 = B.matOf φ 0 0 • Pi.single 0 1 := by
      funext i
      rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i = 0
      · subst hi
        simp
      · rw [apply_zero_eq_zero_of_commute_tau hc hi, Pi.single_eq_of_ne hi, mul_zero]
    have hconj := B.conj_b_of_mulVec_single hφ hcol
    rw [hb0] at hconj
    apply Basis3.mem_normalizer_zpowers_of_conj
    rw [hconj]
    exact Subgroup.npow_mem_zpowers _ _
  have hTmem : T ∈ B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := hτ
  obtain ⟨φτ, ⟨gτ, -, hgτN, hgτ⟩, hφτT⟩ := (B.mem_realized_iff _ T).mp hTmem
  have hτX : φτ ∈ X := mem_ggAutomizer_iff.mpr ⟨gτ, trivial, hgτN, hgτ⟩
  set τ : ↥X := ⟨φτ, hτX⟩ with hτdef
  have hmatτ : B.matOf (τ : MulAut ↥B.span) = T := hφτT
  have hmatmul : ∀ x y : ↥X, B.matOf ((x * y : ↥X) : MulAut ↥B.span) =
      B.matOf (x : MulAut ↥B.span) * B.matOf (y : MulAut ↥B.span) := fun x y => by
    rw [Subgroup.coe_mul, Basis3.matOf_mul]
  have hmatinv : ∀ x : ↥X, B.matOf (x : MulAut ↥B.span) * B.matOf ((x⁻¹ : ↥X) : MulAut ↥B.span) =
      1 ∧ B.matOf ((x⁻¹ : ↥X) : MulAut ↥B.span) * B.matOf (x : MulAut ↥B.span) = 1 := fun x => by
    rw [← hmatmul, ← hmatmul, mul_inv_cancel, inv_mul_cancel, OneMemClass.coe_one,
      Basis3.matOf_one]
    exact ⟨rfl, rfl⟩
  have hmatinj : ∀ x y : ↥X, B.matOf (x : MulAut ↥B.span) = B.matOf (y : MulAut ↥B.span) →
      x = y := fun x y h => Subtype.ext (B.matOf_injective h)
  have hTT : T * T = 1 := by
    rw [hT, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hi : i = 0 <;> simp [tauSign, hi]
  have hτ1 : τ ≠ 1 := by
    intro h
    have e := congrArg (fun x : ↥X => B.matOf (x : MulAut ↥B.span)) h
    simp only [hmatτ, OneMemClass.coe_one, Basis3.matOf_one] at e
    have h10 : (⟨1, by omega⟩ : Fin (n + 1)) ≠ 0 := fun h0 => by
      have := congrArg Fin.val h0
      simp at this
    have e2 := congrFun (congrFun e ⟨1, by omega⟩) ⟨1, by omega⟩
    rw [hT, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at e2
    simp only [tauSign, if_neg h10] at e2
    exact absurd e2 (by decide)
  have hτ2 : τ * τ = 1 := hmatinj _ _ (by rw [hmatmul, hmatτ, hTT, OneMemClass.coe_one,
    Basis3.matOf_one])
  have hiso : ∀ g : ↥X, (g * τ * g⁻¹) * τ = τ * (g * τ * g⁻¹) → g * τ * g⁻¹ = τ := by
    intro g hgc
    set M := B.matOf (g : MulAut ↥B.span) with hM
    set M' := B.matOf ((g⁻¹ : ↥X) : MulAut ↥B.span) with hM'
    obtain ⟨hMM', hM'M⟩ := hmatinv g
    set S := B.matOf ((g * τ * g⁻¹ : ↥X) : MulAut ↥B.span) with hS
    have hSdef : S = M * T * M' := by rw [hS, hmatmul, hmatmul, hmatτ]
    have hST : S * T = T * S := by
      have e := congrArg (fun x : ↥X => B.matOf (x : MulAut ↥B.span)) hgc
      simp only [hmatmul, hmatτ] at e
      rw [hS, hmatmul, hmatmul, hmatτ]
      exact e
    obtain ⟨x, -, hxN, hx⟩ := mem_ggAutomizer_iff.mp (g * τ * g⁻¹).2
    have hSmem : S ∈ monoFix0 n :=
      hle (show S ∈ B.realized _ from ⟨x, hnorm0 _ x hx hST, B.acts_matOf hx⟩)
    have hSS : S * S = 1 := by
      rw [hS, ← hmatmul]
      have : g * τ * g⁻¹ * (g * τ * g⁻¹) = 1 := by
        rw [show g * τ * g⁻¹ * (g * τ * g⁻¹) = g * (τ * τ) * g⁻¹ by group, hτ2, mul_one,
          mul_inv_cancel]
      rw [this, OneMemClass.coe_one, Basis3.matOf_one]
    have hfixT : ∀ v, S *ᵥ v = v → ∃ c : ZMod 3, v = c • (M *ᵥ Pi.single 0 1) := by
      intro v hv
      have hw : T *ᵥ (M' *ᵥ v) = M' *ᵥ v := by
        have e := congrArg (fun u => M' *ᵥ u) hv
        simp only [hSdef, Matrix.mulVec_mulVec] at e
        rw [Matrix.mulVec_mulVec]
        calc (T * M') *ᵥ v = (M' * M * T * M') *ᵥ v := by rw [hM'M, Matrix.one_mul]
          _ = M' *ᵥ v := by rw [← e]; simp only [Matrix.mul_assoc]
      obtain ⟨c, hc⟩ : ∃ c : ZMod 3, M' *ᵥ v = c • Pi.single 0 1 := by
        refine ⟨(M' *ᵥ v) 0, funext fun i => ?_⟩
        by_cases hi : i = 0
        · subst hi
          simp
        · rw [eq_zero_of_diagonal_tauSign_mulVec hw hi, Pi.smul_apply, Pi.single_eq_of_ne hi,
            smul_zero]
      refine ⟨c, ?_⟩
      calc v = M *ᵥ (M' *ᵥ v) := by rw [Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec]
        _ = M *ᵥ (c • Pi.single 0 1) := by rw [hc]
        _ = c • (M *ᵥ Pi.single 0 1) := Matrix.mulVec_smul _ _ _
    have hSe0 : S *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
      obtain ⟨σ, s, -, ⟨hσ0, hs0⟩, hSeq⟩ := hSmem
      rw [hSeq]
      funext i
      rw [spMat_mulVec]
      by_cases hi : i = 0
      · subst hi
        have : σ.symm 0 = 0 := by rw [Equiv.symm_apply_eq, hσ0]
        simp [this, hs0]
      · have : σ.symm i ≠ 0 := fun e => hi (by rw [← hσ0, ← e, Equiv.apply_symm_apply])
        simp [Pi.single_apply, this, hi]
    have hfix : ∀ v, S *ᵥ v = v → ∀ i, i ≠ 0 → v i = 0 := by
      obtain ⟨c₀, hc₀⟩ := hfixT _ hSe0
      have hc₀ne : c₀ ≠ 0 := by
        intro h
        have e := congrFun hc₀ 0
        rw [h, zero_smul, Pi.single_eq_same] at e
        exact one_ne_zero e
      intro v hv i hi
      obtain ⟨c, hc⟩ := hfixT v hv
      have hMe : M *ᵥ Pi.single 0 1 = c₀⁻¹ • Pi.single 0 1 := by
        calc M *ᵥ Pi.single 0 1 = (c₀⁻¹ * c₀) • (M *ᵥ Pi.single 0 1) := by
              rw [inv_mul_cancel₀ hc₀ne, one_smul]
          _ = c₀⁻¹ • (c₀ • (M *ᵥ Pi.single 0 1)) := by rw [smul_smul]
          _ = c₀⁻¹ • Pi.single 0 1 := by rw [← hc₀]
      rw [hc, hMe, smul_smul, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]
    have hST' : S = T := eq_diagonal_tauSign_of_mem_monoFix0 hSmem hSS hfix
    exact hmatinj _ _ (by rw [← hS, hST', hmatτ])
  obtain ⟨N, hNn, hNodd, hNτ⟩ := CFSG.ZStar.glauberman_zStar ↥X τ hτ1 hτ2 hiso
  have hN : N = ⊥ := hodd N hNn hNodd
  have hcent : ∀ g : ↥X, g * τ = τ * g := by
    intro g
    have h1 := hNτ g
    rw [hN, Subgroup.mem_bot, mul_inv_eq_one] at h1
    calc g * τ = g * τ * g⁻¹ * g := by group
      _ = τ * g := by rw [h1]
  apply hfus.1
  intro x hx
  set φx : ↥X := ⟨ggConjAut B.span hx, ggConjAut_mem_ggAutomizer (Subgroup.mem_top x) hx⟩ with hφx
  refine hnorm0 (φx : MulAut ↥B.span) x (ggConjAut_apply B.span hx) ?_
  rw [← hmatτ, ← hmatmul, ← hmatmul, hcent]

theorem l1N6Fix_holds : L1N6Fix := by
  intro G _ _ b₀ K E _ B hB _ hfus hodd hN0
  obtain ⟨hspan, hb0, -⟩ := hB
  subst hspan
  refine false_of_normalizer_le_monoFix0 (by decide) B hb0 hfus hodd ?_ ?_
  · rw [hN0]
    exact evenFix0_subset_monoFix0 _
  · rw [hN0]
    exact diagonal_tauSign_mem_evenFix0 ⟨3, rfl⟩

end CFSG.StandardType.FrameRoute.FS81

end
