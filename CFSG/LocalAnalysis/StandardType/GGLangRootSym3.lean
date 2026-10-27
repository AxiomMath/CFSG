module

public import CFSG.LocalAnalysis.StandardType.GGLangWSLGamma
import CFSG.CharacterTheory.SteinbergBYFieldFour

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem step_pinnedX_of_charTwo_of_frobRootMap
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : L) :
    D.step (pinnedX τ L γ c) = pinnedX τ L (ρ γ) (c ^ D.q) := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := D.steinberg
  obtain ⟨π, hπroot, -, -, hπ⟩ := exists_diagram_data (L := L) hP
  obtain ⟨w, hn⟩ := D.n_weyl
  obtain ⟨ε₁, hε₁, h₁⟩ := hπ γ hγ
  have hπγ : IsRoot τ (π γ) := (hπroot γ).2 hγ
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hπγ
  have e₁ := eq_one_of_mul_self_eq_one_of_charTwo hε₁
  have e₂ := eq_one_of_mul_self_eq_one_of_charTwo hε₂
  have hs : ∀ c, D.step (pinnedX τ L γ c) = pinnedX τ L (w • π γ) (Fr c) := fun c => by
    have h0 : D.step (pinnedX τ L γ c) = D.n * D.Φ (pinnedX τ L γ c) * D.n⁻¹ := by
      simp [LangDatum.step, MulAut.conj_apply]
    rw [h0, hΦ, units_map_entrywiseHom_pinnedX, h₁, e₁, one_mul, hn, h₂, e₂, one_mul]
  have hmem : D.step (pinnedX τ L γ 1) ∈ rootSubgroup τ L (ρ γ) := by
    rw [← hρ.map_rootSubgroup γ hγ]
    exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨1, rfl⟩)
  rw [hs 1, map_one] at hmem
  rw [hs c, eq_of_pinnedX_one_mem_rootSubgroup ((isRoot_smul_iff w).2 hπγ)
    ((hρ.isRoot_iff γ).2 hγ) hmem, hFr]

theorem step_pinnedX_of_charTwo
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : L) :
    S.D.step (pinnedX τ L γ c) = pinnedX τ L (S.ρ γ) (c ^ S.D.q) := by
  exact step_pinnedX_of_charTwo_of_frobRootMap S.D S.frob hγ c

theorem step_rootSL2_of_charTwo_of_frobRootMap
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (D : LangDatum τ L) {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ D.q) (X : SL2 L) :
    D.step (rootSL2 τ L α X) =
      rootSL2 τ L (ρ α) (Matrix.SpecialLinearGroup.map Fr X) := by
  have h : D.step.comp (rootSL2 τ L α) =
      (rootSL2 τ L (ρ α)).comp (Matrix.SpecialLinearGroup.map Fr) :=
    MonoidHom.eq_of_eqOn_dense CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower
      fun g hg => by
        rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
        · change D.step (rootSL2 τ L α (uSL c)) =
            rootSL2 τ L (ρ α) (Matrix.SpecialLinearGroup.map Fr (uSL c))
          rw [rootSL2_uSL_of_charTwo hα,
            step_pinnedX_of_charTwo_of_frobRootMap D hρ hα, map_uSL,
            rootSL2_uSL_of_charTwo ((hρ.isRoot_iff α).2 hα), hFr]
        · change D.step (rootSL2 τ L α (vSL c)) =
            rootSL2 τ L (ρ α) (Matrix.SpecialLinearGroup.map Fr (vSL c))
          rw [rootSL2_vSL_of_charTwo hα,
            step_pinnedX_of_charTwo_of_frobRootMap D hρ (IsRoot.neg hα),
            hρ.neg_eq, map_vSL, rootSL2_vSL_of_charTwo ((hρ.isRoot_iff α).2 hα), hFr]
  exact DFunLike.congr_fun h X

theorem exists_rootSL2_sym3_mem_Γ
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hρα : S.ρ α = α ∨ S.ρ α = -α) :
    ∃ A : SL2 L, rootSL2 τ L α A ∈ S.Γ ∧ A * A = 1 ∧ (WSL * A) ^ 3 = 1 ∧ WSL * A ≠ 1 := by
  have hq' : S.D.q = 2 ^ 1 := hq.trans (pow_one 2).symm
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S hq'
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  suffices H : ∃ A : SL2 L, S.D.step (rootSL2 τ L α A) = rootSL2 τ L α A ∧ A * A = 1 ∧
      (WSL * A) ^ 3 = 1 ∧ WSL * A ≠ 1 by
    obtain ⟨A, hs, hA2, hA3, hA1⟩ := H
    refine ⟨A, langModel_mem_Γ_of_sq_eq_one S hτ hq' hAlg
      ⟨(exceptional_Lang_root_rank_one_data τ L α).2.2.2.2.1 A, hs⟩ ?_, hA2, hA3, hA1⟩
    rw [pow_two, ← map_mul, hA2, map_one]
  rcases hρα with h | h
  · refine ⟨uSL 1, ?_, ?_, ?_, ?_⟩
    · rw [rootSL2_uSL_of_charTwo (K := L) hα, step_pinnedX_one_of_charTwo S hα, h]
    · ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, Matrix.SpecialLinearGroup.coe_one]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2] <;> grind
    · rw [pow_three]
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_WSL,
        Matrix.SpecialLinearGroup.coe_one]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · intro h1
      have h00 := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L) 0 0) h1
      simp [coe_WSL, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two] at h00
  · obtain ⟨ω, hω⟩ := CFSG.CharacterTheory.SteinbergBY.FieldFour.exists_root_sq_add_self_add_one L
    have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
    have hω4 : (ω ^ 2) ^ 2 = ω := by linear_combination ω * hω3
    have hu : ∀ c, S.D.step (rootSL2 τ L α (uSL c)) = rootSL2 τ L α (vSL (c ^ 2)) := fun c => by
      rw [rootSL2_uSL_of_charTwo (K := L) hα, step_pinnedX_of_charTwo S hα, h, hq,
        rootSL2_vSL_of_charTwo (K := L) hα]
    have hv : ∀ c, S.D.step (rootSL2 τ L α (vSL c)) = rootSL2 τ L α (uSL (c ^ 2)) := fun c => by
      rw [rootSL2_vSL_of_charTwo (K := L) hα, step_pinnedX_of_charTwo S (IsRoot.neg hα),
        S.frob.neg_eq, h, neg_neg, hq, rootSL2_uSL_of_charTwo (K := L) hα]
    have hAm : ((uSL ω * vSL (ω ^ 2) * uSL ω : SL2 L) : Matrix (Fin 2) (Fin 2) L) =
        !![0, ω; ω ^ 2, 0] := by
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
    have key : vSL (ω ^ 2) * uSL ((ω ^ 2) ^ 2) * vSL (ω ^ 2) = uSL ω * vSL (ω ^ 2) * uSL ω := by
      ext i j
      rw [hAm, hω4]
      simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
    refine ⟨uSL ω * vSL (ω ^ 2) * uSL ω, ?_, ?_, ?_, ?_⟩
    · calc S.D.step (rootSL2 τ L α (uSL ω * vSL (ω ^ 2) * uSL ω))
          = rootSL2 τ L α (vSL (ω ^ 2) * uSL ((ω ^ 2) ^ 2) * vSL (ω ^ 2)) := by
            simp only [map_mul, hu, hv]
        _ = rootSL2 τ L α (uSL ω * vSL (ω ^ 2) * uSL ω) := by rw [key]
    · ext i j
      rw [Matrix.SpecialLinearGroup.coe_mul, hAm, Matrix.SpecialLinearGroup.coe_one]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
    · rw [pow_three]
      ext i j
      simp only [Matrix.SpecialLinearGroup.coe_mul, hAm, coe_WSL,
        Matrix.SpecialLinearGroup.coe_one]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
    · intro h1
      have h00 := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L) 0 0) h1
      simp only [Matrix.SpecialLinearGroup.coe_mul, hAm, coe_WSL,
        Matrix.SpecialLinearGroup.coe_one] at h00
      simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
      rcases h00 with h0 | h0
      · rw [h0] at hω
        exact one_ne_zero (by linear_combination hω - h2 : (1 : L) = 0)
      · rw [h0] at hω
        exact one_ne_zero (by linear_combination hω : (1 : L) = 0)

end CFSG.StandardType.LangRat
