module

public import CFSG.RankThree.PartTwo.KFacts.K72FixL2

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts3D4

open CFSG.RankThree.PartTwo.KFacts

theorem exists_involution_psl2 (F : Type*) [Field F] :
    ∃ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, x ≠ 1 ∧ x ^ 2 = 1 := by
  have hdet : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    ring
  let w : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![0, 1; -1, 0], hdet⟩
  refine ⟨QuotientGroup.mk w, ?_, ?_⟩
  · intro h
    rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff] at h
    obtain ⟨r, -, hr⟩ := h
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hr
    simp [w] at this
  · rw [sq, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff,
      Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by norm_num, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show _ = !![0, 1; -1, 0] * !![0, 1; -1, 0]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

section Restrict

variable {X : Type*} [Group X]

@[expose] def restrictAut (τ : MulAut X) (H : Subgroup X) (hH : H.map τ.toMonoidHom = H) :
    MulAut H :=
  (τ.subgroupMap H).trans (MulEquiv.subgroupCongr hH)

theorem coe_restrictAut_pow_apply (τ : MulAut X) (H : Subgroup X)
    (hH : H.map τ.toMonoidHom = H) (n : ℕ) (x : H) :
    ((restrictAut τ H hH ^ n) x : X) = (τ ^ n) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih]
    rfl

theorem conj_injective_of_center_eq_bot {M : Type*} [Group M] (hZ : Subgroup.center M = ⊥) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have hmem : u ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : MulAut.conj u g = g := by rw [hu]; rfl
    rw [MulAut.conj_apply] at h1
    calc g * u = u * g * u⁻¹ * u := by rw [h1]
      _ = u * g := by group
  rw [hZ] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem exists_fixed_involution_or_eq_conj {F : Type} [Field F] [Finite F] {τ : MulAut X}
    (hτ3 : τ ^ 3 = 1) {H : Subgroup X} (hH : H.map τ.toMonoidHom = H)
    (ψ : H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    (∃ v ∈ H, v ≠ 1 ∧ v ^ 2 = 1 ∧ τ v = v) ∨
      ∃ k ∈ H, k ^ 3 = 1 ∧ τ k = k ∧ ∀ x ∈ H, τ x = k * x * k⁻¹ := by
  have hr3 : restrictAut τ H hH ^ 3 = 1 := by
    ext x
    rw [coe_restrictAut_pow_apply, hτ3]
    rfl
  set α : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    MulAut.congr ψ (restrictAut τ H hH) with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hr3, map_one]
  by_cases hin : IsInnerAut α
  · right
    obtain ⟨y, hy⟩ := hin
    have hy3 : y ^ 3 = 1 :=
      conj_injective_of_center_eq_bot (CFSG.GorensteinWalter.psl2_center_eq_bot F)
        (by rw [map_pow, hy, hα3, map_one])
    have hrk : restrictAut τ H hH = MulAut.conj (ψ.symm y) := by
      apply (MulAut.congr ψ).injective
      rw [congr_mulAutConj, MulEquiv.apply_symm_apply, ← hα]
      exact hy.symm
    have hact : ∀ x : H, τ x = (ψ.symm y : X) * x * (ψ.symm y : X)⁻¹ := by
      intro x
      have h1 := congrArg (fun f : MulAut H => ((f x : H) : X)) hrk
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      exact h1
    refine ⟨(ψ.symm y : X), (ψ.symm y).2, ?_, ?_, fun x hx => hact ⟨x, hx⟩⟩
    · rw [← Subgroup.coe_pow, ← map_pow, hy3, map_one, Subgroup.coe_one]
    · rw [hact, mul_inv_cancel_right]
  · left
    obtain ⟨ρ, -, ⟨e⟩⟩ := exists_eqLocus_mulEquiv_psl2 hα3 hin
    obtain ⟨z, hz1, hz2⟩ := exists_involution_psl2 (CFSG.GH74.GLS.IVK.fixedField ρ)
    set y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := (e.symm z).1 with hy
    have hyα : α y = y := (e.symm z).2
    have hy1 : y ≠ 1 := by
      intro h
      apply hz1
      have h2 : e.symm z = 1 := Subtype.ext h
      have h3 := congrArg e h2
      rwa [MulEquiv.apply_symm_apply, map_one] at h3
    have hy2 : y ^ 2 = 1 := by
      rw [hy, ← Subgroup.coe_pow, ← map_pow, hz2, map_one, Subgroup.coe_one]
    have hfix : restrictAut τ H hH (ψ.symm y) = ψ.symm y := by
      apply ψ.injective
      rw [MulEquiv.apply_symm_apply]
      exact hyα
    refine ⟨(ψ.symm y : X), (ψ.symm y).2, ?_, ?_, congrArg Subtype.val hfix⟩
    · intro h
      apply hy1
      have h2 : ψ.symm y = 1 := Subtype.ext h
      simpa using congrArg ψ h2
    · rw [← Subgroup.coe_pow, ← map_pow, hy2, map_one, Subgroup.coe_one]

end Restrict

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts3D4
