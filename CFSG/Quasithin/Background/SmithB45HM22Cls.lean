module

public import CFSG.Quasithin.Background.SmithB45HM22Core
public import CFSG.Quasithin.Background.SmithB45HM22HCls

public section

namespace CFSG.Quasithin.HM22

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
  CFSG.Quasithin.HatM22 CFSG.Quasithin.B45Mat Module Matrix

section Rep

variable {W : Type*} [AddCommGroup W] [Module FieldFour W]
  (ρ : Representation FieldFour ↥hatM22Γ₀ W)

theorem toMat_n1P : PM.toMat 6 6 n1P = gmat (genb false) := by
  rw [n1P, PM.toMat_ofMat]
  rfl

theorem toMat_n2P : PM.toMat 6 6 n2P = gmat (genb true) := by
  rw [n2P, PM.toMat_ofMat]
  rfl

theorem equivariant_of_gens (Ψ : (Fin 6 → FieldFour) ≃ₗ[FieldFour] W)
    (h : ∀ b s, Ψ (gmat (genb b) *ᵥ s) = ρ (genb b) (Ψ s)) :
    ∀ g v, Ψ (gmat g *ᵥ v) = ρ g (Ψ v) := by
  refine forall_of_gens (fun g => ∀ v, Ψ (gmat g *ᵥ v) = ρ g (Ψ v)) ?_ h ?_
  · intro v
    rw [gmat_one, Matrix.one_mulVec, map_one, Module.End.one_apply]
  · intro g k hg hk v
    rw [gmat_mul, ← Matrix.mulVec_mulVec, hg, hk, map_mul, Module.End.mul_apply]

theorem false_of_equiv_dim {n : ℕ} (Ψ : (Fin n → FieldFour) ≃ₗ[FieldFour] W)
    (hdim : finrank FieldFour W ≤ 14) (hn : 14 < n) : False := by
  have h := Ψ.finrank_eq
  rw [Module.finrank_fin_fun] at h
  omega

theorem exists_hmap [Nontrivial W] {d : ℕ} [NeZero d]
    (M : ↥hatH →* Matrix (Fin d) (Fin d) FieldFour)
    (U : Subrepresentation (ρ.comp hatH.subtype))
    (e : U.toRepresentation.Equiv (matrixBaseChange (RingHom.id FieldFour) M)) :
    ∃ ψ : (Fin d → FieldFour) →ₗ[FieldFour] W,
      (∀ (h : ↥hatH) (y : Fin d → FieldFour), ψ (M h *ᵥ y) = ρ h (ψ y)) ∧ ψ ≠ 0 := by
  refine ⟨U.toSubmodule.subtype ∘ₗ e.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · intro h y
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap h y
    have h2 : M h *ᵥ y = matrixBaseChange (RingHom.id FieldFour) M h y := by
      rw [matrixBaseChange_apply, RingHom.coe_id, Matrix.map_id]
    rw [h2]
    exact congrArg U.toSubmodule.subtype h1
  · intro h0
    have hy : (Pi.single (0 : Fin d) (1 : FieldFour) : Fin d → FieldFour) ≠ 0 := by
      intro h
      have := congrFun h 0
      simp at this
    apply hy
    have h1 := congrArg (fun f => f (Pi.single (0 : Fin d) (1 : FieldFour) : Fin d → FieldFour))
      h0
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.coe_subtype] at h1
    have h2 : e.symm.toLinearEquiv (Pi.single 0 1) = 0 := Subtype.ext h1
    exact e.symm.toLinearEquiv.injective (h2.trans (map_zero _).symm)

end Rep

theorem hatM22_classify
    (W : Type*) [AddCommGroup W] [Module FieldFour W]
    [FiniteDimensional FieldFour W] (ρ : Representation FieldFour ↥hatM22Γ₀ W)
    [hρ : ρ.IsIrreducible] (hz : ρ hatM22Z = ω • LinearMap.id)
    (hdim : finrank FieldFour W ≤ 14) :
    ∃ Ψ : (Fin 6 → FieldFour) ≃ₗ[FieldFour] W, ∀ g v, Ψ (gmat g *ᵥ v) = ρ g (Ψ v) := by
  have hnt := nontrivial_of_isIrreducible ρ
  set ρH := ρ.comp hatH.subtype with hρH
  obtain ⟨U, hU0, hUirr⟩ := exists_isIrreducible_subrepresentation ρH
  have hUz : U.toRepresentation zH = ω • LinearMap.id := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change ρ hatM22Z (u : W) = ω • (u : W)
    rw [hz]
    rfl
  have hUdim : finrank FieldFour U.toSubmodule ≤ 14 :=
    (Submodule.finrank_le U.toSubmodule).trans hdim
  obtain ⟨hf3a, hf3b, hf9⟩ := hm22_flag_checks
  rcases hatH_classify U.toSubmodule U.toRepresentation hUirr hUz hUdim with e | e | e
  ·
    obtain ⟨e⟩ := e
    obtain ⟨ψ, hψ, hψ0⟩ := exists_hmap ρ rep3a U e
    obtain ⟨i, hi, Ψ, hΨ⟩ := jh_induced ρ (fun w hw => Blk.toMat_blk3a hw) ψ hψ hψ0 hf3a
      (by decide) (by decide) (by decide) (fun i hi => by
        have : i = 0 ∨ i = 1 ∨ i = 2 := by
          have : ([0, 15, 60, 66] : List ℕ).length - 1 = 3 := rfl
          change i < 3 at hi
          omega
        rcases this with rfl | rfl | rfl
        · exact irredFam_std15
        · exact irredFam_std45
        · exact irredFam_std6)
    have hi3 : i < 3 := hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact (false_of_equiv_dim Ψ hdim (by decide)).elim
    · exact (false_of_equiv_dim Ψ hdim (by decide)).elim
    · refine ⟨Ψ, equivariant_of_gens ρ Ψ fun b s => ?_⟩
      have h1 := hΨ b s
      cases b
      · rw [← toMat_n1P]
        exact h1
      · rw [← toMat_n2P]
        exact h1
  ·
    obtain ⟨e⟩ := e
    obtain ⟨ψ, hψ, hψ0⟩ := exists_hmap ρ rep3b U e
    obtain ⟨i, hi, Ψ, hΨ⟩ := jh_induced ρ (fun w hw => Blk.toMat_blk3b hw) ψ hψ hψ0 hf3b
      (by decide) (by decide) (by decide) (fun i hi => by
        have : i = 0 ∨ i = 1 ∨ i = 2 := by
          change i < 3 at hi
          omega
        rcases this with rfl | rfl | rfl
        · exact irredFam_std45c
        · exact irredFam_std6
        · exact irredFam_std15)
    have hi3 : i < 3 := hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact (false_of_equiv_dim Ψ hdim (by decide)).elim
    · refine ⟨Ψ, equivariant_of_gens ρ Ψ fun b s => ?_⟩
      have h1 := hΨ b s
      cases b
      · rw [← toMat_n1P]
        exact h1
      · rw [← toMat_n2P]
        exact h1
    · exact (false_of_equiv_dim Ψ hdim (by decide)).elim
  ·
    obtain ⟨e⟩ := e
    obtain ⟨ψ, hψ, hψ0⟩ := exists_hmap ρ rep9 U e
    obtain ⟨i, hi, Ψ, -⟩ := jh_induced ρ (fun w hw => Blk.toMat_blk9 hw) ψ hψ hψ0 hf9
      (by decide) (by decide) (by decide) (fun i hi => by
        have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
          change i < 4 at hi
          omega
        rcases this with rfl | rfl | rfl | rfl
        · exact irredFam_std84
        · exact irredFam_std15
        · exact irredFam_std15
        · exact irredFam_std84)
    have hi4 : i < 4 := hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
      exact (false_of_equiv_dim Ψ hdim (by decide)).elim

end CFSG.Quasithin.HM22
