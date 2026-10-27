module

public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Std

public section

namespace CFSG.Quasithin.Sp4

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
open CFSG.QuasithinUnique.Lin2.Five

variable {F : Type} [Field F]

@[expose] noncomputable def vP (b c : F) : StatedProj (StatedSp 2 F) := proj 2 F (tauS b c 0)

@[expose] def vAct (l₁ l₂ : F) (σ : F ≃+* F) (ε : Bool) (x : F × F) : F × F :=
  if ε then (l₁ * σ x.2 ^ 2, l₂ * σ x.1) else (l₁ * σ x.1, l₂ * σ x.2)

theorem vP_mul (b c b' c' : F) : vP b c * vP b' c' = vP (b + b') (c + c') := by
  rw [vP, vP, vP, ← map_mul, tauS_mul_tauS, add_zero]

theorem vP_zero : vP (0 : F) 0 = 1 := by
  rw [vP, tauS_zero, map_one]

variable [Finite F] [CharP F 2]

omit [Finite F] in
theorem proj_injective : Function.Injective (proj 2 F) := fun _ _ h =>
  (projEquiv F).injective h

omit [Finite F] in
theorem vP_injective {b c b' c' : F} (h : vP b c = vP b' c') : b = b' ∧ c = c' := by
  have := tauS_injective (proj_injective h)
  exact ⟨this.1, this.2.1⟩

omit [Finite F] [CharP F 2] in
theorem vP_mem_projUnipotent (b c : F) : vP b c ∈ projUnipotent 2 F :=
  ⟨tauS b c 0, tauS_mem_unipotent _ _ _, rfl⟩

omit [Finite F] in
theorem conj_vP {u : StatedSp 2 F} (hu : u ∈ unipotent 2 F) (s : Fin 2 → Fˣ) (b c : F) :
    MulAut.conj (proj 2 F (u * SymplecticTorusWeyl.torusHom s)) (vP b c) =
      vP ((s 0 : F) ^ 2 * b) ((s 0 : F) * (s 1 : F) * c) := by
  have h1 : SymplecticTorusWeyl.torusHom s * tauS b c 0 *
      (SymplecticTorusWeyl.torusHom s)⁻¹ =
      tauS ((s 0 : F) ^ 2 * b) ((s 0 : F) * (s 1 : F) * c) 0 := by
    rw [mul_inv_eq_iff_eq_mul, torusHom_mul_tauS]
    simp
  have h2 : u * tauS ((s 0 : F) ^ 2 * b) ((s 0 : F) * (s 1 : F) * c) 0 * u⁻¹ =
      tauS ((s 0 : F) ^ 2 * b) ((s 0 : F) * (s 1 : F) * c) 0 := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (tauS_zero_mul_comm hu _ _).symm
  rw [MulAut.conj_apply, vP, vP, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [mul_inv_rev]
  calc u * SymplecticTorusWeyl.torusHom s * tauS b c 0 *
        ((SymplecticTorusWeyl.torusHom s)⁻¹ * u⁻¹)
      = u * (SymplecticTorusWeyl.torusHom s * tauS b c 0 *
          (SymplecticTorusWeyl.torusHom s)⁻¹) * u⁻¹ := by group
    _ = _ := by rw [h1, h2]

omit [Finite F] [CharP F 2] in
theorem fieldAut_vP (σ : F ≃+* F) (b c : F) : fieldAut 2 F σ (vP b c) = vP (σ b) (σ c) := by
  rw [vP, fieldAut_proj, fieldSp_tauS, map_zero]
  rfl

theorem tauAut_vP (b c : F) : tauAut (vP b c) = vP (c ^ 2) b := by
  rw [vP, tauAut_proj, tauSp_tauS_zero]
  rfl

theorem standard_action_vP {u : StatedSp 2 F} (hu : u ∈ unipotent 2 F) (s : Fin 2 → Fˣ)
    (σ : F ≃+* F) (ε : Bool) (x : F × F) :
    (MulAut.conj (proj 2 F (u * SymplecticTorusWeyl.torusHom s)) * fieldAut 2 F σ *
        (if ε then tauAut else 1) : MulAut (StatedProj (StatedSp 2 F))) (vP x.1 x.2) =
      vP (vAct ((s 0 : F) ^ 2) ((s 0 : F) * (s 1 : F)) σ ε x).1
        (vAct ((s 0 : F) ^ 2) ((s 0 : F) * (s 1 : F)) σ ε x).2 := by
  rw [MulAut.mul_apply, MulAut.mul_apply]
  cases ε
  · simp only [Bool.false_eq_true, ite_false, vAct, MulAut.one_apply, fieldAut_vP, conj_vP hu]
  · simp only [ite_true, vAct, tauAut_vP, fieldAut_vP, conj_vP hu, map_pow]

omit [Finite F] [CharP F 2] in
theorem eq_of_vAct_eq_id {l₁ l₂ : F} {σ : F ≃+* F} {ε : Bool}
    (h : ∀ x : F × F, vAct l₁ l₂ σ ε x = x) :
    ε = false ∧ l₁ = 1 ∧ l₂ = 1 ∧ σ = 1 := by
  cases ε
  · have h10 := h (1, 0)
    have h01 := h (0, 1)
    simp only [vAct, Bool.false_eq_true, ite_false, map_one, map_zero, mul_one, mul_zero,
      Prod.mk.injEq, and_true, true_and] at h10 h01
    refine ⟨rfl, h10, h01, ?_⟩
    ext b
    have hb := h (b, 0)
    simp only [vAct, Bool.false_eq_true, ite_false, map_zero, mul_zero, Prod.mk.injEq,
      and_true] at hb
    rw [h10, one_mul] at hb
    exact hb
  · have h10 := h (1, 0)
    simp [vAct] at h10

theorem exists_vAct {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card F = 2 ^ n)
    {α : MulAut (StatedProj (StatedSp 2 F))}
    (hα : ∀ x, α x ∈ projUnipotent 2 F ↔ x ∈ projUnipotent 2 F) :
    ∃ (l₁ l₂ : F) (σ : F ≃+* F) (ε : Bool), l₁ ≠ 0 ∧ l₂ ≠ 0 ∧
      (∀ x : F × F, α (vP x.1 x.2) = vP (vAct l₁ l₂ σ ε x).1 (vAct l₁ l₂ σ ε x).2) ∧
      ((∀ x : F × F, vAct l₁ l₂ σ ε x = x) →
        ∃ u ∈ unipotent 2 F, α = MulAut.conj (proj 2 F u)) := by
  obtain ⟨σ, u, s, ε, hu, rfl⟩ := exists_standard_form hn hK hα
  refine ⟨(s 0 : F) ^ 2, (s 0 : F) * (s 1 : F), σ, ε, pow_ne_zero 2 (s 0).ne_zero,
    mul_ne_zero (s 0).ne_zero (s 1).ne_zero, standard_action_vP hu s σ ε, fun hid => ?_⟩
  obtain ⟨rfl, h1, h2, rfl⟩ := eq_of_vAct_eq_id hid
  have hs0 : s 0 = 1 := Units.ext (by
    by_contra h
    exact sq_ne_one_of_charTwo h h1)
  have hs1 : s 1 = 1 := Units.ext (by
    have h3 := h2
    rw [hs0] at h3
    simpa using h3)
  have hs : s = 1 := by
    funext i
    fin_cases i
    · exact hs0
    · exact hs1
  refine ⟨u, hu, ?_⟩
  subst hs
  simp

end CFSG.Quasithin.Sp4
