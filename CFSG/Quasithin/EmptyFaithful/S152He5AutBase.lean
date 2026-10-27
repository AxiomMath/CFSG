module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.Quasithin.EmptyFaithful.S152He5Borel

public section

namespace CFSG.Quasithin.He5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

abbrev InnP (n : ℕ) : Subgroup (MulAut (projectiveSL n K2)) :=
  (MulAut.conj : projectiveSL n K2 →* MulAut (projectiveSL n K2)).range

theorem center_trivial (n : ℕ) : ∀ z : projectiveSL n K2, (∀ g, g * z = z * g) → z = 1 := by
  intro z hz
  have hmem : z ∈ Subgroup.center (projectiveSL n K2) := Subgroup.mem_center_iff.mpr hz
  let e : SpecialLinearGroup (Fin n) K2 ≃* projectiveSL n K2 :=
    MulEquiv.ofBijective (proj n K2) ⟨proj_injective n, proj_surjective n K2⟩
  have h1 : (Subgroup.center (SpecialLinearGroup (Fin n) K2)).map e.toMonoidHom =
      Subgroup.center (projectiveSL n K2) := Subgroup.map_center_eq e
  rw [← h1] at hmem
  obtain ⟨s, hs, rfl⟩ := hmem
  have hs' : s ∈ scalars n K2 := by rw [scalars_eq_center]; exact hs
  rw [CFSG.LieType.SteinbergBR.BinaryLinear.scalars_eq_bot card_K2] at hs'
  have : s = 1 := Subgroup.mem_bot.mp hs'
  rw [this]
  exact map_one _

theorem conj_injective (n : ℕ) :
    Function.Injective (MulAut.conj : projectiveSL n K2 →* MulAut (projectiveSL n K2)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  rw [MonoidHom.mem_ker] at hz
  have : ∀ g, g * z = z * g := fun g => by
    have h := DFunLike.congr_fun hz g
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * z = (z * g * z⁻¹) * z := by rw [h]
      _ = z * g := by group
  exact (Subgroup.mem_bot.mpr (center_trivial n z this))

theorem units_two (u : K2ˣ) : u = 1 := by
  revert u
  decide

theorem exists_toGL_eq (n : ℕ) (A : GL (Fin n) K2) :
    ∃ g : SpecialLinearGroup (Fin n) K2, SpecialLinearGroup.toGL g = A := by
  have hdet : (A : Matrix (Fin n) (Fin n) K2).det = 1 := by
    have h := congrArg Units.val (units_two (Matrix.GeneralLinearGroup.det A))
    simpa using h
  exact ⟨⟨(A : Matrix (Fin n) (Fin n) K2), hdet⟩, Units.ext rfl⟩

theorem fieldAut_two (n : ℕ) (σ : K2 ≃+* K2) : LinearFlag.fieldAut n K2 σ = 1 := by
  have : σ = 1 := Subsingleton.elim _ _
  rw [this, map_one]

theorem conjAut_mem_inn (n : ℕ) (A : GL (Fin n) K2) : LinearFlag.conjAut n K2 A ∈ InnP n := by
  obtain ⟨g, rfl⟩ := exists_toGL_eq n A
  rw [conjAut_toGL]
  exact ⟨proj n K2 g, rfl⟩

theorem inn_le_semilinear (n : ℕ) : InnP n ≤ semilinearAutGroup n K2 := by
  rintro _ ⟨p, rfl⟩
  obtain ⟨g, rfl⟩ := proj_surjective n K2 p
  rw [← conjAut_toGL]
  exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)

theorem dualAut_not_mem_inn {n : ℕ} (hn : 3 ≤ n) : LinearFlag.dualAut n K2 ∉ InnP n := fun h =>
  ProjectivePlane.dualAut_not_mem_semilinearAutGroup hn (inn_le_semilinear n h)

theorem mem_inn_or_eq_conj_dual {n : ℕ} (hn : 3 ≤ n) (α : MulAut (projectiveSL n K2)) :
    α ∈ InnP n ∨ ∃ A : GL (Fin n) K2, α = LinearFlag.conjAut n K2 A * LinearFlag.dualAut n K2 := by
  obtain ⟨-, h⟩ := automorphism_generation (K := K2) hn
  obtain ⟨A, σ, ε, hε, hα⟩ := h α
  rw [fieldAut_two] at hα
  interval_cases ε
  · left
    rw [hα]
    simpa using (InnP n).mul_mem (conjAut_mem_inn n A) (InnP n).one_mem
  · right
    exact ⟨A, by simpa using hα⟩

theorem mul_inv_mem_inn {n : ℕ} (hn : 3 ≤ n) {y z : MulAut (projectiveSL n K2)} (hy : y ∉ InnP n)
    (hz : z ∉ InnP n) : y * z⁻¹ ∈ InnP n := by
  rcases mem_inn_or_eq_conj_dual hn y with h | ⟨A, rfl⟩
  · exact absurd h hy
  rcases mem_inn_or_eq_conj_dual hn z with h | ⟨B, rfl⟩
  · exact absurd h hz
  have hδ : LinearFlag.dualAut n K2 * LinearFlag.dualAut n K2 = 1 := (standard_automorphism_transport (K := K2) (n := n)).2.2.2.1
  have : LinearFlag.conjAut n K2 A * LinearFlag.dualAut n K2 * (LinearFlag.conjAut n K2 B * LinearFlag.dualAut n K2)⁻¹ =
      LinearFlag.conjAut n K2 A * LinearFlag.conjAut n K2 B⁻¹ := by
    have hδinv : (LinearFlag.dualAut n K2)⁻¹ = LinearFlag.dualAut n K2 := inv_eq_of_mul_eq_one_right hδ
    rw [_root_.mul_inv_rev, hδinv, mul_assoc, ← mul_assoc (LinearFlag.dualAut n K2) (LinearFlag.dualAut n K2), hδ, one_mul,
      ← map_inv]
  rw [this]
  exact (InnP n).mul_mem (conjAut_mem_inn n A) (conjAut_mem_inn n B⁻¹)

theorem index_inn_eq_two {n : ℕ} (hn : 3 ≤ n) : (InnP n).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨LinearFlag.dualAut n K2, fun b => ?_⟩
  by_cases hb : b ∈ InnP n
  · refine Or.inr ⟨hb, fun h => ?_⟩
    exact dualAut_not_mem_inn hn (by simpa using (InnP n).mul_mem ((InnP n).inv_mem hb) h)
  · refine Or.inl ⟨?_, hb⟩
    have hδinv : (LinearFlag.dualAut n K2)⁻¹ ∉ InnP n := fun h =>
      dualAut_not_mem_inn hn (by simpa using (InnP n).inv_mem h)
    simpa using mul_inv_mem_inn hn hb hδinv

end CFSG.Quasithin.He5
