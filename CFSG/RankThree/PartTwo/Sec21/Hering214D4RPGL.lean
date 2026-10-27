module

public import CFSG.Open.PGLModelDefs
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.PGLModel (projImage)
open CFSG.RankThree.PartTwo.Sec4 (glPi)
open scoped commutatorElement

theorem pgl3_four_of_commutator {K : Type} [Field K] [Finite K] (q : ℕ)
    (hsl : ∀ (h : Matrix.SpecialLinearGroup (Fin 3) K) (c : K),
      (h : Matrix (Fin 3) (Fin 3) K) ^ 3 = c • 1 →
        (∀ a : K, (h : Matrix (Fin 3) (Fin 3) K) ≠ a • 1) →
        ∃ U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K),
          CFSG.Assembly.IsElemAbelian 2 U ∧ Nat.card U = 4 ∧
            (∀ u ∈ U, h * u * h⁻¹ ∈ U) ∧ ∃ u ∈ U, h * u * h⁻¹ ≠ u)
    (z : ↥(projImage (glPi true 3 q K)))
    (hz : z ∈ ⁅(⊤ : Subgroup ↥(projImage (glPi true 3 q K))),
      (⊤ : Subgroup ↥(projImage (glPi true 3 q K)))⁆)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ W : Subgroup ↥(projImage (glPi true 3 q K)),
      CFSG.Assembly.IsElemAbelian 2 W ∧ Nat.card W = 4 ∧ (∀ w ∈ W, z * w * z⁻¹ ∈ W) ∧
        ∃ w ∈ W, z * w * z⁻¹ ≠ w := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Matrix.GeneralLinearGroup (Fin 3) K →* ↥(projImage (glPi true 3 q K)),
      ∀ g, (ψ g : Matrix.ProjGenLinGroup (Fin 3) K) = Matrix.ProjGenLinGroup.mk g :=
    ⟨Matrix.ProjGenLinGroup.mk.codRestrict (projImage (glPi true 3 q K))
      (fun g => Subgroup.mem_map.2 ⟨g, by simp [glPi], rfl⟩), fun g => rfl⟩
  have hsurj : ∀ x : ↥(projImage (glPi true 3 q K)),
      ∃ a : Matrix.GeneralLinearGroup (Fin 3) K, ψ a = x := by
    intro x
    have hx : (x : Matrix.ProjGenLinGroup (Fin 3) K) ∈
        (glPi true 3 q K).map Matrix.ProjGenLinGroup.mk := x.2
    obtain ⟨a, -, ha⟩ := Subgroup.mem_map.1 hx
    exact ⟨a, Subtype.ext ((hψ a).trans ha)⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Matrix.SpecialLinearGroup (Fin 3) K →* ↥(projImage (glPi true 3 q K)),
      ∀ s, φ s = ψ (Matrix.SpecialLinearGroup.toGL s) :=
    ⟨ψ.comp Matrix.SpecialLinearGroup.toGL, fun s => rfl⟩
  have hcomm : ∀ x y : ↥(projImage (glPi true 3 q K)), ⁅x, y⁆ ∈ φ.range := by
    intro x y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    have hdet : Matrix.GeneralLinearGroup.det ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    have hmem : ⁅a, b⁆ ∈
        (Matrix.SpecialLinearGroup.toGL (n := Fin 3) (R := K)).range := by
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
      exact hdet
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 hmem
    refine MonoidHom.mem_range.2 ⟨s, ?_⟩
    rw [← map_commutatorElement ψ, hφ, hs]
  have hle : ⁅(⊤ : Subgroup ↥(projImage (glPi true 3 q K))),
      (⊤ : Subgroup ↥(projImage (glPi true 3 q K)))⁆ ≤ φ.range :=
    Subgroup.commutator_le.2 fun x _ y _ => hcomm x y
  obtain ⟨h, hh⟩ := MonoidHom.mem_range.1 (hle hz)
  obtain ⟨c, hc⟩ : ∃ c : K, (h : Matrix (Fin 3) (Fin 3) K) ^ 3 = c • 1 := by
    have h1 : φ (h ^ 3) = 1 := by rw [map_pow, hh, hz3]
    have h2 : Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (h ^ 3)) = 1 := by
      have h3 := congrArg Subtype.val h1
      rw [hφ, hψ] at h3
      exact h3
    obtain ⟨d, hd⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1
      (Matrix.ProjGenLinGroup.mk_eq_one.1 h2)
    have hd' : (h : Matrix (Fin 3) (Fin 3) K) ^ 3 = Matrix.scalar (Fin 3) d := by
      rw [hd, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_pow]
    exact ⟨d, by rw [hd', Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
  have hns : ∀ a : K, (h : Matrix (Fin 3) (Fin 3) K) ≠ a • 1 := by
    intro a ha
    apply hz1
    rw [← hh]
    apply Subtype.ext
    rw [hφ, hψ]
    show Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL h) = 1
    rw [Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    refine ⟨a, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ha, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  obtain ⟨U, hUab, hUcard, hUnorm, hUmove⟩ := hsl h c hc hns
  obtain ⟨hUcomm, hUexp⟩ := hUab
  have hinj : ∀ u ∈ U, φ u = 1 → u = 1 := by
    intro u hu hφu
    have h1 : Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL u) = 1 := by
      have h3 := congrArg Subtype.val hφu
      rw [hφ, hψ] at h3
      exact h3
    obtain ⟨d, hd⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1
      (Matrix.ProjGenLinGroup.mk_eq_one.1 h1)
    have hum : (u : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) d := by
      rw [hd, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    have hmat : (u : Matrix (Fin 3) (Fin 3) K) ^ 2 = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hUexp u hu]
      rfl
    have hdet : (u : Matrix (Fin 3) (Fin 3) K).det = 1 := u.2
    rw [hum, ← map_pow, ← map_one (Matrix.scalar (Fin 3)), Matrix.scalar_inj] at hmat
    rw [hum, Matrix.scalar_apply, Matrix.det_diagonal] at hdet
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    have hd1 : d = 1 := by linear_combination hdet - d * hmat
    apply Subtype.ext
    simp [hum, hd1]
  obtain ⟨φU, hφU⟩ : ∃ φU : ↥U →* ↥(projImage (glPi true 3 q K)), ∀ u : ↥U, φU u = φ u :=
    ⟨φ.comp U.subtype, fun u => rfl⟩
  have hφUinj : Function.Injective φU := by
    rw [injective_iff_map_eq_one]
    intro u hu
    rw [hφU] at hu
    exact Subtype.ext (hinj u.1 u.2 hu)
  have hmemW : ∀ x : ↥(projImage (glPi true 3 q K)),
      x ∈ (⊤ : Subgroup ↥U).map φU ↔ ∃ u : ↥U, φU u = x := by
    intro x
    exact Subgroup.mem_map.trans
      ⟨fun ⟨u, _, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, Subgroup.mem_top u, hu⟩⟩
  refine ⟨(⊤ : Subgroup ↥U).map φU, ?_, ?_, ?_, ?_⟩
  · show IsMulCommutative ↥((⊤ : Subgroup ↥U).map φU) ∧
      ∀ x ∈ (⊤ : Subgroup ↥U).map φU, x ^ 2 = 1
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨u, hu⟩ := (hmemW x.1).1 x.2
      obtain ⟨v, hv⟩ := (hmemW y.1).1 y.2
      have huv : u * v = v * u := hUcomm.is_comm.comm u v
      apply Subtype.ext
      show x.1 * y.1 = y.1 * x.1
      rw [← hu, ← hv, ← map_mul, ← map_mul, huv]
    · obtain ⟨u, hu⟩ := (hmemW x).1 hx
      have hu2 : u ^ 2 = 1 := Subtype.ext (by simpa using hUexp u.1 u.2)
      rw [← hu, ← map_pow, hu2, map_one]
  · rw [Subgroup.card_map_of_injective hφUinj, Subgroup.card_top, hUcard]
  · intro w hw
    obtain ⟨u, rfl⟩ := (hmemW w).1 hw
    refine (hmemW _).2 ⟨⟨h * u.1 * h⁻¹, hUnorm u.1 u.2⟩, ?_⟩
    rw [hφU, hφU, ← hh]
    simp only [map_mul, map_inv]
  · obtain ⟨u, hu, hmove⟩ := hUmove
    refine ⟨φU ⟨u, hu⟩, (hmemW _).2 ⟨⟨u, hu⟩, rfl⟩, ?_⟩
    intro heq
    apply hmove
    have h1 : φU ⟨h * u * h⁻¹, hUnorm u hu⟩ = z * φU ⟨u, hu⟩ * z⁻¹ := by
      rw [hφU, hφU, ← hh]
      simp only [map_mul, map_inv]
    exact congrArg Subtype.val (hφUinj (h1.trans heq))

end CFSG.RankThree.PartTwo.Sec21.Hering214
