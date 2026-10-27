module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IJ

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open Matrix CFSG.Quasithin.E2P.Asc80
open scoped MatrixGroups commutatorElement

variable {p : ℕ} [Fact p.Prime]

theorem commutator_leviC (hp5 : 5 ≤ p) : ⁅leviC p, leviC p⁆ = leviY p := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [← leviPsi_range] at hx hy
    obtain ⟨A, rfl⟩ := hx
    obtain ⟨B, rfl⟩ := hy
    rw [← map_commutatorElement]
    have hd : Matrix.GeneralLinearGroup.det ⁅A, B⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    have hdet : ((⁅A, B⁆ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
      have := congrArg Units.val hd
      rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
    refine ⟨(⟨_, hdet⟩ : SL(2, ZMod p)), ?_⟩
    show leviPsi p (Matrix.SpecialLinearGroup.toGL ⟨_, hdet⟩) = leviPsi p ⁅A, B⁆
    congr 1
    exact Units.ext rfl
  · have hperf : commutator SL(2, ZMod p) = ⊤ :=
      (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card (ZMod p)
        (by rw [Nat.card_zmod]; omega)).commutator_eq_top
    calc leviY p = (⊤ : Subgroup SL(2, ZMod p)).map (ofSL2 p) := MonoidHom.range_eq_map _
      _ = (⁅(⊤ : Subgroup SL(2, ZMod p)), ⊤⁆ : Subgroup SL(2, ZMod p)).map (ofSL2 p) := by
          rw [← commutator_def, hperf]
      _ = ⁅(⊤ : Subgroup SL(2, ZMod p)).map (ofSL2 p),
            (⊤ : Subgroup SL(2, ZMod p)).map (ofSL2 p)⁆ := Subgroup.map_commutator _ _ _
      _ ≤ ⁅leviC p, leviC p⁆ := by
          rw [← MonoidHom.range_eq_map]
          exact Subgroup.commutator_mono leviY_le_leviC leviY_le_leviC

theorem mem_centralizer_leviY (hp2 : p ≠ 2) {g : PSL3 p}
    (hg : g ∈ Subgroup.centralizer (leviY p : Set (PSL3 p))) :
    ∃ u : (ZMod p)ˣ, g = leviPsi p (Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
  have hgz : g * zc p = zc p * g :=
    (Subgroup.mem_centralizer_iff.mp hg (zc p) zc_mem_leviY).symm
  obtain ⟨A, rfl⟩ : g ∈ (leviPsi p).range := by
    rw [leviPsi_range]
    exact mem_leviC_of_commute_z hp2 hgz
  have hA : ∀ S : SL(2, ZMod p), A * Matrix.SpecialLinearGroup.toGL S =
      Matrix.SpecialLinearGroup.toGL S * A := fun S =>
    commute_of_piL_commute (Subgroup.mem_centralizer_iff.mp hg (ofSL2 p S) ⟨S, rfl⟩).symm
  obtain ⟨u, hu⟩ := eq_scalar_of_commute_sl2 hA
  exact ⟨u, by rw [hu]⟩

theorem centralizer_leviY_comm (hp2 : p ≠ 2) {a b : PSL3 p}
    (ha : a ∈ Subgroup.centralizer (leviY p : Set (PSL3 p)))
    (hb : b ∈ Subgroup.centralizer (leviY p : Set (PSL3 p))) : a * b = b * a := by
  obtain ⟨u, rfl⟩ := mem_centralizer_leviY hp2 ha
  obtain ⟨v, rfl⟩ := mem_centralizer_leviY hp2 hb
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm u v]

theorem units_eq_one_or_neg_one {w : (ZMod p)ˣ} (hw : w * w = 1) : w = 1 ∨ w = -1 := by
  have h : ((w : ZMod p) - 1) * ((w : ZMod p) + 1) = 0 := by
    have := congrArg Units.val hw
    simp only [Units.val_mul, Units.val_one] at this
    linear_combination this
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (Units.ext (by simpa using (by linear_combination h : (w : ZMod p) = 1)))
  · exact Or.inr (Units.ext (by simpa using (by linear_combination h : (w : ZMod p) = -1)))

theorem leviPsi_scalar_mul {μ : (ZMod p)ˣ} (hμ : μ ^ 3 = 1) (A : GL (Fin 2) (ZMod p)) :
    leviPsi p (Matrix.GeneralLinearGroup.scalar (Fin 2) μ * A) = leviPsi p A := by
  rw [map_mul, leviPsi_scalar_eq_one hμ, one_mul]

theorem exists_mul_self_eq_one {A : GL (Fin 2) (ZMod p)} (hA : leviPsi p A * leviPsi p A = 1) :
    ∃ B : GL (Fin 2) (ZMod p), leviPsi p B = leviPsi p A ∧ B * B = 1 ∧
      ∃ μ : (ZMod p)ˣ, μ ^ 3 = 1 ∧ B = Matrix.GeneralLinearGroup.scalar (Fin 2) μ * A := by
  rw [← map_mul, leviPsi_eq_one_iff] at hA
  obtain ⟨μ, hμ, hAA⟩ := hA
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) μ * A, leviPsi_scalar_mul hμ A, ?_,
    μ, hμ, rfl⟩
  have hc : ∀ X : GL (Fin 2) (ZMod p), Matrix.GeneralLinearGroup.scalar (Fin 2) μ * X =
      X * Matrix.GeneralLinearGroup.scalar (Fin 2) μ := fun X => by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute (μ : ZMod p) (fun _ => Commute.all _ _) _).eq
  calc Matrix.GeneralLinearGroup.scalar (Fin 2) μ * A * (Matrix.GeneralLinearGroup.scalar
        (Fin 2) μ * A) = Matrix.GeneralLinearGroup.scalar (Fin 2) (μ * μ) * (A * A) := by
        rw [map_mul, mul_assoc, ← mul_assoc A, ← hc A]
        group
    _ = Matrix.GeneralLinearGroup.scalar (Fin 2) (μ ^ 3) := by
        rw [hAA, ← map_mul, pow_three, mul_assoc]
    _ = 1 := by rw [hμ, map_one]

theorem eq_zc_of_mem_centralizer_leviY (hp2 : p ≠ 2) {c : PSL3 p}
    (hc : c ∈ Subgroup.centralizer (leviY p : Set (PSL3 p))) (hc2 : orderOf c = 2) :
    c = zc p := by
  obtain ⟨u, rfl⟩ := mem_centralizer_leviY hp2 hc
  have hsq : leviPsi p (Matrix.GeneralLinearGroup.scalar (Fin 2) u) *
      leviPsi p (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
    have h := pow_orderOf_eq_one (leviPsi p (Matrix.GeneralLinearGroup.scalar (Fin 2) u))
    rwa [hc2, pow_two] at h
  obtain ⟨B, hB, hBB, μ, -, rfl⟩ := exists_mul_self_eq_one hsq
  rw [← map_mul] at hBB hB
  have hw := units_eq_one_or_neg_one (w := μ * u) (by
    have := congrArg (fun X : GL (Fin 2) (ZMod p) => (X : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0)
      hBB
    apply Units.ext
    simpa [Matrix.scalar_apply] using this)
  rcases hw with hw | hw
  · exfalso
    rw [hw, map_one, map_one] at hB
    rw [← hB, orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  · rw [← hB, hw, ← leviPsi_neg_one]
    congr 1
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem ne_mul_of_leviY (hp4 : p % 4 = 3) {x : PSL3 p} (hx2 : orderOf x = 2) (hxz : x ≠ zc p)
    {s c : PSL3 p} (hs : s ∈ leviY p) (hc : c ∈ Subgroup.centralizer (leviY p : Set (PSL3 p))) :
    x ≠ s * c := by
  have hp2 : p ≠ 2 := by omega
  rintro rfl
  obtain ⟨S, rfl⟩ := hs
  obtain ⟨u, rfl⟩ := mem_centralizer_leviY hp2 hc
  rw [ofSL2_eq_leviPsi, ← map_mul] at hx2 hxz
  set A := Matrix.SpecialLinearGroup.toGL S * Matrix.GeneralLinearGroup.scalar (Fin 2) u with hA
  have hsq : leviPsi p A * leviPsi p A = 1 := by
    have h := pow_orderOf_eq_one (leviPsi p A)
    rwa [hx2, pow_two] at h
  obtain ⟨B, hB, hBB, μ, -, rfl⟩ := exists_mul_self_eq_one hsq
  have hB1 : Matrix.GeneralLinearGroup.scalar (Fin 2) μ * A ≠ 1 := fun h => by
    rw [h, map_one] at hB
    rw [← hB, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  have hB2 : Matrix.GeneralLinearGroup.scalar (Fin 2) μ * A ≠ -1 := fun h => hxz (by
    rw [← hB, h, leviPsi_neg_one])
  have hdet := det_eq_neg_one_of_mul_self hBB hB1 hB2
  have hdet' : ((Matrix.GeneralLinearGroup.scalar (Fin 2) μ * A :
      GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).det = ((μ : ZMod p) * u) ^ 2 := by
    rw [hA, Units.val_mul, Units.val_mul, det_mul, det_mul,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, S.2]
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ring
  have hsq' : IsSquare (-1 : ZMod p) := ⟨(μ : ZMod p) * u, by rw [← hdet, hdet', pow_two]⟩
  exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq') hp4

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
