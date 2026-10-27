module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelNA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.GH74.KGroups CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix

theorem s16h_ofAdd_mul_inv_mem_orth3Z_iff (a b : GF4 × GF4 × GF4) :
    Multiplicative.ofAdd a * (Multiplicative.ofAdd b)⁻¹ ∈ orth3Z ↔
      a.1 = b.1 ∧ a.2.1 = b.2.1 := by
  have hkey : Multiplicative.toAdd (Multiplicative.ofAdd a * (Multiplicative.ofAdd b)⁻¹) =
      a - b := by
    simp [toAdd_mul, toAdd_inv, sub_eq_add_neg]
  constructor
  · rintro ⟨h1, h2⟩
    rw [hkey] at h1 h2
    exact ⟨sub_eq_zero.mp (show a.1 - b.1 = 0 from h1),
      sub_eq_zero.mp (show a.2.1 - b.2.1 = 0 from h2)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [hkey]; exact sub_eq_zero.mpr h1,
      by rw [hkey]; exact sub_eq_zero.mpr h2⟩

theorem s16h_orth3ActM_eq_one_of_same_quotient (A : Matrix (Fin 2) (Fin 2) GF4)
    (h : ∀ x : GF4 × GF4 × GF4,
      (s16h_orth3ActM A x).1 = x.1 ∧ (s16h_orth3ActM A x).2.1 = x.2.1) : A = 1 := by
  decide +kernel +revert

private def s16h_w : GF4 := GF4.ofNat' 2

private def s16h_upSL : Matrix.SpecialLinearGroup (Fin 2) GF4 :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

private def s16h_downSL : Matrix.SpecialLinearGroup (Fin 2) GF4 :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

private def s16h_diagSL : Matrix.SpecialLinearGroup (Fin 2) GF4 :=
  ⟨!![s16h_w, 0; 0, s16h_w ^ 2], by rw [Matrix.det_fin_two]; decide⟩

private theorem s16h_upSL_coe :
    ((s16h_upSL : GL (Fin 2) GF4) : Matrix (Fin 2) (Fin 2) GF4) = !![1, 1; 0, 1] := rfl

private theorem s16h_downSL_coe :
    ((s16h_downSL : GL (Fin 2) GF4) : Matrix (Fin 2) (Fin 2) GF4) = !![1, 0; 1, 1] := rfl

private theorem s16h_diagSL_coe :
    ((s16h_diagSL : GL (Fin 2) GF4) : Matrix (Fin 2) (Fin 2) GF4) =
      !![s16h_w, 0; 0, s16h_w ^ 2] := rfl

private def s16h_up : ↥(StatedSL 2 GF4) :=
  ⟨(s16h_upSL : GL (Fin 2) GF4),
    StatedAPI.mem_statedSL_of_det (by rw [s16h_upSL_coe]; exact s16h_upSL.2)⟩

private def s16h_down : ↥(StatedSL 2 GF4) :=
  ⟨(s16h_downSL : GL (Fin 2) GF4),
    StatedAPI.mem_statedSL_of_det (by rw [s16h_downSL_coe]; exact s16h_downSL.2)⟩

private def s16h_diag : ↥(StatedSL 2 GF4) :=
  ⟨(s16h_diagSL : GL (Fin 2) GF4),
    StatedAPI.mem_statedSL_of_det (by rw [s16h_diagSL_coe]; exact s16h_diagSL.2)⟩

private theorem s16h_up_apply (v : GF4 × GF4 × GF4) :
    s16h_orth3AutHom s16h_up (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (v.1 + v.2.1, v.2.1, v.2.2 + v.2.1) := by
  rw [s16h_orth3AutHom_apply, s16h_orth3Act_eq]
  congr 1
  rw [show ((s16h_up : ↥(StatedSL 2 GF4)) : GL (Fin 2) GF4) = s16h_upSL from rfl, s16h_upSL_coe]
  ext <;> simp [s16h_orth3ActM]

private theorem s16h_down_apply (v : GF4 × GF4 × GF4) :
    s16h_orth3AutHom s16h_down (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (v.1, v.1 + v.2.1, v.2.2 + v.1) := by
  rw [s16h_orth3AutHom_apply, s16h_orth3Act_eq]
  congr 1
  rw [show ((s16h_down : ↥(StatedSL 2 GF4)) : GL (Fin 2) GF4) = s16h_downSL from rfl,
    s16h_downSL_coe]
  ext <;> simp [s16h_orth3ActM]

private theorem s16h_diag_apply (v : GF4 × GF4 × GF4) :
    s16h_orth3AutHom s16h_diag (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (s16h_w * v.1, s16h_w ^ 2 * v.2.1, v.2.2) := by
  rw [s16h_orth3AutHom_apply, s16h_orth3Act_eq]
  congr 1
  rw [show ((s16h_diag : ↥(StatedSL 2 GF4)) : GL (Fin 2) GF4) = s16h_diagSL from rfl,
    s16h_diagSL_coe]
  ext <;> simp [s16h_orth3ActM]

private theorem s16h_gf4_add_self (x : GF4) : x + x = 0 := by
  have h2 : (2 : GF4) = 0 := by decide
  rw [← two_mul, h2, zero_mul]

theorem s16h_orth3_centralizes_trivial {u : MulAut Orth3}
    (hc : ∀ γ ∈ orth3L, u * γ = γ * u)
    (hq : ∀ v : Orth3, u v * v⁻¹ ∈ orth3Z) : u = 1 := by
  let F : Orth3 → Orth3 := fun v => u v * v⁻¹
  have hFmul : ∀ a b : Orth3, F (a * b) = F a * F b := by
    intro a b
    show u (a * b) * (a * b)⁻¹ = (u a * a⁻¹) * (u b * b⁻¹)
    rw [map_mul, mul_inv_rev]
    ac_rfl
  have hFL : ∀ γ ∈ orth3L, ∀ v : Orth3, F (γ v) = F v := by
    intro γ hγ v
    have hcomm : u (γ v) = γ (u v) := by
      have := congrArg (fun e : MulAut Orth3 => e v) (hc γ hγ)
      simpa [MulAut.mul_apply] using this
    show u (γ v) * (γ v)⁻¹ = u v * v⁻¹
    rw [hcomm]
    have hZ : γ (u v * v⁻¹) = u v * v⁻¹ := by
      have hγ' : γ ∈ s16h_orth3AutHom.range := by
        rwa [← s16h_orth3L_eq_range]
      obtain ⟨δ, rfl⟩ := hγ'
      exact s16h_orth3Aut_fix_Z δ (hq v)
    rw [map_mul, map_inv] at hZ
    exact hZ
  have hup_mem : s16h_orth3AutHom s16h_up ∈ orth3L := by
    rw [s16h_orth3L_eq_range]
    exact ⟨s16h_up, rfl⟩
  have hdown_mem : s16h_orth3AutHom s16h_down ∈ orth3L := by
    rw [s16h_orth3L_eq_range]
    exact ⟨s16h_down, rfl⟩
  have hdiag_mem : s16h_orth3AutHom s16h_diag ∈ orth3L := by
    rw [s16h_orth3L_eq_range]
    exact ⟨s16h_diag, rfl⟩
  have hD1 : ∀ t : GF4, F (Multiplicative.ofAdd (t, 0, t)) = 1 := by
    intro t
    have hact : s16h_orth3AutHom s16h_up (Multiplicative.ofAdd (0, t, 0)) =
        Multiplicative.ofAdd (t, t, t) := by
      rw [s16h_up_apply]
      congr 1
      ext <;> simp
    have hkey : F (Multiplicative.ofAdd (t, 0, t)) *
        F (Multiplicative.ofAdd (0, t, 0)) = F (Multiplicative.ofAdd (0, t, 0)) := by
      rw [← hFmul]
      have hprod : Multiplicative.ofAdd (t, 0, t) * Multiplicative.ofAdd (0, t, 0) =
          s16h_orth3AutHom s16h_up (Multiplicative.ofAdd (0, t, 0)) := by
        have h1 : Multiplicative.ofAdd (t, 0, t) * Multiplicative.ofAdd (0, t, 0) =
            Multiplicative.ofAdd (t, t, t) := by
          rw [← ofAdd_add]
          congr 1
          ext <;> simp
        rw [h1]
        exact hact.symm
      rw [hprod]
      exact hFL _ hup_mem _
    have := congrArg (fun x => x * (F (Multiplicative.ofAdd (0, t, 0)))⁻¹) hkey
    simpa [mul_assoc] using this
  have hD2 : ∀ t : GF4, F (Multiplicative.ofAdd (0, t, t)) = 1 := by
    intro t
    have hact : s16h_orth3AutHom s16h_down (Multiplicative.ofAdd (t, 0, 0)) =
        Multiplicative.ofAdd (t, t, t) := by
      rw [s16h_down_apply]
      congr 1
      ext <;> simp
    have hkey : F (Multiplicative.ofAdd (0, t, t)) *
        F (Multiplicative.ofAdd (t, 0, 0)) = F (Multiplicative.ofAdd (t, 0, 0)) := by
      rw [← hFmul]
      have hprod : Multiplicative.ofAdd (0, t, t) * Multiplicative.ofAdd (t, 0, 0) =
          s16h_orth3AutHom s16h_down (Multiplicative.ofAdd (t, 0, 0)) := by
        have h1 : Multiplicative.ofAdd (0, t, t) * Multiplicative.ofAdd (t, 0, 0) =
            Multiplicative.ofAdd (t, t, t) := by
          rw [← ofAdd_add]
          congr 1
          ext <;> simp
        rw [h1]
        exact hact.symm
      rw [hprod]
      exact hFL _ hdown_mem _
    have := congrArg (fun x => x * (F (Multiplicative.ofAdd (t, 0, 0)))⁻¹) hkey
    simpa [mul_assoc] using this
  have hD3 : ∀ x y z : GF4, F (Multiplicative.ofAdd (s16h_w * x, s16h_w ^ 2 * y, z)) =
      F (Multiplicative.ofAdd (x, y, z)) := by
    intro x y z
    have hact : s16h_orth3AutHom s16h_diag (Multiplicative.ofAdd (x, y, z)) =
        Multiplicative.ofAdd (s16h_w * x, s16h_w ^ 2 * y, z) := s16h_diag_apply (x, y, z)
    rw [← hact]
    exact hFL _ hdiag_mem _
  let ψ : GF4 → Orth3 := fun t => F (Multiplicative.ofAdd (0, 0, t))
  have hψadd : ∀ a b : GF4, ψ (a + b) = ψ a * ψ b := by
    intro a b
    show F (Multiplicative.ofAdd (0, 0, a + b)) =
      F (Multiplicative.ofAdd (0, 0, a)) * F (Multiplicative.ofAdd (0, 0, b))
    rw [← hFmul]
    congr 1
    rw [← ofAdd_add]
    congr 1
    ext <;> simp
  have hψ0 : ψ 0 = 1 := by
    show F (Multiplicative.ofAdd (0, 0, 0)) = 1
    rw [show Multiplicative.ofAdd (0, 0, 0) = (1 : Orth3) from rfl]
    show u 1 * 1⁻¹ = 1
    simp
  have hFdecomp : ∀ x y z : GF4, F (Multiplicative.ofAdd (x, y, z)) =
      F (Multiplicative.ofAdd (x, 0, 0)) * F (Multiplicative.ofAdd (0, y, 0)) *
        F (Multiplicative.ofAdd (0, 0, z)) := by
    intro x y z
    have hdecomp : (Multiplicative.ofAdd (x, y, z) : Orth3) =
        Multiplicative.ofAdd (x, 0, 0) * Multiplicative.ofAdd (0, y, 0) *
          Multiplicative.ofAdd (0, 0, z) := by
      rw [← ofAdd_add, ← ofAdd_add]
      congr 1
      ext <;> simp
    rw [hdecomp, hFmul, hFmul]
  have hFx : ∀ x : GF4, F (Multiplicative.ofAdd (x, 0, 0)) = ψ x := by
    intro x
    have hsplit : (Multiplicative.ofAdd (x, 0, 0) : Orth3) =
        Multiplicative.ofAdd (x, 0, x) * Multiplicative.ofAdd (0, 0, x) := by
      rw [← ofAdd_add]
      congr 1
      ext <;> simp [s16h_gf4_add_self]
    rw [hsplit, hFmul, hD1 x, one_mul]
  have hFy : ∀ y : GF4, F (Multiplicative.ofAdd (0, y, 0)) = ψ y := by
    intro y
    have hsplit : (Multiplicative.ofAdd (0, y, 0) : Orth3) =
        Multiplicative.ofAdd (0, y, y) * Multiplicative.ofAdd (0, 0, y) := by
      rw [← ofAdd_add]
      congr 1
      ext <;> simp [s16h_gf4_add_self]
    rw [hsplit, hFmul, hD2 y, one_mul]
  have hFψ : ∀ x y z : GF4, F (Multiplicative.ofAdd (x, y, z)) = ψ x * ψ y * ψ z := by
    intro x y z
    rw [hFdecomp, hFx, hFy]
  have hD3ψ : ∀ x y : GF4, ψ (s16h_w * x) * ψ (s16h_w ^ 2 * y) = ψ x * ψ y := by
    intro x y
    have := hD3 x y 0
    rw [hFψ (s16h_w * x) (s16h_w ^ 2 * y) 0, hFψ x y 0, hψ0, mul_one, mul_one] at this
    exact this
  have hψ2 : ψ s16h_w = ψ 1 := by
    simpa [hψ0] using hD3ψ 1 0
  have hψ2sq : ψ (s16h_w ^ 2) = ψ 1 := by
    simpa [hψ0] using hD3ψ 0 1
  have hψ1 : ψ 1 = 1 := by
    have hsum : ψ (s16h_w ^ 2) = ψ 1 * ψ s16h_w := by
      have h12 : s16h_w ^ 2 = 1 + s16h_w := by decide
      rw [h12, hψadd]
    rw [hψ2sq, hψ2] at hsum
    have := congrArg (fun x => (ψ 1)⁻¹ * x) hsum
    simpa [mul_assoc] using this.symm
  have hψ : ∀ t : GF4, ψ t = 1 := by
    have hcases : ∀ t : GF4, t = 0 ∨ t = 1 ∨ t = s16h_w ∨ t = s16h_w ^ 2 := by decide
    intro t
    rcases hcases t with h | h | h | h <;> simp [h, hψ0, hψ1, hψ2, hψ2sq]
  have hF1 : ∀ v : Orth3, F v = 1 := by
    intro v
    rw [show v = Multiplicative.ofAdd (Multiplicative.toAdd v) from (ofAdd_toAdd v).symm,
      hFψ (Multiplicative.toAdd v).1 (Multiplicative.toAdd v).2.1
        (Multiplicative.toAdd v).2.2]
    simp [hψ]
  apply MulEquiv.ext
  intro v
  show u v = v
  exact mul_inv_eq_one.mp (show u v * v⁻¹ = 1 from hF1 v)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
