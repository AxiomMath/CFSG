module

public import CFSG.LocalAnalysis.StandardType.PhanEDMFlipBasic

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.DM

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {ι : Type} {M : CoxeterMatrix ι} {W : Type} [Group W] {cs : CoxeterSystem M W}
  {C : Type} {δ : C → C → W} {w₀ : W} {t : C → C}

theorem exists_panel_dstar_lt (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsSphericalFlip cs δ w₀ t) {z : C} {j : ι}
    (hdesc : cs.length (dstar δ w₀ t z * cs.simple j) < cs.length (dstar δ w₀ t z)) :
    ∃ z' ∈ residue cs δ {j} z,
      cs.length (dstar δ w₀ t z') < cs.length (dstar δ w₀ t z) := by
  obtain ⟨j', hj'⟩ := CoxeterSystem.exists_simple_conj_w0 cs w₀ hw j
  have hw0 : w₀ * w₀ = 1 := CoxeterSystem.w0_mul_self cs w₀ hw
  have hsj' : cs.simple j' * w₀ = w₀ * cs.simple j := by
    rw [← hj', mul_assoc, hw0, mul_one]
  have hdstar : dstar δ w₀ t z = δ z (t z) * w₀ := rfl
  have hF1 : cs.length (δ z (t z) * cs.simple j') = cs.length (δ z (t z)) + 1 := by
    have h1 := hw (δ z (t z) * cs.simple j')
    have h2 := hw (δ z (t z))
    have h3 : (δ z (t z) * cs.simple j') * w₀ = dstar δ w₀ t z * cs.simple j := by
      calc (δ z (t z) * cs.simple j') * w₀ = δ z (t z) * (cs.simple j' * w₀) := by group
        _ = δ z (t z) * (w₀ * cs.simple j) := by rw [hsj']
        _ = (δ z (t z) * w₀) * cs.simple j := by group
        _ = dstar δ w₀ t z * cs.simple j := by rw [hdstar]
    have h5 : cs.length ((δ z (t z) * cs.simple j') * w₀) <
        cs.length (δ z (t z) * w₀) := by
      rw [h3, ← hdstar]
      exact hdesc
    have h4 := cs.length_mul_simple (δ z (t z)) j'
    omega
  have hF2 : cs.length (cs.simple j * δ z (t z)) =
      cs.length (δ z (t z) * cs.simple j') := by
    have hinv : (δ z (t z))⁻¹ = w₀ * δ z (t z) * w₀ := dist_inv_flip hB hw ht z
    have h2 : (cs.simple j * δ z (t z))⁻¹ = w₀ * (δ z (t z) * cs.simple j') * w₀ := by
      calc (cs.simple j * δ z (t z))⁻¹ = (δ z (t z))⁻¹ * cs.simple j := by
            rw [mul_inv_rev, CoxeterSystem.inv_simple]
        _ = w₀ * δ z (t z) * w₀ * cs.simple j := by rw [hinv]
        _ = w₀ * (δ z (t z) * (w₀ * cs.simple j)) := by group
        _ = w₀ * (δ z (t z) * (cs.simple j' * w₀)) := by rw [hsj']
        _ = w₀ * (δ z (t z) * cs.simple j') * w₀ := by group
    calc cs.length (cs.simple j * δ z (t z))
        = cs.length ((cs.simple j * δ z (t z))⁻¹) := (cs.length_inv _).symm
      _ = cs.length (w₀ * (δ z (t z) * cs.simple j') * w₀) := by rw [h2]
      _ = cs.length (δ z (t z) * cs.simple j') := CoxeterSystem.length_w0_conj cs w₀ hw _
  have hF3 : cs.length (cs.simple j * δ z (t z)) = cs.length (δ z (t z)) + 1 := by
    rw [hF2, hF1]
  obtain ⟨y, hy, u, hu, hlt⟩ := ht.panel j z
  have hyu_mem : u ∈ panel cs δ j y :=
    mem_residue_trans (mem_residue_symm hB hy) hu
  have hδyu : δ y u = cs.simple j := by
    rcases (mem_panel_iff hB).mp hyu_mem with h | h
    · exfalso
      have hyu_eq : y = u := (hB.eq_one_iff y u).mp h
      rw [hyu_eq] at hlt
      exact (lt_irrefl _) hlt
    · exact h
  have hute : δ u (t y) = δ y (t y) ∨
      δ u (t y) = cs.simple j * δ y (t y) :=
    (mul_simple_left hB hδyu (z := t y)).1
  have hF4 : cs.length (cs.simple j * δ y (t y)) < cs.length (δ y (t y)) := by
    rcases hute with h | h
    · exfalso
      rw [h] at hlt
      exact (lt_irrefl _) hlt
    · rwa [h] at hlt
  have hyz : δ z y = cs.simple j := by
    rcases (mem_panel_iff hB).mp hy with h | h
    · exfalso
      have hyz_eq : y = z := ((hB.eq_one_iff z y).mp h).symm
      rw [hyz_eq] at hF4
      rw [hF3] at hF4
      omega
    · exact h
  have hytz : δ y (t z) = cs.simple j * δ z (t z) :=
    (mul_simple_left hB hyz (z := t z)).2 (by rw [hF3])
  have htzy : δ (t z) (t y) = cs.simple j' := by
    rw [ht.dist z y, hyz, hj']
  have he_cases : δ y (t y) = cs.simple j * δ z (t z) ∨
      δ y (t y) = (cs.simple j * δ z (t z)) * cs.simple j' := by
    rcases (hB.mul_simple y (t z) (t y) j' htzy).1 with h | h
    · left; rw [h, hytz]
    · right; rw [h, hytz]
  have hde : cs.length (δ z (t z)) < cs.length (δ y (t y)) := by
    rcases he_cases with h | h
    · rw [h, hF3]
      omega
    · have h6 := cs.length_mul_simple (cs.simple j * δ z (t z)) j'
      have h7 : cs.length (δ y (t y)) = cs.length (δ z (t z)) ∨
          cs.length (δ y (t y)) = cs.length (δ z (t z)) + 2 := by
        rw [← h] at h6
        omega
      rcases h7 with h7 | h7
      · exfalso
        have h8 : cs.simple j * δ y (t y) = δ z (t z) * cs.simple j' := by
          rw [h]
          calc cs.simple j * ((cs.simple j * δ z (t z)) * cs.simple j')
              = (cs.simple j * cs.simple j) * (δ z (t z) * cs.simple j') := by group
            _ = δ z (t z) * cs.simple j' := by rw [cs.simple_mul_simple_self, one_mul]
        have h9 : cs.length (cs.simple j * δ y (t y)) < cs.length (δ z (t z)) := by
          rw [← h7]; exact hF4
        rw [h8, hF1] at h9
        omega
      · omega
  have hdsy : cs.length (dstar δ w₀ t y) < cs.length (dstar δ w₀ t z) := by
    have h1 : cs.length (δ y (t y)) + cs.length (dstar δ w₀ t y) = cs.length w₀ :=
      length_dstar_add hw y
    have h2 : cs.length (δ z (t z)) + cs.length (dstar δ w₀ t z) = cs.length w₀ :=
      length_dstar_add hw z
    omega
  exact ⟨y, hy, hdsy⟩

end CFSG.ClassicalInvolution.Phan.PhanE.DM
