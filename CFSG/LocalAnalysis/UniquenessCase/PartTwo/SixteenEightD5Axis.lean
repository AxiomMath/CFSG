module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Frame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
  {K : Fin 4 → Subgroup (MulAut W)} {Z : Fin 4 → Subgroup W}

private theorem s16e_d5_comp_inv_toMonoidHom (g : MulAut W) :
    g.toMonoidHom.comp (g⁻¹).toMonoidHom = MonoidHom.id W := by
  ext v
  simp [MulAut.mul_apply, MulAut.inv_def]

private theorem s16e_d5_map_inv_map (U : Subgroup W) (g : MulAut W) :
    (U.map (g⁻¹).toMonoidHom).map g.toMonoidHom = U := by
  rw [Subgroup.map_map, s16e_d5_comp_inv_toMonoidHom, Subgroup.map_id]

theorem s16e_d5_axis_conj (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)}
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W))) {a : MulAut W} (haA : a ∈ A)
    (haC : a ∈ Subgroup.centralizer (L : Set (MulAut W))) (ha1 : a ≠ 1) {i : Fin 4}
    (hai : ∀ k, k ≠ i → ∀ z ∈ Z k, a z = z) {g : MulAut W} (hgA : g ∈ A) {j : Fin 4}
    (hgj : (Z i).map g.toMonoidHom = Z j) :
    g * a * g⁻¹ ∈ A ∧ g * a * g⁻¹ ∈ Subgroup.centralizer (L : Set (MulAut W)) ∧
      g * a * g⁻¹ ≠ 1 ∧ ∀ k, k ≠ j → ∀ z ∈ Z k, (g * a * g⁻¹) z = z := by
  have hginv : g⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) := hLn g⁻¹ (A.inv_mem hgA)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact A.mul_mem (A.mul_mem hgA haA) (A.inv_mem hgA)
  · rw [Subgroup.mem_centralizer_iff] at haC ⊢
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have h := (Subgroup.mem_normalizer_iff.mp hginv l).mp hl
      simpa [inv_inv] using h
    have hcomm : (g⁻¹ * l * g) * a = a * (g⁻¹ * l * g) := haC (g⁻¹ * l * g) hl'
    calc l * (g * a * g⁻¹) = g * ((g⁻¹ * l * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * l * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * a * g⁻¹) * l := by group
  · intro hb
    apply ha1
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [hb]
      _ = 1 := by group
  · intro k hkj z hz
    obtain ⟨k', hk'⟩ := s16e_d5_Frame.perm hfr hginv k
    have hz' : g⁻¹ z ∈ Z k' := by
      rw [← hk']
      exact Subgroup.mem_map_of_mem (g⁻¹).toMonoidHom hz
    have hk'ne : k' ≠ i := by
      intro hk'i
      apply hkj
      apply hfr.Z_inj
      calc Z k = ((Z k).map (g⁻¹).toMonoidHom).map g.toMonoidHom :=
            (s16e_d5_map_inv_map (Z k) g).symm
        _ = (Z i).map g.toMonoidHom := by rw [hk', hk'i]
        _ = Z j := hgj
    have hafix : a (g⁻¹ z) = g⁻¹ z := hai k' hk'ne (g⁻¹ z) hz'
    calc (g * a * g⁻¹) z = g (a (g⁻¹ z)) := by rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = g (g⁻¹ z) := by rw [hafix]
      _ = z := by simpa [MulAut.inv_def] using g.apply_symm_apply z

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
