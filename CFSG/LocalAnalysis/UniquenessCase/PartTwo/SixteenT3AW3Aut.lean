module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Perm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

variable {T : Type} [CommGroup T] {U : Subgroup T}

theorem s16t_w3_map_one : U.map (1 : MulAut T).toMonoidHom = U := by
  ext x
  simp

theorem s16t_w3_map_mul (a b : MulAut T) :
    U.map (a * b).toMonoidHom = (U.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem s16t_w3_map_inv {a : MulAut T} (ha : U.map a.toMonoidHom = U) :
    U.map a⁻¹.toMonoidHom = U := by
  conv_lhs => rw [← ha]
  rw [← s16t_w3_map_mul, inv_mul_cancel, s16t_w3_map_one]

theorem s16t_w3_mem_stabSub {g : MulAut T} (hg : U.map g.toMonoidHom = U) : g ∈ stabSub U := by
  intro u
  constructor
  · intro hu
    rw [← hg] at hu
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 hu
    have hvu' : g v = g u := hvu
    exact g.injective hvu' ▸ hv
  · intro hu
    rw [← hg]
    exact Subgroup.mem_map_of_mem g.toMonoidHom hu

theorem s16t_w3_conj_apply (f v : MulAut T) (y : T) : (f * v * f⁻¹) (f y) = f (v y) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]

theorem s16t_w3_conj_fix {f v : MulAut T} (hv : ∀ u ∈ U, v u = u) :
    ∀ y ∈ U.map f.toMonoidHom, (f * v * f⁻¹) y = y := by
  rintro _ ⟨z, hz, rfl⟩
  exact (s16t_w3_conj_apply f v z).trans (congrArg f (hv z hz))

private theorem s16t_w3_perm_pow_six : ∀ π : Equiv.Perm (Fin 3), π ^ 6 = 1 := by
  decide

private theorem s16t_w3_perm_comm :
    ∀ π σ : Equiv.Perm (Fin 3), π ^ 3 = 1 → σ ^ 3 = 1 → π * σ = σ * π := by
  decide

private theorem s16t_w3_perm_cube_mul :
    ∀ π σ : Equiv.Perm (Fin 3), (π * σ) ^ 3 = 1 ↔ (π ^ 3 = 1 ↔ σ ^ 3 = 1) := by
  decide

private theorem s16t_w3_perm_conj : ∀ π ω : Equiv.Perm (Fin 3), ω ^ 3 = 1 →
    (π ^ 3 = 1 → π * ω * π⁻¹ = ω) ∧ (¬ π ^ 3 = 1 → π * ω * π⁻¹ = ω⁻¹) := by
  decide

private theorem s16t_w3_r_eq_iff {r : ↥(stabSub U) →* Equiv.Perm (Fin 3)}
    (hr : ∀ g : ↥(stabSub U), r g = 1 ↔ ∀ u ∈ U, (g : MulAut T) u = u) (g h : ↥(stabSub U)) :
    r g = r h ↔ ∀ u ∈ U, (g : MulAut T) u = (h : MulAut T) u := by
  constructor
  · intro hgh u hu
    have h1 : r (h⁻¹ * g) = 1 := by rw [map_mul, map_inv, hgh, inv_mul_cancel]
    have h2 := (hr _).1 h1 u hu
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, MulAut.inv_apply] at h2
    exact (MulEquiv.symm_apply_eq _).1 h2
  · intro hgh
    have h1 : r (h⁻¹ * g) = 1 := by
      rw [hr]
      intro u hu
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, MulAut.inv_apply]
      exact (MulEquiv.symm_apply_eq _).2 (hgh u hu)
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm

private theorem s16t_w3_cube_iff {r : ↥(stabSub U) →* Equiv.Perm (Fin 3)}
    (hr : ∀ g : ↥(stabSub U), r g = 1 ↔ ∀ u ∈ U, (g : MulAut T) u = u) (g : ↥(stabSub U)) :
    (∀ u ∈ U, ((g : MulAut T) ^ 3) u = u) ↔ r g ^ 3 = 1 := by
  rw [← map_pow, hr]
  simp

theorem s16t_w3_pow_six (hU : Nat.card ↥U = 4) {g : MulAut T} (hg : U.map g.toMonoidHom = U) :
    ∀ u ∈ U, (g ^ 6) u = u := by
  obtain ⟨r, hr⟩ := s16t_w3_exists_perm hU
  have h := (hr (⟨g, s16t_w3_mem_stabSub hg⟩ ^ 6)).1 (by rw [map_pow, s16t_w3_perm_pow_six])
  simpa using h

theorem s16t_w3_comm (hU : Nat.card ↥U = 4) {g h : MulAut T} (hg : U.map g.toMonoidHom = U)
    (hh : U.map h.toMonoidHom = U) (hg3 : ∀ u ∈ U, (g ^ 3) u = u)
    (hh3 : ∀ u ∈ U, (h ^ 3) u = u) : ∀ u ∈ U, (g * h) u = (h * g) u := by
  obtain ⟨r, hr⟩ := s16t_w3_exists_perm hU
  have hg' := (s16t_w3_cube_iff hr ⟨g, s16t_w3_mem_stabSub hg⟩).1 hg3
  have hh' := (s16t_w3_cube_iff hr ⟨h, s16t_w3_mem_stabSub hh⟩).1 hh3
  have h1 : r (⟨g, s16t_w3_mem_stabSub hg⟩ * ⟨h, s16t_w3_mem_stabSub hh⟩) =
      r (⟨h, s16t_w3_mem_stabSub hh⟩ * ⟨g, s16t_w3_mem_stabSub hg⟩) := by
    rw [map_mul, map_mul]
    exact s16t_w3_perm_comm _ _ hg' hh'
  exact (s16t_w3_r_eq_iff hr _ _).1 h1

theorem s16t_w3_cube_mul (hU : Nat.card ↥U = 4) {g h : MulAut T} (hg : U.map g.toMonoidHom = U)
    (hh : U.map h.toMonoidHom = U) :
    (∀ u ∈ U, ((g * h) ^ 3) u = u) ↔ ((∀ u ∈ U, (g ^ 3) u = u) ↔ ∀ u ∈ U, (h ^ 3) u = u) := by
  obtain ⟨r, hr⟩ := s16t_w3_exists_perm hU
  have e := s16t_w3_cube_iff hr (⟨g, s16t_w3_mem_stabSub hg⟩ * ⟨h, s16t_w3_mem_stabSub hh⟩)
  have eg := s16t_w3_cube_iff hr ⟨g, s16t_w3_mem_stabSub hg⟩
  have eh := s16t_w3_cube_iff hr ⟨h, s16t_w3_mem_stabSub hh⟩
  rw [map_mul] at e
  exact e.trans ((s16t_w3_perm_cube_mul _ _).trans (iff_congr eg.symm eh.symm))

theorem s16t_w3_conj (hU : Nat.card ↥U = 4) {g w : MulAut T} (hg : U.map g.toMonoidHom = U)
    (hw : U.map w.toMonoidHom = U) (hw3 : ∀ u ∈ U, (w ^ 3) u = u) :
    ((∀ u ∈ U, (g ^ 3) u = u) → ∀ u ∈ U, (g * w * g⁻¹) u = w u) ∧
      ((¬ ∀ u ∈ U, (g ^ 3) u = u) → ∀ u ∈ U, (g * w * g⁻¹) u = w⁻¹ u) := by
  obtain ⟨r, hr⟩ := s16t_w3_exists_perm hU
  set g' : ↥(stabSub U) := ⟨g, s16t_w3_mem_stabSub hg⟩ with hg'
  set w' : ↥(stabSub U) := ⟨w, s16t_w3_mem_stabSub hw⟩ with hw'
  have hw3' : r w' ^ 3 = 1 := (s16t_w3_cube_iff hr w').1 hw3
  have hc := s16t_w3_perm_conj (r g') (r w') hw3'
  refine ⟨fun hg3 => ?_, fun hg3 => ?_⟩
  · have h1 : r (g' * w' * g'⁻¹) = r w' := by
      rw [map_mul, map_mul, map_inv]
      exact hc.1 ((s16t_w3_cube_iff hr g').1 hg3)
    exact (s16t_w3_r_eq_iff hr _ _).1 h1
  · have h1 : r (g' * w' * g'⁻¹) = r w'⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_inv]
      exact hc.2 fun h3 => hg3 ((s16t_w3_cube_iff hr g').2 h3)
    exact (s16t_w3_r_eq_iff hr _ _).1 h1

theorem s16t_w3_ext {ι : Type} {Y : ι → Subgroup T} (hsup : ⨆ i, Y i = ⊤) {α β : MulAut T}
    (h : ∀ i, ∀ y ∈ Y i, α y = β y) : α = β := by
  have hle : (⨆ i, Y i) ≤ MonoidHom.eqLocus α.toMonoidHom β.toMonoidHom :=
    iSup_le fun i y hy => h i y hy
  ext t
  have ht : t ∈ ⨆ i, Y i := hsup ▸ Subgroup.mem_top t
  exact hle ht

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
