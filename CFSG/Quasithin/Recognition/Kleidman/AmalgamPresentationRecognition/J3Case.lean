module

public import CFSG.Quasithin.Recognition.Kleidman.BenderClose
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.HPsi
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Fusion
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.W4Local
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Recognition

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open CFSG.Quasithin

theorem eq_one_or_z_of_central_centralizer {G : Type} [Group G] [Finite G] {z : G}
    (h : IsTypeH2 G z) {c : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G))
    (hcen : ∀ x ∈ Subgroup.centralizer ({z} : Set G), x * c = c * x) : c = 1 ∨ c = z := by
  obtain ⟨ψ, hinj, hrange, hmem, hz⟩ := exists_H_psi h
  obtain ⟨m, rfl⟩ := hrange c hc
  have hcm : ∀ g : CFSG.Quasithin.J2Cz.Model, g * m = m * g := by
    intro g
    apply hinj
    rw [map_mul, map_mul]
    exact hcen (ψ g) (hmem g)
  rcases eq_one_or_z_of_central m hcm with h1 | h1
  · left; rw [h1, map_one]
  · right
    rw [h1]
    exact hz


theorem nonempty_mulEquiv_J3Model_of_letters {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {z : G} (h : IsTypeH2 G z) (e : Fin 7 → G) (he3 : e 3 = z)
    (hH : Subgroup.closure (e '' {i : Fin 7 | i.val ≠ 6}) = Subgroup.centralizer ({z} : Set G))
    (he6 : e 6 ∉ Subgroup.centralizer ({z} : Set G)) (hrel : SatisfiesJ3WordsW e) :
    Nonempty (G ≃* J3Model) := by
  classical
  set M : Subgroup G := Subgroup.closure (Set.range e) with hM
  have heM : ∀ i, e i ∈ M := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hHM : Subgroup.centralizer ({z} : Set G) ≤ M := by
    rw [← hH]
    exact Subgroup.closure_mono (by rintro _ ⟨i, -, rfl⟩; exact ⟨i, rfl⟩)
  let g' : Fin 7 → M := fun i => ⟨e i, heM i⟩
  have hgen : Subgroup.closure (Set.range g') = ⊤ := by
    have hr : Set.range g' = ((↑) : M → G) ⁻¹' Set.range e := by
      ext ⟨x, hx⟩
      simp [g']
    rw [hr]
    exact Subgroup.closure_closure_coe_preimage
  have hrel' : SatisfiesJ3WordsW g' := by
    intro r hr
    apply Subtype.ext
    have := hrel r hr
    have h2 : (M.subtype : M →* G) (FreeGroup.lift g' (FreeGroup.mk r)) =
        FreeGroup.lift e (FreeGroup.mk r) := by
      have : M.subtype.comp (FreeGroup.lift g') = FreeGroup.lift e := by
        ext i; simp [g']
      exact congrArg (fun φ => φ (FreeGroup.mk r)) this
    simpa [this] using h2
  have hz2 : z * z = 1 := by rw [← pow_two]; exact h.sq
  have hnoncomm : ∃ a b : M, a * b ≠ b * a := by
    refine ⟨g' 6, g' 3, fun hab => he6 ?_⟩
    have : e 6 * e 3 = e 3 * e 6 := congrArg Subtype.val hab
    rw [he3] at this
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact this
  have hK3 : 3 < Nat.card M := three_lt_natCard_of_noncomm hnoncomm
  have hZ : ∀ c ∈ Subgroup.center M, c = 1 := by
    intro c hc
    have hczM : (c : G) ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_center_iff.mp hc ⟨z, hHM (Subgroup.mem_centralizer_singleton_iff.mpr rfl)⟩
      exact (congrArg Subtype.val this).symm
    have hcen : ∀ x ∈ Subgroup.centralizer ({z} : Set G), x * c = c * x := by
      intro x hx
      have := Subgroup.mem_center_iff.mp hc ⟨x, hHM hx⟩
      exact congrArg Subtype.val this
    rcases eq_one_or_z_of_central_centralizer h hczM hcen with h1 | h1
    · exact Subtype.ext h1
    · exfalso
      apply he6
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_center_iff.mp hc (g' 6)
      have h2 : e 6 * c = c * e 6 := congrArg Subtype.val this
      rw [h1] at h2
      exact h2
  obtain ⟨Θ, hΘ⟩ := exists_mulEquiv_J3Model_of_generated_W g' hgen hrel' hK3 hZ
  have hconj : ∀ y ∈ M, y * y = 1 → y ≠ 1 → ∃ k ∈ M, k * z * k⁻¹ = y := by
    intro y hy hy2 hy1
    have hy2' : Θ ⟨y, hy⟩ * Θ ⟨y, hy⟩ = 1 := by
      rw [← map_mul]
      have : (⟨y, hy⟩ : M) * ⟨y, hy⟩ = 1 := Subtype.ext hy2
      rw [this, map_one]
    have hy1' : Θ ⟨y, hy⟩ ≠ 1 := by
      intro h1
      apply hy1
      have := Θ.injective (h1.trans (map_one Θ).symm)
      exact congrArg Subtype.val this
    obtain ⟨k', hk'⟩ := one_class_involutions_J3Model _ hy2' hy1'
    refine ⟨(Θ.symm k' : M), (Θ.symm k').2, ?_⟩
    have h3 : Θ (g' 3) = uJ 3 := hΘ 3
    have : (Θ.symm k') * g' 3 * (Θ.symm k')⁻¹ = ⟨y, hy⟩ := by
      apply Θ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h3]
      exact hk'
    have h4 := congrArg Subtype.val this
    simpa [g', he3] using h4
  have hMtop : M = ⊤ := CFSG.Quasithin.Kleidman.IsTypeH2.eq_top_of_conj_z h hHM hconj
  have e1 : G ≃* M := (Subgroup.topEquiv (G := G)).symm.trans (MulEquiv.subgroupCongr hMtop.symm)
  exact ⟨e1.trans Θ⟩

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
