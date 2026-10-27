module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup

public section

open CFSG.SignalizerFunctorTheorem.Nonsolvable

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {G : Type*} [Group G]

theorem map_conj_mem_mcal {X M : Subgroup G} (hM : M ∈ mcal X) {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    M.map (MulAut.conj g).toMonoidHom ∈ mcal X := by
  obtain ⟨hMX, hsol, hcomp⟩ := hM
  let φ : MulAut ↥X := X.normalizerMonoidHom ⟨g, hg⟩
  have hφ : ∀ t : X, ((φ t : X) : G) = g * t * g⁻¹ := fun t =>
    Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨g, hg⟩ t
  have hle : M.map (MulAut.conj g).toMonoidHom ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp (hMX hx)
  have heq : (M.map (MulAut.conj g).toMonoidHom).subgroupOf X =
      (M.subgroupOf X).map φ.toMonoidHom := by
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨j, hj, hjx⟩
      refine ⟨⟨j, hMX hj⟩, hj, Subtype.ext ?_⟩
      change ((φ ⟨j, hMX hj⟩ : X) : G) = x
      rw [hφ]
      exact hjx
    · rintro ⟨t, ht, hts⟩
      refine ⟨t, ht, ?_⟩
      have := congrArg Subtype.val hts
      change ((φ t : X) : G) = x at this
      rw [hφ] at this
      exact this
  have hN : (CFSG.solvableRadical ↥X).map φ.toMonoidHom = CFSG.solvableRadical ↥X :=
    solvableRadical_map_mulEquiv φ
  let ψ : (↥X ⧸ CFSG.solvableRadical ↥X) ≃* (↥X ⧸ CFSG.solvableRadical ↥X) :=
    QuotientGroup.congr _ _ φ hN
  have hψ : ∀ t : ↥X, ψ (QuotientGroup.mk t) = QuotientGroup.mk (φ t) := fun t =>
    QuotientGroup.congr_mk _ _ φ hN t
  have hsolmap : (sol X).map (MulAut.conj g).toMonoidHom = sol X := by
    have h1 : (sol X).map (MulAut.conj g).toMonoidHom =
        ((CFSG.solvableRadical ↥X).map φ.toMonoidHom).map X.subtype := by
      unfold sol
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [h1, hN]
    rfl
  refine ⟨hle, ?_, ?_⟩
  · rw [← hsolmap]
    exact Subgroup.map_mono hsol
  · rw [heq]
    have himg : ((M.subgroupOf X).map φ.toMonoidHom).map
        (QuotientGroup.mk' (CFSG.solvableRadical ↥X)) =
        ((M.subgroupOf X).map (QuotientGroup.mk' (CFSG.solvableRadical ↥X))).map ψ.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [himg]
    exact (map_mem_lcalOf_iff ψ).mpr hcomp

theorem map_conj_mem_ltilde {X M : Subgroup G} (hM : M ∈ ltilde X) {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    M.map (MulAut.conj g).toMonoidHom ∈ ltilde X := by
  rcases hM with ⟨hX, rfl⟩ | ⟨hX, hM⟩
  · exact Or.inl ⟨hX, Subgroup.mem_normalizer_iff_map_conj_eq.mp hg⟩
  · exact Or.inr ⟨hX, map_conj_mem_mcal hM hg⟩

theorem mem_normalizer_khat_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : g ∈ Subgroup.normalizer (khat X : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ x ∈ khat X, g * x * g⁻¹ ∈ khat X := by
    intro g hg x hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp (khat_le X hx), ?_⟩
    rw [Subgroup.mem_iInf]
    intro M
    rw [Subgroup.mem_iInf]
    intro hM
    have hM' : M.map (MulAut.conj g⁻¹).toMonoidHom ∈ ltilde X :=
      map_conj_mem_ltilde hM (inv_mem hg)
    have hxN : x ∈ Subgroup.normalizer
        ((M.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) := by
      have h1 := (Subgroup.mem_inf.mp hx).2
      rw [Subgroup.mem_iInf] at h1
      have h2 := h1 (M.map (MulAut.conj g⁻¹).toMonoidHom)
      rw [Subgroup.mem_iInf] at h2
      exact h2 hM'
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h3 := Subgroup.mem_normalizer_iff.mp hxN (g⁻¹ * y * g)
    have e1 : ∀ y : G, y ∈ M ↔ g⁻¹ * y * g ∈ M.map (MulAut.conj g⁻¹).toMonoidHom := by
      intro y
      constructor
      · intro hy
        exact ⟨y, hy, by simp⟩
      · rintro ⟨z, hz, hzy⟩
        have h4 : g⁻¹ * z * g = g⁻¹ * y * g := by simpa using hzy
        have h5 : z = y := mul_left_cancel (mul_right_cancel h4)
        rwa [h5] at hz
    have e3 : g⁻¹ * (g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹) * g = x * (g⁻¹ * y * g) * x⁻¹ := by
      group
    rw [e1 y, e1 (g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹), e3]
    exact h3
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => key g hg x hx, fun hx => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hx⟩

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
