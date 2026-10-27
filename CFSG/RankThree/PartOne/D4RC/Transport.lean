module

public import CFSG.RankThree.PartOne.D4RC.Closure

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Timmesfeld.ARS

variable {G H : Type*} [Group G] [Group H]

theorem rcm_commuting_map (φ : G →* H) {M N : Subgroup G} (h : Commuting M N) :
    Commuting (M.map φ) (N.map φ) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact (h a ha b hb).map φ

theorem rcm_commuting_map_iff {φ : G →* H} (hφ : Function.Injective φ) {M N : Subgroup G} :
    Commuting (M.map φ) (N.map φ) ↔ Commuting M N := by
  refine ⟨fun h a ha b hb => ?_, rcm_commuting_map φ⟩
  have := h (φ a) ⟨a, ha, rfl⟩ (φ b) ⟨b, hb, rfl⟩
  exact hφ (by rw [map_mul, map_mul]; exact this)

theorem rcm_conjSub_map (φ : G →* H) (M : Subgroup G) (g : G) :
    conjSub (M.map φ) (φ g) = (conjSub M g).map φ := by
  simp only [conjSub, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun y => ?_
  simp [MulAut.conj_apply]

theorem rcm_comm_of_mul_self {A : Subgroup G} (hA : ∀ a ∈ A, a * a = 1) :
    ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro a ha b hb
  have h1 := hA _ (A.mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hA a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hA b hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = b * a := by rw [mul_inv_rev, ha', hb']

theorem rcm_comm_closure {S : Set G} (h : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) :
    ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
  intro a ha b hb
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro t ht
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro s hs
    exact h s hs t ht
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set G) := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro t ht
    exact ((Subgroup.mem_centralizer_iff.1 (h1 ht)) s hs).symm
  exact ((Subgroup.mem_centralizer_iff.1 (h2 ha)) b hb).symm

theorem rcm_comm_sup {A B : Subgroup G} (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hAB : Commuting A B) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have hS : ∀ s ∈ (A : Set G) ∪ B, ∀ t ∈ (A : Set G) ∪ B, s * t = t * s := by
    rintro s (hs | hs) t (ht | ht)
    · exact hA s hs t ht
    · exact hAB s hs t ht
    · exact (hAB t ht s hs).symm
    · exact hB s hs t ht
  have hcl : A ⊔ B = Subgroup.closure ((A : Set G) ∪ B) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  intro x hx y hy
  rw [hcl] at hx hy
  exact rcm_comm_closure hS x hx y hy

theorem rcm_center_map (e : G ≃* H) {Γ : Subgroup G} (h : Subgroup.center ↥Γ = ⊥) :
    Subgroup.center ↥(Γ.map e.toMonoidHom) = ⊥ := by
  set φ := Subgroup.equivMapOfInjective Γ e.toMonoidHom e.injective with hφ
  rw [eq_bot_iff]
  intro z hz
  have hz' : φ.symm z ∈ Subgroup.center ↥Γ := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (Subgroup.mem_center_iff.1 hz (φ g))
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  have := congrArg φ hz'
  rwa [MulEquiv.apply_symm_apply, map_one] at this

theorem rcm_twoCore_map (e : G ≃* H) {Γ : Subgroup G}
    (h : ∀ N : Subgroup ↥Γ, N.Normal → IsPGroup 2 N → N = ⊥) :
    ∀ N : Subgroup ↥(Γ.map e.toMonoidHom), N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN h2
  set φ := Subgroup.equivMapOfInjective Γ e.toMonoidHom e.injective with hφ
  have hN' : (N.comap φ.toMonoidHom).Normal := hN.comap _
  have h2' : IsPGroup 2 (N.comap φ.toMonoidHom) :=
    h2.comap_of_injective φ.toMonoidHom φ.injective
  have hbot := h _ hN' h2'
  rw [eq_bot_iff]
  intro z hz
  have : φ.symm z ∈ N.comap φ.toMonoidHom := by
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact hz
  rw [hbot, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  have := congrArg φ this
  rwa [MulEquiv.apply_symm_apply, map_one] at this

theorem rcm_iSup_orbit_map (e : G ≃* H) (Γ A₀ : Subgroup G) :
    ⨆ A ∈ rccOrbit (Γ.map e.toMonoidHom) (A₀.map e.toMonoidHom), A =
      (⨆ A ∈ rccOrbit Γ A₀, A).map e.toMonoidHom := by
  apply le_antisymm
  · refine iSup₂_le ?_
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    rw [rcm_conjSub_map]
    exact Subgroup.map_mono (le_iSup₂ (f := fun A (_ : A ∈ rccOrbit Γ A₀) => A) _ ⟨g, hg, rfl⟩)
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le ?_
    rintro _ ⟨g, hg, rfl⟩
    rw [← Subgroup.map_le_iff_le_comap, ← rcm_conjSub_map]
    exact le_iSup₂ (f := fun A (_ : A ∈ rccOrbit (Γ.map e.toMonoidHom) (A₀.map e.toMonoidHom)) => A)
      _ ⟨e g, ⟨g, hg, rfl⟩, rfl⟩

end CFSG.RankThree.PartOne.D4RC
