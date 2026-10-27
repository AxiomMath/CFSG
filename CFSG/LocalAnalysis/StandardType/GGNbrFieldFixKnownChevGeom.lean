module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open scoped commutatorElement

theorem ggFixDer_eq_ggFixSub {R R₀ : Type} [Group R] [Group R₀] [IsSimpleGroup R₀]
    (hna : ∃ a b : R₀, a * b ≠ b * a) (f : MulAut R) (e : R₀ ≃* ↥(ggFixSub f)) :
    ggFixDer f = ggFixSub f := by
  haveI : IsSimpleGroup ↥(ggFixSub f) := e.symm.isSimpleGroup
  have hnc : ¬ ∀ g h : ↥(ggFixSub f), g * h = h * g := by
    intro hc
    obtain ⟨a, b, hab⟩ := hna
    exact hab (by simpa using congrArg e.symm (hc (e a) (e b)))
  have hperf : commutator ↥(ggFixSub f) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥(ggFixSub f)) with h | h
    · exfalso
      apply hnc
      intro g k
      have hmem : ⁅g, k⁆ ∈ commutator ↥(ggFixSub f) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top k)
      rw [h, Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hmem
    · exact h
  haveI : Group.IsPerfect ↥(ggFixSub f) := ⟨hperf⟩
  rw [ggFixDer]
  exact Subgroup.commutator_eq_self

theorem ggFixGeom_of_inn {R R₀ : Type} [Group R] [Group R₀] [IsSimpleGroup R₀]
    (hna : ∃ a b : R₀, a * b ≠ b * a) {I : Set (MulAut R)} {I₀ : Set (MulAut R₀)}
    {f : MulAut R} (hZ : Subgroup.center R = ⊥)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hI₀ : Set.range (MulAut.conj : R₀ →* MulAut R₀) ⊆ I₀)
    (e : R₀ ≃* ↥(ggFixSub f)) :
    ∃ θ₀ : ggFixDer f ≃* R₀, GGFixGeom I f I₀ θ₀ := by
  have hder : ggFixDer f = ggFixSub f := ggFixDer_eq_ggFixSub hna f e
  let θ₀ : ggFixDer f ≃* R₀ := (MulEquiv.subgroupCongr hder).trans e.symm
  have hcenter : Subgroup.center R₀ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R₀) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      have ha : a ∈ Subgroup.center R₀ := h ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have key : ∀ g : R, MulAut.conj g * f = f * MulAut.conj g → f g = g := by
    intro g hg
    have h1 : ∀ y : R, g * f y * g⁻¹ = f g * f y * (f g)⁻¹ := by
      intro y
      have h := congrArg (fun α : MulAut R => α y) hg
      simpa [MulAut.mul_apply, MulAut.conj_apply] using h
    have hcomm : ∀ y : R, ((f g)⁻¹ * g) * f y = f y * ((f g)⁻¹ * g) := by
      intro y
      calc (f g)⁻¹ * g * f y
          = (f g)⁻¹ * (g * f y * g⁻¹) * g := by group
        _ = (f g)⁻¹ * (f g * f y * (f g)⁻¹) * g := by rw [h1 y]
        _ = f y * ((f g)⁻¹ * g) := by group
    have hz : (f g)⁻¹ * g = 1 := by
      have hmem : (f g)⁻¹ * g ∈ Subgroup.center R := by
        rw [Subgroup.mem_center_iff]
        intro u
        obtain ⟨y, rfl⟩ := f.surjective u
        exact (hcomm y).symm
      rwa [hZ, Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.mp hz
  refine ⟨θ₀, ?_, ?_⟩
  · intro φ hφI hφ
    obtain ⟨g, rfl⟩ := hI hφI
    have hg : g ∈ ggFixDer f := by
      rw [hder, mem_ggFixSub]
      exact key g hφ
    refine ⟨MulAut.conj (θ₀ ⟨g, hg⟩), hI₀ ⟨θ₀ ⟨g, hg⟩, rfl⟩, fun x hx => ?_⟩
    have h1 : (⟨MulAut.conj g x, ggFixDer_map_mem hφ hx⟩ : ggFixDer f) =
        ⟨g, hg⟩ * ⟨x, hx⟩ * ⟨g, hg⟩⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
    rfl
  · intro φ hφI hφ htriv
    obtain ⟨g, rfl⟩ := hI hφI
    have hg : g ∈ ggFixDer f := by
      rw [hder, mem_ggFixSub]
      exact key g hφ
    have hcomm : ∀ v : R₀, v * θ₀ ⟨g, hg⟩ = θ₀ ⟨g, hg⟩ * v := by
      intro v
      obtain ⟨x, rfl⟩ := MulEquiv.surjective θ₀ v
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have he : g * x.val * g⁻¹ = x.val := htriv x.val x.2
      have hxg : x.val * g = g * x.val := by
        simpa [mul_assoc] using (congrArg (fun t => t * g) he).symm
      exact hxg
    have h1 : θ₀ ⟨g, hg⟩ = 1 := by
      have hmem : θ₀ ⟨g, hg⟩ ∈ Subgroup.center R₀ := by
        rw [Subgroup.mem_center_iff]
        exact hcomm
      rwa [hcenter, Subgroup.mem_bot] at hmem
    have h2 : (⟨g, hg⟩ : ggFixDer f) = 1 :=
      θ₀.injective (by rw [h1, map_one])
    have hg1 : g = 1 := congrArg Subtype.val h2
    simpa [hg1]

end CFSG.StandardType

end
