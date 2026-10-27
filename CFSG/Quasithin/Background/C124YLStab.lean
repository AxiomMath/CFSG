module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.Module

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open

variable {W : Type*} [CommGroup W] {Ls : Subgroup (MulAut W)} {x : MulAut W}

theorem commV_stable (hx : x ∈ Subgroup.normalizer (Ls : Set (MulAut W))) {u : W}
    (hu : u ∈ commV Ls) : x u ∈ commV Ls := by
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨l, hl, v, rfl⟩ := hw
    refine Subgroup.subset_closure ⟨x * l * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx l).1 hl, x v, ?_⟩
    simp [MulAut.mul_apply]
  | one => simp
  | mul a b _ _ ha hb =>
    rw [map_mul]
    exact (commV Ls).mul_mem ha hb
  | inv a _ ha =>
    rw [map_inv]
    exact (commV Ls).inv_mem ha

theorem commV_iff (hx : x ∈ Subgroup.normalizer (Ls : Set (MulAut W))) (u : W) :
    u ∈ commV Ls ↔ x u ∈ commV Ls := by
  refine ⟨commV_stable hx, fun h => ?_⟩
  have := commV_stable (inv_mem hx) h
  simpa using this

theorem fixV_iff (hx : x ∈ Subgroup.normalizer (Ls : Set (MulAut W))) (v : W) :
    v ∈ fixV Ls ↔ x v ∈ fixV Ls := by
  have key : ∀ y : MulAut W, y ∈ Subgroup.normalizer (Ls : Set (MulAut W)) → ∀ v ∈ fixV Ls,
      y v ∈ fixV Ls := by
    intro y hy v hv l hl
    have hl' : y⁻¹ * l * y ∈ Ls := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) l).1 hl
      simpa using this
    have := hv _ hl'
    have h2 := congrArg y this
    simpa [MulAut.mul_apply] using h2
  refine ⟨key x hx v, fun h => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ h
  simpa using this

theorem sec_stable (hx : x ∈ Subgroup.normalizer (Ls : Set (MulAut W))) :
    (∀ u, u ∈ commV Ls ↔ x u ∈ commV Ls) ∧
      ∀ z, z ∈ fixV Ls ⊓ commV Ls ↔ x z ∈ fixV Ls ⊓ commV Ls :=
  ⟨commV_iff hx, fun z => by
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (fixV_iff hx z) (commV_iff hx z)⟩

end CFSG.Quasithin.C124.YL
