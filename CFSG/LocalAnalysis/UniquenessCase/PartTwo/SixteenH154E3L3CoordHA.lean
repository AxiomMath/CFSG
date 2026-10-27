module

public import CFSG.Quasithin.Background.HPair
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_isoMod_map {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W))) {A B : Subgroup W}
    (h : H.Pair.IsoMod L A B) :
    H.Pair.IsoMod L (A.map g.toMonoidHom) (B.map g.toMonoidHom) := by
  obtain ⟨e, he⟩ := h
  let eA : A ≃* A.map g.toMonoidHom := MulEquiv.subgroupMap g A
  let eB : B ≃* B.map g.toMonoidHom := MulEquiv.subgroupMap g B
  let e' : A.map g.toMonoidHom ≃* B.map g.toMonoidHom := eA.symm.trans (e.trans eB)
  refine ⟨e', ?_⟩
  intro l hl w hw
  let a : A := eA.symm w
  let a' : A := eA.symm ⟨l w, hw⟩
  have hwa : (w : W) = g (a : W) := by
    have h1 : (eA a : W) = g (a : W) := MulEquiv.coe_subgroupMap_apply g A a
    rwa [show eA a = w from MulEquiv.apply_symm_apply eA w] at h1
  have hwa' : (l w : W) = g (a' : W) := by
    have h1 : (eA a' : W) = g (a' : W) := MulEquiv.coe_subgroupMap_apply g A a'
    rwa [show eA a' = ⟨l w, hw⟩ from MulEquiv.apply_symm_apply eA ⟨l w, hw⟩] at h1
  have hkey : g (a' : W) = l (g (a : W)) := by
    rw [← hwa', ← hwa]
  let l₁ : MulAut W := g⁻¹ * l * g
  have hl₁ : l₁ ∈ L := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) l).mp hl
    simpa [l₁] using h1
  have ha'l₁ : (a' : W) = l₁ (a : W) := by
    apply g.injective
    calc g (a' : W) = l (g (a : W)) := hkey
      _ = g (l₁ (a : W)) := by simp [l₁, MulAut.mul_apply]
  have hl₁a : l₁ (a : W) ∈ A := ha'l₁ ▸ a'.2
  have ha'eq : a' = ⟨l₁ (a : W), hl₁a⟩ := Subtype.ext ha'l₁
  have hea : (e ⟨l₁ (a : W), hl₁a⟩ : W) = l₁ (e a) := he l₁ hl₁ a hl₁a
  have hea' : (e a' : W) = l₁ (e a) := by
    rw [ha'eq]
    exact hea
  have hL : (e' ⟨l w, hw⟩ : W) = g (e a') := by
    have h1 : e' ⟨l w, hw⟩ = eB (e a') := by
      show eB (e (eA.symm ⟨l w, hw⟩)) = eB (e a')
      rw [show eA.symm ⟨l w, hw⟩ = a' from rfl]
    rw [h1]
    exact MulEquiv.coe_subgroupMap_apply g B (e a')
  have hR : (e' w : W) = g (e a) := by
    have h1 : e' w = eB (e a) := by
      show eB (e (eA.symm w)) = eB (e a)
      rw [show eA.symm w = a from rfl]
    rw [h1]
    exact MulEquiv.coe_subgroupMap_apply g B (e a)
  rw [hL, hR, hea']
  simp [l₁, MulAut.mul_apply]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
