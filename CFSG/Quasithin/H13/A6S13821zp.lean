module

public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreElevenA

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Quasithin CFSG.Quasithin.B1Red

theorem isFFModule_autSec_top {U' : Type} [CommGroup U'] {Y : Subgroup (MulAut U')}
    {C : Subgroup U'} (hFF : IsFFModule (autQuot Y C)) : IsFFModule (autSec Y ⊤ C) := by
  have hCe : (C.subgroupOf (⊤ : Subgroup U')).map
      (Subgroup.topEquiv : (⊤ : Subgroup U') ≃* U').toMonoidHom = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hy
    · intro hx
      exact ⟨⟨x, trivial⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  let e : Sec (⊤ : Subgroup U') C ≃* U' ⧸ C :=
    QuotientGroup.congr (C.subgroupOf ⊤) C Subgroup.topEquiv hCe
  have he : ∀ u : ↥(⊤ : Subgroup U'), e (QuotientGroup.mk u) = QuotientGroup.mk (u : U') :=
    fun u => rfl
  have hle : autQuot Y C ≤ (autSec Y ⊤ C).map (MulAut.congr e).toMonoidHom := by
    intro ψ hψ
    obtain ⟨g, hgY, rfl⟩ := mem_autQuot.mp hψ
    let g₀ : stabSub (⊤ : Subgroup U') := ⟨g, fun _ => Iff.rfl⟩
    have hgC : resHom ⊤ g₀ ∈ stabSub (C.subgroupOf (⊤ : Subgroup U')) := by
      intro u
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, resHom_apply]
      exact g.2 (u : U')
    refine ⟨quotHom (C.subgroupOf ⊤) ⟨resHom ⊤ g₀, hgC⟩, ?_, ?_⟩
    · refine mem_autQuot.mpr ⟨⟨resHom ⊤ g₀, hgC⟩, mem_autSub.mpr ⟨g₀, hgY, rfl⟩, rfl⟩
    · ext x
      obtain ⟨y, rfl⟩ := e.surjective x
      induction y using QuotientGroup.induction_on with
      | H u =>
        show e ((quotHom (C.subgroupOf ⊤) ⟨resHom ⊤ g₀, hgC⟩) (e.symm (e (QuotientGroup.mk u)))) =
          (quotHom C g) (e (QuotientGroup.mk u))
        rw [MulEquiv.symm_apply_apply, quotHom_mk, he, he, quotHom_mk]
        rfl
  have h1 := isFFModule_map_congr' e.symm (isFFModule_mono hle hFF)
  have h2 : ((autSec Y ⊤ C).map (MulAut.congr e).toMonoidHom).map
      (MulAut.congr e.symm).toMonoidHom = autSec Y ⊤ C := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id (autSec Y ⊤ C)
    ext φ x
    simp [MulAut.congr_apply]
  rw [h2] at h1
  exact h1

end CFSG.Quasithin.H13.A6.A6S20
