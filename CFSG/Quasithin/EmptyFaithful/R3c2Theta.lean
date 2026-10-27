module

public import CFSG.Quasithin.Background.A3Structure318Defs

public section

namespace CFSG.Quasithin.R3c2

open CFSG.Quasithin

variable {G : Type} [Group G]

theorem thetaOf_le_oPrimeResidualOf_three (H : Subgroup G) : thetaOf H ≤ oPrimeResidualOf 3 H :=
  Subgroup.closure_mono fun _ hx => ⟨hx.1, 1, by simpa using hx.2⟩

theorem exists_surjection_starImage {H L : Subgroup G} (hLH : L ≤ H) {X : Type*} [Group X]
    (ψ : ↥L →* X) (hψ : Function.Surjective ψ)
    (hk : ∀ x : ↥L, ψ x = 1 → (⟨x, hLH x.2⟩ : ↥H) ∈ CFSG.pPrimeCore 3 ↥H) :
    ∃ π : X →* ↥(starImage 3 (L.subgroupOf H)), Function.Surjective π := by
  set e : ↥L ≃* ↥(L.subgroupOf H) := (Subgroup.subgroupOfEquivOfLe hLH).symm with he
  set ρ : ↥L →* ↥(starImage 3 (L.subgroupOf H)) :=
    ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)).comp
      ((L.subgroupOf H).subtype.comp e.toMonoidHom)).codRestrict
      (starImage 3 (L.subgroupOf H)) (fun x => ⟨(e x : ↥H), (e x).2, rfl⟩) with hρdef
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, x', hx', rfl⟩
    refine ⟨e.symm ⟨x', hx'⟩, Subtype.ext ?_⟩
    simp [hρdef]
  have hker : ψ.ker ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥H) _).2 (hk x hx)
  set e' := QuotientGroup.quotientKerEquivOfSurjective ψ hψ with he'
  have he'' : ∀ x : ↥L, e'.symm (ψ x) = (x : ↥L ⧸ ψ.ker) := fun x => e'.symm_apply_eq.mpr rfl
  set π : X →* ↥(starImage 3 (L.subgroupOf H)) :=
    (QuotientGroup.lift ψ.ker ρ hker).comp e'.symm.toMonoidHom with hπ
  have hπψ : ∀ x : ↥L, π (ψ x) = ρ x := by
    intro x
    rw [hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he'', QuotientGroup.lift_mk]
  refine ⟨π, fun b => ?_⟩
  obtain ⟨x, rfl⟩ := hρ b
  exact ⟨ψ x, hπψ x⟩

end CFSG.Quasithin.R3c2
