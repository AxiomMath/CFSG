module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def ggCenterQuotHom {X R : Type*} [Group X] [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) : X →* R :=
  (θ : X ⧸ Subgroup.center X →* R).comp (QuotientGroup.mk' (Subgroup.center X))

theorem ggCenterQuotHom_apply {X R : Type*} [Group X] [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (l : X) :
    ggCenterQuotHom θ l = θ (QuotientGroup.mk l) :=
  rfl

theorem ggCenterQuotHom_ker {X R : Type*} [Group X] [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) : (ggCenterQuotHom θ).ker = Subgroup.center X := by
  ext l
  rw [MonoidHom.mem_ker, ggCenterQuotHom_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

end CFSG.StandardType
