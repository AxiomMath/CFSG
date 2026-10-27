module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarZpowers
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarPComp
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarEnd
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarConfig

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix

section U

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {n f : ℕ} {y : G} {K : Subgroup G}

theorem mem_map_conj_iff {H : Subgroup G} {a h : G} :
    h ∈ H.map (MulAut.conj a).toMonoidHom ↔ ∃ k ∈ H, a * k * a⁻¹ = h := by
  simp [Subgroup.mem_map]

end U

end CFSG.StandardType
