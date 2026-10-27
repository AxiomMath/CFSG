module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps
public import CFSG.Quasithin.EmptyFaithful.SzF53BasD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem lt_bAt_of_s3 (hA : F53Amalgam H M S) (h32 : Hss32At H M) {α β : Geo H M}
    (hαβ : (graph (H ⊔ M) H M).Adj α β) (hα : vtype α = true) (hαb : bAt α = bMin H M) :
    bMin H M < bAt β := by
  rcases (bMin_le_bAt β).lt_or_eq with h | h
  · exact h
  · exfalso
    have hc := centralizer_Zv_eq_Qv_of_bAt hA h.symm
    have hz := h32 α β hαβ hα hαb
    have hcen : stab β ≤ Subgroup.centralizer (Zv β : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz'
      exact ((Subgroup.mem_centralizer_iff.mp (hz hz').2) x hx).symm
    rw [inf_eq_left.mpr hcen] at hc
    exact pCoreOf_ne_stab hA β hc.symm

theorem lt_bAt_of_s5 (hA : F53Amalgam H M S) (h32 : Hss32At H M) {α β : Geo H M}
    (hαβ : (graph (H ⊔ M) H M).Adj α β) (hα : vtype α = false) (hαb : bAt α = bMin H M) :
    bMin H M < bAt β := by
  have hβ : vtype β = true := by
    have h := vtype_ne_of_adj hαβ
    rw [hα] at h
    cases hv : vtype β
    · exact absurd hv.symm h
    · rfl
  rcases (bMin_le_bAt β).lt_or_eq with h | h
  · exact h
  · have := lt_bAt_of_s3 hA h32 hαβ.symm hβ h.symm
    omega

end F53.Stellmacher

end CFSG.Quasithin
