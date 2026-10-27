module

public import CFSG.Quasithin.EmptyFaithful.SzF53Dich2
public import CFSG.Quasithin.EmptyFaithful.SzF53B3Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom

namespace F53B3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem base_of_dich2 (hA : F53Amalgam H M S) (hd : F53DichAt2 H M) (hb : bMin H M = 3)
    (hc : bAt (γ₁ (H ⊔ M) H M) = bMin H M) :
    B3Base H M S ∧ (IsNatSec (stab (γ₀ (H ⊔ M) H M)) (Cv (γ₀ (H ⊔ M) H M)) (Vn (γ₀ (H ⊔ M) H M)) ∨
      IsOrthSec (stab (γ₀ (H ⊔ M) H M)) (Cv (γ₀ (H ⊔ M) H M)) (Vn (γ₀ (H ⊔ M) H M))) := by
  have hcrit : ∀ α : Geo H M, vtype α = true → bAt α = bMin H M := fun α hα =>
    (bAt_eq_of_vtype_eq (by rw [hα]; rfl)).trans hc
  have key : ∀ β : Geo H M, vtype β = false → ∃ α : Geo H M, (graph (H ⊔ M) H M).Adj α β ∧
      vtype α = true ∧ bAt α = bMin H M := by
    intro β hβ
    obtain ⟨α, hα⟩ := exists_adj β
    have hv := vtype_nbr_of_false hα hβ
    exact ⟨α, hα.symm, hv, hcrit α hv⟩
  refine ⟨⟨hA, hb, hcrit, ?_, ?_, ?_⟩, ?_⟩
  · intro β hβ
    obtain ⟨α, hαβ, _, hαc⟩ := key β hβ
    exact hd.zv_central α β hαβ hαc
  · intro α β hαβ hα
    exact (hd.s3_three α β hαβ (hcrit α hα) hα hb).1
  · intro β hβ
    obtain ⟨α, hαβ, hα, hαc⟩ := key β hβ
    exact (hd.s3_three α β hαβ hαc hα hb).2.1
  · obtain ⟨α, hαβ, hα, hαc⟩ := key (γ₀ (H ⊔ M) H M) vtype_γ₀
    exact (hd.s3_three α _ hαβ hαc hα hb).2.2

end F53B3

end CFSG.Quasithin
