module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasD

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open CFSG.Quasithin CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem Zv_inf_centralizer_edge_eq {H M S : Subgroup G} (hA : F53Amalgam H M S)
    {α β : Geo H M} (hαβ : (graph (H ⊔ M) H M).Adj α β) (hz : Zv β ≤ centerOf (stab β)) :
    Zv α ⊓ Subgroup.centralizer ((stab α ⊓ stab β : Subgroup G) : Set G) = Zv β := by
  have hadj : α ∈ nbrs β := hαβ.symm
  have hbadj : β ∈ nbrs α := hαβ
  obtain ⟨hZeq, hZle⟩ := Zv_eq_omegaOneCenter_inf hA hadj hz
  have hCβ : Zv β ≤ Subgroup.centralizer ((stab α ⊓ stab β : Subgroup G) : Set G) := by
    intro z hzβ
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp (hz hzβ).2) g (Subgroup.mem_inf.mp hg).2
  apply le_antisymm
  · rintro z ⟨hzα, hzC⟩
    have hzStab : z ∈ stab α := pCoreOf_le 2 _ (Zv_le_Qv hA α hzα)
    have hzβ : z ∈ stab β := Qv_le_stab_of_mem_nbrs hA hbadj (Zv_le_Qv hA α hzα)
    have hsq : z ^ 2 = 1 := (isElemAbelian_Zv hA α).2 z hzα
    rw [hZeq, inf_comm (stab β) (stab α)]
    have hmem : z ∈ {w : G | w ∈ (stab α ⊓ stab β : Subgroup G) ⊓
        Subgroup.centralizer ((stab α ⊓ stab β : Subgroup G) : Set G) ∧ w ^ 2 = 1} :=
      ⟨⟨Subgroup.mem_inf.mpr ⟨hzStab, hzβ⟩, hzC⟩, hsq⟩
    exact Subgroup.subset_closure hmem
  · exact le_inf hZle hCβ

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

end
