module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ColZ
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2UC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Col

open S35.Std S35.Fin S35.Ch S35.Ch2
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem zvBlock_II (hS : Sit H M S) : S35.II.ZvBlock H M := by
  intro δ l l' hδ hl hl'
  obtain ⟨c⟩ := exists_chart2 hS hδ
  rw [Zv_eq_iff_pt c hS hδ hl hl', c.sameBlock_iff hS hδ hl hl']

theorem zvInf_II (hS : Sit H M S) : S35.II.ZvInf H M := by
  intro δ hδ x hx hn
  obtain ⟨c⟩ := exists_chart2 hS hδ
  rw [← c.iInf_Mbl hS hδ]
  exact Subgroup.mem_iInf.mpr fun l => Subgroup.mem_iInf.mpr fun hl => ⟨hn l hl, hx⟩

theorem rkZvEq_II (hS : Sit H M S) : S35.II.RkZvEq H M := by
  intro δ hδ v hv
  have h := fixSecIn_Zv_eq_Cb hS hδ (A := Subgroup.zpowers v)
    ((Subgroup.zpowers_le).mpr hv)
  unfold S34.rk secIdx
  rw [h]

theorem thatFacts_II (hS : Sit H M S) : S35.II.ThatFacts H M := S35.Ch2.thatFacts hS

end S35.Col

end F53.Stellmacher

end CFSG.Quasithin
