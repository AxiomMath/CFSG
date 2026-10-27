
module

public import CFSG.Quasithin.EmptyFaithful.S151S9TM24Inputs
public import CFSG.Quasithin.EmptyFaithful.S151S9TLat
public import CFSG.Quasithin.EmptyFaithful.S151S9TCen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Base
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Base

@[expose] public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
  CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m24a m24b)

theorem m24_centre [M24Lat] :
    ∃ z₀ : ↥CFSG.Blueprint.NativeSporadic.M24, orderOf z₀ = 2 ∧
      centerOf m24Ctx.S = Subgroup.zpowers z₀ ∧ (tab 24 z₀).toArray = m24SLP[162]! := by
  have hk : 0 < m24Ctx.k := by
    have : m24Ctx.k = 10 := rfl
    omega
  obtain ⟨z₀, hz2, hZ, hzT⟩ := centre_of_baseCertS m24Ctx hk m24a m24b m24Prog
    m24_valid m24Qp 162 213 216 214 217 m24Enum.1 m24Enum.2.1 m24Enum.2.2 10 m24_cert' rfl
  refine ⟨z₀, hz2, hZ, ?_⟩
  rw [hzT, m24_ta, m24_tb]
  rfl

end CFSG.Quasithin.S151S9T
