module

public import CFSG.LieType.BorelTits.Kempf
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderNilpotent
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42GtGrp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem comm_mul_mul {c d v u : G} (h1 : Commute c v) (h2 : Commute c u) (h3 : Commute d v)
    (h4 : Commute d u) (h5 : Commute c d) : ⁅c * v, d * u⁆ = ⁅v, u⁆ := by
  have L1 : ∀ {c v w : G}, Commute c v → Commute c w → ⁅c * v, w⁆ = ⁅v, w⁆ := by
    intro c v w hv hw
    have h : Commute c (v * w * v⁻¹) := (hv.mul_right hw).mul_right hv.inv_right
    have e : ⁅c * v, w⁆ = (c * (v * w * v⁻¹) * c⁻¹) * w⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, h.mul_inv_cancel]
    simp only [commutatorElement_def]
  have e1 : ⁅c * v, d * u⁆ = ⁅v, d * u⁆ := L1 h1 (h5.mul_right h2)
  have e2 : ⁅d * u, v⁆ = ⁅u, v⁆ := L1 h4 h3
  rw [e1, ← commutatorElement_inv, e2, commutatorElement_inv]

omit [Finite G] in
theorem conj_comm (q v u : G) : q * ⁅v, u⁆ * q⁻¹ = ⁅q * v * q⁻¹, q * u * q⁻¹⁆ := by
  simp only [commutatorElement_def]; group

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
