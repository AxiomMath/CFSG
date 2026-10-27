module

public import CFSG.Quasithin.Vol2.KGFactC31J4Off

public section

namespace CFSG.Quasithin.KGC31.Off5

open CFSG.Assembly.LowTwoRank

theorem run5_eq_true : run5 = true := by decide +kernel

theorem exists_eq_conj_T0' {E : Subgroup ↥(StatedSL 5 (ZMod 2))} (hE : IsOff E) :
    ∃ x : ↥(StatedSL 5 (ZMod 2)), E = T0.map (MulAut.conj x).toMonoidHom :=
  exists_eq_conj_T0 run5_eq_true hE

theorem offender_unique' {P : Subgroup ↥(StatedSL 5 (ZMod 2))} (hP : IsPGroup 2 ↥P)
    {E₁ E₂ : Subgroup ↥(StatedSL 5 (ZMod 2))} (h₁ : E₁ ≤ P) (h₂ : E₂ ≤ P) (o₁ : IsOff E₁)
    (o₂ : IsOff E₂) : E₁ = E₂ :=
  offender_unique run5_eq_true hP h₁ h₂ o₁ o₂

end CFSG.Quasithin.KGC31.Off5

end
