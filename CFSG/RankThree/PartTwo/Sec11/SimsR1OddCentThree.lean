module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1Defs
import CFSG.RankThree.PartTwo.Sec11.SimsR1OddAutL2
import CFSG.RankThree.PartTwo.Sec11.SimsR1OddAutL2Cyc
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo OddAut
open CFSG.Assembly.RankThreeEven (projSL)

theorem l2CubeCentThree_holds : SimsR1L2CubeCentThree := by
  intro p _ hp5 X _ _ hX x hx P hP hfix
  obtain ⟨e⟩ := hX
  set F := GaloisField p (3 * 1) with hFdef
  let ε : X ≃* PSL2 F := e.trans (Sec4.projSLEquivPSL F)
  have hle : P ≤ (pglToAut ε).range :=
    le_range_pglToAut_of_isPGroup_two (Fact.out : p.Prime) (card_galoisField_cube p)
      (by decide) ε hP
  set ι : PSL2 F →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL with hι
  set xP : PGL2 F := ι (ε x) with hxP
  have hord : orderOf xP = 3 := by
    have hinj : Function.Injective (ι.comp ε.toMonoidHom) :=
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp ε.injective
    rw [hxP]
    exact (orderOf_injective _ hinj x).trans hx
  have hx2 : xP ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord] at this
    omega
  have hQ : IsPGroup 2 (P.comap (pglToAut ε)) := hP.comap_of_injective _ (pglToAut_injective ε)
  have hc : ∀ q ∈ P.comap (pglToAut ε), q * xP = xP * q := by
    intro q hq
    have h1 := toPGL_pglToAut_apply ε q x
    rw [hfix _ hq] at h1
    have h2 : q * xP * q⁻¹ = xP := h1.symm
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hcyc := isCyclic_of_isPGroup_two_of_le_centralizer
    (two_ne_zero_galoisField p hp5 _) hx2 hQ hc
  exact isCyclic_of_isCyclic_comap ε hle hcyc

end CFSG.RankThree.PartTwo.Sec11.SimsR1
