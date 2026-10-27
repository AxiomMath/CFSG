module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
import CFSG.LocalAnalysis.StandardType.GGTPNThmRACoreLin
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentLin
import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem q2cLI_map_ggAutFixedSubgroup {R R' : Type*} [Group R] [Group R']
    (e : R ≃* R') (σ : MulAut R) :
    (ggAutFixedSubgroup σ).map e.toMonoidHom =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.congr e σ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    have hy' : σ y = y := (mem_ggAutFixedSubgroup σ y).mp hy
    simp [MulAut.congr_apply, hy']
  · intro hx
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup] at hx
    have hx' : e (σ (e.symm x)) = x := by simpa [MulAut.congr_apply] using hx
    refine ⟨e.symm x, ?_, by simp⟩
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact hx'

theorem q2c_lin_irred {N p : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) (h4 : 4 ≤ Nat.card F) (hN : 2 ≤ N)
    {g : GL (Fin N) F} {c : Fˣ} (hc : ∀ z : Fˣ, z ^ p ≠ c)
    (hg : g ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    {J₀ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) F))}
    (hJ₀ : CFSG.Open.IsComponentOf J₀ (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g))) :
    ∃ (a : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧ N = p * a ∧
      Nat.card E = Nat.card F ^ p ∧
      Nonempty (↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin a) E)) := by
  let e := TypeA.recipeEquiv N F
  let T : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL N F) :=
    J₀.map e.toMonoidHom
  have hσ : MulAut.congr e (TableB.linConjAut (Fin N) F g) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut N F g :=
    q1CentLin_congr_linConjAut g
  have hgrp : (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)).map e.toMonoidHom =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut N F g) := by
    rw [q2cLI_map_ggAutFixedSubgroup e (TableB.linConjAut (Fin N) F g), hσ]
  have hJ₀asm : CFSG.Assembly.IsComponentOf J₀
      (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hJ₀
  have hmap := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective
    hJ₀asm e.toMonoidHom e.injective
  have hT : CFSG.Open.IsComponentOf T
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut N F g)) := by
    rw [← hgrp]
    exact CFSG.Assembly.isComponentOf_iff_open.mp hmap
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpk : (p : F) ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h
    exact (Nat.not_even_iff_odd.mpr hpodd) (even_iff_two_dvd.mpr h2)
  have hc' : ∀ b : F, b ^ p ≠ (c : F) := by
    intro b hb
    by_cases hb0 : b = 0
    · subst hb0
      rw [zero_pow hp.ne_zero] at hb
      exact c.ne_zero hb.symm
    · let z : Fˣ := Units.mk0 b hb0
      have hz : (z : F) = b := rfl
      rw [← hz] at hb
      exact hc z (Units.ext (by simpa [Units.val_pow_eq_pow_val] using hb))
  have hstruct := raLin_nonSplit_component hp hp2 hpk hg hc' hT
  have hpN : p ∣ N :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_fieldType_component
      (n := N) (k := F) hp hpk hg hc' hT).1
  obtain ⟨h2a, E, hEfld, hEfin, hEcard, hiso⟩ := hstruct
  letI : Field E := hEfld
  letI : Fintype E := hEfin
  refine ⟨N / p, E, hEfld, inferInstance, h2a, ?_, hEcard, ?_⟩
  · have h := Nat.div_mul_cancel hpN
    rw [mul_comm]
    exact h.symm
  · obtain ⟨eT⟩ := hiso
    let eJ : ↥J₀ ≃* ↥T := Subgroup.equivMapOfInjective J₀ e.toMonoidHom e.injective
    have hcenter : (Subgroup.center ↥J₀).map eJ.toMonoidHom = Subgroup.center ↥T :=
      Subgroup.map_center_eq eJ
    let eQ : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* (↥T ⧸ Subgroup.center ↥T) :=
      QuotientGroup.congr (Subgroup.center ↥J₀) (Subgroup.center ↥T) eJ hcenter
    exact ⟨eQ.trans (eT.trans (TypeA.recipeEquiv (N / p) E).symm)⟩

end CFSG.StandardType
