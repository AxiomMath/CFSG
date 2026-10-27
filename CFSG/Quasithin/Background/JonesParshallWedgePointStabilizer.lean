module

public import CFSG.LinearAlgebra.AlternatingOrderThreeStabilizer
public import CFSG.Quasithin.Background.JonesParshallSL5Wedge
public import CFSG.Quasithin.Background.F918T1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.Quasithin
open CFSG.Quasithin.B5.Ln (mat)

private theorem exists_order_three_fixing_of_ne_zero {v : Fin 10 → ZMod 2} (hv : v ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
      orderOf g = 3 ∧ wedgeRep g v = v := by
  classical
  obtain ⟨Ψ, hΨ⟩ := CFSG.Quasithin.extSq5_equiv_alt
  let x : Multiplicative ↥(⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) :=
    Multiplicative.ofAdd ((wedgeEquiv (ZMod 2)).symm v)
  let A : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
    ((Multiplicative.toAdd (Ψ x) : ↥(altMat 5)) : Matrix (Fin 5) (Fin 5) (ZMod 2))
  have hAalt : Aᵀ = A ∧ ∀ i, A i i = 0 :=
    (CFSG.Quasithin.mem_altMat).mp (Multiplicative.toAdd (Ψ x)).2
  have hAt : Aᵀ = A := hAalt.1
  have hAdiag : ∀ i, A i i = 0 := hAalt.2
  have hA : A ≠ 0 := by
    intro h0
    have hΨx : Ψ x = 1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact h0
    have hx : x = 1 := by
      apply Ψ.injective
      rw [hΨx, map_one]
    have hx0 : Multiplicative.toAdd x = 0 := by
      rw [hx]
      rfl
    have hv0 : v = 0 := by
      have h := congrArg (wedgeEquiv (ZMod 2)) hx0
      simpa [x] using h
    exact hv hv0
  obtain ⟨g, hgord, hgfix⟩ :=
    CFSG.LinearAlgebra.exists_order_three_congr_fix_of_ne_zero hAt hAdiag hA
  let γ : ↥(StatedSL 5 (ZMod 2)) := specialLinearGroupEquivStatedSL 5 (ZMod 2) g
  have hγmat : mat γ = (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) :=
    specialLinearGroupEquivStatedSL_coe 5 (ZMod 2) g
  have hγcoe : ((γ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) := hγmat
  have hAfix : altMulAct γ (Ψ x) = Ψ x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [coe_toAdd_altMulAct, hγmat]
    change (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * A *
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = A
    exact hgfix
  have hxfix : extSqAct (ZMod 2) 5 γ x = x := by
    apply Ψ.injective
    rw [hΨ γ x, hAfix]
  refine ⟨g, hgord, ?_⟩
  have hrep : wedgeRep g v =
      wedgeEquiv (ZMod 2) (Multiplicative.toAdd (extSqAct (ZMod 2) 5 γ x)) := by
    have hμ : wedgeRep g v = muW (ZMod 2) g v := rfl
    rw [hμ, muW_apply]
    show wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v =
      wedgeEquiv (ZMod 2) (exteriorPower.map 2
        (Matrix.toLin' (((γ : GL (Fin 5) (ZMod 2)) :
          Matrix (Fin 5) (Fin 5) (ZMod 2))))
        ((wedgeEquiv (ZMod 2)).symm v))
    rw [hγcoe, wedgeEquiv_apply, wedgeCoord_map, ← wedgeEquiv_apply,
      LinearEquiv.apply_symm_apply]
  rw [hrep, hxfix]
  exact (wedgeEquiv (ZMod 2)).apply_symm_apply v

theorem wedgeRep_exists_order_three_fixing (v : Fin 10 → ZMod 2) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
      orderOf g = 3 ∧ wedgeRep g v = v := by
  by_cases hv : v = 0
  · subst hv
    obtain ⟨g, hgord, -⟩ := exists_order_three_fixing_of_ne_zero
      (v := (Pi.single 0 1 : Fin 10 → ZMod 2)) (by decide)
    exact ⟨g, hgord, map_zero (wedgeRep g)⟩
  · exact exists_order_three_fixing_of_ne_zero hv

end CFSG.Quasithin.JonesParshall
