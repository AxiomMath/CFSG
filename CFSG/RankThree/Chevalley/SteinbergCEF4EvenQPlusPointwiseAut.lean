module

public import CFSG.LieType.Ree.FixedMonomialQuotient
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint F4Weyl
  EvenG2 EvenF4QPlus CFSG.RankThree.E6 CFSG.LieType.Ree
open scoped Pointwise

namespace EvenF4QPlus

section Torus

variable {L : Type} [Field L] [Finite L] [CharP L ReeTag.F4.prime]

theorem finiteExceptionalAut_mem_torusGroup
    {h : ModGL ReeTag.F4.tag L}
    (hh : h ∈ torusGroup ReeTag.F4.tag L) (hC : h ∈ adjointGroup ReeTag.F4.tag L) :
    ((ReeTag.F4.finiteExceptionalAut L ⟨h, hC⟩ : adjointGroup ReeTag.F4.tag L) :
      ModGL ReeTag.F4.tag L) ∈ torusGroup ReeTag.F4.tag L := by
  have h1 := ReeTag.finiteReeAut_mem_torusGroup (t := ReeTag.F4) (K := L) (a := 0) hh hC
  simpa only [ReeTag.finiteReeAut, pow_zero, mul_one] using h1

theorem finiteExceptionalAut_rootDiagUnit
    (a : Fin ReeTag.F4.tag.rank → Lˣ)
    (hC : rootDiagUnit ReeTag.F4.tag a ∈ adjointGroup ReeTag.F4.tag L) :
    ((ReeTag.F4.finiteExceptionalAut L ⟨rootDiagUnit ReeTag.F4.tag a, hC⟩ :
      adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
      rootDiagUnit ReeTag.F4.tag fun j =>
        a (ReeTag.F4.perm j) ^ ReeTag.F4.exponent (ReeTag.F4.perm j) := by
  have hH : ((ReeTag.F4.finiteExceptionalAut L ⟨rootDiagUnit ReeTag.F4.tag a, hC⟩ :
      adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈ torusGroup ReeTag.F4.tag L :=
    finiteExceptionalAut_mem_torusGroup (F4_rootDiagUnit_mem_torusGroup a) hC
  obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hH
  rw [ha']
  have key : ∀ i, a' (ReeTag.F4.perm i) = a i ^ ReeTag.F4.exponent i := by
    intro i
    have e1 : (⟨rootDiagUnit ReeTag.F4.tag a, hC⟩ : adjointGroup ReeTag.F4.tag L) * xElement i 1 *
        (⟨rootDiagUnit ReeTag.F4.tag a, hC⟩ : adjointGroup ReeTag.F4.tag L)⁻¹ =
          xElement i (a i : L) := Subtype.ext (by
      change rootDiagUnit ReeTag.F4.tag a * xUnit ReeTag.F4.tag L i 1 *
          (rootDiagUnit ReeTag.F4.tag a)⁻¹ = xUnit ReeTag.F4.tag L i (a i)
      rw [← pinnedX_single, ← pinnedX_single, rootDiagUnit_conj_pinnedX a (isRoot_single _ i),
        rootChar_pi_single, mul_one])
    have e2 := congrArg (fun y => ((ReeTag.F4.finiteExceptionalAut L y :
      adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L)) e1
    simp only [map_mul, map_inv, ReeTag.finiteExceptionalAut_xElement, Subgroup.coe_mul,
      Subgroup.coe_inv, one_pow] at e2
    rw [ha'] at e2
    change rootDiagUnit ReeTag.F4.tag a' * xUnit ReeTag.F4.tag L (ReeTag.F4.perm i) 1 *
        (rootDiagUnit ReeTag.F4.tag a')⁻¹ =
      xUnit ReeTag.F4.tag L (ReeTag.F4.perm i) ((a i : L) ^ ReeTag.F4.exponent i) at e2
    rw [← pinnedX_single, ← pinnedX_single, rootDiagUnit_conj_pinnedX a' (isRoot_single _ _),
      rootChar_pi_single, mul_one] at e2
    exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact pinnedX_injective _ _ _ e2)
  congr 1
  funext j
  rw [← key (ReeTag.F4.perm j), ReeTag.perm_perm]

theorem perm_F4_eq_rev (j : Fin ReeTag.F4.tag.rank) : ReeTag.F4.perm j = Fin.rev j := by
  fin_cases j <;> rfl

theorem exponent_perm_F4 (j : Fin ReeTag.F4.tag.rank) :
    ReeTag.F4.exponent (ReeTag.F4.perm j) = if (j : ℕ) < 2 then 2 else 1 := by
  fin_cases j <;> rfl

end Torus

end EvenF4QPlus

open EvenF4QPlus

end CFSG.RankThree.Chevalley
