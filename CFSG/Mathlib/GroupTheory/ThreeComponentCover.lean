module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FCover
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Solomon.LocalBalance

theorem le_sup_glaPPrimeCoreOf_of_glaPComponent_of_mem_dQ {X : Type} [Group X] [Finite X]
    {H L J : Subgroup X} {b : X} (hL : GLAPComponent 3 H L) (hb3 : b ^ 3 = 1)
    (hbd : b ∈ dQ L)
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({b} : Set X)) J) :
    L ≤ J ⊔ GLAPPrimeCoreOf 3 H := by
  have hE3 : IsPGroup 3 ↥(Subgroup.zpowers b) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hb3)
  have hEd : Subgroup.zpowers b ≤ dQ L := Subgroup.zpowers_le.2 hbd
  obtain ⟨J₀, hJ₀, hLJ₀, huniq, -⟩ :=
    coverStmt X H L (Subgroup.zpowers b) hL hE3 hEd
  have hC : Subgroup.centralizer (Subgroup.zpowers b : Set X) =
      Subgroup.centralizer ({b} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hJ' : GLAPComponent 3 (L ⊓ Subgroup.centralizer (Subgroup.zpowers b : Set X)) J := by
    rw [hC]
    exact hJ
  have hJeq : J = J₀ := huniq J hJ'
  rw [hJeq]
  exact hLJ₀.trans (sup_le_sup_left
    (glaPPrimeCoreOf_le_of_isSubnormal 3 hL.2.1) J₀)

end CFSG.GroupTheory

end
