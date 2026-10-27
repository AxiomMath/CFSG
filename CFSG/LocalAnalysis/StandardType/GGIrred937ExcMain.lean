module

public import CFSG.LocalAnalysis.StandardType.GGIrred937ExcWeylE7
public import CFSG.LocalAnalysis.StandardType.GGIrred937ExcWeylE8
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMonomialIrred

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly

section Main

theorem ggSCWeylIrred_adjoint_E8_add
    {p : ℕ} (hp35 : p = 3 ∨ p = 5) (K : Type) [Field K]
    [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K + 1) :
    GGSCWeylIrred p 7 (adjointGroup .E8 K) := by
  intro E hE hr hr3 hSC
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hp⟩
  have hrank : Tag.E8.rank - 1 = 7 := by decide
  have hr' : p ^ (Tag.E8.rank - 1) ≤ Nat.card E := by rw [hrank]; exact hr
  have hSC' : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .E8 K)),
      x ^ p = 1 → x ∈ E := by
    intro x hx hxp
    rw [Subgroup.mem_centralizer_iff] at hx
    exact hSC x (fun e he => (hx e he).symm) hxp
  have hF := exists_langFrame_of_sc (Or.inr rfl) hp35 K hpq E hE hr' hSC'
  obtain ⟨ι₀, m, hinj, hrange, hm⟩ := exists_realization_E8 K E hF
  have h : GGWeylIrred ι₀.range :=
    ggWeylIrred_range_of_torusAct ι₀ hinj m hm (latticeIrred_E8 hp35)
  rwa [hrange] at h

theorem ggSCWeylIrred_adjoint_E7_add
    {p : ℕ} (hp35 : p = 3 ∨ p = 5) (K : Type) [Field K]
    [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K + 1) :
    GGSCWeylIrred p 6 (adjointGroup .E7 K) := by
  intro E hE hr hr3 hSC
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hp⟩
  have hrank : Tag.E7.rank - 1 = 6 := by decide
  have hr' : p ^ (Tag.E7.rank - 1) ≤ Nat.card E := by rw [hrank]; exact hr
  have hSC' : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .E7 K)),
      x ^ p = 1 → x ∈ E := by
    intro x hx hxp
    rw [Subgroup.mem_centralizer_iff] at hx
    exact hSC x (fun e he => (hx e he).symm) hxp
  have hF := exists_langFrame_of_sc (Or.inl rfl) hp35 K hpq E hE hr' hSC'
  exact weylIrred_E7_of_langFrame hp35 K hpq E hF

theorem ggNbrKGExcPlusSCWeylIrred_holds :
    GGNbrKGExcPlusSCWeylIrred := by
  intro K _ _ _ p hp35 hpq
  constructor
  · exact ggSCWeylIrred_of_mulEquiv (TableBExc.recipeEquiv .E7 K)
      (ggSCWeylIrred_adjoint_E7_add hp35 K hpq)
  · exact ggSCWeylIrred_of_mulEquiv (TableBExc.recipeEquiv .E8 K)
      (ggSCWeylIrred_adjoint_E8_add hp35 K hpq)

end Main

end Irred937

end CFSG.StandardType
