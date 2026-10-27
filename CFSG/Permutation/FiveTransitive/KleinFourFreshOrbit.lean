module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic

public section

namespace CFSG

namespace FiveTransitive.KleinFourFreshOrbit

open MulAction

private theorem smul_not_fixedBy
    {G X : Type*} [Group G] [MulAction G X] (u v : G) (huv : u * v = v * u)
    (x : X) (hx : x ∉ fixedBy X v) : u • x ∉ fixedBy X v := by
  intro he
  apply hx
  change v • x = x
  apply (MulAction.toPerm u).injective
  change u • (v • x) = u • x
  rw [←mul_smul,huv,mul_smul]
  exact he

theorem orbit_embedding
    {G X : Type*} [Group G] [MulAction G X]
    (a c : G) (ha : a * a = 1) (hc : c * c = 1) (hac : a * c = c * a)
    (s : Set X) (hs : s = fixedBy X a ∪ fixedBy X c ∪ fixedBy X (a * c))
    (x : X) (hx : x ∉ s) :
    ∃ f : Fin 4 ↪ X, (∀ i, f i ∉ s) ∧
      a • f 0 = f 1 ∧ a • f 1 = f 0 ∧ a • f 2 = f 3 ∧ a • f 3 = f 2 ∧
      c • f 0 = f 2 ∧ c • f 2 = f 0 ∧ c • f 1 = f 3 ∧ c • f 3 = f 1 := by
  have haa (z : X) : a • (a • z) = z := by rw [←mul_smul,ha,one_smul]
  have hcc (z : X) : c • (c • z) = z := by rw [←mul_smul,hc,one_smul]
  have hacs (z : X) : c • (a • z) = a • (c • z) := by rw [←mul_smul,←hac,mul_smul]
  have hna : a • x ≠ x := by intro he; exact hx (hs ▸ Or.inl (Or.inl he))
  have hnc : c • x ≠ x := by intro he; exact hx (hs ▸ Or.inl (Or.inr he))
  have hnac : a • (c • x) ≠ x := by
    intro he
    exact hx (hs ▸ Or.inr (show x ∈ fixedBy X (a * c) by change (a * c) • x = x; simpa only [mul_smul] using he))
  have h12 : a • x ≠ c • x := by
    intro he
    have hh := congrArg (fun z : X => a • z) he
    rw [haa] at hh
    exact hnac hh.symm
  have h13 : a • x ≠ a • (c • x) := by
    intro he
    exact hnc ((MulAction.toPerm a).injective he).symm
  have h23 : c • x ≠ a • (c • x) := by
    intro he
    have hh := congrArg (fun z : X => c • z) he
    rw [hcc,hacs,hcc] at hh
    exact hna hh.symm
  have haux (u : G) (hua : u * a = a * u) (huc : u * c = c * u)
      (z : X) (hz : z ∉ s) : u • z ∉ s := by
    rw [hs] at hz ⊢
    intro he
    rcases he with (he | he) | he
    · exact smul_not_fixedBy u a hua z (fun h => hz (Or.inl (Or.inl h))) he
    · exact smul_not_fixedBy u c huc z (fun h => hz (Or.inl (Or.inr h))) he
    · have huac : u * (a * c) = (a * c) * u := by rw [←mul_assoc,hua,mul_assoc,huc,←mul_assoc]
      exact smul_not_fixedBy u (a * c) huac z (fun h => hz (Or.inr h)) he
  have hax := haux a rfl hac x hx
  have hcx := haux c hac.symm rfl x hx
  have hacx := haux a rfl hac (c • x) hcx
  let f : Fin 4 → X := ![x,a • x,c • x,a • (c • x)]
  have hf : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact (hna he).elim
      | exact (hna he.symm).elim
      | exact (hnc he).elim
      | exact (hnc he.symm).elim
      | exact (hnac he).elim
      | exact (hnac he.symm).elim
      | exact (h12 he).elim
      | exact (h12 he.symm).elim
      | exact (h13 he).elim
      | exact (h13 he.symm).elim
      | exact (h23 he).elim
      | exact (h23 he.symm).elim
  refine ⟨⟨f,hf⟩,?_,rfl,haa x,rfl,haa (c • x),rfl,hcc x,hacs x,?_⟩
  · intro i
    fin_cases i
    · exact hx
    · exact hax
    · exact hcx
    · exact hacx
  · change c • (a • (c • x)) = a • x
    rw [hacs,hcc]

end FiveTransitive.KleinFourFreshOrbit

end CFSG
