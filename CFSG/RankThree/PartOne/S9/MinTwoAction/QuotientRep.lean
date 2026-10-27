module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientDefs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction

public section

namespace CFSG.RankThree.PartOne.Quotient36

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
open scoped IsMulCommutative

section Rep

variable {E X : Type*} [Group E] [Group X] [Finite X] [MulDistribMulAction E X] (q : ℕ)
  [Fact q.Prime] [Fact (IsPGroup q X)]

instance instIsElementaryAbelianFrattiniQuotient : IsElementaryAbelian q (X ⧸ frattini X) :=
  isElementaryAbelian_quotient_frattini (p := q) (R := X)

@[expose] noncomputable def frattiniRep :
    Representation (ZMod q) E (Additive (X ⧸ frattini X)) :=
  letI := frattiniQuotientAction E X
  Theory.Representation.ofElementaryAbelianAction (A := E) (G := X ⧸ frattini X) (p := q)

theorem frattiniRep_apply (e : E) (v : X ⧸ frattini X) :
    frattiniRep (E := E) (X := X) q e (Additive.ofMul v) =
      Additive.ofMul (letI := frattiniQuotientAction E X; e • v) := by
  let _ := frattiniQuotientAction E X
  exact Theory.Representation.ofElementaryAbelianAction_apply_ofMul (A := E)
    (G := X ⧸ frattini X) (p := q) e v

theorem frattiniRep_apply_mk (e : E) (x : X) :
    frattiniRep (E := E) (X := X) q e (Additive.ofMul (x : X ⧸ frattini X)) =
      Additive.ofMul ((e • x : X) : X ⧸ frattini X) := by
  rw [frattiniRep_apply]
  rfl

@[expose] def toSubgroup (U : Submodule (ZMod q) (Additive (X ⧸ frattini X))) :
    Subgroup (X ⧸ frattini X) where
  carrier := {v | Additive.ofMul v ∈ U}
  mul_mem' {a b} ha hb := by
    change Additive.ofMul (a * b) ∈ U
    rw [ofMul_mul]
    exact U.add_mem ha hb
  one_mem' := U.zero_mem
  inv_mem' {a} ha := by
    change Additive.ofMul a⁻¹ ∈ U
    rw [ofMul_inv]
    exact U.neg_mem ha

theorem mem_toSubgroup (U : Submodule (ZMod q) (Additive (X ⧸ frattini X)))
    (v : X ⧸ frattini X) : v ∈ toSubgroup q U ↔ Additive.ofMul v ∈ U := Iff.rfl

theorem toSubgroup_eq_bot_iff (U : Submodule (ZMod q) (Additive (X ⧸ frattini X))) :
    toSubgroup q U = ⊥ ↔ U = ⊥ := by
  constructor
  · intro h
    rw [Submodule.eq_bot_iff]
    intro w hw
    have : Additive.toMul w ∈ toSubgroup q U := by
      rw [mem_toSubgroup]
      simpa using hw
    rw [h, Subgroup.mem_bot] at this
    exact toMul_eq_one.mp this
  · intro h
    rw [Subgroup.eq_bot_iff_forall]
    intro v hv
    rw [mem_toSubgroup, h, Submodule.mem_bot] at hv
    exact ofMul_eq_zero.mp hv

theorem toSubgroup_eq_top_iff (U : Submodule (ZMod q) (Additive (X ⧸ frattini X))) :
    toSubgroup q U = ⊤ ↔ U = ⊤ := by
  constructor
  · intro h
    rw [Submodule.eq_top_iff']
    intro w
    have : Additive.toMul w ∈ toSubgroup q U := by rw [h]; exact Subgroup.mem_top _
    simpa [mem_toSubgroup] using this
  · intro h
    rw [Subgroup.eq_top_iff']
    intro v
    rw [mem_toSubgroup, h]
    exact Submodule.mem_top

theorem toSubgroup_invariant (U : Submodule (ZMod q) (Additive (X ⧸ frattini X)))
    (hU : ∀ e : E, ∀ w ∈ U, frattiniRep (E := E) (X := X) q e w ∈ U) :
    letI := frattiniQuotientAction E X
    ∀ e : E, ∀ v ∈ toSubgroup q U, e • v ∈ toSubgroup q U := by
  intro e v hv
  have h := hU e (Additive.ofMul v) hv
  rw [frattiniRep_apply] at h
  exact h

@[expose] def toSubmodule
    (T : Subgroup (X ⧸ frattini X)) : Submodule (ZMod q) (Additive (X ⧸ frattini X)) :=
  (AddSubgroup.toZModSubmodule (n := q) (Subgroup.toAddSubgroup T))

theorem mem_toSubmodule (T : Subgroup (X ⧸ frattini X)) (w : Additive (X ⧸ frattini X)) :
    w ∈ toSubmodule q T ↔ Additive.toMul w ∈ T := Iff.rfl

theorem toSubgroup_toSubmodule (T : Subgroup (X ⧸ frattini X)) :
    toSubgroup q (toSubmodule q T) = T := by
  ext v
  rw [mem_toSubgroup, mem_toSubmodule]
  rfl

theorem isIrreducible_frattiniRep (h : IrredFrattini E X) :
    (frattiniRep (E := E) (X := X) q).IsIrreducible := by
  obtain ⟨hnt, hirr⟩ := h
  have hne : (⊥ : Subrepresentation (frattiniRep (E := E) (X := X) q)) ≠ ⊤ := by
    intro hbt
    obtain ⟨v, hv⟩ := exists_ne (1 : X ⧸ frattini X)
    have h1 : Additive.ofMul v ∈ (⊤ : Subrepresentation (frattiniRep (E := E) (X := X) q)) :=
      Submodule.mem_top
    rw [← hbt] at h1
    exact hv (ofMul_eq_zero.mp (Submodule.mem_bot _ |>.mp h1))
  have : Nontrivial (Subrepresentation (frattiniRep (E := E) (X := X) q)) := ⟨⟨⊥, ⊤, hne⟩⟩
  refine { eq_bot_or_eq_top := fun U => ?_ }
  have hinv : letI := frattiniQuotientAction E X
      ∀ e : E, ∀ v ∈ toSubgroup q U.toSubmodule, e • v ∈ toSubgroup q U.toSubmodule :=
    toSubgroup_invariant q U.toSubmodule fun e w hw => U.apply_mem_toSubmodule e hw
  rcases hirr _ hinv with h0 | h1
  · left
    exact Subrepresentation.ext ((toSubgroup_eq_bot_iff q U.toSubmodule).mp h0)
  · right
    exact Subrepresentation.ext ((toSubgroup_eq_top_iff q U.toSubmodule).mp h1)

end Rep

end CFSG.RankThree.PartOne.Quotient36
