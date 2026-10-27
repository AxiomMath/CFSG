module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallSound

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def Pt.Closed (P : Pt) [Fact P.p.Prime] : Prop :=
  (∃ g ∈ P.group, IsTransv g) ∨ P.bound < Nat.card P.group ∨ P.FrameViolation ∨
    CFSG.StandardType.ZS.LinWeyl P.p P.group

theorem verify_closed {P : Pt}
    [Fact P.p.Prime] {w : Witness} (h : verify P w = true) : P.Closed :=
  verify_elim h (fun hK => Or.inr (Or.inr (Or.inl hK))) Or.inl (fun hO => Or.inr (Or.inl hO))
    (fun hW => Or.inr (Or.inr (Or.inr hW)))

theorem check1_closed {P : Pt}
    [Fact P.p.Prime] (h : check1 P = true) : P.Closed :=
  check1_elim h (fun hK => Or.inr (Or.inr (Or.inl hK))) Or.inl (fun hO => Or.inr (Or.inl hO))
    (fun hW => Or.inr (Or.inr (Or.inr hW)))

theorem nineDepCheck_iff : nineDepCheck () = true ↔
    ∀ P ∈ pts8 () ++ pts9 () ++ pts9m (), check1 P = true := by
  simp [nineDepCheck, List.all_eq_true, List.mem_append, or_imp, forall_and]

theorem bound9_eq : bound9 = 3 ^ 9 * (6 * (3 - 1) * Nat.factorial 9) := by
  decide +kernel

end CFSG.TwoNodeSmall
