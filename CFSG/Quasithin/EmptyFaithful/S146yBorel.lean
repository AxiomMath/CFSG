module

public import CFSG.Quasithin.EmptyFaithful.S146yBorelBender
public import CFSG.Quasithin.EmptyFaithful.S146yBorelL3
public import CFSG.Quasithin.EmptyFaithful.S146yBorelSp

public section

namespace CFSG.Quasithin

theorem borelRigid_of_family {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : E2.IsBenderOf n X ∨ (2 ≤ n ∧ (IsPSL 3 2 n X ∨ E2.IsSp4Prime n X))) : BorelRigid X := by
  rcases h with h | ⟨hn, h | h⟩
  · exact borelRigid_of_isBenderOf h
  · exact borelRigid_psl3 hn h
  · have hn1 : n ≠ 1 := by omega
    exact borelRigid_psp4 hn (by simpa [E2.IsSp4Prime, hn1] using h)

theorem borelAutFree_proof : BorelAutFree :=
  borelAutFree_of_rigid fun _ _ _ _ h => borelRigid_of_family h

end CFSG.Quasithin
