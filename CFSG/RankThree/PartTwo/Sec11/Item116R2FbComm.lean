module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1RankTwoPure

public section

open Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem not_isRankTwoByCyclic_of_commutator_cubeRoots {S : Type*} [Group S] [Finite S]
    (h : 9 < Nat.card {x : ↥(commutator S) // x ^ 3 = 1}) : ¬ IsRankTwoByCyclic S := by
  rintro ⟨N, hN, -, hrank, hcyc⟩
  have hcomm' : ∀ a b : S ⧸ N, a * b = b * a := fun a b => by
    letI := IsCyclic.commGroup (α := S ⧸ N)
    exact mul_comm a b
  have hle : commutator S ≤ N := by
    rw [commutator_eq_closure]
    refine (Subgroup.closure_le N).2 ?_
    rintro _ ⟨x, y, rfl⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, commutatorElement_def]
    have := hcomm' (QuotientGroup.mk x) (QuotientGroup.mk y)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [this]
    group
  let f : {x : ↥(commutator S) // x ^ 3 = 1} → {y : ↥N // y ^ 3 = 1} := fun x =>
    ⟨⟨x.1.1, hle x.1.2⟩, Subtype.ext (by simpa using congrArg (fun z : ↥(commutator S) => (z : S)) x.2)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have : (x.1.1 : S) = y.1.1 := congrArg (fun z : {y : ↥N // y ^ 3 = 1} => ((z.1 : ↥N) : S)) hxy
    exact Subtype.ext (Subtype.ext this)
  have := Nat.card_le_card_of_injective f hf
  omega

end CFSG.RankThree.PartTwo.Sec11
