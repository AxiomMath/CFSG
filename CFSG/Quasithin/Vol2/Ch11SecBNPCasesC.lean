module

public import CFSG.Quasithin.Background.E2TwoCLie
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Quasithin.Vol2.Ch11SecBNPE114

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem typeOne_or_lieCases {H T M K : Subgroup Γ} (hc : E2.E22CasesNoN H T M K) :
    TypeOne ↥(E2.star M H K) ∨ E2.E22LieCases H T M K := by
  dsimp only [E2.E22CasesNoN] at hc
  dsimp only [E2.E22LieCases]
  rcases hc with ⟨hJ, t, ht, hne, hM, ⟨n, hn2, hty, hB⟩ | ⟨p, hp, hp8, hK, -, -⟩⟩ |
      ⟨hTK, hJ, ⟨n, hBen, hB⟩ | ⟨n, hn1, hK, hD, hB⟩ | ⟨p, e, hp, hp3, he, hpe8, hK, -, -⟩ |
        ⟨p, hp, hp2, hK, -⟩⟩
  · exact Or.inr (Or.inl ⟨hJ, t, ht, hne, hM, n, hn2, hty, hB⟩)
  · left
    have h1 := hp.one_lt
    have hp2 : p ≠ 2 := by omega
    have h5 : 5 < p ^ 1 := by rw [pow_one]; omega
    exact Or.inr (Or.inr (Or.inl ⟨p, 1, hp, hp2, h5, hK⟩))
  · exact Or.inr (Or.inr ⟨hTK, hJ, Or.inl ⟨n, hBen, hB⟩⟩)
  · rcases Nat.lt_or_ge n 2 with hlt | hge
    · left
      obtain rfl : n = 1 := by omega
      rcases hK with hK | hK
      · exact Or.inl hK
      · exact Or.inr (Or.inl (by simpa [E2.IsSp4Prime] using hK))
    · right
      refine Or.inr ⟨hTK, hJ, Or.inr ⟨n, hge, ?_, hD, hB⟩⟩
      rcases hK with hK | hK
      · exact Or.inl hK
      · right
        rw [E2.IsSp4Prime] at hK
        split_ifs at hK with h1
        · omega
        · exact hK
  · left
    have h5 : 5 ≤ p ^ e := by
      rcases he with rfl | rfl
      · rw [pow_one] at hpe8 ⊢; omega
      · nlinarith
    refine Or.inr (Or.inr (Or.inl ⟨p, e, hp, by omega, ?_, hK⟩))
    generalize p ^ e = q at h5 hpe8 ⊢
    omega
  · left
    rcases hK with ⟨-, hK⟩ | ⟨-, hK, -⟩
    · exact Or.inr (Or.inr (Or.inr ⟨false, p, hp, hp2, hK⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨true, p, hp, hp2, hK⟩))

theorem isSolvable_kerIn_of_e22CasesNoN {H T M K : Subgroup Γ} (hc : E2.E22CasesNoN H T M K) :
    Group.IsSolvable ↥(kerIn M H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hQs : Group.IsSolvable ↥(pCoreOf 2 H) := by
    have := hQ.isNilpotent
    infer_instance
  dsimp only [E2.E22CasesNoN] at hc
  rcases hc with ⟨hJ, -⟩ | ⟨-, hJ, -⟩
  · rw [hJ]
    exact hQs
  · set J := kerIn M H with hJdef
    have hle : (commutator ↥J).map J.subtype ≤ pCoreOf 2 H := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      have := ((hJ a).mp ha).2 b ((hJ b).mp hb).1
      simpa [commutatorElement_def] using this
    have hcomm : ∀ x : ↥(commutator ↥J), ((x : ↥J) : Γ) ∈ pCoreOf 2 H := fun x =>
      hle ⟨x, x.2, rfl⟩
    let j : ↥(commutator ↥J) →* ↥(pCoreOf 2 H) :=
      { toFun := fun x => ⟨((x : ↥J) : Γ), hcomm x⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hj : Function.Injective j := fun a b hab => by
      apply Subtype.ext
      apply Subtype.ext
      simpa [j] using congrArg Subtype.val hab
    have : Group.IsSolvable ↥(commutator ↥J) := Group.isSolvable_of_isSolvable_injective hj
    have hab : Group.IsSolvable (Abelianization ↥J) := inferInstance
    refine Group.isSolvable_of_ker_le_range (commutator ↥J).subtype (Abelianization.of) ?_
    rw [Abelianization.ker_of, Subgroup.range_subtype]

end CFSG.Quasithin.Vol2.Ch11.SecB
