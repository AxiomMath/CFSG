module

public import CFSG.Quasithin.Vol2.Ch11SecBNPE114
public import CFSG.Quasithin.Background.E2Two
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

theorem TypeOne.isSimpleGroup {Y : Type} [Group Y] (h : TypeOne Y) : IsSimpleGroup Y := by
  rcases h with h | h | ⟨p, f, -, -, -, h⟩ | ⟨s, p, -, -, h⟩
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 3 2 1 h).2
  · obtain ⟨e⟩ : Nonempty (Y ≃* alternatingGroup (Fin 6)) := h
    have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 2 p f h).2
  · cases s with
    | true => exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 3 p 1 h).2
    | false => exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity Y 3 p 1 h).2

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem le_one_of_nParam_eq {H : Subgroup Γ} {n : ℕ} (hn : E1.nParam H ≤ 1)
    (h : E1.nParam H = n) : n ≤ 1 := by
  rw [h] at hn
  exact_mod_cast hn

omit [Finite Γ] in
theorem typeOne_star_of_e22Cases {H T M K : Subgroup Γ} (hc : E2.E22Cases H T M K)
    (hn : E1.nParam H ≤ 1) : TypeOne ↥(E2.star M H K) := by
  dsimp only [E2.E22Cases] at hc
  rcases hc with ⟨-, -, -, -, -, hcase⟩ | ⟨-, -, hcase⟩
  · rcases hcase with ⟨n, hn2, -, -, hnH⟩ | ⟨p, hp, hp8, hK, -⟩
    · exact absurd (le_one_of_nParam_eq hn hnH) (by omega)
    · have h1 := hp.one_lt
      have hp2 : p ≠ 2 := by omega
      have h5 : 5 < p ^ 1 := by rw [pow_one]; omega
      exact Or.inr (Or.inr (Or.inl ⟨p, 1, hp, hp2, h5, hK⟩))
  · rcases hcase with ⟨n, ⟨hn2, -⟩, -, hnH⟩ | ⟨n, hn1, hK, -, -, hnH⟩ |
        ⟨p, e, hp, hp3, he, hpe8, hK, -⟩ | ⟨p, hp, hp2, hK, -⟩
    · exact absurd (le_one_of_nParam_eq hn hnH) (by omega)
    · have hn' : n = 1 := le_antisymm (le_one_of_nParam_eq hn hnH) hn1
      subst hn'
      rcases hK with hK | hK
      · exact Or.inl hK
      · exact Or.inr (Or.inl (by simpa [E2.IsSp4Prime] using hK))
    · have h5 : 5 ≤ p ^ e := by
        rcases he with rfl | rfl
        · rw [pow_one] at hpe8 ⊢; omega
        · nlinarith
      refine Or.inr (Or.inr (Or.inl ⟨p, e, hp, by omega, ?_, hK⟩))
      generalize p ^ e = q at h5 hpe8 ⊢
      omega
    · rcases hK with ⟨-, hK⟩ | ⟨-, hK, -⟩
      · exact Or.inr (Or.inr (Or.inr ⟨false, p, hp, hp2, hK⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨true, p, hp, hp2, hK⟩))

theorem isSolvable_kerIn_of_e22Cases {H T M K : Subgroup Γ} (hc : E2.E22Cases H T M K) :
    Group.IsSolvable ↥(kerIn M H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hQs : Group.IsSolvable ↥(pCoreOf 2 H) := by
    have := hQ.isNilpotent
    infer_instance
  dsimp only [E2.E22Cases] at hc
  rcases hc with ⟨hJ, -⟩ | ⟨-, hJ, -⟩
  · rw [hJ]
    exact hQs
  ·
    set J := kerIn M H with hJdef
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
