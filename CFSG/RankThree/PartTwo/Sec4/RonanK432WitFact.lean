module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Wit3
public import CFSG.RankThree.PartTwo.Sec4.RonanK432WitCheck

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Monster.B.Co2 (permOfArr)

@[expose] noncomputable def genSub (n : ℕ) (S : Array (Array ℕ)) (j : ℕ) :
    Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {g | ∃ k < j, permOfArr n S[k]! = g}

@[expose] def WitFact (X : WitData) : Prop :=
  ∃ P : Subgroup (Equiv.Perm (Fin X.n)), P ≤ genSub X.n X.gens X.gens.size ∧
    Nat.card P = X.pOrd ∧ ∀ σ ∈ P, σ ≠ 1 → σ ^ 3 = 1 → Wit3 (genSub X.n X.gens X.nGens) σ

theorem WitFact.apply {X : WitData} (h : WitFact X) (G N : Subgroup (Equiv.Perm (Fin X.n)))
    (hG : ∀ k < X.gens.size, permOfArr X.n X.gens[k]! ∈ G)
    (hN : ∀ k < X.nGens, permOfArr X.n X.gens[k]! ∈ N) :
    ∃ P : Subgroup (Equiv.Perm (Fin X.n)), P ≤ G ∧ Nat.card P = X.pOrd ∧
      ∀ σ ∈ P, σ ≠ 1 → σ ^ 3 = 1 → Wit3 N σ := by
  obtain ⟨P, hP, hc, hw⟩ := h
  have hG' : genSub X.n X.gens X.gens.size ≤ G := by
    rw [genSub, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hG k hk
  have hN' : genSub X.n X.gens X.nGens ≤ N := by
    rw [genSub, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hN k hk
  refine ⟨P, hP.trans hG', hc, fun σ hσ h1 h3 => ?_⟩
  obtain ⟨y, hy, hcomm, hn⟩ := hw σ hσ h1 h3
  exact ⟨y, hN' hy, hcomm, hn⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
