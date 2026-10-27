module

public import CFSG.RankThree.PartOne.KE6.Phi3Orbit
public import CFSG.RankThree.PartOne.KE6.Phi3Std
public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityConjugacy

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
open CFSG.RankThree.Lattice (e6T3W toMat lmul lget)

@[expose] def e6D4Table : List (List (List ℤ) × ℕ × List (Fin 4)) :=
  [([[0, 0, 0, 0, 0, -1], [1, 0, 0, 0, -1, 0], [1, 1, 0, -1, 0, -1], [1, 1, 1, -1, -1, -1], [1, 1, 0, 0, -1, -1], [1, 0, 0, 0, 0, -1]], 1, [1, 0, 2, 3, 1, 0, 2, 0]),
    ([[0, 0, 0, 0, 0, -1], [0, -1, 1, 0, 0, -1], [1, -1, 0, 0, 0, -1], [1, -1, 1, 0, -1, -1], [1, -1, 0, 1, -1, -1], [1, 0, 0, 0, 0, -1]], 1, [1, 2, 3, 1, 0, 2, 1, 0]),
    ([[0, 0, 0, 0, 0, -1], [1, 0, 0, 0, -1, 0], [1, 0, -1, 1, -1, -1], [2, 1, -1, 0, -1, -1], [1, 1, 0, 0, -1, -1], [1, 0, 0, 0, 0, -1]], 1, [2, 1, 0, 2, 3, 1, 2, 0]),
    ([[0, 0, 0, 0, 0, -1], [1, 0, 0, -1, 1, -1], [1, 1, 0, -1, 0, -1], [1, 1, 1, -2, 1, -2], [1, 0, 1, -1, 0, -1], [1, 0, 0, 0, 0, -1]], 1, [1, 0, 2, 3, 2, 1, 0, 2]),
    ([[0, 0, 0, 0, 0, -1], [1, -1, -1, 1, 0, -1], [1, 0, -1, 1, -1, -1], [2, -1, -1, 1, -1, -1], [1, -1, 0, 1, -1, -1], [1, 0, 0, 0, 0, -1]], 1, [2, 1, 0, 2, 3, 2, 1, 0]),
    ([[0, 0, 0, 0, 0, -1], [0, -1, 1, 0, 0, -1], [1, -1, 0, 0, 0, -1], [1, -1, 1, -1, 1, -2], [1, 0, 1, -1, 0, -1], [1, 0, 0, 0, 0, -1]], 1, [1, 2, 3, 2, 1, 0, 2, 1]),
    ([[0, 0, 0, 0, 0, -1], [1, 0, 0, -1, 1, -1], [1, 0, -1, 0, 1, -2], [2, 1, -1, -1, 1, -2], [2, 0, -1, 0, 0, -1], [1, 0, 0, 0, 0, -1]], 1, [3, 2, 1, 0, 2, 3, 1, 2]),
    ([[0, 0, 0, 0, 0, -1], [1, -1, -1, 1, 0, -1], [1, 0, -1, 0, 1, -2], [2, -1, -1, 0, 1, -2], [2, 0, -1, 0, 0, -1], [1, 0, 0, 0, 0, -1]], 1, [3, 2, 1, 0, 2, 3, 2, 1]),
    ([[-1, 0, 0, 0, 0, 1], [-1, 0, 1, -1, 0, 1], [-1, 0, 0, 0, -1, 2], [-2, 1, 1, -1, -1, 2], [-2, 0, 1, 0, -1, 1], [-1, 0, 0, 0, 0, 0]], 2, [1, 0, 2, 3, 1, 0, 2, 1]),
    ([[-1, 0, 0, 0, 0, 1], [0, 0, -1, 0, 0, 1], [-1, 1, -1, 0, 0, 1], [-1, 1, -1, 0, -1, 2], [-1, 0, -1, 1, -1, 1], [-1, 0, 0, 0, 0, 0]], 2, [0, 2, 3, 1, 0, 2, 1, 0]),
    ([[-1, 0, 0, 0, 0, 1], [-1, -1, 0, 1, -1, 1], [-1, 0, 0, 0, -1, 2], [-2, -1, 1, 0, -1, 2], [-2, 0, 1, 0, -1, 1], [-1, 0, 0, 0, 0, 0]], 2, [2, 1, 0, 2, 3, 0, 2, 1]),
    ([[-1, 0, 0, 0, 0, 1], [-1, 0, 1, -1, 0, 1], [-1, 0, 0, -1, 1, 1], [-2, 1, 1, -2, 1, 1], [-1, 1, 0, -1, 0, 1], [-1, 0, 0, 0, 0, 0]], 2, [1, 0, 2, 3, 2, 1, 0, 2]),
    ([[-1, 0, 0, 0, 0, 1], [-1, -1, 0, 1, -1, 1], [-1, -1, -1, 1, 0, 1], [-1, -1, -1, 1, -1, 2], [-1, 0, -1, 1, -1, 1], [-1, 0, 0, 0, 0, 0]], 2, [2, 1, 0, 2, 3, 2, 1, 0]),
    ([[-1, 0, 0, 0, 0, 1], [0, 0, -1, 0, 0, 1], [-1, 1, -1, 0, 0, 1], [-1, 1, -1, -1, 1, 1], [-1, 1, 0, -1, 0, 1], [-1, 0, 0, 0, 0, 0]], 2, [0, 2, 3, 2, 1, 0, 2, 0]),
    ([[-1, 0, 0, 0, 0, 1], [-1, -1, 0, 0, 1, 0], [-1, 0, 0, -1, 1, 1], [-2, -1, 1, -1, 1, 1], [-1, -1, 0, 0, 0, 1], [-1, 0, 0, 0, 0, 0]], 2, [3, 2, 1, 0, 2, 3, 0, 2]),
    ([[-1, 0, 0, 0, 0, 1], [-1, -1, 0, 0, 1, 0], [-1, -1, -1, 1, 0, 1], [-1, -1, -1, 0, 1, 1], [-1, -1, 0, 0, 0, 1], [-1, 0, 0, 0, 0, 0]], 2, [3, 2, 1, 0, 2, 3, 2, 0])]

@[expose] def d4TableOK (L : List (List ℤ)) (e : ℕ) (ω : List (Fin 4)) : Prop :=
  ∀ m : Fin 72, e6RootVec m 0 = 0 → e6RootVec m 5 = 0 →
    (toMat Tag.E6.rank L).mulVec (e6RootVec m) =
      d4Lat (ω.foldr (reflect Tag.D4)
        (permLattice (d4RhoPerm ^ e) (fun k => e6RootVec m (d4Idx k))))

@[expose] def d4Pres (L : List (List ℤ)) : Prop :=
  ∀ j : Fin 6, 1 ≤ j.val → j.val ≤ 4 → lget L 0 j = 0 ∧ lget L 5 j = 0

instance (L : List (List ℤ)) : Decidable (d4Pres L) := by unfold d4Pres; infer_instance

theorem e6D4Table_ok : ∀ ent ∈ e6D4Table, d4TableOK ent.1 ent.2.1 ent.2.2 := by
  unfold d4TableOK
  decide +kernel

theorem e6D4Table_exp : ∀ ent ∈ e6D4Table, ent.2.1 = 1 ∨ ent.2.1 = 2 := by
  decide +kernel

theorem e6D4Table_complete : ∀ L ∈ e6T3Orbit, d4Pres L → ∃ ent ∈ e6D4Table, ent.1 = L := by
  unfold d4Pres
  decide +kernel

theorem d4TrialityWeylType_of_conj {T : WeylGroup Tag.E6} {L : List (List ℤ)}
    (hL : L ∈ e6T3Orbit) (hLT : weylMatrix T = toMat Tag.E6.rank L)
    (hT : ∀ α ∈ parabolicRoots Tag.E6 d4Support, T • α ∈ parabolicRoots Tag.E6 d4Support) :
    ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ D4TrialityWeylType T e := by
  have key : ∀ j i : Fin 6, 1 ≤ j.val → j.val ≤ 4 → (i ≠ 0 ∧ i ≠ 5 → False) → i ≠ j := by
    decide
  have hsingle : ∀ j : Fin 6, 1 ≤ j.val → j.val ≤ 4 →
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 d4Support := by
    intro j hj1 hj4
    exact ⟨isRoot_single Tag.E6 j, fun i hi => Pi.single_eq_of_ne (key j i hj1 hj4 hi) 1⟩
  have hpres : d4Pres L := by
    intro j hj1 hj4
    have h := hT _ (hsingle j hj1 hj4)
    have h0 := h.2 0 (by simp [d4Support])
    have h5 := h.2 5 (by simp [d4Support])
    exact ⟨(smul_single_apply_eq_lget hLT 0 j).symm.trans h0,
      (smul_single_apply_eq_lget hLT 5 j).symm.trans h5⟩
  obtain ⟨ent, hent, rfl⟩ := e6D4Table_complete L hL hpres
  refine ⟨ent.2.1, e6D4Table_exp ent hent, (coxeterSystem Tag.D4).wordProd ent.2.2, ?_⟩
  intro β hβ
  obtain ⟨m, hm⟩ := isRoot_iff_exists_e6RootVec.1 ((isRoot_d4Lat_iff).2 hβ)
  have hok := e6D4Table_ok ent hent m (by rw [hm]; rfl) (by rw [hm]; rfl)
  rw [hm] at hok
  have hβ' : (fun k => d4Lat β (d4Idx k)) = β := funext fun k => d4Lat_apply_d4Idx β k
  rw [hβ'] at hok
  rw [← weylMatrix_mulVec, hLT, hok]
  exact congrArg d4Lat
    (wordProd_smul (τ := Tag.D4) ent.2.2 (permLattice (d4RhoPerm ^ ent.2.1) β)).symm

end CFSG.RankThree.PartOne.KE6
