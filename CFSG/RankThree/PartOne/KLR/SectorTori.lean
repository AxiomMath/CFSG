module

public import CFSG.RankThree.PartOne.KLR.TorusGeneric
public import CFSG.RankThree.Lattice.SteinbergBIChecks
public import CFSG.RankThree.PartOne.KE.CTStatement

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.RankThree.Lattice


theorem smul_single_eq_lget (l : List (Fin ReeTag.F4.tag.rank)) (L : List (List ℤ))
    (h : wordMat ReeTag.F4.tag l = toMat ReeTag.F4.tag.rank L)
    (k i : Fin ReeTag.F4.tag.rank) :
    ((coxeterSystem ReeTag.F4.tag).wordProd l • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) i =
      lget L i k := by
  rw [wordProd_smul_eq_wordMat_mulVec, h, Matrix.mulVec_single_one]
  rfl

section Phi2

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

@[expose] noncomputable def wPhi2 : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0]

theorem torus_phi2 (hF : IsReeFrob a F) :
    ∃ E : Subgroup (ModGL ReeTag.F4.tag L), E ≤ torusGroup ReeTag.F4.tag L ∧
      E ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2) ∧
      Nat.card E = (2 ^ (2 * a + 1) + 1) ^ 2 := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, -1, 1, 0], [-3, 0, 1, 0], [-4, 0, 1, 1], [-2, 0, 1, 0]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  have hm : Odd (2 ^ (2 * a + 1) + 1) := by
    refine Even.add_one ?_
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  refine exists_twisted_subgroup hF wPhi2 (2 ^ (2 * a + 1) + 1) hm
    (toMat 4 [[-1, -1, 1, 0], [-3, 0, 1, 0], [-4, 0, 1, 1], [-2, 0, 1, 0]])
    ![![0, -1, 0, 1 - 2 ^ a], ![-1, -1, -2 ^ a, 2]] 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · exact ⟨-1, 0, by norm_num⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget] <;>
      refine Int.modEq_iff_dvd.2 ?_ <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)


end Phi2

section Phi1

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

@[expose] noncomputable def wPhi1 : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd []

theorem torus_phi1 (hF : IsReeFrob a F) :
    ∃ E : Subgroup (ModGL ReeTag.F4.tag L), E ≤ torusGroup ReeTag.F4.tag L ∧
      E ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi1) ∧
      Nat.card E = (2 ^ (2 * a + 1) - 1) ^ 2 := by
  have hW : wordMat ReeTag.F4.tag [] =
      toMat ReeTag.F4.tag.rank [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  have h2 : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hm : Odd (2 ^ (2 * a + 1) - 1) := by
    rw [Nat.odd_iff]
    omega
  have hmc : (((2 ^ (2 * a + 1) - 1 : ℕ)) : ℤ) = 2 ^ (2 * a + 1) - 1 := by
    push_cast [Nat.cast_sub h1]
    ring
  refine exists_twisted_subgroup hF wPhi1 (2 ^ (2 * a + 1) - 1) hm
    (toMat 4 [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    ![![-1, 0, 0, -2 ^ a], ![0, -1, -2 ^ a, 0]] 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · rw [hmc]
    exact ⟨1, 0, by norm_num⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget, hmc] <;>
      refine Int.modEq_iff_dvd.2 ?_ <;>
      first
        | (refine ⟨1, ?_⟩; ring1)

end Phi1

section Phi4

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

@[expose] noncomputable def wPhi4m : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd [0, 1, 0, 2, 1, 0]

theorem torus_phi4m (hF : IsReeFrob a F) :
    ∃ E : Subgroup (ModGL ReeTag.F4.tag L), E ≤ torusGroup ReeTag.F4.tag L ∧
      E ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi4m) ∧
      Nat.card E = (2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) ^ 2 := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  have h2 : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
  have h2' : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (by omega)
  have hle : 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm : Odd (2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) := by
    rw [Nat.odd_iff]
    omega
  have hmc : (((2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 : ℕ)) : ℤ) =
      2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 := by
    push_cast [Nat.cast_sub hle]
    ring
  refine exists_twisted_subgroup hF wPhi4m (2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) hm
    (toMat 4 [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]])
    ![![-1, 0, 0, 1 - 2 ^ a], ![-1, -1, 1 - 2 ^ a, 1]] 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · rw [hmc]
    exact ⟨1, 0, by norm_num⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget, hmc] <;>
      refine Int.modEq_iff_dvd.2 ?_ <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)

@[expose] noncomputable def wPhi4p : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0]

theorem torus_phi4p (hF : IsReeFrob a F) :
    ∃ E : Subgroup (ModGL ReeTag.F4.tag L), E ≤ torusGroup ReeTag.F4.tag L ∧
      E ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi4p) ∧
      Nat.card E = (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) ^ 2 := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 0], [-1, -1, 0, 1], [-2, -2, 1, 1], [-2, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  have h2 : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
  have h2' : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (by omega)
  have hm : Odd (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) := by
    rw [Nat.odd_iff]
    omega
  refine exists_twisted_subgroup hF wPhi4p (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) hm
    (toMat 4 [[-1, 0, 0, 0], [-1, -1, 0, 1], [-2, -2, 1, 1], [-2, 0, 0, 1]])
    ![![-1, 0, 0, -2 ^ a], ![-1, -1, -2 ^ a, 1]] 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · exact ⟨1, 0, by norm_num⟩
  · intro s k
    fin_cases s <;> fin_cases k <;>
      simp [Fin.sum_univ_succ, toMat, lget] <;>
      refine Int.modEq_iff_dvd.2 ?_ <;>
      first
        | (refine ⟨0, ?_⟩; ring1)
        | (refine ⟨-1, ?_⟩; ring1)

end Phi4

end CFSG.RankThree.PartOne.KLR
