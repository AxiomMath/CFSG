module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenArr
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenJ2HSMcLCheck
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (GJ xJ yJ P3 Ej xArr zArr)
open scoped commutatorElement

namespace Item434SporGen


theorem j2_chain :
    rawChainOK 315 ((pushWords 315 j2SigArrs j2Words).extract 0 j2SigArrs.size)
      (pushWords 315 j2SigArrs j2Words) (j2Base.map Fin.val).toArray
      (wordsOf j2SigArrs.size j2Words) 4 = true := by
  have h := j2_chain_check
  simp only [j2ChainCheck, Bool.and_eq_true] at h
  exact h.1

theorem j2_orbits :
    rawOrbitSizes 315 (pushWords 315 j2SigArrs j2Words) (j2Base.map Fin.val).toArray =
      [315, 32, 20, 3] := by
  have h := j2_chain_check
  simp only [j2ChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem j2_sifts :
    siftA 315 (rawLevels 315 (pushWords 315 j2SigArrs j2Words) (j2Base.map Fin.val).toArray)
        (j2Base.map Fin.val).toArray 0 CFSG.ComponentClassification.J2Cover.autStrong[0]! =
          true ∧
      siftA 315 (rawLevels 315 (pushWords 315 j2SigArrs j2Words) (j2Base.map Fin.val).toArray)
        (j2Base.map Fin.val).toArray 0 CFSG.ComponentClassification.J2Cover.autStrong[1]! =
          true ∧
      siftA 315 (rawLevels 315 (pushWords 315 j2SigArrs j2Words) (j2Base.map Fin.val).toArray)
        (j2Base.map Fin.val).toArray 0 zArr = true ∧
      siftA 315 (rawLevels 315 (pushWords 315 j2SigArrs j2Words) (j2Base.map Fin.val).toArray)
        (j2Base.map Fin.val).toArray 0 xArr = true := by
  have h := j2_sift_check
  simp only [j2SiftCheck, j2Levels, j2GenS, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem closure_j2Sig :
    Subgroup.closure (Set.range fun i : Fin j2SigArrs.size => permOfArr 315 j2SigArrs[(i : ℕ)]!) =
      CFSG.ComponentClassification.J2Cover.P := by
  refine closure_eq_of_chain (by norm_num) (by decide) (by norm_num) j2_chain rfl ?_ ?_
  · rw [j2_orbits, CFSG.ComponentClassification.J2Cover.card_P]
    rfl
  · intro g hg
    rcases hg with rfl | rfl
    · exact ⟨_, CFSG.ComponentClassification.J2Cover.rep_strong (by norm_num), j2_sifts.1⟩
    · exact ⟨_, CFSG.ComponentClassification.J2Cover.rep_strong (by norm_num), j2_sifts.2.1⟩

theorem j2_sig : sigCheck 315 j2SigArrs j2Ords j2PExps zArr xArr = true := by
  have h := j2_elt_check
  simp only [j2EltCheck, Bool.and_eq_true] at h
  exact h.2

theorem Ej_zero_eq :
    Ej 0 = Subgroup.closure ({⁅xJ, yJ⁆, xJ} : Set GJ) :=
  rfl

theorem fixGen_j2E0 :
    FixGen (Ej 0) := by
  rw [Ej_zero_eq]
  exact fixGen_of_sigCheck closure_j2Sig (rep_sig_of_chain j2_chain) Sporadic.J2.rep_z'
    Sporadic.J2.rep_x j2_sig

theorem kill9_j2
    (P : Subgroup GJ) (_hP : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    FixGen P ∨ NoSignalizer P := by
  left
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  have hP3 : Nat.card P3 = 3 ^ (Nat.card GJ).factorization 3 := by
    rw [Sporadic.J2.card_P3]
    change 27 = 3 ^ (Nat.card CFSG.ComponentClassification.J2Cover.P).factorization 3
    rw [CFSG.ComponentClassification.J2Cover.card_P, show (604800 : ℕ) = 3 ^ 3 * 22400 by norm_num,
      Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
    norm_num
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hP3 hPp
  have hle := Item434AltPerm.map_conj_inv_le hg
  have hmem : P.map (MulAut.conj g⁻¹).toMonoidHom ∈
      {B : Subgroup GJ | B ≤ P3 ∧ Nat.card B = 9} :=
    ⟨hle, by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP9]⟩
  rw [Sporadic.J2.nine_eq] at hmem
  obtain ⟨j, hj⟩ := hmem
  obtain ⟨n, -, hn⟩ := Sporadic.J2.exists_conj_E0 j
  have hPeq : P = ((Ej 0).map (MulAut.conj n⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom := by
    rw [← Item434AltPerm.map_conj_map_conj_inv P g, ← hj, ← hn]
    rfl
  rw [hPeq]
  exact (fixGen_j2E0.map_conj n⁻¹).map_conj g

end Item434SporGen

section Families


theorem item434Spor_J2_9 :
    Item434Spor_J2_9 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have b₀ : NativeSporadic.J2 ≃* Spor .J2 := b
  have eJ : NativeSporadic.J2 ≃* CFSG.ComponentClassification.J2Cover.P :=
    CFSG.ComponentClassification.J2Cover.nativeEquivP
  have hout : Nat.card (Outer CFSG.ComponentClassification.J2Cover.P) =
      Nat.card (Outer NativeSporadic.J2) :=
    (Nat.card_congr (equivalence eJ).toEquiv).symm
  refine Item434SporGen.item434SporAtCard_nine_of_kill9 (eJ.symm.trans b₀) ?_
    (by rw [CFSG.ComponentClassification.J2Cover.card_P]; norm_num) Item434SporGen.kill9_j2
  refine Item434Spor.not_three_dvd_card_outer_of_le_two ?_
  rw [hout]
  exact CFSG.Sporadic.Schreier.AT_J2_Schreier.1

end Families

end CFSG.RankThree.PartTwo.Sec4
