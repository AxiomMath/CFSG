module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporWords
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import Certificates.Certificate9564

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

namespace Item434SporGen

theorem he_check : heCheck = true :=
  Certificates.certificate9564

theorem heP_eq_closure_gens : heP = Subgroup.closure {heGenPerm 0, heGenPerm 1} := by
  rw [heP]

theorem factorization_card_heP :
    (Nat.card heP).factorization 3 = 3 := by
  rw [card_heP, show (4030387200 : ℕ) = 3 ^ 3 * 149273600 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]

theorem kill9_he
    (P : Subgroup heP) (_hP : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    FixGen P ∨ NoSignalizer P := by
  have : Finite heP := Nat.finite_of_card_ne_zero (by rw [card_heP]; norm_num)
  exact Or.inl (fixGen_of_ex27Check (rep_heGen (k := 0) (by norm_num))
    (rep_heGen (k := 1) (by norm_num)) heP_eq_closure_gens factorization_card_heP he_check P hP9)

end Item434SporGen

section Families


theorem item434Spor_He_9
 :
    Item434Spor_He_9 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .He ≃* Spor .He := b
  have eH : NativeSporadic.Carrier .He ≃* heP := heEquivP
  have : Finite heP := Nat.finite_of_card_ne_zero (by rw [card_heP]; norm_num)
  have hout : Nat.card (Outer heP) = Nat.card (Outer (NativeSporadic.Carrier .He)) :=
    (Nat.card_congr (equivalence eH).toEquiv).symm
  refine Item434SporGen.item434SporAtCard_nine_of_kill9 (eH.symm.trans b₀) ?_
    (by rw [card_heP]; norm_num) Item434SporGen.kill9_he
  refine Item434Spor.not_three_dvd_card_outer_of_le_two ?_
  rw [hout]
  exact CFSG.Sporadic.Schreier.AT_He_Schreier.1

end Families

end CFSG.RankThree.PartTwo.Sec4
