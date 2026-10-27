module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenArr
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenMathieuCheck
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

namespace Item434SporGen

theorem rep_m22GenA : Monster.B.Co2.Rep 22 m22GenA CFSG.Sporadic.Mathieu.m22gA := by
  unfold Monster.B.Co2.Rep
  decide

theorem rep_m22GenB : Monster.B.Co2.Rep 22 m22GenB CFSG.Sporadic.Mathieu.m22gB := by
  unfold Monster.B.Co2.Rep
  decide


theorem m22_chain :
    rawChainOK 22 ((pushWords 22 m22SigArrs m22Words).extract 0 m22SigArrs.size)
      (pushWords 22 m22SigArrs m22Words) (m22Base.map Fin.val).toArray
      (wordsOf m22SigArrs.size m22Words) 4 = true := by
  have h := m22_chain_check
  simp only [m22ChainCheck, Bool.and_eq_true] at h
  exact h.1

theorem m22_orbits :
    rawOrbitSizes 22 (pushWords 22 m22SigArrs m22Words) (m22Base.map Fin.val).toArray =
      [22, 21, 20, 16, 3] := by
  have h := m22_chain_check
  simp only [m22ChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem m22_sifts :
    siftA 22 (rawLevels 22 (pushWords 22 m22SigArrs m22Words) (m22Base.map Fin.val).toArray)
        (m22Base.map Fin.val).toArray 0 m22GenA = true ∧
      siftA 22 (rawLevels 22 (pushWords 22 m22SigArrs m22Words) (m22Base.map Fin.val).toArray)
        (m22Base.map Fin.val).toArray 0 m22GenB = true ∧
      siftA 22 (rawLevels 22 (pushWords 22 m22SigArrs m22Words) (m22Base.map Fin.val).toArray)
        (m22Base.map Fin.val).toArray 0 m22E1 = true ∧
      siftA 22 (rawLevels 22 (pushWords 22 m22SigArrs m22Words) (m22Base.map Fin.val).toArray)
        (m22Base.map Fin.val).toArray 0 m22E2 = true := by
  have h := m22_sift_check
  simp only [m22SiftCheck, m22Levels, m22GenS, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem closure_m22Sig :
    Subgroup.closure (Set.range fun i : Fin m22SigArrs.size => permOfArr 22 m22SigArrs[(i : ℕ)]!) =
      NativeSporadic.M22 := by
  refine closure_eq_of_chain (by norm_num) (by decide) (by norm_num) m22_chain
    CFSG.Sporadic.Mathieu.m22_eq.symm ?_ ?_
  · rw [m22_orbits, CFSG.Sporadic.Mathieu.card_M22]
    rfl
  · intro g hg
    rcases hg with rfl | rfl
    · exact ⟨_, rep_m22GenA, m22_sifts.1⟩
    · exact ⟨_, rep_m22GenB, m22_sifts.2.1⟩

theorem m22_e9 : e9Check 22 m22E1 m22E2 = true := by
  have h := m22_elt_check
  simp only [m22EltCheck, Bool.and_eq_true] at h
  exact h.1

theorem m22_sig : sigCheck 22 m22SigArrs m22Ords m22PExps m22E1 m22E2 = true := by
  have h := m22_elt_check
  simp only [m22EltCheck, Bool.and_eq_true] at h
  exact h.2

theorem rep_m22E1 : Monster.B.Co2.Rep 22 m22E1 (permOfArr 22 m22E1) := by
  have h := m22_e9
  simp only [e9Check, Bool.and_eq_true] at h
  exact (rep_permOfArr h.1.1.1.1.1.1.1.1).1

theorem rep_m22E2 : Monster.B.Co2.Rep 22 m22E2 (permOfArr 22 m22E2) := by
  have h := m22_e9
  simp only [e9Check, Bool.and_eq_true] at h
  exact (rep_permOfArr h.1.1.1.1.1.1.1.2).1

@[expose] noncomputable def m22e1 : NativeSporadic.M22 :=
  ⟨permOfArr 22 m22E1, closure_m22Sig ▸ mem_closure_of_sift (D := m22Words) (by norm_num)
    (by decide) (by norm_num) m22_chain rep_m22E1 m22_sifts.2.2.1⟩

@[expose] noncomputable def m22e2 : NativeSporadic.M22 :=
  ⟨permOfArr 22 m22E2, closure_m22Sig ▸ mem_closure_of_sift (D := m22Words) (by norm_num)
    (by decide) (by norm_num) m22_chain rep_m22E2 m22_sifts.2.2.2⟩

theorem card_m22E :
    Nat.card (Subgroup.closure ({m22e1, m22e2} : Set NativeSporadic.M22)) = 9 :=
  card_closure_of_e9Check rep_m22E1 rep_m22E2 m22_e9

theorem fixGen_m22E :
    FixGen (Subgroup.closure ({m22e1, m22e2} : Set NativeSporadic.M22)) :=
  fixGen_of_sigCheck closure_m22Sig (rep_sig_of_chain m22_chain) rep_m22E1 rep_m22E2 m22_sig

theorem kill9_m22 (P : Subgroup NativeSporadic.M22)
    (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    FixGen P ∨ NoSignalizer P := by
  refine kill9_of_sylow ?_ card_m22E fixGen_m22E P hP hP9
  rw [card_m22E, CFSG.Sporadic.Mathieu.card_M22,
    show (443520 : ℕ) = 3 ^ 2 * 49280 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)]
  norm_num

end Item434SporGen

section Families


theorem item434Spor_M22_9 :
    Item434Spor_M22_9 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have b' : NativeSporadic.M22 ≃* Spor .M22 := b
  have : Finite NativeSporadic.M22 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Mathieu.card_M22]; norm_num)
  refine Item434SporGen.item434SporAtCard_nine_of_kill9 b' ?_
    (by rw [CFSG.Sporadic.Mathieu.card_M22]; norm_num) Item434SporGen.kill9_m22
  exact Item434Spor.not_three_dvd_card_outer_of_le_two
    (Sec4.card_outer_le_two_of_card_mulAut_le CFSG.Sporadic.Schreier.m22_center_eq_bot'
      CFSG.Sporadic.Schreier.m22_mulAut_card)

end Families

end CFSG.RankThree.PartTwo.Sec4
