module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenArr
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenJ2HSMcLCheck
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import CFSG.RankThree.Native.HSMcLSmall

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint CFSG.RankThree.Native
open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

namespace Item434SporGen


theorem hs_chain :
    rawChainOK 100 ((pushWords 100 hsSigArrs hsWords).extract 0 hsSigArrs.size)
      (pushWords 100 hsSigArrs hsWords) (hsBase.map Fin.val).toArray
      (wordsOf hsSigArrs.size hsWords) 4 = true := by
  have h := hs_chain_check
  simp only [hsChainCheck, Bool.and_eq_true] at h
  exact h.1

theorem hs_orbits :
    rawOrbitSizes 100 (pushWords 100 hsSigArrs hsWords) (hsBase.map Fin.val).toArray =
      [100, 77, 60, 12, 8] := by
  have h := hs_chain_check
  simp only [hsChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem hs_sifts :
    isInvA 100 (hs100Arr 0) (invCand 100 (hs100Arr 0)) = true ∧
      isInvA 100 (hs100Arr 1) (invCand 100 (hs100Arr 1)) = true ∧
      siftA 100 (rawLevels 100 (pushWords 100 hsSigArrs hsWords) (hsBase.map Fin.val).toArray)
        (hsBase.map Fin.val).toArray 0 (hs100Arr 0) = true ∧
      siftA 100 (rawLevels 100 (pushWords 100 hsSigArrs hsWords) (hsBase.map Fin.val).toArray)
        (hsBase.map Fin.val).toArray 0 (hs100Arr 1) = true ∧
      siftA 100 (rawLevels 100 (pushWords 100 hsSigArrs hsWords) (hsBase.map Fin.val).toArray)
        (hsBase.map Fin.val).toArray 0 hsE1 = true ∧
      siftA 100 (rawLevels 100 (pushWords 100 hsSigArrs hsWords) (hsBase.map Fin.val).toArray)
        (hsBase.map Fin.val).toArray 0 hsE2 = true := by
  have h := hs_sift_check
  simp only [hsSiftCheck, hsLevels, hsGenS, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem rep_hs100A : Monster.B.Co2.Rep 100 (hs100Arr 0) hs100A :=
  (rep_permOfArr hs_sifts.1).1

theorem rep_hs100B : Monster.B.Co2.Rep 100 (hs100Arr 1) hs100B :=
  (rep_permOfArr hs_sifts.2.1).1

theorem closure_hsSig :
    Subgroup.closure (Set.range fun i : Fin hsSigArrs.size => permOfArr 100 hsSigArrs[(i : ℕ)]!) =
      hs100P := by
  refine closure_eq_of_chain (by norm_num) (by decide) (by norm_num) hs_chain rfl ?_ ?_
  · rw [hs_orbits, card_hs100P]
    rfl
  · intro g hg
    rcases hg with rfl | rfl
    · exact ⟨_, rep_hs100A, hs_sifts.2.2.1⟩
    · exact ⟨_, rep_hs100B, hs_sifts.2.2.2.1⟩

theorem hs_e9 : e9Check 100 hsE1 hsE2 = true := by
  have h := hs_elt_check
  simp only [hsEltCheck, Bool.and_eq_true] at h
  exact h.1

theorem hs_sig : sigCheck 100 hsSigArrs hsOrds hsPExps hsE1 hsE2 = true := by
  have h := hs_elt_check
  simp only [hsEltCheck, Bool.and_eq_true] at h
  exact h.2

theorem rep_hsE1 : Monster.B.Co2.Rep 100 hsE1 (permOfArr 100 hsE1) := by
  have h := hs_e9
  simp only [e9Check, Bool.and_eq_true] at h
  exact (rep_permOfArr h.1.1.1.1.1.1.1.1).1

theorem rep_hsE2 : Monster.B.Co2.Rep 100 hsE2 (permOfArr 100 hsE2) := by
  have h := hs_e9
  simp only [e9Check, Bool.and_eq_true] at h
  exact (rep_permOfArr h.1.1.1.1.1.1.1.2).1

@[expose] noncomputable def hse1 : hs100P :=
  ⟨permOfArr 100 hsE1, closure_hsSig ▸ mem_closure_of_sift (D := hsWords) (by norm_num)
    (by decide) (by norm_num) hs_chain rep_hsE1 hs_sifts.2.2.2.2.1⟩

@[expose] noncomputable def hse2 : hs100P :=
  ⟨permOfArr 100 hsE2, closure_hsSig ▸ mem_closure_of_sift (D := hsWords) (by norm_num)
    (by decide) (by norm_num) hs_chain rep_hsE2 hs_sifts.2.2.2.2.2⟩

theorem card_hsE :
    Nat.card (Subgroup.closure ({hse1, hse2} : Set hs100P)) = 9 :=
  card_closure_of_e9Check rep_hsE1 rep_hsE2 hs_e9

theorem fixGen_hsE :
    FixGen (Subgroup.closure ({hse1, hse2} : Set hs100P)) :=
  fixGen_of_sigCheck closure_hsSig (rep_sig_of_chain hs_chain) rep_hsE1 rep_hsE2 hs_sig

theorem kill9_hs (P : Subgroup hs100P)
    (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    FixGen P ∨ NoSignalizer P := by
  refine kill9_of_sylow ?_ card_hsE fixGen_hsE P hP hP9
  rw [card_hsE, card_hs100P, show (44352000 : ℕ) = 3 ^ 2 * 4928000 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)]
  norm_num

end Item434SporGen

section Families


theorem item434Spor_HS_9 :
    Item434Spor_HS_9 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .HS ≃* Spor .HS := b
  have eH : NativeSporadic.Carrier .HS ≃* hs100P := hs100Equiv
  have hout : Nat.card (Outer hs100P) = Nat.card (Outer (NativeSporadic.Carrier .HS)) :=
    (Nat.card_congr (equivalence eH).toEquiv).symm
  refine Item434SporGen.item434SporAtCard_nine_of_kill9 (eH.symm.trans b₀) ?_
    (by rw [card_hs100P]; norm_num) Item434SporGen.kill9_hs
  refine Item434Spor.not_three_dvd_card_outer_of_le_two ?_
  rw [hout]
  exact CFSG.RankThree.PartOne.SPOR.card_outer_HS_le_two

end Families

end CFSG.RankThree.PartTwo.Sec4
