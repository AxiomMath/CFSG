
module

public import CFSG.Sporadic.Co1.Module.InvRepsBase

public import CFSG.Sporadic.Co1.Module.InvData
public import CFSG.Sporadic.Co1.Module.Forms

public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative Matrix

theorem ncard_orbit_code3 :
    (Set.range fun g : NativeSporadic.Co1 => co1Act g (toVecD 24 code3)).ncard = 8386560 := by
  have hq : q₀ (toVecD 24 code3) = 1 := by
    rw [q₀_toVecD]
    simp [q0_code3]
  rw [range_co1Act, MulAction.orbit_eq_iff.2 ((q₀_eq_one_iff_mem_orbit _).1 hq), orbit_ncard_v₃]

theorem ncard_orbit_code4 :
    (Set.range fun g : NativeSporadic.Co1 => co1Act g (toVecD 24 code4)).ncard = 8292375 := by
  obtain ⟨g, hg⟩ := exists_co1_wordMat code4Word
  have hgv : co1Act g v₄ = toVecD 24 code4 := by
    rw [← toVecD_v₄, co1Act_eq_mulVec, hg, ← rowsMatrix_wordRows, rowsMatrix_mulVec, code4_word]
  have hm : toVecD 24 code4 ∈ MulAction.orbit Jmat v₄ := by
    rw [← range_co1Act]
    exact ⟨g, hgv⟩
  rw [range_co1Act, MulAction.orbit_eq_iff.2 hm, orbit_ncard_v₄]

theorem rep_facts :
    ∃ sA sB sC : NativeSporadic.Co1, RepFacts sA sB sC := by
  have hc3 : code3 < 2 ^ 24 := by norm_num [code3]
  have hc4 : code4 < 2 ^ 24 := by norm_num [code4]
  obtain ⟨kK, hkK⟩ := exists_gen_family kWord1 kWord2
  obtain ⟨kN, hkN⟩ := exists_gen_family nWord1 nWord2
  have hkK' : ∀ l < kGens.size, matHom (kK l) = rowsMatrix 24 kGens[l]! := hkK
  have hkN' : ∀ l < nGens.size, matHom (kN l) = rowsMatrix 24 nGens[l]! := hkN
  obtain ⟨hKs, -, -, -, -⟩ := repOK_facts repOK_A
  obtain ⟨hNs, -, -, -, -⟩ := repOK_facts repOK_B
  obtain ⟨sA, hsA⟩ := exists_rep kGens kK hkK' wordA (by rw [hKs]; decide) 7
  obtain ⟨sB, hsB⟩ := exists_rep nGens kN hkN' wordB (by rw [hNs]; decide) 6
  obtain ⟨sC, hsC⟩ := exists_rep nGens kN hkN' wordC (by rw [hNs]; decide) 5
  have hsA' : matHom sA = rowsMatrix 24 rowsSA := hsA
  have hsB' : matHom sB = rowsMatrix 24 rowsSB := hsB
  have hsC' : matHom sC = rowsMatrix 24 rowsSC := hsC
  obtain ⟨-, -, hoA, hfA, -⟩ := repOK_facts repOK_A
  obtain ⟨-, -, hoB, hfB, -⟩ := repOK_facts repOK_B
  obtain ⟨-, -, hoC, hfC, -⟩ := repOK_facts repOK_C
  have fixSet : ∀ (s : NativeSporadic.Co1) (S : Array ℕ), matHom s = rowsMatrix 24 S →
      {v : Vec24 | co1Act s v = v} = {v | rowsMatrix 24 S *ᵥ v = v} := by
    intro s S hs
    ext v
    simp only [Set.mem_ofPred_eq, co1Act_eq_mulVec, hs]
  have fixSetQ : ∀ (s : NativeSporadic.Co1) (S : Array ℕ), matHom s = rowsMatrix 24 S →
      {v : Vec24 | co1Act s v = v ∧ q₀ v = 1} = {v | rowsMatrix 24 S *ᵥ v = v ∧ q₀ v = 1} := by
    intro s S hs
    ext v
    simp only [Set.mem_ofPred_eq, co1Act_eq_mulVec, hs]
  obtain ⟨cA1, cA2⟩ := countsOK_facts counts_A
  obtain ⟨cB1, cB2⟩ := countsOK_facts counts_B
  obtain ⟨cC1, cC2⟩ := countsOK_facts counts_C
  have nA1 := (fixSet sA _ hsA').symm ▸ cA1
  have nA2 := (fixSetQ sA _ hsA').symm ▸ cA2
  have nB1 := (fixSet sB _ hsB').symm ▸ cB1
  have nB2 := (fixSetQ sB _ hsB').symm ▸ cB2
  have nC1 := (fixSet sC _ hsC').symm ▸ cC1
  have nC2 := (fixSetQ sC _ hsC').symm ▸ cC2
  have hN3 := ncard_orbit_code3
  have hN4 := ncard_orbit_code4
  have hq3 : q₀ (toVecD 24 code3) = 1 := by
    rw [q₀_toVecD]
    simp [q0_code3]
  have hF3 : {w ∈ Set.range (fun g : NativeSporadic.Co1 => co1Act g (toVecD 24 code3)) |
      co1Act sA w = w}.ncard ≤ 30720 := by
    rw [← nA2]
    refine Set.ncard_le_ncard (fun w hw => ⟨hw.2, ?_⟩)
    obtain ⟨g, hg⟩ := hw.1
    rw [← hg, q₀_co1Act, hq3]
  have hFB : {w ∈ Set.range (fun g : NativeSporadic.Co1 => co1Act g (toVecD 24 code4)) |
      co1Act sB w = w}.ncard ≤ 4096 := by
    rw [← nB1]
    exact Set.ncard_le_ncard (fun w hw => hw.2)
  have hFC : {w ∈ Set.range (fun g : NativeSporadic.Co1 => co1Act g (toVecD 24 code4)) |
      co1Act sC w = w}.ncard ≤ 4096 := by
    rw [← nC1]
    exact Set.ncard_le_ncard (fun w hw => hw.2)
  obtain ⟨W, hW⟩ := conj_ok
  have hsv : ∀ {s : NativeSporadic.Co1} {S : Array ℕ} {c : ℕ}, c < 2 ^ 24 →
      matHom s = rowsMatrix 24 S → isFixedN (transposeRows 24 S) c = true →
      co1Act s (toVecD 24 c) = toVecD 24 c := fun hc hs hf => by
    rw [co1Act_eq_mulVec, hs]
    exact (isFixedN_iff _ hc).1 hf
  obtain ⟨fA, dA, pA⟩ := InvFam.famA hW hsA'
  obtain ⟨fB, dB, pB⟩ := InvFam.famB hW hsB'
  obtain ⟨fC, dC, pC⟩ := InvFam.famC hW hsC'
  have bA := family_bound_set (hsv hc3 hsA' hfA) dA pA hN3 hF3
  have bB := family_bound_set (hsv hc4 hsB' hfB) dB pB hN4 hFB
  have bC := family_bound_set (hsv hc4 hsC' hfC) dC pC hN4 hFC
  rw [CFSG.Sporadic.Co1.card_Co1] at bA bB bC
  refine ⟨sA, sB, sC, orderOf_eq_of_orderIs hsA' (by norm_num) hoA,
    orderOf_eq_of_orderIs hsB' (by norm_num) hoB, orderOf_eq_of_orderIs hsC' (by norm_num) hoC,
    nA1, nB1, nC1, nA2, nB2, nC2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num at bA ⊢
    omega
  · norm_num at bB ⊢
    omega
  · norm_num at bC ⊢
    omega
  · exact witOK_facts (by norm_num) wit_A hsA' hsA'
  · exact witOK_facts (by norm_num) wit_B hsA' hsB'
  · exact witOK_facts (by norm_num) wit_C hsA' hsC'

end CFSG.Sporadic.Co1.Module
