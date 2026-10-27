module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrL
public import CFSG.Quasithin.Vol2.Ch10SecKHBC
public import CFSG.Quasithin.Vol2.Ch11SecKGBorelComm
public import CFSG.Quasithin.Vol2.Ch11SecBHBMainC

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.H13 C11AmS

theorem fact10_2_3Wreath_of (hE22 : E2.E22StatementC) (hW2 : FactOutL34Sp44) :
    Fact10_2_3Wreath := by
  intro G _ _ T M H B hs hnab hK hT hTM hN hH hn2 hB hB9 hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 < E1.nParam H := by
    rw [hn2]
    exact_mod_cast (one_lt_two : (1 : ℕ) < 2)
  set X := H ⊓ M with hXdef
  have hTH : T ≤ H := hH.1.1
  have hTX : T ≤ X := le_inf hTH hTM.2
  have hXH : X ≤ H := inf_le_left
  have hTS : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hT hTH
  have hTXs : IsSylowTwoOf T X := isSylowTwoOf_of_quasithinIsSylowTwo hT hTX
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hU : IsUniqueMaxOver H T X := by
    have := IsHStar.isUniqueMaxOver P (hP ▸ hH) (hP ▸ hTM.2)
    rwa [hP] at this
  have hmin : MinParabolic H T X := ⟨hTS, hH.not_le_normalizer hN, hU⟩
  have hns : ¬ Group.IsSolvable ↥H := fun hsol =>
    absurd hn1 (not_lt.mpr (E1.solvable_nParam_le_one hsol))
  obtain ⟨⟨K, hKc, hHK, -, hcases⟩, -⟩ := hE22.exists_cases hmin
    (sqtkGroup_of_pCoreOf_ne_bot hK hs hnab hH.1.2) hns
  obtain ⟨B₀, hB₀, -, hTQ⟩ := Ch11.SecB.derivedHallBorel_ofC hE22 Ch11.SecB.factBorelComm_holds
    G T M H hs hnab hK hT hTM hN hH hn1
  have hn_eq : ∀ n : ℕ, 2 ≤ n → (E2.IsBenderOf n ↥(E2.star X H K) ∨
      IsPSL 3 2 n ↥(E2.star X H K) ∨ IsPSp4 2 n ↥(E2.star X H K)) →
      E2.IsBorelIn (E2.star X H K) (E2.star X H (X ⊓ K)) → n = 2 := by
    intro n hn htype hBor
    obtain ⟨d, hd, hdo⟩ := exists_borel_elt factBorelCartan hn htype hBor
    have hodd : Odd (2 ^ n - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    obtain ⟨b, hb, hdvd⟩ := exists_hall_dvd hTXs hB₀ hTQ hB hd (by rw [hdo]; exact hodd)
    have h9 : orderOf b ∣ 9 := hB9 ▸ Subgroup.orderOf_dvd_natCard B hb
    exact eq_two_of_dvd_nine hn (hdo ▸ hdvd.trans h9)
  dsimp only [E2.E22CasesC] at hcases
  rcases hcases with ⟨hJ, t, ht, hne, hMeq, h1⟩ | ⟨hTK, hJ, h2⟩
  ·
    rcases h1 with ⟨n, hn, htype, hBor, -⟩ | ⟨_, _, _, _, _, _, hnH⟩
    · have hn' := hn_eq n hn (Or.inl ⟨hn, htype.elim Or.inl fun h => Or.inr (Or.inl h)⟩) hBor
      subst hn'
      exact case1a factBorelCartan hmin hXH hTX hTXs hns hKc hHK hJ ht hne hMeq
        (htype.resolve_right not_isSz_two) hBor hB hB9 hA
    · rw [hnH] at hn2
      exact absurd hn2 (by decide)
  ·
    exfalso
    rcases h2 with ⟨n, hBen, hBor, -, -⟩ | ⟨n, -, htype, -, hBor, hnH, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hnH⟩ | ⟨_, _, _, _, _, hnH⟩
    · have hn' := hn_eq n hBen.1 (Or.inl hBen) hBor
      subst hn'
      exact case2a_false factBorelCartan hXH hTX hTXs hTK hHK hBen hBor hB hB9 hA
    · have hn2' : 2 ≤ n := E2.E22A.two_le_of_one_lt_of_le hn1 hnH
      have htype' : IsPSL 3 2 n ↥(E2.star X H K) ∨ IsPSp4 2 n ↥(E2.star X H K) := by
        rcases htype with h | h
        · exact Or.inl h
        · rw [E2.IsSp4Prime] at h
          split_ifs at h with h1
          · omega
          · exact Or.inr h
      have hn' := hn_eq n hn2' (Or.inr htype') hBor
      subst hn'
      exact case2b_false hW2 Ch11.SecB.factBorelComm_holds hmin hXH hTX hTXs hKc hTK hHK hJ
        htype' hBor hB hA
    · rw [hnH] at hn2
      exact absurd hn2 (by decide)
    · rw [hnH] at hn2
      exact absurd hn2 (by decide)

end CFSG.Quasithin.Vol2.Ch10.SecB
