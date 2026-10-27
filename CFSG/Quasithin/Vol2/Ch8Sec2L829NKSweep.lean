module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKLift
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNi
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Sub
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.U3Rank
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.Classify
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2aB
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS4L3
public import CFSG.Quasithin.Background.E2TwoNoNStmt

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.H13.L829N

structure NKLeaves : Prop where
  sz : NKLeafSz
  szDvd : NKLeafSzDvd
  u3Even : NKLeafU3Even
  u3Five : NKLeafU3Five
  l3TwoOdd : NKLeafL3TwoOdd
  l2Odd : NKLeafL2Odd
  l2Tw : NKLeafL2TwentyFive
  l3Odd : NKLeafL3Odd
  u3Odd : NKLeafU3Odd
  u3FiveP : NKLeafU3FiveP
  l2Dvd3 : NKLeafL2Dvd3
  lift1 : NKLiftCase1 5
  lift2 : NKLiftCase2 5
  l32 : NKLeafL32
  schur : NKLeafSchurL32
  sl3 : NKLeafSL3Rep

theorem nk_uout_of_borel {Q : Type} [Group Q] {Ks MKs : Subgroup Q} (hB : E2.IsBorelIn Ks MKs)
    (hleaf : ∀ S : Subgroup ↥Ks, IsSylowTwoOf S ⊤ →
      UOut ↥Ks (Subgroup.normalizer (S : Set ↥Ks))) :
    UOut ↥Ks (MKs.subgroupOf Ks) := by
  obtain ⟨S, hS, hMKs⟩ := hB
  have hS' : IsSylowTwoOf (S.subgroupOf Ks) ⊤ := (isSylowTwoOf_top_iff_cs5 hS.1).mpr hS
  have e : MKs.subgroupOf Ks = Subgroup.normalizer ((S.subgroupOf Ks : Subgroup ↥Ks) : Set ↥Ks) := by
    ext b
    rw [hMKs, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      mem_normalizer_subgroupOf_cs5 hS.1 b]
    exact ⟨fun h => h.2, fun h => ⟨b.2, h⟩⟩
  rw [e]
  exact hleaf _ hS'

theorem nk_uout_of_centralizer {Q : Type} [Group Q] {Ks TKs : Subgroup Q}
    (hSyl : IsSylowTwoOf TKs Ks)
    (hleaf : ∀ S : Subgroup ↥Ks, IsSylowTwoOf S ⊤ →
      UOut ↥Ks (Subgroup.centralizer ((S ⊓ Subgroup.centralizer (S : Set ↥Ks) : Subgroup ↥Ks) :
        Set ↥Ks))) :
    UOut ↥Ks ((Ks ⊓ Subgroup.centralizer ((TKs ⊓ Subgroup.centralizer (TKs : Set Q) :
      Subgroup Q) : Set Q)).subgroupOf Ks) := by
  have hS' : IsSylowTwoOf (TKs.subgroupOf Ks) ⊤ := (isSylowTwoOf_top_iff_cs5 hSyl.1).mpr hSyl
  have e : (Ks ⊓ Subgroup.centralizer ((TKs ⊓ Subgroup.centralizer (TKs : Set Q) : Subgroup Q) :
      Set Q)).subgroupOf Ks =
      Subgroup.centralizer (((TKs.subgroupOf Ks) ⊓ Subgroup.centralizer
        ((TKs.subgroupOf Ks : Subgroup ↥Ks) : Set ↥Ks) : Subgroup ↥Ks) : Set ↥Ks) := by
    ext b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, hb⟩ h hh
      obtain ⟨hhS, hhC⟩ := Subgroup.mem_inf.mp hh
      have hhT : (h : Q) ∈ TKs := Subgroup.mem_subgroupOf.mp hhS
      have hhC' : (h : Q) ∈ Subgroup.centralizer (TKs : Set Q) := by
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have := Subgroup.mem_centralizer_iff.mp hhC ⟨s, hSyl.1 hs⟩ (Subgroup.mem_subgroupOf.mpr hs)
        exact congrArg Subtype.val this
      have := hb (h : Q) (Subgroup.mem_inf.mpr ⟨hhT, hhC'⟩)
      exact Subtype.ext this
    · intro hb
      refine ⟨b.2, fun z hz => ?_⟩
      obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.mp hz
      have hzK : z ∈ Ks := hSyl.1 hzT
      have hmem : (⟨z, hzK⟩ : ↥Ks) ∈ (TKs.subgroupOf Ks) ⊓ Subgroup.centralizer
          ((TKs.subgroupOf Ks : Subgroup ↥Ks) : Set ↥Ks) := by
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hzT, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have := Subgroup.mem_centralizer_iff.mp hzC (s : Q) (Subgroup.mem_subgroupOf.mp hs)
        exact Subtype.ext this
      have := hb _ hmem
      exact congrArg Subtype.val this
  rw [e]
  exact hleaf _ hS'

theorem nk_star_sylow {G : Type} [Group G] [Finite G] {H T M K : Subgroup G}
    (hT : IsSylowTwoOf T H) (hKc : K ∈ cComp H) :
    IsSylowTwoOf (E2.star M H (T ⊓ K)) (E2.star M H K) :=
  CFSG.Quasithin.F146Field.Case2a.isSylowTwoOf_star (le_of_mem_cComp hKc)
    (CFSG.Quasithin.A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hKc) hT)

theorem sweep_noKantor (hL : NKLeaves)
    {G : Type} [Group G] [Finite G] {H T M K : Subgroup G}
    (hcases : E2.E22CasesNoN H T M K) (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hT : IsSylowTwoOf T H)
    (hr3 : CFSG.Open.pRank 3 H ≤ 1) (hr5 : CFSG.Open.pRank 5 H ≤ 1)
    (hs : IsSimpleGroup ↥(E2.star M H K))
    (hna : ∃ a b : ↥(E2.star M H K), a * b ≠ b * a)
    (hfork : T ≤ Subgroup.normalizer (K : Set G) → UIn ↥(E2.star M H K) →
      UOut ↥(E2.star M H K) ((E2.star M H (M ⊓ K)).subgroupOf (E2.star M H K)) → False)
    (hStep8 : T ≤ Subgroup.normalizer (K : Set G) → ∀ n : ℕ, 2 ≤ n →
      IsPSL 2 2 n ↥(E2.star M H K) →
      E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → False) :
    L32Residual H T M K := by
  have hTH : T ≤ H := hHK ▸ le_sup_right
  have hKH : K ≤ H := le_of_mem_cComp hKc
  unfold E2.E22CasesNoN at hcases
  simp only at hcases
  unfold L32Residual
  simp only
  rcases hcases with ⟨hJ, t, htT, hne, hMeq, hcase⟩ | ⟨hTK, hJ, hcase⟩
  ·
    exfalso
    rcases hcase with ⟨n, hn2, hPSLSz, hBor⟩ | ⟨p, hp, hp8, hLp, hMK, h8⟩
    · rcases hPSLSz with hL2 | hS
      · exact not_surv1a_L2_of_pRank hKc (hTH htT) hJ hne (by omega) hL2 hr3
      · exact hL.lift1 hKc (hTH htT) hJ hne hs hna (hL.szDvd n _ hS) hr5
    · have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        rcases hp8 with h | h <;> omega
      exact nk_liftCase1_three hKc (hTH htT) hJ hne hs hna (hL.l2Dvd3 p hp hp5 _ hLp) hr3
  ·
    refine ⟨hTK, hJ, ?_⟩
    rcases hcase with ⟨n, hBend, hBor⟩ | ⟨n, hn1, hPSL, hDiag, hBor⟩ |
      ⟨p, e', hp, hp3, hee, hmod8, hL2, hMK, h8⟩ | ⟨p, hp, hp2, hrest, hMK⟩
    ·
      exfalso
      obtain ⟨hn2, hB⟩ := hBend
      rcases hB with hL2 | hS | hU
      · exact hStep8 hTK n hn2 hL2 hBor
      · obtain ⟨hIn, hOut⟩ := hL.sz n _ hS
        exact hfork hTK hIn (UOut.of_all hOut _)
      · rcases Nat.even_or_odd n with hev | hod
        · have h4 : n % 4 = 0 ∨ n % 4 = 2 := by
            obtain ⟨m, hm⟩ := hev
            omega
          rcases h4 with h0 | h2
          · obtain ⟨hIn, hOutB⟩ := hL.u3Even n h0 _ hU
            exact hfork hTK hIn (nk_uout_of_borel hBor hOutB)
          · exact hL.lift2 hKH hJ (hL.u3Five n h2 _ hU) hr5
        · exact nk_liftCase2_three hKH hJ
            (CFSG.HardMathSupport.Timmesfeld.Tables.Census.two_le_pRank_three_psu_three_two_pow_odd hod hU) hr3
    ·
      rcases hPSL with hL2 | hSp
      · rcases Nat.even_or_odd n with hev | hod
        · exfalso
          exact not_surv2b_of_pRank hKH hJ ⟨n, hn1, Or.inl ⟨hL2, hev⟩⟩ hr3
        · by_cases hn3 : n = 1
          · subst hn3
            exact Or.inl ⟨hL2, hDiag, hBor⟩
          · exfalso
            have h3 : 3 ≤ n := by
              obtain ⟨m, hm⟩ := hod
              omega
            obtain ⟨hIn, hOutB⟩ := hL.l3TwoOdd n hod h3 _ hL2
            exact hfork hTK hIn (nk_uout_of_borel hBor hOutB)
      · exfalso
        exact not_surv2b_of_pRank hKH hJ ⟨n, hn1, Or.inr hSp⟩ hr3
    ·
      by_cases h7 : p ^ e' = 7
      · have hpe : p = 7 ∧ e' = 1 := by
          rcases hee with rfl | rfl
          · exact ⟨by simpa using h7, rfl⟩
          · exfalso
            have : p ^ 2 = 7 := h7
            nlinarith
        obtain ⟨rfl, rfl⟩ := hpe
        exact Or.inr ⟨hL2, hMK, h8⟩
      · exfalso
        by_cases h25 : p ^ e' = 25
        · have hpe : p = 5 ∧ e' = 2 := by
            rcases hee with rfl | rfl
            · exfalso
              have : p = 25 := by simpa using h25
              subst this
              norm_num at hp
            · have : p ^ 2 = 25 := h25
              exact ⟨by nlinarith, rfl⟩
          obtain ⟨rfl, rfl⟩ := hpe
          exact hL.lift2 hKH hJ (hL.l2Tw _ hL2) hr5
        · obtain ⟨hIn, hOutC⟩ := hL.l2Odd p e' hp hp3 hee hmod8 h7 h25 _ hL2
          have hsyl := nk_star_sylow (M := M) hT hKc
          have hOut := nk_uout_of_centralizer hsyl hOutC
          rw [← hMK] at hOut
          exact hfork hTK hIn hOut
    ·
      exfalso
      rcases hrest with ⟨hp4, hU⟩ | ⟨hp4, hL3, -⟩
      · by_cases hp5 : p = 5
        · subst hp5
          exact hL.lift2 hKH hJ (hL.u3FiveP _ hU) hr5
        · have hp13 : 13 ≤ p := by
            by_contra hlt
            push Not at hlt
            have h2 := hp.two_le
            interval_cases p <;> first | omega | (norm_num at hp)
          obtain ⟨hIn, hOutC⟩ := hL.u3Odd p hp hp13 hp4 _ hU
          have hsyl := nk_star_sylow (M := M) hT hKc
          have hOut := nk_uout_of_centralizer hsyl hOutC
          rw [← hMK] at hOut
          exact hfork hTK hIn hOut
      · by_cases hp3' : p = 3
        · subst hp3'
          exact nk_liftCase2_three hKH hJ (CFSG.HardMathSupport.Timmesfeld.FieldBonus.two_le_pRank_of_char_three hL3) hr3
        · have hp7 : 7 ≤ p := by omega
          obtain ⟨hIn, hOutC⟩ := hL.l3Odd p hp hp7 hp4 _ hL3
          have hsyl := nk_star_sylow (M := M) hT hKc
          have hOut := nk_uout_of_centralizer hsyl hOutC
          rw [← hMK] at hOut
          exact hfork hTK hIn hOut

end CFSG.Quasithin.H13.L829NK
