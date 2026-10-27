module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySevenTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyTwoRootLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4CartanRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4CartanRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.G2CartanRank
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevG2Rank
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20v
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218d
public import CFSG.GroupTheory.NormalizerQuotientQuotient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RootLine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

section CertB


private theorem pRank_eq_two_of_adjointG2 {Y K : Type} [Group Y] [Finite Y]
    [hfield : Field K] [hft : Fintype K] {f p : ℕ}
    (hKcard : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f)
    (e : Y ≃* CFSG.Blueprint.Chevalley.adjointGroup .G2 K)
    (hp : p.Prime) (hp2 : p ≠ 2) (hcong : (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)]) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) = 2 := by
  have hp1 : 1 ≤ 2 ^ f := Nat.one_le_pow f 2 (by norm_num)
  have hdvd : p ∣ (2 ^ f) ^ 2 - 1 := by
    have hfac : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ f) 1
    rw [hfac]
    exact dvd_mul_of_dvd_left (CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong) _
  have hES : CFSG.LocalAnalysis.RankThreeUC.S15.eS (2 ^ f) p = 1 :=
    (CFSG.LocalAnalysis.RankThreeUC.S15.eS_eq_one_iff hp1).2 hdvd
  have hKcard' : Fintype.card K = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  have hrank := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_adjointG2_eq K hKcard' hf2 hp hp2
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e, hrank, hKcard',
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_rkG2_of_eS hES]

theorem pRank_eq_two_of_isG2 {Y : Type} [Group Y] [Finite Y] {f p : ℕ} (hf2 : 2 ≤ f)
    (hG2 : IsG2 Y f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcong : (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)]) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) = 2 := by
  have hcheb : CFSG.Blueprint.ChevalleyExceptionalModel Y .G2 2 f :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2 (by decide)
  have hU : CFSG.Blueprint.UntwistedChevalleyModel Y .G2 (2 ^ f) := by
    simpa [CFSG.Blueprint.ChevalleyExceptionalModel] using hcheb.2
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup (τ := .G2) (q := 2 ^ f) hU
  let hft : Fintype K := @Fintype.ofFinite K hKfin
  exact pRank_eq_two_of_adjointG2 (Y := Y) (K := K) (hfield := hKf) (hft := hft)
    hKcard hf2 e hp hp2 hcong

theorem pRank_eq_two_of_isSp4_or_isG2_bar2 {L : Subgroup G} {f p : ℕ}
    (hshape : IsSp4 (Bar2 L) f ∨ IsG2 (Bar2 L) f) (hf2 : 2 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcong : (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)]) :
    CFSG.Open.pRank p L = 2 := by
  rw [← CFSG.Quasithin.pRank_modO2_eq L hp hp2]
  rcases hshape with hSp | hG2
  · have hdvd : p ∣ (2 ^ f) ^ 2 - 1 := by
      have hfac : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
        simpa using Nat.sq_sub_sq (2 ^ f) 1
      rw [hfac]
      exact dvd_mul_of_dvd_left
        (CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong) _
    exact le_antisymm (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p218d_pRank_le_two_sp4 hSp hp hp2)
      (CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.two_le_pRank_sp4 hSp hp hdvd)
  · exact pRank_eq_two_of_isG2 hf2 hG2 hp hp2 hcong

theorem exists_elemAbelian_sq_le_borel {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    {f r : ℕ} (hshape : IsU4 (Bar2 L) f ∨ IsSp4 (Bar2 L) f ∨ IsG2 (Bar2 L) f)
    (hq : 2 < 2 ^ f) (hr : r.Prime) (hr2 : r ≠ 2) (hrdvd : r ∣ 2 ^ f - 1) :
    ∃ E : Subgroup G, E ≤ L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G) ∧
      IsElemAbelian r E ∧ Nat.card E = r ^ 2 := by
  classical
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (sylowBar2 L (D.T ⊓ L)) ⊤ :=
    isSylowTwoOf_sylowBar2 hL
  have hrank : CFSG.Open.pRank r (⊤ : Subgroup
      (TauCeti.Subgroup.normalizerQuotient (sylowBar2 L (D.T ⊓ L)))) = 2 := by
    rcases hshape with hU4 | hSp | hG2
    · exact (CFSG.SectionRank.pRank_coe_eq_openPRank r _).symm.trans
        (Inputs1719.k_U4CartanRank_holds (Bar2 L) f hU4 hq _ hS r hr hr2 hrdvd).1
    · exact (CFSG.SectionRank.pRank_coe_eq_openPRank r _).symm.trans
        ((Inputs1719.k_Sp4CartanRank_holds (Bar2 L) f hSp hq _ hS).2 r hr hr2 hrdvd).1
    · exact (CFSG.SectionRank.pRank_coe_eq_openPRank r _).symm.trans
        (Inputs1719.k_G2CartanRank_holds (Bar2 L) f hG2 hq _ hS r hr hr2 hrdvd).1
  have hO2 : CFSG.pCore 2 ↥L ≤ (D.T ⊓ L).subgroupOf L := pCore_le_sylow_of_mem_calC hL
  have htrans : CFSG.Open.pRank r (⊤ : Subgroup
        (TauCeti.Subgroup.normalizerQuotient ((D.T ⊓ L).subgroupOf L))) =
      CFSG.Open.pRank r (⊤ : Subgroup
        (TauCeti.Subgroup.normalizerQuotient (sylowBar2 L (D.T ⊓ L)))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt
      (CFSG.GroupTheory.normalizerQuotient_quotientEquiv (CFSG.pCore 2 ↥L)
        ((D.T ⊓ L).subgroupOf L) hO2)
  set N : Subgroup ↥L := (D.T ⊓ L).subgroupOf L with hN
  set Nrm : Subgroup ↥L := Subgroup.normalizer (N : Set ↥L) with hNrm
  have hN2 : IsPGroup 2 N := (isSylowTwoOf_inf_of_mem_calC hL).2.1.comap_subtype
  have hcardN : ¬ r ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk]
    intro h
    have hd : r ∣ 2 := hr.dvd_of_dvd_pow h
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
    · exact hr.ne_one h1
    · exact hr2 h2
  have h2 : CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient N)) =
      CFSG.Open.pRank r (⊤ : Subgroup ↥Nrm) :=
    CFSG.SectionRank.pRank_quotient_eq (hp := ⟨hr⟩) (N.subgroupOf Nrm) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show N ≤ Nrm from
        Subgroup.le_normalizer)).toEquiv]
      exact hcardN)
  have hNrm2 : CFSG.Open.pRank r Nrm = 2 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← h2, htrans, hrank]
  obtain ⟨E₀, hE₀, hE₀el, hE₀card⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (hp := ⟨hr⟩) (H := Nrm) (k := 2)
      hNrm2.ge
  refine ⟨E₀.map L.subtype, ?_, CFSG.Open.IsElemAbelian.map hE₀el _, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxN : x ∈ (L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G)).subgroupOf L := by
      rw [← normalizer_sylow_subgroupOf]
      exact hE₀ hx
    exact Subgroup.mem_subgroupOf.mp hxN
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hE₀card]

theorem exists_rootLine_le_borel_mem_uniqueSet
    {D : Data G} {L : Subgroup G} {p f r : ℕ}
    (hL : L ∈ calC D.M) (hp : p ∈ D.sig)
    (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D) (h72 : F07.R72 D) (hK35 : UCK.K35w)
    (hKU4 : Inputs1719.K_U4RootLine) (hKSp4 : Inputs1719.K_Sp4RootLine)
    (hKG2 : Inputs1719.K_G2RootLine)
    (hshape : IsU4 (Bar2 L) f ∨ IsSp4 (Bar2 L) f ∨ IsG2 (Bar2 L) f) (hf1 : 1 < f)
    (hcong : (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)])
    (hcase : CFSG.Open.pRank p L = 2 ∨ IsU4 (Bar2 L) f)
    (hr : r.Prime) (hr5 : 5 < r) (hrdvd : r ∣ 2 ^ f - 1) (hLopp : L = Opp r D.M) :
    ∃ B : Subgroup G, B ≤ L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G) ∧
      Nat.card B = r ∧ B ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
  classical
  have hp' : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hp
  have h3 : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p hp
  have hOp : UC22.F10.OpRes p D.M = D.M := h638 p hp' hp2 (Or.inl hp)
  have hr7 : 7 ≤ r := by
    rcases hr.eq_two_or_odd' with h2 | hodd
    · omega
    · rcases hodd with ⟨k, hk⟩
      omega
  have hn : 3 ≤ f := by
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
    have hpos : 0 < 2 ^ f - 1 := by
      norm_num at h4
      omega
    have hle : r ≤ 2 ^ f - 1 := Nat.le_of_dvd hpos hrdvd
    have h8 : 8 ≤ 2 ^ f := by omega
    by_contra hlt
    have hn2 : f ≤ 2 := by omega
    have hpow : 2 ^ f ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    norm_num at hpow
    omega
  have hq : 2 < 2 ^ f := by
    have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hn
    norm_num at this
    omega
  have hpn : p ∣ 2 ^ f + 1 := CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong
  have hZ : Subgroup.center (Bar2 L) = ⊥ :=
    Inputs1719.center_eq_bot_of_rootLineShape hq hshape
  have hOut : IsCyclic (Outer (Bar2 L)) :=
    Inputs1719.isCyclic_outer_of_rootLineShape hshape
  have hroot : ∀ E : Subgroup G, E ≤ L → IsElemAbelian r E → Nat.card E = r ^ 2 →
      ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = r ∧
        (∃ Yt : Subgroup G, Yt ≤ L ⊓ Subgroup.centralizer (B : Set G) ∧
          ∃ N₀ : Subgroup ↥Yt, ∃ hN : N₀.Normal,
            @IsL2 (↥Yt ⧸ N₀) (@QuotientGroup.Quotient.group _ _ N₀ hN) f) ∧
        (IsU4 (Bar2 L) f →
          2 ≤ CFSG.Open.pRank p (L ⊓ Subgroup.centralizer (B : Set G)) ∧
          p ∣ Nat.card ↥(L ⊓ Subgroup.centralizer (E : Set G))) := by
    intro E hEX hEel hEcard
    obtain ⟨B, hBE, hBcard, ⟨Yt, hYt, N₀, hN, hL2⟩, hU4⟩ :=
      Inputs1719.exists_rootLine_lift hKU4 hKSp4 hKG2 hshape hq hr (by omega) hrdvd hEX hEel
        hEcard
    exact ⟨B, hBE, hBcard, ⟨Yt, hYt, N₀, hN, hL2⟩, fun hU4' => hU4 hU4' p hp' hp2 hpn⟩
  obtain ⟨E, hEB, hEel, hEcard⟩ :=
    exists_elemAbelian_sq_le_borel hL hshape hq hr (by omega) hrdvd
  obtain ⟨B, hBE, hBcard, -, hBU⟩ :=
    exists_mem_uniqueSet_rootLine h72 hK35 hp hsp h3 hOp hn hpn hZ hOut hr (by omega) hLopp
      hcase hroot (hEB.trans inf_le_left) hEel hEcard
  exact ⟨B, hBE.trans hEB, hBcard, hBU⟩

end CertB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
