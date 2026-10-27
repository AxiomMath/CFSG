module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InPStarCriteria
public import CFSG.GroupTheory.BangPrimeLarge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.PermutingTorusLe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRankBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanRankBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySixA2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SylowCentralOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Section17KFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Section17KFactsSmallRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanSylowAbelianLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20w
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySevenE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySevenF
public import CFSG.CGT.Timmesfeld75.OddCenter
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Sec5Nine
public import CFSG.CGT.Timmesfeld75.Sec5Ten
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp4Out
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySeven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inPStar_of_inP11_of_involutions {D : Data G} {V₀ X T₀ : Subgroup G}
    (hX : F11.InP11 D X) (hT₀T : T₀ ≤ D.T) (hTT₀ : D.T ≤ normalizer (T₀ : Set G))
    (hXT₀ : X ≤ normalizer (T₀ : Set G))
    (hinv : ∀ v ∈ D.T, ∀ w ∈ D.T, v ^ 2 = 1 → w ^ 2 = 1 → v ∉ T₀ → w ∉ T₀ → v * w⁻¹ ∈ T₀) :
    InPStar D V₀ X := by
  classical
  obtain ⟨p, hp, hp2, hXM, hXp, hXexp, hXnc, hperm, hΓ, hrest⟩ := hX
  have hXin : F11.InP11 D X := ⟨p, hp, hp2, hXM, hXp, hXexp, hXnc, hperm, hΓ, hrest⟩
  have hT₀2 : IsPGroup 2 ↥T₀ := D.sylowM.isPGroup.to_le hT₀T
  have hT₀core : T₀ ≤ pCoreOf 2 (X ⊔ D.T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hT₀T.trans le_sup_right)
      (sup_le hXT₀ hTT₀) hT₀2
  refine ⟨hXin, fun hV₀ => ?_⟩
  subst hV₀
  refine ⟨p, hp, hXp, Or.inr (Or.inl ?_)⟩
  let Y : Subgroup G := F11.Omega1p 2 D.T
  let Z : Subgroup G := pCoreOf 2 (X ⊔ D.T)
  have hYle : Y ≤ D.T := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hXZ : X ≤ normalizer (Z : Set G) := by
    intro x hx
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ D.T) (Subgroup.mem_sup_left hx)
  have hTZ : D.T ≤ normalizer (Z : Set G) := by
    intro t ht
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X ⊔ D.T) (Subgroup.mem_sup_right ht)
  by_cases hex : ∃ a ∈ D.T, a ^ 2 = 1 ∧ a ∉ T₀
  · obtain ⟨a, haT, ha2, haT₀⟩ := hex
    have hsub : ∀ v ∈ D.T, v ^ 2 = 1 → v ∈ zpowers a ⊔ T₀ := by
      intro v hvT hv2
      by_cases hv : v ∈ T₀
      · exact Subgroup.mem_sup_right hv
      · have hva : v * a⁻¹ ∈ T₀ := hinv v hvT a haT hv2 ha2 hv haT₀
        have hmem : (v * a⁻¹) * a ∈ T₀ ⊔ zpowers a :=
          Subgroup.mul_mem_sup hva (Subgroup.mem_zpowers a)
        have hv_eq : v = (v * a⁻¹) * a := by group
        rw [hv_eq, sup_comm]
        exact hmem
    have hYsup : Y ≤ zpowers a ⊔ T₀ :=
      (Subgroup.closure_le _).mpr fun x hx => hsub x hx.1 hx.2
    have haY : a ∈ Y := Subgroup.subset_closure ⟨haT, ha2⟩
    refine ⟨a, haY, ?_⟩
    apply le_antisymm
    · intro y hy
      have hYZ : y ∈ T₀ ⊔ zpowers a := by
        have h1 := hYsup hy
        rwa [sup_comm] at h1
      have hcoe : ((T₀ ⊔ zpowers a : Subgroup G) : Set G) =
          (T₀ : Set G) * (zpowers a : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left T₀ (zpowers a)
          ((Subgroup.zpowers_le.mpr haT).trans hTT₀)
      rw [← SetLike.mem_coe, hcoe] at hYZ
      obtain ⟨t, ht, w, hw, htw⟩ := Set.mem_mul.mp hYZ
      have hwY : w ∈ Y := Subgroup.zpowers_le.mpr haY hw
      have htY : t ∈ Y := by
        have hta : t = y * w⁻¹ := by rw [← htw]; group
        rw [hta]
        exact Y.mul_mem hy (Y.inv_mem hwY)
      have htZ : t ∈ Z := hT₀core ht
      have hmem : t * w ∈ (Y ⊓ Z) ⊔ zpowers a :=
        Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨htY, htZ⟩) hw
      rw [← htw, sup_comm]
      exact hmem
    · exact sup_le (Subgroup.zpowers_le.mpr haY) inf_le_left
  · have hYleT₀ : Y ≤ T₀ := by
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      by_contra hxT₀
      exact hex ⟨x, hx.1, hx.2, hxT₀⟩
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    apply le_antisymm
    · intro y hy
      exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hy, hT₀core (hYleT₀ hy)⟩)
    · exact sup_le (by simp) inf_le_left

theorem s17_47_pRank_bar2_isL3 {D : Data G} {L : Subgroup G} {n r : ℕ}
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev)
    (hL : L ∈ calC D.M) (hL3 : IsL3 (BarInf L) n) (hn : 3 ≤ n)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrdvd : r ∣ 2 ^ n - 1) :
    CFSG.Open.pRank r (⊤ : Subgroup (Bar2 L)) = 2 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨e⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hL
  have hmodel : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .PSL 3 2 n :=
    CFSG.Blueprint.LieModel.of_mulEquiv e hL3
  have hS : CFSG.Open.StatedClassicalModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .PSL 3 2 n :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  have h := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20w_pRank_psl hT hq (m := 3) (n := n)
    hS (by norm_num) hn hr hr2
  rw [h]
  have hq1 : ((2 ^ n : ℕ) : ZMod r) = 1 := by
    rw [Nat.cast_pow]
    exact (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff n).mp hrdvd
  simp [CFSG.LocalAnalysis.RankThreeUC.S15.rkLin, CFSG.LocalAnalysis.RankThreeUC.S15.eP, hq1,
    show ¬ (4 ≤ 3) by norm_num]

theorem s17_47_exists_inP11_of_large
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hL3 : IsL3 (BarInf L) n) (hLX : L = X) (h4 : 4 < 2 ^ n)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h638 : UC6.R6_38 D)
    (h1219 : D.sig = D.sig1)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D)
    (hK3 : Inputs1719.K_BorelTorusAbelianRankTwoNotL34)
    (hK4 : Inputs1719.K_CartanRankLeThree)
    (hK17 : Inputs1719.K_L3CartanThree)
    (hKAut3 : K_L3AutOThreeRank)
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hrn : ¬ r ∣ n) (hrdvd : r ∣ 2 ^ n - 1) :
    ∃ E : Subgroup G, E ≤ L ∧ E ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G) ∧
      CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Permutes E D.T ∧ F11.InP11 D E := by
  classical
  have hL : L ∈ calC D.M := ctx.mem_calC
  have hMN : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).mp
      (uc22p21j_normal_of_conjClosure_eq hL.1.le (hLX.trans ctx.X_eq))
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> norm_num [Nat.pow_succ] at h4
    · exact hn
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hC2 : 2 ≤ CFSG.Open.pRank r C := by
    have hbound := cartanRank_le_pRank_cartan_on (hK4 := hK4) (t := .PSL) (m := 3) (n := n)
      (r := r) hL ctx.cartan (by decide) hL3 hr hr2 hrdvd
      (fun _ hd => by have := Nat.le_of_dvd (by norm_num : 0 < 3) hd; omega)
      (fun h => absurd h (by decide))
    simpa [CS17LieRank] using hbound
  obtain ⟨E, hEB, hEel, hEperm, hEC⟩ :=
    ctx.exists_permuting_elemAbelian_le_of_borel
      (Inputs1719.BorelChevOver.of_on hK3 hL3 ⟨by decide, fun ⟨_, _, hn⟩ => by
        subst hn; norm_num at h4⟩) hr hr2
  have hEX : E ≤ X := hEB.trans inf_le_left
  have hEL : E ≤ L := by rwa [← hLX] at hEX
  have hEN : E ≤ Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
    rw [hLX]
    exact hEB.trans inf_le_right
  have hEM : E ≤ D.M := hEL.trans hL.1.le
  have hB2 : CFSG.Open.pRank r (X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G)) ≤ 2 := by
    have hB_le : X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G) ≤ L := by
      rw [hLX]
      exact inf_le_left
    have hLbar : CFSG.Open.pRank r L = CFSG.Open.pRank r (⊤ : Subgroup (Bar2 L)) := by
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
      exact (CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥L) (by
        exact CFSG.GroupTheory.not_dvd_card_of_isPGroup (CFSG.pCore_isPGroup (p := 2) (G := L))
          hr hr2)).symm
    have hL2 : CFSG.Open.pRank r L ≤ 2 := by
      rw [hLbar, s17_47_pRank_bar2_isL3 hT hL hL3 hn3 hr hr2 hrdvd]
    exact (CFSG.SectionRank.pRank_mono hr.one_lt hB_le).trans hL2
  have hErank_ge : 2 ≤ CFSG.Open.pRank r E := hC2.trans hEC
  have hErank_le : CFSG.Open.pRank r E ≤ 2 :=
    (CFSG.SectionRank.pRank_mono hr.one_lt hEB).trans hB2
  have hErank : CFSG.Open.pRank r E = 2 := le_antisymm hErank_le hErank_ge
  have hEcard : Nat.card E = r ^ 2 := by
    rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hr hEel, hErank]
  have hE2p : IsPGroup r E := hEel.isPGroup
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    have h1 : CFSG.Open.pRank r E ≤ 1 :=
      CFSG.SectionRank.pRank_le_one_of_isCyclic hr hcyc
    omega
  have hmodelK : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) .PSL 3 2 n :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hL).some hL3
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22l_odd_center_quotient
  have hab : ∀ P : Sylow r (Bar2 L), IsMulCommutative (P : Subgroup (Bar2 L)) :=
    fun P => Inputs1719.k_CartanSylowAbelian_linear (Bar2 L) .PSL 3 n r hL3.admissible
      hmodelK hL.2.2 hodd (Or.inl ⟨rfl, rfl⟩) hr hr5 hrdvd P
  have hout : ¬ r ∣ (L ⊔ F08.CentOverO2 D.M L).relIndex D.M := by
    intro hdvd
    exact not_dvd_card_outer_bar2 hL hL3 (Or.inl ⟨rfl, Or.inl rfl⟩) hr hr5 hrn
      (hdvd.trans (relIndex_centOverO2_dvd_card_outer hL.1.le hMN))
  obtain ⟨R, hR, hER⟩ :=
    exists_sylow_le_centralizer_of_isMulCommutative (M := D.M) (X := L) (E := E)
      hr hr2 hL.1.le hMN hab hout hEL hE2p
  have hF : 2 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) :=
    s17_47_cartan_cent (D := D) (V₀ := V₀) (V := V) (L := L) (X := X) (p := p)
      (n := n) (l := l) (C := C) (Dc := Dc) (Gamma := Gamma) ctx hL3 h4 hLX hSg h638
      hK3 hK4 hK17 hKAut3 hT hr hr5 hrdvd (E := E) hEL hEN hEel
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M :=
    strongly_of_two_le_pRank_centralizer hSg h1219 h76 h614 ctx.p_mem hr hr2 hR hEel hEcard hER hF
  exact ⟨E, hEL, hEN, hEel, hEcard, hEperm,
    inP11_of_strongly hr hr2 hstr hEM hE2p hEel.2 hEnc hEperm⟩

theorem s17_47_false_of_large
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hL3 : IsL3 (BarInf L) n) (hLX : L = X)
    (h4 : 4 < 2 ^ n) (h16 : 2 ^ n ≠ 16)
    (h1 : R17_1At D V₀ V ctx.hyp125)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h638 : UC6.R6_38 D)
    (h1219 : D.sig = D.sig1)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D)
    (hK3 : Inputs1719.K_BorelTorusAbelianRankTwoNotL34)
    (hK4 : Inputs1719.K_CartanRankLeThree)
    (hK17 : Inputs1719.K_L3CartanThree)
    (hKAut3 : K_L3AutOThreeRank)
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev) :
    False := by
  have hL : L ∈ calC D.M := ctx.mem_calC
  have hMN : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).mp
      (uc22p21j_normal_of_conjClosure_eq hL.1.le (hLX.trans ctx.X_eq))
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> norm_num [Nat.pow_succ] at h4
    · exact hn
  obtain ⟨r, hr, hr5, hrn, hrdvd, hhalf⟩ :=
    CFSG.GroupTheory.exists_prime_five_le_not_dvd_dvd_two_pow_sub_one h4 h16
  obtain ⟨E, hEL, hEN, hEel, -, hEperm, hEin⟩ :=
    s17_47_exists_inP11_of_large ctx hL3 hLX h4 hSg h638 h1219 h76 h614 hK3 hK4 hK17 hKAut3 hT
      hr hr5 hrn hrdvd
  obtain ⟨T₀, hT₀T, hTT₀, hET₀, hinv⟩ :=
    s17_47_exists_T0_of_borel (D.sylowM.le.trans hMN) (isSL3_of_isL3_barInf hL hL3) hn3
      (CFSG.GroupTheory.dvd_two_pow_sub_one_of_dvd_two_mul hrdvd hhalf) hEL hEN hEel.2 hEperm
  exact h1.1 E (inPStar_of_inP11_of_involutions hEin hT₀T hTT₀ hET₀ hinv)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
